{-# LANGUAGE GADTs #-}
module CmmCreateSwitchPlans
  ( cmmCreateSwitchPlans
  )
where

import Data.Functor ((<$>))

import Hoopl
import BlockId
import Cmm
import CmmUtils
import CmmSwitch
import UniqSupply
import DynFlags

cmmCreateSwitchPlans :: DynFlags -> CmmGraph -> UniqSM CmmGraph
cmmCreateSwitchPlans dflags g = do
    blocks' <- concat <$> mapM (visitSwitches dflags) (toBlockList g)
    return $ ofBlockList (g_entry g) blocks'

-- Implementing a switch plan (returning a tail block)
implementSwitchPlan :: DynFlags -> CmmExpr -> SwitchPlan -> UniqSM (Block CmmNode O C, [CmmBlock])
implementSwitchPlan _ _ (Unconditionally l)
  = return (emptyBlock `blockJoinTail` CmmBranch l, [])
implementSwitchPlan _ expr (JumpTable ids)
  = return (emptyBlock `blockJoinTail` CmmSwitch expr ids, [])
implementSwitchPlan dflags expr (IfLT i ids1 ids2)
  = do
    (bid1, newBlocks1) <- implementSwitchPlan' dflags expr ids1
    (bid2, newBlocks2) <- implementSwitchPlan' dflags expr ids2
    
    -- TODO: Is this cast safe?
    let scrut = cmmULtWord dflags expr (mkIntExpr dflags (fromIntegral i))
        lastNode = CmmCondBranch scrut bid1 bid2
        lastBlock = emptyBlock `blockJoinTail` lastNode
    return (lastBlock, newBlocks1++newBlocks2)
implementSwitchPlan dflags expr (IfEqual i l ids2)
  = do
    (bid2, newBlocks2) <- implementSwitchPlan' dflags expr ids2

    -- TODO: Is this cast safe?
    let scrut = cmmNeWord dflags expr (mkIntExpr dflags (fromIntegral i))
        lastNode = CmmCondBranch scrut bid2 l
        lastBlock = emptyBlock `blockJoinTail` lastNode
    return (lastBlock, newBlocks2)

-- Implementing a switch plan (returning a label to branch to)
implementSwitchPlan' :: DynFlags -> CmmExpr -> SwitchPlan -> UniqSM (Label, [CmmBlock])
implementSwitchPlan' _ _ (Unconditionally l)
  = return (l, [])
implementSwitchPlan' dflags expr p
  = do
    bid <- mkBlockId <$> getUniqueM 
    (last, newBlocks) <- implementSwitchPlan dflags expr p
    let block = CmmEntry bid GlobalScope `blockJoinHead` last
    return (bid, block: newBlocks)


visitSwitches :: DynFlags -> CmmBlock -> UniqSM [CmmBlock]
visitSwitches dflags block
  | (CmmEntry l s, middle, CmmSwitch expr ids) <- blockSplit block
  = do
    let plan = createSwitchPlan ids

    (newTail, newBlocks) <- implementSwitchPlan dflags expr plan

    let block' = CmmEntry l s `blockJoinHead` middle `blockAppend` newTail 

    return $ block' : newBlocks

  | otherwise
  = return [block]


