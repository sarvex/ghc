%*********************************************************************************
%*                                                                               *
%*       John Hughes's and Simon Peyton Jones's Pretty Printer Combinators       *
%*                                                                               *
%*               based on "The Design of a Pretty-printing Library"              *
%*               in Advanced Functional Programming,                             *
%*               Johan Jeuring and Erik Meijer (eds), LNCS 925                   *
%*               http://www.cs.chalmers.se/~rjmh/Papers/pretty.ps                *
%*                                                                               *
%*               Heavily modified by Simon Peyton Jones, Dec 96                  *
%*                                                                               *
%*********************************************************************************

Version 3.0     28 May 1997
  * Cured massive performance bug.  If you write

        foldl <> empty (map (text.show) [1..10000])

    you get quadratic behaviour with V2.0.  Why?  For just the same reason as you get
    quadratic behaviour with left-associated (++) chains.

    This is really bad news.  One thing a pretty-printer abstraction should
    certainly guarantee is insensivity to associativity.  It matters: suddenly
    GHC's compilation times went up by a factor of 100 when I switched to the
    new pretty printer.

    I fixed it with a bit of a hack (because I wanted to get GHC back on the
    road).  I added two new constructors to the Doc type, Above and Beside:

         <> = Beside
         $$ = Above

    Then, where I need to get to a "TextBeside" or "NilAbove" form I "force"
    the Doc to squeeze out these suspended calls to Beside and Above; but in so
    doing I re-associate. It's quite simple, but I'm not satisfied that I've done
    the best possible job.  I'll send you the code if you are interested.

  * Added new exports:
        punctuate, hang
        int, integer, float, double, rational,
        lparen, rparen, lbrack, rbrack, lbrace, rbrace,

  * fullRender's type signature has changed.  Rather than producing a string it
    now takes an extra couple of arguments that tells it how to glue fragments
    of output together:

        fullRender :: Mode
                   -> Int                       -- Line length
                   -> Float                     -- Ribbons per line
                   -> (TextDetails -> a -> a)   -- What to do with text
                   -> a                         -- What to do at the end
                   -> Doc
                   -> a                         -- Result

    The "fragments" are encapsulated in the TextDetails data type:
        data TextDetails = Chr  Char
                         | Str  String
                         | PStr FastString

    The Chr and Str constructors are obvious enough.  The PStr constructor has a packed
    string (FastString) inside it.  It's generated by using the new "ptext" export.

    An advantage of this new setup is that you can get the renderer to do output
    directly (by passing in a function of type (TextDetails -> IO () -> IO ()),
    rather than producing a string that you then print.


Version 2.0     24 April 1997
  * Made empty into a left unit for <> as well as a right unit;
    it is also now true that
        nest k empty = empty
    which wasn't true before.

  * Fixed an obscure bug in sep that occassionally gave very wierd behaviour

  * Added $+$

  * Corrected and tidied up the laws and invariants

======================================================================
Relative to John's original paper, there are the following new features:

1.  There's an empty document, "empty".  It's a left and right unit for
    both <> and $$, and anywhere in the argument list for
    sep, hcat, hsep, vcat, fcat etc.

    It is Really Useful in practice.

2.  There is a paragraph-fill combinator, fsep, that's much like sep,
    only it keeps fitting things on one line until it can't fit any more.

3.  Some random useful extra combinators are provided.
        <+> puts its arguments beside each other with a space between them,
            unless either argument is empty in which case it returns the other


        hcat is a list version of <>
        hsep is a list version of <+>
        vcat is a list version of $$

        sep (separate) is either like hsep or like vcat, depending on what fits

        cat  is behaves like sep,  but it uses <> for horizontal conposition
        fcat is behaves like fsep, but it uses <> for horizontal conposition

        These new ones do the obvious things:
                char, semi, comma, colon, space,
                parens, brackets, braces,
                quotes, quote, doubleQuotes

4.      The "above" combinator, $$, now overlaps its two arguments if the
        last line of the top argument stops before the first line of the second begins.
        For example:  text "hi" $$ nest 5 "there"
        lays out as
                        hi   there
        rather than
                        hi
                             there

        There are two places this is really useful

        a) When making labelled blocks, like this:
                Left ->   code for left
                Right ->  code for right
                LongLongLongLabel ->
                          code for longlonglonglabel
           The block is on the same line as the label if the label is
           short, but on the next line otherwise.

        b) When laying out lists like this:
                [ first
                , second
                , third
                ]
           which some people like.  But if the list fits on one line
           you want [first, second, third].  You can't do this with
           John's original combinators, but it's quite easy with the
           new $$.

        The combinator $+$ gives the original "never-overlap" behaviour.

5.      Several different renderers are provided:
                * a standard one
                * one that uses cut-marks to avoid deeply-nested documents
                        simply piling up in the right-hand margin
                * one that ignores indentation (fewer chars output; good for machines)
                * one that ignores indentation and newlines (ditto, only more so)

6.      Numerous implementation tidy-ups
        Use of unboxed data types to speed up the implementation



\begin{code}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS -fno-warn-unused-imports #-}
-- XXX GHC 6.9 seems to be confused by unpackCString# being used only in
--     a RULE

module Pretty (
        Doc,            -- Abstract
        Mode(..), TextDetails(..),

        empty, isEmpty, nest,

        char, text, ftext, ptext, ztext, zeroWidthText,
        int, integer, float, double, rational,
        parens, brackets, braces, quotes, quote, doubleQuotes,
        semi, comma, colon, space, equals,
        lparen, rparen, lbrack, rbrack, lbrace, rbrace, cparen,

        (<>), (<+>), hcat, hsep,
        ($$), ($+$), vcat,
        sep, cat,
        fsep, fcat,

        hang, punctuate,

--      renderStyle,            -- Haskell 1.3 only
        render, fullRender, printDoc, showDocWith,
        bufLeftRender -- performance hack
  ) where

import BufWrite
import FastString
import FastTypes
import Panic
import StaticFlags
import Numeric (fromRat)
import System.IO

#if defined(__GLASGOW_HASKELL__)
--for a RULES
import GHC.Base ( unpackCString# )
import GHC.Exts ( Int# )
import GHC.Ptr  ( Ptr(..) )
#endif

-- Don't import Util( assertPanic ) because it makes a loop in the module structure

infixl 6 <>
infixl 6 <+>
infixl 5 $$, $+$
\end{code}


\begin{code}

-- Disable ASSERT checks; they are expensive!
#define LOCAL_ASSERT(x)

\end{code}


%*********************************************************
%*                                                       *
\subsection{The interface}
%*                                                       *
%*********************************************************

The primitive @Doc@ values

\begin{code}
empty                     :: Doc
isEmpty                   :: Doc    -> Bool
-- | Some text, but without any width. Use for non-printing text
-- such as a HTML or Latex tags
zeroWidthText :: String   -> Doc

text                      :: String -> Doc
char                      :: Char -> Doc

semi, comma, colon, space, equals              :: Doc
lparen, rparen, lbrack, rbrack, lbrace, rbrace :: Doc

parens, brackets, braces    :: Doc -> Doc
quotes, quote, doubleQuotes :: Doc -> Doc

int      :: Int -> Doc
integer  :: Integer -> Doc
float    :: Float -> Doc
double   :: Double -> Doc
rational :: Rational -> Doc
\end{code}

Combining @Doc@ values

\begin{code}
(<>)   :: Doc -> Doc -> Doc     -- Beside
hcat   :: [Doc] -> Doc          -- List version of <>
(<+>)  :: Doc -> Doc -> Doc     -- Beside, separated by space
hsep   :: [Doc] -> Doc          -- List version of <+>

($$)   :: Doc -> Doc -> Doc     -- Above; if there is no
                                -- overlap it "dovetails" the two
vcat   :: [Doc] -> Doc          -- List version of $$

cat    :: [Doc] -> Doc          -- Either hcat or vcat
sep    :: [Doc] -> Doc          -- Either hsep or vcat
fcat   :: [Doc] -> Doc          -- ``Paragraph fill'' version of cat
fsep   :: [Doc] -> Doc          -- ``Paragraph fill'' version of sep

nest   :: Int -> Doc -> Doc     -- Nested
\end{code}

GHC-specific ones.

\begin{code}
hang :: Doc -> Int -> Doc -> Doc
punctuate :: Doc -> [Doc] -> [Doc]      -- punctuate p [d1, ... dn] = [d1 <> p, d2 <> p, ... dn-1 <> p, dn]
\end{code}

Displaying @Doc@ values.

\begin{code}
instance Show Doc where
  showsPrec _ doc cont = showDoc doc cont

render     :: Doc -> String             -- Uses default style
fullRender :: Mode
           -> Int                       -- Line length
           -> Float                     -- Ribbons per line
           -> (TextDetails -> a -> a)   -- What to do with text
           -> a                         -- What to do at the end
           -> Doc
           -> a                         -- Result

{-      When we start using 1.3
renderStyle  :: Style -> Doc -> String
data Style = Style { lineLength     :: Int,     -- In chars
                     ribbonsPerLine :: Float,   -- Ratio of ribbon length to line length
                     mode :: Mode
             }
style :: Style          -- The default style
style = Style { lineLength = 100, ribbonsPerLine = 2.5, mode = PageMode }
-}

data Mode = PageMode            -- Normal
          | ZigZagMode          -- With zig-zag cuts
          | LeftMode            -- No indentation, infinitely long lines
          | OneLineMode         -- All on one line

\end{code}


%*********************************************************
%*                                                       *
\subsection{The @Doc@ calculus}
%*                                                       *
%*********************************************************

The @Doc@ combinators satisfy the following laws:
\begin{verbatim}
Laws for $$
~~~~~~~~~~~
<a1>    (x $$ y) $$ z   = x $$ (y $$ z)
<a2>    empty $$ x      = x
<a3>    x $$ empty      = x

        ...ditto $+$...

Laws for <>
~~~~~~~~~~~
<b1>    (x <> y) <> z   = x <> (y <> z)
<b2>    empty <> x      = empty
<b3>    x <> empty      = x

        ...ditto <+>...

Laws for text
~~~~~~~~~~~~~
<t1>    text s <> text t        = text (s++t)
<t2>    text "" <> x            = x, if x non-empty

Laws for nest
~~~~~~~~~~~~~
<n1>    nest 0 x                = x
<n2>    nest k (nest k' x)      = nest (k+k') x
<n3>    nest k (x <> y)         = nest k z <> nest k y
<n4>    nest k (x $$ y)         = nest k x $$ nest k y
<n5>    nest k empty            = empty
<n6>    x <> nest k y           = x <> y, if x non-empty

 - Note the side condition on <n6>!  It is this that
   makes it OK for empty to be a left unit for <>.

Miscellaneous
~~~~~~~~~~~~~
<m1>    (text s <> x) $$ y = text s <> ((text "" <> x)) $$
                                         nest (-length s) y)

<m2>    (x $$ y) <> z = x $$ (y <> z)
        if y non-empty


Laws for list versions
~~~~~~~~~~~~~~~~~~~~~~
<l1>    sep (ps++[empty]++qs)   = sep (ps ++ qs)
        ...ditto hsep, hcat, vcat, fill...

<l2>    nest k (sep ps) = sep (map (nest k) ps)
        ...ditto hsep, hcat, vcat, fill...

Laws for oneLiner
~~~~~~~~~~~~~~~~~
<o1>    oneLiner (nest k p) = nest k (oneLiner p)
<o2>    oneLiner (x <> y)   = oneLiner x <> oneLiner y
\end{verbatim}


You might think that the following verion of <m1> would
be neater:
\begin{verbatim}
<3 NO>  (text s <> x) $$ y = text s <> ((empty <> x)) $$
                                         nest (-length s) y)
\end{verbatim}
But it doesn't work, for if x=empty, we would have
\begin{verbatim}
        text s $$ y = text s <> (empty $$ nest (-length s) y)
                    = text s <> nest (-length s) y
\end{verbatim}



%*********************************************************
%*                                                       *
\subsection{Simple derived definitions}
%*                                                       *
%*********************************************************

\begin{code}
semi  = char ';'
colon = char ':'
comma = char ','
space = char ' '
equals = char '='
lparen = char '('
rparen = char ')'
lbrack = char '['
rbrack = char ']'
lbrace = char '{'
rbrace = char '}'

int      n = text (show n)
integer  n = text (show n)
float    n = text (show n)
double   n = text (show n)
rational n = text (show (fromRat n :: Double))
--rational n = text (show (fromRationalX n)) -- _showRational 30 n)

quotes p        = char '`' <> p <> char '\''
quote p         = char '\'' <> p
doubleQuotes p  = char '"' <> p <> char '"'
parens p        = char '(' <> p <> char ')'
brackets p      = char '[' <> p <> char ']'
braces p        = char '{' <> p <> char '}'

cparen :: Bool -> Doc -> Doc
cparen True  = parens
cparen False = id

hcat = foldr (<>)  empty
hsep = foldr (<+>) empty
vcat = foldr ($$)  empty

hang d1 n d2 = sep [d1, nest n d2]

punctuate _ []     = []
punctuate p (d:ds) = go d ds
                   where
                     go d [] = [d]
                     go d (e:es) = (d <> p) : go e es
\end{code}


%*********************************************************
%*                                                       *
\subsection{The @Doc@ data type}
%*                                                       *
%*********************************************************

A @Doc@ represents a {\em set} of layouts.  A @Doc@ with
no occurrences of @Union@ or @NoDoc@ represents just one layout.
\begin{code}
data Doc
 = Empty                                -- empty
 | NilAbove Doc                         -- text "" $$ x
 | TextBeside !TextDetails FastInt Doc       -- text s <> x
 | Nest FastInt Doc                         -- nest k x
 | Union Doc Doc                        -- ul `union` ur
 | NoDoc                                -- The empty set of documents
 | Beside Doc Bool Doc                  -- True <=> space between
 | Above  Doc Bool Doc                  -- True <=> never overlap

type RDoc = Doc         -- RDoc is a "reduced Doc", guaranteed not to have a top-level Above or Beside


reduceDoc :: Doc -> RDoc
reduceDoc (Beside p g q) = beside p g (reduceDoc q)
reduceDoc (Above  p g q) = above  p g (reduceDoc q)
reduceDoc p              = p


data TextDetails = Chr  {-#UNPACK#-}!Char
                 | Str  String
                 | PStr FastString                      -- a hashed string
                 | ZStr FastZString                     -- a z-encoded string
                 | LStr {-#UNPACK#-}!LitString FastInt  -- a '\0'-terminated
                                                        -- array of bytes

space_text :: TextDetails
space_text = Chr ' '
nl_text :: TextDetails
nl_text    = Chr '\n'
\end{code}

Here are the invariants:
\begin{itemize}
\item
The argument of @NilAbove@ is never @Empty@. Therefore
a @NilAbove@ occupies at least two lines.

\item
The arugment of @TextBeside@ is never @Nest@.

\item
The layouts of the two arguments of @Union@ both flatten to the same string.

\item
The arguments of @Union@ are either @TextBeside@, or @NilAbove@.

\item
The right argument of a union cannot be equivalent to the empty set (@NoDoc@).
If the left argument of a union is equivalent to the empty set (@NoDoc@),
then the @NoDoc@ appears in the first line.

\item
An empty document is always represented by @Empty@.
It can't be hidden inside a @Nest@, or a @Union@ of two @Empty@s.

\item
The first line of every layout in the left argument of @Union@
is longer than the first line of any layout in the right argument.
(1) ensures that the left argument has a first line.  In view of (3),
this invariant means that the right argument must have at least two
lines.
\end{itemize}

\begin{code}
-- Arg of a NilAbove is always an RDoc
nilAbove_ :: Doc -> Doc
nilAbove_ p = LOCAL_ASSERT( _ok p ) NilAbove p
            where
              _ok Empty = False
              _ok _     = True

-- Arg of a TextBeside is always an RDoc
textBeside_ :: TextDetails -> FastInt -> Doc -> Doc
textBeside_ s sl p = TextBeside s sl (LOCAL_ASSERT( _ok p ) p)
                   where
                     _ok (Nest _ _) = False
                     _ok _          = True

-- Arg of Nest is always an RDoc
nest_ :: FastInt -> Doc -> Doc
nest_ k p = Nest k (LOCAL_ASSERT( _ok p ) p)
          where
            _ok Empty = False
            _ok _     = True

-- Args of union are always RDocs
union_ :: Doc -> Doc -> Doc
union_ p q = Union (LOCAL_ASSERT( _ok p ) p) (LOCAL_ASSERT( _ok q ) q)
           where
             _ok (TextBeside _ _ _) = True
             _ok (NilAbove _)       = True
             _ok (Union _ _)        = True
             _ok _                  = False
\end{code}

Notice the difference between
        * NoDoc (no documents)
        * Empty (one empty document; no height and no width)
        * text "" (a document containing the empty string;
                   one line high, but has no width)



%*********************************************************
%*                                                       *
\subsection{@empty@, @text@, @nest@, @union@}
%*                                                       *
%*********************************************************

\begin{code}
empty = Empty

isEmpty Empty = True
isEmpty _     = False

char  c = textBeside_ (Chr c) (_ILIT(1)) Empty
text  s = case iUnbox (length   s) of {sl -> textBeside_ (Str s)  sl Empty}
ftext :: FastString -> Doc
ftext s = case iUnbox (lengthFS s) of {sl -> textBeside_ (PStr s) sl Empty}
ptext :: LitString -> Doc
ptext s = case iUnbox (lengthLS s) of {sl -> textBeside_ (LStr s sl) sl Empty}
ztext :: FastZString -> Doc
ztext s = case iUnbox (lengthFZS s) of {sl -> textBeside_ (ZStr s) sl Empty}
zeroWidthText s = textBeside_ (Str s) (_ILIT(0)) Empty

#if defined(__GLASGOW_HASKELL__)
-- RULE that turns (text "abc") into (ptext (A# "abc"#)) to avoid the
-- intermediate packing/unpacking of the string.
{-# RULES
  "text/str" forall a. text (unpackCString# a) = ptext (Ptr a)
 #-}
#endif

nest k  p = mkNest (iUnbox k) (reduceDoc p)        -- Externally callable version

-- mkNest checks for Nest's invariant that it doesn't have an Empty inside it
mkNest :: Int# -> Doc -> Doc
mkNest k       (Nest k1 p) = mkNest (k +# k1) p
mkNest _       NoDoc       = NoDoc
mkNest _       Empty       = Empty
mkNest k       p  | k ==# _ILIT(0)  = p       -- Worth a try!
mkNest k       p           = nest_ k p

-- mkUnion checks for an empty document
mkUnion :: Doc -> Doc -> Doc
mkUnion Empty _ = Empty
mkUnion p q     = p `union_` q
\end{code}

%*********************************************************
%*                                                       *
\subsection{Vertical composition @$$@}
%*                                                       *
%*********************************************************


\begin{code}
p $$  q = Above p False q
($+$) :: Doc -> Doc -> Doc
p $+$ q = Above p True q

above :: Doc -> Bool -> RDoc -> RDoc
above (Above p g1 q1)  g2 q2 = above p g1 (above q1 g2 q2)
above p@(Beside _ _ _) g  q  = aboveNest (reduceDoc p) g (_ILIT(0)) (reduceDoc q)
above p g q                  = aboveNest p             g (_ILIT(0)) (reduceDoc q)

aboveNest :: RDoc -> Bool -> FastInt -> RDoc -> RDoc
-- Specfication: aboveNest p g k q = p $g$ (nest k q)

aboveNest NoDoc               _ _ _ = NoDoc
aboveNest (p1 `Union` p2)     g k q = aboveNest p1 g k q `union_`
                                      aboveNest p2 g k q

aboveNest Empty               _ k q = mkNest k q
aboveNest (Nest k1 p)         g k q = nest_ k1 (aboveNest p g (k -# k1) q)
                                  -- p can't be Empty, so no need for mkNest

aboveNest (NilAbove p)        g k q = nilAbove_ (aboveNest p g k q)
aboveNest (TextBeside s sl p) g k q = textBeside_ s sl rest
                                    where
                                      !k1  = k -# sl
                                      rest = case p of
                                                Empty -> nilAboveNest g k1 q
                                                _     -> aboveNest  p g k1 q
aboveNest _                   _ _ _ = panic "aboveNest: Unhandled case"
\end{code}

\begin{code}
nilAboveNest :: Bool -> FastInt -> RDoc -> RDoc
-- Specification: text s <> nilaboveNest g k q
--              = text s <> (text "" $g$ nest k q)

nilAboveNest _ _ Empty       = Empty    -- Here's why the "text s <>" is in the spec!
nilAboveNest g k (Nest k1 q) = nilAboveNest g (k +# k1) q

nilAboveNest g k q           | (not g) && (k ># _ILIT(0))        -- No newline if no overlap
                             = textBeside_ (Str (spaces k)) k q
                             | otherwise                        -- Put them really above
                             = nilAbove_ (mkNest k q)
\end{code}


%*********************************************************
%*                                                       *
\subsection{Horizontal composition @<>@}
%*                                                       *
%*********************************************************

\begin{code}
p <>  q = Beside p False q
p <+> q = Beside p True  q

beside :: Doc -> Bool -> RDoc -> RDoc
-- Specification: beside g p q = p <g> q

beside NoDoc               _ _   = NoDoc
beside (p1 `Union` p2)     g q   = (beside p1 g q) `union_` (beside p2 g q)
beside Empty               _ q   = q
beside (Nest k p)          g q   = nest_ k $! beside p g q       -- p non-empty
beside p@(Beside p1 g1 q1) g2 q2
           {- (A `op1` B) `op2` C == A `op1` (B `op2` C)  iff op1 == op2
                                                 [ && (op1 == <> || op1 == <+>) ] -}
         | g1 == g2              = beside p1 g1 $! beside q1 g2 q2
         | otherwise             = beside (reduceDoc p) g2 q2
beside p@(Above _ _ _)     g q   = let d = reduceDoc p in d `seq` beside d g q
beside (NilAbove p)        g q   = nilAbove_ $! beside p g q
beside (TextBeside s sl p) g q   = textBeside_ s sl $! rest
                               where
                                  rest = case p of
                                           Empty -> nilBeside g q
                                           _     -> beside p g q
\end{code}

\begin{code}
nilBeside :: Bool -> RDoc -> RDoc
-- Specification: text "" <> nilBeside g p
--              = text "" <g> p

nilBeside _ Empty      = Empty  -- Hence the text "" in the spec
nilBeside g (Nest _ p) = nilBeside g p
nilBeside g p          | g         = textBeside_ space_text (_ILIT(1)) p
                       | otherwise = p
\end{code}

%*********************************************************
%*                                                       *
\subsection{Separate, @sep@, Hughes version}
%*                                                       *
%*********************************************************

\begin{code}
-- Specification: sep ps  = oneLiner (hsep ps)
--                         `union`
--                          vcat ps

sep = sepX True         -- Separate with spaces
cat = sepX False        -- Don't

sepX :: Bool -> [Doc] -> Doc
sepX _ []     = empty
sepX x (p:ps) = sep1 x (reduceDoc p) (_ILIT(0)) ps


-- Specification: sep1 g k ys = sep (x : map (nest k) ys)
--                            = oneLiner (x <g> nest k (hsep ys))
--                              `union` x $$ nest k (vcat ys)

sep1 :: Bool -> RDoc -> FastInt -> [Doc] -> RDoc
sep1 _ NoDoc               _ _  = NoDoc
sep1 g (p `Union` q)       k ys = sep1 g p k ys
                                  `union_`
                                  (aboveNest q False k (reduceDoc (vcat ys)))

sep1 g Empty               k ys = mkNest k (sepX g ys)
sep1 g (Nest n p)          k ys = nest_ n (sep1 g p (k -# n) ys)

sep1 _ (NilAbove p)        k ys = nilAbove_ (aboveNest p False k (reduceDoc (vcat ys)))
sep1 g (TextBeside s sl p) k ys = textBeside_ s sl (sepNB g p (k -# sl) ys)
sep1 _ _                   _ _  = panic "sep1: Unhandled case"

-- Specification: sepNB p k ys = sep1 (text "" <> p) k ys
-- Called when we have already found some text in the first item
-- We have to eat up nests

sepNB :: Bool -> Doc -> FastInt -> [Doc] -> Doc
sepNB g (Nest _ p)  k ys  = sepNB g p k ys

sepNB g Empty k ys        = oneLiner (nilBeside g (reduceDoc rest))
                                `mkUnion`
                            nilAboveNest False k (reduceDoc (vcat ys))
                          where
                            rest | g         = hsep ys
                                 | otherwise = hcat ys

sepNB g p k ys            = sep1 g p k ys
\end{code}

%*********************************************************
%*                                                       *
\subsection{@fill@}
%*                                                       *
%*********************************************************

\begin{code}
fsep = fill True
fcat = fill False

-- Specification:
--   fill []  = empty
--   fill [p] = p
--   fill (p1:p2:ps) = oneLiner p1 <#> nest (length p1)
--                                          (fill (oneLiner p2 : ps))
--                     `union`
--                      p1 $$ fill ps

fill :: Bool -> [Doc] -> Doc
fill _ []     = empty
fill g (p:ps) = fill1 g (reduceDoc p) (_ILIT(0)) ps


fill1 :: Bool -> RDoc -> FastInt -> [Doc] -> Doc
fill1 _ NoDoc               _ _  = NoDoc
fill1 g (p `Union` q)       k ys = fill1 g p k ys
                                   `union_`
                                   (aboveNest q False k (fill g ys))

fill1 g Empty               k ys = mkNest k (fill g ys)
fill1 g (Nest n p)          k ys = nest_ n (fill1 g p (k -# n) ys)

fill1 g (NilAbove p)        k ys = nilAbove_ (aboveNest p False k (fill g ys))
fill1 g (TextBeside s sl p) k ys = textBeside_ s sl (fillNB g p (k -# sl) ys)
fill1 _ _                   _ _  = panic "fill1: Unhandled case"

fillNB :: Bool -> Doc -> Int# -> [Doc] -> Doc
fillNB g (Nest _ p)  k ys  = fillNB g p k ys
fillNB _ Empty _ []        = Empty
fillNB g Empty k (y:ys)    = nilBeside g (fill1 g (oneLiner (reduceDoc y)) k1 ys)
                             `mkUnion`
                             nilAboveNest False k (fill g (y:ys))
                           where
                             !k1 | g         = k -# _ILIT(1)
                                 | otherwise = k

fillNB g p k ys            = fill1 g p k ys
\end{code}


%*********************************************************
%*                                                       *
\subsection{Selecting the best layout}
%*                                                       *
%*********************************************************

\begin{code}
best :: Int             -- Line length
     -> Int             -- Ribbon length
     -> RDoc
     -> RDoc            -- No unions in here!

best w_ r_ p
  = get (iUnbox w_) p
  where
    !r = iUnbox r_
    get :: FastInt          -- (Remaining) width of line
        -> Doc -> Doc
    get _ Empty               = Empty
    get _ NoDoc               = NoDoc
    get w (NilAbove p)        = nilAbove_ (get w p)
    get w (TextBeside s sl p) = textBeside_ s sl (get1 w sl p)
    get w (Nest k p)          = nest_ k (get (w -# k) p)
    get w (p `Union` q)       = nicest w r (get w p) (get w q)
    get _ _                   = panic "best/get: Unhandled case"

    get1 :: FastInt         -- (Remaining) width of line
         -> FastInt         -- Amount of first line already eaten up
         -> Doc         -- This is an argument to TextBeside => eat Nests
         -> Doc         -- No unions in here!

    get1 _ _  Empty               = Empty
    get1 _ _  NoDoc               = NoDoc
    get1 w sl (NilAbove p)        = nilAbove_ (get (w -# sl) p)
    get1 w sl (TextBeside t tl p) = textBeside_ t tl (get1 w (sl +# tl) p)
    get1 w sl (Nest _ p)          = get1 w sl p
    get1 w sl (p `Union` q)       = nicest1 w r sl (get1 w sl p)
                                                   (get1 w sl q)
    get1 _ _  _                   = panic "best/get1: Unhandled case"

nicest :: FastInt -> FastInt -> Doc -> Doc -> Doc
nicest w r p q = nicest1 w r (_ILIT(0)) p q
nicest1 :: FastInt -> FastInt -> Int# -> Doc -> Doc -> Doc
nicest1 w r sl p q | fits ((w `minFastInt` r) -# sl) p = p
                   | otherwise                   = q

fits :: FastInt     -- Space available
     -> Doc
     -> Bool    -- True if *first line* of Doc fits in space available

fits n _   | n <# _ILIT(0) = False
fits _ NoDoc               = False
fits _ Empty               = True
fits _ (NilAbove _)        = True
fits n (TextBeside _ sl p) = fits (n -# sl) p
fits _ _                   = panic "fits: Unhandled case"
\end{code}

@first@ and @nonEmptySet@ are similar to @nicest@ and @fits@, only simpler.
@first@ returns its first argument if it is non-empty, otherwise its second.

\begin{code}
first :: Doc -> Doc -> Doc
first p q | nonEmptySet p = p
          | otherwise     = q

nonEmptySet :: Doc -> Bool
nonEmptySet NoDoc              = False
nonEmptySet (_ `Union` _)      = True
nonEmptySet Empty              = True
nonEmptySet (NilAbove _)       = True           -- NoDoc always in first line
nonEmptySet (TextBeside _ _ p) = nonEmptySet p
nonEmptySet (Nest _ p)         = nonEmptySet p
nonEmptySet _                  = panic "nonEmptySet: Unhandled case"
\end{code}

@oneLiner@ returns the one-line members of the given set of @Doc@s.

\begin{code}
oneLiner :: Doc -> Doc
oneLiner NoDoc               = NoDoc
oneLiner Empty               = Empty
oneLiner (NilAbove _)        = NoDoc
oneLiner (TextBeside s sl p) = textBeside_ s sl (oneLiner p)
oneLiner (Nest k p)          = nest_ k (oneLiner p)
oneLiner (p `Union` _)       = oneLiner p
oneLiner _                   = panic "oneLiner: Unhandled case"
\end{code}



%*********************************************************
%*                                                       *
\subsection{Displaying the best layout}
%*                                                       *
%*********************************************************


\begin{code}
{-
renderStyle Style{mode, lineLength, ribbonsPerLine} doc
  = fullRender mode lineLength ribbonsPerLine doc ""
-}

render doc       = showDocWith PageMode doc

showDoc :: Doc -> String -> String
showDoc doc rest = showDocWithAppend PageMode doc rest

showDocWithAppend :: Mode -> Doc -> String -> String
showDocWithAppend mode doc rest = fullRender mode 100 1.5 string_txt rest doc

showDocWith :: Mode -> Doc -> String
showDocWith mode doc = showDocWithAppend mode doc ""

string_txt :: TextDetails -> String -> String
string_txt (Chr c)   s  = c:s
string_txt (Str s1)  s2 = s1 ++ s2
string_txt (PStr s1) s2 = unpackFS s1 ++ s2
string_txt (ZStr s1) s2 = zString s1 ++ s2
string_txt (LStr s1 _) s2 = unpackLitString s1 ++ s2
\end{code}

\begin{code}

fullRender OneLineMode _ _ txt end doc
  = lay (reduceDoc doc)
  where
    lay NoDoc              = cant_fail
    lay (Union _ q)        = lay q -- Second arg can't be NoDoc
    lay (Nest _ p)         = lay p
    lay Empty              = end
    lay (NilAbove p)       = space_text `txt` lay p -- NoDoc always on
                                                    -- first line
    lay (TextBeside s _ p) = s `txt` lay p
    lay _                  = panic "fullRender/OneLineMode/lay: Unhandled case"

fullRender LeftMode    _ _ txt end doc
  = lay (reduceDoc doc)
  where
    lay NoDoc              = cant_fail
    lay (Union p q)        = lay (first p q)
    lay (Nest _ p)         = lay p
    lay Empty              = end
    lay (NilAbove p)       = nl_text `txt` lay p -- NoDoc always on first line
    lay (TextBeside s _ p) = s `txt` lay p
    lay _                  = panic "fullRender/LeftMode/lay: Unhandled case"

fullRender mode line_length ribbons_per_line txt end doc
  = display mode line_length ribbon_length txt end best_doc
  where
    best_doc = best hacked_line_length ribbon_length (reduceDoc doc)

    hacked_line_length, ribbon_length :: Int
    ribbon_length = round (fromIntegral line_length / ribbons_per_line)
    hacked_line_length = case mode of
                         ZigZagMode -> maxBound
                         _ -> line_length

display :: Mode -> Int -> Int -> (TextDetails -> t -> t) -> t -> Doc -> t
display mode page_width ribbon_width txt end doc
  = case (iUnbox page_width) -# (iUnbox ribbon_width) of { gap_width ->
    case gap_width `quotFastInt` _ILIT(2) of { shift ->
    let
        lay k (Nest k1 p)  = lay (k +# k1) p
        lay _ Empty        = end

        lay k (NilAbove p) = nl_text `txt` lay k p

        lay k (TextBeside s sl p)
            = case mode of
                    ZigZagMode |  k >=# gap_width
                               -> nl_text `txt` (
                                  Str (multi_ch shift '/') `txt` (
                                  nl_text `txt` (
                                  lay1 (k -# shift) s sl p)))

                               |  k <# _ILIT(0)
                               -> nl_text `txt` (
                                  Str (multi_ch shift '\\') `txt` (
                                  nl_text `txt` (
                                  lay1 (k +# shift) s sl p )))

                    _ -> lay1 k s sl p
        lay _ _            = panic "display/lay: Unhandled case"

        lay1 k s sl p = indent k (s `txt` lay2 (k +# sl) p)

        lay2 k (NilAbove p)        = nl_text `txt` lay k p
        lay2 k (TextBeside s sl p) = s `txt` (lay2 (k +# sl) p)
        lay2 k (Nest _ p)          = lay2 k p
        lay2 _ Empty               = end
        lay2 _ _                   = panic "display/lay2: Unhandled case"

        -- optimise long indentations using LitString chunks of 8 spaces
        indent n r | n >=# _ILIT(8) = LStr (sLit "        ") (_ILIT(8)) `txt`
                                      indent (n -# _ILIT(8)) r
                   | otherwise      = Str (spaces n) `txt` r
    in
    lay (_ILIT(0)) doc
    }}

cant_fail :: a
cant_fail = error "easy_display: NoDoc"

multi_ch :: Int# -> Char -> String
multi_ch n ch | n <=# _ILIT(0) = ""
              | otherwise      = ch : multi_ch (n -# _ILIT(1)) ch

spaces :: Int# -> String
spaces n | n <=# _ILIT(0) = ""
         | otherwise      = ' ' : spaces (n -# _ILIT(1))

\end{code}

\begin{code}
printDoc :: Mode -> Int -> Handle -> Doc -> IO ()
printDoc LeftMode _ hdl doc
  = do { printLeftRender hdl doc; hFlush hdl }
printDoc mode pprCols hdl doc
  = do { fullRender mode pprCols 1.5 put done doc ;
         hFlush hdl }
  where
    put (Chr c)  next = hPutChar hdl c >> next
    put (Str s)  next = hPutStr  hdl s >> next
    put (PStr s) next = hPutStr  hdl (unpackFS s) >> next
                        -- NB. not hPutFS, we want this to go through
                        -- the I/O library's encoding layer. (#3398)
    put (ZStr s) next = hPutFZS  hdl s >> next
    put (LStr s l) next = hPutLitString hdl s l >> next

    done = hPutChar hdl '\n'

  -- some versions of hPutBuf will barf if the length is zero
hPutLitString :: Handle -> Ptr a -> Int# -> IO ()
hPutLitString handle a l = if l ==# _ILIT(0)
                            then return ()
                            else hPutBuf handle a (iBox l)

-- Printing output in LeftMode is performance critical: it's used when
-- dumping C and assembly output, so we allow ourselves a few dirty
-- hacks:
--
-- (1) we specialise fullRender for LeftMode with IO output.
--
-- (2) we add a layer of buffering on top of Handles.  Handles
--     don't perform well with lots of hPutChars, which is mostly
--     what we're doing here, because Handles have to be thread-safe
--     and async exception-safe.  We only have a single thread and don't
--     care about exceptions, so we add a layer of fast buffering
--     over the Handle interface.
--
-- (3) a few hacks in layLeft below to convince GHC to generate the right
--     code.

printLeftRender :: Handle -> Doc -> IO ()
printLeftRender hdl doc = do
  b <- newBufHandle hdl
  bufLeftRender b doc
  bFlush b

bufLeftRender :: BufHandle -> Doc -> IO ()
bufLeftRender b doc = layLeft b (reduceDoc doc)

-- HACK ALERT!  the "return () >>" below convinces GHC to eta-expand
-- this function with the IO state lambda.  Otherwise we end up with
-- closures in all the case branches.
layLeft :: BufHandle -> Doc -> IO ()
layLeft b _ | b `seq` False  = undefined -- make it strict in b
layLeft _ NoDoc              = cant_fail
layLeft b (Union p q)        = return () >> layLeft b (first p q)
layLeft b (Nest _ p)         = return () >> layLeft b p
layLeft b Empty              = bPutChar b '\n'
layLeft b (NilAbove p)       = bPutChar b '\n' >> layLeft b p
layLeft b (TextBeside s _ p) = put b s >> layLeft b p
 where
    put b _ | b `seq` False = undefined
    put b (Chr c)    = bPutChar b c
    put b (Str s)    = bPutStr  b s
    put b (PStr s)   = bPutFS   b s
    put b (ZStr s)   = bPutFZS  b s
    put b (LStr s l) = bPutLitString b s l
layLeft _ _                  = panic "layLeft: Unhandled case"
\end{code}
