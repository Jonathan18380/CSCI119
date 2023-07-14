--Jonathan Wong
-- CSci 119, Lab 4

import Data.List (sort, stripPrefix) -- for your solution to Lab 3


---------------- Code provided to you in Lab 3 ----------------

-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

-- Length-Ordered Lists over "character type" a (aka "strings")
-- Invariant: In LOL n xs, n == length xs
data LOL a = LOL Int [a] deriving (Eq,Ord)

instance Show a => Show (LOL a) where
  show (LOL n xs) = show xs

-- Empty list (epsilon)
eps :: LOL a
eps = LOL 0 []

-- Smart constructor for LOL a, establishes invariant
lol :: [a] -> LOL a
lol xs = LOL (length xs) xs

-- Normalized lists of LOLs (aka "languages")
-- Invariant: xs :: Lang a implies xs is sorted with no duplicates
type Lang a = [LOL a]

-- Smart constructor for (finite) languages
lang :: Ord a => [[a]] -> Lang a
lang xs = norm $ map lol xs

---- Regular expressions, along with input and output
data RegExp = Empty                -- Empty language
            | Let Char             -- Single letter language
            | Union RegExp RegExp  -- Union
            | Cat RegExp RegExp    -- Concatenation
            | Star RegExp          -- Kleene star
            deriving (Show, Eq)

-- Compact display form for RegExp
newtype Compact = Compact RegExp

instance (Show Compact) where    -- use precedence to minimize parentheses
  showsPrec d (Compact r) = sp d r where
    sp d Empty         = showString "@"
    sp d (Let c)       = showString [c]
    sp d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                         sp 6 r1 .
                         showString "+" .
                         sp 6 r2
    sp d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                         sp 7 r1 .
                         sp 7 r2
    sp d (Star r1)     = sp 9 r1 .     -- prec(Star) = 8
                         showString "*"

-- Quick and dirty postfix RegExp parser, gives non-exaustive match on error
toRE :: String -> RegExp
toRE w = go w [] where
  go [] [r]              = r
  go ('+':xs) (r2:r1:rs) = go xs (Union r1 r2:rs)
  go ('.':xs) (r2:r1:rs) = go xs (Cat r1 r2:rs)
  go ('*':xs) (r:rs)     = go xs (Star r:rs)
  go ('0':xs) rs         = go xs (Empty:rs)
  go ('1':xs) rs         = go xs (Star Empty:rs)
  go (x:xs) rs           = go xs (Let x:rs)


---------------- Your solution to Lab 3 ----------------

-- Include here any code you need from your solution to Lab 3 for testing
-- purposes. After a few days, I will release a solution for you to use.
-- Don't duplicate the code just given above.



---------------- Part 1 ----------------

-- Implement the seven RECURSIVE predicates/operations on RegExp given in
-- Section 3.3 of the notes; call them empty, uni, byp, inf, revrs, lq,
-- and nep. Each should begin with a type declaration. Include several tests
-- for each function. Then implement one more not given there: purity.


empty :: RegExp -> Bool
empty Empty = True
empty (Let a) = False
empty (Union r1 r2) = empty r1 && empty r2
empty (Cat r1 r2) = empty r1 || empty r2
empty (Star r1) = False

revrs :: RegExp -> Bool
revrs Empty = True
revrs (Let a) = False
revrs (Union r1 r2) = revrs r1 && revrs r2
revrs (Cat r1 r2) = revrs r1 && revrs r2
revrs (Star r1) = revrs r1

uni :: RegExp -> Bool
uni Empty = False
uni (Let a) = True
uni (Union r1 r2) = uni r1 || uni r2
uni (Cat r1 r2) = uni r1 && uni r2
uni (Star r1) = uni r1


byp :: RegExp -> Bool
byp Empty = False
byp (Let a) = False
byp (Union r1 r2) = byp r1 || byp r2
byp (Cat r1 r2) = byp r1 && byp r2
byp (Star r1) = True

inf :: RegExp -> Bool
inf Empty = False
inf (Let a) = False
inf (Union r1 r2) = inf r1 || inf r2
inf (Cat r1 r2) = (inf r1 && byp r2) || inf r2 || (inf r1 && inf r2)
inf (Star r1) = not (empty r1)

lq :: RegExp -> RegExp
lq Empty = Empty
lq (Let a) = Empty
lq (Union r1 r2) = Union (lq r1) (lq r2)
lq (Cat r1 r2) = Union (Cat (lq r1) r2) (Cat (lq r1) (lq r2))
lq (Star r1) = Cat (lq r1) (Star r1)

nep :: RegExp -> Bool
nep Empty = False
nep (Let a) = True
nep (Union r1 r2) = nep r1 || nep r2
nep (Cat r1 r2) = nep r1 && nep r2
nep (Star r1) = not (empty r1)


-- Purity. A regular expression is *pure* if every string matching r
-- has at least one character, or, equivalently, if ε is not in [[r]].
-- (Note that r is pure exactly when r is not bypassable, but you are
-- to give a recursive definition here, not define it in terms of byp.)

purity :: RegExp -> Bool
purity Empty = False
purity (Let a) = True
purity (Union r1 r2) = purity r1 && purity r2
purity (Cat r1 r2) = purity r1 && purity r2
purity (Star r1) = purity r1

---------------- Part 2 ----------------

-- Implement the two matching algorithms given in Section 3.4 of the notes,
-- where the second algorithm is the modified one I posted on Piazza (@96).
-- Call them match1 and match2. Start by implementing splits:

-- splits xs = list of all possible splits of xs, in order. For example,
-- splits "bc" =  [("","bc"), ("b","c"), ("bc","")]
-- splits "abc" = [("","abc"), ("a","bc"), ("ab","c"), ("abc","")]

splits :: [a] -> [([a], [a])]
splits [] = [([], [])]
splits (x:xs) = [([], x:xs)] ++ [(x:ys, zs) | (ys, zs) <- splits xs]

{-
*Main> splits [1,2,3,4]
[([],[1,2,3,4]),([1],[2,3,4]),([1,2],[3,4]),([1,2,3],[4]),([1,2,3,4],[])]
*Main> splits [1,2,3]
[([],[1,2,3]),([1],[2,3]),([1,2],[3]),([1,2,3],[])]
*Main> splits [1,2]
[([],[1,2]),([1],[2]),([1,2],[])]
*Main> splits []
[([],[])]
*Main> splits ['a','b','c']
[("","abc"),("a","bc"),("ab","c"),("abc","")]
*Main>
-}



match1 :: RegExp -> String -> Bool
match1 Empty w = False
match1 (Let c) (x:xs) = c == x && null xs
match1 (Let _) [] = False
match1 (Union r1 r2) w = match1 r1 w || match1 r2 w
match1 (Cat r1 r2) w = or [match1 r1 u && match1 r2 v | (u,v) <- splits w]
match1 (Star r) [] = True
match1 (Star r) (x:xs) = match1 r [x] && match1 (Star r) xs

{-
*Main> match1 Empty "abc"
False
*Main> match1 Empty "Hello"
False
*Main> match1 Empty "a"
False
*Main> match1 (Cat (Let 'x') (Let 'y')) "xy"
True
*Main> match1 (Cat (Let 'x') (Let 'y')) "x"
False
*Main> match1 (Cat (Let 'x') (Let 'y')) "y"
False
*Main> match1 (Cat (Let 'x') (Let 'y')) "xyz"
False
*Main> match1 (Union (Let 'x') (Let 'y')) "xyz"
False
*Main> match1 (Union (Let 'x') (Let 'y')) "xy"
False
*Main> match1 (Union (Let 'x') (Let 'y')) "x"
True
-}



match2 :: RegExp -> String -> Bool
match2 r w = match2' (r:[]) False w where
  match2' :: [RegExp] -> Bool -> String -> Bool
  match2' [] b w = (b == False) && (w == "")
  match2' (Empty:rs) b w = False
  match2' ((Let a):rs) b w
    | length w >= 1 = (Let a == toRE [head w]) && match2' rs False (tail(w))
    | otherwise = False
  match2' ((Union r1 r2):rs) b w = match2' (r1:rs) b w || match2' (r2:rs) b w
  match2' ((Cat r1 r2):rs) b w = match2' (r1:r2:rs) b w || (b == True) && byp(r1) && match2' (r2:rs) True w
  match2' ((Star r1):rs) b w = (b == False) && (match2' rs False w) || (match2' (r1:(Star r1):rs) True w)

{-
*Main> match2 Empty "abc"
False
*Main> match2 Empty "Hello"
False
*Main> match2 Empty "a"
False
*Main> match2 (Cat (Let 'x') (Let 'y')) "xy"
True
*Main> match2 (Cat (Let 'x') (Let 'y')) "x"
False
*Main> match2 (Cat (Let 'x') (Let 'y')) "y"
False
*Main> match2 (Cat (Let 'x') (Let 'y')) "xyz"
False
*Main> match2 (Union (Let 'x') (Let 'y')) "xyz"
False
*Main> match2 (Union (Let 'x') (Let 'y')) "xy"
False
*Main> match2 (Union (Let 'x') (Let 'y')) "x"
True
*Main> match2 (Union (Let 'x') (Let 'y')) "y"
True

-}


-- Some regular expressions for testing. Also, test them on other solutions
-- to the exercises of Section 3.2 (as many as you can get). 

sigma = ['a', 'b']                -- Alphabet used in all examples below

ab   = toRE "aa.bb.+*"            -- every letter is duplicated
ttla = toRE "ab+*a.ab+.ab+."      -- third to last letter is a
ena  = toRE "b*a.b*.a.*b*."       -- even number of a's
bb1  = toRE "aba.+*b.b.aab.+*."   -- contains bb exactly once


-- For your tests, you may also find the following helpful. For example,
-- you can generate all strings of length 10 (or 20) or less and then test
-- to see whether match1 r w == memb (lol w) (lang_of r) for each such w.

-- All strings on sigma of length <= n (useful for testing)
strings :: Int -> [String]
strings n = concatMap str [0..n] where
  str 0 = [""]
  str n = [a:w | a <- sigma, w <- str (n-1)]
