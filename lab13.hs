--Jonathan Wong
import Data.List (foldl')
import Data.Char (isUpper)

-- CFG' G = (Start, Follows, Nullable)
type CFG' = (Char, Char -> Char -> [String], Char -> Bool)

close :: CFG' -> String -> [String]
close cfg@(_, _, e) s@(x:xs)
  | e x = s : close cfg xs
  | otherwise = [s]
close _ "" = [""]

lq :: CFG' -> Char -> String -> [String]
lq cfg@(s, d, e) a [] = []
lq cfg@(s, d, e) a (x:xs)
  | isUpper x = concatMap (\s -> close cfg (s ++ xs)) $ d x a
  | otherwise = if a == x then close cfg xs else []

accept' :: CFG' -> String -> Bool
accept' cfg@(s, d, e) = elem "" . foldl' (\xs c -> concatMap (lq cfg c) xs) (close cfg [s])

-- Balanced parentheses
-- Original:  S --> (S) | SS | ε
-- TNF + ε:   S --> (S) | (S)S  (S nullable)

bp' :: CFG'
bp' = ('S', d, e) where
  d 'S' '(' = ["S)", "S)S"]
  d 'S' ')' = []
  e 'S' = True

-- Original: S --> aS | aSbS | epsilon
-- TNF: S --> aS | aSbS | abS | aSb | ab | a
cfg5' :: CFG'
cfg5' = ('S', d, e) where
  d 'S' 'a' = ["S", "SbS","bS", "Sb","b" , []];
  d 'S' 'b' = [];
  e 'S' = True
  e _ = False

{-
*Main> accept' cfg5' "aaaaaabbbbbbbbbbbbbbbbbbbbb"
False
*Main> accept' cfg5' "aaaaaabbbbbbbb"
False
*Main> accept' cfg5' "aaaaaabbbb"
True
*Main> accept' cfg5' "aaaaaabb"
True
*Main> accept' cfg5' "abb"
False
*Main> accept' cfg5' "bb"
False
*Main> accept' cfg5' "aaabb"
True
*Main> accept' cfg5' "aaabbbbaa"
False
*Main> accept' cfg5' "aaaaaabbbbaa"
True
*Main> accept' cfg5' "aaaaaabbbbaaa"
True
*Main> accept' cfg5' "aaaaaabbbbbbbbbbbbbbbbaaa"
False
*Main>
-}


cfg6' :: CFG'
cfg6' = ('S', d, e) where
  d 'S' 'a' = ["Sa"]
  d 'S' 'b' = [[], "S"]
  e 'S' = True
  e  _ = False

{-
*Main> accept' cfg6' "aaaaaabbbbbbbbbbbbbbbbaaa"
False
*Main> accept' cfg6' "aba"
True
*Main> accept' cfg6' "abbbbbbbbbbbbbbbba"
True
*Main> accept' cfg6' "abbaa"
False
*Main> accept' cfg6' "aaa"
False
*Main> accept' cfg6' "ababa"
False
*Main> accept' cfg6' "aaabbaaa"
True
*Main> accept' cfg6' "aaabbbaaa"
True
*Main> accept' cfg6' "aaaaaabbbaaaaaa"
True
*Main> accept' cfg6' "aaaaaaaaaaabbbaaaaaaaaa"
False
*Main> accept' cfg6' "aaaaaaaaaaabbbaaaaaaaaaa"
False
*Main> accept' cfg6' "aaaaaaaaaaabbbaaaaaaaa"
False
-}



cfg2' :: CFG'
cfg2' = ('S', d, e) where
  d 'S' 'a' = ["U", "S", "T"]
  d 'S' 'b' = ["U", "S", "T"]
  d 'S' '0' = ["U"]
  d 'S' '1' = ["U", "S"]
  d 'S' '(' = ["S)", "S)S", "S)U", "S)T"]
  d 'S' ')' = []
  d 'S' '+' = []
  d 'S' '*' = []

  d 'U' '+' = ["S"]
  d 'U' '*' = []
  d 'U' 'a' = []
  d 'U' 'b' = []
  d 'U' '0' = []
  d 'U' '1' = []
  d 'U' '(' = []
  d 'U' ')' = []

  d 'T' '*' = ["S", "U"]
  d 'T' 'a' = []
  d 'T' 'b' = []
  d 'T' '0' = []
  d 'T' '1' = []
  d 'T' '(' = []
  d 'T' ')' = []
  d 'T' '+' = []

  e 'S' = True
  e  _ = False


{-
*Main> accept' cfg2' "ab"
True
*Main> accept' cfg2' "ab*"
True
*Main> accept' cfg2' "ab*(ba)"
True
*Main> accept' cfg2' "ab*(ba+b)"
True
*Main> accept' cfg2' "ab*(ba+b+bb)"
True
*Main> accept' cfg2' "ab*(ba+b+bb)*"
True
*Main> accept' cfg2' "ab*(ba+b+bb)*+aba"
True
*Main> accept' cfg2' "ab*(ba+b+bb)*+aba+1"
True
*Main>
-}