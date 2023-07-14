--Jonathan Wong
import Data.List (foldl')
import Data.Char (isUpper)

-- CFG G = (Start, Follows)
type CFG = (Char, Char -> Char -> [String])

accept :: CFG -> [Char] -> Bool
accept (s,d) = elem [] . foldl' (\xs c -> concatMap (lq c) xs) [[s]] where
  lq a [] = []
  lq a (x:xs) | isUpper x = map (++ xs) $ d x a          -- nonterminal
              | otherwise = if a == x then [xs] else []  -- terminal

-- Example 1: Balanced parentheses (not including the empty string)
-- original: S --> () | (S) | SS
-- in TNF:   S --> () | ()S | (S) | (S)S
bp :: CFG
bp = ('S', d) where
  d 'S' '(' = [")", ")S", "S)", "S)S"]
  d 'S' ')' = []



-- Example 2: {a^i b^j c^{i+j} | i >= 0, j > 0}
-- original: S --> aSc | T
--           T --> bTc | bc

-- in TNF:   S --> aSc | bTc | bc | ac
--           T --> bTc | bc
pl = ('S', d) where
  d 'S' 'a' = ["Sc","c"]  ;  
  d 'S' 'b' = ["Tc","c"]  ;  
  d 'S' 'c' = []
  d 'T' 'a' = []          ;  
  d 'T' 'b' = ["Tc","c"]  ;  
  d 'T' 'c' = []


--original: S --> aS | aSbS | epsilon
--in TNF: S --> aS | aSbS | abS | aSb | ab | a
cfg5 :: CFG
cfg5 = ('S', d) where
  d 'S' 'a' = ["S", "SbS","bS", "Sb","b" , []];
  d 'S' 'b' = [];



{-
*Main> accept cfg5 "aaaaaabbbbbbbbbbbbbbbbbbbbb"
False
*Main> accept cfg5 "aaaaaabbbbbbbb"
False
*Main> accept cfg5 "aaaaaabbbb"
True
*Main> accept cfg5 "aaaaaabb"
True
*Main> accept cfg5 "abb"
False
*Main> accept cfg5 "bb"
False
*Main> accept cfg5 "aaabb"
True
*Main> accept cfg5 "aaabbbb"
False
*Main> accept cfg5 "aaabbbba"
False
*Main> accept cfg5 "aaabbbbaa"
False
*Main> accept cfg5 "aaabbbaa"
True
*Main> accept cfg5 "aaaaaaaaabbbaa"
True
*Main> accept cfg5 "aaaaaaaaabbbbaa"
True
*Main> accept cfg5 "aaaaaaaaabbbbbaa"
True
*Main> accept cfg5 "aaaaaaaaabbbbbaabb"
True
*Main> accept cfg5 "aaaaaaaaabbbbbaabbbbb"
True
*Main> accept cfg5 "aaaaaaaaabbbbbaabbbbbbbbbbbbbbbbbbb"
False
*Main>
-}



--Original: S -->B1 | bS
--          B1 --> aSa | B2
--          B2 --> b
--TNF:      S --> aSa | bS | b

cfg6 :: CFG
cfg6 = ('S', d) where
  d 'S' 'a' = ["Sa"];
  d 'S' 'b' = [[], "S"];

{-
*Main> accept cfg6 "aabaa"
True
*Main> accept cfg6 "aaaa"
False
*Main> accept cfg6 "b"
True
*Main> accept cfg6 "aabb"
False
*Main> accept cfg6 "aabba"
False
*Main> accept cfg6 "aabbaa"
True
*Main> accept cfg6 "aaaaaabbaaaaaa"
True
*Main> accept cfg6 "aaaaabbaaaaa"
True
*Main> accept cfg6 "aaaaaaaaaa"
False
*Main> accept cfg6 ""
False
*Main> accept cfg6 "aaaabaaaa"
True
*Main> accept cfg6 "aaaaaaaaaaaaaaaaaaaaaaaaaabaaaaaaaaaaaaaaaaaaaaaaaaaa"
True
*Main>
-}








--Original: S--> U | epsilon
--          E--> a|b|U|1|S
--          C--> CE|CT|E|T
--          U--> C+U|C
--          T-->E*

--TNF:      S--> a | b | 0 | 1 | (S) | aS | bS | 1S | (S)S | aU | bU | 0U | 1U | (S)U | aT | bT | (S)T
--          U--> +S
--          T--> * | *S | *U

{-
cfg2 :: CFG
cfg2 = ('S', d) where
  d 'S' 'a' = [[], "U", "S", "T"];
  d 'S' 'b' = [[], "U", "S", "T"];
  d 'S' '0' = [[], "U"];
  d 'S' '1' = [[], "U", "S"];
  d 'S' '(' = ["S)", "S)S", "S)U", "S)T"];
  d 'S' ')' = [];
  d 'S' '+' = [];
  d 'S' '*' = [];

  d 'U' '+' = ["S"];
  d 'U' '*' = [];
  d 'U' 'a' = [];
  d 'U' 'b' = [];
  d 'U' '0' = [];
  d 'U' '1' = [];
  d 'U' '(' = [];
  d 'U' ')' = [];

  d 'T' '*' = [[], "S", "U"];
  d 'T' 'a' = [];
  d 'T' 'b' = [];
  d 'T' '0' = [];
  d 'T' '1' = [];
  d 'T' '(' = [];
  d 'T' ')' = [];
  d 'T' '+' = [];
-}



cfg2 :: CFG
cfg2 = ('S', d) where
  d 'S' 'a' = [[], "E", "C", "S"]
  d 'S' 'b' = [[], "E", "C", "S"]
  d 'S' '1' = [[]]
  d 'S' '(' = ["S)", "S)S", "S)C", "E)S", "E)C"]

  d 'E' '+' = ["E", "S"]
  d 'C' '*' = ["E", "C", [], "S"]

  d _ _ = []





{-
*Main> accept cfg2 "ab"
True
*Main> accept cfg2 "aba"
True
*Main> accept cfg2 "aba*"
True
*Main> accept cfg2 "ab*"
True
*Main> accept cfg2 "ab*(ba+b+bb)"
True
*Main> accept cfg2 "ab*(ba+b+bb)*"
True
*Main> accept cfg2 "ab*(ba+b+bb)*+aba"
True
*Main> accept cfg2 "ab*(ba+b+bb)*+aba+1"
True
*Main> accept cfg2 ""
False
*Main> accept cfg2 "abc"
*** Exception: lab12.hs:(144,3)-(170,16): Non-exhaustive patterns in function d

*Main>
-}







