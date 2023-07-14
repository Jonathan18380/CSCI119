--Jonathan Wong

-- CSci 119, Lab 5
-- Reference: Lecture notes, Sections 4.1, 4.2

import Data.List (nub, isInfixOf, isSuffixOf)  -- useful for testing in Part 2

-- Again, for this (and most) labs, the alphabet will be {a,b} to keep testing
-- easier, but your code should work just as well for any finite list.
sigma = ['a', 'b']

-- Finite State Machine M = (Q, s, F, d) with integer states
type FSM = ([Int], Int, [Int], Int -> Char -> Int)


---------------- Part 1: Representing FSMs

-- Check whether a finite state machine (qs, s, fs, d) is correct/complete:
-- (1) States qs are unique (no duplicates)
-- (2) Start state is a state (s is in qs)
-- (3) Final states are states (fs is a subset of qs)
-- (4) Transition function d gives a state in qs for every state in qs and
--     letter from sigma

--Clears all 4 checks for checkFSM
fsm1 :: FSM
fsm1 = ([0,1,2], 0, [2], d)
    where d 0 'a' = 1
          d 0 'b' = 0
          d 1 'a' = 1
          d 1 'b' = 2
          d 2 'a' = 2
          d 2 'b' = 2



--Violates second check for checkFSM (3 is not an element in [0,1,2])
fsm2 :: FSM
fsm2 = ([0,1,2], 3, [2], d)
    where d 0 'a' = 1
          d 0 'b' = 0
          d 1 'a' = 1
          d 1 'b' = 2
          d 2 'a' = 2
          d 2 'b' = 2

--True
--Has 2 final states ( [1,2] )
fsm3 :: FSM
fsm3 = ([0,1,2,3], 0, [1,2], d)
    where d 0 'a' = 1
          d 0 'b' = 0
          d 1 'a' = 1
          d 1 'b' = 2
          d 2 'a' = 3
          d 2 'b' = 2
          d 3 'a' = 1
          d 3 'b' = 2


checkFSM :: FSM -> Bool
checkFSM (qs, s, fs, d) =
    length qs == length (nub qs) &&
    s `elem` qs &&                   
    all (`elem` qs) fs &&            
    all (\q -> all (\c -> d q c `elem` qs) sigma) qs  


{-
*Main> checkFSM fsm1
True
*Main> checkFSM fsm2
False
*Main> checkFSM fsm3
True
-}


-- Gives the delta* function (recursive in w)
-- dstar will compute the state that a FSM will be in after processing the input string.


dstar :: FSM -> Int -> [Char] -> Int
dstar _ q [] = q  
dstar m q (x:xs) = dstar m (d q x) xs  
    where (_, _, _, d) = m 



{-
*Main> dstar fsm3 0 "abaa"
1
*Main> dstar fsm2 3 "bb"
*** Exception: lab5.hs:(37,11)-(42,21): Non-exhaustive patterns in function d

*Main> dstar fsm1 0 "a"
1
*Main> dstar fsm2 0 "a"
1
*Main> dstar fsm2 3 "bb"
*** Exception: lab5.hs:(37,11)-(42,21): Non-exhaustive patterns in function d

*Main> dstar fsm2 2 "bb"
2
*Main> dstar fsm3 0 "abb"
2
*Main> dstar fsm3 0 "abaa"
1
*Main> dstar fsm2 1 "bab"
2
*Main>
-}


-- Machine acceptance, Definition 1 (via delta*)
accept1 :: FSM -> [Char] -> Bool
accept1 m w = let (_, s, f, d) = m
                  finalState = dstar m s w
              in finalState `elem` f




{-
*Main> accept1 fsm1 "abba"
True
*Main> accept1 fsm1 "aba"
True
*Main> accept1 fsm1 "b"
False
*Main> accept1 fsm1 "ba"
False
*Main> accept1 fsm1 "babb"
True
*Main> accept1 fsm2 "bb"
*** Exception: lab5.hs:(37,11)-(42,21): Non-exhaustive patterns in function d

*Main> accept1 fsm2 "a"
*** Exception: lab5.hs:(37,11)-(42,21): Non-exhaustive patterns in function d

*Main> accept1 fsm3 "aba"
False
*Main> accept1 fsm3 "abaa"
True
*Main> accept1 fsm3 "ababa"
False
*Main> accept1 fsm3 "ababaa"
True
*Main> accept1 fsm3 "abaabaa"
True
*Main>

-}


-- Machine acceptance, Definition 2 (via L_q(M))

accept2 :: FSM -> [Char] -> Bool
accept2 (qs, s, fs, d) w = aux s w
  where
    -- aux q w = whether the machine, starting in q, accepts w (recursive in w)
    aux :: Int -> [Char] -> Bool
    aux q [] = q `elem` fs  
    aux q (x:xs) = aux (d q x) xs  



{-
*Main> accept2 fsm1 "ab"
True
*Main> accept2 fsm1 "a"
False
*Main> accept2 fsm2 "abc"
*** Exception: lab5.hs:(37,11)-(42,21): Non-exhaustive patterns in function d
*Main> accept2 fsm3 "ab"
True
*Main> accept2 fsm3 "a"
True
*Main> accept2 fsm3 "ababa"
False
*Main> accept2 fsm3 "abababab"
True
*Main> accept2 fsm3 "ababababaaaa"
True
*Main> accept2 fsm3 "ababababaaaab"
True
-}









---------------- Part 2: FSM construction

-- Define a machine that accepts exactly the strings with an odd number of b's
-- (Solution given for illustration)
oddbs :: FSM
oddbs = ([0,1], 0, [1], d) where
  d q 'a' = q        -- stay in the same state
  d q 'b' = 1 - q    -- switch states

-- Define a machine that accepts exactly the strings that do not contain "aab"
-- as a substring and test it adequately

avoid_aab :: FSM
avoid_aab = ([0,1], 0, [0], d) where
  d q 'a' = if q == 0 then 1 else if q == 1 then 1 else 0
  d q 'b' = if q == 0 then 0 else if q == 1 then 0 else 0


{-
*Main> accept1 avoid_aab "aab"
True
*Main> accept1 avoid_aab "aab"
True
*Main> accept1 avoid_aab "aaba"
False
*Main> accept1 avoid_aab "aabaa"
False
*Main> accept1 avoid_aab "aabab"
True
*Main> accept1 avoid_aab "babab"
True
*Main> accept1 avoid_aab "babaab"
True
-}



-- Define a machine that accepts all strings that end in "ab" and test
end_ab :: FSM
end_ab = ([0,1,2], 0, [2], d)
  where
    d q 'a' = if q == 0 then 1 else if q == 1 then 0 else 1
    d q 'b' = if q == 1 then 2 else 0

{-
*Main> accept1 end_ab "bab"
True
*Main> accept1 end_ab "babb"
False
*Main> accept1 end_ab "babba"
False
*Main> accept1 end_ab "babbab"
True
*Main> accept1 end_ab "babbaba"
False
*Main> accept1 end_ab "babbabab"
True
*Main> accept2 end_ab "abba"
False
*Main> accept2 end_ab "abab"
True
*Main> accept2 end_ab "ababaa"
False
-}


-- Define a function that takes a string and returns a machine that accepts
-- exactly that string and nothing else (compare to 'onestr' from Lab 3)
-- Hint: the expression w !! i gives the i-th character of the string w

exactly :: String -> FSM
exactly w = (qs, 0, [n], d)
  where qs = [0..n]
        n = length w
        d q c
          | q < n && w !! q == c = q + 1
          | otherwise = 0


{-
*Main> let fsm4 = exactly "abc"
*Main> accept1 fsm4 "abc"
True
*Main> accept1 fsm4 "ab"
False
*Main> accept1 fsm4 "abcd"
False
*Main> accept1 fsm4 "acd"
False
*Main> accept1 fsm4 "ad"
False
*Main> accept1 fsm4 "abc"
True
-}



-- Test the machines above. Also, try out the exerices at the end of Section 3.2
-- in my notes as FSMs. Do they produce the same results as your RegExp's did?

-- Recursive reimplementation of strings function from Lab 4
strings :: Int -> [String]
strings n = concat [strs i | i <- [0..n]] where
  strs 0 = [""]
  strs n = [a:xs | a <- sigma, xs <- strs (n-1)]

s10 = strings 10  -- or larger, if you like

-- Example test for the oddbs machine above
oddbs_test = and [accept1 oddbs w == odd (num_bs w) | w <- s10] where
  num_bs w = sum (map (\x -> if x == 'b' then 1 else 0) w)
  
