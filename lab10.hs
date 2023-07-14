--Jonathan Wong (3rd attempt)
-- Lab 10: FSM Minimization
import Data.List
import Data.Array



-----------------------Code from previous labs--------------------------------
-- Fixed alphabet, but everything below should work for any sigma!
sigma :: [Char]
sigma = "ab"

-- FSM definition
-- M = (states, start, finals, transitions)  
type FSM a = ([a], a, [a], a -> Char -> a)


--NFSM definition
-- M = (states, starts, finals, transitions)  
type Trans a = a -> Char -> [a]
type NFSM a = ([a], [a], [a], Trans a)

-- Cartesian product
(><) :: [a] -> [b] -> [(a,b)]
xs >< ys = [(x,y) | x <- xs, y <- ys]


norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

uclosure :: Ord a => [a] -> (a -> [a]) -> [a]
uclosure xs g = sort $ stable $ iterate close (xs, []) where
  stable ((fr,xs):rest) = if null fr then xs else stable rest
  close (fr, xs) = (fr', xs') where
    xs' = fr ++ xs
    fr' = norm $ filter (`notElem` xs') $ concatMap g fr
                    


------------------------------------------------------------------------------






-- Boolean binary operation on FSMs. Examples:
-- binopFSM (||) m1 m2 computes union machine
-- binopFSM (&&) m1 m2 computes intersection machine
type BoolOp = Bool -> Bool -> Bool

binopFSM :: (Eq a, Eq b) => BoolOp -> FSM a -> FSM b -> FSM (a,b)
binopFSM op (qs1,s1,fs1,d1) (qs2,s2,fs2,d2) = (qs,s,fs,d) where
    qs = qs1 >< qs2
    s  = (s1,s2)
    fs = [(q1,q2) | (q1,q2) <- qs, op (q1 `elem` fs1) (q2 `elem` fs2)]
    d (q1,q2) a = (d1 q1 a, d2 q2 a)

-- Reverse FSM to a NFSM. Output machine accepts reverse of language of input machine.
reverseFSM :: Eq a => FSM a -> NFSM a
reverseFSM m@(qs1,s1,fs1,d1) = (qs,s,fs,d) where
    qs = qs1
    s  = fs1 --Start becomes final
    fs = [s1] --Final becomes start
    d q a = [q' | q' <- qs1, q == d1 q' a]

-- Reachable states of a NFSM (similar to reachable but on NFSMs)
nreachable :: Ord a => NFSM a -> [a]
nreachable m@(qs,s,fs,d) = uclosure s f where
    f q = norm $ concatMap (d q) sigma 


minimize :: Ord a => FSM [a] -> FSM [a]
minimize (qs, s, fs, d) = (qs', s', fs', d') where
  xor = binopFSM (/=) fsm fsm
  revrs = reverseFSM xor
  nreach = nreachable revrs
  compl = [(q1, q2) | q1 <- qs, q2 <- qs, (q1, q2) `notElem` nreach]
  rep r = minimum [q2 | (q1, q2) <- compl, q1 == r]
  qs' = nub $ map rep qs
  s' = rep s
  fs' = intersect qs' fs
  d' q a = rep (d q a)
  fsm = (qs, s, fs, d)



-- Test. For example, make sure that the minimal machine agrees with the original machine
-- on lots of input strings. Try for multiple machines.

{-
*Main> qs1 = ["", "a", "b", "aa", "ab", "ba", "bb"]
*Main> d1 q c = if length q < 2 then q ++ [c] else tail (q ++ [c])
*Main> [(q,a,d1 q a) | q <- qs1, a <- sigma]
[("",'a',"a"),("",'b',"b"),("a",'a',"aa"),("a",'b',"ab"),("b",'a',"ba"),("b",'b',"bb"),("aa",'a',"aa"),("aa",'b',"ab"),("ab",'a',"ba"),("ab",'b',"bb"),("ba",'a',"aa"),("ba",'b',"ab"),("bb",'a',"ba"),("bb",'b',"bb")]
*Main> m = (qs1, "", ["ab"], d1) :: FSM String
*Main> (qs,s,fs,d) = minimize m
*Main> qs
["","a","ab"]
*Main> s
""
*Main> fs
["ab"]
*Main> [(q,a,d q a) | q <- qs, a <- sigma]
[("",'a',"a"),("",'b',""),("a",'a',"a"),("a",'b',"ab"),("ab",'a',"a"),("ab",'b',"")]




*Main> qs1 = ["", "a", "b", "aa"]
*Main> d1 q c = if length q < 2 then q ++ [c] else tail (q ++ [c])
*Main> [(q,a,d1 q a) | q <- qs1, a <- sigma]
[("",'a',"a"),("",'b',"b"),("a",'a',"aa"),("a",'b',"ab"),("b",'a',"ba"),("b",'b',"bb"),("aa",'a',"aa"),("aa",'b',"ab")]
*Main> m = (qs1, "", ["ab"], d1) :: FSM String
*Main> (qs,s,fs,d) = minimize m
*Main> qs
[""]
*Main> s
""
*Main> fs
[]
*Main> [(q,a,d q a) | q <- qs, a <- sigma]
[("",'a',""),("",'b',"")]
*Main>
*Main>





*Main> qs1 = ["", "a", "b", "aa", "ab"]
*Main> d1 q c = if length q < 2 then q ++ [c] else tail (q ++ [c])
*Main> [(q,a,d1 q a) | q <- qs1, a <- sigma]
[("",'a',"a"),("",'b',"b"),("a",'a',"aa"),("a",'b',"ab"),("b",'a',"ba"),("b",'b',"bb"),("aa",'a',"aa"),("aa",'b',"ab"),("ab",'a',"ba"),("ab",'b',"bb")]
*Main> m = (qs1, "", ["ab"], d1) :: FSM String
*Main> (qs,s,fs,d) = minimize m
*Main> qs
["","a","ab"]
*Main> s
""
*Main> fs
["ab"]
*Main> [(q,a,d q a) | q <- qs, a <- sigma]
[("",'a',"a"),("",'b',""),("a",'a',"a"),("a",'b',"ab"),("ab",'a',"*** Exception: Prelude.minimum: empty list




*Main> qs1 = [""]
*Main> d1 q c = if length q < 2 then q ++ [c] else tail (q ++ [c])
*Main> [(q,a,d1 q a) | q <- qs1, a <- sigma]
[("",'a',"a"),("",'b',"b")]
*Main> m = (qs1, "", ["ab"], d1) :: FSM String
*Main> (qs,s,fs,d) = minimize m
*Main> qs
[""]
*Main> s
""
*Main> fs
[]
*Main> [(q,a,d q a) | q <- qs, a <- sigma]
[("",'a',"*** Exception: Prelude.minimum: empty list
*Main>



-}




