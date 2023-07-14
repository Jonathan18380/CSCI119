--Jonathan Wong

-- Lab 8: Additional constructions, nondeterministic machines

import Data.List
import Data.Array

-- Fixed alphabet, but everything below should work for any sigma!
sigma :: [Char]
sigma = "ab"

-- Recursive reimplementation of strings function from Lab 4
strings :: Int -> [String]
strings n = concat [strs i | i <- [0..n]] where
  strs 0 = [""]
  strs n = [a:xs | a <- sigma, xs <- strs (n-1)]

-- Finite state machines, now indexed by the type of their states
-- M = (states, start, finals, transitions)  
type FSM a = ([a], a, [a], a -> Char -> a)




fsm1 :: FSM Int
fsm1 = ([0,1,2], 0, [2], d)
  where d 0 'a' = 1
        d 1 'b' = 2
        d _ _   = 0

fsm2 :: FSM Int
fsm2 = ([0,1,2,3], 0, [3], d)
  where d 0 'a' = 1
        d 1 'b' = 2
        d 2 'c' = 3
        d _ _   = 0

fsm3 :: FSM Int
fsm3 = ([0,1,2,3], 0, [3], d)
  where d 0 'a' = 1
        d 1 'b' = 2
        d 2 'c' = 3
        d 3 'd' = 3
        d _ _   = 0








---------------- Given functions ----------------

-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

-- Cartesian product (preserves normalization)
(><) :: [a] -> [b] -> [(a,b)]
xs >< ys = [(x,y) | x <- xs, y <- ys]

-- Powerset  (preserves normalization)
power :: [a] -> [[a]]
power [] = [[]]
power (x:xs) = let ys = power xs
               in [] : map (x:) ys ++ tail ys

-- Check whether two lists overlap
overlap :: Eq a => [a] -> [a] -> Bool
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys

-- delta* construction
star :: (a -> Char -> a) -> (a -> [Char] -> a)
star = foldl'

-- Unary set closure (where "set" = normalized list)
-- uclosure xs g == smallest set containing xs and closed under g
uclosure :: Ord a => [a] -> (a -> [a]) -> [a]
uclosure xs g = sort $ stable $ iterate close (xs, []) where
  stable ((fr,xs):rest) = if null fr then xs else stable rest
  close (fr, xs) = (fr', xs') where
    xs' = fr ++ xs
    fr' = norm $ filter (`notElem` xs') $ concatMap g fr

-- reachable m == the part of m that is reachable from the start state
reachable :: Ord a => FSM a -> FSM a
reachable m@(qs, s, fs, d) = (qs', s, fs', d) where
  qs' = uclosure [s] (\q -> map (d q) sigma)
  fs' = filter (`elem` fs) qs'

-- Change the states of an FSM from an equality type to Int 
-- and use an array lookup for the transition function
intify :: Eq a => FSM a -> FSM Int
intify (qs, s, fs, d) = ([0..n-1], s', fs', d') where
  n = length qs
  m = length sigma
  s'  = ind qs s
  fs' = map (ind qs) fs
  arr = listArray ((0,0), (n-1,m-1)) [ind qs (d q a) | q <- qs, a <- sigma]
  d' q a = arr ! (q, ind sigma a)
  ind (q':qs) q = if q == q' then 0 else 1 + ind qs q

reduce :: Ord a => FSM a -> FSM Int
reduce = intify . reachable


---- Regular expressions, along with output and input
data RegExp = Empty
             | Let Char
             | Union RegExp RegExp
             | Cat RegExp RegExp
             | Star RegExp
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

-- Quick and dirty postfix regex parser, gives non-exaustive match on error
toRE :: String -> RegExp
toRE w = toRE' w [] where
  toRE' [] [r] = r
  toRE' ('+':xs) (r2:r1:rs) = toRE' xs (Union r1 r2:rs)
  toRE' ('.':xs) (r2:r1:rs) = toRE' xs (Cat r1 r2:rs)
  toRE' ('*':xs) (r:rs) = toRE' xs (Star r:rs)
  toRE' ('@':xs) rs = toRE' xs (Empty:rs)
  toRE' (x:xs) rs = toRE' xs (Let x:rs)






---------------- Part 1: Additional constructions ----------------
-- Define the operations given in Section 7 of the notes

-- Intersection
inters :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a,b)
inters (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d)
  where
    qs = qs1 >< qs2
    s = (s1, s2)
    fs = [(q1, q2) | q1 <- qs1, q2 <- qs2, q1 `elem` fs1, q2 `elem` fs2]
    d (q1, q2) a = (d1 q1 a, d2 q2 a)


-- Symmetric difference (xor)
symdiff :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a,b)
symdiff (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = qs1 >< qs2
  s = (s1, s2)
  fs = [(q1,q2) | q1 <- qs1, q2 <- qs2, (q1 `elem` fs1 && q2 `notElem` fs2) || (q1 `notElem` fs1 && q2 `elem` fs2)]
  d (q1,q2) a = (d1 q1 a, d2 q2 a)



-- Complement
compl :: Eq a => FSM a -> FSM a
compl (qs, s, fs, delta) = (qs, s, qs \\ fs, delta')
  where delta' q c = if q `elem` fs then complement (delta q c) else delta q c
        complement q = head (qs \\ [q])


-- Direct homomorphic image: k is a substitution
homo_dir :: (Char -> String) -> RegExp -> RegExp
homo_dir k Empty = Empty
homo_dir k (Let c) = h (k c)
  where
    h []     = Star Empty
    h (x:xs) = Cat (Let x) (h xs)
homo_dir k (Union r1 r2) = Union (homo_dir k r1) (homo_dir k r2)
homo_dir k (Cat r1 r2) = Cat (homo_dir k r1) (homo_dir k r2)
homo_dir k (Star r) = Star (homo_dir k r)


-- Inverse homomorphic image
homo_inv :: Eq a => (Char -> String) -> FSM a -> FSM a
homo_inv k (qs, s, fs, delta) = (qs, s, fs, delta')
  where delta' q c = head [q' | (c', q') <- delta_pairs, c' `elem` k c, q' `elem` qs]
        delta_pairs = [ (c, q) | q <- qs, c <- kmap q ]
        kmap q = norm [ c | c <- sigma, let str = k c, not (null str), delta q (head str) `elem` fs ]


-- Right quotient by a finite language
quot_right :: Eq a => [String] -> FSM a -> FSM a
quot_right k (state, start, final, delta) = (qs, s, fs, d) where
    qs = state
    s = start
    fs = [q | q <- state, or [elem (star d q w) final | w <- k]] 
    d q a = delta q a




---------------- Part 2: Nondeterministic machines ----------------

-- Nondeterministic FSMs, indexed by their type of state
-- All states are normalized and the output of d is normalized
-- M = (states, starts, finals, transitions)  
type Trans a = a -> Char -> [a]
type NFSM a = ([a], [a], [a], Trans a)

-- nap_hat d qs a == normalized list of all transitions possible from qs on a
nap_hat :: Ord a => Trans a -> [a] -> Char -> [a]
nap_hat d qs a = norm $ concat [d q a | q <- qs]


-- nap_hat_star d qs w == normalized list of transitions possible from qs on w
nap_hat_star :: Ord a => Trans a -> [a] -> [Char] -> [a]
nap_hat_star d qs w = star (nap_hat d) qs w


-- nacc m w == m accepd the string w
nacc :: Ord a => NFSM a -> [Char] -> Bool
nacc (qs, ss, fs, d) w = any (`elem` fs) (concatMap (nap_hat_star d ss) w')
  where w' = if null w then [[]] else map return w



--NFSM's
n1 = ([1, 2, 3], [1, 2, 3, 4, 5, 6], [3], d1)
  where
    d1 1 'a' = [2]
    d1 2 'b' = [3]
    d1 1 'd' = [2]
    d1 2 'e' = [3]
    d1 _ _ = []

n2 = ([1, 2], [1, 2], [2], d2)
  where
    d2 1 'a' = [2]
    d2 2 'b' = [2]
    d2 _ _   = [1]





-- Nondeterministic FSMs with epsilon moves, indexed by their type of state
-- M = (states, starts, finals, transitions, epsilon-moves)
type Eps a = [(a, a)]
type EFSM a = ([a], [a], [a], Trans a, Eps a)

-- Normalized epsilon closure of a set of states (Hint: use uclosure)
eclose :: Ord a => Eps a -> [a] -> [a]
eclose eps qs = uclosure qs (\q -> [q' | (p, q') <- eps, p == q])


-- eap_hat d es qs a == eclosure of transitions possible from qs on a
eap_hat :: Ord a => (Trans a, Eps a) -> [a] -> Char -> [a]
eap_hat (d, es) qs a = eclose es $ concatMap (\q -> eclose es $ d q a) qs


eacc :: Ord a => EFSM a -> [Char] -> Bool
eacc (qs, ss, fs, d, es) w = any (`elem` fs') (star step ss w)
  where fs' = eclose es fs
        step q a = eap_hat (d, es) q a




---------------- Part 3: Conversion between machines ----------------

-- Easy conversion from FSM to NFSM (given)

fsm_to_nfsm :: Eq a => FSM a -> NFSM a
fsm_to_nfsm (qs, s, fs, d) = (qs, [s], fs, nd)
  where
    nd q c = [d q c]



-- Conversion from NFSM to FSM by the "subset construction"
nfsm_to_fsm :: Ord a => NFSM a -> FSM [a]
nfsm_to_fsm (qs, s, fs, d) = (states, start, finals, delta)
  where
    subsets = power qs
    states = subsets
    start = s
    finals = filter (overlap fs) subsets
    delta qs' a = norm $ concatMap (`nap_hat` a) qs'
      where
        qs'' = norm qs'
        nap_hat q a' = if a == a' then d q a' else []



-- Similar conversion from EFSM to FSM using epsilon closure
efsm_to_fsm :: Ord a => EFSM a -> FSM [a]
efsm_to_fsm (qs, s, fs, d, es) = (qs', s', fs', d')
  where
    qs' = power qs
    s' = eclose es s
    fs' = [q | q <- qs', any (`elem` fs) q]
    d' q a = eclose es $ concatMap (\p -> d p a) q



delta_star :: Eq a => FSM a -> a -> [Char] -> a
delta_star (_, _, _, d) = foldl d
accept1 :: Eq a => FSM a -> [Char] -> Bool
accept1 m@(_, s, fs, _) w = elem (delta_star m s w) fs




nfsm1 = fsm_to_nfsm fsm1
nfsm2 = fsm_to_nfsm fsm2
nfsm3 = fsm_to_nfsm fsm3
newfsm1 = nfsm_to_fsm n1
newfsm2 = nfsm_to_fsm n2




{-
--Tests:

*Main> nacc nfsm1 "ab"
False
*Main> nacc (fsm_to_nfsm fsm1) "a"
False
*Main> nacc nfsm2 "ab"
False
*Main> nacc nfsm2 "a"
False


*Main> nacc (fsm_to_nfsm fsm2) "a"
True
*Main> nacc (fsm_to_nfsm fsm2) "b"
True
*Main> nacc (fsm_to_nfsm fsm2) "ab"
True
*Main> let fsm2 = compl fsm1
*Main> accept1 (fsm1) "a"
False
*Main> accept1 (fsm1) "lol"
False
*Main> accept1 (newfsm1) "lol"
False
*Main> accept1 (newfsm2) "lol"
False
*Main> accept1 (newfsm2) "bebebebe"
False
*Main> accept1 (newfsm2) "a"
True
*Main> accept1 (newfsm2) "ab"
True
*Main>



-}



{- Tests:










1. m and fsm_to_nfsm m accept the same strings
2. m and nfsm_to_fsm m accept the same strings
3. m and efsm_to_fsm m accept the same strings

-}
