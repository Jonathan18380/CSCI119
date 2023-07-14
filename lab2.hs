----Jonathan Wong

---- CSci 119, Spring 2021, Lab 2 ----
import Data.List

----- PART 1:  Testing properties of relations -----

-- As in Lab 1, we will be working with the finite universe U = [1..8],
-- but your code should work with any universe.
u = [1..8]

-- A relation, R, on U is a list of the ordered pairs of elements of U:
type Reln = [(Int,Int)]
              
-- For example, here are the < and <= relations
less_reln :: Reln
less_reln = [(i,j) | i <- u, j <- u, i < j]

leq_reln :: Reln
leq_reln  = [(i,j) | i <- u, j <- u, i <= j]
            
-- and here is the relation of equivalence mod 3:
eqmod3_reln :: Reln
eqmod3_reln = [(i,j) | i <- u, j <- u, (j - i) `mod` 3 == 0]


-- Write a function refl that tests whether a relation is reflexive:
-- R is reflexive if: forall a, (a,a) in R
-- Example: [(i,i) | i <- u] is the smallest reflexive relation over u.
-- Anything that does not contain all of these 8 elements is not reflexive.
refl :: Reln -> Bool
refl rs = and [ (a,a) `elem` rs | (a,b) <- rs ]

-- Write a function symm that tests whether a relation is symmetric:
-- R is symmetric if: forall a b, (a,b) in R -> (b,a) in R
-- Example: [(1,1), (1,2), (2,1)] is symmetric but [(1,1), (1,2)] is not.
symm :: Reln -> Bool
symm rs = and [ (b,a) `elem` rs | (a,b) <- rs ]

-- Write a function trans that tests whether a relation is transitive:
-- R is transistive if: forall a b c, ((a,b) in R /\ (b,c) in R) -> (a,c) in R
-- Example: [(1,2),(2,3),(1,3),(4,4)] is transitive but [(2,3),(3,2)] is not
trans :: Reln -> Bool
trans rs = and [ (a,c) `elem` rs | (a,b) <- rs , (b1,c) <- rs, (a,b1) `elem` rs , b==b1]


-- Use the functions above to check the less, leq, and eqmod3 relations for
-- relexivity, symmetry, and transitivity.


----- PART 2:  Finding minimal relations with combinations of properties -----

-- For the following problems, you can assume that u = [1..8].
--
-- For each of the 8 possible combinations of yes/no on reflexivity,
-- symmetry, and transitivity, find a MINIMAL relation on u that has exactly
-- that combination of properties. Add a test to check whether you got the
-- properties right. (I'll do the first one as an example.)

-- refl, symm, trans
rst :: Reln
rst = [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (8,8)]
rst_test = refl rst && symm rst && trans rst

-- refl, symm, not trans
rst' :: Reln
rst' = [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (8,8), (1,4), (4,1), (2,5), (5,2)]
rst'_test = refl rst' && symm rst' /= trans rst'

-- refl, not symm, trans
rs't :: Reln
rs't = [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (8,8), (2,4), (4,5), (2,5)]
rs't_test = refl rs't && trans rs't /= symm rs't

-- refl, not symm, not trans
rs't' :: Reln
rs't' = [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (8,8), (2,4), (4,6), (3,7)]
rs't'_test = trans rs't' /= symm rs't' && refl rs't'

-- not refl, symm, trans
r'st :: Reln
r'st = []
r'st_test = symm r'st' /= trans r'st' || refl r'st'

-- not refl, symm, not trans
r'st' :: Reln
r'st' = [(1,2), (2,1)]
r'st'_test = trans r'st' /= refl r'st' || symm r'st'

-- not refl, not symm, trans
r's't :: Reln
r's't = [(1,2), (2,3), (1,3)]
r's't_test = trans r's't /= symm r's't || refl r's't

-- not refl, not symm, not trans
r's't' :: Reln
r's't' = [(1,1), (1,2), (2,3)]
r's't'_test = not(refl r's't) && not(symm r's't) && not(trans r's't)


---- PART 3: Partitions of u -----

-- Again, the functions in this part should work with any finite universe, u

-- A partitition, P, of u is a list of blocks, each of which are lists of
-- elements of u, that satisfies these conditions:
-- nontrivial: forall X in P, exists x in U, x in X;
--             equivalently, [] not in P
nontrivial :: [[Int]] -> Bool
nontrivial xs = or [null (ys) | ys <- xs]

-- total:      forall x in U, exists X in P, x in X
total :: [[Int]] -> Bool
total xs = and [or [x `elem` ys | ys <- xs] | x <- u] 


-- disjoint:   forall X,Y in P (exists a, a in X /\ a in Y) -> X = Y,
--             equivalently, forall X,Y in P, X /= Y -> X intersect Y = []

disjoint :: [[Int]] -> Bool
disjoint xs = and [or [not(a `elem` ys) | a <- zs] | zs <- xs, ys <- xs, ys /= zs]



-- For example, here is the partitition of u = [1..8] corresponding to
-- eqmod3_reln:
eqmod3_part :: [[Int]]
eqmod3_part = [[1,4,7], [2,5,8], [3,6]]

-- Write a function, part, that tests whether a list of lists is a partition
-- of u
part :: [[Int]] -> Bool
part bs = total bs && disjoint bs /= nontrivial bs
          

-- Write a function eq2part that takes an equivalence relation on u as input
-- and returns the associated partition of u. You can assume that the input is
-- really an equivalence relation on u (i.e., you do not need to check this).

--eq2part :: Reln -> [[Int]]
--eq2part rs = nub [[d | (c,d) <- rs, a == c] | (a,b) <- rs]
eq2part :: Reln -> [[Int]]
eq2part rs = help u where
help [] = []
help (x:xs) = eqclass x:help
eqclass x = 

-- Write a function part2eq that takes a partition of u as input and returns
-- the associated equivalence relation on u. You can assume that the argument
-- is really a partition of u.
part2eq :: [[Int]] -> Reln
part2eq bs = [(x,y) | cs <- bs, x <- cs, y <- cs]
