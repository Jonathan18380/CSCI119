--Jonathan Wong
--Csci 119
-- 1/29/2023
--Professor Wilson
---- CSci 119, Lab 1 ----

-- Instructions: replace all instances of "undefined" below with your answers
-- and then resubmit your file back to Canvas by the deadline

-- Notes on precedence and associativity:
-- * The operators ==, <, >, <=, and >= all have the SAME precedence,
--   and they are NON-ASSOCIATIVE (e.g., you can't write x < y < z)
-- * The operator == has a HIGHER precedence than either && or ||


---- Part 1: Boolean operators

-- The two truth values
bools = [True, False]

-- The following code tests whether "and" is commutative:
and_comm = and [(p && q) == (q && p) | p <- bools, q <- bools]

-- Write similar defintions that test whether "or" is commutative,
-- "and" and "or" are associative, "and" distributes over "or",
-- "or" distributes over "and". All of these should be True.
or_comm     = and  [(p || q) == (q || p) | p <- bools, q <- bools]
and_assoc   = and  [ (p && (q && r)) == ((p && q) && r) | p <- bools, q <- bools, r <- bools]
or_assoc    = and  [ (p || (q || r)) == ((p || q) || r) | p <- bools, q <- bools, r <- bools]
and_dist_or = and  [ (p && (q || r)) == ((p && q) || (p && r)) | p <- bools, q <- bools, r <- bools]
or_dist_and = and  [ (p || (q && r)) == ((p || q) && (p || r)) | p <- bools, q <- bools, r <- bools]
          
-- The exclusive-or operation on Bool in Haskell is equivalent to /=.
-- Test the properties of this operation (commutativity, associativity,
-- distributivity over and+or, and distributivity of and+or over it)
-- using the same method as above. Some of these are True, some are False. 
xor_comm     = and  [(p /= q) == (q /= p) | p <- bools, q <- bools]
xor_assoc    = and  [ (p /= (q /= r)) == ((p /= q) /= r) | p <- bools, q <- bools, r <- bools]
xor_dist_and = and  [ (p /= (q && r)) == ((p /= q) && (p /= r)) | p <- bools, q <- bools, r <- bools]
xor_dist_or  = and  [ (p /= (q || r)) == (p /= q) || (p /= r) | p <- bools, q <- bools, r <- bools]
and_dist_xor = and  [ (p && (q /= r)) == ((p && q) /= (p && r)) | p <- bools, q <- bools, r <- bools]
or_dist_xor  = and  [ (p || (q /= r)) == ((p || q) /= (p || r)) | p <- bools, q <- bools, r <- bools]
               
-- The implication operator on Bool in Haskell is equivalent to <=.
-- Test whether implication is associative or commutative. Spoiler:
-- both of these should be False.
assoc_imp = and  [ (p <= (q <= r)) == ((p <= q) <= r) | p <- bools, q <- bools, r <- bools]
comm_imp  = and  [(p <= q) == (q <= p) | p <- bools, q <- bools]


----- Part 2: Evaluating statements involving quantifiers

-- Assume that the universe of discourse is either the set
-- u1 = {1,2,3,4,5,6,7,8} or the set u2 = {5,2,17,58,21}; that is,
-- the word "number" temporarily means element of u1 (or u2).

u1 = [1..8]
u2 = [5, 2, 17, 58, 21]

-- Translate each of the statements 1 - 10 below, first, in a comment, to a
-- logical statement involving forall, exists, and, or, imp, and not,
-- and then into Haskell code that checks ("brute force") whether
-- the statement is true in a given universe u. Provide the results for
-- both u1 and u2. I'll do number 1, with two possible solutions.
-- You only need to provide one answer for each one.

-- 1. "Every number that's greater than 2 is greater than 1"
-- Formula: forall n, (n > 2) imp (n > 1)
prob1 u = and [(n > 2) <= (n > 1) | n <- u]
-- prob1 u1 --> True
-- prob1 u2 --> True

-- Another solution to problem 1 using a bounded quantifier:
prob1' u = and [n > 1 | n <- u, n > 2]

-- 2. Every number is either greater than 1 or less than 2
-- Formula: forall n, (n > 1) or (n < 2)
prob2 u = and [(n > 1) || (n < 2) | n <- u1]
-- prob2 u1 --> True
-- prob2 u2 --> True

-- 3. Every two numbers are comparable with <= (i.e., either one is <=
--    the other or vice-versa)
-- Formula: forall n, n imp n
prob3 u = and [ ( n <= n ) | n <- u1 ]
-- prob3 u1 --> True
-- prob3 u2 --> True

-- 4. There is an odd number greater than 4
-- A: exists odd n, n > 4
prob4 u = or [(n > 4) | n <- u1, odd n]
-- prob4 u1 --> True 
-- prob4 u2 --> True

-- 5: There are two odd numbers that add up to 10
-- Formula: exists odd n m, (n + m) == 10
prob5 u = or [ (n + m) == 10 | n <- u, m <- u, odd n, odd m] 
-- prob5 u1 --> True
-- prob5 u2 --> True

-- 6. For every odd number, there is a greater even number (use the Haskell
--    predicates odd, even :: Integral a => a -> Bool)
-- Formula: exists odd n even m, m > n
prob6 u = and [or[ ( m > n) | m <- u, n <- u, even m, odd n]]
-- prob6 u1 --> True
-- prob6 u2 --> True

-- 7. For every even number, there is a greater odd number
-- Formula: forall even n exists odd m, m > n
prob7 u = and [or[ ( m > n) | m <- u, n <- u, odd m, even n]]
-- prob7 u1 --> True
-- prob7 u2 --> True

-- 8. There are two odd numbers that add up to 6
-- Formula: exists odd n odd m, (m + n == 6)
prob8 u = or [( m + n == 6 ) | n <- u, m <- u, odd n, odd m]
-- prob8 u1 --> True
-- prob8 u2 --> False

-- 9. There is a number that is at least as large as every number
--    (i.e., according to >=)
-- Formula: exists n m, (n >= m)
prob9 u = or[(n >= m) | n <- u, m <- u]
-- prob9 u1 --> True
-- prob9 u2 --> True

-- 10. For every number, there is a different number such that there are no
--    numbers between these two.
-- Formula: forall n exists m, (m - n == 1)
prob10 u = and [ or [( m - n == 1 ) | n <- u, m <- u]]
-- prob10 u1 --> True
-- prob10 u2 --> False
