-- CSci 119, Lab 2 --  Simran Arora ———
-- See https://piazza.com/class/hz53js0sjhm44z?cid=20 for definitions

import Data.List (sort, intersect)

-- normalize a list, i.e., sort and remove (now adjacent) duplicates
norm :: Ord a => [a] -> [a]
norm = mynub . sort where
  mynub [] = []
  mynub [x] = [x]
  mynub (x:ys@(y:zs)) | x == y = mynub ys
                      | otherwise = x : mynub ys

-- Invariant: Lists, when treated as sets, should be (recursively) normalized.
-- In particular, your functions should assume that all inputs are normalized,
-- and should insure that all outputs are normalized.
--------------------------------------------------------------------------------


-- Universe of discourse: this is being set to [1..4], but everything below
-- should be defined in terms of u and should work for any (finite, normalized)
-- list of Ints (including [])
u = [1..4]


-- eqrel r == True, if r is an equivalence relation on u, False otherwise
-- (you may assume that r is a relation on u)
eqrel :: [(Int,Int)] -> Bool
eqrel r = and[ elem (a,a) r | a <- u ] &&  and[ elem (y,x) r | (x,y) <-r] &&      		    and[ elem (x,z) r | (x,y1) <- r,(y2,z)<-r,y1==y2]

-- part p == True, if p is a partition of u, False otherwise
-- (you may assume that every element of concat p is an element of u)
part :: [[Int]] -> Bool
part p = and[or[x `elem` xs | ps <- u ,x <- u ,xs <- u,xs <- ps]] && and[or[xs `elem` ps && a `elem` xs | ps <-u, xs <-u, a <- u]] && and[and[xs == ys || xs `intersect` ys == [] | ps <-u, xs <- u, ys <- u,xs <- ps && ys <- ps]] 
 
-- eq_to_p r == the partition associated to r
-- (you may assume eqrel r == True)
eq_to_p :: [(Int,Int)] -> [[Int]]
eq_to_p r = [f(x) | x<-u] 
            where f(x) = [b| (a,b)<-r]

-- p_to_eq p == the equivalence relation associated to p
-- (you may assume part p == True)
p_to_eq :: [[Int]] -> [(Int,Int)]
p_to_eq p = [(a,b) | xs <-ps , a<-ps , b<-ps]

-- Test, on a "good" collection of cases, the equalities
--    p_to_eq (eq_to_p r) == r
--    eq_to_p (p_to_eq p) == p
