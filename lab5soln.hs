-- Lab 6: Convert regular expressions to FSMs
-- Contains a (generalized) solution to Lab 5

{-#LANGUAGE GADTs, StandaloneDeriving #-}   -- required for defn. of RegExp a

import Data.List (sort, subsequences, isInfixOf)

-- normalize a list, i.e., sort and remove (now adjacent) duplicates
norm :: Ord a => [a] -> [a]
norm = mynub . sort where
  mynub [] = []
  mynub [x] = [x]
  mynub (x:ys@(y:zs)) | x == y = mynub ys
                      | otherwise = x : mynub ys


-- Fixed alphabet, but everything below should work for any sigma!
sigma = ['a', 'b']   

-- Type of states for the machines accepting the empty set and single letter
data EmptyFSM = Etrap  deriving (Show, Eq, Ord)
data LetterFSM = Lstart | Lfinal | Ltrap  deriving (Show, Eq, Ord)

-- Regexps indexed by the type of the states of their associated FSMs;
-- all state types are orderable, even though that may not strictly be required
data RegExp a where
  Empty  :: RegExp EmptyFSM
  Letter :: Char -> RegExp LetterFSM
  Union  :: (Ord a, Ord b) => RegExp a -> RegExp b -> RegExp (a, b)
  Cat    :: (Ord a, Ord b) => RegExp a -> RegExp b -> RegExp (a, [b])
  Star   :: Ord a => RegExp a -> RegExp [a]
deriving instance Show (RegExp a)


---------------- Solution to Lab 5, ported to this datatype ----------------

-- Finite state machines indexed by the type of their states
-- (states, start, final, transitions)  
type FSM a = ([a], a, [a], [(a, Char, a)])

-- no_dups xs = "xs has no duplicates"
no_dups :: Eq a => [a] -> Bool
no_dups [] = True           
no_dups (x:xs) = not (elem x xs) && no_dups xs

-- subset xs ys == "xs is a subset of ys"
subset :: Eq a => [a] -> [a] -> Bool
subset [] ys = True
subset (x:xs) ys = elem x ys && subset xs ys

-- func3 as bs ts == "ts determines a function from (as x bs) to cs"
func3 :: (Eq a, Eq b, Eq c) => [a] -> [b] -> [c] -> [(a,b,c)] -> Bool
func3 as bs cs ts = and [single (thirds a b ts) cs | a <- as, b <- bs] where
  thirds a b ts = [c' | (a',b',c') <- ts, a' == a, b' == b]
  single [x] ys = elem x ys
  single _ _ = False

-- check whether a finite state machine is correct/complete:
checkFSM :: Eq a => FSM a -> Bool
checkFSM (qs, s, fs, d) = no_dups qs &&        -- (1)
                          elem s qs &&         -- (2)
                          subset fs qs &&      -- (3)
                          func3 qs sigma qs d  -- (4)


-- All functions below assume that the machine is correct

-- ap ts q a == the unique q' such that (q, a, q') is in ts;  assumes success
ap :: Eq a => [(a,Char,a)] -> a -> Char -> a 
ap ((q1, a1, q2):ts) q a | q1 == q && a1 == a = q2
                         | otherwise = ap ts q a

delta :: Eq a => FSM a -> a -> Char -> a
delta (_, _, _, d) = ap d

delta_star :: Eq a => FSM a -> a -> [Char] -> a
delta_star = foldl . delta

accept1 :: Eq a => FSM a -> [Char] -> Bool
accept1 m@(qs, s, fs, d) w = elem (delta_star m s w) fs

accept2_aux :: Eq a => FSM a -> a -> [Char] -> Bool
accept2_aux m@(_, _, fs, _) q [] = elem q fs
accept2_aux m q (a:w) = accept2_aux m (delta m q a) w

accept2 :: Eq a => FSM a -> [Char] -> Bool
accept2 m@(_, s, _, _) w = accept2_aux m s w


-- Solutions to exercises, using Ints as states (since that's what you had)

-- Exercise 5: every instance of aa coming before every instance of bb
-- Idea: accept everything up to the first bb, and then avoid aa after that.
-- Explanations of states:
--   0: have not yet read 'bb', previous letter (if any) an 'a'
--   1: have not yet read 'bb', just read one 'b'
--   2: have already read 'bb', previous letter a 'b'
--   3: have already read 'bb', just read one 'a'
--   4: trap state (have already read 'bb' and then 'aa')
ex5 :: FSM Int
ex5 = (qs, s, fs, d) where
  qs = [0..4]
  s  = 0
  fs = [0,1,2,3]
  d  = [(0,'a',0), (0,'b',1),
        (1,'a',0), (1,'b',2),
        (2,'a',3), (2,'b',2),
        (3,'a',4), (3,'b',2),
        (4,'a',4), (4,'b',4)]

-- Exercise 6: no instance of aba
-- Explanation of states:
--   0: previous letter (if any) a 'b'
--   1: just read 'a'
--   2: just read 'ab'
--   3: trap state (have already read 'aba')
ex6 :: FSM Int
ex6 = (qs, s, fs, d) where
  qs = [0..3]
  s  = 0
  fs = [0,1,2]
  d  = [(0,'a',1), (0,'b',0),
        (1,'a',1), (1,'b',2),
        (2,'a',3), (2,'b',0),
        (3,'a',3), (3,'b',3)]

-- Exercise 7: even number of a's and odd number of b's
-- Explanation of states:
--   0: even number of 'a's, even number of 'b's
--   1: even number of 'a's, odd  number of 'b's
--   2: odd  number of 'a's, even number of 'b's
--   3: odd  number of 'a's, odd  number of 'b's
ex7 :: FSM Int
ex7 = (qs, s, fs, d) where
  qs = [0..3]
  s  = 0
  fs = [1]
  d  = [(0,'a',2), (0,'b',1),
        (1,'a',3), (1,'b',0),
        (2,'a',0), (2,'b',3),
        (3,'a',1), (3,'b',2)]


---------------- Lab 6 begins here -----------------------------------------

-- Some helpful functions

(><) :: [a] -> [b] -> [(a,b)]              -- Cartesian product
xs >< ys = [(x,y) | x <- xs, y <- ys]   

overlap :: Eq a => [a] -> [a] -> Bool      -- overlap
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys

power :: [a] -> [[a]]
power = subsequences                       -- powerlist (imported)


-- Machine that accepts the empty language
emptyFSM :: FSM EmptyFSM
emptyFSM = ([Etrap], Etrap, [], [(Etrap, a, Etrap) | a <- sigma])

-- Machine that accepts the language {"a"} where a in sigma
letterFSM :: Char -> FSM LetterFSM
letterFSM = undefined
              
-- Machine that accepts the union of the languages accepted by m1 and m2
unionFSM :: (Ord a, Ord b) => FSM a -> FSM b -> FSM (a, b)
unionFSM = undefined

-- Machine that accepts the concatenation of the languages accepted by m1 and m2
catFSM :: (Ord a, Ord b) => FSM a -> FSM b -> FSM (a, [b])
catFSM = undefined

-- Machine that accepts the Kleene star of the language accepted by m1
starFSM :: Ord a => FSM a -> FSM [a]
starFSM = undefined

-- Convert a regular expression to a finite state machine
conv :: RegExp a -> FSM a
conv (Empty) = emptyFSM
conv (Letter c) = letterFSM c
conv (Union r1 r2) = unionFSM (conv r1) (conv r2)
conv (Cat r1 r2) = catFSM (conv r1) (conv r2)
conv (Star r1) = starFSM (conv r1)


-- One last machine to construct: the singleton-string language
-- Machine that accepts the language {w}, where w in Sigma^*
-- Build a mimimal machine for this language (not the one using catFSM)
-- Use any type you want in place of Int for your states
stringFSM :: [Char] -> FSM Int
stringFSM = undefined


-------------------------------------------------------------------------
-- Bonus feature:  a much more frugal conversion function that eliminates
-- unreachable states from the resulting machine. For you to play with.

-- reachable m == the part of m that is reachable from the start state
reachable :: Ord a => FSM a -> FSM a
reachable m@(qs, s, fs, d) = (qs', s, fs', d') where
  qs' = sort $ stable $ iterate close ([s], [])
  fs' = filter (`elem` qs') fs
  d'  = filter (\(q,_,_) -> q `elem` qs') d
  stable ((fr,qs):rest) = if null fr then qs else stable rest
  close (fr, xs) = (fr', xs') where
    xs' = fr ++ xs
    fr' = norm $ filter (`notElem` xs') (concatMap step fr)
    step q = map (ap d q) sigma

-- a better conversion
conv' :: RegExp a -> FSM a
conv' Empty = emptyFSM
conv' (Letter c) = letterFSM c
conv' (Union r1 r2) = reachable $ unionFSM (conv' r1) (conv' r2)
conv' (Cat r1 r2) = reachable $ catFSM (conv' r1) (conv' r2)
conv' (Star r1) = reachable $ starFSM (conv' r1)


