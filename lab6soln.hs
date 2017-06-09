-- Lab 6 solution

{-#LANGUAGE GADTs, StandaloneDeriving #-}   -- required for defn. of RegExp a

import Data.List (nub, sort, subsequences, inits, isPrefixOf, isInfixOf)

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
                                             
-- Regular expressions indexed by the state-type of their associated FSMs
data RegExp a where
  Empty  :: RegExp EmptyFSM
  Letter :: Char -> RegExp LetterFSM
  Union  :: (Ord a, Ord b) => RegExp a -> RegExp b -> RegExp (a, b)
  Cat    :: (Ord a, Ord b) => RegExp a -> RegExp b -> RegExp (a, [b])
  Star   :: Ord a => RegExp a -> RegExp [a]
deriving instance Show (RegExp a)


-- Finite state machines indexed by the type of their states
-- (states, start, final, transitions)  
type FSM a = ([a], a, [a], [(a, Char, a)])

-- ap ts q a == the unique q' such that (q, a, q') is in ts;  assumes success
ap :: Eq a => [(a,Char,a)] -> a -> Char -> a 
ap ((q1, a1, q2):ts) q a | q1 == q && a1 == a = q2
                             | otherwise = ap ts q a

---------------- Lab 6 begins here -----------------------------------------

-- Some helpful functions

(><) :: [a] -> [b] -> [(a,b)]              -- Cartesian product
xs >< ys = [(x,y) | x <- xs, y <- ys]   

overlap :: Eq a => [a] -> [a] -> Bool      -- have inhabited intersection
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys

power :: [a] -> [[a]]
power = subsequences                       -- powerlist (imported)


-- Machine that accepts the empty language
emptyFSM :: FSM EmptyFSM
emptyFSM = ([Etrap], Etrap, [], [(Etrap, a, Etrap) | a <- sigma])

-- Machine that accepts the language {"a"} where a in sigma
letterFSM :: Char -> FSM LetterFSM
letterFSM a = ([Lstart, Lfinal, Ltrap], Lstart, [Lfinal],
              [(q, a', if q == Lstart && a' == a then Lfinal else Ltrap) |
               q <- [Lstart, Lfinal, Ltrap], a' <- sigma])
              
-- Machine that accepts the union of the languages accepted by m1 and m2
unionFSM :: (Ord a, Ord b) => FSM a -> FSM b -> FSM (a, b)
unionFSM (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = qs1 >< qs2
  s = (s1, s2)
  fs = [q | q <- qs, elem (fst q) fs1 || elem (snd q) fs2]
  d  = [(q, a, step q a) | q <- qs, a <- sigma]
  step (q1, q2) a = (ap d1 q1 a, ap d2 q2 a)

-- Machine that accepts the concatenation of the languages accepted by m1 and m2
catFSM :: (Ord a, Ord b) => FSM a -> FSM b -> FSM (a, [b])
catFSM (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = qs1 >< power qs2
  -- or: [(q1,x2) | q1 <- qs1, x2 <- power qs2, notElem q1 fs1 || elem s2 x2]
  s = (s1, [s2 | elem s1 fs1])
  fs = [q | q <- qs, overlap (snd q) fs2]
  d  = [(q, a, step q a) | q <- qs, a <- sigma]
  step (q1, x2) a = (q1', x2') where
    q1' = ap d1 q1 a
    x2' = norm $ [s2 | elem q1' fs1] ++ map (\q2 -> ap d2 q2 a) x2

-- Machine that accepts the Kleene star of the language accepted by m1
starFSM :: Ord a => FSM a -> FSM [a]
starFSM (qs, s, fs, d) = (qs', s', fs', d') where
  qs' = power qs -- or: [x | x <- power qs, not (overlap x fs) || elem s x]
  s' = []
  fs' = [q' | q' <- qs', q' == [] || overlap q' fs]
  d'  = [(q', a, step q' a) | q' <- qs', a <- sigma]
  step [] a = norm $ [s | elem q fs] ++ [q] where q = ap d s a
  step x a  = norm $ [s | overlap x' fs] ++ x' where x' = map (\q -> ap d q a) x
    

-- Convert a regular expression to a finite state machine
conv :: RegExp a -> FSM a
conv Empty = emptyFSM
conv (Letter c) = letterFSM c
conv (Union r1 r2) = unionFSM (conv r1) (conv r2)
conv (Cat r1 r2) = catFSM (conv r1) (conv r2)
conv (Star r1) = starFSM (conv r1)


-- Machine that accepts the language {w}, where w in Sigma^*
-- Explanation of states:
--   0..n : correctly read this many characters of w
--   n+1  : trap state
stringFSM :: [Char] -> FSM Int
stringFSM w = ([0..n+1], 0, [n], d) where
  n = length w
  d =  [(i, a, step i a) | i <- [0..n+1], a <- sigma]
  step i a = if i >= n || w !! i /= a then n+1 else i+1
