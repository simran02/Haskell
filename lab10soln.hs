-- Lab 10: Derivative-based conversion from RE' to FSM
-- Same set-up as in Lab 7, including RE' simplifier

import Data.List (nub, sort)

sigma = ['a', 'b']

-- normalize a list, i.e., sort and remove (now adjacent) duplicates
norm :: Ord a => [a] -> [a]
norm = mynub . sort where
  mynub [] = []
  mynub [x] = [x]
  mynub (x:ys@(y:zs)) | x == y = mynub ys
                      | otherwise = x : mynub ys

-- Ordinary regular expressions and a show method for them
data RE  = Empty | Letter Char | Union RE RE | Cat RE RE | Star RE
instance (Show RE) where    -- use precedence to minimize parentheses
  showsPrec d Empty         = showString "@"
  showsPrec d (Letter c)    = showString [c]
  showsPrec d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                              showsPrec 6 r1 .
                              showString "+" .
                              showsPrec 6 r2
  showsPrec d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                              showsPrec 7 r1 .
                              showsPrec 7 r2
  showsPrec d (Star r1)     = showsPrec 9 r1 .     -- prec(Star) = 8
                              showString "*"

-- Extended regular expressions, including a name for One = Star Empty,
-- and arbitrary numbers of arguments for (associative) Union and Cat
data RE' = Zero | One | Letter' Char | Union' [RE'] | Cat' [RE'] | Star' RE'
  deriving (Eq, Ord, Show)

-- Convert ordinary REs into extended REs
toRE' :: RE -> RE'
toRE' Empty = Zero
toRE' (Letter c) = Letter' c
toRE' (Union r1 r2) = Union' [toRE' r1, toRE' r2]
toRE' (Cat r1 r2) = Cat' [toRE' r1, toRE' r2]
toRE' (Star r1) = Star' (toRE' r1)

-- Convert extended REs into ordinary REs, eliminating Union' and Cat' on
-- lists of length < 2, and right-associating them on longer lists
toRE :: RE' -> RE
toRE Zero = Empty
toRE One = Star Empty
toRE (Letter' c) = Letter c
toRE (Union' []) = Empty
toRE (Union' [r]) = toRE r
toRE (Union' (r:rs)) = Union (toRE r) (toRE (Union' rs))
toRE (Cat' []) = Star Empty
toRE (Cat' [r]) = toRE r
toRE (Cat' (r:rs)) = Cat (toRE r) (toRE (Cat' rs))
toRE (Star' r) = Star (toRE r)

-- Basic postfix parser for RE', assuming binary + and ., for testing
re :: String -> RE'
re w = re' w [] where
  re' [] [r] = r
  re' ('0':xs) rs = re' xs (Zero:rs)
  re' ('1':xs) rs = re' xs (One:rs)
  re' ('+':xs) (r2:r1:rs) = re' xs (Union' [r1,r2]:rs)
  re' ('.':xs) (r2:r1:rs) = re' xs (Cat' [r1,r2]:rs)
  re' ('*':xs) (r:rs) = re' xs (Star' r:rs)
  re' (x:xs) rs = re' xs (Letter' x:rs)


-- FSMs indexed by the type of their states (states, start, final, transitions)
type FSM a = ([a], a, [a], [(a, Char, a)])

-- ap ts q a == the unique q' such that (q, a, q') is in ts;  assumes success
ap :: Eq a => [(a,Char,a)] -> a -> Char -> a 
ap ((q1, a1, q2):ts) q a | q1 == q && a1 == a = q2
                         | otherwise = ap ts q a

-- An extended regular expression simplifier
simp :: RE' -> RE'
simp Zero = Zero
simp One = One
simp (Letter' c) = Letter' c
simp (Union' rs) = union' $ flat_uni $ map simp rs
simp (Cat' rs) = union' $ flat_cat $ map simp rs
simp (Star' r) = star' $ simp r

-- Smart constructor for Union' that normalizes its arguments and
-- handles the empty and singleton cases
union' :: [RE'] -> RE'
union' rs =  case norm rs of
  []  -> Zero
  [r] -> r
  rs  -> Union' rs

-- Smart constructor for Cat' that handles the empty and singleton cases
cat' :: [RE'] -> RE'
cat' [] = One
cat' [r] = r
cat' rs = Cat' rs

-- Smart constructor for Star' that handles the constant and Star' cases
star' :: RE' -> RE'
star' Zero = One
star' One = One
star' (Star' r) = star' r
star' r = Star' r

-- Flatten a list of arguments to Union'; assumes each argument is simplified
flat_uni :: [RE'] -> [RE']
flat_uni [] = []
flat_uni (Zero:rs) = flat_uni rs
flat_uni (Union' rs':rs) = rs' ++ flat_uni rs
flat_uni (r:rs) = r : flat_uni rs

-- Flatten a list of arguments to Cat', turning them into a list of arguments
-- to Union'; assumes each argument is simplified
flat_cat :: [RE'] -> [RE']
flat_cat rs = fc [] rs where
  -- fc (args already processed, in reverse order) (args still to be processed)
  fc :: [RE'] -> [RE'] -> [RE']
  fc pr [] = [cat' $ reverse pr]
  fc pr (Zero:rs) = []
  fc pr (One:rs) = fc pr rs
  fc pr (Cat' rs':rs) = fc (reverse rs' ++ pr) rs
  fc pr (Union' rs':rs) = concat $ map (fc pr . (:rs)) rs'
  fc pr (r:rs) = fc (r:pr) rs


---------------- Lab 10 begins here ----------------

-- Bypassable (aka has_epsilon) on extended REs, computed directly.
byp :: RE' -> Bool
byp Zero = False
byp One = True
byp (Letter' a) = False
byp (Union' rs) = any byp rs
byp (Cat' rs) = all byp rs
byp (Star' r) = True

-- Regular-expression derivatives (aka left quotients) on extended REs,
-- computed directly. Should always return a simplified RE'.
deriv :: Char -> RE' -> RE'
deriv a = simp . der where
  der Zero = Zero
  der One = Zero
  der (Letter' b) = if a == b then One else Zero
  der (Union' rs) = Union' $ map der rs
  der (Cat' rs) = Union' $ der_cat rs
  der (Star' r) = Cat' [der r, Star' r]
  --
  der_cat :: [RE'] -> [RE']
  der_cat [] = []
  der_cat (r:rs) | byp r     = Cat' (der r:rs) : der_cat rs
                 | otherwise = [Cat' (der r:rs)]

-- Find the list of all (simplified) derivatives of a regular expression
all_derivs r = stable $ iterate close ([r], []) where
  stable ((fr,rs):rest) = if null fr then rs else stable rest
  close (fr, rs) = (fr', rs') where  
    rs' = fr ++ rs
    fr' = nub $ filter (`notElem` rs') (concatMap step fr)
    step r = map (\a -> deriv a r) sigma

-- Convert an RE' to an FSM using the derivative construction
conv :: RE' -> FSM RE'
conv r = (qs, s, fs, ts) where
  qs = all_derivs r
  s  = r
  fs = filter byp qs
  ts = [(r, a, deriv a r) | r <- qs, a <- sigma]

-- Change the states of an FSM from an equality type to Int
intify :: Eq a => FSM a -> FSM Int
intify (qs, s, fs, ts) = ([0..length qs - 1], s', fs', ts') where
  s'  = ind qs s
  fs' = map (ind qs) fs
  ts' = map (\(q,a,q') -> (ind qs q, a, ind qs q')) ts
  ind (q:qs) q0 = if q == q0 then 0 else 1 + ind qs q0

