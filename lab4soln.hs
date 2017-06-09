-- Lab 4 Solution 

import Data.List (sort, stripPrefix)

-- normalize a list, i.e., sort and remove (now adjacent) duplicates
norm :: Ord a => [a] -> [a]
norm = mynub . sort where
  mynub [] = []
  mynub [x] = [x]
  mynub (x:ys@(y:zs)) | x == y = mynub ys
                      | otherwise = x : mynub ys

type Language = [String]

mylen :: String -> Int
mylen [] = 0
mylen (c:cs) = 1 + mylen cs
-- below, however, we will use "length" for efficiency

myconcat :: String -> String -> String
myconcat [] s = s
myconcat (c:cs) s = c : myconcat cs s
-- below, however, we will use "++" for efficiency

zero :: Language
zero = []

one :: Language
one = [""]

cat :: Language -> Language -> Language
cat l1 l2 = norm [w1 ++ w2 | w1 <- l1, w2 <- l2]

uni :: Language -> Language -> Language
uni l1 l2  = norm $ l1 ++ l2

bstar :: Language -> Int -> Language
bstar l n = concat $ scanl cat one $ replicate n l

rightq :: Language -> Language -> Language
rightq l1 l2  = norm [w | w1 <- l1, w2 <- l2, Just w <- [stripPrefix w1 w2]]

leftq :: Language -> Language -> Language
leftq l1 l2 = norm [w | w2 <- l2, (w, w1) <- splits w2, elem w1 l1] where
  splits [] = [([], [])]
  splits w@(x:xs) = ([],w) : map (\(a,b) -> (x:a,b)) (splits xs)

star :: Language -> Language
star l = concat $ scanl cat one $ repeat l


---------------- Lab 4 ----------------

-- RegLetter
letter :: Char -> Language
letter c = [[c]]

data RE = Empty
            | Letter Char
            | Cat RE RE
            | Union RE RE
            | Star RE

lang_of :: RE -> Language
lang_of Empty = zero
lang_of (Letter c) = letter c
lang_of (Cat r1 r2) = cat (lang_of r1) (lang_of r2)
lang_of (Union r1 r2) = uni (lang_of r1) (lang_of r2)
lang_of (Star r) = bstar (lang_of r) 10

ab :: RE
ab = Union (Letter 'a') (Letter 'b')

ex1 :: RE
ex1 = Star ab

ex2 :: RE
ex2 = Cat ab ex1

ex3 :: RE
ex3 = Cat (Star (Letter 'b')) (Cat (Letter 'a') ex1)

ex4 :: RE
ex4 = let astar = Star (Letter 'a')
      in Union astar (Cat astar (Cat (Letter 'b') astar))

is_empty :: RE -> Bool
is_empty Empty = True
is_empty (Letter c) = False
is_empty (Union r1 r2) = is_empty r1 && is_empty r2
is_empty (Cat r1 r2) = is_empty r1 || is_empty r2
is_empty (Star r) = False

is_one :: RE -> Bool
is_one Empty = False
is_one (Letter c) = False
is_one (Union r1 r2) = let e1 = is_empty r1; o1 = is_one r1
                           e2 = is_empty r2; o2 = is_one r2
                       in e1 && o2 || e2 && o1 || o1 && o2
is_one (Cat r1 r2) = is_one r1 && is_one r2
is_one (Star r) = is_empty r

has_epsilon :: RE -> Bool
has_epsilon Empty = False
has_epsilon (Letter c) = False
has_epsilon (Union r1 r2) = has_epsilon r1 || has_epsilon r2
has_epsilon (Cat r1 r2) = has_epsilon r1 && has_epsilon r2
has_epsilon (Star r) = True

is_infinite :: RE -> Bool
is_infinite Empty = False
is_infinite (Letter c) = False
is_infinite (Union r1 r2) = is_infinite r1 || is_infinite r2
is_infinite (Cat r1 r2) = is_infinite r1 && not (is_empty r2) ||
                          is_infinite r2 && not (is_empty r1)
is_infinite (Star r) = not (is_empty r || is_one r)

rev :: RE -> RE
rev Empty = Empty
rev (Letter c) = Letter c
rev (Union r1 r2) = Union (rev r1) (rev r2)
rev (Cat r1 r2) = Cat (rev r2) (rev r1)
rev (Star r) = Star (rev r)

nepart :: RE -> RE
nepart Empty = Empty
nepart (Letter c) = Letter c
nepart (Union r1 r2) = Union (nepart r1) (nepart r2)
nepart (Cat r1 r2) = let n1 = nepart r1
			 n2 = nepart r2
                         e1 = has_epsilon r1
                         e2 = has_epsilon r2
		     in if e1 then if e2 then Union (Union n1 n2) (Cat n1 n2)
                                         else Union r2 (Cat n1 r2)
                              else if e2 then Union r1 (Cat r1 n2)
                                         else Cat r1 r2
nepart (Star r) = let r' = nepart r
                  in Cat r' (Star r')

