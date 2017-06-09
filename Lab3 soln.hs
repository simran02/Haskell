-- Lab 4 (including a solution to Lab 3)


---------------- Lab 3 Solution ----------------

-- Warning: Some parts of this solution are overly concise.
-- Exercise: Figure out how they work!

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
letter c = undefined

data RE = Empty
            | Letter Char
            | Cat RE RE
            | Union RE RE
            | Star RE

-- The [[ ]] function from the lecture notes (the language named by
-- a regular expression). Use the constructions above, except that
-- all stars should have a bound of 10.
lang_of :: RE -> Language
lang_of r = undefined

-- Define Examples 1-4 from the lecture notes as elements of RE
-- and use lang_of and elem to check two representative matches
-- and two non-matches for each one.
ex1 :: RE
ex1 = undefined

ex2 :: RE
ex2 = undefined

ex3 :: RE
ex3 = undefined

ex4 :: RE
ex4 = undefined


-- Give structurally recursive definitions of the following functions.
-- You can *only* use the built-in Boolean constants and operations
-- True, False, &&, ||, not, and if then else; local definitions (let, where);
-- and the functions themselves (either recursively or each other). Test.

-- is_empty r == "[[r]] = {}" (i.e., r matches no strings)
is_empty :: RE -> Bool
is_empty r = undefined

-- is_one r == "[[r]] = {epsilon}" (i.e., r matches only "")
is_one :: RE -> Bool
is_one r = undefined

-- has_epsilon r == "epsilon `elem` [[r]]" (i.e., r matches at least "")
has_epsilon :: RE -> Bool
has_epsilon r = undefined

-- is_infinite r == "[[r]] is infinite"
is_infinite :: RE -> Bool
is_infinite r = undefined

-- [[rev r]] == {reverse w | w <- [[r]]} (i.e., rev r returns a RE
-- that matches exactly the reversals of the strings matched by r)
rev :: RE -> RE
rev r = undefined

-- [[nepart r]] = [[r]] - {epsilon} (i.e., nepart r returns a RE
-- that does not match "" but otherwise matches the same strings as r)
nepart :: RE -> RE
nepart r = undefined
