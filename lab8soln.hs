-- Lab 8: REG closure under other operations

sigma = ['a','b']
data RE  = Empty | Letter Char | Union RE RE | Cat RE RE | Star RE deriving Show
type FSM a = ([a], a, [a], [(a, Char, a)])

-- has_epsilon r = True iff "" in [[r]]; useful in defining leftq below
has_epsilon :: RE -> Bool
has_epsilon Empty = False
has_epsilon (Letter c) = False
has_epsilon (Union r1 r2) = has_epsilon r1 || has_epsilon r2
has_epsilon (Cat r1 r2) = has_epsilon r1 && has_epsilon r2
has_epsilon (Star r) = True

-- Implement each of the following operations on regular expressions or FSMs

-- [[reverseRE r]] = rev([[r]]), defined by recursion on r
reverseRE :: RE -> RE
reverseRE Empty = Empty
reverseRE (Letter c) = Letter c
reverseRE (Union r1 r2) = Union (reverseRE r1) (reverseRE r2)
reverseRE (Cat r1 r2) = Cat (reverseRE r2) (reverseRE r1)
reverseRE (Star r1) = Star (reverseRE r1)

-- L(complementFSM M) = Sigma^* - L(M)
complementFSM :: Eq a => FSM a -> FSM a
complementFSM (qs, s, fs, rs) = (qs, s, fs', rs) where
  fs' = filter (\q -> notElem q fs) qs

-- Cartesian product
(><) :: [a] -> [b] -> [(a,b)]
xs >< ys = [(x,y) | x <- xs, y <- ys]   

-- L(intersectFSM m1 m2) = L(m1) intersect L(m2)
intersectFSM :: (Ord a, Ord b) => FSM a -> FSM b -> FSM (a,b)
intersectFSM (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = qs1 >< qs2
  s = (s1, s2)
  fs = [q | q <- qs, elem (fst q) fs1 && elem (snd q) fs2]
  d  = [(q, a, step q a) | q <- qs, a <- sigma]
  step (q1, q2) a = (ap d1 q1 a, ap d2 q2 a)

-- [[stringRE w]] = {w}
stringRE :: [Char] -> RE
stringRE [] = Star Empty
stringRE [a] = Letter a              
stringRE (a:as) = Cat (Letter a) (stringRE as)

-- [[himage r h]] = h^*([[r]]), defined by recursion on r
himage :: RE -> (Char -> [Char]) -> RE
himage Empty h = Empty
himage (Letter c) h = stringRE (h c)
himage (Union r1 r2) h = Union (himage r1 h) (himage r2 h)
himage (Cat r1 r2) h = Cat (himage r1 h) (himage r2 h)
himage (Star r1) h = Star (himage r1 h)

-- ap ts q a == the unique q' such that (q, a, q') is in ts;  assumes success
ap :: Eq a => [(a,Char,a)] -> a -> Char -> a 
ap ((q1, a1, q2):ts) q a | q1 == q && a1 == a = q2
                         | otherwise = ap ts q a

-- apstar ts q w
apstar :: Eq a => [(a,Char,a)] -> a -> [Char] -> a
apstar = foldl . ap
                                       
-- L(hinvimage m h) = (h^*)^{-1}(L(m))
hinvimage :: Eq a => FSM a -> (Char -> [Char]) -> FSM a
hinvimage (qs, s, fs, rs) h = (qs, s, fs, rs') where
  rs' = [(q,a,apstar rs q (h a)) | (q,a,_) <- rs]

-- L(rightq m a) = { w | wa in L(m) }
rightq :: Eq a => FSM a -> Char -> FSM a
rightq  (qs, s, fs, rs) a = (qs, s, fs', rs) where
  fs' = [q | q <- qs, ap rs q a `elem` fs]

-- [[leftq r a]] = { w | aw in [[r]] }, defined by recursion on r
leftq :: RE -> Char -> RE
leftq Empty a = Empty
leftq (Letter c) a = if a == c then Star Empty else Empty
leftq (Union r1 r2) a = Union (leftq r1 a) (leftq r2 a)
leftq (Cat r1 r2) a = if has_epsilon r1
                      then Union (Cat (leftq r1 a) r2) (leftq r2 a)
                      else Cat (leftq r1 a) r2
leftq (Star r1) a = Cat (leftq r1 a) (Star r1)



