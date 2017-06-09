-- Lab 9: Non-deterministic finite state machines
-- Feel free to use any additional functions from previous labs

—****** Simran Arora ****


import Data.List (sort, subsequences)

-- normalize a list, i.e., sort and remove (now adjacent) duplicates
norm :: Ord a => [a] -> [a]
norm = mynub . sort where
  mynub [] = []
  mynub [x] = [x]
  mynub (x:ys@(y:zs)) | x == y = mynub ys
                      | otherwise = x : mynub ys

-- Sigma = [a,b] for testing, but must work for any finite list
sigma :: [Char]
sigma = ['a', 'b']

-- Finite State Machines
type FSM a  = ([a], a,   [a], [(a, Char,  a)]) -- function: a x Char -> a

-- ap ts q a == the unique q' such that (q, a, q') is in ts;  assumes success
ap :: Eq a => [(a,Char,a)] -> a -> Char -> a 
ap ((q1, a1, q2):ts) q a | q1 == q && a1 == a = q2
                         | otherwise = ap ts q a
						 
-- Some helpful functions

(><) :: [a] -> [b] -> [(a,b)]              -- Cartesian product
xs >< ys = [(x,y) | x <- xs, y <- ys]   

overlap :: Eq a => [a] -> [a] -> Bool      -- overlap
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys

power :: [a] -> [[a]]
power = subsequences                       -- powerlist (imported)

----------------------------------------------------------------
-- Nondeterministic FSMs
type NFSM a = ([a], [a], [a], [(a, Char,  a)]) -- relation: a x Char x a

ndelta (qs,s,fs,ts) a b= [q| (a1,b1,q)<-ts,a==a1,b==b1]

ndeltalis m@(qs,s,fs,ts) [] b = []
ndeltalis m@(qs,s,fs,ts) (a:as) b= norm $(ndelta m a b) ++ (ndeltalis m as b )

ndeltalis2 m@(qs,s,fs,ts) (a:as) []=[]
ndeltalis2 m@(qs,s,fs,ts) (a:as) (b:bs)= let gs= (ndeltalis m (a:as) b);
										in norm $ gs ++ ndeltalis2 m gs bs

ndelta_star :: Ord a =>Eq a => NFSM a -> a -> [Char] -> [a]
ndelta_star m@(qs,s,fs,ts) a w =  let ls =ndeltalis2 m (ndelta m a (head w)) (tail w);
									in norm $(ndelta m a (head w) ) ++ ls

naccept :: Ord a=>Eq a => NFSM a -> [Char] -> Bool
naccept m@(qs,s,fs,ts) w= or [q`elem`fs|a<-s, q<-ndelta_star m a w]




----------------------------------------------------------------
-- Nondeterministic FSMs with epsilon moves

data CharE = Eps | Chr Char deriving Eq 
type EFSM a = ([a], [a], [a], [(a, CharE, a)]) -- relation: a x CharE x a

-- Epsilon closure of a set of states (Hint: look at reachable below)
eclose :: Eq a => EFSM a -> [a] -> [a]
eclose m@(qs,s,fs,ts) as =[q|(q1,Eps,q)<-ts,q2<-as,q1==q2] ++ as

edelta (qs,s,fs,ts) a b= [q| (a1,b1,q)<-ts,a==a1,b==b1||b1==Eps]

edeltalis m@(qs,s,fs,ts) [] b = []
edeltalis m@(qs,s,fs,ts) (a:as) b= norm $(edelta m a b) ++ (edeltalis m as b )

edeltalis2 m@(qs,s,fs,ts) (a:as) []=[]
edeltalis2 m@(qs,s,fs,ts) (a:as) (b:bs)= let gs= (edeltalis m (a:as) b);
										in norm $ gs ++ edeltalis2 m gs bs

edelta_star ::Ord a=> Eq a => EFSM a -> a -> [Char] -> [a]
edelta_star m@(qs,s,fs,ts) a w =  let ks=charer w;
										ls =edeltalis2 m (edelta m a (head ks)) (tail ks);
									in norm $(edelta m a (head ks) ) ++ ls 

eaccept :: Ord a => Eq a => EFSM a -> [Char] -> Bool
eaccept m@(qs,s,fs,ts) w= or [q`elem`fs|a<-s, q<-edelta_star m a w]

charer [] = []
charer (a:as) = [Chr a]++charer as

k=([1..5],[1,2,3],[4,5],[(1,Chr 'a',4),(1,Eps,5),(1,Chr 'b',3),(2,Chr 'a',4),(2,Eps,3),(2,Chr 'b',2),(3,Chr 'a',3),(3,Chr 'b',1),(4,Chr 'a',5),(4,Chr 'b',2),(5,Chr 'a',4),(5,Chr 'b',5),(5,Chr 'b',3)])

----------------------------------------------------------------
-- Machine conversions

-- Easy conversion from FSM to NFSM
fsm_to_nfsm :: Eq a => FSM a -> NFSM a
fsm_to_nfsm (qs, s, fs, ts) = (qs, [s], fs, ts)

-- Conversion from NFSM to FSM by the "subset construction"
nfsm_to_fsm :: Ord a => NFSM a -> FSM [a]
nfsm_to_fsm m@(qs, s, fs, ts)= (qs1, s1, fs1, ts1) where
							qs1= power qs;
							s1=s;
							fs1=[q|q<-qs1, overlap q fs];
							ts1=[(q,a,q2)| q<-qs1, a<-sigma, q2<- [ndeltalis m q a] ]
							

-- Conversion from EFSM to FSM by epsilon elimination (and subset construction)
enfsm_to_fsm :: Ord a => EFSM a -> FSM [a]
enfsm_to_fsm m@(qs, s, fs, ts)= (qs1, s1, fs1, ts1) where
							qs1= power qs;
							s1= eclose m s
							fs1=[q|q<-qs1, overlap q fs];
							ts1=[(q,a,q2)| q<-qs1, a<-sigma, q2<- [edeltalis m q (charers a)] ]

charers a = Chr a
----------------------------------------------------------------
-- Reachability (from Lab 6)

-- reachable m == the part of m that is reachable from the start state
reachable :: Ord a => FSM a -> FSM a
reachable m@(qs, s, fs, d) = (qs', s, fs', d') where
  qs' = sort $ stable $ iterate close ([s], [])
  fs' = filter (`elem` qs') fs
  d'  = filter (\(q,_,_) -> q `elem` qs') d
  stable ((fr,qs):rest) = if null fr then qs else stable rest
  -- in close (fr, xs), fr (frontier) and xs (current closure) are disjoint
  close (fr, xs) = (fr', xs') where  
    xs' = fr ++ xs
    fr' = norm $ filter (`notElem` xs') (concatMap step fr)
    step q = map (ap d q) sigma
