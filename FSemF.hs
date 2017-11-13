module FSemF where 

import Data.List
import Data.Char (toUpper)
import Control.Monad
import System.Random
import FSynF hiding (propNames)


-- Semantics of Sea Battle

type Grid = [(Column,Row)]

exampleGrid :: Grid
exampleGrid = [(A',9),
               (B',4),(B',5),(B',6),(B',7),(B',9),
               (C',9),(D',4),(E',4),(F',4),
               (G',4),(G',7),(G',8),(G',9),
               (H',1),(H',4),(I',1)]

attacks :: Grid
attacks = [(F',9),(E',8),(D',7),(C',6)]

battleship, frigate, sub1, sub2, destroyer :: Grid
battleship = [(D',4),(E',4),(F',4),(G',4),(H',4)]
frigate    = [(B',4),(B',5),(B',6),(B',7)]
sub1       = [(A',9),(B',9),(C',9)]
sub2       = [(G',7),(G',8),(G',9)]
destroyer  = [(H',1),(I',1)]

type State = ([Grid],Grid) 

shipsDistrib :: [Grid]
shipsDistrib = [battleship,frigate,sub1,sub2,destroyer]

exampleState = (shipsDistrib,attacks)

noClashes :: State -> Bool
noClashes (distrib,_) = nodups (concat distrib) 
  where nodups []     = True
        nodups (x:xs) = notElem x xs && nodups xs

-- c5e1
allAdjacent :: (Eq a, Enum a) => [a] -> Bool
allAdjacent (x:[]) = True
allAdjacent (x1:x2:xt) = succ x1 == x2 && allAdjacent (x2:xt)

allEqual :: Eq a => [a] -> Bool
allEqual (x:xt) = all (\y -> y == x) xt

shipOK' :: [Column] -> [Row] -> Bool
shipOK' cs rs | allAdjacent cs = allEqual rs
              | allEqual cs = allAdjacent rs
              | otherwise = False

shipOK :: Grid -> Bool
shipOK = uncurry shipOK' . unzip . sort

-- como fazer shipOK' ser local à shipOK ??

lineupOK :: State -> Bool
lineupOK (distrib,_) = all shipOK distrib


hit :: Attack -> State -> Bool
hit pos (gs,_) = elem pos (concat gs)

missed :: Attack -> State -> Bool
missed pos = not . (hit pos)

-- c5e2
-- how to relate Ship to Grid?
shipType :: Grid -> Ship
shipType g | len == 2 = Destroyer
           | len == 3 = Submarine
           | len == 4 = Frigate
           | len == 5 = Battleship
  where len = length g

isShip :: Ship -> Grid -> Bool
isShip s g = s == shipType g

sunkShip :: Attack -> Grid -> Grid -> Bool
sunkShip pos s as = [pos] == s \\ as

sunk :: Attack -> Ship -> State -> Bool
sunk pos ship (ss,as) = any (\s -> sunkShip pos s as) $ filter (isShip ship) ss
----

defeated :: State -> Bool
defeated  (gs,g) = all (`elem` g) (concat gs)

updateBattle :: Attack -> State -> State
updateBattle p (gs,g) = (gs, insert p g)

--
-- Propositional logic

propNames :: Form -> [String]
propNames (P name) = [name]
propNames (Ng f)   = propNames f
propNames (Cnj fs) = (sort.nub.concat) (map propNames fs)
propNames (Dsj fs) = (sort.nub.concat) (map propNames fs)

genVals :: [String] -> [[(String,Bool)]]
genVals [] = [[]]
genVals (name:names) = map ((name,True) :) (genVals names) 
                    ++ map ((name,False):) (genVals names)

allVals :: Form -> [[(String,Bool)]]
allVals = genVals . propNames 

eval :: [(String,Bool)] -> Form -> Bool
eval [] (P c)    = error ("no info about " ++ show c)
eval ((i,b):xs) (P c) 
     | c == i    = b 
     | otherwise = eval xs (P c) 
eval xs (Ng f)   = not (eval xs f)
eval xs (Cnj fs) = all (eval xs) fs
eval xs (Dsj fs) = any (eval xs) fs

tautology :: Form -> Bool
tautology f = all (\ v -> eval v f) (allVals f)

satisfiable :: Form -> Bool
satisfiable f = any (\ v -> eval v f) (allVals f)

contradiction :: Form -> Bool
contradiction = not . satisfiable

implies :: Form -> Form -> Bool
implies f1 f2 = contradiction (Cnj [f1,Ng f2])

-- c5e10
impliesL :: [Form] -> Form -> Bool
--impliesL ps c = contradiction (Cnj $ (Ng c):ps)
impliesL ps = implies $ Cnj ps
----

-- c5e11
propEquiv :: Form -> Form -> Bool
propEquiv f1 f2 = implies f1 f2 && implies f2 f1
----

update :: [[(String,Bool)]] -> Form -> [[(String,Bool)]]
update vals f = [ v | v <- vals, eval v f ]

-- c5e12
genVals' :: [String] -> [[String]]
genVals' [] = [[]]
genVals' ps = filterM (\p -> [True, False]) ps

allVals' :: Form -> [[String]]
allVals' = genVals' . propNames 

eval' :: [String] -> Form -> Bool
eval' [] (P c)    = error ("no info about " ++ show c)
eval' (x:xt) (P c) 
      | c == x    = True
      | otherwise = eval' xt (P c)
eval' xs (Ng f)   = not (eval' xs f)
eval' xs (Cnj fs) = all (eval' xs) fs
eval' xs (Dsj fs) = any (eval' xs) fs

tautology' :: Form -> Bool
tautology' f = all (\ v -> eval' v f) (allVals' f)

satisfiable' :: Form -> Bool
satisfiable' f = any (\ v -> eval' v f) (allVals' f)

contradiction' :: Form -> Bool
contradiction' = not . satisfiable'

implies' :: Form -> Form -> Bool
implies' f1 f2 = contradiction' (Cnj [f1,Ng f2])

impliesL' :: [Form] -> Form -> Bool
impliesL' ps = implies' $ Cnj ps

propEquiv' :: Form -> Form -> Bool
propEquiv' f1 f2 = implies' f1 f2 && implies' f2 f1

update' :: [[String]] -> Form -> [[String]]
update' vals f = [ v | v <- vals, eval' v f ]
----

--
-- Semantics of mastermind
samepos :: Pattern -> Pattern -> Int
samepos _      []                 = 0 
samepos []     _                  = 0 
samepos (x:xs) (y:ys) | x == y    = samepos xs ys + 1
                      | otherwise = samepos xs ys 

occurscount ::  Pattern -> Pattern -> Int
occurscount xs []       = 0
occurscount xs (y:ys) 
          | y `elem` xs = occurscount (delete y xs) ys + 1
          | otherwise   = occurscount xs ys 

reaction :: Pattern -> Pattern -> [Answer]
reaction secret guess = take n (repeat Black) 
                     ++ take m (repeat White)
    where n = samepos secret guess 
          m = occurscount secret guess - n 

secret = [Red,Blue,Green,Yellow]

updateMM :: [Pattern] -> Pattern -> Feedback -> [Pattern]
updateMM state guess answer = 
   [ xs | xs <- state, reaction xs guess == answer ]

string2pattern :: String -> Pattern 
string2pattern = convertP . (map toUpper)

convertP :: String -> Pattern
convertP []       = []
convertP (' ':xs) =          convertP xs
convertP ('R':xs) = Red    : convertP xs
convertP ('Y':xs) = Yellow : convertP xs
convertP ('B':xs) = Blue   : convertP xs
convertP ('G':xs) = Green  : convertP xs
convertP ('O':xs) = Orange : convertP xs

getColours :: IO [Colour]
getColours = do i <- getStdRandom (randomR (0,4))
                j <- getStdRandom (randomR (0,4))
                k <- getStdRandom (randomR (0,4))
                l <- getStdRandom (randomR (0,4))
                return [toEnum i,toEnum j,toEnum k, toEnum l]

-- c5e15
playMM' :: Pattern -> IO ()
playMM' secret = 
  do 
    putStrLn "Give a sequence of four colours from RGBYO"
    s <- getLine
    if (string2pattern s) /= secret 
      then 
        let answer = reaction secret (string2pattern s) in 
        do 
          putStrLn (show answer)
          putStrLn "Please make another guess"
          playMM' secret
      else putStrLn "correct"

playMM :: IO ()
playMM = do secret <- getColours
            playMM' secret
----

-- c5e16
colours = [Red, Yellow, Blue, Green, Orange]
initialState = [w:x:y:z:[] | w <- colours, x <-colours, y<-colours,z<-colours]

playMM'' :: Pattern -> [Pattern] -> IO ()
playMM'' secret state = do
  putStrLn "Give a sequence of four colours from RGBYO"
  s <- getLine
  let guess = (string2pattern s)
      answer = reaction secret guess
      newState = updateMM state guess answer
  if elem guess state
    then putStrLn "good guess"
    else do
      putStrLn "not so good a guess, are you sure you want to try that?"
      playMM'' secret state
  if guess /= secret
    then do
      putStrLn (show answer)
      putStrLn "Please make another guess"
      playMM'' secret newState
    else putStrLn "correct"

playMM''' :: IO ()
playMM''' = do secret <- getColours
               playMM'' secret initialState
----
