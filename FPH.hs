module FPH

where 

import Data.List
import Data.Char


square :: Int -> Int
square x = x * x

hword :: String -> Bool
hword [] = False
hword (x:xs) = (x == 'h') || (hword xs)

plus :: Int -> Int -> Int
plus x y = x + y

gen :: Int -> String
gen 0 = "Sentences can go on"
gen n = gen (n - 1) ++ " and on"

genS :: Int -> String
genS n = gen n ++ "."

-- c3e12
minList' :: Ord a => [a] -> a
minList' [x] = x
minList' (x1:x2:xt) = minList ((min x1 x2):xt)

minList :: Ord a => [a] -> a
minList [x]  = x
minList (x:xs) = min x (minList xs)
----

-- c3e13
delete' :: Eq a => a -> [a] -> [a]
delete' _ [] = []
delete' y (x:xt)
  | x /= y = x : (delete y xt)
  | otherwise = xt -- delete y xt

-- delete :: Eq a => a -> [a] -> [a]
-- delete p [] = []
-- delete p (x:xs) | (p == x) = xs
--                 | otherwise = x : delete p xs

-- duas alternativas para delete all. Parece que não podemos usar x
-- x:xs sem erro de dual bind para x.

deleteAll :: Eq a => a -> [a] -> [a]
deleteAll p [] = []
deleteAll p (x:xs) | (p == x) = deleteAll p xs
                   | otherwise = x : deleteAll p xs

deleteAll2 :: Eq a => a -> [a] -> [a]
deleteAll2 p xs = filter (\ x -> x /= p) xs
----

-- c3e14
-- duas formas alternativas, let nos permite reaproveitar
-- processamento linear do minList

srt :: Ord a => [a] -> [a]
srt [] = []
srt xs =
  let n = (minList xs)
  in
    n : srt (delete n xs)

srt1 :: Ord a => [a] -> [a]
srt1 [] = []
srt1 xs = (minList xs) : srt1 (delete (minList xs) xs)
----

-- sec 3.10
  
reversal :: String -> String
reversal []    = []
reversal (x:t) = reversal t ++ [x]


sonnet18 = 
 "Shall I compare thee to a summer's day? \n"
 ++ "Thou art more lovely and more temperate: \n"
 ++ "Rough winds do shake the darling buds of May, \n"
 ++ "And summer's lease hath all too short a date: \n"
 ++ "Sometime too hot the eye of heaven shines, \n"
 ++ "And often is his gold complexion dimm'd; \n"
 ++ "And every fair from fair sometime declines, \n"
 ++ "By chance or nature's changing course untrimm'd; \n"
 ++ "But thy eternal summer shall not fade \n"
 ++ "Nor lose possession of that fair thou owest; \n"
 ++ "Nor shall Death brag thou wander'st in his shade, \n"
 ++ "When in eternal lines to time thou growest: \n"
 ++ "  So long as men can breathe or eyes can see, \n"
 ++ "  So long lives this and this gives life to thee."

sonnet73 =
 "That time of year thou mayst in me behold\n"
 ++ "When yellow leaves, or none, or few, do hang\n"
 ++ "Upon those boughs which shake against the cold,\n"
 ++ "Bare ruin'd choirs, where late the sweet birds sang.\n"
 ++ "In me thou seest the twilight of such day\n"
 ++ "As after sunset fadeth in the west,\n"
 ++ "Which by and by black night doth take away,\n"
 ++ "Death's second self, that seals up all in rest.\n"
 ++ "In me thou see'st the glowing of such fire\n"
 ++ "That on the ashes of his youth doth lie,\n"
 ++ "As the death-bed whereon it must expire\n"
 ++ "Consumed with that which it was nourish'd by.\n"
 ++ "This thou perceivest, which makes thy love more strong,\n"
 ++ "To love that well which thou must leave ere long."
 
count :: Eq a => a -> [a] -> Int
count x []  = 0
count x (y:ys) | x == y    = succ (count x ys)
               | otherwise = count x ys


average :: [Int] -> Rational
average [] = error "empty list"
average xs = toRational (sum xs) / toRational (length xs)

-- exercicio 3.16
-- Usage: averageWordsLength sonnet18

averageWordsLength :: String -> Rational
averageWordsLength xs = 
  average (map length [filter (`notElem` "!;:?,.") w | w <- (words xs)])

-- c3e17
prefix :: Eq a => [a] -> [a] -> Bool
prefix [] ys         = True
prefix (x:xs) []     = False
prefix (x:xs) (y:ys) = (x == y) && prefix xs ys


sublist :: Eq a => [a] -> [a] -> Bool
sublist [] [] = True
sublist xs [] = False
sublist xs (y:ys) = prefix xs (y:ys) || sublist xs ys

sublist' :: Eq a => [a] -> [a] -> Bool
sublist' [] [] = True
sublist' _ [] = False
sublist' xs ys@(_:yt)
  | prefix xs ys = True
  | sublist xs yt = True
  | otherwise = False

----

nub1 :: Eq a => [a] -> [a]
nub1 [] = []
nub1 (x:xs) = x : nub1 (filter (\ y -> y /= x) xs)
  
preprocess :: String -> String
preprocess = (map toLower) . filter (`notElem` "?;:,.")

process :: String -> [String]
process = sort . nub . words

cnt :: String -> [(String,Int)]
cnt sonnet = [ (x,n) |
               x <- (process . preprocess) sonnet,
               n <- [count x (words (preprocess sonnet))],
               n > 1 ]


-- Section 3.11

aUml, oUml :: Char
aUml = chr(228)
oUml = chr(246)

appendSuffixF :: String -> String -> String
appendSuffixF stem suffix = stem ++ map vh suffix
  where vh | or [elem c "aou" | c <- stem]           = back
           | or [elem c [aUml,oUml,'y'] | c <- stem] = front
           | otherwise                               = id
               
front :: Char -> Char
front s | s == 'a'  = aUml
        | s == 'o'  = oUml
        | s == 'u'  = 'y'
        | otherwise = s

back :: Char -> Char
back s  | s == aUml  = 'a'
        | s == oUml  = 'o'
        | s == 'y'   = 'u'
        | otherwise  = s


data DeclClass = One | Two | Three | Four | Five

oSlash,aRing :: Char
oSlash = chr(248)
aRing  = chr(229)

swedishVowels = ['a','i','o','u','e','y',aUml,aRing,oUml,oSlash]

swedishPlural :: String -> DeclClass -> String
swedishPlural noun d = case d of
                         One   -> init noun ++ "or"
                         Two   -> init noun ++ "ar"
                         Three -> if  (last noun) `elem` swedishVowels
                                  then noun ++ "r"
                                  else noun ++ "er"
                         Four  -> noun ++ "n"
                         Five  -> noun

                 
-- section 3.13 : datatypes

data Subject   = Chomsky | Montague deriving Show
data Predicate = Wrote String       deriving Show

data Sentence  = S Subject Predicate
type Sentences = [Sentence]

instance Show Sentence where
  show (S subj pred) = show subj ++ " " ++ show pred

makeP :: String -> Predicate
makeP title = Wrote title

makeS :: Subject -> Predicate -> Sentence
makeS subj pred = S subj pred

data Colour = RGB Int Int Int deriving Show

showColour :: Colour -> String
showColour (RGB 0 0 0)       = "black"
showColour (RGB 255 255 255) = "white"
showColour (RGB 255 0 0)     = "red"
showColour (RGB 0 255 0)     = "green"
showColour (RGB 0 0 255)     = "blue"
showColour (RGB 255 255 0)   = "yellow"
showColour (RGB 0 255 255)   = "cyan"
showColour (RGB 255 0 255)   = "magenta"
-- showColour c                 = c

redAlert  :: Colour -> String
redAlert c@(RGB r _ _) =
  case r of
    0 -> show c ++ " has no red"
    _ -> show c ++ " has red"


-- section 3.14 : representing phonemes

data Feature = F Attr Value               deriving (Eq,Show)
data Attr    = Back | High | Round | Cons deriving (Eq,Show)
data Value   = Plus | Minus               deriving (Eq,Show)
type Phoneme = [Feature]

yawelmaniVowels = [i,a,o,u,e]

i = [F Cons Minus, F High Plus, F Round Minus, F Back Minus]
a = [F Cons Minus, F High Minus, F Round Minus, F Back Plus ]
o = [F Cons Minus, F High Minus, F Round Plus, F Back Plus ]
u = [F Cons Minus, F High Plus, F Round Plus, F Back Plus ]
e = [F Cons Minus, F High Minus, F Round Minus, F Back Minus]

c = [F Cons Plus]

realize :: Phoneme -> Char
realize x | x == i = 'i'
          | x == a = 'a'
          | x == o = 'o'
          | x == u = 'u'
          | x == e = 'e'
          | x == c = 'c'

fValue :: Attr -> Phoneme -> Value
fValue attr [] = error "feature not found"
fValue attr ((F a v) : fs) | attr == a = v
                           | otherwise = fValue attr fs

fMatch :: Attr -> Value -> Phoneme -> Phoneme
fMatch attr value fs = map (match attr value) fs
   where match a v f@(F a' v') | a == a'  = F a' v
                               | otherwise = f

-- c3e19
appendSuffixY :: [Phoneme] -> [Phoneme] -> [Phoneme]
appendSuffixY stem suffix = stem ++ (map (harmonize stemV) suffix)
  where isVowel = (\c -> elem c yawelmaniVowels)
        getVowel = head . filter isVowel -- only gets first vowel
        stemV = getVowel stem
        harmonize' stemVowel = (\c -> fMatch Round (fValue Round stemVowel) (fMatch Back (fValue Back stemVowel) c))
        harmonize stemVowel = (\c -> if isVowel c && (fValue High stemVowel) == (fValue High c) then harmonize' stemVowel c else c)
----

main = putStrLn ( s ++ show s)
  where s = "main = putStrLn (s ++ show s) \n where s = "
        
