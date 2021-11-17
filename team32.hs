data Item a = It Tag (Data a) Bool Int | NotPresent deriving (Show, Eq)
data Tag = T Int deriving (Show, Eq)
data Data a = D a deriving (Show, Eq)

getDataIt (It _ (D d) _ _) =d

getTagIt (It (T t) _ _ _) =t

getValidIt (It _ _ b _) =b

getOrderIt (It _ _ _ o) = o

-------------------------
convertBinToDec :: Integral a => a -> a

convertBinToDec x = (convertBinToDecHelp x 1)

convertBinToDecHelp x p = if x==0 then 0 else ((mod x 10)*p)+(convertBinToDecHelp (div x 10) (p*2))

--------------------------

replaceIthItem :: t -> [t] -> Int -> [t]

replaceIthItem item (x:xs) 0 = (item:xs)
replaceIthItem item (x:xs) idx = (x:(replaceIthItem item xs (idx-1)))

--------------------------

splitEvery :: Int -> [a] -> [[a]]

splitEvery n l = (splitter n 0 ([]) l)

splitter _ _ acc [] = [acc]
splitter n i acc (x:xs) = if i==n then (acc:(splitter n 0 [] (x:xs))) else (splitter n (i+1) (acc++[x]) xs)

--------------------------

logBase2 :: Floating a => a -> a

logBase2 n = logBase 2 n

--------------------------

getNumBits :: (Integral a, RealFloat a1) =>a1 -> [Char] -> [c] -> a

getNumBits _  "directMap" cache = round (logBase2 (fromIntegral(length cache)))

getNumBits _ "fullyAssoc" _ = 0

getNumBits n "setAssoc" _ = round (logBase2 n)

--------------------------

fillZeros :: [Char] -> Int -> [Char]

fillZeros l n = if n==0 then l else ('0':(fillZeros l (n-1)))

-----------getDataFromCache------------------

data Output a = Out (a, Int) | NoOutput deriving (Show, Eq)

getTagandInd stringAddress bit= (mod address (10^bit), div address (10^bit)) where address = read stringAddress :: Int
 
findData stringAddress cache bitsNum = cache !! (convertBinToDec index) where (index,_) = getTagandInd stringAddress bitsNum




helpSearch [] _ _ = NoOutput

helpSearch (h:xs) t hop = if ((getValidIt h)&& (getTagIt h == t)) then Out (getDataIt h,hop) else helpSearch xs t (hop+1)

getIdx l n = reverse (helpA l n)

helpA l 0 = []

helpA l n =((last l):(helpA (init l) (n-1))) 

getTag :: (Eq t, Num t) => [a] -> t -> [a]

getTag l 0 = l

getTag l n = init (getTag l (n-1))




getfully _ [] "fullyAssoc" _ _ =NoOutput
getfully stringAddress (x:xs) "fullyAssoc" bitsNum hopsNum|((read stringAddress)==((getTagIt x))&&getValidIt x) =Out ((getDataIt x),hopsNum) |otherwise =(getfully stringAddress xs "fullyAssoc" bitsNum (hopsNum+1))




getDataFromCache stringAddress cache "directMap" bitsNum 
    |(valid && tagNeeded==tagFound) = Out (dataFrom,0)
    |otherwise = NoOutput
    where ((index,tagNeeded),It (T tagFound) (D dataFrom) valid _ )=( getTagandInd stringAddress bitsNum, findData stringAddress  cache bitsNum )



getDataFromCache stringAddress cache "fullyAssoc" bitsNum= getfully stringAddress cache "fullyAssoc" bitsNum 0

getDataFromCache stringAddress cache "setAssoc" bitsNum = helpSearch ((splitEvery (div (length cache) (2^bitsNum)) cache )!!(convertBinToDec (read (getIdx stringAddress bitsNum) :: Int))) (read (getTag stringAddress bitsNum) :: Int) 0



--------------------------------------


---------convertAddress---------------


convertAddress address bit "directMap" = (div address (10^bit),mod address (10^bit))

convertAddress binAddress bitsNum "fullyAssoc"=(binAddress,bitsNum)       

convertAddress binAddress bitsNum "setAssoc" = ((read (if (getTag (show binAddress) bitsNum)=="" then "0" else (getTag (show binAddress) bitsNum)) :: Int),(read (if (getIdx (show binAddress) bitsNum)=="" then "0" else (getIdx (show binAddress) bitsNum)) :: Int))


--------------------------------------
--------replaceInCache----------------

convertStringtoInt string = read string :: Int

getIndex tag idx bit =convertBinToDec( convertStringtoInt((show tag)++(fillZeros(show idx)(bit- length(show idx)))))



getReplacedIdx [] _ id _=id

getReplacedIdx (x:xs) item id curr |(getValidIt x)==False =curr |(getOrderIt x)>=(getOrderIt item) = (getReplacedIdx xs x curr (curr+1)) |otherwise = (getReplacedIdx xs item id (curr+1))



replaceInCache tag idx memory oldCache "setAssoc" bitsNum =(d,foldr (++) [] (replaceIthItem (replaceIthItem (It (T tag) (D d) True 0) ss (getReplacedIdx ss (ss!!0) 0 0)) (s) (convertBinToDec idx))) where (d,s,ss)=(memory!!(convertBinToDec (read ((fillZeros (show tag) (6-bitsNum-(length (show tag))))++(fillZeros (show idx) (bitsNum-(length (show idx))))) :: Int)),(splitEvery (div (length oldCache) (2^bitsNum)) oldCache),(map (\x -> if(getValidIt x)==True then (It (T (getTagIt x)) (D (getDataIt x)) True ((getOrderIt x)+1)) else x)  (s!!(convertBinToDec idx))))



replaceInCache tag idx memory oldCache "directMap" bitsNum = (memory!!(getIndex tag idx bitsNum),replaceIthItem (It (T tag) (D (memory!!(getIndex tag idx bitsNum))) True 0) oldCache (convertBinToDec idx))


replaceInCache tag idx memory oldCache "fullyAssoc" bitsNum | (help4 oldCache) = ((memory!!(convertBinToDec tag))     , (help1  tag idx memory (help3 oldCache) bitsNum ((help2 oldCache)+1))) | otherwise = ((memory!!(convertBinToDec tag))     , (help  tag idx memory (help3 oldCache) bitsNum))




help tag idx memory [] bitsNum =[]
help tag idx memory ((It (T tag1) (D this) bol order ):xs) bitsNum | bol==False = ((It (T tag) (D (memory!!(convertBinToDec tag))) True 0 ):xs) | otherwise = ((It (T tag1) (D this) bol order ):(help tag idx memory xs bitsNum))

help2 [] =0
help2 ((It (T tag1) (D this) bol order ):xs) | order > (help2 xs) = order | otherwise = (help2 xs)

help1 tag idx memory ((It (T tag1) (D this) bol order ):xs) bitsNum h2  | (order==h2) = ((It (T tag) (D (memory!!(convertBinToDec tag))) True 0 ):xs) | otherwise = ((It (T tag1) (D this) bol order ):(help1 tag idx memory xs bitsNum h2))
help3 []=[]
help3 ((It (T tag1) (D this) bol order ):xs) = if (bol==True) then ((It (T tag1) (D this) bol (order + 1)):(help3 xs))  else ((It (T tag1) (D this) bol order):(help3 xs))
help4 [] = True
help4 ((It (T tag) (D this) bol order ):xs) | bol==True = (help4 xs) | otherwise = False


---------------------------------------------------
-----------------preDefined------------------------

getData stringAddress cache memory cacheType bitsNum
    | x == NoOutput = replaceInCache tag index memory cache cacheType bitsNum
    | otherwise = (getX x, cache)
     where
          x = getDataFromCache stringAddress cache cacheType bitsNum
          address = read stringAddress:: Int
          (tag, index) = convertAddress address bitsNum cacheType
          getX (Out (d, _)) = d

runProgram [] cache _ _ _ = ([], cache)
runProgram (addr: xs) cache memory cacheType numOfSets =((d:prevData), finalCache)
          where
               bitsNum = round(logBase2 numOfSets)
               (d, updatedCache) = getData addr cache memory cacheType bitsNum
               (prevData, finalCache) = runProgram xs updatedCache memory cacheType numOfSets

