-- XXX We are using head/tail at one place
#if __GLASGOW_HASKELL__ >= 908
{-# OPTIONS_GHC -Wno-x-partial #-}
#endif

module Main (main) where

import Control.Applicative ((<|>))
import Control.Exception (SomeException(..), try)
import Data.Either (fromRight)
import Data.Word (Word8, Word32, Word64)
import Streamly.Test.Common (listEquals, checkListEqual, chooseInt)
import Test.Hspec (Spec, hspec, describe, it, expectationFailure, shouldBe)
import Test.Hspec.QuickCheck
import Test.QuickCheck
       (arbitrary, forAll, elements, Property,
        property, listOf, vectorOf, (.&&.), Gen)
import Test.QuickCheck.Monadic (monadicIO, assert, run)

import qualified Data.List as List
import qualified Prelude
import qualified Streamly.Data.Stream as S
import qualified Streamly.Internal.Data.Array as A
import qualified Streamly.Internal.Data.Fold as FL
import qualified Streamly.Internal.Data.Parser as P
import qualified Streamly.Internal.Data.Parser as Parser
import qualified Streamly.Internal.Data.ParserK as ParserK
import qualified Streamly.Internal.Data.Producer as Producer
import qualified Streamly.Internal.Data.Stream as S
import qualified Streamly.Internal.Data.Stream as Stream
import qualified Streamly.Internal.Data.StreamK as StreamK
import qualified Streamly.Internal.Data.Stream as D
import qualified Streamly.Internal.Data.Unfold as Unfold
import qualified Test.Hspec as H

import Prelude hiding (sequence)

#if MIN_VERSION_QuickCheck(2,14,0)

import Test.QuickCheck (chooseAny)
import Control.Monad.Identity (runIdentity, Identity (Identity))

#else

import System.Random (Random(random))
import Test.QuickCheck.Gen (Gen(MkGen))

-- | Generates a random element over the natural range of `a`.
chooseAny :: Random a => Gen a
chooseAny = MkGen (\r _ -> let (x,_) = random r in x)

#endif

maxTestCount :: Int
maxTestCount = 100

min_value :: Int
min_value = 0

mid_value :: Int
mid_value = 5000

max_value :: Int
max_value = 10000

max_length :: Int
max_length = 1000

toList :: Monad m => S.Stream m a -> m [a]
toList = S.fold FL.toList

-- Accumulator Tests

fromFold :: Property
fromFold =
    forAll (listOf $ chooseInt (min_value, max_value))
      $ \ls ->
            case (==) <$> runIdentity (S.parseD (P.fromFold FL.sum) (S.fromList ls))
                   <*> (S.fold FL.sum (S.fromList ls)) of
                Right is_equal -> is_equal
                Left _ -> False

fromPure :: Property
fromPure =
    forAll (chooseInt (min_value, max_value)) $ \x ->
        case runIdentity $ S.parseD (P.fromPure x) (S.fromList [1 :: Int]) of
            Right r -> r == x
            Left _ -> False

fromEffect :: Property
fromEffect =
    forAll (chooseInt (min_value, max_value)) $ \x ->
        case runIdentity $ S.parseD (P.fromEffect $ return x) (S.fromList [1 :: Int]) of
            Right r -> r == x
            Left _ -> False

die :: Property
die =
    property $
    case runIdentity (S.parseD (P.die "die test") (S.fromList [0 :: Int])) of
        Right _ -> False
        Left _ -> True

dieM :: Property
dieM =
    property $
    case runIdentity (S.parseD (P.dieM (Identity "die test")) (S.fromList [0 :: Int])) of
        Right _ -> False
        Left _ -> True

-- Element Parser Tests

peekPass :: Property
peekPass =
    forAll (chooseInt (1, max_length)) $ \list_length ->
        forAll (vectorOf list_length (chooseInt (min_value, max_value))) $ \ls ->
            case runIdentity $ S.parseD P.peek (S.fromList ls) of
                Right head_value -> case ls of
                    head_ls : _ -> head_value == head_ls
                    _ -> False
                Left _ -> False

peekFail :: Property
peekFail =
    property (case runIdentity $ S.parseD P.peek (S.fromList []) of
        Right _ -> False
        Left _ -> True)

eofPass :: Property
eofPass =
    property (case S.parseD P.eof (S.fromList []) of
        Right _ -> True
        Left _ -> False)

eofFail :: Property
eofFail =
    forAll (chooseInt (1, max_length)) $ \list_length ->
        forAll (vectorOf list_length (chooseInt (min_value, max_value))) $ \ls ->
            case runIdentity $ S.parseD P.eof (S.fromList ls) of
                Right _ -> False
                Left _ -> True

satisfyPass :: Property
satisfyPass =
    forAll (chooseInt (mid_value, max_value)) $ \first_element ->
        forAll (listOf (chooseInt (min_value, max_value))) $ \ls_tail ->
            let
                ls = first_element : ls_tail
                predicate = (>= mid_value)
            in
                case runIdentity $ S.parseD (P.satisfy predicate) (S.fromList ls) of
                    Right r -> r == first_element
                    Left _ -> False

satisfy :: Property
satisfy =
    forAll (listOf (chooseInt (min_value, max_value))) $ \ls ->
        case runIdentity $ S.parseD (P.satisfy predicate) (S.fromList ls) of
            Right r -> case ls of
                [] -> False
                (x : _) -> predicate x && (r == x)
            Left _ -> case ls of
                [] -> True
                (x : _) -> not $ predicate x
        where
            predicate = (>= mid_value)

-- Sequence Parsers Tests
takeBetweenPass :: Property
takeBetweenPass =
    forAll (chooseInt (min_value, max_value)) $ \m ->
        forAll (chooseInt (m, max_value)) $ \n ->
            forAll (chooseInt (m, max_value)) $ \list_length ->
                forAll (vectorOf list_length (chooseInt (min_value, max_value))) $ \ls ->
                    case runIdentity $ S.parseD (P.takeBetween m n FL.toList) (S.fromList ls) of
                        Right parsed_list ->
                            let lpl = Prelude.length parsed_list
                            in checkListEqual parsed_list (Prelude.take lpl ls)
                        Left _ -> property False


takeBetween :: Property
takeBetween =
    forAll (chooseInt (min_value, max_value)) $ \m ->
        forAll (chooseInt (min_value, max_value)) $ \n ->
            forAll (listOf (chooseInt (min_value, max_value))) $ \ls ->
                let
                    list_length = Prelude.length ls
                in monadicIO $ do
                    let p = P.takeBetween m n FL.toList
                    r <- run $ try $ S.parseD p (S.fromList ls)
                    return $ case r of
                        Right x -> case x of
                            Right parsed_list ->
                                if m <= list_length && n >= m
                                then
                                    let len = Prelude.length parsed_list
                                    in checkListEqual
                                            parsed_list (Prelude.take len ls)
                                else property False
                            Left _ ->
                                property (m > n || list_length < m)
                        Left (_ :: SomeException) ->
                            property (m > n || list_length < m)

take :: Property
take =
    forAll (chooseInt (min_value, max_value)) $ \n ->
        forAll (listOf (chooseInt (min_value, max_value))) $ \ls ->
            case runIdentity $ S.parseD (P.fromFold $ FL.take n FL.toList) (S.fromList ls) of
                Right parsed_list -> checkListEqual parsed_list (Prelude.take n ls)
                Left _ -> property False

takeEQPass :: Property
takeEQPass =
    forAll (chooseInt (min_value, max_value)) $ \n ->
        forAll (chooseInt (n, max_value)) $ \list_length ->
            forAll (vectorOf list_length (chooseInt (min_value, max_value))) $ \ls ->
                case runIdentity $ S.parseD (P.takeEQ n FL.toList) (S.fromList ls) of
                    Right parsed_list -> checkListEqual parsed_list (Prelude.take n ls)
                    Left _ -> property False

takeEQ :: Property
takeEQ =
    forAll (chooseInt (min_value, max_value)) $ \n ->
        forAll (listOf (chooseInt (min_value, max_value))) $ \ls ->
            let
                list_length = Prelude.length ls
            in
                case runIdentity $ S.parseD (P.takeEQ n FL.toList) (S.fromList ls) of
                    Right parsed_list ->
                        if (n <= list_length) then
                            checkListEqual parsed_list (Prelude.take n ls)
                        else
                            property False
                    Left _ -> property (n > list_length)

takeGEPass :: Property
takeGEPass =
    forAll (chooseInt (min_value, max_value)) $ \n ->
        forAll (chooseInt (n, max_value)) $ \list_length ->
            forAll (vectorOf list_length (chooseInt (min_value, max_value))) $ \ls ->
                case runIdentity $ S.parseD (P.takeGE n FL.toList) (S.fromList ls) of
                    Right parsed_list -> checkListEqual parsed_list ls
                    Left _ -> property False

takeGE :: Property
takeGE =
    forAll (chooseInt (min_value, max_value)) $ \n ->
        forAll (listOf (chooseInt (min_value, max_value))) $ \ls ->
            let
                list_length = Prelude.length ls
            in
                case runIdentity $ S.parseD (P.takeGE n FL.toList) (S.fromList ls) of
                    Right parsed_list ->
                        if (n <= list_length) then
                            checkListEqual parsed_list ls
                        else
                            property False
                    Left _ -> property (n > list_length)

nLessThanEqual0 ::
       (  Int
       -> FL.Fold Identity Int [Int]
       -> P.Parser Int Identity [Int]
       )
    -> (Int -> [Int] -> [Int])
    -> Property
nLessThanEqual0 tk ltk =
    forAll (elements [0, (-1)]) $ \n ->
        forAll (listOf arbitrary) $ \ls ->
            case runIdentity $ S.parseD (tk n FL.toList) (S.fromList ls) of
                Right parsed_list -> checkListEqual parsed_list (ltk n ls)
                Left _ -> property False

takeProperties :: Spec
takeProperties =
    describe "take combinators when n <= 0/" $ do
        prop "takeEQ n FL.toList = []" $
            nLessThanEqual0 P.takeEQ (\_ -> const [])
        prop "takeGE n FL.toList xs = xs" $
            nLessThanEqual0 P.takeGE (\_ -> id)


-- XXX lookAhead can't deal with EOF which in this case means when
-- n==list_length, this test will fail. So excluding that case for now.
lookAheadPass :: Property
lookAheadPass =
    forAll (chooseInt (min_value, max_value)) $ \n ->
        let
            takeWithoutConsume = P.lookAhead $ P.fromFold $ FL.take n FL.toList
            parseTwice = do
                parsed_list_1 <- takeWithoutConsume
                parsed_list_2 <- takeWithoutConsume
                return (parsed_list_1, parsed_list_2)
        in
            forAll (chooseInt (n+1, max_value)) $ \list_length ->
                forAll (vectorOf list_length (chooseInt (min_value, max_value))) $ \ls ->
                    case runIdentity $ S.parseD parseTwice (S.fromList ls) of
                        Right (ls_1, ls_2) -> checkListEqual ls_1 ls_2 .&&. checkListEqual ls_1 (Prelude.take n ls)
                        Left _ -> property $ False

lookAhead :: Property
lookAhead =
    forAll (chooseInt (min_value, max_value)) $ \n ->
        let
            takeWithoutConsume = P.lookAhead $ P.fromFold $ FL.take n FL.toList
            parseTwice = do
                parsed_list_1 <- takeWithoutConsume
                parsed_list_2 <- takeWithoutConsume
                return (parsed_list_1, parsed_list_2)
        in
            forAll (listOf (chooseInt (min_value, max_value))) $ \ls ->
                case runIdentity $ S.parseD parseTwice (S.fromList ls) of
                    Right (ls_1, ls_2) -> checkListEqual ls_1 ls_2 .&&. checkListEqual ls_1 (Prelude.take n ls)
                    Left _ -> property ((list_length < n) || (list_length == n && n == 0))
                        where
                            list_length = Prelude.length ls

takeWhile :: Property
takeWhile =
    forAll (listOf (chooseInt (0, 1))) $ \ ls ->
        case runIdentity $ S.parseD (P.takeWhile predicate FL.toList) (S.fromList ls) of
            Right parsed_list -> checkListEqual parsed_list (Prelude.takeWhile predicate ls)
            Left _ -> property False
        where
            predicate = (== 0)

takeWhile1 :: Property
takeWhile1 =
    forAll (listOf (chooseInt (0, 1))) $ \ ls ->
        case runIdentity $ S.parseD (P.takeWhile1 predicate  FL.toList) (S.fromList ls) of
            Right parsed_list -> case ls of
                [] -> property False
                (x : _) ->
                    if predicate x then
                        checkListEqual parsed_list (Prelude.takeWhile predicate ls)
                    else
                        property False
            Left _ -> case ls of
                [] -> property True
                (x : _) -> property (not $ predicate x)
        where
            predicate = (== 0)

groupBy :: Property
groupBy =
    forAll (listOf (chooseInt (0, 1)))
        $ \ls ->
              case runIdentity $ S.parseD parser (S.fromList ls) of
                  Right parsed -> checkListEqual parsed (groupByLF ls)
                  Left _ -> property False

    where

    cmp = (==)
    parser = P.groupBy cmp FL.toList
    groupByLF lst
        | null lst = []
        | otherwise = head $ List.groupBy cmp lst

groupByRolling :: Property
groupByRolling =
    forAll (listOf (chooseInt (0, 1)))
        $ \ls ->
              case runIdentity $ S.parseD parser (S.fromList ls) of
                  Right parsed -> checkListEqual parsed (groupByLF Nothing ls)
                  Left _ -> property False

    where

    cmp = (==)
    parser = P.groupBy cmp FL.toList
    groupByLF _ [] = []
    groupByLF Nothing (x:xs) = x : groupByLF (Just x) xs
    groupByLF (Just y) (x:xs) =
        if cmp y x
        then x : groupByLF (Just x) xs
        else []

takeEndByOrMax :: Property
takeEndByOrMax =
    forAll (chooseInt (min_value, max_value)) $ \n ->
        forAll (listOf (chooseInt (0, 1))) $ \ls ->
            case runIdentity $ S.parseD (P.fromFold $ FL.takeEndBy_ predicate (FL.take n FL.toList)) (S.fromList ls) of
                Right parsed_list -> checkListEqual parsed_list (Prelude.take n (Prelude.takeWhile (not . predicate) ls))
                Left _ -> property False
            where
                predicate = (== 1)

wordBy :: Property
wordBy =
    forAll (listOf (elements [' ', 's']))
        $ \ls ->
              case runIdentity $ S.parseD parser (S.fromList ls) of
                  Right parsed -> checkListEqual parsed (words' ls)
                  Left _ -> property False

    where

    predicate = (== ' ')
    parser = P.many (P.wordBy predicate FL.toList) FL.toList
    words' lst =
        let wrds = words lst
         in if wrds == [] && length lst > 0 then [""] else wrds


splitWith :: Property
splitWith =
    forAll (listOf (chooseInt (0, 1))) $ \ls ->
        case runIdentity $ S.parseD (P.splitWith (,) (P.satisfy (== 0)) (P.satisfy (== 1))) (S.fromList ls) of
            Right (result_first, result_second) -> case ls of
                0 : 1 : _ -> (result_first == 0) && (result_second == 1)
                _ -> False
            Left _ -> case ls of
                0 : 1 : _ -> False
                _ -> True

splitWithFailLeft :: Property
splitWithFailLeft =
    property (case runIdentity $ S.parseD (P.splitWith (,) (P.die "die") (P.fromPure (1 :: Int))) (S.fromList [1 :: Int]) of
        Right _ -> False
        Left _ -> True)

splitWithFailRight :: Property
splitWithFailRight =
    property (case runIdentity $ S.parseD (P.splitWith (,) (P.fromPure (1 :: Int)) (P.die "die")) (S.fromList [1 :: Int]) of
        Right _ -> False
        Left _ -> True)

splitWithFailBoth :: Property
splitWithFailBoth =
    property (case runIdentity $ S.parseD (P.splitWith (,) (P.die "die") (P.die "die")) (S.fromList [1 :: Int]) of
        Right _ -> False
        Left _ -> True)

{-
teeWithPass :: Property
teeWithPass =
    forAll (chooseInt (min_value, max_value)) $ \n ->
        forAll (listOf (chooseInt (0, 1))) $ \ls ->
            let
                prsr = P.fromFold $ FL.take n FL.toList
            in
                case S.parseD (P.teeWith (,) prsr prsr) (S.fromList ls) of
                    Right (ls_1, ls_2) -> checkListEqual (Prelude.take n ls) ls_1 .&&. checkListEqual ls_1 ls_2
                    Left _ -> property False

teeWithFailLeft :: Property
teeWithFailLeft =
    property (case S.parseD (P.teeWith (,) (P.die "die") (P.fromPure (1 :: Int))) (S.fromList [1 :: Int]) of
        Right _ -> False
        Left _ -> True)

teeWithFailRight :: Property
teeWithFailRight =
    property (case S.parseD (P.teeWith (,) (P.fromPure (1 :: Int)) (P.die "die")) (S.fromList [1 :: Int]) of
        Right _ -> False
        Left _ -> True)

teeWithFailBoth :: Property
teeWithFailBoth =
    property (case S.parseD (P.teeWith (,) (P.die "die") (P.die "die")) (S.fromList [1 :: Int]) of
        Right _ -> False
        Left _ -> True)

shortestPass :: Property
shortestPass =
    forAll (listOf (chooseInt(min_value, max_value))) $ \ls ->
        let
            half_mid_value = mid_value `Prelude.div` 2
            prsr_1 = P.takeWhile (<= half_mid_value) FL.toList
            prsr_2 = P.takeWhile (<= mid_value) FL.toList
            prsr_shortest = P.shortest prsr_1 prsr_2
        in
            case S.parseD prsr_shortest (S.fromList ls) of
                Right short_list -> checkListEqual short_list (Prelude.takeWhile (<= half_mid_value) ls)
                Left _ -> property False

shortestPassLeft :: Property
shortestPassLeft =
    property (case S.parseD (P.shortest (P.die "die") (P.fromPure (1 :: Int))) (S.fromList [1 :: Int]) of
        Right r -> r == 1
        Left _ -> False)

shortestPassRight :: Property
shortestPassRight =
    property (case S.parseD (P.shortest (P.fromPure (1 :: Int)) (P.die "die")) (S.fromList [1 :: Int]) of
        Right r -> r == 1
        Left _ -> False)

shortestFailBoth :: Property
shortestFailBoth =
    property
        (case S.parseD
                  (P.shortest (P.die "die") (P.die "die"))
                  (S.fromList [1 :: Int]) of
             Right _ -> False
             Left _ -> True)

longestPass :: Property
longestPass =
    forAll (listOf (chooseInt(min_value, max_value))) $ \ls ->
        let
            half_mid_value = mid_value `Prelude.div` 2
            prsr_1 = P.takeWhile (<= half_mid_value) FL.toList
            prsr_2 = P.takeWhile (<= mid_value) FL.toList
            prsr_longest = P.longest prsr_1 prsr_2
        in
            case S.parseD prsr_longest (S.fromList ls) of
                Right long_list -> long_list == Prelude.takeWhile (<= mid_value) ls
                Left _ -> False

longestPassLeft :: Property
longestPassLeft =
    property (case S.parseD (P.shortest (P.die "die") (P.fromPure (1 :: Int))) (S.fromList [1 :: Int]) of
        Right r -> r == 1
        Left _ -> False)

longestPassRight :: Property
longestPassRight =
    property (case S.parseD (P.shortest (P.fromPure (1 :: Int)) (P.die "die")) (S.fromList [1 :: Int]) of
        Right r -> r == 1
        Left _ -> False)

longestFailBoth :: Property
longestFailBoth =
    property
        (case S.parseD (P.shortest (P.die "die") (P.die "die")) (S.fromList [1 :: Int]) of
        Right _ -> False
        Left _ -> True)
-}

many :: Property
many =
    forAll (listOf (chooseInt (0, 1)))
      $ \ls ->
            let fldstp conL currL = return $ FL.Partial (conL ++ currL)
                concatFold =
                    FL.Fold fldstp (return (FL.Partial [])) return return
                prsr =
                    flip P.many concatFold
                        $ P.fromFold $ FL.takeEndBy_ (== 1) FL.toList
             in case runIdentity $ S.parseD prsr (S.fromList ls) of
                    Right res_list ->
                        checkListEqual res_list (Prelude.filter (== 0) ls)
                    Left _ -> property False

many_empty :: Property
many_empty =
    property (case runIdentity $ S.parseD (flip P.many FL.toList (P.die "die")) (S.fromList [1 :: Int]) of
        Right res_list -> checkListEqual res_list ([] :: [Int])
        Left _ -> property False)

some :: Property
some =
    forAll (listOf (chooseInt (0, 1)))
      $ \ls ->
            let fldstp conL currL = return $ FL.Partial $ conL ++ currL
                concatFold = FL.Fold fldstp (return (FL.Partial [])) return return
                prsr =
                    flip P.some concatFold
                        $ P.fromFold $ FL.takeEndBy_ (== 1) FL.toList
             in case runIdentity $ S.parseD prsr (S.fromList ls) of
                    Right res_list -> res_list == Prelude.filter (== 0) ls
                    Left _ -> False

someFail :: Property
someFail =
    property (case runIdentity $ S.parseD (P.some (P.die "die") FL.toList) (S.fromList [1 :: Int]) of
        Right _ -> False
        Left _ -> True)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

applicative :: Property
applicative =
    forAll (listOf (chooseAny :: Gen Int)) $ \ list1 ->
        forAll (listOf (chooseAny :: Gen Int)) $ \ list2 ->
            monadicIO $ do
            let parser =
                        (,)
                            <$> P.fromFold (FL.take (length list1) FL.toList)
                            <*> P.fromFold (FL.take (length list2) FL.toList)

            return $
                case runIdentity $ S.parseD parser (S.fromList $ list1 ++ list2) of
                    Right (olist1, olist2) -> olist1 == list1 && olist2 == list2
                    Left _ -> False

sequence :: Property
sequence =
    forAll (vectorOf 11 (listOf (chooseAny :: Gen Int))) $ \ ins ->
        monadicIO $ do
        let parsers = fmap (\xs -> P.fromFold $ FL.take (length xs) FL.toList) ins
        outs <- S.parseD
                    (Prelude.sequence parsers)
                    (S.fromList $ concat ins)
        return $
            case outs of
                Right x -> x == ins
                Left _ -> False

altEOF1 :: Property
altEOF1 =
    monadicIO $ do
    s1 <- S.parseD
        (P.satisfy (> 0) <|> return 66)
        (S.fromList ([]::[Int]))
    return $
        case s1 of
            Right x -> x == 66
            Left _ -> False

altEOF2 :: Property
altEOF2 =
    monadicIO $ do
    s1 <- S.parseD
        ((P.takeEQ 2 FL.toList) <|> (P.takeEQ 1 FL.toList))
        (S.fromList ([51]::[Int]))
    return $
        case s1 of
            Right x -> x == [51]
            Left _ -> False

monad :: Property
monad =
    forAll (listOf (chooseAny :: Gen Int)) $ \ list1 ->
        forAll (listOf (chooseAny :: Gen Int)) $ \ list2 ->
            monadicIO $ do
            let parser = do
                            olist1 <- P.fromFold (FL.take (length list1) FL.toList)
                            olist2 <- P.fromFold (FL.take (length list2) FL.toList)
                            return (olist1, olist2)
            s1 <- S.parseD parser (S.fromList $ list1 ++ list2)
            return $
                case s1 of
                Right (olist1, olist2) -> olist1 == list1 && olist2 == list2
                Left _ -> False

-------------------------------------------------------------------------------
-- Stream parsing
-------------------------------------------------------------------------------

parseMany :: Property
parseMany =
    forAll (chooseInt (1,100)) $ \len ->
        forAll (listOf (vectorOf len (chooseAny :: Gen Int))) $ \ ins ->
            monadicIO $ do
            outs <-
                (toList $ S.catRights $ S.parseManyD
                    (P.fromFold $ FL.take len FL.toList) (S.fromList $ concat ins)
                )
            return $ outs == ins

-- basic sanity test for parsing from arrays
parseUnfold :: Property
parseUnfold = do
    let len = 200
    -- ls = input list (stream)
    -- clen = chunk size
    -- tlen = parser take size
    forAll
        ((,,)
            <$> vectorOf len (chooseAny :: Gen Int)
            <*> chooseInt (1, len)
            <*> chooseInt (1, len)) $ \(ls, clen, tlen) ->
        monadicIO $ do
            arrays <- toList $ S.chunksOf clen (S.fromList ls)
            let src = Producer.source (Just (Producer.OuterLoop arrays))
            let parser = P.fromFold (FL.take tlen FL.toList)
            let readSrc =
                    Producer.producer
                        $ Producer.concat Producer.fromList A.producer
            let streamParser =
                    Producer.simplify (Producer.parseManyD parser readSrc)
            xs <- run
                $ toList
                $ S.unfoldMany Unfold.fromList
                $ S.catRights
                $ S.unfold streamParser src

            listEquals (==) xs ls

parserSequence :: Property
parserSequence =
  forAll (vectorOf 11 (listOf (chooseAny :: Gen Int))) $ \ins ->
    monadicIO $ do
    let parsers = D.fromList
            $ fmap (\xs -> P.fromFold $ FL.take (length xs) FL.sum) ins
    let sequencedParser = P.sequence parsers FL.sum
    outs <-
        S.parseD sequencedParser $ S.concatMap S.fromList (S.fromList ins)
    return $
        case outs of
            Right x -> x == sum (map sum ins)
            Left _ -> False

-------------------------------------------------------------------------------
-- Test for a particular case hit during fs events testing
-------------------------------------------------------------------------------

evId :: [Word8]
evId = [96,238,17,9,0,0,0,0]

evFlags :: [Word8]
evFlags = [0,4,1,0,0,0,0,0]

evPathLen :: [Word8]
evPathLen = [71,0,0,0,0,0,0,0]

evPath :: [Word8]
evPath =
    [47,85,115,101,114,115,47,118,111,108,47,118,101,109,98,97,47,99,111,109
    ,112,111,115,101,119,101 ,108,108,45,116,101,99,104,47,69,110,103,47,112
    ,114,111,106,101,99,116,115,47,115,116,114,101,97,109,108,121,47,115,116
    ,114,101,97,109,108,121,47,116,109,112,47,122,122
    ]

event :: [Word8]
event = evId ++ evFlags ++ evPathLen ++ evPath

data Event = Event
   { eventId :: Word64
   , eventFlags :: Word32
   , eventAbsPath :: A.Array Word8
   } deriving (Show, Ord, Eq)

readOneEvent :: P.Parser Word8 IO Event
readOneEvent = do
    arr <- P.takeEQ 24 (A.createOf 24)
    let arr1 = A.castUnsafe arr :: A.Array Word64
        eid = A.getIndexUnsafe 0 arr1
        eflags = A.getIndexUnsafe 1 arr1
        pathLen = fromIntegral $ A.getIndexUnsafe 2 arr1
    path <- P.takeEQ pathLen (A.createOf pathLen)
    return $ Event
        { eventId = eid
        , eventFlags = fromIntegral eflags
        , eventAbsPath = path
        }

parseMany2Events :: Property
parseMany2Events =
    monadicIO $ do
        xs <-
            ( run
            $ toList
            $ S.catRights
            $ S.parseManyD readOneEvent
            $ S.fromList (concat (replicate 2 event))
            )
        assert (length xs == 2)
        -- XXX assuming little endian machine
        let ev = Event
                { eventId = 152170080
                , eventFlags = 66560
                , eventAbsPath = A.fromList evPath
                }
         in listEquals (==) xs (replicate 2 ev)

toParser :: Spec
toParser = do
    let p = ParserK.toParser (ParserK.adapt Parser.one)
        runP xs = Stream.parse p (Stream.fromList xs)
    describe "toParser . adapt" $ do
        it "empty stream" $ do
            r1 <- runP ([] :: [Int])
            case r1 of
                Left e -> print e
                Right x ->
                    expectationFailure $ "Expecting failure, got: " ++ show x
        it "exact stream" $ do
            r2 <- runP [0::Int]
            fromRight undefined r2 `shouldBe` 0
        it "longer stream" $ do
            r3 <- runP [0,1::Int]
            fromRight undefined r3 `shouldBe` 0

    let p1 = ParserK.adapt $ ParserK.toParser (ParserK.adapt Parser.one)
        runP1 xs = StreamK.parse p1 (StreamK.fromStream $ Stream.fromList xs)
    describe "adapt . toParser . adapt" $ do
        it "empty stream" $ do
            r1 <- runP1 ([] :: [Int])
            case r1 of
                Left e -> print e
                Right x ->
                    expectationFailure $ "Expecting failure, got: " ++ show x
        it "exact stream" $ do
            r2 <- runP1 [0::Int]
            fromRight undefined r2 `shouldBe` 0
        it "longer stream" $ do
            r3 <- runP1 [0,1::Int]
            fromRight undefined r3 `shouldBe` 0

-------------------------------------------------------------------------------
-- Main
-------------------------------------------------------------------------------

moduleName :: String
moduleName = "Data.ParserK"

main :: IO ()
main =
  hspec $
  H.parallel $
  modifyMaxSuccess (const maxTestCount) $ do
  describe moduleName $ do

    describe "Instances" $ do
        prop "applicative" applicative
        prop "Alternative: end of input 1" altEOF1
        prop "Alternative: end of input 2" altEOF2
        prop "monad" monad
        prop "sequence" sequence

    describe "Stream parsing" $ do
        prop "parseMany" parseMany
        prop "parseMany2Events" parseMany2Events
        prop "parseUnfold" parseUnfold
        prop "parserSequence" parserSequence

    describe "test for accumulator" $ do
        prop "P.fromFold FL.sum = FL.sum" fromFold
        prop "fromPure value provided" fromPure
        prop "fromPure monadic value provided" fromEffect
        prop "always fail" die
        prop "always fail but monadic" dieM

    describe "test for element parser" $ do
        prop "peek = head with list length > 0" peekPass
        prop "peek fail on []" peekFail
        prop "eof pass on []" eofPass
        prop "eof fail on non-empty list" eofFail
        prop "first element exists and >= mid_value" satisfyPass
        prop "check first element exists and satisfies predicate" satisfy

    describe "test for sequence parser" $ do
        prop "P.takeBetween m n = Prelude.take when len >= m and len <= n"
                takeBetweenPass
        prop ("P.takeBetween m n = Prelude.take when len >= m and len <= n and"
            ++ " fail otherwise") takeBetween
        prop "P.take = Prelude.take" Main.take
        prop "P.takeEQ = Prelude.take when len >= n" takeEQPass
        prop "P.takeEQ = Prelude.take when len >= n and fail otherwise" Main.takeEQ
        prop "P.takeGE n ls = ls when len >= n" takeGEPass
        prop "P.takeGE n ls = ls when len >= n and fail otherwise" Main.takeGE
        prop "lookAhead . take n >> lookAhead . take n = lookAhead . take n" lookAheadPass
        prop "lookAhead . take n >> lookAhead . take n = lookAhead . take n, else fail" lookAhead
        prop "P.takeWhile = Prelude.takeWhile" Main.takeWhile
        prop "P.takeWhile1 = Prelude.takeWhile if taken something, else check why failed" takeWhile1
        prop "P.groupBy = Prelude.head . Prelude.groupBy" groupBy
        prop "groupByRolling" groupByRolling
        prop "P.takeEndByOrMax = Prelude.take n (Prelude.takeWhile (not . predicate)" takeEndByOrMax
        prop "many (P.wordBy ' ') = words'" wordBy
        prop "parse 0, then 1, else fail" splitWith
        prop "fail due to die as left parser" splitWithFailLeft
        prop "fail due to die as right parser" splitWithFailRight
        prop "fail due to die as both parsers" splitWithFailBoth
        {-
        prop "parsed two lists should be equal" teeWithPass
        prop "fail due to die as left parser" teeWithFailLeft
        prop "fail due to die as right parser" teeWithFailRight
        prop "fail due to die as both parsers" teeWithFailBoth
        prop "P.takeWhile (<= half_mid_value) = Prelude.takeWhile half_mid_value" shortestPass
        prop "pass even if die is left parser" shortestPassLeft
        prop "pass even if die is right parser" shortestPassRight
        prop "fail due to die as both parsers" shortestFailBoth
        prop "P.takeWhile (<= mid_value) = Prelude.takeWhile (<= mid_value)" longestPass
        prop "pass even if die is left parser" longestPassLeft
        prop "pass even if die is right parser" longestPassRight
        prop "fail due to die as both parsers" longestFailBoth
        -}
        prop "P.many concatFold $ P.takeEndBy_ (== 1) FL.toList = Prelude.filter (== 0)" many
        prop "[] due to parser being die" many_empty
        prop "P.some concatFold $ P.takeEndBy_ (== 1) FL.toList = Prelude.filter (== 0)" some
        prop "fail due to parser being die" someFail
    takeProperties
    toParser
