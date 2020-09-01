#!/usr/bin/env stack
-- stack --resolver lts-14.23 script --package split,scientific,MissingH,parsec

module Main where
import Text.ParserCombinators.Parsec
import Data.Char (isSpace)
import Data.CSV
import Data.List.Split
import Data.List
import Data.Maybe
import Data.Scientific
import Numeric

main :: IO ()
main = do
  c <- getContents
  case parse csvFile "(stdin)" c of
    Left e -> do putStrLn "Error parsing input:"
                 print e
    Right csv -> do
      let results = map (parseLine . take 2) $ tail csv
      let columns = nub.sort $ map (fst.fst) results
      putStrLn $ longifyTo 5 "n" ++ dropWhileEnd isSpace (concatMap longify columns)
      let resAt n col = longify $ fromMaybe "nan" $ lookup (col,n) results
      let resultrow n = concatMap (resAt n) columns
      let firstcol = nub.sort $ map (snd.fst) results
      let resultrows = map (\n -> longifyTo 5 (show n) ++ dropWhileEnd isSpace (resultrow n)) firstcol
      mapM_ putStrLn resultrows
  where
    parseLine [namestr,numberstr] = ((name,n),valuestr) where
      [name,nstr] = splitOn "/" namestr
      n = read nstr :: Integer
      value = toRealFloat (read numberstr :: Scientific) :: Double
      valuestr = Numeric.showFFloat (Just 7) value ""
    parseLine l = error $ "could not parse this line:\n  " ++ show l
    longify = longifyTo 14
    longifyTo n s = s ++ replicate (n - length s) ' '
