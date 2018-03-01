{-# LANGUAGE Strict #-}
{-# LANGUAGE StrictData #-}

binarySplitting p q r i 0 = (p i, q i * r i, r i)
binarySplitting p q r i n =
  let
     (a,  b,  c)  = binarySplitting p q r (2 * i - 1) (n - 1)
     (a', b', c') = binarySplitting p q r (2 * i) (n - 1)
  in (a * a', a * b' + b * c', c * c')

main :: IO ()
main = do
  s <- getLine
  let
    n = read s
    (_, x, y) =
      binarySplitting
        (\i -> (1 - 4 * i) * (2 * i - 1) * (4 * i - 3))
        (\i -> (21460 * i - 20337))
        (\i -> 24893568 * i * i * i) 1 $
      max 0 $ ceiling $ logBase 2 (fromIntegral n) - 1.55849716603186539
  putStrLn $ show $ 3528 * y * (10 ^ n) `div` x
