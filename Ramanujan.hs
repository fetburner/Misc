{-# LANGUAGE Strict #-}
{-# LANGUAGE StrictData #-}

main :: IO ()
main = do
  s <- getLine
  let
    n = read s
    (_, x, y) =
      binarySplitting 0 $
      max 1 $ ceiling $ fromIntegral n * 0.1697522772858307
  putStrLn $ show $ 3528 * y * (10 ^ n) `div` x
  where
    p i = (1 - 4 * i) * (2 * i - 1) * (4 * i - 3)
    q i = 21460 * i - 20337
    r i = 24893568 * i * i * i

    -- (n, m]
    binarySplitting n m
      | m - n <= 1 = (p m, q m * r m, r m)
      | otherwise  =
          let
             (a,  b,  c)  = binarySplitting n ((n + m) `div` 2)
             (a', b', c') = binarySplitting ((n + m) `div` 2) m
          in (a * a', a * b' + b * c', c * c')
