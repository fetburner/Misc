{-# LANGUAGE Strict #-}
{-# LANGUAGE StrictData #-}

main :: IO ()
main = do
  s <- getLine
  let
    n = read s
    (_, x, y) = go 1 $ max 0 $ ceiling $
      logBase 2 (fromIntegral n) - 1.55849716603186539
  putStrLn $ show $ 3528 * y * (10 ^ n) `div` x

  where
    go i 0 =
      ( (1 - 4 * i) * (2 * i - 1) * (4 * i - 3)
      , 24893568 * i * i * i * (21460 * i - 20337)
      , 24893568 * i * i * i )
    go i n =
      let
        (a,  b,  c)  = go (2 * i - 1) (n - 1) 
        (a', b', c') = go (2 * i) (n - 1)
      in (a * a', a * b' + b * c', c * c')
