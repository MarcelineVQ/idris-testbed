module TimeIt

import Control.Monad.Managed
import System.Clock
import Data.IORef

import Data.Nat

import public System

import Control.Monad.State

-- showTime doesn't pad nanoseconds properly

showTime' : Clock Duration -> String
showTime' t = show $ (cast {to=Double} (seconds t)) + (cast {to=Double} (nanoseconds t) / 1000000000)

export
timeItT : HasIO io => String -> io a -> io (Clock Duration,a)
timeItT str act = do
  now <- liftIO $ clockTime Monotonic
  r <- act
  later <- liftIO $ clockTime Monotonic
  let dif = timeDifference later now
  putStrLn $ str ++ ": " ++ showTime' dif
  pure (dif,r)

export
timeIt : HasIO io => String -> io a -> io a
timeIt str act = snd <$> timeItT str act

-- export
-- withTime : IO a -> (Clock Duration -> IO a) -> IO a
-- withTime act f = do
--   now <- liftIO $ clockTime Monotonic
--   r <- act
--   later <- liftIO $ clockTime Monotonic
--   let dif = timeDifference later now
--   printLn $ (seconds dif, nanoseconds dif)
--   pure r

-- export
-- managedTime : Managed (Clock Duration)
-- managedTime = managed withTi

-- youtube-dl -o "%(autonumber)s-%(title)s.%(ext)s"  --cookies ../cooks.txt -f http-540p
