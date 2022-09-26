open import Aeres.Prelude

module Aeres.Foreign.Time where

{-# FOREIGN GHC import Data.Time #-}
{-# FOREIGN GHC import Data.Time.Clock #-}
{-# FOREIGN GHC import Data.Time.Calendar.OrdinalDate #-}
{-# FOREIGN GHC import Data.Time.Calendar.MonthDay #-}
{-# FOREIGN GHC import Data.Time.LocalTime #-}

{-# FOREIGN GHC

year :: UTCTime -> Integer
year = fst . toOrdinalDate . utctDay

month :: UTCTime -> Integer
month x = toInteger . fst . dayOfYearToMonthAndDay (isLeapYear . year $ x) . snd . toOrdinalDate . utctDay $ x

day :: UTCTime -> Integer
day x = toInteger . snd . dayOfYearToMonthAndDay (isLeapYear . year $ x) . snd . toOrdinalDate . utctDay $ x

hour :: UTCTime -> Integer
hour = toInteger . todHour . timeToTimeOfDay . utctDayTime

minute :: UTCTime -> Integer
minute = toInteger . todMin . timeToTimeOfDay . utctDayTime

second :: UTCTime -> Integer
second = fst . properFraction . todSec . timeToTimeOfDay . utctDayTime
#-}

postulate
  UTCTime Day : Set

module UTC where
  postulate
    year   : UTCTime → ℕ
    month  : UTCTime → ℕ
    day    : UTCTime → ℕ
    hour   : UTCTime → ℕ
    minute : UTCTime → ℕ
    second : UTCTime → ℕ

{-# COMPILE GHC UTCTime    = type UTCTime #-}
{-# COMPILE GHC Day        = type Day #-}
{-# COMPILE GHC UTC.year   = year  #-}
{-# COMPILE GHC UTC.month  = month  #-}
{-# COMPILE GHC UTC.day    = day  #-}
{-# COMPILE GHC UTC.hour   = hour  #-}
{-# COMPILE GHC UTC.minute = minute  #-}
{-# COMPILE GHC UTC.second = second  #-}
