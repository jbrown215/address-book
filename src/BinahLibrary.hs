{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE QuasiQuotes                #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}

{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--no-totality"                         @-}
{-@ LIQUID "--no-pattern-inline"                         @-}

module BinahLibrary where
import           Prelude hiding (filter)
import           Control.Monad.IO.Class  (liftIO, MonadIO)
import           Control.Monad.Trans.Reader
import           Database.Persist
import           Model
import           Data.Text hiding (map, filter)
import           TaggedUser
import           TaggedEmail
import           TaggedPerson
import           TaggedFriends

data RefinedPersistFilter = EQUAL | NE | LE | LTP | GE | GTP

{-@ data RefinedFilter record typ <p :: record -> User -> Bool> = RefinedFilter
    { refinedFilterField  :: EntityField record typ
    , refinedFilterValue  :: typ
    , refinedFilterFilter :: RefinedPersistFilter
    }
  @-}
{-@ data variance RefinedFilter covariant covariant contravariant @-}
data RefinedFilter record typ = RefinedFilter
    { refinedFilterField  :: EntityField record typ
    , refinedFilterValue  :: typ
    , refinedFilterFilter :: RefinedPersistFilter
    }


{-@ data RefinedUpdate record typ = RefinedUpdate
    { refinedUpdateField :: EntityField record typ
    , refinedUpdateValue :: typ } @-}
data RefinedUpdate record typ = RefinedUpdate
    { refinedUpdateField :: EntityField record typ
    , refinedUpdateValue :: typ
    }

toPersistentFilter :: PersistField typ =>
                      RefinedFilter record typ -> Filter record
toPersistentFilter filter =
    case refinedFilterFilter filter of
         EQUAL -> (refinedFilterField filter) ==. (refinedFilterValue filter)
         NE -> (refinedFilterField filter) !=. (refinedFilterValue filter)
         LE -> (refinedFilterField filter) <=. (refinedFilterValue filter)
         LTP -> (refinedFilterField filter) <. (refinedFilterValue filter)
         GE -> (refinedFilterField filter) >=. (refinedFilterValue filter)
         GTP -> (refinedFilterField filter) >. (refinedFilterValue filter)

toPersistentUpdate :: PersistField typ =>
                      RefinedUpdate record typ -> Update record
toPersistentUpdate (RefinedUpdate a b) = a =. b

refinedUpdate id us = update id (map toPersistentUpdate us)

{-@ filter :: f:(a -> Bool) -> [a] -> [{v:a | f v}] @-}
filter :: (a -> Bool) -> [a] -> [a]
filter f (x:xs)
  | f x         = x : filter f xs
  | otherwise   =     filter f xs
filter _ []     = []

{-@ reflect evalQUserEmail @-}
evalQUserEmail :: RefinedPersistFilter -> [Char] -> [Char] -> Bool
evalQUserEmail EQUAL filter given = given == filter
evalQUserEmail LE filter given = given <= filter
evalQUserEmail GE filter given = given >= filter
evalQUserEmail LTP filter given = given < filter
evalQUserEmail GTP filter given = given > filter
evalQUserEmail NE filter given = given /= filter

{-@ reflect evalQUserPassword @-}
evalQUserPassword :: RefinedPersistFilter -> Maybe [Char] -> Maybe [Char] -> Bool
evalQUserPassword EQUAL filter given = given == filter
evalQUserPassword NE filter given = given /= filter

{-@ reflect evalQUserVerkey @-}
evalQUserVerkey :: RefinedPersistFilter -> Maybe [Char] -> Maybe [Char] -> Bool
evalQUserVerkey EQUAL filter given = given == filter
evalQUserVerkey NE filter given = given /= filter

{-@ reflect evalQUserVerified @-}
evalQUserVerified :: RefinedPersistFilter -> Int -> Int -> Bool
evalQUserVerified EQUAL filter given = given == filter
evalQUserVerified NE filter given = given /= filter

{-@ reflect evalQUser @-}
evalQUser :: RefinedFilter User typ -> User -> Bool
evalQUser filter x = case refinedFilterField filter of
    UserEmail -> evalQUserEmail (refinedFilterFilter filter) (refinedFilterValue filter) (userEmail x)
    UserPassword -> evalQUserPassword (refinedFilterFilter filter) (refinedFilterValue filter) (userPassword x)
    UserVerkey -> evalQUserVerkey (refinedFilterFilter filter) (refinedFilterValue filter) (userVerkey x)
    UserVerified -> evalQUserVerified (refinedFilterFilter filter) (refinedFilterValue filter) (userVerified x)
    UserId -> False

{-@ reflect evalQsUser @-}
evalQsUser :: [RefinedFilter User typ] -> User -> Bool
evalQsUser (f:fs) x = evalQUser f x && (evalQsUser fs x)
evalQsUser [] _ = True

{-@ reflect evalQEmailEmail @-}
evalQEmailEmail :: RefinedPersistFilter -> [Char] -> [Char] -> Bool
evalQEmailEmail EQUAL filter given = given == filter
evalQEmailEmail LE filter given = given <= filter
evalQEmailEmail GE filter given = given >= filter
evalQEmailEmail LTP filter given = given < filter
evalQEmailEmail GTP filter given = given > filter
evalQEmailEmail NE filter given = given /= filter

{-@ reflect evalQEmailUserId @-}
evalQEmailUserId :: RefinedPersistFilter -> Maybe UserId -> Maybe UserId -> Bool
evalQEmailUserId EQUAL filter given = given == filter
evalQEmailUserId NE filter given = given /= filter

{-@ reflect evalQEmailVerkey @-}
evalQEmailVerkey :: RefinedPersistFilter -> Maybe [Char] -> Maybe [Char] -> Bool
evalQEmailVerkey EQUAL filter given = given == filter
evalQEmailVerkey NE filter given = given /= filter

{-@ reflect evalQEmail @-}
evalQEmail :: RefinedFilter Email typ -> Email -> Bool
evalQEmail filter x = case refinedFilterField filter of
    EmailEmail -> evalQEmailEmail (refinedFilterFilter filter) (refinedFilterValue filter) (emailEmail x)
    EmailUserId -> evalQEmailUserId (refinedFilterFilter filter) (refinedFilterValue filter) (emailUserId x)
    EmailVerkey -> evalQEmailVerkey (refinedFilterFilter filter) (refinedFilterValue filter) (emailVerkey x)
    EmailId -> False

{-@ reflect evalQsEmail @-}
evalQsEmail :: [RefinedFilter Email typ] -> Email -> Bool
evalQsEmail (f:fs) x = evalQEmail f x && (evalQsEmail fs x)
evalQsEmail [] _ = True

{-@ reflect evalQPersonEmail @-}
evalQPersonEmail :: RefinedPersistFilter -> [Char] -> [Char] -> Bool
evalQPersonEmail EQUAL filter given = given == filter
evalQPersonEmail LE filter given = given <= filter
evalQPersonEmail GE filter given = given >= filter
evalQPersonEmail LTP filter given = given < filter
evalQPersonEmail GTP filter given = given > filter
evalQPersonEmail NE filter given = given /= filter

{-@ reflect evalQPersonName @-}
evalQPersonName :: RefinedPersistFilter -> [Char] -> [Char] -> Bool
evalQPersonName EQUAL filter given = given == filter
evalQPersonName LE filter given = given <= filter
evalQPersonName GE filter given = given >= filter
evalQPersonName LTP filter given = given < filter
evalQPersonName GTP filter given = given > filter
evalQPersonName NE filter given = given /= filter

{-@ reflect evalQPersonStreet @-}
evalQPersonStreet :: RefinedPersistFilter -> [Char] -> [Char] -> Bool
evalQPersonStreet EQUAL filter given = given == filter
evalQPersonStreet LE filter given = given <= filter
evalQPersonStreet GE filter given = given >= filter
evalQPersonStreet LTP filter given = given < filter
evalQPersonStreet GTP filter given = given > filter
evalQPersonStreet NE filter given = given /= filter

{-@ reflect evalQPersonNumber @-}
evalQPersonNumber :: RefinedPersistFilter -> Int -> Int -> Bool
evalQPersonNumber EQUAL filter given = given == filter
evalQPersonNumber LE filter given = given <= filter
evalQPersonNumber GE filter given = given >= filter
evalQPersonNumber LTP filter given = given < filter
evalQPersonNumber GTP filter given = given > filter
evalQPersonNumber NE filter given = given /= filter

{-@ reflect evalQPerson @-}
evalQPerson :: RefinedFilter Person typ -> Person -> Bool
evalQPerson filter x = case refinedFilterField filter of
    PersonEmail -> evalQPersonEmail (refinedFilterFilter filter) (refinedFilterValue filter) (personEmail x)
    PersonName -> evalQPersonName (refinedFilterFilter filter) (refinedFilterValue filter) (personName x)
    PersonStreet -> evalQPersonStreet (refinedFilterFilter filter) (refinedFilterValue filter) (personStreet x)
    PersonNumber -> evalQPersonNumber (refinedFilterFilter filter) (refinedFilterValue filter) (personNumber x)
    PersonId -> False

{-@ reflect evalQsPerson @-}
evalQsPerson :: [RefinedFilter Person typ] -> Person -> Bool
evalQsPerson (f:fs) x = evalQPerson f x && (evalQsPerson fs x)
evalQsPerson [] _ = True

{-@ reflect evalQFriendsEmail @-}
evalQFriendsEmail :: RefinedPersistFilter -> [Char] -> [Char] -> Bool
evalQFriendsEmail EQUAL filter given = given == filter
evalQFriendsEmail LE filter given = given <= filter
evalQFriendsEmail GE filter given = given >= filter
evalQFriendsEmail LTP filter given = given < filter
evalQFriendsEmail GTP filter given = given > filter
evalQFriendsEmail NE filter given = given /= filter

{-@ reflect evalQFriendsRequests @-}
evalQFriendsRequests :: RefinedPersistFilter -> [[Char]] -> [[Char]] -> Bool
evalQFriendsRequests EQUAL filter given = given == filter
evalQFriendsRequests LE filter given = given <= filter
evalQFriendsRequests GE filter given = given >= filter
evalQFriendsRequests LTP filter given = given < filter
evalQFriendsRequests GTP filter given = given > filter
evalQFriendsRequests NE filter given = given /= filter

{-@ reflect evalQFriendsFriends @-}
evalQFriendsFriends :: RefinedPersistFilter -> [[Char]] -> [[Char]] -> Bool
evalQFriendsFriends EQUAL filter given = given == filter
evalQFriendsFriends LE filter given = given <= filter
evalQFriendsFriends GE filter given = given >= filter
evalQFriendsFriends LTP filter given = given < filter
evalQFriendsFriends GTP filter given = given > filter
evalQFriendsFriends NE filter given = given /= filter

{-@ reflect evalQFriendsOutgoingRequests @-}
evalQFriendsOutgoingRequests :: RefinedPersistFilter -> [[Char]] -> [[Char]] -> Bool
evalQFriendsOutgoingRequests EQUAL filter given = given == filter
evalQFriendsOutgoingRequests LE filter given = given <= filter
evalQFriendsOutgoingRequests GE filter given = given >= filter
evalQFriendsOutgoingRequests LTP filter given = given < filter
evalQFriendsOutgoingRequests GTP filter given = given > filter
evalQFriendsOutgoingRequests NE filter given = given /= filter

{-@ reflect evalQFriends @-}
evalQFriends :: RefinedFilter Friends typ -> Friends -> Bool
evalQFriends filter x = case refinedFilterField filter of
    FriendsEmail -> evalQFriendsEmail (refinedFilterFilter filter) (refinedFilterValue filter) (friendsEmail x)
    FriendsRequests -> evalQFriendsRequests (refinedFilterFilter filter) (refinedFilterValue filter) (friendsRequests x)
    FriendsFriends -> evalQFriendsFriends (refinedFilterFilter filter) (refinedFilterValue filter) (friendsFriends x)
    FriendsOutgoingRequests -> evalQFriendsOutgoingRequests (refinedFilterFilter filter) (refinedFilterValue filter) (friendsOutgoingRequests x)
    FriendsId -> False

{-@ reflect evalQsFriends @-}
evalQsFriends :: [RefinedFilter Friends typ] -> Friends -> Bool
evalQsFriends (f:fs) x = evalQFriends f x && (evalQsFriends fs x)
evalQsFriends [] _ = True

-- End evalQs

{-@ assume selectUser :: forall <p :: User -> User -> Bool>. f:[RefinedFilter<p> User typ]
                -> [SelectOpt User]
                -> Control.Monad.Trans.Reader.ReaderT backend m (TaggedUser<p> [Entity {v:User | evalQsUser f v}]) @-}
selectUser :: (PersistEntityBackend User ~ BaseBackend backend,
      PersistEntity User, Control.Monad.IO.Class.MonadIO m,
      PersistQueryRead backend, PersistField typ) =>
      [RefinedFilter User typ]
      -> [SelectOpt User]
      -> Control.Monad.Trans.Reader.ReaderT backend m (TaggedUser [Entity User])
selectUser fs ts = selectList (map toPersistentFilter fs) ts >>= return . TaggedUser

{-@ assume selectEmail :: forall <p :: Email -> User -> Bool>. f:[RefinedFilter<p> Email typ]
                -> [SelectOpt Email]
                -> Control.Monad.Trans.Reader.ReaderT backend m (TaggedEmail<p> [Entity {v:Email | evalQsEmail f v}]) @-}
selectEmail :: (PersistEntityBackend Email ~ BaseBackend backend,
      PersistEntity Email, Control.Monad.IO.Class.MonadIO m,
      PersistQueryRead backend, PersistField typ) =>
      [RefinedFilter Email typ]
      -> [SelectOpt Email]
      -> Control.Monad.Trans.Reader.ReaderT backend m (TaggedEmail [Entity Email])
selectEmail fs ts = selectList (map toPersistentFilter fs) ts >>= return . TaggedEmail

{-@ assume selectPerson :: forall <p :: Person -> User -> Bool>. f:[RefinedFilter<p> Person typ]
                -> [SelectOpt Person]
                -> Control.Monad.Trans.Reader.ReaderT backend m (TaggedPerson<p> [Entity {v:Person | evalQsPerson f v}]) @-}
selectPerson :: (PersistEntityBackend Person ~ BaseBackend backend,
      PersistEntity Person, Control.Monad.IO.Class.MonadIO m,
      PersistQueryRead backend, PersistField typ) =>
      [RefinedFilter Person typ]
      -> [SelectOpt Person]
      -> Control.Monad.Trans.Reader.ReaderT backend m (TaggedPerson [Entity Person])
selectPerson fs ts = selectList (map toPersistentFilter fs) ts >>= return . TaggedPerson

{-@ assume selectFriends :: forall <p :: Friends -> User -> Bool>. f:[RefinedFilter<p> Friends typ]
                -> [SelectOpt Friends]
                -> Control.Monad.Trans.Reader.ReaderT backend m (TaggedFriends<p> [Entity {v:Friends | evalQsFriends f v}]) @-}
selectFriends :: (PersistEntityBackend Friends ~ BaseBackend backend,
      PersistEntity Friends, Control.Monad.IO.Class.MonadIO m,
      PersistQueryRead backend, PersistField typ) =>
      [RefinedFilter Friends typ]
      -> [SelectOpt Friends]
      -> Control.Monad.Trans.Reader.ReaderT backend m (TaggedFriends [Entity Friends])
selectFriends fs ts = selectList (map toPersistentFilter fs) ts >>= return . TaggedFriends

{-@ filterUserEmail :: RefinedPersistFilter -> String -> RefinedFilter<{\u v -> true}> User (String) @-}
{-@ reflect filterUserEmail @-}
filterUserEmail :: RefinedPersistFilter -> String -> RefinedFilter User (String)
filterUserEmail f v = RefinedFilter UserEmail v f

{-@ filterUserPassword :: RefinedPersistFilter -> Maybe String -> RefinedFilter<{\u v -> true}> User (Maybe String) @-}
{-@ reflect filterUserPassword @-}
filterUserPassword :: RefinedPersistFilter -> Maybe String -> RefinedFilter User (Maybe String)
filterUserPassword f v = RefinedFilter UserPassword v f

{-@ filterUserVerkey :: RefinedPersistFilter -> Maybe String -> RefinedFilter<{\u v -> true}> User (Maybe String) @-}
{-@ reflect filterUserVerkey @-}
filterUserVerkey :: RefinedPersistFilter -> Maybe String -> RefinedFilter User (Maybe String)
filterUserVerkey f v = RefinedFilter UserVerkey v f

{-@ filterUserVerified :: RefinedPersistFilter -> Int -> RefinedFilter<{\u v -> true}> User (Int) @-}
{-@ reflect filterUserVerified @-}
filterUserVerified :: RefinedPersistFilter -> Int -> RefinedFilter User (Int)
filterUserVerified f v = RefinedFilter UserVerified v f

{-@ filterEmailEmail :: RefinedPersistFilter -> String -> RefinedFilter<{\u v -> true}> Email (String) @-}
{-@ reflect filterEmailEmail @-}
filterEmailEmail :: RefinedPersistFilter -> String -> RefinedFilter Email (String)
filterEmailEmail f v = RefinedFilter EmailEmail v f

{-@ filterEmailUserId :: RefinedPersistFilter -> Maybe UserId -> RefinedFilter<{\u v -> true}> Email (Maybe UserId) @-}
{-@ reflect filterEmailUserId @-}
filterEmailUserId :: RefinedPersistFilter -> Maybe UserId -> RefinedFilter Email (Maybe UserId)
filterEmailUserId f v = RefinedFilter EmailUserId v f

{-@ filterEmailVerkey :: RefinedPersistFilter -> Maybe String -> RefinedFilter<{\u v -> true}> Email (Maybe String) @-}
{-@ reflect filterEmailVerkey @-}
filterEmailVerkey :: RefinedPersistFilter -> Maybe String -> RefinedFilter Email (Maybe String)
filterEmailVerkey f v = RefinedFilter EmailVerkey v f

{-@ filterPersonEmail :: RefinedPersistFilter -> String -> RefinedFilter<{\u v -> personEmail u == userEmail v}> Person (String) @-}
{-@ reflect filterPersonEmail @-}
filterPersonEmail :: RefinedPersistFilter -> String -> RefinedFilter Person (String)
filterPersonEmail f v = RefinedFilter PersonEmail v f

{-@ filterPersonName :: RefinedPersistFilter -> {n:String | len n > 0} -> RefinedFilter<{\u v -> true}> Person (String) @-}
{-@ reflect filterPersonName @-}
filterPersonName :: RefinedPersistFilter -> String -> RefinedFilter Person (String)
filterPersonName f v = RefinedFilter PersonName v f

{-@ filterPersonStreet :: RefinedPersistFilter -> {n:String | len n > 0} -> RefinedFilter<{\u v -> true}> Person (String) @-}
{-@ reflect filterPersonStreet @-}
filterPersonStreet :: RefinedPersistFilter -> String -> RefinedFilter Person (String)
filterPersonStreet f v = RefinedFilter PersonStreet v f

{-@ filterPersonNumber :: RefinedPersistFilter -> {v:Int | v > 0} -> RefinedFilter<{\u v -> true}> Person (Int) @-}
{-@ reflect filterPersonNumber @-}
filterPersonNumber :: RefinedPersistFilter -> Int -> RefinedFilter Person (Int)
filterPersonNumber f v = RefinedFilter PersonNumber v f

{-@ filterFriendsEmail :: RefinedPersistFilter -> String -> RefinedFilter<{\u v -> true}> Friends (String) @-}
{-@ reflect filterFriendsEmail @-}
filterFriendsEmail :: RefinedPersistFilter -> String -> RefinedFilter Friends (String)
filterFriendsEmail f v = RefinedFilter FriendsEmail v f

{-@ filterFriendsRequests :: RefinedPersistFilter -> [String] -> RefinedFilter<{\u v -> true}> Friends ([String]) @-}
{-@ reflect filterFriendsRequests @-}
filterFriendsRequests :: RefinedPersistFilter -> [String] -> RefinedFilter Friends ([String])
filterFriendsRequests f v = RefinedFilter FriendsRequests v f

{-@ filterFriendsFriends :: RefinedPersistFilter -> [String] -> RefinedFilter<{\u v -> true}> Friends ([String]) @-}
{-@ reflect filterFriendsFriends @-}
filterFriendsFriends :: RefinedPersistFilter -> [String] -> RefinedFilter Friends ([String])
filterFriendsFriends f v = RefinedFilter FriendsFriends v f

{-@ filterFriendsOutgoingRequests :: RefinedPersistFilter -> [String] -> RefinedFilter<{\u v -> true}> Friends ([String]) @-}
{-@ reflect filterFriendsOutgoingRequests @-}
filterFriendsOutgoingRequests :: RefinedPersistFilter -> [String] -> RefinedFilter Friends ([String])
filterFriendsOutgoingRequests f v = RefinedFilter FriendsOutgoingRequests v f


{-@ safeUnwrapUser ::
             row:TaggedUser<{\u v -> false}> User
          -> viewer:(TaggedUser<{\u v -> true}> User)
          -> msg:TaggedUser<{\u v -> v == userContent viewer && u == userContent row}> a
          -> a @-}
safeUnwrapUser :: TaggedUser User -> TaggedUser User -> TaggedUser a -> a
safeUnwrapUser _ _ (TaggedUser x) = x

{-@ safeUnwrapEmail ::
             row:TaggedEmail <{\u v -> false}> Email
          -> viewer:(TaggedEmail <{\u v -> true}> User)
          -> msg:TaggedEmail <{\u v -> v == emailContent viewer && u == emailContent row}> a
          -> a @-}
safeUnwrapEmail :: TaggedEmail Email -> TaggedEmail User -> TaggedEmail a -> a
safeUnwrapEmail _ _ (TaggedEmail x) = x

{-@ safeUnwrapPerson ::
             row:TaggedPerson <{\u v -> false}> Person
          -> viewer:(TaggedPerson <{\u v -> true}> User)
          -> msg:TaggedPerson <{\u v -> v == personContent viewer && u == personContent row}> a
          -> a @-}
safeUnwrapPerson :: TaggedPerson Person -> TaggedPerson User -> TaggedPerson a -> a
safeUnwrapPerson _ _ (TaggedPerson x) = x

{-@ safeUnwrapFriends ::
             row:TaggedFriends <{\u v -> false}> Friends
          -> viewer:(TaggedFriends <{\u v -> true}> User)
          -> msg:TaggedFriends<{\u v -> v == friendsContent viewer && u == friendsContent row}> a
          -> a @-}
safeUnwrapFriends :: TaggedFriends Friends -> TaggedFriends User -> TaggedFriends a -> a
safeUnwrapFriends _ _ (TaggedFriends x) = x

{-@ measure isVerified :: User -> Bool @-}
{-@ assume isUserVerified :: u:User -> {b:Bool | b <=> isVerified u} @-}
isUserVerified :: User -> Bool
isUserVerified (User _ _ _ 1) = True
isUserVerified (User _ _ _ 0) = False

{-@ assume isPersonSameUser :: forall <p :: Person -> User -> Bool>.
   u:TaggedPerson<p> Person ->
   v:TaggedPerson<p> User ->
   TaggedPerson<p> {b:Bool | b <=> personEmail (personContent u) == (userEmail (personContent v))}
@-}
isPersonSameUser :: TaggedPerson Person -> TaggedPerson User -> TaggedPerson Bool
isPersonSameUser person user = do
  p <- person
  u <- user
  return $ userEmail u == (personEmail p)

{-@ measure personFriendsWithUser :: Person -> User -> Bool @-}
{-@ assume isPersonFriendsWithUser :: forall <p :: Person -> User -> Bool>.
   u:TaggedPerson<p> Person ->
   v:TaggedPerson<p> User ->
   TaggedPerson<p> {b:Bool | b <=> personFriendsWithUser (personContent u) (personContent v)}
@-}
isPersonFriendsWithUser :: TaggedPerson Person -> TaggedPerson User -> TaggedPerson Bool
isPersonFriendsWithUser = undefined


-- Getters

{-@ getUserEmail :: forall <p :: User -> User -> Bool, q :: User -> User -> Bool>.
    {w :: User |- User<q w> <: User<{\u v -> true}>}
    {w :: User |- User<q w> <: User<p w>}
    TaggedUser<p> User -> TaggedUser<q> (String)
@-}
getUserEmail :: TaggedUser User -> TaggedUser (String)
getUserEmail (TaggedUser x) = TaggedUser $ userEmail x

{-@ getUserPassword :: forall <p :: User -> User -> Bool, q :: User -> User -> Bool>.
    {w :: User |- User<q w> <: User<{\u v -> true}>}
    {w :: User |- User<q w> <: User<p w>}
    TaggedUser<p> User -> TaggedUser<q> (Maybe String)
@-}
getUserPassword :: TaggedUser User -> TaggedUser (Maybe String)
getUserPassword (TaggedUser x) = TaggedUser $ userPassword x

{-@ getUserVerkey :: forall <p :: User -> User -> Bool, q :: User -> User -> Bool>.
    {w :: User |- User<q w> <: User<{\u v -> true}>}
    {w :: User |- User<q w> <: User<p w>}
    TaggedUser<p> User -> TaggedUser<q> (Maybe String)
@-}
getUserVerkey :: TaggedUser User -> TaggedUser (Maybe String)
getUserVerkey (TaggedUser x) = TaggedUser $ userVerkey x

{-@ getUserVerified :: forall <p :: User -> User -> Bool, q :: User -> User -> Bool>.
    {w :: User |- User<q w> <: User<{\u v -> true}>}
    {w :: User |- User<q w> <: User<p w>}
    TaggedUser<p> User -> TaggedUser<q> (Int)
@-}
getUserVerified :: TaggedUser User -> TaggedUser (Int)
getUserVerified (TaggedUser x) = TaggedUser $ userVerified x

{-@ getEmailEmail :: forall <p :: Email -> User -> Bool, q :: Email -> User -> Bool>.
    {w :: Email |- User<q w> <: User<{\u v -> true}>}
    {w :: Email |- User<q w> <: User<p w>}
    TaggedEmail<p> Email -> TaggedEmail<q> (String)
@-}
getEmailEmail :: TaggedEmail Email -> TaggedEmail (String)
getEmailEmail (TaggedEmail x) = TaggedEmail $ emailEmail x

{-@ getEmailUserId :: forall <p :: Email -> User -> Bool, q :: Email -> User -> Bool>.
    {w :: Email |- User<q w> <: User<{\u v -> true}>}
    {w :: Email |- User<q w> <: User<p w>}
    TaggedEmail<p> Email -> TaggedEmail<q> (Maybe UserId)
@-}
getEmailUserId :: TaggedEmail Email -> TaggedEmail (Maybe UserId)
getEmailUserId (TaggedEmail x) = TaggedEmail $ emailUserId x

{-@ getEmailVerkey :: forall <p :: Email -> User -> Bool, q :: Email -> User -> Bool>.
    {w :: Email |- User<q w> <: User<{\u v -> true}>}
    {w :: Email |- User<q w> <: User<p w>}
    TaggedEmail<p> Email -> TaggedEmail<q> (Maybe String)
@-}
getEmailVerkey :: TaggedEmail Email -> TaggedEmail (Maybe String)
getEmailVerkey (TaggedEmail x) = TaggedEmail $ emailVerkey x

{-@ getPersonEmail :: forall <p :: Person -> User -> Bool, q :: Person -> User -> Bool>.
    {w :: Person |- User<q w> <: User<{\u v -> true}>}
    {w :: Person |- User<q w> <: User<p w>}
    TaggedPerson<p> Person -> TaggedPerson<q> (String)
@-}
getPersonEmail :: TaggedPerson Person -> TaggedPerson (String)
getPersonEmail (TaggedPerson x) = TaggedPerson $ personEmail x

{-@ getPersonName :: forall <p :: Person -> User -> Bool, q :: Person -> User -> Bool>.
    {w :: Person |- User<q w> <: User<{\u v -> true}>}
    {w :: Person |- User<q w> <: User<p w>}
    TaggedPerson<p> Person -> TaggedPerson<q> (String)
@-}
getPersonName :: TaggedPerson Person -> TaggedPerson (String)
getPersonName (TaggedPerson x) = TaggedPerson $ personName x

{-@ getPersonStreet :: forall <p :: Person -> User -> Bool, q :: Person -> User -> Bool>.
    {w :: Person |- User<q w> <: User<{\u v -> true}>}
    {w :: Person |- User<q w> <: User<p w>}
    TaggedPerson<p> Person -> TaggedPerson<q> (String)
@-}
getPersonStreet :: TaggedPerson Person -> TaggedPerson (String)
getPersonStreet (TaggedPerson x) = TaggedPerson $ personStreet x

{-@ getPersonNumber :: forall <p :: Person -> User -> Bool, q :: Person -> User -> Bool>.
    {w :: Person |- User<q w> <: User<{\u v -> true}>}
    {w :: Person |- User<q w> <: User<p w>}
    TaggedPerson<p> Person -> TaggedPerson<q> (Int)
@-}
getPersonNumber :: TaggedPerson Person -> TaggedPerson (Int)
getPersonNumber (TaggedPerson x) = TaggedPerson $ personNumber x

{-@ getFriendsEmail :: forall <p :: Friends -> User -> Bool, q :: Friends -> User -> Bool>.
    {w :: Friends |- User<q w> <: User<{\u v -> true}>}
    {w :: Friends |- User<q w> <: User<p w>}
    TaggedFriends<p> Friends -> TaggedFriends<q> (String)
@-}
getFriendsEmail :: TaggedFriends Friends -> TaggedFriends (String)
getFriendsEmail (TaggedFriends x) = TaggedFriends $ friendsEmail x

{-@ getFriendsRequests :: forall <p :: Friends -> User -> Bool, q :: Friends -> User -> Bool>.
    {w :: Friends |- User<q w> <: User<{\u v -> true}>}
    {w :: Friends |- User<q w> <: User<p w>}
    TaggedFriends<p> Friends -> TaggedFriends<q> ([String])
@-}
getFriendsRequests :: TaggedFriends Friends -> TaggedFriends ([String])
getFriendsRequests (TaggedFriends x) = TaggedFriends $ friendsRequests x

{-@ getFriendsFriends :: forall <p :: Friends -> User -> Bool, q :: Friends -> User -> Bool>.
    {w :: Friends |- User<q w> <: User<{\u v -> true}>}
    {w :: Friends |- User<q w> <: User<p w>}
    TaggedFriends<p> Friends -> TaggedFriends<q> ([String])
@-}
getFriendsFriends :: TaggedFriends Friends -> TaggedFriends ([String])
getFriendsFriends (TaggedFriends x) = TaggedFriends $ friendsFriends x

{-@ getFriendsOutgoingRequests :: forall <p :: Friends -> User -> Bool, q :: Friends -> User -> Bool>.
    {w :: Friends |- User<q w> <: User<{\u v -> true}>}
    {w :: Friends |- User<q w> <: User<p w>}
    TaggedFriends<p> Friends -> TaggedFriends<q> ([String])
@-}
getFriendsOutgoingRequests :: TaggedFriends Friends -> TaggedFriends ([String])
getFriendsOutgoingRequests (TaggedFriends x) = TaggedFriends $ friendsOutgoingRequests x

-- Tests
-- TODO: move downgrades into the Tagged files!

{-@
downgradeBoolUser :: forall < p :: User -> User -> Bool
                , q :: User -> User -> Bool
                , r :: Bool -> Bool
                >.
       {w:: User, x:: {v:Bool<r> | v <=> true} |- User<p w> <: User<q w>}
      x: TaggedUser <q> (Bool<r>)
    -> TaggedUser <p> (Bool<r>)
@-}
downgradeBoolUser :: TaggedUser Bool -> TaggedUser Bool
downgradeBoolUser (TaggedUser x) = TaggedUser x

{-@
downgradeBoolPerson :: forall < p :: Person -> User -> Bool
                , q :: Person -> User -> Bool
                , r :: Bool -> Bool
                >.
       {w:: Person, x:: {v:Bool<r> | v <=> true} |- User<p w> <: User<q w>}
      x: TaggedPerson <q> (Bool<r>)
    -> TaggedPerson <p> (Bool<r>)
@-}
downgradeBoolPerson :: TaggedPerson Bool -> TaggedPerson Bool
downgradeBoolPerson (TaggedPerson x) = TaggedPerson x

{-@
downgradeBoolEmail :: forall < p :: Email -> User -> Bool
                , q :: Email -> User -> Bool
                , r :: Bool -> Bool
                >.
       {w:: Email, x:: {v:Bool<r> | v <=> true} |- User<p w> <: User<q w>}
      x: TaggedEmail <q> (Bool<r>)
    -> TaggedEmail <p> (Bool<r>)
@-}
downgradeBoolEmail :: TaggedEmail Bool -> TaggedEmail Bool
downgradeBoolEmail (TaggedEmail x) = TaggedEmail x

{-@
downgradeBoolFriends :: forall < p :: Friends -> User -> Bool
                , q :: Friends -> User -> Bool
                , r :: Bool -> Bool
                >.
       {w:: Friends, x:: {v:Bool<r> | v <=> true} |- User<p w> <: User<q w>}
      x: TaggedFriends<q> (Bool<r>)
    -> TaggedFriends<p> (Bool<r>)
@-}
downgradeBoolFriends :: TaggedFriends Bool -> TaggedFriends Bool
downgradeBoolFriends (TaggedFriends x) = TaggedFriends x

{-@ defaultFriends :: TaggedUser <{\u v -> true}> [User] @-}
defaultFriends :: TaggedUser [User]
defaultFriends = return []

{-@ message :: viewer:TaggedUser <{\u v -> true}> User -> 
               user:TaggedUser <{\u v -> isVerified v}> User ->
               TaggedUser <{\u v -> v == userContent viewer && u == userContent user}> [User] @-}
message :: TaggedUser User -> TaggedUser User -> TaggedUser [User]
message viewer user =
  let verified = do v <- viewer
                    return $ isUserVerified v in
  let b = downgradeBoolUser verified in
  do
    c <- b
    if c 
      then (return [])
      else defaultFriends

{-@ selectTaggedData :: () -> TaggedUser<{\u v -> isVerified v}> User @-}
selectTaggedData :: () -> TaggedUser User
selectTaggedData () = undefined

sink :: TaggedUser User -> TaggedUser User -> [User]
sink viewer viewer2 =
  let user = selectTaggedData () in
  let out = message viewer user in
  safeUnwrapUser user viewer out

{-@ messagePersonEmail :: viewer:TaggedPerson <{\u v -> true}> User -> 
               person:TaggedPerson <{\u v -> personEmail u == (userEmail v)}> Person ->
               TaggedPerson<{\u v -> v == personContent viewer && u == personContent person}> String @-}
messagePersonEmail :: TaggedPerson User -> TaggedPerson Person -> TaggedPerson String 
messagePersonEmail viewer person =
  let emailsEqual = isPersonSameUser person viewer in
  let b = downgradeBoolPerson emailsEqual in
  do
    c <- b
    if c 
      then (person >>= (return . personEmail))
      else return ""

{-@ messagePersonStreet :: viewer:TaggedPerson <{\u v -> true}> User -> 
               person:TaggedPerson <{\u v -> personFriendsWithUser u v}> Person ->
               TaggedPerson<{\u v -> v == personContent viewer && u == personContent person}> String @-}
messagePersonStreet :: TaggedPerson User -> TaggedPerson Person -> TaggedPerson String 
messagePersonStreet viewer person =
  let friends = isPersonFriendsWithUser person viewer in
  let b = downgradeBoolPerson friends in
  do
    c <- b
    if c 
      then (person >>= (return . personStreet))
      else return ""

{-@ selectTaggedDataPerson :: () -> TaggedPerson <{\u v -> personEmail u == (userEmail v)}> Person @-}
selectTaggedDataPerson :: () -> TaggedPerson Person 
selectTaggedDataPerson () = undefined

{-@ selectTaggedDataPersonStreet :: () -> TaggedPerson <{\u v -> personFriendsWithUser u v}> Person @-}
selectTaggedDataPersonStreet :: () -> TaggedPerson Person 
selectTaggedDataPersonStreet () = undefined

sinkPersonEmail :: TaggedPerson User -> TaggedPerson User -> String
sinkPersonEmail viewer viewer2 =
  let user = selectTaggedDataPerson () in
  let out = messagePersonEmail viewer user in
  safeUnwrapPerson user viewer out

sinkPersonStreet :: TaggedPerson User -> TaggedPerson User -> String
sinkPersonStreet viewer viewer2 =
  let user = selectTaggedDataPersonStreet () in
  let out = messagePersonStreet viewer user in
  safeUnwrapPerson user viewer out

-- Collapse functions
{-@ assume collapseTaggedUser :: forall a m <p :: User -> User -> Bool, q :: User -> User -> Bool, r :: User -> User -> Bool>.
    {w :: User |- User<r w> <: User<p w>}
    {w :: User |- User<r w> <: User<q w>}
    TaggedUser<p> (m (TaggedUser<q> a)) -> m (TaggedUser<r> a)
@-}
collapseTaggedUser :: Monad m => TaggedUser (m (TaggedUser a)) -> m (TaggedUser a)
collapseTaggedUser (TaggedUser x) = x

{-@ assume collapseTaggedEmail :: forall a m <p :: Email -> User -> Bool, q :: Email -> User -> Bool, r :: Email -> User -> Bool>.
    {w :: Email |- User<r w> <: User<p w>}
    {w :: Email |- User<r w> <: User<q w>}
    TaggedEmail<p> (m (TaggedEmail<q> a)) -> m (TaggedEmail <r> a)
@-}
collapseTaggedEmail :: Monad m => TaggedEmail (m (TaggedEmail a)) -> m (TaggedEmail a)
collapseTaggedEmail (TaggedEmail x) = x

{-@ assume collapseTaggedPerson :: forall a m <p :: Person -> User -> Bool, q :: Person -> User -> Bool, r :: Person -> User -> Bool>.
    {w :: Person |- User<r w> <: User<p w>}
    {w :: Person |- User<r w> <: User<q w>}
    TaggedPerson <p> (m (TaggedPerson <q> a)) -> m (TaggedPerson <r> a)
@-}
collapseTaggedPerson :: Monad m => TaggedPerson (m (TaggedPerson a)) -> m (TaggedPerson a)
collapseTaggedPerson (TaggedPerson x) = x

{-@ assume collapseTaggedFriends :: forall a m <p :: Friends -> User -> Bool, q :: Friends -> User -> Bool, r :: Friends -> User -> Bool>.
    {w :: Friends |- User<r w> <: User<p w>}
    {w :: Friends |- User<r w> <: User<q w>}
    TaggedFriends <p> (m (TaggedFriends <q> a)) -> m (TaggedFriends <r> a)
@-}
collapseTaggedFriends :: Monad m => TaggedFriends (m (TaggedFriends a)) -> m (TaggedFriends a)
collapseTaggedFriends (TaggedFriends x) = x

-- Insert functions
{-@
  insertTaggedUser ::
    TaggedUser<{\u v -> true}> User -> ReaderT backend m (Key User)
@-}
insertTaggedUser :: (PersistEntityBackend User ~ BaseBackend backend,
      PersistEntity User, Control.Monad.IO.Class.MonadIO m,
      PersistStoreWrite backend) =>
      TaggedUser User -> ReaderT backend m (Key User)
insertTaggedUser (TaggedUser u) = insert u

{-@
  insertTaggedEmail ::
    TaggedEmail<{\u v -> true}> Email -> ReaderT backend m (Key Email)
@-}
insertTaggedEmail :: (PersistEntityBackend Email ~ BaseBackend backend,
      PersistEntity Email, Control.Monad.IO.Class.MonadIO m,
      PersistStoreWrite backend) =>
      TaggedEmail Email -> ReaderT backend m (Key Email)
insertTaggedEmail (TaggedEmail u) = insert u

{-@
  insertTaggedPerson ::
    TaggedPerson<{\u v -> true}> Person -> ReaderT backend m (Key Person)
@-}
insertTaggedPerson :: (PersistEntityBackend Person ~ BaseBackend backend,
      PersistEntity Person, Control.Monad.IO.Class.MonadIO m,
      PersistStoreWrite backend) =>
      TaggedPerson Person -> ReaderT backend m (Key Person)
insertTaggedPerson (TaggedPerson u) = insert u

{-@
  insertTaggedFriends ::
    TaggedFriends<{\u v -> true}> Friends -> ReaderT backend m (Key Friends)
@-}
insertTaggedFriends :: (PersistEntityBackend Friends ~ BaseBackend backend,
      PersistEntity Friends, Control.Monad.IO.Class.MonadIO m,
      PersistStoreWrite backend) =>
      TaggedFriends Friends -> ReaderT backend m (Key Friends)
insertTaggedFriends (TaggedFriends u) = insert u
