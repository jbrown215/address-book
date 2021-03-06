{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Foundation where

import Import.NoFoundation
import Database.Persist.Sql (ConnectionPool, runSqlPool)
import Text.Hamlet          (hamletFile)
import Text.Jasmine         (minifym)

-- Used only when in "auth-dummy-login" setting is enabled.
import Yesod.Auth.Dummy

import Yesod.Auth.OpenId    (authOpenId, IdentifierType (Claimed))
import Yesod.Auth.Email
import Yesod.Default.Util   (addStaticContentExternal)
import Yesod.Core.Types     (Logger)
import qualified Yesod.Core.Unsafe as Unsafe
import qualified Data.CaseInsensitive as CI
import qualified Data.Text.Encoding as TE
import qualified Data.Text as T
import qualified Yesod.Auth.Message as Msg

-- | The foundation datatype for your application. This can be a good place to
-- keep settings and values requiring initialization before your application
-- starts running, such as database connections. Every handler will have
-- access to the data present here.
data App = App
    { appSettings    :: AppSettings
    , appStatic      :: Static -- ^ Settings for static file serving.
    , appConnPool    :: ConnectionPool -- ^ Database connection pool.
    , appHttpManager :: Manager
    , appLogger      :: Logger
    }

data MenuItem = MenuItem
    { menuItemLabel :: Text
    , menuItemRoute :: Route App
    , menuItemAccessCallback :: Bool
    }

data MenuTypes
    = NavbarLeft MenuItem
    | NavbarRight MenuItem

-- This is where we define all of the routes in our application. For a full
-- explanation of the syntax, please see:
-- http://www.yesodweb.com/book/routing-and-handlers
--
-- Note that this is really half the story; in Application.hs, mkYesodDispatch
-- generates the rest of the code. Please see the following documentation
-- for an explanation for this split:
-- http://www.yesodweb.com/book/scaffolding-and-the-site-template#scaffolding-and-the-site-template_foundation_and_application_modules
--
-- This function also generates the following type synonyms:
-- type Handler = HandlerT App IO
-- type Widget = WidgetT App IO ()
mkYesodData "App" $(parseRoutesFile "config/routes")

-- | A convenient synonym for creating forms.
type Form x = Html -> MForm (HandlerT App IO) (FormResult x, Widget)

-- Please see the documentation for the Yesod typeclass. There are a number
-- of settings which can be configured by overriding methods here.
instance Yesod App where
    -- Controls the base of generated URLs. For more information on modifying,
    -- see: https://github.com/yesodweb/yesod/wiki/Overriding-approot
    approot = ApprootRequest $ \app req ->
        case appRoot $ appSettings app of
            Nothing -> getApprootText guessApproot app req
            Just root -> root

    -- Store session data on the client in encrypted cookies,
    -- default session idle timeout is 120 minutes
    makeSessionBackend _ = Just <$> defaultClientSessionBackend
        120    -- timeout in minutes
        "config/client_session_key.aes"

    -- Yesod Middleware allows you to run code before and after each handler function.
    -- The defaultYesodMiddleware adds the response header "Vary: Accept, Accept-Language" and performs authorization checks.
    -- Some users may also want to add the defaultCsrfMiddleware, which:
    --   a) Sets a cookie with a CSRF token in it.
    --   b) Validates that incoming write requests include that token in either a header or POST parameter.
    -- To add it, chain it together with the defaultMiddleware: yesodMiddleware = defaultYesodMiddleware . defaultCsrfMiddleware
    -- For details, see the CSRF documentation in the Yesod.Core.Handler module of the yesod-core package.
    yesodMiddleware = defaultYesodMiddleware

    defaultLayout widget = do
        master <- getYesod
        mmsg <- getMessage

        muser <- maybeAuthPair
        mcurrentRoute <- getCurrentRoute

        -- Get the breadcrumbs, as defined in the YesodBreadcrumbs instance.
        (title, parents) <- breadcrumbs

        -- We break up the default layout into two components:
        -- default-layout is the contents of the body tag, and
        -- default-layout-wrapper is the entire page. Since the final
        -- value passed to hamletToRepHtml cannot be a widget, this allows
        -- you to use normal widget features in default-layout.

        pc <- widgetToPageContent $ do
            addStylesheet $ StaticR css_bootstrap_css
            $(widgetFile "default-layout")
        withUrlRenderer $(hamletFile "templates/default-layout-wrapper.hamlet")

    -- The page to be redirected to when authentication is required.
    authRoute _ = Just $ AuthR LoginR

    -- Routes not requiring authentication.
    isAuthorized (AuthR _) _ = return Authorized
    isAuthorized HomeR _ = return Authorized
    isAuthorized FaviconR _ = return Authorized
    isAuthorized RobotsR _ = return Authorized
    isAuthorized (StaticR _) _ = return Authorized
    isAuthorized BrowseR _ = return Authorized
    isAuthorized (ProfileR personId) _ = authorizedFriend personId--Change isAuthenticated when you get authentication working
    isAuthorized (UpdatePersonR personId) _ = isAuthenticated personId
    isAuthorized (AddFriendR personId) _ = return Authorized
    isAuthorized (ConfirmLinkR personId) _ = return Authorized
    isAuthorized (ConfirmFriendR personId) _ = authorizedFriendRequest personId

    -- This function creates static content files in the static folder
    -- and names them based on a hash of their content. This allows
    -- expiration dates to be set far in the future without worry of
    -- users receiving stale content.
    addStaticContent ext mime content = do
        master <- getYesod
        let staticDir = appStaticDir $ appSettings master
        addStaticContentExternal
            minifym
            genFileName
            staticDir
            (StaticR . flip StaticRoute [])
            ext
            mime
            content
      where
        -- Generate a unique filename based on the content itself
        genFileName lbs = "autogen-" ++ base64md5 lbs

    -- What messages should be logged. The following includes all messages when
    -- in development, and warnings and errors in production.
    shouldLog app _source level =
        appShouldLogAll (appSettings app)
            || level == LevelWarn
            || level == LevelError

    makeLogger = return . appLogger

-- Define breadcrumbs.
instance YesodBreadcrumbs App where
  breadcrumb HomeR = return ("Home", Nothing)
  breadcrumb (AuthR _) = return ("Login", Just HomeR)
  breadcrumb (ProfileR _) = return ("Profile", Just HomeR)
  breadcrumb  _ = return ("home", Nothing)

-- How to run database actions.
instance YesodPersist App where
    type YesodPersistBackend App = SqlBackend
    runDB action = do
        master <- getYesod
        runSqlPool action $ appConnPool master
instance YesodPersistRunner App where
    getDBRunner = defaultGetDBRunner appConnPool

instance YesodAuth App where
      type AuthId App = UserId

      loginDest _ = HomeR
      logoutDest _ = HomeR
      authPlugins _ = [authEmail]

      -- Need to find the UserId for the given email address.
      getAuthId creds = runDB $ do
        x <- insertBy $ User (unpack (credsIdent creds)) Nothing Nothing 0
        return $ Just $
          case x of
            Left (Entity userid _) -> userid -- newly added user
            Right userid -> userid -- existing user

      authHttpManager = error "Email doesn't need an HTTP manager"

-- Here's all of the email-specific code
instance YesodAuthEmail App where
      type AuthEmailId App = UserId

      afterPasswordRoute _ = HomeR

      addUnverified email verkey = do
        uid <- runDB $ insert $ User (unpack email) Nothing (Just (unpack verkey)) 0
        return uid
        --redirect AuthR $ verifyR uid verkey

      sendVerifyEmail email verkey verurl = do
        -- Print out to the console the verification email, for easier
        -- debugging.
        redirect $ ConfirmLinkR $ unpack verurl
        --liftIO $ putStrLn $ "Copy/ Paste this URL in your browser:" ++ verurl

      getVerifyKey = runDB . fmap (fmap pack . join . fmap userVerkey) . get
      setVerifyKey uid key = runDB $ update uid [UserVerkey =. Just (unpack key)]
      verifyAccount uid = runDB $ do
        mu <- get uid
        case mu of
          Nothing -> return Nothing
          Just u -> do
            insert $ Person (userEmail u) "[No Name]" "[No Street]" 0
            update uid [UserVerified =. 1]
            return $ Just uid
      getPassword = runDB . fmap (fmap pack . join . fmap userPassword) . get
      setPassword uid pass = runDB $ update uid [UserPassword =. Just (unpack pass)]
      getEmailCreds email = runDB $ do
        mu <- getBy $ UniqueUser (unpack email)
        case mu of
          Nothing -> return Nothing
          Just (Entity uid u) -> return $ Just EmailCreds
                { emailCredsId = uid
                , emailCredsAuthId = Just uid
                , emailCredsStatus = isJust $ userPassword u
                , emailCredsVerkey = fmap pack $ userVerkey u
                , emailCredsEmail = email
                }
      getEmail = runDB . fmap (fmap pack . fmap userEmail) . get

getAuthPerson :: Handler (Maybe (Key Person, Person))
getAuthPerson = do
    myId <- maybeAuthId
    authPerson <- case myId of
                   Nothing -> return $ Nothing
                   Just id -> runDB $ do
                     user <- get id
                     authPerson <-
                       case user of
                         Nothing -> return $ Nothing
                         Just u -> do
                           x <- getBy $ UniquePerson (userEmail u)
                           authPerson <- case x of
                                           Nothing -> return $ Nothing
                                           Just (Entity uid person) -> return $ Just (uid, person)
                           return authPerson
                     return authPerson
    return authPerson


getFriendList :: PersonId -> Handler [Text]
getFriendList personId = do
  personOpt <- runDB $ get personId
  case personOpt of
    Nothing -> return []
    Just (Person email _ _ _) ->
      runDB $ do
        friendsOpt <- getBy $ UniqueFriend email
        case friendsOpt of
          Nothing -> return []
          Just (Entity uid (Friends _ _ friendList _)) -> return $ map pack friendList

getRequestList :: PersonId -> Handler [Text]
getRequestList personId = do
  personOpt <- runDB $ get personId
  case personOpt of
    Nothing -> return []
    Just (Person email _ _ _) ->
      runDB $ do
        friendsOpt <- getBy $ UniqueFriend email
        case friendsOpt of
          Nothing -> return []
          Just (Entity uid (Friends _ requestList _ _)) -> return $ map pack requestList

getOutgoingRequestList :: PersonId -> Handler [Text]
getOutgoingRequestList personId = do
  personOpt <- runDB $ get personId
  case personOpt of
    Nothing -> return []
    Just (Person email _ _ _) ->
      runDB $ do
        friendsOpt <- getBy $ UniqueFriend email
        case friendsOpt of
          Nothing -> return []
          Just (Entity uid (Friends _ _ _ outgoingRequests)) -> return $ map pack outgoingRequests



isFriend :: PersonId -> Handler Bool
isFriend p2 = do
  muid <- maybeAuthId
  pid <- getAuthPerson
  case pid of
    Nothing -> return False
    Just (p1, Person email1 _ _ _) -> do
      friendList <- getFriendList p1
      person2Opt <- runDB $ get p2
      case person2Opt of
        Nothing -> return False
        Just (Person email2 _ _ _) -> return $ let e2 = pack email2 in any (\x -> e2 == x) friendList


isFriendRequest :: PersonId -> Handler Bool
isFriendRequest p2 = do
  muid <- maybeAuthId
  pid <- getAuthPerson
  case pid of
    Nothing -> return False
    Just (p1, Person email1 _ _ _) -> do
      friendList <- getRequestList p1
      person2Opt <- runDB $ get p2
      case person2Opt of
        Nothing -> return False
        Just (Person email2 _ _ _) -> return $ let e2 = pack email2 in any (\x -> e2 == x) friendList


isMe :: PersonId -> Handler Bool
isMe personId = do
    muid <- maybeAuthId
    pid <- getAuthPerson
    case muid of
        Nothing -> return False
        Just id -> case pid of
                     Nothing -> return False
                     Just (pid, _) -> do
                       if pid == personId
                         then return True
                         else return False

authorizedFriend :: PersonId -> Handler AuthResult
authorizedFriend personId = do
  friend <- isFriend personId
  me <- isMe personId
  if friend || me
    then return Authorized
    else return $ Unauthorized "If you want to view this page, send a friend request."

authorizedFriendRequest :: PersonId -> Handler AuthResult
authorizedFriendRequest personId = do
  friend <- isFriendRequest personId
  me <- isMe personId
  if friend || me
    then return Authorized
    else return $ Unauthorized "If you want to view this page, send a friend request."


-- | Access function to determine if a user is logged in.
isAuthenticated :: PersonId -> Handler AuthResult
isAuthenticated personId = do
    muid <- maybeAuthId
    pid <- getAuthPerson
    case muid of
        Nothing -> return $ Unauthorized "You must login to access this page"
        Just id -> case pid of
                     Nothing -> return $ Unauthorized "Account invalid. Please log in."
                     Just (pid, _) -> do
                       if pid == personId
                         then return Authorized
                         else return $ Unauthorized "You do not have permission to view this page."

instance YesodAuthPersist App

-- This instance is required to use forms. You can modify renderMessage to
-- achieve customized and internationalized form validation messages.
instance RenderMessage App FormMessage where
    renderMessage _ _ = defaultFormMessage

-- Useful when writing code that is re-usable outside of the Handler context.
-- An example is background jobs that send email.
-- This can also be useful for writing code that works across multiple Yesod applications.
instance HasHttpManager App where
    getHttpManager = appHttpManager

unsafeHandler :: App -> Handler a -> IO a
unsafeHandler = Unsafe.fakeHandlerGetLogger appLogger

-- Note: Some functionality previously present in the scaffolding has been
-- moved to documentation in the Wiki. Following are some hopefully helpful
-- links:
--
-- https://github.com/yesodweb/yesod/wiki/Sending-email
-- https://github.com/yesodweb/yesod/wiki/Serve-static-files-from-a-separate-domain
-- https://github.com/yesodweb/yesod/wiki/i18n-messages-in-the-scaffolding
