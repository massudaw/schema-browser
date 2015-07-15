{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoMonomorphismRestriction,UndecidableInstances,FlexibleContexts,OverloadedStrings ,TupleSections, ExistentialQuantification #-}

import Query
import Types
import Step
import Location
import PrefeituraSNFSE
import Safe hiding (at)
import Siapi3
import CnpjReceita
import TP.Widgets
import TP.QueryWidgets
import Control.Monad.Reader
import Control.Concurrent
import Data.Functor.Apply
import System.Environment
import Debug.Trace
import Data.Ord
import OFX

-- Timeline
--import Data.Time.Format
--import System.Locale
--import Data.Aeson
--import Text.Read

import Data.Time.Parse
import Utils
import Schema
import Data.Char (toLower)
import PandocRenderer
-- import Control.Monad
import Postgresql
import Data.Maybe
import Data.Functor.Identity
import Reactive.Threepenny
import Data.Graph(stronglyConnComp,flattenSCCs)
import Data.Traversable (traverse)
import qualified Data.Traversable as Tra
-- import Warshal
import Data.Time.LocalTime
import Data.Functor.Compose
import qualified Data.List as L
import qualified Data.Vector as Vector
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL
import Data.Time

import RuntimeTypes
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get,delete)
import Data.Monoid hiding (Product(..))

import qualified Data.Foldable as F
import qualified Data.Text.Lazy as T
import Data.ByteString.Lazy(toStrict)
import Data.Text.Lazy.Encoding
import qualified Data.Text.Encoding as TE
import qualified Data.Text as TE
import Data.Text.Lazy (Text)
import qualified Data.Set as S


import Database.PostgreSQL.Simple
import qualified Data.Map as M
import Data.Map (Map)
import Data.String


import Control.Arrow
import Crea

data BrowserState
  = BrowserState
  {host :: String
  ,dbn :: String
  ,user :: String
  ,pass :: String
  ,schema :: Maybe String
  ,table :: Maybe String
  }


argsToState  [h,d,u,p,s,t] = BrowserState h d  u p (Just s) (Just t )
argsToState  [h,d,u,p,s] = BrowserState h d  u p  (Just s)  Nothing
argsToState  [h,d,u,p] = BrowserState h d  u p Nothing Nothing

setup
     :: Show a =>   Event [a] -> [String] -> Window -> UI ()
setup e args w = void $ do
  return w # set title "Data Browser"
  let bstate = argsToState args
  (evDB,chooserDiv) <- databaseChooser bstate
  body <- UI.div
  be <- stepper [] e
  pollRes <- UI.div # sink UI.text (show <$> be)
  getBody w #+ [element chooserDiv , element body]
  mapUITEvent body (traverse (\(inf)-> do
    let k = M.keys $  M.filter (not. null. rawAuthorization) $   (pkMap inf )
    span <- chooserKey  inf k (table bstate)
    element body # set UI.children [span,pollRes] )) evDB


listDBS ::  BrowserState -> IO (Text,(Connection,[Text]))
listDBS dname = do
  connMeta <- connectPostgreSQL (fromString $ "host=" <> host dname <> " user=" <> user dname <> " dbname=" <> dbn  dname <> " password=" <> pass dname <> " sslmode= require" )
  dbs :: [Only Text]<- query_  connMeta "SELECT datname FROM pg_database  WHERE datistemplate = false"
  map <- (\db -> do
        connDb <- connectPostgreSQL ((fromString $ "host=" <> host dname <>" user=" <> user dname <> " dbname=" ) <> toStrict (encodeUtf8 db) <> (fromString $ " password=" <> pass dname <> " sslmode= require") )
        schemas :: [Only Text] <- query_  connDb "SELECT schema_name from information_schema.schemata"
        return (db,(connDb,filter (not . (`elem` ["information_schema","pg_catalog","pg_temp_1","pg_toast_temp_1","pg_toast","public"])) $ fmap unOnly schemas))) (T.pack $ dbn dname)
  return map

loginWidget userI passI =  do
  username <- UI.input # set UI.name "username" # set UI.value (maybe "" id userI)
  password <- UI.input # set UI.name "password" # set UI.type_ "password" # set UI.value (maybe "" id passI)
  let usernameE = (\i -> if L.null i then Nothing else Just i) <$> UI.valueChange username
      passwordE = (\i -> if L.null i then Nothing else Just i) <$> UI.valueChange password
  usernameB <- stepper userI usernameE
  passwordB <- stepper passI passwordE
  let usernameT = tidings usernameB usernameE
      passwordT = tidings passwordB passwordE
  login <- UI.div # set children [username,password]
  return $ TrivialWidget (liftA2 (liftA2 (,)) usernameT passwordT) login

instance Ord Connection where
  i < j = 1 < 2
  i <= j = 1 < 2
instance Eq Connection where
  i == j = True


form td ev =  tidings (facts td ) (facts td <@ ev )

databaseChooser sargs = do
  dbs <- liftIO $ listDBS  sargs
  let dbsInit = fmap (\s -> (T.pack $ dbn sargs ,) . (,T.pack s) . fst $ snd $ dbs ) $ ( schema sargs)
  wid <- loginWidget (Just $ user sargs  ) (Just $ pass sargs )
  dbsW <- listBox (pure $ (\(i,(c,j)) -> (i,) . (c,) <$> j) $ dbs ) (pure dbsInit  ) (pure id) (pure (line . show .fmap snd ))
  cc <- currentValue (facts $ userSelection dbsW)
  let dbsWE = rumors $ userSelection dbsW
  dbsWB <- stepper cc dbsWE
  let dbsWT  = tidings dbsWB dbsWE
  load <- UI.button # set UI.text "Connect" # sink UI.enabled (facts (isJust <$> dbsWT) )
  let login = liftA2 (liftA2 (,)) (triding wid) ( dbsWT )
      formLogin = form login (UI.click load)
  let genSchema ((user,pass),(dbN,(dbConn,schemaN))) = do
        conn <- connectPostgreSQL ("host=" <> (BS.pack $ host sargs) <>" user=" <> BS.pack user <> " password=" <> BS.pack pass <> " dbname=" <> toStrict ( encodeUtf8 dbN )<> " sslmode= require")
        execute_ conn "set bytea_output='hex'"
        keyTables dbConn conn (schemaN,T.pack user)
  chooserT <-  mapTEvent (traverse genSchema) formLogin
  chooserDiv <- UI.div # set children [getElement wid ,getElement dbsW,load]
  return $ (chooserT,chooserDiv)



unSOptional' (SOptional i ) = i
unSOptional' (SSerial i )  = i
unSOptional' i   = Just i

applyUI el f = (\a-> getWindow el >>= \w -> runUI w (f a))

tableNonRec k  =  F.toList $  tableNonRef  k

line n =   set  text n

attrLine i e   = do
  let nonRec = tableNonrec i
      attr i (k,v) = set  (strAttr (T.unpack $ keyValue k)) (renderShowable v) i
      attrs   l i  = foldl attr i l
  attrs (F.toList (tableAttrs i) ) $ line (   L.intercalate "," (F.toList $ fmap (renderShowable ) $  _kvKey $ allKVRec i) <> "," <>  (L.intercalate "," $ fmap (renderShowable) nonRec)) e

chooserKey inf kitems i = do
  let initKey = pure . join $ fmap rawPK . flip M.lookup (tableMap inf) . T.pack <$> i
  filterInp <- UI.input
  filterInpBh <- stepper "" (UI.valueChange filterInp)

  i :: [(Text,Int)] <- liftIO $ query (rootconn inf) (fromString "SELECT table_name,usage from metadata.ordering where schema_name = ?") (Only (schemaName inf))
  let orderMap = Just $ M.fromList  i
  bset <- buttonFSet  (L.sortBy (flip $  comparing (\ pkset -> liftA2 M.lookup  (fmap rawName . flip M.lookup (pkMap inf) $ pkset ) orderMap)) kitems)  initKey ((\j -> (\i -> L.isInfixOf (toLower <$> j) (toLower <$> i) ))<$> filterInpBh) (\i -> case M.lookup i (pkMap inf) of
                                       Just t -> T.unpack (translatedName t)
                                       Nothing -> show i )
  let bBset = triding bset
  onEvent (rumors bBset) (\ i ->
      liftIO $ execute (rootconn inf) (fromString $ "UPDATE  metadata.ordering SET usage = usage + 1 where table_name = ? AND schema_name = ? ") (( fmap rawName $ M.lookup i (pkMap inf)) ,  schemaName inf )
        )
  body <- UI.div # sink items (facts (pure . chooseKey inf <$> bBset ))
  UI.div # set children [filterInp,getElement bset, body]

tableNonrec k  = F.toList $ Compose $  _kvAttr $ (\(TB1 k)-> k) $ tableNonRef k

tableKeys (TB1 k) = concat $ fmap keyattr (F.toList k)
tableKeys (LeftTB1 (Just i)) = tableKeys i
tableKeys (ArrayTB1 [i]) = tableKeys i

tableAttrs (TB1 k) = concat $ fmap aattr (F.toList k)
tableAttrs (LeftTB1 (Just i)) = tableAttrs i
tableAttrs (ArrayTB1 [i]) = tableAttrs i



chooseKey
  ::
      InformationSchema -> S.Set Key -> UI Element
chooseKey inf key = mdo
  -- Filter Box (Saved Filter)

  liftIO$ swapMVar  (mvarMap inf) M.empty
  let bBset = pure key :: Tidings (S.Set Key)
  vp <- liftIO $addTable inf (fromJust  $ M.lookup key $ pkMap inf )

  -- Final Query ListBox
  filterInp <- UI.input
  filterInpBh <- stepper "" (UI.valueChange filterInp)
  let filterInpT = tidings filterInpBh (UI.valueChange filterInp)
      sortSet =  F.toList . tableKeys . allRec' (tableMap inf). (\(Just i)-> i) . flip M.lookup (pkMap inf) $ key
  sortList  <- multiListBox (pure sortSet) (F.toList <$> bBset) (pure (line . show))
  asc <- checkedWidget (pure True)
  let
      filteringPred i = (T.isInfixOf (T.pack $ toLower <$> i) . T.toLower . T.intercalate "," . fmap (T.pack . renderShowable) . F.toList  )
      tdiItemList = pure Nothing
  itemList <- listBox (tidings res2 never ) itemListT (pure id ) ((\l -> (\ i -> (set UI.style (noneShow $ filteringPred l i  ) ) . attrLine i)) <$> filterInpT)
  let itemListE = unionWith const (rumors (userSelection itemList)) (rumors tdiItemList)
  initItemListB <- currentValue (facts tdiItemList)
  itemListB <- stepper initItemListB itemListE
  let itemListT = tidings itemListB itemListE
  element (getElement itemList) # set UI.multiple True
  element itemList # set UI.style [("width","70%"),("height","300px")]

  let
     table = (\(Just i)-> i) $ M.lookup key (pkMap inf)

  chk <- checkedWidget (pure True)
  (cru,evs) <- crudUITable inf plugList  (pure True ) res2 [] (allRec' (tableMap inf) table) itemListT
  let eres = fmap addToList <$> evs
      tsort = (\ b c -> trace "sort" . sorting b c ) <$> triding asc <*> multiUserSelection sortList
  inisort <- currentValue (facts tsort)
  res2 <- accumB (inisort vp) (fmap concatenate $ unions [rumors tsort , (flip (foldr (\i -> addToList i ) ) <$> evs)])
  insertDiv <- UI.div # set children cru
  itemSel <- UI.ul # set items ((\i -> UI.li # set children [ i]) <$> [filterInp,getElement sortList,getElement asc] )
  itemSelec <- UI.div # set children [getElement itemList, itemSel] # set UI.style [("display","inline-flex")]
  UI.div # set children ([itemSelec,insertDiv ] )


lplugOrcamento = BoundedPlugin2 "Orçamento" "pricing" (fst renderProjectPricingA )  ( snd renderProjectPricingA )
lplugReport = BoundedPlugin2 "Relatório " "pricing" (fst renderProjectReport )  ( snd renderProjectReport )


testShowable  v s = case s of
          (SOptional Nothing ) -> False
          (SOptional (Just i)) -> testShowable v i
          i -> v i


(siapi2Polling   :: PollingPlugisIO  , siapi2Plugin :: Plugins) = (BoundedPollingPlugins pname 60 (tname  ,staticP url) elem,BoundedPlugin2  pname tname (staticP url) elemp)
  where
    pname ="Siapi2 Andamento"
    tname = "fire_project"
    varTB = fmap ( fmap (BS.pack . renderShowable ))<$>  varT
    url :: ArrowPlug (Kleisli IO) (Maybe (TB2 Text Showable))
    url = proc t -> do
      protocolo <- varTB "protocolo" -< t
      ano <- varTB "ano" -< t
      odx "aproval_date" -< t
      at "andamentos" (proc t -> do
        odx "andamento_date" -<  t
        odx "andamento_user" -<  t
        odx "andamento_status" -<  t
        odx "andamento_description" -<  t) -< t
      b <- act ( Tra.traverse  (\(i,j)-> if read (BS.unpack j) >= 15 then  return Nothing else (siapi2  i j)  )) -<  (liftA2 (,) protocolo ano )
      let ao bv =   case  join (findTB1 (== iat  bv)<$> (mapKey keyValue  <$> t)) of
                    Just i -> Nothing
                    Nothing -> Just $ TB1 $ KV (PK [] []) ( [iat bv])
          convertAndamento :: [String] -> TB2 Text (Showable)
          convertAndamento [da,des] =  TB1 $ fmap attrT  $ KV  (PK [] []) ([("andamento_date",STimestamp . fst . justError "wrong date parse" $  strptime "%d/%m/%y" da  ),("andamento_description",SText (T.filter (not . (`L.elem` "\n\r\t")) $ T.pack  des)),("andamento_user",SOptional Nothing ),("andamento_status",SOptional Nothing )])
          convertAndamento i = error $ "convertAndamento " <> show i
          iat bv = Compose . Identity $ (IT
                                            "andamentos"
                                            (LeftTB1 $ Just $ ArrayTB1 $ reverse $  fmap convertAndamento bv))
      returnA -< join  (  ao  .  tailEmpty . concat <$> join b)

    elem inf =  fmap (pure. catMaybes) . (\l -> mapM (\inp -> do
                              o <- elemp inf (Just inp)
                              maybe (return Nothing )  (\i -> updateModAttr inf i inp (lookTable inf tname)) o) l)
    elemp inf = maybe (return Nothing) (\inp -> do
                              b <- dynPK url (Just inp)
                              return $ liftKeys inf tname   <$> b)
    tailEmpty [] = []
    tailEmpty i  = tail i



type PollingPlugisIO = PollingPlugins [TB1 Showable] (IO [([TableModification Showable])])

(siapi3Polling   :: PollingPlugisIO  , siapi3Plugin :: Plugins) = (BoundedPollingPlugins pname 60 (tname ,staticP url) elem,BoundedPlugin2 pname tname  (staticP url) elemp)

  where
    pname , tname :: Text
    pname = "Siapi3 Andamento"
    tname = "fire_project"
    varTB i =  fmap (BS.pack . renderShowable ) . join . fmap unRSOptional' <$>  idxR i
    url :: ArrowReader -- ArrowPlug (Kleisli IO) (Maybe (TB2  Text Showable))
    url = proc t -> do
      protocolo <- varTB "protocolo" -< ()
      ano <- varTB "ano" -< ()
      cpf <- atR "id_owner,id_contact"
                $ atR "id_owner"
                    $ atAny "number" [varTB "cpf_number",varTB "cnpj_number"] -< t
      odxR "taxa_paga" -< ()
      odxR "aproval_date" -< ()
      atR "andamentos" (proc t -> do
          odxR "andamento_date" -<  t
          odxR "andamento_description" -<  t
          odxR "andamento_user" -<  t
          odxR "andamento_status" -<  t) -< ()

      b <- act (fmap join .  Tra.traverse   (\(i,j,k)-> if read (BS.unpack j) <= 14 then  return Nothing else liftIO $ siapi3  i j k )) -<   (liftA3 (,,) protocolo ano cpf)
      let convertAndamento [_,da,desc,user,sta] = TB1 $ fmap attrT  $ KV (PK [] []) ([("andamento_date",STimestamp . fst . justError "wrong date parse" $  strptime "%d/%m/%Y %H:%M:%S" da  ),("andamento_description",SText $ T.pack  desc),("andamento_user",SOptional $ Just $ SText $ T.pack  user),("andamento_status",SOptional $ Just $ SText $ T.pack sta)] )
          convertAndamento i = error $ "convertAndamento2015 :  " <> show i
      let ao  (bv,taxa) t = case  join $ (findTB1 (== iat  bv)<$> (mapKey keyValue  <$> t)) of
                    Just i ->  Nothing
                    Nothing ->    Just $ TB1 $ KV (PK [] []) ( [attrT ("taxa_paga",SOptional $ Just $  SBoolean $ not taxa),iat bv])
          iat bv = Compose . Identity $ (IT "andamentos"
                         (LeftTB1 $ Just $ ArrayTB1 $ reverse $ fmap convertAndamento bv))
      act (\i ->  do
          t <- ask
          return $  join $ ($t)<$> i ) -< ao <$> b

    elem inf =  fmap (pure. catMaybes)
          .  mapM (\inp -> do
                        o  <- geninf inf inp
                        maybe (return Nothing )  (\i -> updateModAttr inf i inp (lookTable inf "fire_project")) o)
    elemp inf = maybe (return Nothing) (geninf inf)
    geninf inf inp = do
            b <- runReaderT (dynPK url $ () ) (Just inp)
            return $ liftKeys inf tname  <$> b


lookKey' inf t k = justError ("lookKey' cant find key " <> show k <> " in " <> show t) $  foldr1 mplus $ fmap (\ti -> M.lookup (ti,k) (keyMap inf)) t

eitherToMaybeT (Left i) =  Nothing
eitherToMaybeT (Right r) =  Just r


sdate = SDate . localDay
stimestamp = STimestamp




{-
data Timeline
  = Timeline
  { header :: String
  , dates :: [(Either Day LocalTime,String)]
  }

queryTimeline = BoundedPlugin "Timeline" "pricing"(staticP arrow)  elem
  where
    convDateArr i = swap . fmap projDate  <$> (catMaybes $ fmap (traverse unRSOptional') $ catMaybes $ i)
    projDate (SDate (Finite f)) = Left f
    projDate (STimestamp (Finite f)) =  Right f
    projDate (SOptional (Just j )  ) = projDate j
    projDate i = error $ " projDate " <> show i
    arrow :: FunArrowPlug [(Either Day LocalTime,String)]
    arrow = proc t -> do
      prd <- varT "pricing_date" -< t
      papr <- varN "pricing_approval" -< t
      apd <- varN "id_project:aproval_date" -< t
      arr <- varN "pagamentos:payment_date" -< t
      arrD <- varN "pagamentos:payment_description" -< t
      andDa <- varN "id_project:andamentos:andamento_date" -< t
      andDe <- varN "id_project:andamentos:andamento_description" -< t
      let vv =  concat $ maybeToList $ (\(SComposite i) (SComposite j)-> fmap Just $ zip (renderShowable <$> F.toList j ) (F.toList i)) <$>  arr <*> arrD

      returnA -<  convDateArr ([("Proposta de Enviada",)<$> prd,("Projeto Aprovado",) <$> apd ,("Proposta Aprovada",) <$> papr] <>  vv {-<> vvand -})
    elem inf inputs = do
        e <- UI.div # set UI.id_ "timeline-embed"
        let  timeline i = Timeline "hello" (dynP arrow $ i)
        i <- UI.div # sink UI.html  (fmap (\i->  "<script>    var container = document.getElementById('timeline-embed');var items = new vis.DataSet("  <>  BSL.unpack ( encode (timeline i)) <> ") ;  var options = {} ; if (container.vis != null ) { container.vis.destroy(); } ; container.vis = new vis.Timeline(container,items,options); </script>") $ facts inputs)
        UI.div # set children [e,i]


instance ToJSON Timeline where
  toJSON (Timeline h v) = toJSON (dates <$> zip [0..] v)

    where dates (id,(Right i,j)) = object ["id" .= (id :: Int) ,"start" .=  ti i, "content" .= j, "type" .= ("point" :: String)]
          dates (id,(Left i,j)) = object ["id" .= (id :: Int) ,"start" .=  tti i, "content" .= j, "type" .= ("point" :: String)]
          ti  = formatTime defaultTimeLocale "%Y/%m/%d"
          tti  = formatTime defaultTimeLocale "%Y/%m/%d %H:%M:%S"
-}



gerarPagamentos = BoundedPlugin2 "Gerar Pagamento" tname  (staticP url) elem
  where
    tname = "plano_aluno"
    url :: Parser (Kleisli (ReaderT (Maybe (TB1 Showable)) IO)) (Access Text) () (Maybe (TB2  Text Showable))
    url = proc t -> do
          descontado <-  liftA2 (\v k -> v*(1 - k) )
              <$> atR "frequencia,meses"
                  (liftA2 (\v m -> v * fromIntegral m) <$> idxR "price" <*> idxR "meses")
              <*> idxR "desconto" -< ()
          atR "pagamento" (proc descontado -> do
              pinicio <- idxR "inicio"-< ()
              p <- idxR "vezes" -< ()
              let valorParcela = liftA2 (/)  descontado p
              atR "pagamentos" (proc t -> do
                  odxR "description" -<  t
                  odxR "price" -<  t
                  odxR "scheduled_date" -<  t ) -< ()
              let total = maybe 0 fromIntegral  p :: Int
              let pagamento = _tb $ FKT ([ attrT  ("pagamentos",SOptional Nothing)]) True [] (LeftTB1 $ Just $ ArrayTB1 ( fmap (\ix -> TB1 (KV (PK [attrT ("id",SSerial Nothing)] [attrT ("description",SOptional $ Just $ SText $ T.pack $ "Parcela (" <> show ix <> "/" <> show total <>")" )]) [attrT ("price",SOptional valorParcela), attrT ("scheduled_date",SOptional pinicio) ])) ([1.. total] )))
                  ao :: Maybe (TB2 Text Showable)
                  ao =  Just $ TB1 $ KV (PK [] []) [_tb $ IT   "pagamento"  (LeftTB1 $ Just $ TB1 $ KV (PK [] [] ) [pagamento ])]
              returnA -< ao ) -< descontado

    elem inf = maybe (return Nothing) (\inp -> do
                  b <- runReaderT (dynPK   url $ ())  (Just inp)
                  return $ liftKeys inf tname  <$> b )

pagamentoServico = BoundedPlugin2 "Gerar Pagamento" tname (staticP url) elem
  where
    tname = "servico_venda"
    url :: Parser (Kleisli (ReaderT (Maybe (TB1 (Showable))) IO)) (Access Text) () (Maybe (TB2  Text (Showable)))
    url = proc t -> do
          descontado <- atR "pacote,servico"
                  (liftA3 (\v m k -> v * fromIntegral m * (1 -k) ) <$> atR "servico" (idxR "price") <*> idxR "pacote"
                        <*> idxR "desconto") -< ()
          atR "pagamento" (proc descontado -> do
              pinicio <- idxR "inicio"-< ()
              p <- idxR "vezes" -< ()
              let valorParcela = liftA2 (/)  descontado p
              atR "pagamentos" (proc t -> do
                  odxR "description" -<  t
                  odxR "price" -<  t
                  odxR "scheduled_date" -<  t ) -< ()
              let total = maybe 0 fromIntegral  p :: Int
              let pagamento = Compose $ Identity $ FKT ([attrT  ("pagamentos",SOptional Nothing)]) True [] (LeftTB1 $ Just $ ArrayTB1 ( fmap (\ix -> TB1 (KV (PK [attrT ("id",SSerial Nothing)] [attrT ("description",SOptional $ Just $ SText $ T.pack $ "Parcela (" <> show ix <> "/" <> show total <>")" )]) [attrT ("price",SOptional valorParcela), attrT ("scheduled_date",SOptional pinicio) ])) ([1 .. total] )))
                  ao :: Maybe (TB2 Text (Showable))
                  ao =  Just $ TB1 $ KV (PK [] []) [Compose $ Identity $ IT   ("pagamento")  (LeftTB1 $ Just $ TB1 $ KV (PK [] [] ) [pagamento ])]
              returnA -< ao ) -< descontado

    elem inf = maybe (return Nothing) (\inp -> do
                      b <- runReaderT (dynPK   url $ ())  (Just inp)
                      return $  liftKeys inf tname  <$> b
                            )


importarofx = BoundedPlugin2 "OFX Import" tname  (staticP url) elem
  where
    tname = "account_file"
    url :: Parser (Kleisli IO) (Access Text) (Maybe (TB1 (Showable))) (Maybe (TB2 Text (Showable)))
    url = proc t -> do
      fn <- varT "file_name" -< t
      i <- varT "import_file" -< t
      r <- at "account" $ varT "id_account" -< t
      at "statements" (proc t -> do
        odx "fitid" -< t
        odx "memo" -< t
        odx "trntype" -< t
        odx "dtposted" -< t
        odx "dtuser" -< t
        odx "dtavail" -< t
        odx "trnamt" -< t
        odx "correctfitid" -< t
        odx "srvrtid" -< t
        odx "checknum" -< t
        odx "refnum" -< t
        odx "sic" -< t
        odx "payeeid" -< t
        ) -< t
      b <- act (fmap join . traverse (\(SText i, SBinary r) -> ofxPlugin (T.unpack i) (BS.unpack r))) -< liftA2 (,) fn i
      let ao :: TB2 Text (Showable)
          ao =  LeftTB1 $ ArrayTB1 . fmap (TB1 . fmap (attrT )) <$>  b
          ref :: [Compose Identity (TB Identity Text) (Showable)]
          ref = [attrT  ("statements",SOptional $ SComposite . Vector.fromList . fmap (snd . head ._pkKey . _kvKey ) <$> b)]
          tbst :: (Maybe (TB2 Text (Showable)))
          tbst = Just $ TB1 (KV (PK [] []) [_tb $ FKT ref True [] ao])
      returnA -< tbst
    elem inf = maybe (return Nothing) (\inp -> do
                b <- dynPK url (Just inp)
                return $ liftKeys inf  tname  <$> b)



notaPrefeitura = BoundedPlugin2 "Nota Prefeitura" tname (staticP url) elem
  where
    tname = "nota"
    varTB = fmap ( fmap (BS.pack . renderShowable ))<$>  varT
    url :: ArrowPlug (Kleisli IO) (Maybe (TB2 Text (Showable)))
    url = proc t -> do
      i <- varTB "id_nota" -< t
      odx "nota" -<  t
      r <- at "inscricao" (proc t -> do
                               n <- varTB "inscricao_municipal" -< t
                               u <- varTB "goiania_user"-< t
                               p <- varTB "goiania_password"-< t
                               returnA -< liftA3 (, , ) n u p  ) -< t
      b <- act (fmap join  . traverse (\(i, (j, k,a)) -> prefeituraNota j k a i ) ) -< liftA2 (,) i r
      let ao =  Just $ TB1 $ KV (PK [] []) [attrT ("nota",    SOptional b)]
      returnA -< ao
    elem inf = maybe (return Nothing) (\inp -> do
                              b <- dynPK url (Just inp)
                              return $ liftKeys inf tname  <$> b
                            )

queryArtCrea = BoundedPlugin2 "Documento Final Art Crea" tname (staticP url) elem
  where
    tname = "art"
    varTB = fmap ( fmap (BS.pack . renderShowable ))<$>  varT
    url :: ArrowPlug (Kleisli IO) (Maybe (TB2 Text (Showable)))
    url = proc t -> do
      i <- varTB "art_number" -< t
      idxT "payment_date" -<  t
      odx "art" -<  t
      r <- at "crea_register" (proc t -> do
                               n <- varTB "crea_number" -< t
                               u <- varTB "crea_user"-< t
                               p <- varTB "crea_password"-< t
                               returnA -< liftA3 (, , ) n u p  ) -< t
      b <- act (fmap join  . traverse (\(i, (j, k,a)) -> creaLoginArt  j k a i ) ) -< liftA2 (,) i r
      let ao =  Just $ TB1 $ KV (PK [] []) [attrT ("art",    SOptional b)]
      returnA -< ao
    elem inf = maybe (return Nothing) (\inp -> do
                              b <- dynPK url (Just inp)
                              return $ liftKeys inf tname <$> b
                            )


-- queryArtBoletoCrea :: Plugins
queryArtBoletoCrea = BoundedPlugin2  pname tname (staticP url) elem
  where
    pname = "Boleto Art Crea"
    tname = "art"
    varTB = fmap ( fmap (BS.pack . renderShowable ))<$>  varT
    url :: ArrowPlug (Kleisli IO) (Maybe (TB2 Text (Showable)))
    url = proc t -> do
      i <- varTB "art_number" -< t
      idxT "verified_date" -< t
      odx "boleto" -< t
      r <- at "crea_register" (proc t -> do
                               n <- varTB "crea_number" -< t
                               u <- varTB "crea_user"-< t
                               p <- varTB "crea_password"-< t
                               returnA -< liftA3 (, , ) n u p  ) -< t
      b <- act ( traverse (\(i, (j, k,a)) -> creaBoletoArt  j k a i ) ) -< liftA2 (,) i r
      let ao =  Just $ TB1 $ KV (PK [] []) [attrT ("boleto",   SOptional $ (SBinary. BSL.toStrict) <$> b)]
      returnA -< ao
    elem inf
       = maybe (return Nothing) (\inp -> do
                            b <- dynPK url (Just inp)
                            return $ liftKeys inf tname <$> b )



(queryArtAndamento ,artAndamentoPolling :: PollingPlugisIO ) = (BoundedPlugin2 pname tname (staticP url) elemp,BoundedPollingPlugins   pname 60 (tname ,staticP url) elem)
  where
    tname = "art"
    pname = "Andamento Art Crea"
    varTB = fmap ( fmap (BS.pack . renderShowable ))<$>  varT
    url :: ArrowPlug (Kleisli IO) (Maybe (TB2 Text Showable))
    url = proc t -> do
      i <- varTB "art_number" -< t
      odx "payment_date" -< t
      odx "verified_date" -< t
      r <- at "crea_register" (proc t -> do
                               n <- varTB "crea_number" -< t
                               u <- varTB "crea_user"-< t
                               p <- varTB "crea_password"-< t
                               returnA -< liftA3 (, , ) n u p  ) -< t
      v <- act (fmap (join .maybeToList) . traverse (\(i, (j, k,a)) -> creaConsultaArt  j k a i ) ) -< liftA2 (,) i r
      let artVeri dm = ("verified_date" ,) . SOptional . join $(\d ->  fmap (STimestamp . fst) $ strptime "%d/%m/%Y %H:%M" ( d !!1) ) <$> dm
          artPayd dm = ("payment_date" ,) . SOptional . join $ (\d -> fmap (STimestamp . fst )  $ strptime "%d/%m/%Y %H:%M" (d !!1) ) <$> dm
          artInp inp = Just $ TB1 $ KV (PK [] [] ) $fmap attrT   $ [artVeri $  L.find (\[h,d,o] -> L.isInfixOf "Cadastrada" h )  inp ,artPayd $ L.find (\[h,d,o] -> L.isInfixOf "Registrada" h ) (inp) ]
      i <- checkOutput "verified_date" -< (t,artInp v)
      j <- checkOutput "payment_date" -< (t,artInp v)
      returnA -< (catMaybes [i, j] )
      returnA -< Just $ TB1 $KV  (PK [] [] ) $ fmap attrT  $  catMaybes [ i,j]
    elem inf =  fmap (pure. catMaybes) . mapM (\inp -> do
                 o <- elemp inf (Just inp)
                 maybe
                  (return Nothing)
                  (\i-> if L.null (F.toList i)
                           then return Nothing
                           else updateModAttr inf i inp (lookTable inf tname)) o)
    elemp inf
          = maybe (return Nothing) (\inp -> do
                   b <- dynPK url (Just inp)
                   return $  liftKeys inf tname  <$> b)


queryCPFStatefull =  StatefullPlugin "CPF Receita" "owner" [staticP arrowF,staticP arrowS]   [[("captchaViewer",Primitive "jpg") ],[("captchaInput",Primitive "character varying")]] cpfCall
    where
      arrowF ,arrowS :: ArrowReader-- ArrowPlug (->) (Maybe (TB1 (Text,Showable)))
      arrowF = proc t -> do
              atAny "number" [idxR "cpf_number"] -< t
              odxR "captchaViewer" -< t
              returnA -< Nothing
      arrowS = proc t -> do
              idxR "captchaInput" -< t
              odxR "owner_name" -< t
              returnA -< Nothing




queryCNPJStatefull = StatefullPlugin "CNPJ Receita" "owner"
  [staticP arrowF ,staticP arrowS ]
  [[("captchaViewer",Primitive "jpg") ],[("captchaInput",Primitive "character varying")]] wrapplug
    where arrowF ,arrowS :: ArrowReader -- ArrowPlug (->) (Maybe (TB1 (Text,Showable)))
          arrowF = proc t -> do
            atAny "number" [idxR "cnpj_number"] -< t
            odxR "captchaViewer"-< t
            returnA -< Nothing
          arrowS = proc t -> do
            idxR "captchaInput" -< t
            odxR "owner_name" -< t
            odxR "address"-< t
            odxR "atividade_principal" -< ()
            odxR "atividades_secundarias" -< ()
            atR "atividades_secundarias" cnae -< t
            atR "atividade_principal" cnae -< t
            atR "address"  addrs -< t

            returnA -< Nothing

          cnae = proc t -> do
                  odxR "id" -< t
                  odxR "description" -< t
          addrs = proc t -> do
                  odxR "logradouro" -< t
                  odxR "number " -< t
                  odxR "uf" -< t
                  odxR "cep" -< t
                  odxR "complemento" -< t
                  odxR "municipio" -< t
                  odxR "bairro" -< t



topSortTables tables = flattenSCCs $ stronglyConnComp item
  where item = fmap (\n@(Raw _ _ _ t _ k _ fk _ ) -> (n,k,fmap (\(Path _ _ end)-> end) (S.toList fk) )) tables



main :: IO ()
main = do
  args <- getArgs
  --let schema = "public"
  --conn <- connectPostgreSQL "user=postgres password=queijo dbname=usda"
  {-
  let sorted = topSortTables (M.elems baseTables)

  print "DROPPING TABLES"
  traverse (\t -> do
    execute_ connTest . fromString . T.unpack . dropTable $ t
    print $ tableName t
    )  $ reverse  sorted

  print "CREATING TABLES"
  traverse (\t -> do
    execute_  connTest . fromString . T.unpack . createTable $ t
    print $ tableName t
    )  sorted
  -}
  (e:: Event [[TableModification (Showable) ]] ,h) <- newEvent

  forkIO $ do
      mapM_ (poller h) [siapi3Polling,siapi2Polling,artAndamentoPolling]

  startGUI (defaultConfig { tpStatic = Just "static", tpCustomHTML = Just "index.html"})  (setup e args)
  print "Finish"

poller handler (BoundedPollingPlugins n d (a,f) elem ) = do
  conn <- connectPostgreSQL ("user=postgres dbname=incendio")
  inf <- keyTables conn  conn ("incendio","postgres")
  forever $ do
        threadDelay (1000*1000)
        [t :: Only UTCTime] <- query conn "SELECT start_time from metadata.polling where poll_name = ? and table_name = ? and schema_name = ?" (n,a,"incendio" :: String)
        startTime <- getCurrentTime
        let intervalsec = fromIntegral $ 60*d
        if diffUTCTime startTime  (unOnly t) >  intervalsec
        then do
            execute conn "UPDATE metadata.polling SET start_time = ? where poll_name = ? and table_name = ? and schema_name = ?" (startTime,n,a,"incendio" :: String)
            print ("START - " <> show startTime  ::String)
            let rp = rootPaths'  (tableMap inf) (fromJust  $ M.lookup  a  $ tableMap inf )
            listRes <- queryWith_ (fromAttr (fst rp) ) conn  (fromString $ T.unpack $ snd rp)
            let evb = filter (\i -> tdInput i  && tdOutput1 i ) listRes
                tdInput i =  isJust  $ testTable i (fst f)
                tdOutput1 i =   not $ isJust  $ testTable i (snd f)
            i <- elem inf evb
            handler i
            end <- getCurrentTime
            print ("END - " <> show end ::String)
            execute conn "UPDATE metadata.polling SET end_time = ? where poll_name = ? and table_name = ? and schema_name = ?" (end ,n,a,"incendio" :: String)
            threadDelay (d*1000*1000*60)
        else do
            threadDelay (round $ (*1000000) $  diffUTCTime startTime (unOnly t))

{-
layout  infT = do
  vis <- UI.div # set UI.id_ "visualization"
  let draw inf  =
        let
            -- g = graphP inf
            v :: [(Int,Set Key)]
            v = zip [0..] (L.nub $ hvertices g <> tvertices g)
            e = filter  (\case {(Path _ _ _)-> True ; i -> False}) $ concat $ fmap snd $ M.toList $ edges g
            vmap = M.fromList $ swap <$>  v
            genVertices (i,t ) = object [ "id" .= i, "label" .= T.intercalate "," (F.toList (S.map keyValue t)) ]
            genEdges (Path i (FKJoinTable m _ l)  j ) = object [ "from" .= lid i , "to" .= lid j  , "label" .= (tableName m <> " join " <> tableName l ) ]
            genEdges (Path i (FetchTable  l)  j ) = object [ "from" .= lid i , "to" .= lid j  , "label" .= tableName l ]
            genEdges (Path i (FKInlineTable l)  j ) = object [ "from" .= lid i , "to" .= lid j  , "label" .= tableName l ]
            lid t = justError ("no key " <> show t) (M.lookup t vmap)
            nodesJSON = "var nodes = " <> encode (genVertices <$> v) <> ";"
            edgesJSON = "var edges = " <> encode (genEdges <$> e) <> ";"
            graphJSON = "<script> " <> BSL.unpack (nodesJSON <> edgesJSON) <> "var container = document.getElementById('visualization');  var data = { nodes: nodes,edges: edges}; var options = { hierarchicalLayout : { layout : 'direction' } , edges : { style : 'arrow'}} ;  var network = new vis.Network(container, data, options ); </script> "
        in graphJSON
  script <- UI.div # sink UI.html (maybe "" draw <$> infT)
  UI.div # set children [vis,script]
-}

withInf d s f = withConn d (f <=< (\conn -> keyTables conn conn (s,"postgres")))
withConnInf d s f = withConn d (\conn ->  f =<< liftIO ( keyTables  conn conn (s,"postgres")) )

testParse db sch q = withConnInf db sch (\inf -> do
                                       let (rp,rpq) = rootPaths' (tableMap inf) (fromJust $ M.lookup q (tableMap inf))
                                       putStrLn (  show rpq)
                                       putStrLn (  show rp)
                                       q <- queryWith_ (fromAttr (rp) ) (conn  inf) (fromString $ T.unpack $ rpq)
                                       print q
                                       return $ q
                                           )
testFireMetaQuery q = testParse "incendio" "metadata"  q
testFireQuery q = testParse "incendio" "incendio"  q
testAcademia q = testParse "academia" "academia"  q

plugList = [lplugOrcamento ,lplugReport,siapi3Plugin ,siapi2Plugin , importarofx,gerarPagamentos , pagamentoServico , notaPrefeitura,queryArtCrea , queryArtBoletoCrea , queryCEPBoundary,{-queryGeocodeBoundary,-}queryCNPJStatefull,queryCPFStatefull,queryArtAndamento]
