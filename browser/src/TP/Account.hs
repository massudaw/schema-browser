{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TP.Account where

import GHC.Stack
import Environment
import TP.View
import Data.Ord
import Utils
import Step.Host
import Control.Lens (_2,(^.))
import qualified Data.Interval as Interval
import NonEmpty (NonEmpty)
import qualified NonEmpty as Non
import Data.Functor.Identity
import Control.Concurrent
import Types.Patch
import Control.Arrow
import Data.Either
import Data.Interval (Interval(..))
import Control.Monad.Writer
import Data.Time.Calendar.WeekDate
import Data.Char
import qualified Data.Text.Encoding as TE
import Control.Concurrent.Async
import Safe
import Query
import Data.Time
import qualified Data.Aeson as A
import Text
import qualified Types.Index as G
import Debug.Trace
import Types
import SchemaQuery
import TP.Widgets
import Control.Monad.Reader
import Data.Maybe
import Reactive.Threepenny hiding(apply)
import qualified Data.List as L
import qualified Data.ByteString.Lazy.Char8 as BSL

import RuntimeTypes
import qualified Graphics.UI.Threepenny as UI
import Graphics.UI.Threepenny.Core hiding (get,delete,apply)
import Data.Monoid hiding (Product(..))

import qualified Data.Foldable as F
import qualified Data.Text as T
import Data.Text (Text)

import qualified Data.Map as M



accountWidgetMeta inf = do
  (fmap F.toList . currentValue . facts ) =<<  (transactionNoLog (meta inf) $ dynPK (accountDef inf) ())

accountDef inf
  = projectS
      (innerJoinS
        (innerJoinS
          (tableDef inf `whereS` schemaPred)
          (fromS "accounts" ) (schemaI "accounts"))
        (fromS "event" ) (schemaI "event")) (irecord fields)

  where
      schemaPred = [(keyRef "schema",Left (int (schemaId inf),Equals))]
      schemaI t = [Rel "oid" Equals (NInline t "table")]
      fields =  proc t -> do
        (color,afields) <- iforeign (schemaI "accounts")(ivalue $ irecord (
          (,)<$> ifield "color" (ivalue $ readV PText)
             <*> ifield "account" (imap $ ivalue $  readV PText))) -< ()
        (tname,desc,dir,pks) <- tableProj inf -< ()
        efields <- iforeign (schemaI "event") (ivalue $ 
            irecord 
              (iforeign [Rel (RelAccess (Rel "table" Equals "oid") "table") Equals "table", Rel "column" Equals "ordinal_position"] 
                (imap . ivalue $ 
                irecord 
                  (ifield  "column_name" (ivalue $  readV PText))))) -< ()
        let
          toLocalTime = fmap to
            where
              to (STime (STimestamp i ))  = STime $ STimestamp $  i
              to (STime (SDate i )) = STime $ SDate i
          convField (IntervalTB1 i) = catMaybes [fmap (("start",). toLocalTime )$ unFinite $ Interval.lowerBound i,fmap (("end",).toLocalTime) $ unFinite $ Interval.upperBound i]
          convField v = [("start",toLocalTime $v)]
          convField i = errorWithStackTrace (show i)
          scolor =  "#" <> renderPrim color
          projf r desc efield@(SText field) (SText aafield)  = do
              i <- unSOptional =<< recLookupInf inf tname (indexerRel field) r
              accattr <- unSOptional =<< recLookupInf inf tname (indexerRel aafield) r
              fields <- mapM (\(SText i) -> unSOptional =<< recLookupInf inf tname (indexerRel i) r) (fromMaybe pks desc)
              return . M.fromList $
                [
                ("title",txt (T.pack $  L.intercalate "," $ renderShowable <$> F.toList fields))
                ,("commodity", accattr )
                ,("field", TB1 efield )] <> convField i
          proj r = ( F.toList $ projf r (fmap toListTree desc) <$> efields <*> afields)
        returnA -< (txt $ T.pack $ scolor ,lookTable inf tname,TB1 <$> efields,TB1 <$> afields,proj )


accountWidget (incrementT,resolutionT) sel inf = do
    let
      calendarSelT = liftA2 (,) incrementT resolutionT
    dashes <- ui $ accountWidgetMeta inf
    let allTags =  dashes
    itemListEl2 <- mapM (\i ->
      (i^. _2,) <$> UI.div  # set UI.style [("width","100%"),("height","150px") ,("overflow-y","auto")]) dashes
    let
      legendStyle lookDesc table b
          =  do
            let item = M.lookup table  (M.fromList  $ fmap (\i@(_,b,_,_,_)-> (b,i)) dashes )
            traverse (\k@(c,tname,_,_,_) ->   mdo
              header <-  UI.div # set text  (T.unpack lookDesc)  # set UI.class_ "col-xs-11"
              element b # set UI.class_ "col-xs-1"
              UI.label # set children [b,header]
                       # set UI.style [("background-color",renderShowable c)] # set UI.class_ "table-list-item" # set UI.style [("display","-webkit-box")]
              ) item
    calendar <- UI.div # set UI.class_ "col-xs-10"

    let
      calFun :: UI [Element]
      calFun = do
         els <- traverseUI
            (\(selected ,calT )->
              mapM (\(_,table,fields,efields,proj) -> do
                let pred = WherePredicate $ timePred inf table (fieldKey <$> fields ) calT
                    fieldKey (TB1 (SText v))=   v
                v <-  ui $ transactionNoLog  inf $ selectFrom (tableName table) Nothing pred
                els <- traverseUI
                  (\i -> do
                    let caption =  UI.caption # set text (T.unpack $ tableName table)
                        header = UI.tr # set items (sequence [UI.th # set text (L.intercalate "," $ F.toList $ renderShowable<$>  fields) , UI.th # set text "Title" ,UI.th # set text (L.intercalate "," $ F.toList $ renderShowable<$>efields) ])
                        row i = UI.tr # set items (sequence [UI.td # set text (L.intercalate "," [maybe "" renderShowable $ M.lookup "start" i , maybe "" renderShowable $ M.lookup "end" i]), UI.td # set text (maybe "" renderShowable $ M.lookup "title" i), UI.td # set text (maybe "" renderShowable $ M.lookup "commodity" i)])
                        body = fmap row dat <> if L.null dat then [] else [totalrow totalval]
                        dat =  concatMap (catMaybes.proj)  $ G.toList (primary i)

                        totalval = M.fromList [("start",mindate),("end",maxdate),("title",txt "Total") ,("commodity", totalcom)]
                          where
                            totalcom = sum $ justError "no" .M.lookup "commodity" <$> dat
                            mindate = minimum $ justError "no" . M.lookup "start" <$> dat
                            maxdate = maximum $ justError "no" . M.lookup "start" <$> dat
                        totalrow i = UI.tr # set items  (mapM (\i -> i # set UI.style [("border","solid 2px")] )[UI.td # set text (L.intercalate "," [maybe "" renderShowable $ M.lookup "start" i , maybe "" renderShowable $ M.lookup "end" i]), UI.td # set text (maybe "" renderShowable $ M.lookup "title" i), UI.td # set text (maybe "" renderShowable $ M.lookup "commodity" i)] ) # set UI.style [("border","solid 2px")]
                    UI.table # set items (sequence $ caption:header:body)) (collectionTid v)
                UI.div # sink UI.children (pure <$> facts els)
                    ) (filter (flip L.elem (F.toList selected) .  (^. _2)) dashes )

                ) $ (,) <$> sel <*> calendarSelT

         pure <$> UI.div # sink children (facts  els)
    return (legendStyle,dashes,calFun )


