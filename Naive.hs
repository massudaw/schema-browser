import Data.List(intersperse)
import Data.Monoid
import Data.Maybe
import qualified Data.Foldable as F
import qualified Data.Set as S
import Data.Set (Set) 
import qualified Data.Map as M
import Data.Map (Map)

data Relation = Relation 
    { natural :: (Set String) 
    , specific :: (Set String)}
    deriving(Show)

-- Smart Constructors
spec x y = Relation (S.fromList [x]) (S.fromList [y])
nat x = Relation (S.singleton x) S.empty

instance Monoid Relation where
  mempty = Relation S.empty S.empty 
  (Relation x y ) `mappend` (Relation x1 y1) = Relation (x <> x1) (y <> y1)

data SqlField
data Filter 
    = Category 
    { field :: String
    , elements :: Set Int }
    | Interval 
    { field :: String 
    , interval :: (Int,Int) }
    deriving(Eq,Ord,Show)


renderFilter (Category s e ) = s <> " IN ( " <> (concat $ intersperse " , " (fmap show $ F.toList e) )  <> " ) "
renderFilter (Interval s (init,end) ) = s <> " >= " <>  show init <> " AND "  <> s <> " < " <> show end 


buildContext norm fields path = foldr (<>) mempty $ catMaybes $ fmap (find path norm )  fields  

specializeFilters path rel norm filters = Relation (S.fromList $ renderFilters f ) (specific rel)
    where map = M.fromList (fmap (\i-> (i,[])) (F.toList $ natural rel )) 
          f = foldl insertion map filters
          insertion  m f =  case (findFirst path norm (field f) ) of
                            Just i -> M.insertWith (++)  i [f]  m
                            Nothing -> m
    
renderFilters f = fmap render (zip (M.toList f ) [0..])
    where 
        render ((c,l),i) = "(SELECT * FROM " <> c <> " WHERE " <> (concat $ intersperse " AND " (fmap renderFilter l)) <> ") AS ctx_" <> show i


renderQuery rel = "(SELECT * FROM " <> naturalPart <> specificPart <> ") AS relation "
    where
        naturalPart = concat $ intersperse " NATURAL JOIN " (F.toList (natural rel ))         
        specificPart = case (F.toList $ specific rel) of
                        [] -> ""
                        x -> " WHERE " <> (concat $ intersperse " AND " x )

    

        
query = ["id_spraying","id_daily","id_operator","id_client","id_contour"]

filters = [Category "id_daily" (S.singleton 19)]

main = do
    let rel = buildContext "id_spraying" query pathMap 
    print $ rel  
    let spec = specializeFilters pathMap rel "id_spraying" filters 
    print $ renderQuery spec 

pathMap = fmap M.fromList $  M.fromList $ [("id_spraying",
            [("timestamp_init",se)
            ,("id_daily",se)
            ,("id_machine",se)
            ,("id_farm",farm)
            ,("id_contour",contour)
            ,("id_operator",operator)
            ,("id_spraying",s)])]
    where s = nat "(select *,id_sequence AS id_spraying from onetgeo.spraying) as spraying"
          se = nat "(SELECT (((timestamp_init/1000)/3600)/24) :: bigint AS id_daily,(date_part('hour', to_timestamp(timestamp_init/1000) AT TIME ZONE 'BRT')) as time_h,service_order_number,id_machine,id_sequence,timestamp_init,timestamp_end,operator_number   FROM onetgeo.services) as s"
          contour =  spec "otmisnet.contour" "st_contains(geom_c,geom_s)"
          farm =  nat "otmisnet.farm" <> contour
          operator  = nat "otmisnet.operator" <> se

findFirst m norm =  fmap ( head . F.toList . natural ) . find m norm
                        
find m norm end  = case M.lookup norm m of
                    Just i -> M.lookup end i
                    Nothing -> Nothing


