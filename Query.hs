

import Data.Lens
import Data.Lens.TH

data User 
  = User
  { _id :: Int
  , _name :: String
  , _cpf :: String
  , _age :: Int
  , _access :: Int
  }


query :: [(ks, vs)] -> (vs -> vs -> vs)  -> [(ki, vs)] 
query  t r = undefined 
