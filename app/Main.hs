{-# LANGUAGE UnicodeSyntax #-}


import Diagrams.Backend.Rasterific.CmdLine
import Diagrams.Prelude
import Diagrams.TwoD.GraphViz
import Data.GraphViz.Commands
import Control.Monad.State
import Control.Lens
import Control.Lens.TH

import Data.Set (Set)
import qualified Data.Set as Set


main = theGraph >>= defaultMain
  where
    theGraph :: IO (Diagram B)
    theGraph = simpleGraphDiagram Neato hex

hex = mkGraph [0..19]
        (   [ (v, (v+1)`mod`6, ()) | v <- [0..5] ]
         ++ [ (v, v+k, ()) | v <- [0..5], k <- [6,12] ]
         ++ [ (2,18,()), (2,19,()), (15,18,()), (15,19,()), (18,3,()), (19,3,()) ]
        )

data RelProp
  = CanonRelationship -- This is a canon relationship
  | CanonInterest -- There is confirmed intrest in canon
  | Speculative -- This is purely speculative, we have no evidence for it
  | Omake -- This is from an omake
  deriving (Ord,Eq,Show,Read)

data LinkProp
  = Unrequited
  deriving (Ord,Eq,Show,Read)

data Link = Link {
    linkName :: String
  , linkProperties :: Set LinkProp
  }

makeFields ''Link

newtype Person = Person String
  deriving (Eq, Ord, Show, Read)

data Rel = Rel {
    relID :: Integer
  , relProperties :: Set RelProp
  } deriving (Ord, Eq, Show, Read)

makeFields ''Rel

type Vert = Either Person Rel

data ShipS = ShipS {
    shipsRelCounter :: Integer
  , shipsVertices :: [Vert]
  , shipsEdges :: [(Vert,Vert,Set LinkProp)]
  } deriving (Ord, Eq, Show, Read)


makeFields ''ShipS

type ShipM a = State ShipS a

-- unrequited :: Link -> Link
--
-- ♠ u2660
(♠) :: Link -> Link -> ShipM ()
(♠) = undefined


--
-- ♣ u2663
-- (♣) :: Link -> (Link, Link) -> ShipM ()
--
-- ♥ u2665
-- (♥) :: Link -> Link -> ShipM ()
--
-- ♦ u2666
-- (♦) :: Link -> Link -> ShipM ()
--
-- canon         :: ShipM () -> ShipM ()
-- speculative   :: ShipM () -> ShipM ()
--
--
-- title :: String
-- title = "Marked For Death : Shipping Diagram v2.7"
--
-- data VertType
--   = Name
--   | Heart
--   | Spade
--   | Club
--   | Diamond
--   deriving (Eq, Show, Read, Ord)
--
-- data Vertex = Vertex {
--     vName :: String
--   , vType :: VertType
--   }
--
--
-- data Edge = Edge
--

