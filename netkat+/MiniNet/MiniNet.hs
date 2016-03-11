{-# LANGUAGE ImplicitParams, TupleSections #-}

module MiniNet.MiniNet (generateMininetTopology, NodeMap) where

import Text.JSON
import Data.Maybe
import Control.Monad.State
import Data.List

import Topology
import Util
import Syntax

hstep = 100
vstep = 100

type Switches = [JSValue]
type Hosts    = [JSValue]
type NodeMap  = [(InstanceDescr, String)]

generateMininetTopology :: Refine -> Topology -> (String, NodeMap)
generateMininetTopology r topology = (encode $ toJSObject attrs, nmap)
    where -- max number of nodes in a layer
          width = maximum $ map (length . (uncurry instMapFlatten)) topology
          -- render nodes
          (sws, hs, nmap) = execState (mapIdxM (renderNodes width) topology) ([],[],[])
          -- render links
          links = let ?r = r in
                  let ?t = topology in
                  mapMaybe (renderLink nmap)
                  $ concatMap (\(n, imap) -> concatMap instLinks $ instMapFlatten n imap) topology
          attrs = [ ("controllers", JSArray [])
                  , ("hosts"      , JSArray hs)
                  , ("switches"   , JSArray sws)
                  , ("links"      , JSArray links)
                  , ("version"    , JSRational False 2)
                  ]
          

renderNodes :: Int -> (Node, InstanceMap) -> Int -> State (Switches, Hosts, NodeMap) ()
renderNodes w (n, imap) voffset = do 
    let nodes = instMapFlatten n imap
        offset = (w - length nodes) `div` 2
        nodeoff = zip nodes [offset..]
    mapM_ (renderNode voffset n) nodeoff

renderNode :: Int -> Node -> ((InstanceDescr, PortLinks), Int) -> State (Switches, Hosts, NodeMap) ()
renderNode voffset node ((descr, _), hoffset) = do
    (sws, hs, nmap) <- get
    let (letter, number) = if' (nodeType node == NodeSwitch) ("s", length sws) ("h", length hs)
        ndname = letter ++ show number
        opts = [ ("controllers", JSArray [])
               , ("hostname"   , JSString $ toJSString ndname) 
               , ("nodeNum"    , JSRational False $ fromIntegral number)
               , ("switchType" , JSString $ toJSString "bmv2")] ++
               if' (nodeType node == NodeHost) [("ip4", JSString $ toJSString $ formatIP (head $ idescKeys descr))] []
        attrs = [ ("number", JSString $ toJSString $ show number)
                , ("opts"  , JSObject $ toJSObject opts)
                , ("x"     , JSString $ toJSString $ show $ (hoffset + 1) * hstep)
                , ("y"     , JSString $ toJSString $ show $ (voffset + 1) * vstep)]
        n = JSObject $ toJSObject attrs 
        nmap' = (descr, ndname):nmap
    put $ if' (nodeType node == NodeSwitch) ((n:sws), hs, nmap') (sws, (n:hs), nmap')

formatIP :: Expr -> String
formatIP (EStruct _ _ fs) = intercalate "." $ map (show . exprIVal) fs
formatIP e                = error $ "MiniNet.formatIP " ++ show e

instLinks :: (?t::Topology,?r::Refine) => (InstanceDescr, PortLinks) -> [(PortInstDescr, PortInstDescr)]
instLinks (node, plinks) = 
    concatMap (\((_,o), _, links) -> mapMaybe (\(pnum, mpdescr) -> fmap (portFromNode ?r node o pnum,) mpdescr) links) 
              plinks

renderLink :: (?t::Topology,?r::Refine) => NodeMap -> (PortInstDescr, PortInstDescr) -> Maybe JSValue
renderLink nmap (srcport, dstport) = if (srcndname, srcpnum) < (dstndname,dstpnum)
                                        then Just $ JSObject $ toJSObject attrs
                                        else Nothing
    where dstnode = nodeFromPort ?r dstport
          srcnode = nodeFromPort ?r srcport
          srcndname = fromJust $ lookup srcnode nmap
          dstndname = fromJust $ lookup dstnode nmap
          dstpnum = phyPortNum ?t dstnode (pdescPort dstport) (fromInteger $ exprIVal $ last $ pdescKeys dstport)
          srcpnum = phyPortNum ?t srcnode (pdescPort srcport) (fromInteger $ exprIVal $ last $ pdescKeys srcport)
          attrs = [ ("src"     , JSString $ toJSString srcndname)
                  , ("srcport" , JSRational False $ fromIntegral $ srcpnum)
                  , ("dest"    , JSString $ toJSString dstndname)
                  , ("destport", JSRational False $ fromIntegral dstpnum)
                  , ("opts"    , JSObject $ toJSObject ([]::[(String, JSValue)]))]
