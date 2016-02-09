{-# LANGUAGE ImplicitParams #-}

module MiniNet.MiniNet () where

import Text.JSON
import Data.Maybe
import Control.Monad.State

import Topology
import Util
import Syntax
import Eval
import NS
import Name

hstep = 80
vstep = 80

type Switches = [JSValue]
type Hosts    = [JSValue]
type Links    = [JSValue]
type NodeMap  = [(InstanceDescr, String)]

generateMininetTopology :: Refine -> Topology -> String
generateMininetTopology r topology = encode $ toJSObject attrs
    where -- max number of nodes in a layer
          width = maximum $ map (length . flatten . snd) topology
          -- render nodes
          (sws, hs, nmap) = execState (mapIdxM (renderNodes r width) topology) ([],[],[])
          -- render links
          links = let ?r = r in
                  let ?t = topology in
                  concatMap (\(n, imap) -> concatMap (\(keys, plinks) -> renderLinks nmap (InstanceDescr n keys) plinks) $ flatten imap) topology
          attrs = [ ("controllers", JSArray [])
                  , ("hosts"      , JSArray hs)
                  , ("sws"        , JSArray sws)
                  , ("links"      , JSArray links)
                  ]
          
renderNodes :: Refine -> Int -> (String, InstanceMap) -> Int -> State (Switches, Hosts, NodeMap) ()
renderNodes r w (n, imap) voffset = do 
    let nodes = flatten imap
        offset = (w - length nodes) `div` 2
        nodeoff = zip nodes [offset..]
    mapM_ (renderNode voffset (getNode r n)) nodeoff

flatten :: InstanceMap -> [([Expr], PortLinks)]
flatten (InstanceMap (Left insts))  = concatMap (\(k, imap) -> map (\(keys, links) -> (k:keys, links)) $ flatten imap) insts
flatten (InstanceMap (Right links)) = [([], links)]

renderNode :: Int -> Node -> (([Expr], PortLinks), Int) -> State (Switches, Hosts, NodeMap) ()
renderNode voffset node ((keys, links), hoffset) = do
    (sws, hs, nmap) <- get
    let (letter, number) = if' (nodeType node == NodeSwitch) ("s", length sws) ("h", length hs)
        ndname = letter ++ show number
        opts = [ ("controllers", JSArray [])
               , ("hostname"   , JSString $ toJSString ndname) 
               , ("nodeNum"    , JSRational False $ fromIntegral number)
               , ("switchType" , JSString $ toJSString "bmv2")]
        attrs = [ ("number", JSRational False $ fromIntegral number)
                , ("opts"  , JSObject $ toJSObject opts)
                , ("x"     , JSRational False $ fromIntegral $ hoffset * hstep)
                , ("y"     , JSRational False $ fromIntegral $ voffset * vstep)]
        n = JSObject $ toJSObject attrs 
        nmap' = (InstanceDescr (name node) keys, ndname):nmap
    put $ if' (nodeType node == NodeSwitch) ((n:sws), hs, nmap') (sws, (n:hs), nmap')

renderLinks :: (?t::Topology,?r::Refine) => NodeMap -> InstanceDescr -> PortLinks -> Links
renderLinks nmap node plinks = 
    concatMap (\((_,o), (base,_), links) -> mapMaybe (renderLink nmap node base) links) plinks

renderLink :: (?t::Topology,?r::Refine) => NodeMap -> InstanceDescr -> Int -> (Int, Maybe PortInstDescr) -> Maybe JSValue
renderLink nmap srcnode srcprtbase (srcportnum, Just dstportinst@(PortInstDescr dstpname dstkeys)) = Just $ JSObject $ toJSObject attrs
    where dstnode = nodeFromPort ?r ?t dstportinst
          dstpnum = phyPortNum ?t dstnode dstpname (fromInteger $ exprIVal $ last dstkeys)
          attrs = [ ("src"     , JSString $ toJSString $ fromJust $ lookup srcnode nmap)
                  , ("srcport" , JSRational False $ fromIntegral $ srcportnum + srcprtbase)
                  , ("dest"    , JSString $ toJSString $ fromJust $ lookup dstnode nmap)
                  , ("destport", JSRational False $ fromIntegral dstpnum)
                  , ("opts"    , JSObject $ toJSObject ([]::[(String, JSValue)]))]
renderLink _ _ _ _ = Nothing
