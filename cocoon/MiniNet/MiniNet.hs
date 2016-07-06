{-
Copyrights (c) 2016. Samsung Electronics Ltd. All right reserved. 

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-}
{-# LANGUAGE ImplicitParams, TupleSections #-}

module MiniNet.MiniNet (generateMininetTopology, NodeMap) where

import Text.JSON
import Data.Maybe
import Control.Monad.State
import Data.List
import Numeric

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
          width = (maximum $ map (length . (uncurry instMapFlatten)) topology) * hstep
          -- render nodes
          (sws, hs, nmap) = execState (mapIdxM (renderNodes width) topology) ([],[],[])
          -- render links
          links = let ?r = r in
                  let ?t = topology in
                  mapMaybe (renderLink nmap) $ topologyLinks topology
          attrs = [ ("controllers", JSArray [])
                  , ("hosts"      , JSArray hs)
                  , ("switches"   , JSArray sws)
                  , ("links"      , JSArray links)
                  , ("version"    , JSRational False 2)
                  ]
          

renderNodes :: Int -> (Node, InstanceMap PortLinks) -> Int -> State (Switches, Hosts, NodeMap) ()
renderNodes w (n, imap) voffset = do 
    let nodes = instMapFlatten n imap
        offset = (w `div` length nodes) `div` 2
        step = w `div` length nodes
        nodeoff = mapIdx (\nd i -> (nd, offset + i * step)) nodes
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
               if (nodeType node == NodeHost) && (not $ null $ idescKeys descr)
                  then case head $ idescKeys descr of
                            e@(EStruct _ _ _) -> [("ip4", JSString $ toJSString $ formatIP e)] 
                            (EInt _ 48 m)     -> [("mac", JSString $ toJSString $ formatMAC m)] ++
                                                 if length (idescKeys descr) >= 2
                                                    then case idescKeys descr !! 1 of
                                                              e@(EStruct _ _ _) -> [("ip4", JSString $ toJSString $ formatIP e)] 
                                                              _                 -> []
                                                    else []
                            _                 -> []
                  else []                  
        attrs = [ ("number", JSString $ toJSString $ show number)
                , ("opts"  , JSObject $ toJSObject opts)
                , ("x"     , JSString $ toJSString $ show $ hoffset)
                , ("y"     , JSString $ toJSString $ show $ (voffset + 1) * vstep)]
        n = JSObject $ toJSObject attrs 
        nmap' = (descr, ndname):nmap
    put $ if' (nodeType node == NodeSwitch) ((n:sws), hs, nmap') (sws, (n:hs), nmap')

formatIP :: Expr -> String
formatIP (EStruct _ _ fs) = intercalate "." $ map (show . exprIVal) fs
formatIP e                = error $ "MiniNet.formatIP " ++ show e

formatMAC :: Integer -> String
formatMAC i = 
    ( showHex b0 . colon . showHex b1 . colon . showHex b2 . colon
    . showHex b3 . colon . showHex b4 . colon . showHex b5) ""
  where colon = showString ":"
        b5 = bitSlice i 7 0
        b4 = bitSlice i 15 8
        b3 = bitSlice i 23 16
        b2 = bitSlice i 31 24
        b1 = bitSlice i 39 32
        b0 = bitSlice i 47 40

renderLink :: (?t::Topology,?r::Refine) => NodeMap -> (PortInstDescr, PortInstDescr) -> Maybe JSValue
renderLink nmap (srcport, dstport) = if isPort ?r $ pdescPort dstport
                                        then if (srcndname, srcpnum) < (dstndname,dstpnum)
                                                then Just $ JSObject $ toJSObject attrs
                                                else Nothing
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
