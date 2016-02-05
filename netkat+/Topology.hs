-- Managing physical network topology induced by a NetKAT+ spec

module Topology () where

-- Multidimensional array of switch instances.  Each dimension corresponds to a 
-- key.  Innermost elements enumerate ports of an instance.
type InstanceMap = Either [(Expr, InstanceMap)] PortMap

-- Input-output port pair; a list of port indices and remote ports they are 
-- connected to.
type PortMap = [((String, String), [(Int, Maybe PortDescr)])]

-- Switch instance descriptor
data InstanceDescr = InstanceDescr String [Expr] 

-- Port instance descriptor
data PortDescr = PortDescr InstanceDescr String Int

data Topology = [(String, InstanceMap)]
