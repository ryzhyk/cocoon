# Cocoon: Correct by Construction Networking 

Cocoon (for Correct by Construction Networking), is an SDN programming language 
designed around the idea of iterative refinement.  The 
network programmer starts with a high-level description of the 
desired network behavior, focusing on the service the network 
should provide to each packet, as opposed to how this service is 
implemented within the network fabric.  The programmer then 
iteratively refines the top-level specification, adding details of 
the topology, routing, fault recovery, etc., until reaching a 
level of detail sufficient for the Cocoon compiler to generate an 
SDN application that manages network switches via the southbound 
interface (we currently support P4).  
