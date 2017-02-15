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

# Installation

Install the [Haskell Platform](https://www.haskell.org/platform/).
Note: on Ubuntu 15.10 or older, use generic Linux
instructions instead of Ubuntu-specific instructions to get an
up-to-date version of Haskell compiler and packages.

Update Haskell package list:
~~~
cabal update
~~~

Download and compile Cocoon:
~~~
git clone git@github.com:ryzhyk/cocoon.git
cd cocoon/cocoon
cabal install --only-dependencies 
cabal configure
cabal build
~~~

Install [Z3](https://github.com/Z3Prover/z3)

Download and compile [Corral](https://github.com/boogie-org/corral). (This requires
mono on Linux; install it, e.g., with `sudo apt-get install mono-complete`)

Add `corral.exe` to your `$PATH`.

To test the Cocoon verifier, run `test_verification.sh` script in the
top directory.
