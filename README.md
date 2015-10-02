# "Free" (Co)Recursion Schemes Using Indexed Functors & DataKinds

To install and tinker:

    cd your-scratch-directory
    mkdir gpif-datakinds
    cd gpif-datakinds
    cabal sandbox init
    git clone git@github.com:pbl64k/gpif-datakinds.git
    cabal install gpif-datakinds/gpif-datakinds.cabal

`Control.IxFunctor.Examples.Examples` contains a few really sketchy examples,
`Control.IxFunctor` will import most of the stuff you need if you want to
tinker with your own data types, while `Control.IxFunctor.Nat`,
`Control.IxFunctor.List`, `Control.IxFunctor.Rose` and
`Control.IxFunctor.EvenOdd` contain sample definitions, isomorphisms and
concrete maps/recursion schemes for corresponding data types.

To generate some documentation of questionable utility:

    mkdir docs
    haddock -h -o docs/ `find gpif-datakinds/src/ -name '*.hs'`

Note that `haddock` seems to get a little confused by all of the extensions
this library is using, so some signatures look quite nonsensical. When in
doubt, look in the sources.

