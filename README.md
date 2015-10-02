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

# What is this all about?

It's the same thing as Edward A. Kmett's [`recursion-schemes`](https://github.com/ekmett/recursion-schemes),
only more general and less practical. The problem is that `Functor`s
(`Bifunctor`s etc.) in Haskell sense of the word are not closed under `fix`.
Not to mention the fact that it's not clear how to generalize to arbitrary
arities, apart from going the "no one's going to need a 15-tuple" route.
Mutual recursion also presents some problems.

I mused about this idly [on reddit](https://www.reddit.com/r/haskell/comments/3dcidp/the_evolution_of_a_haskell_programmer/ct3yvr9?context=3),
when SUDDENLY, [Conor McBride](https://github.com/pigworker) showed up and
pointed me towards his slides. I also found the unfinished
[Slicing It!](https://personal.cis.strath.ac.uk/conor.mcbride/pub/SlicingIt/SlicingIt.pdf)
of his. All of that was more than a little mind-boggling and seemed to require
non-standard extensions I've never even heard of before.

Further research led me to [Generic Programming with Indexed Functors](http://dreixel.net/research/pdf/gpif.pdf)
by [Andres Löh](https://github.com/kosmikus) and [José Pedro Magalhães](https://github.com/dreixel)
(see [also](https://github.com/kosmikus/indexed)). That was in Agda, though,
which has a strictly more powerful type system than Haskell, and which I'm
not particularly familiar with.

Anyway, I tinkered with *GPIF* and Idris a bit, time passed, and meanwhile,
[nponeccop](https://github.com/nponeccop) suggested to me that `DataKinds` do
the same thing as the relevant SHE features. Unsurprisingly, I later found
out that McBride earlier suggested using `DataKinds` for these purposes
somewhere on SO as well.

But nothing that would qualify as even a remotely complete implementation
appeared to be available in Haskell. So I decided to suck it up and follow
the combination of *Slicing It!* and *GPIF* program spiced up by `DataKinds`
myself. This is the end result.

The generality of this fascinates me. It also works quite well in simple
cases. Conversions between host types and indexed functors can be encoded
very neatly using the generic cata- and anamorphisms. Concrete maps and
recursion schemes fall out of it simply by specifying the right types and
letting the isomorphisms do the work.

Nevertheless, it's not very practical even in those simple cases. It's
just less work to write the recursion schemes needed from scratch. And the
going gets much, *much* tougher when we get to mutually recursive types,
as `EvenOdd` here illustrates...

So, this isn't intended for any kind (pardon the pun) of practical use,
but I think that the insight into the nature of (mind fail -- algebraic
data types? indexed functors? recursion schemes? all of the above? I don't
really know how to put this down concisely) was entirely worth the trouble.

