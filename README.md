# lean-profunctors

A very incomplete port of the Haskell [profunctors package](https://hackage.haskell.org/package/profunctors)
to Lean 4.

Contributions are welcome!

## Credit

Credit (without liability!) is due to [Edward Kmett](https://github.com/ekmett) and [Ryan Scott](https://github.com/RyanGlScott)
for creating and maintaining the [original Haskell package](https://hackage.haskell.org/package/profunctors) this library is based on.

Additionally, the idea of the `lensE` and `prismE` methods of `Strong` and `Choice` respectively are owed to [Oleg Grenrus](https://github.com/phadej)'s [blog post](https://oleg.fi/gists/posts/2017-04-18-glassery.html) and [David Feuer](https://github.com/treeowl)'s [GitHub issue for the profunctors package](https://github.com/ekmett/profunctors/issues/47).

## Why make this?

To be honest, I forgot that Lean's dependent types would kill any chance of type inference for optics Just Working™ and wanted to play
around with the idea of making a profunctor optics library.

Maybe it's possible to hack together with some clever use of metaprogramming,
but it'd take me a long time to get to that level of proficiency with the language. Instead of throwing this away or keeping it hidden,
I figure it's best to go ahead and make it a standalone library so people can play with it.

## To-Do List

- [ ] Yoneda
- [ ] Coyoneda
- [ ] Indexed Profunctors
