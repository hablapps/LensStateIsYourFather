# Lens, State is your father... and I can prove it!

About a year ago, we published ["Lens, State Is Your
Father"](https://blog.hablapps.com/2016/11/10/lens-state-is-your-father/) in
this blog. It led us to [our first contribution to
Monocle](https://github.com/julien-truffaut/Monocle/pull/415) and sowed the
seeds of [Stateless](https://github.com/hablapps/stateless), the Scala library
that we are currently working on. The post left some questions opened, which
we'll try to address today. Particularly, we have set two goals:

* Proving the major claim from the original post: an instance of `MonadState` with `State[S, ?]` and `A` as type arguments has a direct correspondence with a `Lens[S, A]`.
* Contextualizing the relevance of a proof assistant like [Coq](https://coq.inria.fr/) in functional programming.

**It doesn't matter if you haven't read the previous post**, we'll help you to
catch up with a brief recapitulation. Let's go for it!

## 1. Recap

In the aforementioned post, we claimed the existence of some connections between
lenses and the state monad. So, first of all, we'll introduce these elements.

A lens is just a pair of methods packed together, one of them to *get* a part
from a bigger whole and another one to *put* a new version of the part in an old
whole, returning a new whole. We, as programmers, are very familiar with those
methods, since they correspond with the notion of *getter* and *setter*,
respectively. However, to avoid name conflicts with other definitions, we'll
refer to them as `view` and `update`. We can encode a lens in Scala as follows:

```scala
case class Lens[S, A](
  view: S => A,
  update: S => A => S)
```

_(*) Notice that the "whole" data structure is represented with an `S`, while the
"part" is represented with an `A`._

Lenses are extremely useful to update [nested data
structures](http://julien-truffaut.github.io/Monocle/optics/lens.html), but we
won't go further down that road today. Instead, we'll focus on the properties
that a lens must hold to be considered very well-behaved:

```scala
viewUpdate:   update(s)(view(s)) = s
updateView:   view(update(s)(a)) = a
updateUpdate: update(update(s)(a1))(a2) == update(s)(a2)
```

So, a very well-behaved lens is any instance of `Lens` whose `view` and `update`
methods are compliant with the previous laws.

On the other hand, there is `MonadState`. It's a [widespread
typeclass](http://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/utp-monads.pdf)
that classifies all those effects which are able to access and manipulate an
inner state. To do so, this typeclass contains a pair of methods, the first of
them to get the current state and the second one to replace it with a new
version. We'll be using the terms *get* and *put* to refer to these new methods.
Having said so, this is how we encode this typeclass in Scala (where `A`
corresponds with the type of the inner state):

```scala
trait MonadState[A, M[_]] extends Monad[M] {
  def get: M[A]
  def put: A => M[Unit]
}
```

As usual, this typeclass comes along with some properties that any instance
should satisfy. We show them here:

```scala
getGet: get >>= (a1 => get >>= (a2 => point((a1, a2)))) =
        get >>= (a => point((a, a)))
getPut: get >>= put = point(())
putGet: put a >>= get = put a >>= point(a)
putPut: put a1 >> put a2 = put a2
```

_(*) Notice that `>>=` and `point` correspond with the `Monad` methods, which
are also known as `bind` and `return`, respectively._

The most popular instance of this typeclass is `State`, which is just a state transformation that produces additional output `A`:

```scala
case class State[S, A](runState: S => (A, S))

def stateMonadState[S] = new MonadState[S, State[S, ?]] {
  def get = State(s => (s, s))
  def put = s => State(_ => ((), s))
}
```

Now, we have all the ingredients to state our claim. In fact, you might have
noticed that `Lens` and `MonadState` show a high degree of similarity, which
embraces not only their methods but also their associated laws. However, they're
quite different beasts: lenses deal with immutable data structures while
`MonadState` handles monadic effects. In the original post, we were surprised to
find out that `MonadState` generalises a lens. Indeed, we suggested that
instantiating `MonadState` sith `State` is just an alternative way of
representing a lens:

```scala
type MSLens[S, A] = MonadState[A, State[S, ?]]
```

In the next section, we will prove it right, both informally and formally. We'll
state why this connection is important to us in the concluding section.

## 2. Proof

### Informal Proof

### Coq Proof

## 3. Conclusions

Stateless paragraph

Coq paragraph
