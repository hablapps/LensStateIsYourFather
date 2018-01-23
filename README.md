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

```Scala
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

```Scala
viewUpdate:   update(s)(view(s)) = s
updateView:   view(update(s)(a)) = a
updateUpdate: update(update(s)(a1))(a2) = update(s)(a2)
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

```Scala
trait MonadState[A, M[_]] extends Monad[M] {
  def get: M[A]
  def put: A => M[Unit]
}
```

As usual, this typeclass comes along with some properties that any instance
should satisfy. We show them here:

```Scala
getGet: get >>= (a1 => get >>= (a2 => point((a1, a2)))) =
        get >>= (a => point((a, a)))
getPut: get >>= put = point(())
putGet: put a >>= get = put a >>= point(a)
putPut: put a1 >> put a2 = put a2
```

_(*) Notice that `>>=` and `point` correspond with the `Monad` methods, which
are also known as `bind` and `return` in the folklore, respectively._

The most popular instance of this typeclass is `State`, which is just a state transformation that produces additional output `A`:

```Scala
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

```Scala
type MSLens[S, A] = MonadState[A, State[S, ?]]
```

In the next section, we will prove it right, both informally and formally.
Later, in the concluding section, we'll argue why this connection is important
to us.

## 2. Proof

Now, it's time for us to prove our claim! Remember, we want to assert that any
instance of `MonadState` with `State` is just a lens. Firstly, we'll do it
informally, old school style, though using a pseudo-scala notation. Then, we'll
formalise it with Coq. Since the proof would take too much writing, we'll just
show you a subpart of it, and we'll reference the rest of them.

### Informal Proof

So, where should we start? Well, we want to check that `MonadState[A, State[S, ?]]`
is just a lens. Thereby, it would be helpful if we could provide a function to
evidence that mapping:

```Scala
def ms_2_ln[S, A](ms: MonadState[A, State[S, ?]]): Lens[S, A] =
  Lens[S, A](
    view = s => evalState(get)(s),
    update = s => a => execState(put(a))(s))
```

where `execState` and `evalState` are just convenience methods to simplify the
implementation:

```Scala
def evalState[S, A](st: State[S, A])(s: S): A = st.runState(s)._1
def execState[S, A](st: State[S, A])(s: S): S = st.runState(s)._2
```

However, we can't guarantee right now that the result of an invocation to
`ms_2_ln` is a very well-behaved lens. In fact, we only know that this
implementation compiles nicely! Our mission here consists on proving that the
resulting lens is lawful. How can we state such an argument? Well, we don't
start from scratch here, we are aware that `MonadState` holds some laws that we
could use for this purpose.

Before we dive in, we're going to narrow the scope of the proof, to make things
simpler. Instead of showing the whole correspondence, we'll simply show the
following subproof: for any `State S` instance of `MonadState` where `putPut`
holds, we get a lens where `updateUpdate` holds. Here it's the proof:

```Scala
> [0. update(update(s)(a1))(a2) => update(s)(a2)]
  update(update(s)(a1))(a2)
= [1. def update]
  execState(put(a2))(execState(put(a1))(s))
= [2. Lemma execexec is >>]
  execState(put(a1) >> put(a2))(s)
= [3. putPut (MonadState)]
  execState(put(a2))(s)
= [4. def update]
  update(s)(a2)
◻
```

We start in *0* with an hypothesis `update(update(s)(a1))(a2)` and a goal
`update(s)(a2)`. Given all the information in the context, that is `MonadState`
laws and other information related to `State`, we should be able to reach that
goal. The step *1* simply unfolds the definition of `update` that we provided in
`ms_2_lens`. Now, in *2*, we assume a lemma *execexec is >>* (which we invite
you to prove) which manifests that sequencing executions of two programs is the
same as the single execution of the sequence of those programs. This leads to
the step *3* where we can apply *putPut* smoothly. Finally, we simply apply the
definition of `update` again in *4*, but this time in a reversed way, to reach
our desired goal. We're done here!

You can find the whole informal proof [here](LensStateIsYourFatherProof.md).
Please, notice that this linked version uses pseudo-haskell notation, which is
more standard in computer science publications.

### Coq Proof

```Coq
Record lens (S A : Type) := mkLens
{ view : S -> A
; update : S -> A -> S
}.
```

```Coq
Definition view_update {S A : Type} (ln : lens S A) : Prop :=
  forall s, update _ _ ln s (view _ _ ln s) = s.

Definition update_view {S A : Type} (ln : lens S A) : Prop :=
  forall s a, view _ _ ln (update _ _ ln s a) = a.

Definition update_update {S A : Type} (ln : lens S A) : Prop :=
  forall s a1 a2, update _ _ ln (update _ _ ln s a1) a2 = update _ _ ln s a2.

Definition very_well_behaved {S A : Type} (ln : lens S A) : Prop :=
  view_update ln /\ update_view ln /\ update_update ln.
```

```Coq
Class MonadState (A : Type) (m : Type -> Type) `{Monad m} : Type :=
{ get : m A
; put : A -> m unit
}.
```

```Coq
Class MonadStateLaws (A : Type) (m : Type -> Type) `{MonadState A m} : Type :=
{ get_get : get >>= (fun s1 => get >>= (fun s2 => ret (s1, s2))) =
            get >>= (fun s => ret (s, s))
; get_put : get >>= put = ret tt
; put_get : forall s, put s >> get = put s >> ret s
; put_put : forall s1 s2, put s1 >> put s2 = put s2
}.
```

```Coq
Record state (S A : Type) := mkState
{ runState : S -> A * S }.
```

```Coq
Definition ms_2_lens {S A : Type} (ms : MonadState A (state S)) : lens S A :=
{| view s := evalState get s
;  update s a := execState (put a) s
|}.
```

```Coq
Theorem lens_state_is_your_father_forward :
    forall {S A : Type} (ms : MonadState A (state S)),
    @MonadStateLaws A (state S) _ ms -> very_well_behaved (ms_2_lens ms).
Proof.
  ...
  unfold ms_2_lens.
  ...
  - (* update_update *)
    rewrite -> execexec_is_gtgt.
    now rewrite -> pp.
Qed.
```

You can find the sources associated to the formal proof
[here](LensStateIsYourFatherProof.v).

## 3. Conclusions

Stateless paragraph

Coq paragraph
