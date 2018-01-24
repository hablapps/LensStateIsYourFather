# Lens, State is your father... and I can prove it!

About a year ago, we published ["Lens, State Is Your
Father"](https://blog.hablapps.com/2016/11/10/lens-state-is-your-father/) in
this blog. It led us to [our first contribution to
Monocle](https://github.com/julien-truffaut/Monocle/pull/415) and sowed the
seeds of [Stateless](https://github.com/hablapps/stateless), the Scala library
that we are currently working on. The post left some questions opened, which
we'll try to address today. Particularly, we have set two goals:

* Proving the major claim from the original post: `MonadState[A, State[S, ?]]` is yet another `Lens[S, A]` definition (besides concrete, van laarhoven, [profunctor](https://github.com/hablapps/DontFearTheProfunctorOptics), etc.).
* Contextualizing the relevance of a proof assistant like [Coq](https://coq.inria.fr/) in functional programming.

**It doesn't matter if you haven't read the previous post**, we'll help you to
catch up with a brief recap. Let's go for it!

## 1. Recap

In the aforementioned post, we showed some connections between *lens* and *state
monad*. So, first of all, we'll introduce these elements separately. Then, we'll
bring those connections back.

A lens is just a pair of methods packed together, one of them to *get* a part
from a bigger whole and another one to *put* a new version of the part in an old
whole, returning a new whole. We, as programmers, are very familiar with those
methods, since they correspond with the notions of *getter* and *setter*,
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
that a lens must hold to be considered [very
well-behaved](http://sebfisch.github.io/research/pub/Fischer+MPC15.pdf):

```Scala
law viewUpdate:   update(s)(view(s)) = s
law updateView:   view(update(s)(a)) = a
law updateUpdate: update(update(s)(a1))(a2) = update(s)(a2)
```

So, a very well-behaved lens is any instance of `Lens` whose `view` and `update`
methods are compliant with the previous laws.

On the other hand, there is `MonadState`. It's a [widespread
typeclass](http://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/utp-monads.pdf)
that classifies all those effects which are able to access and manipulate an
inner state which in turn, might be contextualized within a bigger one.
`MonadState` supplies a pair of methods, the first of them to get the current
inner state and the second one to replace it with another one, taken as
argument. We'll be using the terms *get* and *put* to refer to these methods.
Having said so, this is how we encode this typeclass in Scala:

```Scala
trait MonadState[A, M[_]] extends Monad[M] {
  def get: M[A]
  def put: A => M[Unit]
}
```

As we can see, `A` refers to the inner state and the effect `M` provides the way
to access and manipulate it. Whether `A` roles the whole state or it's just a
part of it, it's something that is hidden by `M`, beyond our vision at this
point.

As usual, this typeclass comes along with some laws that any instance should
satisfy. We show them here:

```Scala
law getGet: get >>= (a1 => get >>= (a2 => point((a1, a2)))) =
            get >>= (a => point((a, a)))
law getPut: get >>= put = point(())
law putGet: put a >>= get = put a >>= point(a)
law putPut: put a1 >> put a2 = put a2
```

_(*) Notice that `>>=` and `point` are the `Monad` methods, which are also known
as `bind` and `return`, respectively._

The most popular instance of this typeclass is `MonadState[S, State[S, ?]]`,
which is just a state transformation that also produces an additional output
`Out`. In this particular case, the state `S` hidden by `State[S, ?]` is exactly
the same as the one we are providing access to via `MonadState`, I mean, the
inner state corresponds to the whole state:

```Scala
case class State[S, Out](runState: S => (Out, S))

def stateMonadState[S] = new MonadState[S, State[S, ?]] {
  def get = State(s => (s, s))
  def put = s => State(_ => ((), s))
}
```

These are convenience methods for `State` that we'll be using in the upcoming
definitions:

```Scala
def evalState[S, A](st: State[S, A])(s: S): A = st.runState(s)._1
def execState[S, A](st: State[S, A])(s: S): S = st.runState(s)._2
```

Now, we have collected all the ingredients to state our claim. Perhaps, you
might have noticed that `Lens` and `MonadState` show a high degree of
similarity, which embraces not only their methods (view-get, update-put) but
also their associated laws (viewUpdate-getPut, updateUpdate-putPut, etc.).
However, they're quite different beasts: lenses deal with immutable data
structures while `MonadState` handles monadic effects. In the original post, we
related them by suggesting that `MonadState` generalizes `Lens`. Particularly,
we claimed that any `State` instance of `MonadState` is just an alternative way
of representing a lens:

```Scala
type MSLens[S, A] = MonadState[A, State[S, ?]]
```

_(*) Notice, that `MonadState[A, State[S, ?]]` differs from the instance we
showed above, since the state `S` hidden by `State[S, ?]` is not the same as the
focus `A` that we are providing access to via `MonadState`._

The equivalence is manifested by the following isomorphism:

```Scala
// forward arrow
def ms_2_ln[S, A](ms: MSLens[S, A]): Lens[S, A] =
  Lens[S, A](
    view = s => evalState(get)(s),
    update = s => a => execState(put(a))(s))

// backward arrow
def ln_2_ms[S, A](ln: Lens[S, A]): MSLens[S, A] =
  new MonadState[A, State[S, ?]] {
    def get = State(s => (ln.view(s), s))
    def put = a => State(s => ((), ln.update(s)(a)))
  }
```

Right now, we can't guarantee that the result of an invocation to `ms_2_ln`
yields a very well-behaved lens. Indeed, the only fact that we can say about
this definition is that it compiles (and that's saying a lot). Thereby, our
mission consists on proving that the resulting lens is lawful. We'll do so in
the next section. Later, in the concluding section, we'll argue why this proof
is so important to us.

## 2. Proof of Paternity

If we want to show that ~~`State`~~ `MonadState` is the parent of `Lens`, we're
gonna need proofs. Firstly, we'll do it informally, old school style (though
using a pseudo-scala notation). Then, we'll formalize the same idea using Coq.
Since the proof would take too much writing, we'll just show you a subpart of
it, and we'll link the rest of them, just in case you are interested.

### Informal Proof

Fortunately, we don't have to start from scratch to prove that our isomorphism
is correct, we know that `MonadState` has some laws that we could exploit for
this purpose. Prior to that, we're going to narrow the scope of the proof, to
make things simpler. Instead of showing the whole correspondence, we'll simply
show the following subproof of the forward function:

```Coq
∀ ms ∈ MSLens[S, A], putPut ms -> updateUpdate (ms_2_ln ms)
```

that we can read as: "for any `ms` of type `MSLens[S, A]` (or `MonadState[A,
State[S, ?]]`) where `putPut` holds, then passing `ms` through `ms_2_ln` must
return a lens where `updateUpdate` holds". Here it's the informal proof:

```Scala
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

We start in with the hypothesis `update(update(s)(a1))(a2)`, being our goal
`update(s)(a2)`. Given all the information in the context, that is `MonadState`
laws and other information related to `State`, we should be able to reach that
goal. Step *1* simply unfolds the definition of `update` that we provided in
`ms_2_lens`. Now, in *2*, we assume a lemma *execexec is >>* (which we invite
you to prove) which manifests that sequencing executions of different stateful
programs is the same as the single execution of the sequence of those programs.
This leads to step *3* where we can apply *putPut* smoothly. Finally, we apply
the definition of `update` again (step *4*), but this time in a reversed way, to
reach our desired goal. Seems that we're done here!

You can find the whole informal forward proof
[here](LensStateIsYourFatherProof.md). Please, notice that this linked version
uses pseudo-haskell notation, which is more standard in computer science
publications.

### Coq Proof

I'm sure you've heard that [Coq](https://coq.inria.fr/) is a proof assistant
but, did you know that it's also a purely functional language? A very nice one
indeed, which is equipped with dependent types features. As in Scala, it's
possible to define a lens using Coq:

```Coq
Record lens (S A : Type) := mkLens
{ view : S -> A
; update : S -> A -> S
}.
```

Now, we're going to encode *putPut* in Coq. Of course, you don't have to
understand everything, I just want you to see that this definitions takes a lens
as parameter and returns a law (or *proposition*) over it:

```Coq
Definition update_update {S A : Type} (ln : lens S A) : Prop :=
  forall s a1 a2, update _ _ ln (update _ _ ln s a1) a2 = update _ _ ln s a2.
```

Now, we can read `update_update ln` as a proposition where we postulate that
update_update` holds for `ln`.

Being a functional language as it is, Coq also enables typeclass definitions.
This is how we represent `MonadState`. I invite you to come back to the Scala
definition to spot the differences between them:

```Coq
Class MonadState (A : Type) (m : Type -> Type) `{Monad m} : Type :=
{ get : m A
; put : A -> m unit
}.
```

What comes next is quite interesting. We encode the laws of a typeclass in
another class that depends on the original one. In this sense, when we create a
new typeclass instance, we should provide not only an instance of the main class
but also an instance of its associated laws, where we prove that the laws of the
main instance hold. Having said so, this is how we encode `MonadStateLaws` in
Coq:

```Coq
Class MonadStateLaws (A : Type) (m : Type -> Type) `{MonadState A m} : Type :=
{ get_get : get >>= (fun s1 => get >>= (fun s2 => ret (s1, s2))) =
            get >>= (fun s => ret (s, s))
; get_put : get >>= put = ret tt
; put_get : forall s, put s >> get = put s >> ret s
; put_put : forall s1 s2, put s1 >> put s2 = put s2
}.
```

The previous definition is rather strange. Usually, a method signature contains
types exclusively, but `MonadStateLaws` methods include expressions in it! This
is a nice consequence of having dependent types, which are just types that
depend on plain values. In fact, the dependent type that we find here is `=`,
which depends on two values: the left hand side expression and the right hand
side expression of the particular equation (or law) that we want to declare.

Now, defining `state` turns out to be straightforward:

```Coq
Record state (S A : Type) := mkState
{ runState : S -> A * S }.
```

Once we have defined the main structures, we can translate the function that
maps any `MonadState A (state S)` into a `lens S A`, which we'll use in our
proof.

```Coq
Definition ms_2_lens {S A : Type} (ms : MonadState A (state S)) : lens S A :=
{| view s := evalState get s
;  update s a := execState (put a) s
|}.
```

And finally here it's the formal proof:

```Coq
Theorem putput_leads_to_updateupdate :
    forall {S A : Type} (ms : MonadState A (state S)),
    (forall a1 a2, put a1 >> put a2 = put a2) -> update_update (ms_2_lens ms).
Proof.
  intros.
  rename H into putPut.
  unfold update_update.
  unfold ms_2_lens.
  simpl.
  intros.
  rewrite -> execexec_is_gtgt.
  now rewrite -> putPut.
Qed.
```

Reading the header of the proof (from `Theorem` to `Proof`) should be
straightforward at this point. After `Proof` we use the *tactics* language to
prove such a proposition. Again, you don't have to understand everything, but
you could find some analogous elements from the informal proof. Particularly,
the `unfold` is quite similar to the expansion of definitions (step *1* in the
informal proof), `rewrite -> execexec_is_gtgt` corresponds directly to the lemma
in step *2* and `rewrite -> putPut` is exactly the step *3*. The final `Qed`
(*quod erat demonstrandum*) evidences the positive Dna test result that we were
searching for. As a consequence, we can conclude that `MonadState` is actually
the father of `Lens`. ;)

You can find the sources associated to the formal proof
[here](LensStateIsYourFatherProof.v).

## 3. Further Insights and Conclusions

Ok, I buy it, `MonadState A (state S)` is a `lens S A`. *So what?* As I said
previously, "Lens, State Is Your Father" was the starting point of
[*Stateless*](https://github.com/hablapps/stateless), a library that we are
currently working on. In this library, we try to take optics (lens, optional,
traversal, etc.) [beyond immutable data
structures](https://skillsmatter.com/skillscasts/11214-llghtning-talk-optic-algebras-beyond-immutable-data-structures).
Particularly, we want to take the algebra and design patterns from optics to
more realistic settings, such as databases or microservices, since indeed it's
not practical to keep the whole state of a modern application in memory.
`MonadState`, distilling the algebraic essence of a lens, opens up these new
possibilities, including, but not restricted to immutable data structures. In
fact, we could say that `MonadState` is the father of many children, siblings of
lens, which are about to be discovered in future posts. As a final note, we must
say that we haven't found this connection between `MonadState` and `Lens`
elsewhere, but it seems to be evident [on previous
work](http://www.cs.ox.ac.uk/jeremy.gibbons/publications/mlenses.pdf).

We've found it essential to prove that the foundations of Stateless are solid.
However, it was becoming quite annoying to do this task, as proofs were becoming
more complex. This situation inevitably led us to leap of faiths, you know,
everything compiles with pen and paper. That's why we decided to jump into a
proof assistant. Honestly, learning Coq will blow your mind, because it's such a
different beast (although [exactly the
same](https://softwarefoundations.cis.upenn.edu/lf-current/ProofObjects.html) at
the end), but you start to be more confident after one fully immersed week (I
recommend to follow [the dark arrow
itinerary](https://softwarefoundations.cis.upenn.edu/lf-current/deps.html) from
*Logical Foundations*). In my case, it was totally worth it, since there's no
room for leap of faiths any more.

Proof assistants are the natural step towards more reliable systems. Given the
nowadays society needs, unit testing is becoming completely obsolete. In this
regard, property based testing is a nice alternative, but we can do better. If
we can prove our software, there's no need for additional tests. It's correct.
Period. Proof assistants are still very academic and they're not necessarily
focused on functional programming, but dependent type languages like Idris are
starting to emerge and [they enable such
capabilities](http://docs.idris-lang.org/en/latest/tutorial/theorems.html). And
here's a new claim that I hope to "prove" in the future: they're here to stay!
