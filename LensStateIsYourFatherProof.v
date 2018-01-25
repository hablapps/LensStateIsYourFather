(***********************************************)
(* LENS, STATE IS YOUR FATHER, I CAN PROVE IT! *)
(***********************************************)

Axiom functional_extensionality : forall {X Y: Type}
                                         {f g : X -> Y},
  (forall (x : X), f x = g x) -> f = g.


(************)
(** * Monad *)
(************)

(* Definition and aliases *)

Class Monad (m : Type -> Type) : Type :=
{ ret : forall {A : Type}, A -> m A
; bind : forall {A B : Type}, m A -> (A -> m B) -> m B
}.

Notation "aM >>= f" := (bind aM f) (at level 50, left associativity).

Notation "aM >> bM" := (aM >>= fun _ => bM) (at level 50, left associativity).

(* Laws *)

Class MonadLaws (m : Type -> Type) {H : Monad m} : Type :=
{ left_id : forall {A B : Type} (a : A) (f : A -> m B), ret a >>= f = f a
; right_id : forall {A : Type} (aM : m A), aM >>= ret = aM
; assoc : forall {A B C : Type} (aM : m A) (f : A -> m B) (g : B -> m C),
          aM >>= f >>= g = aM >>= (fun x => f x >>= g)
}.


(*****************)
(** * MonadState *)
(*****************)

(* Definition and aliases *)

Class MonadState (A : Type) (m : Type -> Type) `{Monad m} : Type :=
{ get : m A
; put : A -> m unit
}.

(* Laws *)

Class MonadStateLaws (A : Type) (m : Type -> Type) `{MonadState A m} : Type :=
{ get_get : get >>= (fun s1 => get >>= (fun s2 => ret (s1, s2))) =
            get >>= (fun s => ret (s, s))
; get_put : get >>= put = ret tt
; put_get : forall s, put s >> get = put s >> ret s
; put_put : forall s1 s2, put s1 >> put s2 = put s2
}.

(* Theorems *)

Axiom general_putput : forall {M : Type -> Type} {A : Type}
  `{MonadStateLaws A M} {X : Type} (p : A * A -> M X),
  get >>= (fun x1 => get >>= (fun x2 => p (x1, x2))) = get >>= (fun x1 => p (x1, x1)).

Theorem non_eff_get : forall {M : Type -> Type} {A : Type}
    `{msd : MonadStateLaws A M} {md : MonadLaws M} {X : Type} (p : M X),
    get >> p = p.
Proof.
  intros.
  pose proof (@general_putput M A H H0 msd) as F.
  destruct md as [li ri ass].
  assert (G : forall {X} (mx : M X), mx = ret tt >> mx).
  { intros. now rewrite -> li. }
  destruct msd as [gg gp pg pp].
  rewrite -> (G X p).
  rewrite <- gp.
  repeat rewrite -> ass.
  now rewrite -> (F X (fun pair => put (snd pair) >> p)).
Qed.


(******************)
(** * State Monad *)
(******************)

(* Data type and definitions *)

Record state (S A : Type) := mkState
{ runState : S -> A * S }.
Arguments mkState [S A].
Arguments runState [S A].

Definition evalState {S A : Type} (st : state S A) (s : S) : A :=
  fst (runState st s).

Definition execState {S A : Type} (st : state S A) (s : S) : S :=
  snd (runState st s).

(* Typeclass instances *)

Instance Monad_state {S : Type} : Monad (state S) :=
{ ret := fun A a => mkState (fun s => (a, s))
; bind := fun A B m f => mkState (fun s0 => let (a, s1) := runState m s0
                                            in runState (f a) s1)
}.

Ltac reason :=
  (* this tactic contains the easy reasoning steps that suffice
     to prove the intermediary lemmas *)
  match goal with
  | [ |- context [runState _]] => unfold runState
  | [ |- context [execState] ] => unfold execState
  | [ |- context [evalState] ] => unfold evalState
  | [ |- {| runState := _ |} = {| runState := _ |} ] => f_equal
  | [ |- (fun _ => _) = _ ] => apply functional_extensionality; intros
  | [ |- {| runState := _ |} = ?x ] => destruct x as [rs]
  | [ s : state S _ |- _ ] => destruct s as [rs]
  | [ |- context [ let (_, _) := ?rs ?x in _ ] ] => destruct (rs x)
  end; simpl; auto.

Instance MonadLaws_state {S : Type} : MonadLaws (state S).
Proof.
  constructor; intros; simpl; repeat reason.
Defined.

Instance MonadState_state {S : Type} : MonadState S (state S) :=
{ get := mkState (fun s => (s, s))
; put := fun s => mkState (fun _ => (tt, s))
}.

Instance MonadStateLaws_state {S : Type} : MonadStateLaws S (state S).
Proof.
  constructor; auto.
Defined.

(* Related theorems *)

Lemma execexec_is_gtgt : forall {S A B} (s : S) (st1 : state S A) (st2 : state S B),
    execState st2 (execState st1 s) = execState (st1 >> st2) s.
Proof.
  intros. repeat reason.
Qed.

Lemma execeval_is_gtgt : forall {S A B} (s : S) (st1 : state S A) (st2 : state S B),
    evalState st2 (execState st1 s) = evalState (st1 >> st2) s.
Proof.
  intros. repeat reason.
Qed.

Lemma execeval_is_bind : forall {S A B} (s : S) (st1 : state S A) (f : A -> state S B),
    execState (f (evalState st1 s)) (execState st1 s) = execState (st1 >>= f) s.
Proof.
  intros. repeat reason.
Qed.

Lemma eval_aM_return : forall {S A X} (m : state S A) (s : S) (x : X),
    evalState (m >> ret x) s = x.
Proof.
  intros. repeat reason.
Qed.

(* XXX: This has to be standard somehow... *)
Theorem unwrap_runState : forall {S A : Type} (f g : S -> A * S),
    f = g -> mkState f = mkState g.
Proof.
  intros.
  now rewrite H.
Qed.


(***********)
(** * Lens *)
(***********)

Record lens (S A : Type) := mkLens
{ view : S -> A
; update : S -> A -> S
}.
Arguments mkLens [S A].
Arguments view [S A].
Arguments update [S A].

Definition view_update {S A : Type} (ln : lens S A) : Prop :=
  forall s, update ln s (view ln s) = s.

Definition update_view {S A : Type} (ln : lens S A) : Prop :=
  forall s a, view ln (update ln s a) = a.

Definition update_update {S A : Type} (ln : lens S A) : Prop :=
  forall s a1 a2, update ln (update ln s a1) a2 = update ln s a2.

Definition very_well_behaved {S A : Type} (ln : lens S A) : Prop :=
  view_update ln /\ update_view ln /\ update_update ln.


(***************************************)
(** * Lens, State Is Your Father Proof *)
(***************************************)

(* Isomorphism [MonadState A (state S) <-> lens S A] *)

Definition ms_2_lens {S A : Type} (ms : MonadState A (state S)) : lens S A :=
{| view s := evalState get s
;  update s a := execState (put a) s
|}.

(* Notice that the backwards arrow (iso) is a typeclass instance that depends on a lens! *)
Instance lens_2_ms {S A : Type} (ln : lens S A) : MonadState A (state S) :=
{ get := mkState (fun s => (view ln s, s))
; put a := mkState (fun s => (tt, update ln s a))
}.

(* Proving that any lawful [MonadState A (state S)] corresponds with a very well-behaved lens *)
Theorem lens_state_is_your_father_forward :
    forall {S A : Type} (ms : MonadState A (state S)),
    @MonadStateLaws A (state S) _ ms -> very_well_behaved (ms_2_lens ms).
Proof.
  intros.
  pose proof (@non_eff_get (state S) A _ ms H _) as non_eff.
  unfold very_well_behaved.
  unfold view_update; unfold update_view; unfold update_update.
  unfold ms_2_lens.
  destruct H as [gg gp pg pp].
  split; [|split]; intros; simpl.

  - (* view_update *)
    rewrite <- (non_eff unit (put (evalState get s))).
    rewrite <- execexec_is_gtgt.
    rewrite -> execeval_is_bind.
    now rewrite -> gp.

  - (* update_view *)
    rewrite -> execeval_is_gtgt.
    rewrite -> pg.
    now rewrite -> eval_aM_return.

  - (* update_update *)
    rewrite -> execexec_is_gtgt.
    now rewrite -> pp.
Qed.

(* and backwards *)
Theorem lens_state_is_your_father_backward :
    forall {S A : Type} (ln : lens S A),
    very_well_behaved ln -> @MonadStateLaws A (state S) _ (lens_2_ms ln).
Proof.
  unfold very_well_behaved.
  unfold view_update. unfold update_view. unfold update_update.
  intros.
  destruct H as [vu [uv uu]].
  constructor;
    unfold get; unfold put;
    unfold lens_2_ms;
    simpl;
    intros;
    apply unwrap_runState;
    apply functional_extensionality;
    intros;
    [| rewrite vu | rewrite uv | rewrite uu];
    reflexivity.
Qed.

(* Subproof to be shown in the post *)
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
