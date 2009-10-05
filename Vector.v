Require Import Program.Equations Program Omega.
Require Export Bvector.

Delimit Scope vect_scope with vect.
Bind Scope vect_scope with vector.

Notation " x |:| y " := (@Vcons _ x _ y) (at level 20, right associativity) : vect_scope.
Notation " [[ x .. y ]] " := (Vcons x .. (Vcons y Vnil) ..) : vect_scope.
Notation " [[]] " := Vnil : vect_scope.

Implicit Arguments Vhead [ [A] [n] ].
Implicit Arguments Vtail [ [A] [n] ].

Open Local Scope vect_scope.

Equations(nocomp) constant_vector {A} (n : nat) (x : A) : vector A n :=
constant_vector A O x := Vnil ;
constant_vector A (S n) x := Vcons x (constant_vector n x).

Equations(nocomp) vector_append {A} {n m : nat} (v : vector A n) (w : vector A m) : vector A (n + m) :=
vector_append A ?(O) m Vnil w := w ;
vector_append A ?(S n) m (Vcons a n x) w := Vcons a (vector_append x w).

Equations vector_append_one {A} {n : nat} (v : vector A n) (a : A) : vector A (S n) :=
vector_append_one A ?(O) Vnil w := Vcons w Vnil ;
vector_append_one A ?(S n) (Vcons a n x) w := Vcons a (vector_append_one x w).

Equations(nocomp) vmap {A B n} (f : A -> B) (v : vector A n) : vector B n :=
vmap A B ?(0) f Vnil := Vnil ;
vmap A B ?(S n) f (Vcons a n v) := Vcons (f a) (vmap f v).

Equations(nocomp) vector_split {A n m} (v : vector A (n + m)) : vector A n * vector A m :=
vector_split A O m v := (Vnil, v) ;
vector_split A (S n) m (Vcons a _ v') := let '(l, r) := vector_split v' in
  (Vcons a l, r).

Equations vfold_left {A B n} (f : B -> A -> B) (v : vector A n) (b : B) : B :=
vfold_left A B ?(0) f Vnil b := b ;
vfold_left A B ?(S n) f (Vcons a n v) b := vfold_left f v (f b a).

Global Transparent vfold_left.

Equations(nocomp) vfold_right {A : nat -> Type} {B} (f : Π n, B -> A n -> A (S n)) (e : A 0) {n} 
  (v : vector B n) : A n := 
vfold_right A B f e ?(O) Vnil := e ;
vfold_right A B f e ?(S n) (Vcons hdv n tlv) := 
  f n hdv (vfold_right f e tlv).

Equations(nocomp) vfold_right2 {A : nat -> Type} {B C} 
  (f : Π n, B -> C -> A n -> A (S n)) (e : A 0) {n} (v : vector B n) (v' : vector C n) : A n := 
vfold_right2 A B C f e ?(O) Vnil Vnil := e ;
vfold_right2 A B C f e ?(S n) (Vcons hdv n tlv) (Vcons hdv' n tlv') := 
  f n hdv hdv' (vfold_right2 f e tlv tlv').

Lemma Vcons_append_one {A n} (a : A) (v : vector A n) : exists a' v', (Vcons a v) = vector_append_one v' a'.
Proof. intros. revert a.
  induction v.
  intros. exists a. exists (@Vnil A). reflexivity.

  intros.
  destruct (IHv a) as [a' [ v' Hv' ] ].
  exists a'. exists (a0 |:| v'). 
  simp vector_append_one. congruence.
Qed.

Lemma vector_rev_ind : Π (A : Type) (P : Π n : nat, vector A n -> Prop),
  P 0 [[]] -> (Π (a : A) (n : nat) (v : vector A n), P n v -> P (S n) (vector_append_one v a)) ->
  Π (n : nat) (v : vector A n), P n v.
Proof.
  intros.
  destruct v.
  assumption.
  revert a v. induction n. intros.
  depelim v. apply (H0 a 0 Vnil H).

  intros.
  depelim v.
  destruct (Vcons_append_one a0 v) as [a' [ v' Ha'v' ] ].
  pose (IHn a0 v).
  rewrite Ha'v' in p.
  rewrite Ha'v'.
  replace (a |:| vector_append_one v' a') with (vector_append_one (a |:| v') a').
  apply H0. apply IHn.
  simp vector_append_one.
Qed.

Lemma f_JMequal {A B} (f : Π x : A, B x) (x y : A) : x = y -> f x ~= f y.
Proof. intros. subst. reflexivity. Qed.

Lemma f_JMequal2 {A B C} (f : Π x : A, B x -> C x) (x : A) (b b' : B x) : b ~= b' -> f x b ~= f x b'.
Proof. intros. pose JMeq_rect.
  apply (p (B x) b b' (fun b' => f x b ~= f x b')). reflexivity.
  assumption.
Qed.

Lemma f_JMequal3 {A B C} (f : Π x : A, B x -> C x) (x y : A) (b : B x) (b' : B y) : x = y ->
  b ~= b' -> f x b ~= f y b'.
Proof. intros. subst. apply f_JMequal2. assumption. Qed.

Lemma vector_append_nil {A n} {v : vector A n} : vector_append v [[]] ~= v.
Proof. intros. funind (vector_append v [[]]) vvnil.
  apply (f_JMequal3 (@Vcons A a)). omega.
  assumption.
Qed.

Equations(nocomp) vector_firstn {A} {l : nat} (s : nat) (c : vector A l) (Hsl : s < l) : vector A s :=
vector_firstn A ?(O) s Vnil Hsl :=! Hsl ;
vector_firstn A ?(S n) O (Vcons a n v) Hsl := Vnil ;
vector_firstn A ?(S n) (S m) (Vcons a n v) Hsl := Vcons a (vector_firstn m v _).

  Next Obligation. omega. Defined.

  Next Obligation. revert s Hsl ; induction c ; intros ;
    simp vector_firstn ; auto with * ; destruct s ; simp vector_firstn.
  Defined.