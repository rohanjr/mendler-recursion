(* Normalization proof for the simply-typed lambda calculus with recursive types *)

Require Import Coq.Init.Peano. (* natural number lemmas *)
Require Import Coq.Setoids.Setoid. (* advanced rewriting *)

(* Simple recursive types *)

Inductive type : Set :=
  | t_unit : type
  | t_arr : type -> type -> type
  | t_var : nat -> type
  | t_rec : type -> type
  | t_pair : type -> type -> type
  | t_sum : type -> type -> type.

(* Expressions, values and environments *)

Inductive expr : Set :=
  | unit : expr
  | var : nat -> expr
  | lam : expr -> expr
  | rec : expr -> expr
  | app : expr -> expr -> expr
  | pair : expr -> expr -> expr
  | fst : expr -> expr
  | snd : expr -> expr
  | inl : expr -> expr
  | inr : expr -> expr
  | case : expr -> expr -> expr -> expr
with value : Set :=
  | v_unit : value
  | v_lam : expr -> environment -> value
  | v_rec : expr -> environment -> value
  | v_pair : value -> value -> value
  | v_inl : value -> value
  | v_inr : value -> value
with environment : Set :=
  | empty : environment
  | extend : environment -> value -> environment.

(* Environment-based lookup and evaluation *)

Inductive lookup : environment -> nat -> value -> Prop :=
  | top env val : lookup (extend env val) 0 val
  | pop env i val val' : lookup env i val' -> lookup (extend env val) (S i) val'.

Inductive eval : environment -> expr -> value -> Prop :=
  | e_unit env : eval env unit v_unit
  | e_var env i val : lookup env i val -> eval env (var i) val
  | e_lam env e : eval env (lam e) (v_lam e env)
  | e_rec env e : eval env (rec e) (v_rec e env)
  | e_app env e1 e2 val1 val2 val : eval env e1 val1 -> eval env e2 val2 -> eval_app val1 val2 val -> eval env (app e1 e2) val
  | e_pair env e1 e2 val1 val2 : eval env e1 val1 -> eval env e2 val2 -> eval env (pair e1 e2) (v_pair val1 val2)
  | e_fst env e val1 val2 : eval env e (v_pair val1 val2) -> eval env (fst e) val1
  | e_snd env e val1 val2 : eval env e (v_pair val1 val2) -> eval env (snd e) val2
  | e_inl env e val : eval env e val -> eval env (inl e) (v_inl val)
  | e_inr env e val : eval env e val -> eval env (inr e) (v_inr val)
  | e_case_inl env e e1 e2 val val' : eval env e (v_inl val) -> eval (extend env val) e1 val' -> eval env (case e e1 e2) val'
  | e_case_inr env e e1 e2 val val' : eval env e (v_inr val) -> eval (extend env val) e2 val' -> eval env (case e e1 e2) val'
with eval_app : value -> value -> value -> Prop :=
  | e_app_lam env e val val': eval (extend env val') e val -> eval_app (v_lam e env) val' val
  | e_app_rec env e v u w : eval (extend env (v_rec e env)) e v -> eval_app v u w -> eval_app (v_rec e env) u w.

(* Typing context *)

Inductive context : Set :=
  | c_empty : context
  | c_extend : context -> type -> context.

Inductive c_lookup : context -> nat -> type -> Prop :=
  | c_top ctx ty : c_lookup (c_extend ctx ty) 0 ty
  | c_pop ctx i ty ty' : c_lookup ctx i ty' -> c_lookup (c_extend ctx ty) (S i) ty'.

(* Type variable context *)

Inductive tv_context : Set :=
  | tv_empty : tv_context
  | tv_extend : tv_context -> tv_context.

(* Not yet needed since kind-checking is redundant *)
Inductive tv_lookup : tv_context -> nat -> Prop :=
  | tv_top tvc : tv_lookup (tv_extend tvc) 0
  | tv_pop tvc i : tv_lookup tvc i -> tv_lookup (tv_extend tvc) (S i).

(* Type substitutions and renamings *)

Inductive subst : Set :=
  | sub_shift : nat -> subst
  | sub_extend : subst -> type -> subst.

Definition sub_single (ty : type) : subst := sub_extend (sub_shift 0) ty.

Inductive renaming : Set :=
  | ren_shift : nat -> renaming
  | ren_extend : renaming -> nat -> renaming.

Fixpoint subst_of_renaming (ren : renaming) : subst :=
  match ren with
    | ren_shift n => sub_shift n
    | ren_extend ren' k => sub_extend (subst_of_renaming ren') (t_var k)
  end.

Fixpoint sub_lookup (sub : subst) (k : nat) : type :=
  match sub with
    | sub_shift n => t_var (n + k)
    | sub_extend sub' ty =>
        match k with
          | 0 => ty
          | S k' => sub_lookup sub' k'
        end
  end.

Fixpoint ren_lookup (ren: renaming) (k : nat) : nat :=
  match ren with
    | ren_shift n => n + k
    | ren_extend ren' j =>
        match k with
          | 0 => j
          | S k' => ren_lookup ren' k'
        end
  end.

Fixpoint ren_pop (ren : renaming) (n : nat) : renaming :=
  match ren with
    | ren_shift m => ren_shift (n + m)
    | ren_extend ren' k =>
        match n with
          | 0 => ren
          | S n' => ren_pop ren' n'
        end
  end.

Fixpoint renaming_under_renaming (ren1 ren2 : renaming) : renaming :=
  match ren1 with
    | ren_shift n => ren_pop ren2 n
    | ren_extend ren' k => ren_extend (renaming_under_renaming ren' ren2) (ren_lookup ren2 k)
  end.

Fixpoint type_under_renaming (ty : type) (ren : renaming) : type :=
  match ty with
    | t_unit => t_unit
    | t_arr ty1 ty2 => t_arr (type_under_renaming ty1 ren) (type_under_renaming ty2 ren)
    | t_var k => t_var (ren_lookup ren k)
    | t_rec ty' => t_rec (type_under_renaming ty' (ren_extend (renaming_under_renaming ren (ren_shift 1)) 0))
    | t_pair ty1 ty2 => t_pair (type_under_renaming ty1 ren) (type_under_renaming ty2 ren)
    | t_sum ty1 ty2 => t_sum (type_under_renaming ty1 ren) (type_under_renaming ty2 ren)
  end.

Fixpoint subst_under_renaming (sub : subst) (ren : renaming) : subst :=
  match sub with
    | sub_shift n => subst_of_renaming (ren_pop ren n)
    | sub_extend sub' ty => sub_extend (subst_under_renaming sub' ren) (type_under_renaming ty ren)
  end.

Fixpoint type_under_subst (ty : type) (sub : subst) : type :=
  match ty with
    | t_unit => t_unit
    | t_arr ty1 ty2 => t_arr (type_under_subst ty1 sub) (type_under_subst ty2 sub)
    | t_var k => sub_lookup sub k
    | t_rec ty' => t_rec (type_under_subst ty' (sub_extend (subst_under_renaming sub (ren_shift 1)) (t_var 0)))
    | t_pair ty1 ty2 => t_pair (type_under_subst ty1 sub) (type_under_subst ty2 sub)
    | t_sum ty1 ty2 => t_sum (type_under_subst ty1 sub) (type_under_subst ty2 sub)
  end.

Fixpoint shift_context (ctx : context) : context :=
  match ctx with
    | c_empty => c_empty
    | c_extend ctx' ty => c_extend (shift_context ctx') (type_under_renaming ty (ren_shift 1))
  end.

(* Typing rules *)

Inductive of_type : tv_context -> context -> expr -> type -> Prop :=
  | oft_unit tvc ctx : of_type tvc ctx unit t_unit
  | oft_var tvc ctx i ty : c_lookup ctx i ty -> of_type tvc ctx (var i) ty
  | oft_lam tvc ctx e ty1 ty2 : of_type tvc (c_extend ctx ty1) e ty2 -> of_type tvc ctx (lam e) (t_arr ty1 ty2)
  | oft_app tvc ctx e1 e2 ty1 ty2 : of_type tvc ctx e1 (t_arr ty1 ty2) -> of_type tvc ctx e2 ty1 -> of_type tvc ctx (app e1 e2) ty2
  | oft_pair tvc ctx e1 e2 ty1 ty2 : of_type tvc ctx e1 ty1 -> of_type tvc ctx e2 ty2 -> of_type tvc ctx (pair e1 e2) (t_pair ty1 ty2)
  | oft_fst tvc ctx e ty1 ty2 : of_type tvc ctx e (t_pair ty1 ty2) -> of_type tvc ctx (fst e) ty1
  | oft_snd tvc ctx e ty1 ty2 : of_type tvc ctx e (t_pair ty1 ty2) -> of_type tvc ctx (snd e) ty2
  | oft_inl tvc ctx e ty1 ty2 : of_type tvc ctx e ty1 -> of_type tvc ctx (inl e) (t_sum ty1 ty2)
  | oft_inr tvc ctx e ty1 ty2 : of_type tvc ctx e ty2 -> of_type tvc ctx (inr e) (t_sum ty1 ty2)
  | oft_case tvc ctx e e1 e2 ty1 ty2 ty : of_type tvc ctx e (t_sum ty1 ty2) -> of_type tvc (c_extend ctx ty1) e1 ty -> of_type tvc (c_extend ctx ty2) e2 ty -> of_type tvc ctx (case e e1 e2) ty
  | oft_fold tvc ctx e ty : of_type tvc ctx e (type_under_subst ty (sub_single (t_rec ty))) -> of_type tvc ctx e (t_rec ty)
  | oft_rec tvc ctx e ty ty': of_type (tv_extend tvc) (c_extend (shift_context ctx) (t_arr (t_var 0) (type_under_renaming ty' (ren_shift 1)))) e (t_arr ty (type_under_renaming ty' (ren_shift 1))) -> of_type tvc ctx (rec e) (t_arr (t_rec ty) ty').


(* Set theory *)

Definition set (S : Type) : Type := S -> Prop.

Definition empty_set {S : Type} : set S := fun x => False.

Definition id {S : Type} : S -> S := fun x => x.

Definition set_eq {S : Type} (A B : set S) : Prop := forall x : S, A x <-> B x.

Lemma set_eq_refl {S : Type} (A : set S) : set_eq A A.
  unfold set_eq.
  intro.
  apply iff_refl.
  Qed.

Lemma set_eq_sym {S : Type} (A B : set S) : set_eq A B -> set_eq B A.
  unfold set_eq.
  intros.
  apply iff_sym.
  apply H.
  Qed.

Lemma set_eq_trans {S : Type} (A B C : set S) : set_eq A B -> set_eq B C -> set_eq A C.
  unfold set_eq.
  intros.
  apply iff_trans with (B := B x).
  apply H.
  apply H0.
  Qed.

Lemma iff_inst (A B : Prop) : A <-> B -> A -> B.
  intros.
  destruct H.
  apply H.
  apply H0.
  Qed.

Lemma set_eq_inst {S : Type} (A B : set S) (x : S) : set_eq A B -> A x -> B x.
  unfold set_eq.
  intros.
  apply iff_inst with (A := A x).
  apply H.
  apply H0.
  Qed.

Definition subset {S : Type} (A B : set S) : Prop := forall x : S, A x -> B x.

Lemma subset_inst {S : Type} (A B : set S) (x : S) : subset A B -> A x -> B x.
  unfold subset.
  intros.
  apply H with (x := x).
  apply H0.
  Qed.

Lemma subset_refl {S : Type} (A : set S) : subset A A.
  unfold subset.
  auto.
  Qed.

Lemma set_eq_subset {S : Type} (A B : set S) (H1 : subset A B) (H2 : subset B A) : set_eq A B.
  unfold set_eq.
  split.
  apply H1.
  apply H2.
  Qed.

Lemma subset_set_eq {S : Type} (A A' B : set S) (H1 : set_eq A A') (H2 : subset A B) : subset A' B.
  unfold subset.
  intros.
  apply subset_inst with (A0 := A).
  apply H2.
  apply set_eq_inst with (A0 := A').
  apply set_eq_sym.
  apply H1.
  apply H.
  Qed.

Definition union {S : Type} (A B : set S) : set S :=
  fun x : S => A x \/ B x.

Lemma union_subset1 {S : Type} (A B : set S) : subset A (union A B).
  unfold subset, union.
  intros.
  left.
  apply H.
  Qed.

Lemma union_subset2 {S : Type} (A B : set S) : subset B (union A B).
  unfold subset, union.
  intros.
  right.
  apply H.
  Qed.

Definition union_set_eq {S : Type} (A A' B B' : set S) (H1 : set_eq A A') (H2 : set_eq B B') :
  set_eq (union A B) (union A' B').
  unfold set_eq, union.
  split.
  intros.
  destruct H.
  left.
  apply set_eq_inst with (A0 := A).
  apply H1.
  apply H.
  right.
  apply set_eq_inst with (A0 := B).
  apply H2.
  apply H.
  intros.
  destruct H.
  left.
  apply set_eq_inst with (A0 := A').
  apply set_eq_sym.
  apply H1.
  apply H.
  right.
  apply set_eq_inst with (A0 := B').
  apply set_eq_sym.
  apply H2.
  apply H.
  Qed.

Definition intersection {S T : Type} (P : set S) (f : S -> set T) : set T :=
  fun v : T => forall i : S, P i -> f i v.

Lemma in_intersection {S T : Type} (A : set T) (P : set S) (f : S -> set T) :
  subset A (intersection P f) <-> forall i : S, P i -> subset A (f i).
  unfold subset.
  unfold intersection.
  split.
  auto.
  auto.
  Qed.

Lemma intersection_in {S T : Type} (A : set T) (P : set S) (f : S -> set T) :
  forall i : S, (P i -> subset (f i) A -> subset (intersection P f) A).
  unfold subset.
  unfold intersection.
  auto.
  Qed.

Definition prefp {S : Type} (F : set S -> set S) : set S :=
  intersection (fun C : set S => (forall X : set S, subset X C -> subset (F X) C)) id.

Lemma prefp_fp {S : Type} (F : set S -> set S) : subset (F (prefp F)) (prefp F).
  unfold prefp at 2.
  apply in_intersection.
  intros C H.
  apply H.
  apply intersection_in with (i := C).
  apply H.
  apply subset_refl.
  Qed.

Lemma prefp_subset {S : Type} (F F' : set S -> set S)
  (H : forall X, set_eq (F X) (F' X)) : subset (prefp F) (prefp F').
  unfold prefp.
  apply in_intersection.
  intros.
  apply intersection_in with (i0 := i).
  intros.
  apply subset_set_eq with (A := F' X).
  apply set_eq_sym.
  apply H.
  apply H0.
  apply H1.
  apply subset_refl.
  Qed.

Lemma prefp_set_eq {S : Type} (F F' : set S -> set S)
  (H : forall X, set_eq (F X) (F' X)) : set_eq (prefp F) (prefp F').
  apply set_eq_subset.
  apply prefp_subset.
  apply H.
  apply prefp_subset.
  intro.
  apply set_eq_sym.
  apply H.
  Qed.

(* Semantic function space *)

Definition funsp (A B : set value) : set value :=
  fun v : value => forall u : value, A u -> exists w, B w /\ eval_app v u w.

Lemma funsp_set_eq (A A' B B' : set value) : set_eq A A' -> set_eq B B' -> set_eq (funsp A B) (funsp A' B').
  unfold funsp, set_eq.
  intros.
  split.
  intros.
  assert (A u).
  apply iff_inst with (A := A' u).
  apply iff_sym.
  apply H.
  apply H2.
  destruct H1 with (u := u).
  apply H3.
  exists x0.
  destruct H4.
  split.
  apply iff_inst with (A := B x0).
  apply H0.
  apply H4.
  apply H5.
  intros.
  assert (A' u).
  apply iff_inst with (A := A u).
  apply H.
  apply H2.
  destruct H1 with (u := u).
  apply H3.
  exists x0.
  destruct H4.
  split.
  apply iff_inst with (A := B' x0).
  apply iff_sym.
  apply H0.
  apply H4.
  apply H5.
  Qed.

Definition evset (v : value) (B : set value) : set value :=
  fun u : value => exists w : value, B w /\ eval_app v u w.

Lemma funsp_evset (v : value) (A B : set value) :
  funsp A B v <-> subset A (evset v B).
  split.
  auto.
  auto.
  Qed.

Lemma funsp_prefp (v : value) (C : set value) (F : set value -> set value) :
  (forall X : set value, funsp X C v -> funsp (F X) C v) -> funsp (prefp F) C v.
  setoid_rewrite funsp_evset.
  intro H.
  unfold prefp.
  apply intersection_in with (i := evset v C).
  apply H.
  apply subset_refl.
  Qed.

(* Cross product of value sets *)

Definition product (A B : set value) : set value :=
  fun v : value =>
    exists val1 val2 : value,
    A val1 /\ B val2 /\ v = v_pair val1 val2.

Lemma product_set_eq (A A' B B' : set value) (HA : set_eq A A') (HB : set_eq B B') :
  set_eq (product A B) (product A' B').
  unfold set_eq, product.
  intro.
  split.
  intro.
  destruct H.
  destruct H.
  destruct H.
  destruct H0.
  subst.
  exists x0.
  exists x1.
  split.
  apply set_eq_inst with (A0 := A).
  apply HA.
  apply H.
  split.
  apply set_eq_inst with (A0 := B).
  apply HB.
  apply H0.
  reflexivity.
  intro.
  destruct H.
  destruct H.
  destruct H.
  destruct H0.
  subst.
  exists x0.
  exists x1.
  split.
  apply set_eq_inst with (A0 := A').
  apply set_eq_sym.
  apply HA.
  apply H.
  split.
  apply set_eq_inst with (A0 := B').
  apply set_eq_sym.
  apply HB.
  apply H0.
  reflexivity.
  Qed.

(* Injections of sets *)

Definition inl_set (A : set value) : set value :=
  fun w => exists v, A v /\ w = v_inl v.

Definition inr_set (A : set value) : set value :=
  fun w => exists v, A v /\ w = v_inr v.

Definition disj_sum (A B : set value) : set value :=
  union (inl_set A) (inr_set B).

Lemma in_inl_set (A B : set value) (v : value) : A v -> (disj_sum A B) (v_inl v).
  intro.
  unfold disj_sum.
  apply union_subset1.
  unfold inl_set.
  exists v.
  split.
  apply H.
  reflexivity.
  Qed.

Lemma in_inr_set (A B : set value) (v : value) : B v -> (disj_sum A B) (v_inr v).
  intro.
  unfold disj_sum.
  apply union_subset2.
  unfold inr_set.
  exists v.
  split.
  apply H.
  reflexivity.
  Qed.

Lemma inl_set_eq (A A' : set value) : set_eq A A' -> set_eq (inl_set A) (inl_set A').
  intro.
  unfold set_eq, inl_set.
  split.
  intros.
  destruct H0.
  destruct H0.
  exists x0.
  split.
  apply set_eq_inst with (A0 := A).
  apply H.
  apply H0.
  apply H1.
  intros.
  destruct H0.
  destruct H0.
  exists x0.
  split.
  apply set_eq_inst with (A0 := A').
  apply set_eq_sym.
  apply H.
  apply H0.
  apply H1.
  Qed.

Lemma inr_set_eq (A A' : set value) : set_eq A A' -> set_eq (inr_set A) (inr_set A').
  intro.
  unfold set_eq, inr_set.
  split.
  intros.
  destruct H0.
  destruct H0.
  exists x0.
  split.
  apply set_eq_inst with (A0 := A).
  apply H.
  apply H0.
  apply H1.
  intros.
  destruct H0.
  destruct H0.
  exists x0.
  split.
  apply set_eq_inst with (A0 := A').
  apply set_eq_sym.
  apply H.
  apply H0.
  apply H1.
  Qed.

Lemma disj_sum_eq (A A' B B' : set value) (HA : set_eq A A') (HB : set_eq B B') :
  set_eq (disj_sum A B) (disj_sum A' B').
  unfold disj_sum.
  apply union_set_eq.
  apply inl_set_eq.
  apply HA.
  apply inr_set_eq.
  apply HB.
  Qed.

(* Type variable map *)

Inductive tv_map : Type :=
  | tvm_empty : tv_map
  | tvm_extend : tv_map -> set value -> tv_map.

Inductive tv_map_eq : tv_map -> tv_map -> Prop :=
  | tvm_eq_empty : tv_map_eq tvm_empty tvm_empty
  | tvm_eq_extend tvm1' tvm2' X1 X2 : tv_map_eq tvm1' tvm2' -> set_eq X1 X2 -> tv_map_eq (tvm_extend tvm1' X1) (tvm_extend tvm2' X2).

(* Well-formed tv map under a tv context *)

Inductive tv_map_of_ctx : tv_map -> tv_context -> Prop :=
  | tv_map_empty : tv_map_of_ctx tvm_empty tv_empty
  | tv_map_extend tvc tvm C : tv_map_of_ctx tvm tvc -> tv_map_of_ctx (tvm_extend tvm C) (tv_extend tvc).

(* Lemmas about tv_map equality *)

Lemma tv_map_eq_refl (tvm : tv_map) : tv_map_eq tvm tvm.
  induction tvm.
  apply tvm_eq_empty.
  apply tvm_eq_extend.
  apply IHtvm.
  apply set_eq_refl.
  Qed.

Lemma tv_map_eq_sym (tvm1 tvm2 : tv_map) (H : tv_map_eq tvm1 tvm2) : tv_map_eq tvm2 tvm1.
  induction H.
  apply tvm_eq_empty.
  apply tvm_eq_extend.
  apply IHtv_map_eq.
  apply set_eq_sym.
  apply H0.
  Qed.

Lemma tv_map_eq_trans (tvm2 : tv_map) :
  forall tvm1 tvm3 : tv_map, tv_map_eq tvm1 tvm2 -> tv_map_eq tvm2 tvm3 -> tv_map_eq tvm1 tvm3.
  induction tvm2.
  intros.
  inversion H.
  inversion H0.
  apply tvm_eq_empty.
  intros.
  inversion H.
  inversion H0.
  subst.
  apply tvm_eq_extend.
  apply IHtvm2.
  apply H4.
  apply H8.
  apply set_eq_trans with (B := s).
  assumption.
  assumption.
  Qed.

Fixpoint tvm_lookup (tvm : tv_map) (k : nat) : set value :=
  match tvm with
    | tvm_empty => empty_set
    | tvm_extend tvm' X =>
        match k with
          | 0 => X
          | S k' => tvm_lookup tvm' k'
        end
  end.

Lemma tvm_lookup_eq (tvm1 tvm2 : tv_map) (H : tv_map_eq tvm1 tvm2) :
  forall k : nat, set_eq (tvm_lookup tvm1 k) (tvm_lookup tvm2 k).
  induction H.
  intro.
  simpl.
  apply set_eq_refl.
  intro.
  destruct k.
  simpl.
  apply H0.
  simpl.
  apply IHtv_map_eq.
  Qed.

Fixpoint tvm_pop (tvm : tv_map) (n : nat) : tv_map :=
  match tvm with
    | tvm_empty => tvm_empty
    | tvm_extend tvm' X =>
        match n with
          | 0 => tvm
          | S n' => tvm_pop tvm' n'
        end
  end.

(* Semantic interpretation of types/contexts as sets of values/environments *)

Fixpoint semantic_type (ty : type) (tvm : tv_map) : set value :=
  match ty with
    | t_unit => (fun val => val = v_unit)
    | t_arr ty1 ty2 => funsp (semantic_type ty1 tvm) (semantic_type ty2 tvm)
    | t_var k => tvm_lookup tvm k
    | t_rec ty => prefp (fun X => semantic_type ty (tvm_extend tvm X))
    | t_pair ty1 ty2 => product (semantic_type ty1 tvm) (semantic_type ty2 tvm)
    | t_sum ty1 ty2 => disj_sum (semantic_type ty1 tvm) (semantic_type ty2 tvm)
  end.

Fixpoint semantic_ctx (ctx : context) (tvm : tv_map) : set environment :=
  match ctx with
    | c_empty => (fun env => env = empty)
    | c_extend ctx' ty => (fun env => exists env', exists val, semantic_ctx ctx' tvm env' /\ semantic_type ty tvm val /\ env = extend env' val)
  end.

(* Semantic interpretations of substitution and renaming as type variable maps *)

Fixpoint semantic_subst (sub : subst) (tvm : tv_map) : tv_map :=
  match sub with
    | sub_shift n => tvm_pop tvm n
    | sub_extend sub' ty => tvm_extend (semantic_subst sub' tvm) (semantic_type ty tvm)
  end.

Fixpoint semantic_renaming (ren : renaming) (tvm : tv_map) : tv_map :=
  match ren with
    | ren_shift n => tvm_pop tvm n
    | ren_extend ren' k => tvm_extend (semantic_renaming ren' tvm) (tvm_lookup tvm k)
  end.

Lemma semantic_type_tv_map_eq (ty : type) :
  forall tvm1 tvm2 : tv_map, forall H : tv_map_eq tvm1 tvm2,
  set_eq (semantic_type ty tvm1) (semantic_type ty tvm2).
  induction ty.
  intros.
  apply set_eq_refl.
  intros.
  simpl.
  apply funsp_set_eq.
  apply IHty1.
  apply H.
  apply IHty2.
  apply H.
  intros.
  simpl.
  apply tvm_lookup_eq.
  apply H.
  intros.
  simpl.
  apply prefp_set_eq.
  intro.
  apply IHty.
  apply tvm_eq_extend.
  apply H.
  apply set_eq_refl.
  intros.
  simpl.
  apply product_set_eq.
  apply IHty1.
  apply H.
  apply IHty2.
  apply H.
  intros.
  simpl.
  apply disj_sum_eq.
  apply IHty1.
  apply H.
  apply IHty2.
  apply H.
  Qed.

Lemma type_fun_subset (ty : type) (tvm : tv_map) :
  subset (semantic_type ty (tvm_extend tvm (semantic_type (t_rec ty) tvm))) (semantic_type (t_rec ty) tvm).
  simpl.
  apply subset_set_eq with (A := semantic_type ty (tvm_extend tvm (prefp (fun X : set value => (semantic_type ty (tvm_extend tvm X)))))).
  apply semantic_type_tv_map_eq.
  apply tvm_eq_extend.
  apply tv_map_eq_refl.
  apply prefp_set_eq.
  intro.
  apply set_eq_refl.
  apply prefp_fp with (F := fun X => semantic_type ty (tvm_extend tvm X)).
  Qed.

(* Many lemmas for preservation of semantics under substitution structures *)

Lemma tvm_pop_0 (tvm : tv_map) : tvm_pop tvm 0 = tvm.
  destruct tvm; simpl; reflexivity.
  Qed.

Lemma tvm_pop_pop (tvm : tv_map) :
  forall n m : nat, tv_map_eq (tvm_pop (tvm_pop tvm m) n) (tvm_pop tvm (n + m)).
  induction tvm.
  intros.
  simpl.
  apply tvm_eq_empty.
  intros.
  destruct m.
  rewrite tvm_pop_0.
  rewrite <- plus_n_O.
  apply tv_map_eq_refl.
  rewrite <- plus_n_Sm.
  simpl.
  apply IHtvm.
  Qed.

Lemma tvm_lookup_pop (tvm : tv_map) :
  forall n k : nat, set_eq (tvm_lookup (tvm_pop tvm n) k) (tvm_lookup tvm (n + k)).
  induction tvm.
  intros.
  simpl.
  apply set_eq_refl.
  intros.
  destruct n.
  simpl.
  apply set_eq_refl.
  simpl.
  apply IHtvm.
  Qed.

Lemma semantic_ren_pop (ren : renaming) (tvm : tv_map) :
  forall n : nat, tv_map_eq (semantic_renaming (ren_pop ren n) tvm) (tvm_pop (semantic_renaming ren tvm) n).
  induction ren.
  intro m.
  simpl.
  apply tv_map_eq_sym.
  apply tvm_pop_pop.
  intro m.
  destruct m.
  simpl.
  apply tv_map_eq_refl.
  simpl.
  apply IHren.
  Qed.

Lemma semantic_ren_lookup (ren : renaming) (tvm : tv_map) :
  forall k : nat, set_eq (tvm_lookup (semantic_renaming ren tvm) k) (tvm_lookup tvm (ren_lookup ren k)).
  induction ren.
  intros.
  simpl.
  apply tvm_lookup_pop.
  intros.
  destruct k.
  simpl.
  apply set_eq_refl.
  simpl.
  apply IHren.
  Qed.

Lemma semantic_renaming_under_renaming (ren1 ren2 : renaming) :
  forall tvm : tv_map,
  tv_map_eq (semantic_renaming (renaming_under_renaming ren1 ren2) tvm)
  (semantic_renaming ren1 (semantic_renaming ren2 tvm)).
  induction ren1.
  intro.
  simpl.
  apply semantic_ren_pop.
  intro.
  simpl.
  apply tvm_eq_extend.
  apply IHren1.
  apply set_eq_sym.
  apply semantic_ren_lookup.
  Qed.

Lemma semantic_type_under_renaming (ty : type) :
  forall ren : renaming, forall tvm : tv_map,
  set_eq (semantic_type (type_under_renaming ty ren) tvm)
  (semantic_type ty (semantic_renaming ren tvm)).
  induction ty.
  intros.
  simpl.
  apply set_eq_refl.
  intros.
  simpl.
  apply funsp_set_eq.
  apply IHty1.
  apply IHty2.
  intros.
  simpl.
  apply set_eq_sym.
  apply semantic_ren_lookup.
  intros.
  simpl.
  apply prefp_set_eq.
  intro.
  apply set_eq_trans with (B := semantic_type ty (semantic_renaming (ren_extend (renaming_under_renaming ren (ren_shift 1)) 0) (tvm_extend tvm X))).
  apply IHty.
  simpl.
  apply semantic_type_tv_map_eq.
  apply tvm_eq_extend.
  apply tv_map_eq_trans with (tvm2 := semantic_renaming ren (semantic_renaming (ren_shift 1) (tvm_extend tvm X))).
  simpl.
  apply semantic_renaming_under_renaming.
  simpl.
  rewrite tvm_pop_0.
  apply tv_map_eq_refl.
  apply set_eq_refl.
  intros.
  simpl.
  apply product_set_eq.
  apply IHty1.
  apply IHty2.
  intros.
  simpl.
  apply disj_sum_eq.
  apply IHty1.
  apply IHty2.
  Qed.

Lemma semantic_subst_of_renaming (ren : renaming) (tvm : tv_map) :
  tv_map_eq (semantic_subst (subst_of_renaming ren) tvm) (semantic_renaming ren tvm).
  induction ren.
  simpl.
  apply tv_map_eq_refl.
  simpl.
  apply tvm_eq_extend.
  apply IHren.
  apply set_eq_refl.
  Qed.

Lemma semantic_subst_under_renaming (sub : subst) (ren : renaming) (tvm : tv_map) :
  tv_map_eq (semantic_subst (subst_under_renaming sub ren) tvm)
  (semantic_subst sub (semantic_renaming ren tvm)).
  induction sub.
  simpl.
  apply tv_map_eq_trans with (tvm2 := semantic_renaming (ren_pop ren n) tvm).
  apply semantic_subst_of_renaming.
  apply semantic_ren_pop.
  simpl.
  apply tvm_eq_extend.
  apply IHsub.
  apply semantic_type_under_renaming.
  Qed.

Lemma semantic_sub_lookup (sub : subst) (tvm : tv_map) :
  forall k : nat, set_eq (semantic_type (sub_lookup sub k) tvm) (tvm_lookup (semantic_subst sub tvm) k).
  induction sub.
  intros.
  simpl.
  apply set_eq_sym.
  apply tvm_lookup_pop.
  intros.
  destruct k.
  simpl.
  apply set_eq_refl.
  simpl.
  apply IHsub.
  Qed.

(* Main substitution lemma *)

Lemma semantic_type_under_subst (ty : type) :
  forall sub : subst, forall tvm : tv_map,
  set_eq (semantic_type (type_under_subst ty sub) tvm) (semantic_type ty (semantic_subst sub tvm)).
  induction ty.
  intros.
  simpl.
  apply set_eq_refl.
  intros.
  simpl.
  apply funsp_set_eq.
  apply IHty1.
  apply IHty2.
  intros.
  simpl.
  apply semantic_sub_lookup.
  intros.
  simpl.
  apply prefp_set_eq.
  intro.
  apply set_eq_trans with (B := semantic_type ty (semantic_subst (sub_extend (subst_under_renaming sub (ren_shift 1)) (t_var 0)) (tvm_extend tvm X))).
  apply IHty.
  simpl.
  apply semantic_type_tv_map_eq.
  apply tvm_eq_extend.
  apply tv_map_eq_trans with (tvm2 := semantic_subst sub (semantic_renaming (ren_shift 1) (tvm_extend tvm X))).
  apply semantic_subst_under_renaming.
  simpl.
  rewrite tvm_pop_0.
  apply tv_map_eq_refl.
  apply set_eq_refl.
  intros.
  simpl.
  apply product_set_eq.
  apply IHty1.
  apply IHty2.
  intros.
  simpl.
  apply disj_sum_eq.
  apply IHty1.
  apply IHty2.
  Qed.

Corollary semantic_type_under_single_subst (tvm : tv_map) (ty ty' : type) (val : value) :
  set_eq (semantic_type (type_under_subst ty (sub_single ty')) tvm)
  (semantic_type ty (tvm_extend tvm (semantic_type ty' tvm))).
  apply set_eq_trans with (B := semantic_type ty (semantic_subst (sub_single ty') tvm)).
  apply semantic_type_under_subst.
  unfold sub_single.
  simpl.
  apply semantic_type_tv_map_eq.
  apply tvm_eq_extend.
  rewrite tvm_pop_0.
  apply tv_map_eq_refl.
  apply set_eq_refl.
  Qed.

(* Cases of normalization theorem *)

Definition normalizes (tvm : tv_map) (ty : type) (env : environment) (e : expr) :=
  exists val : value, semantic_type ty tvm val /\ eval env e val.

Lemma norm_unit (tvm : tv_map) (env : environment) : normalizes tvm t_unit env unit.
  unfold normalizes.
  exists v_unit.
  split.
  simpl.
  reflexivity.
  apply e_unit.
  Qed.
  
Lemma norm_var' (i : nat) (tvc : tv_context) (tvm : tv_map) :
  forall ctx : context, forall env : environment, forall ty : type,
  tv_map_of_ctx tvm tvc -> semantic_ctx ctx tvm env -> c_lookup ctx i ty -> exists val, semantic_type ty tvm val /\ lookup env i val.
  induction i.
  intros.
  inversion H1.
  subst.
  inversion H0.
  destruct H2.
  destruct H2.
  destruct H3.
  subst.
  exists x0.
  split.
  assumption.
  apply top.
  intros.
  inversion H1.
  subst.
  inversion H0.
  destruct H2.
  destruct H2.
  destruct H3.
  subst.
  destruct IHi with (env := x)(ctx := ctx0)(ty := ty).
  assumption.
  assumption.
  assumption.
  destruct H5.
  exists x1.
  split.
  assumption.
  apply pop.
  assumption.
  Qed.

Lemma eval_var (k : nat) (env : environment) (val : value) :
  eval env (var k) val <-> lookup env k val.
  split.
  intro.
  inversion H.
  apply H2.
  intro.
  apply e_var.
  apply H.
  Qed.

Lemma norm_var (k : nat) (tvc : tv_context) (tvm : tv_map)
               (ctx : context) (env : environment) (ty : type) :
  tv_map_of_ctx tvm tvc -> semantic_ctx ctx tvm env -> c_lookup ctx k ty -> normalizes tvm ty env (var k).
  unfold normalizes.
  setoid_rewrite eval_var.
  apply norm_var'.
  Qed.

Lemma backward_closure (e : expr) (env : environment) (A B : set value) :
  (exists val : value, eval (extend env (v_rec e env)) e val /\ funsp A B val) ->
  funsp A B (v_rec e env).
  unfold funsp.
  intros.
  destruct H.
  destruct H.
  destruct H1 with (u := u).
  apply H0.
  destruct H2.
  exists x0.
  split.
  apply H2.
  apply e_app_rec with (v := x).
  apply H.
  apply H3.
  Qed.

Lemma semantic_shift_context (ctx : context) (tvm : tv_map) (X : set value) :
  set_eq (semantic_ctx (shift_context ctx) (tvm_extend tvm X)) (semantic_ctx ctx tvm).
  induction ctx.
  simpl.
  apply set_eq_refl.
  unfold set_eq.
  intro.
  simpl.
  split.
  intros.
  destruct H.
  destruct H.
  destruct H.
  destruct H0.
  subst.
  exists x0.
  exists x1.
  split.
  apply set_eq_inst with (A := semantic_ctx (shift_context ctx) (tvm_extend tvm X)).
  apply IHctx.
  apply H.
  split.
  apply set_eq_inst with (A := semantic_type (type_under_renaming t (ren_shift 1)) (tvm_extend tvm X)).
  apply set_eq_trans with (B := semantic_type t (semantic_renaming (ren_shift 1) (tvm_extend tvm X))).
  apply semantic_type_under_renaming.
  simpl.
  rewrite tvm_pop_0.
  apply set_eq_refl.
  apply H0.
  reflexivity.
  intros.
  destruct H.
  destruct H.
  destruct H.
  destruct H0.
  subst.
  exists x0.
  exists x1.
  split.
  apply set_eq_inst with (A := semantic_ctx ctx tvm).
  apply set_eq_sym.
  apply IHctx.
  apply H.
  split.
  apply set_eq_inst with (A := semantic_type t tvm).
  apply set_eq_trans with (B := semantic_type t (semantic_renaming (ren_shift 1) (tvm_extend tvm X))).
  simpl.
  rewrite tvm_pop_0.
  apply set_eq_refl.
  apply set_eq_sym.
  apply semantic_type_under_renaming.
  apply H0.
  reflexivity.
  Qed.

(* Main theorem *)

Theorem normalization' (tvc : tv_context) (ctx : context) (e : expr) (ty : type) (D : of_type tvc ctx e ty) :
  forall env : environment, forall tvm : tv_map, tv_map_of_ctx tvm tvc ->
  semantic_ctx ctx tvm env -> normalizes tvm ty env e.
  induction D.
  intros.
  apply norm_unit.
  intros.
  apply norm_var with (k:=i)(tvc:=tvc)(tvm:=tvm)(env:=env)(ctx:=ctx)(ty:=ty).
  apply H0.
  apply H1.
  apply H.
  intros.
  unfold normalizes.
  exists (v_lam e env).
  split.
  simpl.
  unfold funsp.
  intros.
  destruct IHD with (env := extend env u)(tvm := tvm).
  apply H.
  simpl.
  exists env.
  exists u.
  split.
  apply H0.
  split.
  apply H1.
  reflexivity.
  exists x.
  split.
  destruct H2.
  assumption.
  apply e_app_lam.
  destruct H2.
  assumption.
  apply e_lam.
  intros.
  unfold normalizes.
  destruct IHD1 with (env := env)(tvm := tvm).
  assumption.
  assumption.
  destruct IHD2 with (env := env)(tvm := tvm).
  assumption.
  assumption.
  destruct H1.
  destruct H2.
  simpl in H1.
  unfold funsp in H1.
  destruct H1 with (u := x0).
  assumption.
  exists x1.
  split.
  destruct H5.
  assumption.
  apply e_app with (val1 := x)(val2 := x0).
  assumption.
  assumption.
  destruct H5.
  apply H6.
  intros.
  unfold normalizes.
  destruct IHD1 with (env := env)(tvm := tvm).
  apply H.
  apply H0.
  destruct H1.
  destruct IHD2 with (env := env)(tvm := tvm).
  apply H.
  apply H0.
  destruct H3.
  exists (v_pair x x0).
  split.
  simpl.
  unfold product.
  exists x.
  exists x0.
  split.
  apply H1.
  split.
  apply H3.
  reflexivity.
  apply e_pair.
  apply H2.
  apply H4.
  intros.
  unfold normalizes.
  destruct IHD with (env := env)(tvm := tvm).
  assumption.
  assumption.
  destruct H1.
  simpl in H1.
  unfold product in H1.
  destruct H1.
  destruct H1.
  destruct H1.
  destruct H3.
  subst.
  exists x0.
  split.
  apply H1.
  apply e_fst with (val2 := x1).
  apply H2.
  intros.
  unfold normalizes.
  destruct IHD with (env := env)(tvm := tvm).
  assumption.
  assumption.
  destruct H1.
  simpl in H1.
  unfold product in H1.
  destruct H1.
  destruct H1.
  destruct H1.
  destruct H3.
  subst.
  exists x1.
  split.
  assumption.
  apply e_snd with (val1 := x0).
  assumption.
  intros.
  unfold normalizes.
  destruct IHD with (env := env)(tvm := tvm).
  apply H.
  apply H0.
  destruct H1.
  exists (v_inl x).
  simpl.
  split.
  apply in_inl_set.
  apply H1.
  apply e_inl.
  apply H2.
  intros.
  unfold normalizes.
  destruct IHD with (env := env)(tvm := tvm).
  apply H.
  apply H0.
  destruct H1.
  exists (v_inr x).
  simpl.
  split.
  apply in_inr_set.
  apply H1.
  apply e_inr.
  apply H2.
  intros.
  unfold normalizes.
  destruct IHD1 with (env := env)(tvm := tvm).
  apply H.
  apply H0.
  destruct H1.
  simpl in H1.
  unfold disj_sum, union in H1.
  destruct H1.
  unfold inl_set in H1.
  destruct H1.
  destruct H1.
  subst.
  destruct IHD2 with (env := extend env x0)(tvm := tvm).
  apply H.
  simpl.
  exists env.
  exists x0.
  split.
  apply H0.
  split.
  apply H1.
  reflexivity.
  exists x.
  destruct H3.
  split.
  apply H3.
  apply e_case_inl with (val := x0).
  apply H2.
  apply H4.
  unfold inr_set in H1.
  destruct H1.
  destruct H1.
  subst.
  destruct IHD3 with (env := extend env x0)(tvm := tvm).
  apply H.
  simpl.
  exists env.
  exists x0.
  split.
  apply H0.
  split.
  apply H1.
  reflexivity.
  exists x.
  destruct H3.
  split.
  apply H3.
  apply e_case_inr with (val := x0).
  apply H2.
  apply H4.
  intros.
  unfold normalizes.
  destruct IHD with (env := env)(tvm := tvm).
  assumption.
  assumption.
  destruct H1.
  exists x.
  split.
  apply subset_inst with (A := semantic_type ty (tvm_extend tvm (semantic_type (t_rec ty) tvm))).
  apply type_fun_subset.
  apply set_eq_inst with (A := semantic_type (type_under_subst ty (sub_single (t_rec ty))) tvm).
  apply semantic_type_under_single_subst.
  assumption.
  assumption.
  apply H2.
  intros.
  unfold normalizes.
  exists (v_rec e env).
  split.
  simpl.
  apply funsp_prefp.
  intros.
  apply backward_closure.
  unfold normalizes in IHD.
  simpl in IHD.
  destruct IHD with (env := extend env (v_rec e env))(tvm := tvm_extend tvm X).
  apply tv_map_extend.
  apply H.
  exists env.
  exists (v_rec e env).
  split.
  apply set_eq_inst with (A := semantic_ctx ctx tvm).
  apply set_eq_sym.
  apply semantic_shift_context.
  apply H0.
  split.
  simpl.
  apply set_eq_inst with (A := funsp X (semantic_type ty' tvm)).
  apply funsp_set_eq.
  apply set_eq_refl.
  apply set_eq_sym.
  apply set_eq_trans with (B := semantic_type ty' (semantic_renaming (ren_shift 1) (tvm_extend tvm X))).
  apply semantic_type_under_renaming.
  simpl.
  setoid_rewrite tvm_pop_0.
  apply set_eq_refl.
  apply H1.
  reflexivity.
  exists x.
  destruct H2.
  split.
  apply H3.
  apply set_eq_inst with (A := funsp (semantic_type ty (tvm_extend tvm X)) (semantic_type (type_under_renaming ty' (ren_shift 1)) (tvm_extend tvm X))).
  apply funsp_set_eq.
  apply set_eq_refl.
  apply set_eq_trans with (B := semantic_type ty' (semantic_renaming (ren_shift 1) (tvm_extend tvm X))).
  apply semantic_type_under_renaming.
  simpl.
  setoid_rewrite tvm_pop_0.
  apply set_eq_refl.
  apply H2.
  apply e_rec.
  Qed.

Corollary normalization (tvc : tv_context) (tvm : tv_map) (ctx : context) (e : expr) (ty : type) (env : environment) :
  of_type tvc ctx e ty -> tv_map_of_ctx tvm tvc -> semantic_ctx ctx tvm env -> normalizes tvm ty env e.
  intro D.
  apply normalization'.
  apply D.
  Qed.

(* Final statement of normalization with empty contexts and environment *)

Corollary norm (e : expr) (ty : type) :
  of_type tv_empty c_empty e ty -> exists val : value, eval empty e val.
  intro.
  assert (normalizes tvm_empty ty empty e).
  apply normalization with (tvc := tv_empty)(ctx := c_empty).
  apply H.
  apply tv_map_empty.
  simpl.
  reflexivity.
  unfold normalizes in H0.
  destruct H0.
  destruct H0.
  exists x.
  apply H1.
  Qed.