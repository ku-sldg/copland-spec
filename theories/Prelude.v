From JSON Require Export JSON.
From RocqCandy Require Export All.
Import ResultNotation.

Fixpoint json_depth (j : json) : nat :=
  match j with
  | JSON__Object l => S (fold_right (fun x acc => max acc (json_depth (snd x))) 0 l)
  | JSON__Array l => S (fold_right (fun x acc => max acc (json_depth x)) 0 l)
  | _ => 1
  end.

Lemma fold_right_max_lt_max : forall {A} l (x : A) init f,
  In x l ->
  f x <= fold_right (fun x acc => max acc (f x)) init l.
Proof.
  induction l; ff a, l;
  eapply (IHl _ init f) in H0; ff l.
Qed.

Lemma json_depth_in_respects_array : forall jl j,
  In j jl ->
  json_depth j < json_depth (JSON__Array jl).
Proof.
  induction jl; ff l, a.
Qed.

Lemma json_depth_in_respects_object : forall jl j,
  In j jl ->
  json_depth (snd j) < json_depth (JSON__Object jl).
Proof.
  induction jl; ff l, a.
Qed.

Theorem json_ind_deep (P : json -> Prop)
  (fO : forall l : list (string * json), 
    (forall x, In x l -> P (snd x)) -> P (JSON__Object l))
  (fA : forall l : list json, 
    (forall x, In x l -> P x) -> P (JSON__Array l))
  (fS : forall s : string, P (JSON__String s))
  (fZ : forall n : Z, P (JSON__Number n))
  (fT : P JSON__True)
  (fF : P JSON__False)
  (fN : P JSON__Null) :
  forall j : json, P j.
Proof.  
  assert (forall x : json, (forall y : json, (fun j1 j2 => json_depth j1 < json_depth j2) y x -> P y) -> P x). {
    ltac1:(intros x F; destruct x eqn:?; eauto;
    [ eapply fO | eapply fA ]; intros; eapply F;
    [ eapply json_depth_in_respects_object | eapply json_depth_in_respects_array ]; eauto).
  }
  assert (well_founded (fun j1 j2 => json_depth j1 < json_depth j2)). {
    apply well_founded_ltof.
  }
  eapply well_founded_ind; eauto.
Qed.

Theorem json_rect_deep (P : json -> Type)
  (fO : forall l : list (string * json), 
    (forall x, In x l -> P (snd x)) -> P (JSON__Object l))
  (fA : forall l : list json, 
    (forall x, In x l -> P x) -> P (JSON__Array l))
  (fS : forall s : string, P (JSON__String s))
  (fZ : forall n : Z, P (JSON__Number n))
  (fT : P JSON__True)
  (fF : P JSON__False)
  (fN : P JSON__Null) :
  forall j : json, P j.
Proof.  
  assert (forall x : json, (forall y : json, (fun j1 j2 => json_depth j1 < json_depth j2) y x -> P y) -> P x). {
    ltac1:(intros x F; destruct x eqn:?; eauto;
    [ eapply fO | eapply fA ]; intros; eapply F;
    [ eapply json_depth_in_respects_object | eapply json_depth_in_respects_array ]; eauto).
  }
  assert (well_founded (fun j1 j2 => json_depth j1 < json_depth j2)). {
    apply well_founded_ltof.
  }
  eapply well_founded_induction_type; eauto.
Qed.

Fixpoint safe_zip {A B} (l1 : list A) (l2 : list B) : Result (list (A * B)) unit :=
  match l1, l2 with
  | nil, _ => err tt
  | _, nil => err tt
  | a1 :: l1, a2 :: l2 => 
    l <- safe_zip l1 l2 ;;
    res ((a1, a2) :: l)
  end.

Definition map_eqb_eqb {A B} `{DecEq A} (dec_eq_b : IDecEq B) : IDecEq (Map A B).
  ref (fix F l1 l2 :=
    match l1, l2 with
    | nil, nil => left eq_refl
    | (k1, v1) :: l1', (k2, v2) :: l2' => 
      _ (dec_eq k1 k2) (dec_eq_b v1 v2) (F l1' l2')
    | _, _ => right _
    end);  try congruence;
  clear F; intros; 
  destruct x, x0, x1; ff.
Defined.

Definition list_eqb_eqb {A} (dec_eq_a : IDecEq A) : IDecEq (list A).
  ref (fix F l1 l2 :=
    match l1, l2 with
    | nil, nil => left _
    | a1 :: l1, a2 :: l2 => 
      _ (dec_eq_a a1 a2) (F l1 l2)
    | _, _ => right _
    end); try congruence; clear F; ff;
    destruct x, x0; ff.
Defined.

Global Instance DecEq_json `{DecEq Z, DecEq string} : DecEq json.
  ref (Build_DecEq _ (fix F (j1 j2 : json) :=
  match j1, j2 with
  | JSON__Object o1, JSON__Object o2 => _ (map_eqb_eqb F o1 o2)
  | JSON__Array a1, JSON__Array a2 => _ (list_eqb_eqb F a1 a2)
  | JSON__String s1, JSON__String s2 => _ (dec_eq s1 s2)
  | JSON__Number n1, JSON__Number n2 => _ (dec_eq n1 n2)
  | JSON__True, JSON__True => left _
  | JSON__False, JSON__False => left _
  | JSON__Null, JSON__Null => left _
  | _, _ => right _
  end)); clear F; ff; destruct x; ff.
Defined.