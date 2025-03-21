From JSON Require Export JSON.
From RocqCandy Require Export All.

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
  induction l; simpl in *; intros; eauto; try lia.
  destruct H; subst; eauto; try lia.
  eapply (IHl _ init f) in H.
  lia.
Qed.

Lemma json_depth_in_respects_array : forall jl j,
  In j jl ->
  json_depth j < json_depth (JSON__Array jl).
Proof.
  induction jl; simpl; intros.
  - inversion H.
  - destruct H.
    + subst; simpl; lia.
    + eapply (fold_right_max_lt_max jl _ 0 json_depth) in H.
      try lia.
Qed.

Lemma json_depth_in_respects_object : forall jl j,
  In j jl ->
  json_depth (snd j) < json_depth (JSON__Object jl).
Proof.
  induction jl; simpl; intros.
  - inversion H.
  - destruct H.
    + subst; simpl; lia.
    + eapply (fold_right_max_lt_max jl _ 0 (fun x => json_depth (snd x))) in H.
      try lia.
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
    intros x F; destruct x eqn:?; eauto;
    [ eapply fO | eapply fA ]; intros; eapply F;
    [ eapply json_depth_in_respects_object | eapply json_depth_in_respects_array ]; eauto.
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
    intros x F; destruct x eqn:?; eauto;
    [ eapply fO | eapply fA ]; intros; eapply F;
    [ eapply json_depth_in_respects_object | eapply json_depth_in_respects_array ]; eauto.
  }
  assert (well_founded (fun j1 j2 => json_depth j1 < json_depth j2)). {
    apply well_founded_ltof.
  }
  eapply well_founded_induction_type; eauto.
Qed.

Fixpoint safe_zip {A B} (l1 : list A) (l2 : list B) : unit + list (A * B) :=
  match l1, l2 with
  | nil, _ => raise tt
  | _, nil => raise tt
  | a1 :: l1, a2 :: l2 => 
    match safe_zip l1 l2 with
    | inl _ => raise tt
    | inr l => inr ((a1, a2) :: l)
    end
  end.

Definition map_eqb_eqb {A B} `{EqClass A} (eqb : B -> B -> bool) 
    : FMap A B -> FMap A B -> bool :=
  fix F l1 l2 :=
    match l1, l2 with
    | nil, nil => true
    | (k1, v1) :: l1, (k2, v2) :: l2 => 
      (if equiv_dec k1 k2 then true else false) &&
      eqb v1 v2 &&
      F l1 l2
    | _, _ => false
    end.

Theorem map_eqb_eq {A B : Type} `{EqClass A} (eqb : B -> B -> bool) : 
  forall m1,
  (forall x b2, In x m1 -> eqb (snd x) b2 = true <-> (snd x) = b2) ->
  forall m2, map_eqb_eqb eqb m1 m2 = true <-> m1 = m2.
Proof.  
  induction m1; destruct m2; split; intros; simpl in *; eauto; try congruence.
  - destruct a; try congruence.
  - ff; eq_crush.
    erewrite (H0 (a, b)) in *; eq_crush;
    erewrite IHm1 in *; eq_crush.
  - ff; eq_crush; eauto;
    try erewrite (H0 (a0, b)) in *; eq_crush;
    try erewrite IHm1 in *; eq_crush.
Qed.

Definition list_eqb_eqb {A} (eqb : A -> A -> bool) 
    : list A -> list A -> bool :=
  fix F l1 l2 :=
    match l1, l2 with
    | nil, nil => true
    | a1 :: l1, a2 :: l2 => 
      eqb a1 a2 &&
      F l1 l2
    | _, _ => false
    end.

Theorem list_eqb_eq {B : Type} (eqb : B -> B -> bool) : 
  forall m1,
  (forall b1 b2, In b1 m1 -> eqb b1 b2 = true <-> b1 = b2) ->
  forall m2, list_eqb_eqb eqb m1 m2 = true <-> m1 = m2.
Proof.  
  induction m1; destruct m2; split; intros; simpl in *; eauto; try congruence.
  - ff; eq_crush.
    erewrite H in *; eq_crush;
    erewrite IHm1 in *; eq_crush.
  - ff; eq_crush; eauto;
    try erewrite H in *; eq_crush;
    try erewrite IHm1 in *; eq_crush.
Qed.

Fixpoint eqb_json `{EqClass Z, EqClass string} (j1 j2 : json) : bool :=
  match j1, j2 with
  | JSON__Object o1, JSON__Object o2 =>
    map_eqb_eqb eqb_json o1 o2
  | JSON__Array a1, JSON__Array a2 =>
    list_eqb_eqb eqb_json a1 a2
  | JSON__String s1, JSON__String s2 => eqb s1 s2 
  | JSON__Number n1, JSON__Number n2 => eqb n1 n2
  | JSON__True, JSON__True => true
  | JSON__False, JSON__False => true
  | JSON__Null, JSON__Null => true
  | _, _ => false
  end.

Lemma eqb_json_eq : forall `{Heqz : EqClass Z, Heqs : EqClass string} j1 j2, 
  eqb_json j1 j2 = true <-> eq j1 j2.
Proof.
  induction j1 using json_ind_deep;
  destruct j2; simpl in *; split; try congruence; eq_crush;
  intros; eauto;
  try erewrite map_eqb_eq in *; ff; eauto;
  try erewrite list_eqb_eq in *; ff; eauto;
  try erewrite H in *; eauto.
Qed.

Global Instance EqClass_json `{EqClass Z, EqClass string} : EqClass json := {
  eqb := eqb_json ;
  eqb_eq := eqb_json_eq
}.