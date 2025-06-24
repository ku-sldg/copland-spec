From RocqCandy Require Import All.

From CoplandSpec Require Import Term_Defs_Core String_Vars.

Global Instance DecEq_ASP_PARAMS `{DecEq ASP_ID, DecEq Plc, DecEq TARG_ID, DecEq ASP_ARGS} : DecEq ASP_PARAMS.
build_deq.
Defined.

Global Instance DecEq_ASP `{DecEq ASP_PARAMS, DecEq Plc}: DecEq ASP.
build_deq.
Defined.

Global Instance DecEq_SP : DecEq SP.
build_deq.
Defined.

Global Instance DecEq_Split `{DecEq SP} : DecEq Split.
build_deq.
Defined.

Global Instance DecEq_Term `{DecEq Plc, DecEq Split, DecEq ASP} : DecEq Term.
ref (Build_DecEq _ _).
intros x; induction x;
intros y; destruct y; ff;
try (decdec_eq ()).
- destruct (IHx y); ff.
- destruct (IHx1 y1), (IHx2 y2); ff.
- destruct (IHx1 y1), (IHx2 y2); ff.
- destruct (IHx1 y1), (IHx2 y2); ff.
Defined.

Global Instance DecEq_EvidenceT `{DecEq N_ID, DecEq Plc, DecEq ASP_PARAMS} : DecEq EvidenceT.
ref (Build_DecEq _ _).
intros x; induction x;
intros y; destruct y; ff;
try (decdec_eq ()).
- destruct (IHx y); ff.
- destruct (IHx y); ff.
- destruct (IHx y); ff.
- destruct (IHx1 y1), (IHx2 y2); ff.
Defined.

(* Jsonifiable Instances *)
Lemma json_get_object_result_always_smaller : forall js s js',
  JSON_get_Object s js = res js' ->
  lt (JSON_depth js') (JSON_depth js).
Proof.
  induction js; simpl in *; intuition; 
  jsonifiable_hammer.
  unfold depth_js_map.
  eapply fold_right_ind; ff l.
  right; exists (s, js'); simpl in *; split; try lia; eauto.
  eapply (@lookup_impl_in string _ DecEq_string); ff.
Defined.

Lemma json_all_map_elements_smaller : forall js m s,
  m ![ s ] = Some js ->
  lt (JSON_depth js) (JSON_depth (JSON_Object m)).
Proof.
  induction m; simpl in *; intuition; try congruence;
  jsonifiable_hammer; ff u, l, a.
Defined.

Lemma json_all_array_elements_smaller : forall js ls,
  In js ls ->
  lt (JSON_depth js) (JSON_depth (JSON_Array ls)).
Proof.
  induction ls; ff l, a.
Defined.

Global Instance Jsonifiable_ASP_ARGS : Jsonifiable ASP_ARGS. 
eapply Build_Jsonifiable with 
  (to_JSON := (fun x => x)) 
  (from_JSON := (fun x => res x)).
intuition; simpl in *;
jsonifiable_hammer.
Defined.

Definition ASP_PARAMS_to_JSON `{Jsonifiable ASP_ARGS} (t : ASP_PARAMS) : JSON := 
    match t with
    | asp_paramsC asp_id args plc targ_id => 
        JSON_Object [
          (STR_ASP_ID, JSON_String (to_string asp_id));
          (STR_ASP_ARGS, (to_JSON args));
          (STR_ASP_PLC, JSON_String (to_string plc));
          (STR_ASP_TARG_ID, JSON_String (to_string targ_id))
        ]
    end.

Definition ASP_PARAMS_from_JSON `{Jsonifiable ASP_ARGS} (js : JSON) : Result ASP_PARAMS string :=
  asp_id  <- JSON_get_string STR_ASP_ID js ;;
  args    <- JSON_get_Object STR_ASP_ARGS js ;;
  plc     <- JSON_get_string STR_ASP_PLC js ;;
  targ    <- JSON_get_string STR_ASP_TARG_ID js ;;

  asp_id' <- from_string asp_id ;;
  args'   <- from_JSON args ;;
  plc'    <- from_string plc ;;
  targ'   <- from_string targ ;;
  res (asp_paramsC asp_id' args' plc' targ').

Global Instance Jsonifiable_ASP_Params `{Jsonifiable ASP_ARGS} : Jsonifiable ASP_PARAMS. 
eapply Build_Jsonifiable with 
  (to_JSON := ASP_PARAMS_to_JSON) 
  (from_JSON := ASP_PARAMS_from_JSON).
unfold ASP_PARAMS_to_JSON; 
unfold ASP_PARAMS_from_JSON;
intuition; simpl in *;
jsonifiable_hammer.
Defined.


Local Open Scope string_scope.

(* JSONification for constructors *)
Definition noArgConstructor_to_JSON (type_name : string) (cons_name : string) : JSON := 
  JSON_Object [((type_name ++ type_sep ++ type_string_constant), JSON_String cons_name)]. 

Definition oneArgConstructor_to_JSON (type_name : string) (cons_name : string) (inner:JSON) : JSON := 
    JSON_Object [
      ((type_name ++ type_sep ++ type_string_constant), JSON_String cons_name);
      ((type_name ++ type_sep ++ body_string_constant), inner)
    ].

Definition multiArgConstructor_to_JSON (type_name : string) (cons_name : string) (ls:list JSON) : JSON := 
    JSON_Object [
      ((type_name ++ type_sep ++ type_string_constant), JSON_String cons_name);
      ((type_name ++ type_sep ++ body_string_constant), (JSON_Array ls))
    ].

Definition constructor_to_JSON (type_name : string) (cons_name : string) (ls:list JSON) : JSON := 
  match ls with 
  | [] => noArgConstructor_to_JSON type_name cons_name 
  | [v] => oneArgConstructor_to_JSON type_name cons_name v 
  | _ => multiArgConstructor_to_JSON type_name cons_name ls
  end.

Definition constructor_body_from_JSON_gen (type_name:string) (js:JSON) 
    : list JSON :=
  match (JSON_get_Object (type_name ++ type_sep ++ body_string_constant) js) with
  | res (JSON_Array ls) => ls  (* 2+ constructor args case *)
  | res jv => [jv]             (* 1 arg case *)
  | err _ => nil                   (* 0 args case *)
  end.

Definition from_JSON_gen {A:Type} (type_name:string) 
  (cmap: (Map string (JSON -> (Result A string)))) 
    : JSON -> Result A string := 
  fun js => 
    match (JSON_get_Object (type_name ++ type_sep ++ type_string_constant) js) as m' return m' = (JSON_get_Object (type_name ++ type_sep ++ type_string_constant) js) -> Result A string with
    | res (JSON_String cons_name) =>
      match (cmap ![ cons_name ]) with 
      | Some f => fun Heq => f js
      | None => fun _ => err err_str_json_unrecognized_constructor
      end
    | res _ => fun _ => err err_str_json_no_constructor_name_string
    | err e => fun _ => err e
    end eq_refl.

Definition FWD_to_string (t : FWD) : string := 
  match t with
  | REPLACE => replace_name_constant
  | WRAP    => wrap_name_constant
  | UNWRAP  => unwrap_name_constant
  | EXTEND  => extend_name_constant
  end.

Definition constructor_from_JSON {A:Type} (type_name:string) 
  (f:(list JSON) -> Result A string) : (JSON -> Result A string) := 
(fun js => f (constructor_body_from_JSON_gen type_name js)).

Definition constructor_body_from_JSON_gen_rec {top_js:JSON} (type_name:string) : { ls : list JSON | (forall y : JSON, In y ls -> JSON_depth y < JSON_depth top_js) }.
destruct (JSON_get_Object (type_name ++ type_sep ++ body_string_constant) top_js) eqn:?.
- destruct j. 
  * (* object, so 1 args case *) 
    exists ([JSON_Object m]); simpl in *.
    intuition; subst.
    eapply json_get_object_result_always_smaller; eauto.
  * (* array so multiple args *) 
    exists l; simpl in *; intuition.
    find_eapply_lem_hyp json_get_object_result_always_smaller;
    eapply PeanoNat.Nat.lt_trans > [ | eauto];
    eapply json_all_array_elements_smaller; eauto.
  * (* string so 1 arg *) 
    exists ([JSON_String s]); simpl in *.
    intuition; subst.
    eapply json_get_object_result_always_smaller; eauto.
  * (* nat so 1 arg *) 
    exists ([JSON_Nat n]); simpl in *.
    intuition; subst.
    eapply json_get_object_result_always_smaller; eauto.
  * (* boolean so 1 arg *) 
    exists ([JSON_Boolean b]); simpl in *.
    intuition; subst.
    eapply json_get_object_result_always_smaller; eauto.
- (* no body, must be 0 args *) 
  exists nil; ff.
Defined.

Definition constructor_from_JSON_rec {A:Type} {top_js : JSON} (type_name:string) 
  (f: { ls : list JSON | (forall y : JSON, In y ls -> JSON_depth y < JSON_depth top_js) } -> Result A string) : Result A string := 
f (@constructor_body_from_JSON_gen_rec top_js type_name).

Definition FWD_from_string (s : string) : Result FWD string :=
  if (String.eqb s replace_name_constant)
  then res REPLACE
  else if (String.eqb s wrap_name_constant)
  then res WRAP
  else if (String.eqb s unwrap_name_constant)
  then res UNWRAP
  else if (String.eqb s extend_name_constant)
  then res EXTEND
  else err err_str_fwd_from_string.

Theorem from_JSON_gen_constructor_to_JSON_works : forall {A : Type} tname cname ls jsmap (f : JSON -> Result A string) v,
  jsmap ![ cname ] = Some f ->
  f (constructor_to_JSON tname cname ls) = v ->
  from_JSON_gen tname jsmap (constructor_to_JSON tname cname ls) = v.
Proof.
  induction jsmap; ff;
  unfold constructor_to_JSON, noArgConstructor_to_JSON, 
      oneArgConstructor_to_JSON, multiArgConstructor_to_JSON,
      from_JSON_gen in *; ff.
Qed.

Lemma string_app_helper : forall s1 s2 s3,
  s1 ++ s2 = s1 ++ s3 <->
  s2 = s3.
Proof.
  induction s1; simpl in *; intuition; eauto.
  - invc H; eapply IHs1; eauto.
  - subst; eauto.
Qed.

Theorem constructor_from_JSON_to_JSON_works : forall {A : Type} tname cname ls (f : list JSON -> Result A string) v,
  f ls = v ->
  ~ (exists v', ls = [JSON_Array v']) ->
  constructor_from_JSON tname f (constructor_to_JSON tname cname ls) = v.
Proof.
  intuition; unfold constructor_from_JSON, constructor_body_from_JSON_gen, constructor_to_JSON,
    noArgConstructor_to_JSON, oneArgConstructor_to_JSON,
    multiArgConstructor_to_JSON in *; ff;
  try (erewrite string_app_helper in e; 
    unfold type_string_constant, body_string_constant in *; ff; fail).
  ltac1:(exfalso); eauto.
Qed.

Global Instance Stringifiable_FWD : Stringifiable FWD.
eapply Build_Stringifiable with 
  (to_string := FWD_to_string)
  (from_string := FWD_from_string).
intuition; simpl in *;
unfold FWD_to_string, FWD_from_string; ff.
Defined.

Definition EvOutSig_to_JSON `{Jsonifiable nat} (t : EvOutSig) : JSON := 
  let type_const := ev_out_sig_name_constant ++ type_sep ++ type_string_constant in
  let body_const := ev_out_sig_name_constant ++ type_sep ++ body_string_constant in
  match t with
  | OutN n => JSON_Object 
    [ (type_const, JSON_String outn_name_constant); 
      (body_const, to_JSON n)]
  | OutUnwrap => JSON_Object 
    [(type_const, JSON_String outunwrap_name_constant)]
  end.

Definition EvOutSig_from_JSON `{Jsonifiable nat} (js : JSON) : Result EvOutSig string :=
  let type_const := ev_out_sig_name_constant ++ type_sep ++ type_string_constant in
  let body_const := ev_out_sig_name_constant ++ type_sep ++ body_string_constant in
  match (JSON_get_Object type_const js) with
  | res (JSON_String cons_name) =>
    if (String.eqb cons_name outunwrap_name_constant) 
    then res OutUnwrap
    else if (String.eqb cons_name outn_name_constant) 
    then match js with
        | JSON_Object [
            _;
            (_, n_js)
          ] =>
            n_js <- from_JSON n_js ;;
            res (OutN n_js)
        | _ => err err_str_json_parsing_outn
        end
    else err err_str_evoutsig_json_constructor
  | res _ => err err_str_json_no_constructor_name_string
  | err e => err e
  end.

Global Instance Jsonifiable_EvOutSig `{Jsonifiable nat} : Jsonifiable EvOutSig.
eapply Build_Jsonifiable with 
  (to_JSON := EvOutSig_to_JSON)
  (from_JSON := EvOutSig_from_JSON).
unfold EvOutSig_from_JSON, EvOutSig_to_JSON; 
induction a; jsonifiable_hammer.
Defined.

Definition EvSig_to_JSON `{Jsonifiable EvOutSig, Stringifiable FWD} (t : EvSig) : JSON := 
  let '(ev_arrow fwd in_sig out_sig) := t in
  JSON_Object [
    (fwd_name_constant, JSON_String (to_string fwd));
    (ev_in_sig_name_constant, 
      JSON_String (match in_sig with
      | InAll => all_name_constant
      | InNone => none_name_constant
      end));
    (ev_out_sig_name_constant, to_JSON out_sig)].

Definition EvSig_from_JSON `{Jsonifiable EvOutSig, Stringifiable FWD} (js : JSON) : Result EvSig string :=
  fwd_js <- JSON_get_string fwd_name_constant js ;;
  in_sig_js <- JSON_get_string ev_in_sig_name_constant js ;;
  out_sig_js <- JSON_get_Object ev_out_sig_name_constant js ;;

  fwd <- from_string fwd_js ;;
  in_sig <- 
    (if (String.eqb in_sig_js all_name_constant) 
    then res InAll
    else if (String.eqb in_sig_js none_name_constant) 
    then res InNone
    else err err_str_invalid_evinsig_json) ;;
  out_sig <- from_JSON out_sig_js ;;

  res (ev_arrow fwd in_sig out_sig).

Global Instance Jsonifiable_EvSig `{Jsonifiable EvOutSig, Stringifiable FWD} : Jsonifiable EvSig.
eapply Build_Jsonifiable with
(to_JSON := EvSig_to_JSON)
(from_JSON := EvSig_from_JSON);
unfold EvSig_from_JSON, EvSig_to_JSON;
destruct a; ff u;
jsonifiable_hammer.
Defined.

Fixpoint EvidenceT_to_JSON `{Jsonifiable nat, Stringifiable Plc, Jsonifiable ASP_PARAMS} (e : EvidenceT) : JSON := 
  match e with
  | mt_evt=> constructor_to_JSON evidencet_name_constant mt_name_constant []
  | nonce_evt n => 
      constructor_to_JSON evidencet_name_constant nonce_evt_name_constant 
        [(to_JSON n)]
  | asp_evt plc ps e' => 
      constructor_to_JSON evidencet_name_constant asp_evt_name_constant 
        [(JSON_String (to_string plc)); (to_JSON ps); EvidenceT_to_JSON e']
  | left_evt e' => 
      constructor_to_JSON evidencet_name_constant left_evt_name_constant
        [(EvidenceT_to_JSON e')]
  | right_evt e' => 
      constructor_to_JSON evidencet_name_constant right_evt_name_constant
        [(EvidenceT_to_JSON e')]
  | split_evt e1 e2 => 
      constructor_to_JSON evidencet_name_constant split_evt_name_constant 
        [(EvidenceT_to_JSON e1); (EvidenceT_to_JSON e2)]
  end.

Fixpoint EvidenceT_from_JSON `{Jsonifiable nat, Stringifiable Plc, Jsonifiable ASP_PARAMS} (js : JSON) : Result EvidenceT string :=
    let type_name := evidencet_name_constant in
    match (JSON_get_Object (type_name ++ type_sep ++ type_string_constant) js) with
    | res (JSON_String cons_name) =>
      if (String.eqb cons_name mt_name_constant) 
      then res mt_evt
      else if (String.eqb cons_name nonce_evt_name_constant) 
      then match js with
          | JSON_Object [
              _;
              (_, n_js)
            ] =>
              n_js <- from_JSON n_js ;;
              res (nonce_evt n_js)
          | _ => err err_str_json_parsing_failure_wrong_number_args
          end
      else if (String.eqb cons_name asp_evt_name_constant) 
      then match js with
          | JSON_Object [
              _;
              (_, JSON_Array [ JSON_String plc; asp_par; ev' ])
            ] =>
              plc <- from_string plc ;;
              asp_par <- from_JSON asp_par ;;
              ev' <- EvidenceT_from_JSON ev' ;;
              res (asp_evt plc asp_par ev')
          | _ => err err_str_json_parsing_failure_wrong_number_args
          end 
      else if (String.eqb cons_name left_evt_name_constant)
      then match js with
          | JSON_Object [
              _;
              (_, ev')
           ] =>
              ev' <- EvidenceT_from_JSON ev' ;;
              res (left_evt ev')
          | _ => err err_str_json_parsing_failure_wrong_number_args
          end 
      else if (String.eqb cons_name right_evt_name_constant)
      then match js with
          | JSON_Object [
              _;
              (_, ev')
           ] =>
              ev' <- EvidenceT_from_JSON ev' ;;
              res (right_evt ev')
          | _ => err err_str_json_parsing_failure_wrong_number_args
          end 
      else if (String.eqb cons_name split_evt_name_constant) 
      then match js with
          | JSON_Object [
              _;
              (_, JSON_Array [ ev1; ev2 ])
           ] =>
              ev1 <- EvidenceT_from_JSON ev1 ;;
              ev2 <- EvidenceT_from_JSON ev2 ;;
              res (split_evt ev1 ev2)
          | _ => err err_str_json_parsing_failure_wrong_number_args
          end 
      else err err_str_json_invalid_constructor_name
    | res _ => err err_str_json_no_constructor_name_string
    | err e => err e
    end.

Global Instance Jsonifiable_EvidenceT `{Stringifiable Plc, Jsonifiable ASP_ARGS, Jsonifiable nat, Jsonifiable ASP_PARAMS} : Jsonifiable EvidenceT.
eapply Build_Jsonifiable with (to_JSON := EvidenceT_to_JSON) (from_JSON := EvidenceT_from_JSON).
induction a; ff u; jsonifiable_hammer.
Defined.

Global Instance Stringifiable_SP : Stringifiable SP := {
  to_string := (fun sp => 
                  match sp with
                  | ALL => all_name_constant
                  | NONE => none_name_constant
                  end);
  from_string := (fun s => 
                    if (String.eqb s all_name_constant)
                    then res ALL
                    else if (String.eqb s none_name_constant)
                    then res NONE
                    else err err_str_json_parsing_SP);
  canonical_stringification := fun s => match s with
                                        | ALL => eq_refl
                                        | NONE => eq_refl
                                        end
}.

Definition ASP_to_JSON `{Stringifiable Plc, Jsonifiable ASP_ARGS} (t : ASP) : JSON := 
  match t with
  | NULL => constructor_to_JSON STR_ASP null_name_constant []
  (* | CPY => constructor_to_JSON STR_ASP copy_name_constant [] *)
  | APPR => constructor_to_JSON STR_ASP appr_name_constant []
  | ASPC ps => 
      constructor_to_JSON STR_ASP aspc_name_constant 
        [(to_JSON ps)]
  | SIG => constructor_to_JSON STR_ASP sig_name_constant []
  | HSH => constructor_to_JSON STR_ASP hsh_name_constant []
  | ENC q => 
      constructor_to_JSON STR_ASP enc_name_constant 
        [(JSON_String (to_string q))]
  end.

Definition ASP_from_JSON_map `{Stringifiable Plc, Jsonifiable ASP_ARGS}: Map string (JSON -> (Result ASP string)) := 
  [(null_name_constant, constructor_from_JSON STR_ASP (fun _ => res NULL));
   (* (copy_name_constant, constructor_from_JSON STR_ASP (fun _ => res CPY)); *)
   (appr_name_constant, constructor_from_JSON STR_ASP (fun _ => res APPR));
   (aspc_name_constant, constructor_from_JSON STR_ASP 
      (fun ljs =>
        match ljs with
        | [ps_js] => 
            ps <- from_JSON ps_js ;;
            res (ASPC ps)
        | _ => err err_str_json_parsing_ASPC
        end));
   (sig_name_constant, constructor_from_JSON STR_ASP (fun _ => res SIG));
   (hsh_name_constant, constructor_from_JSON STR_ASP (fun _ => res HSH));
   (enc_name_constant, constructor_from_JSON STR_ASP 
      (fun ljs => 
        match ljs with
        | [JSON_String n_js] => 
          n <- from_string n_js ;;
          res (ENC n)
        | _ => err err_str_json_parsing_failure_wrong_number_args
        end))].

Definition ASP_from_JSON `{Jsonifiable ASP_ARGS} (js : JSON) : Result ASP string :=
   from_JSON_gen STR_ASP ASP_from_JSON_map js.

Global Instance Jsonifiable_ASP `{Jsonifiable ASP_ARGS}: Jsonifiable ASP.
eapply (Build_Jsonifiable) with 
  (to_JSON := ASP_to_JSON)
  (from_JSON := ASP_from_JSON).
induction a; try (ff; fail);
try (unfold ASP_from_JSON, ASP_to_JSON, from_JSON_gen; ff; 
  try (unfold aspc_name_constant in *);
  try (unfold appr_name_constant in *);
  try (unfold null_name_constant in *);
  try (unfold sig_name_constant in *);
  try (unfold hsh_name_constant in *);
  try (unfold enc_name_constant in *); ff).
- induction a; unfold constructor_from_JSON, constructor_body_from_JSON_gen; ff u;
  unfold ASP_PARAMS_from_JSON in *; ff u; jsonifiable_hammer.
- unfold constructor_from_JSON, constructor_body_from_JSON_gen; ff u;
  unfold ASP_PARAMS_from_JSON in *; ff u; jsonifiable_hammer.
Defined.

Global Instance Jsonifiable_Split : Jsonifiable Split := {
  to_JSON := (fun '(s1, s2) => 
                JSON_Object [
                  (split1_name_constant, JSON_String (to_string s1));
                  (split2_name_constant, JSON_String (to_string s2))
                ]);
  from_JSON := (fun js => 
                  match (JSON_get_string split1_name_constant js), (JSON_get_string split2_name_constant js) with
                  | res s1, res s2 => 
                    s1 <- from_string s1 ;;
                    s2 <- from_string s2 ;;
                    res (s1, s2)
                  | _, _ => err err_str_json_parsing_failure_wrong_number_args
                  end);
  canonical_jsonification := fun '(s1, s2) => 
                              match s1, s2 with
                              | ALL, ALL => eq_refl
                              | NONE, NONE => eq_refl
                              | _, _ => eq_refl
                              end
}.

Fixpoint Term_to_JSON `{Jsonifiable ASP, Jsonifiable Split} (t : Term) : JSON := 
  match t with
  | asp a => constructor_to_JSON STR_TERM asp_name_constant [(to_JSON a)]
  | att p t' => constructor_to_JSON STR_TERM att_name_constant 
      [(JSON_String (to_string p)); (Term_to_JSON t')]
  | lseq t1 t2 => constructor_to_JSON STR_TERM lseq_name_constant
      [(Term_to_JSON t1); (Term_to_JSON t2)]
  | bseq sp t1 t2 => constructor_to_JSON STR_TERM bseq_name_constant
      [(to_JSON sp); (Term_to_JSON t1); (Term_to_JSON t2)]
  | bpar sp t1 t2 => constructor_to_JSON STR_TERM bpar_name_constant
      [(to_JSON sp); (Term_to_JSON t1); (Term_to_JSON t2)]
  end.

Fixpoint Term_from_JSON `{Jsonifiable ASP, Jsonifiable Split} (js : JSON) : Result Term string :=
    let type_name := STR_TERM in
    let type_str := type_name ++ type_sep ++ type_string_constant in
    let body_str := type_name ++ type_sep ++ body_string_constant in
    match (JSON_get_Object type_str js) with
    | res (JSON_String cons_name) =>
      if (String.eqb cons_name asp_name_constant) 
      then 
        asp_js <- (JSON_get_Object body_str js) ;;
        asp_val <- from_JSON asp_js ;;
        res (asp asp_val)
      else if (String.eqb cons_name att_name_constant) 
      then match js with
        | (JSON_Object [
            _;
            (_, JSON_Array [JSON_String plc; term'])
          ]) =>
            plc_val <- from_string plc ;;
            term_val <- (Term_from_JSON term') ;;
            res (att plc_val term_val)
        | _ => err err_str_json_parsing_failure_wrong_number_args
        end
      else if (String.eqb cons_name lseq_name_constant) 
      then match js with
        | JSON_Object [
            _;
            (_, JSON_Array [ term1; term2 ])
         ] =>
            term1_val <- (Term_from_JSON term1) ;;
            term2_val <- (Term_from_JSON term2) ;;
            res (lseq term1_val term2_val)
        | _ => err err_str_json_parsing_failure_wrong_number_args
        end
      else if (String.eqb cons_name bseq_name_constant) 
      then match js with
        | JSON_Object [
            _;
            (_, JSON_Array [ sp; term1; term2 ])
          ] =>
            sp_val <- from_JSON sp ;;
            term1_val <- (Term_from_JSON term1) ;;
            term2_val <- (Term_from_JSON term2) ;;
            res (bseq sp_val term1_val term2_val)
        | _ => err err_str_json_parsing_failure_wrong_number_args
        end
      else if (String.eqb cons_name bpar_name_constant) 
      then match js with
        | JSON_Object [
            _;
            (_, JSON_Array [ sp; term1; term2 ])
         ] =>
            sp_val <- from_JSON sp ;;
            term1_val <- (Term_from_JSON term1) ;;
            term2_val <- (Term_from_JSON term2) ;;
            res (bpar sp_val term1_val term2_val)
        | _ => err err_str_json_parsing_failure_wrong_number_args
        end
      else err err_str_json_invalid_constructor_name
    | res _ => err err_str_json_invalid_constructor_name
    | err e => err e
    end.

Global Instance Jsonifiable_Term `{Jsonifiable ASP, Jsonifiable Split} : Jsonifiable Term. 
eapply Build_Jsonifiable with (to_JSON := Term_to_JSON) (from_JSON := Term_from_JSON).
induction a; 
repeat (ff u;
jsonifiable_hammer; repeat (rewrite canonical_jsonification in *); eauto).
Defined.

Global Instance Jsonifiable_RawEv : Jsonifiable RawEv. 
  eapply Build_Jsonifiable with (to_JSON := (fun ev => 
                JSON_Object [
                  (rawev_name_constant, JSON_Array (map (fun bs => JSON_String (to_string bs)) ev))
                ]))
  (from_JSON := (fun js => 
                  match (JSON_get_Array rawev_name_constant js) with
                  | res js' => 
                      result_map (fun js' => 
                                    match js' with
                                    | JSON_String s => 
                                        match (from_string s) with
                                        | res bs => res bs
                                        | err e => err e
                                        end
                                    | _ => err err_str_json_invalid_constructor_name
                                    end) js'
                  | err e => err e
                  end)).
induction a; ff u; jsonifiable_hammer.
Defined.

Global Instance Jsonifiable_Evidence `{Jsonifiable RawEv, Jsonifiable EvidenceT}: Jsonifiable Evidence.
eapply Build_Jsonifiable with
  (to_JSON := 
    (fun e => let '(evc r et) := e in
      JSON_Array [ (to_JSON r); (to_JSON et) ])
  )
  (from_JSON := 
    (fun j => 
      match j with
      | JSON_Array [ r_js; et_js ] =>
          r <- from_JSON r_js ;;
          et <- from_JSON et_js ;;
          res (evc r et)
      | _ => err err_str_invalid_evidence_json
      end)
  ); 
destruct a; jsonifiable_hammer.
Defined.

Global Instance Jsonifiable_GlobalContext `{Stringifiable ASP_ID, 
  Jsonifiable (Map ASP_ID ASP_ID), Jsonifiable ASP_Type_Env} : Jsonifiable GlobalContext. 
eapply Build_Jsonifiable with 
  (to_JSON := (fun g => 
                JSON_Object [
                  (asp_types_name_constant, to_JSON (asp_types g));
                  (asp_comps_name_constant, to_JSON (asp_comps g))
                ]))
  (from_JSON := (fun j =>
    ats <- (JSON_get_Object asp_types_name_constant j) ;;
    acs <- (JSON_get_Object asp_comps_name_constant j) ;;
    ats <- from_JSON ats ;;
    acs <- from_JSON acs ;;
    res {| asp_types := ats; asp_comps := acs |}
    )); solve_json.
Defined.

Close Scope string_scope.