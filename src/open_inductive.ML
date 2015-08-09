(*  Title: open_inductive.ML
    Author: Richard Molitor, IPD Snelting, KIT

Open inductive predicates with flexible sets of introduction rules
and open theorems with inductive proofs on a per-introduction-rule basis.
*)

signature OPEN_INDUCTIVE =
sig
  type open_predicate
  type open_thm

  (** helpers **)

  val pred_merge: open_predicate * open_predicate -> open_predicate
  val thm_merge: open_thm * open_thm -> open_thm

  (** interface **)

  val open_inductive: string -> typ option ->
    Context.generic -> Context.generic
  val add_intro: local_theory -> string -> string -> term ->
    Context.generic -> Context.generic
  val open_theorem: local_theory -> string -> term ->
    Context.generic -> Context.generic
  val show_intro: local_theory ->
    string -> string -> string list -> Proof.state
  val show_open: local_theory ->
    string -> string list -> Proof.state
  val show_open_switch: (string * string) * (binding * 'a * 'b) list ->
    Proof.context -> Proof.state
  val close_inductive: local_theory -> string -> string list -> string ->
    (string * thm) list * local_theory


  (** outer syntax **)

  val open_inductive_cmd: (binding * string option * mixfix) list ->
    local_theory -> local_theory
  val add_intro_cmd: string * (string * string) -> local_theory -> local_theory
  val open_theorem_cmd: string * string -> local_theory -> local_theory
  val show_intro_cmd: string -> string -> (binding * string option * mixfix) list -> local_theory -> Proof.state
  val show_open_cmd: string -> (binding * string option * mixfix) list -> local_theory -> Proof.state
  val close_inductive_cmd: (string * (binding * string option * mixfix) list) * string ->
    local_theory -> local_theory
end

structure Open_Inductive : OPEN_INDUCTIVE =
struct

open OI_Fmt

(*** Rewrite Helpers ***)

fun make_inductive pred_name close_name typ intros lthy =
  let
    val intrs = map (fn (n, p) => ((Binding.name n, []), p)) intros
    val monos = []
    val flags =
     {quiet_mode = true, verbose = false, alt_name = Binding.empty,
      coind = false, no_elim = false, no_ind = false, skip_mono = false}
    fun find_typ (Free (n, ty)) ty0 =
          if n = pred_name then SOME ty else ty0
      | find_typ _ ty0 = ty0
    val ty =
      case typ of
        SOME typ => typ
      | NONE => Term.fold_aterms find_typ (snd (hd intros)) NONE |> the
    val vars' = [((Binding.name close_name, ty), NoSyn)]
    val intrs' = map (fn (b, t) => (b, Term.subst_free [(Free (pred_name, ty), Free (close_name, ty))] t)) intrs
  in
    Inductive.gen_add_inductive_i Inductive.add_ind_def flags vars' [] intrs' monos lthy
  end

fun prepare_intro pred_name typ intro spec lthy =
  let
    val ({induct, ...}, _) = make_inductive pred_name pred_name typ [(intro, spec)] lthy
  in
    induct
  end

fun add_assms intros pred_name ctxt =
  let
    val assm_props = map snd intros
    val assm_names = map (fn (name, _) =>
      (Binding.name name |> Binding.qualify true pred_name, [])) intros
    val assms = map (fn (n, thm) => (n, [(thm, [])])) (assm_names ~~ assm_props)
  in
    Proof_Context.add_assms_i Assumption.assume_export assms ctxt
    |> snd
  end

fun rewrite_prop pred t intro_name intro_spec ctxt prop =
  let
    val ind_thm = prepare_intro pred t intro_name intro_spec ctxt
    val prop_as_goal = Thm.cterm_of ctxt prop |> Goal.init
    val ind_tac = etac ind_thm 1 (* TODO: use real induction *)
  in
    case ind_tac prop_as_goal |> Seq.pull of
      NONE => error "rewrite_prop: could not apply induction theorem"
    | SOME (p, ctxt') => Thm.prems_of p |> hd
    (* ctxt' discarded on purpose! *)
  end


(*** Data Structures ***)

(** Open Predicates **)

datatype open_predicate = Open_Predicate of
  {typ: typ option, (* raw_typ of the predicate, must be "... => bool" *)
   thms: string list, (* names of open_theorems  that use this predicate *)
   intros: (string * term) list} (* introduction rules, format: (name * raw_spec) *)

val empty_open_pred = Open_Predicate
  {typ = NONE,
   thms = [],
   intros = []}

fun pred_add_typ typ' ctxt msg (Open_Predicate {typ, thms, intros}) =
  if is_some typ andalso not (typ' = typ) then
    (if is_some typ' then
       error ("Can't re-type predicate, was " ^ (the typ |> str_typ ctxt) ^
         ", would become " ^ (the typ' |> str_typ ctxt))
     else
       error ("Can't delete type from predicate, was " ^ (the typ |> str_typ ctxt)))
  else
    (Pretty.writeln msg;
     Open_Predicate {typ = typ',
      thms = thms,
      intros = intros})

fun pred_add_intro name spec (Open_Predicate {typ, thms, intros}) =
  (Open_Predicate {
    typ = typ,
    thms = thms,
    intros = (name, spec)::intros})

fun pred_add_thm thm_name (Open_Predicate {typ, thms, intros}) =
  Open_Predicate {
    typ = typ,
    thms = thm_name::thms,
    intros = intros}

fun pred_merge (a, b) =
  let
    val Open_Predicate {typ = ta, thms = a_thms, intros = a_intrs} = a
    val Open_Predicate {typ = tb, thms = b_thms, intros = b_intrs} = b
  in
    if ta <> tb then
      a
    else
      Open_Predicate {typ = ta,
       thms = a_thms @ b_thms |> sort_distinct string_ord,
       intros = AList.merge (op =) (op =) (a_intrs, b_intrs)}
        (* TODO fix fst op=: Better choice available once keys are proper bindings *)
        (* TODO fix snd op=: terms up to alpha equality? *)
  end



(** Open Theorems **)

datatype open_thm = Open_Thm of
  {prop: term,
   preds: string list,
   proofs: (string * (string * (string list * thm)) list) list,
   direct_proof: (string list * thm) option}

val empty_thm =
  Open_Thm {prop = @{const True},
    preds = [],
    proofs = [],
    direct_proof = NONE}

fun make_open_thm prop preds =
  Open_Thm {prop = prop,
    preds = preds,
    proofs = [],
    direct_proof = NONE}

fun add_intro_proof pred intro assms thm (Open_Thm {prop, preds, proofs, direct_proof}) =
  let
    val prfs = the_default [] (AList.lookup (op =) proofs pred)
    val prfs' = AList.update (op =) (intro, (assms, thm)) prfs
  in
    Open_Thm {prop = prop,
     preds = preds,
     proofs = AList.update (op =) (pred, prfs') proofs,
     direct_proof = direct_proof}
  end

fun add_direct_proof assms thm (Open_Thm {prop, preds, proofs, ...}) =
  Open_Thm {prop = prop,
   preds = preds,
   proofs = proofs,
   direct_proof = SOME (assms, thm)}

fun thm_merge (Open_Thm a, Open_Thm b) =
  let
    val {prop = pa, preds = a_preds, proofs = a_prfs, direct_proof = da} = a
    val {prop = pb, preds = b_preds, proofs = b_prfs, direct_proof = db} = b
    fun merge_prfs a b =
      AList.join (op =) (K (AList.merge (op =) (K true))) (a, b) (* TODO fix op=, see above *)
  in
    if pa <> pb orelse a_preds <> b_preds then
      Open_Thm a
    else
      Open_Thm {prop = pa,
       preds = a_preds,
       proofs = merge_prfs a_prfs b_prfs,
       direct_proof = if is_some da then da else db}
  end


(* Open Theorem and Open Predicate Data Storage *)

structure Data = Generic_Data
  (type T = open_thm Symtab.table * open_predicate Symtab.table
   val empty = (Symtab.empty, Symtab.empty)
   val extend = I
   val merge = fn ((a1, b1), (a2, b2)) =>
    (Symtab.join (K thm_merge) (a1, a2), Symtab.join (K pred_merge) (b1, b2)))

val thm_lookup' = Symtab.lookup o fst o Data.get o Context.Proof

fun thm_update' f k =
  Symtab.map_default (k, empty_thm) f

fun thm_update (f:open_thm -> open_thm) k =
  Data.map (fn (a, b) => (thm_update' f k a, b))


val pred_lookup = Symtab.lookup o snd o Data.get

val pred_lookup' = pred_lookup o Context.Proof

fun pred_update' f k =
  Symtab.map_default (k, empty_open_pred) f

fun pred_update (f: open_predicate -> open_predicate) k =
  Data.map (fn (a, b) => (a, pred_update' f k b))


fun morph_open_prf phi (assms, thm) =
  (assms, (*Morphism.thm phi*) thm)

fun apply_morphism phi =
  let
    val map_thms = Symtab.map (K
      (fn Open_Thm {prop, preds, proofs, direct_proof} =>
        Open_Thm {
          prop = Morphism.term phi prop,
          preds = preds,
          proofs = proofs |> map (fn (p, is) =>
            (p, is |> map (fn (i, prf) =>
              (i, morph_open_prf phi prf)))),
          direct_proof = Option.map (morph_open_prf phi) direct_proof}))
    val map_preds  = Symtab.map (K
      (fn Open_Predicate {typ, thms, intros} =>
        Open_Predicate {
          typ = Option.map (Morphism.typ phi) typ,
          thms = thms,
          intros =
            map (fn (n, i) => (n, (*Morphism.term phi*) i)) intros}))
  in
    Data.map (fn (thms, preds) => (map_thms thms, map_preds preds))
  end

(*** Commands ***)

(** Opening Predicates **)

fun open_inductive n t context =
  let
    val ctxt = Context.proof_of context
    val msg = [Pretty.str "Registered open inductive predicate ", color_pred_name n] @
       (case t of
          SOME typ => [Pretty.str " with type ", color_typ ctxt typ]
        | NONE => [Pretty.str " without type"])
       |> Pretty.block
  in
    pred_update (pred_add_typ t ctxt msg) n context
  end

fun pred_register (b, t, _) context =
  let
    val ctxt = Context.proof_of context
    val typ = Option.map (Syntax.read_typ ctxt) t
  in
    open_inductive (Binding.name_of b) typ context
  end

fun open_inductive_cmd fixes =
  let
    fun decl phi context =
      apply_morphism phi context
      |> fold pred_register fixes
  in
    Local_Theory.declaration {pervasive = false, syntax = false} decl
  end



(** Defining Intros **)

fun add_intro ctxt pred_name intro_name prop context =
  case pred_lookup context pred_name of
    NONE => error ("No such open inductive predicate: " ^ pred_name)
  | SOME (Open_Predicate p) =>
    let
      val _ (* typecheck only*) = prepare_intro pred_name (#typ p) intro_name prop ctxt
    in
      Pretty.block [Pretty.str "Registered introduction rule ", color_intro_name intro_name,
         Pretty.str ": ", Syntax.pretty_term ctxt prop, Pretty.str " for ", color_pred_name pred_name,
         Pretty.str "."]
       |> Pretty.writeln;
      (pred_update (pred_add_intro intro_name prop)) pred_name context
    end


fun add_intro_cmd (pred_name, (intro_name, raw_prop)) lthy =
  let
    fun decl phi context =
      let
        val context' = apply_morphism phi context
        val pred =
          case pred_lookup context' pred_name of
            NONE => error ("No such open inductive predicate: " ^ pred_name)
          | SOME (Open_Predicate p) => p
        val ((_, specs), _) = Specification.check_spec [(Binding.name pred_name, #typ pred, NoSyn)] [((Binding.name intro_name, []), Syntax.parse_prop lthy raw_prop)] lthy
        val prop = hd specs |> snd
      in
        add_intro lthy pred_name intro_name prop context'
      end
  in
    Local_Theory.declaration {pervasive = false, syntax = false} decl lthy
  end





(** Defining Theorems **)

fun maybe_typ context name =
  case pred_lookup context name of
    (SOME (Open_Predicate {typ, ...})) =>
      typ
  | _ => NONE

fun thm_reg_preds nam = fold (pred_update (pred_add_thm nam))

fun open_theorem ctxt nam prop context =
  let
    fun known (Free (n, _)) = Long_Name.explode n |> List.last |> cons (* TODO *)
      | known _ = I
    val opreds = Term.fold_aterms known prop []
      |> filter (pred_lookup context #> is_some)
      |> sort_distinct string_ord
  in
    Pretty.block [Pretty.str "Declared open theorem ", color_lemma_name nam, Pretty.str " as ",
        Syntax.pretty_term ctxt prop, Pretty.str " on ",
        Pretty.commas (map color_pred_name opreds) |> Pretty.block]
    |> Pretty.writeln;
    thm_reg_preds nam opreds context
    |> thm_update (K (make_open_thm prop opreds)) nam
  end


fun open_theorem_cmd (n, raw_prop) lthy =
  let
    fun decl phi context =
      let
        val context' = apply_morphism phi context
        val pred_names = Data.get context' |> snd |> Symtab.keys
        val pred_fixes = pred_names |> map (fn p =>
          (Binding.name p,
           maybe_typ context p,
           NoSyn))
        val ((_, specs), _) = Specification.check_spec pred_fixes [((Binding.empty, []), Syntax.parse_prop lthy raw_prop)] lthy
        val prop = hd specs |> snd
      in
        open_theorem lthy n prop context'
      end
  in
    Local_Theory.declaration {pervasive = false, syntax = false} decl lthy
  end





(** Proving Theorems **)

fun thm_err name = error ("No such theorem: " ^ name)

fun many_thms_err thmss ctxt = error ("More than one theorem proved? Have: " ^
  (map (Pretty.string_of o Pretty.block o map (Display.pretty_thm ctxt)) thmss |> commas))


fun find_preds context intro_names thm =
  let
    fun get_intrs pred_name =
      case pred_lookup' context pred_name of
        SOME (Open_Predicate {intros, ...}) => intros
      | _ => []
    fun match_pred intro_name pred_name =
      case filter (fst #> (curry op =) intro_name) (get_intrs pred_name) of
        [] => NONE
      | i::_ =>
        SOME ((pred_name, maybe_typ (Context.Proof context) pred_name), (intro_name, snd i))
    val intrs = map (fn iname => Result.first (match_pred iname) iname (#preds thm)) intro_names
    val fails = Result.zip_errors intrs
  in
    if not (null fails) then
      Result.Error fails
    else
      Result.Ok (Result.zip_results intrs |> AList.group (eq_fst (op =)))
  end

fun intro_err preds intro_name =
  error ("No introduction rule named " ^ intro_name ^ " in " ^ commas preds)

fun save_assms ((p, _), p_assms) = add_assms p_assms p

fun gen_pname pname =
  implies_intr_hyps #> Drule.generalize ([], [pname])


fun show_intro ctxt thm_name intro_name assms =
  let
    val othm =
      (case thm_lookup' ctxt thm_name of
         SOME (Open_Thm t) => t
       | NONE => thm_err thm_name)
    val intro_err' = intro_err (#preds othm)
    val assms' =
      (case find_preds ctxt (intro_name::assms) othm of
         Result.Error n => intro_err' (hd n)
       | Result.Ok r => r)
    val (pred_name, ty) = hd assms' |> fst
    val intro_spec =  hd assms' |> snd |> hd |> snd
    val prop = rewrite_prop pred_name ty intro_name intro_spec ctxt (#prop othm)
    val (_, ctxt00) = Proof_Context.add_fixes [(Binding.name pred_name, ty, NoSyn)] ctxt
    val ctxt' = fold save_assms assms' ctxt00
    fun after_qed pred [[thm]] =
      let val generalized_thm = gen_pname pred_name thm
        fun decl phi context =
          apply_morphism phi context |>
          thm_update (add_intro_proof pred intro_name assms generalized_thm) thm_name
      in
        Local_Theory.declaration {pervasive = false, syntax = false} decl
      end
      | after_qed _ thmss = many_thms_err thmss ctxt
  in
    Proof.theorem NONE (after_qed pred_name) [[(prop, [])]] ctxt'
  end


fun name_of_bindfix (b, _, _) = Binding.name_of b

fun show_intro_cmd lemma_name intro_name assms lthy =
  let
    val assms' = map name_of_bindfix assms
  in
    show_intro lthy lemma_name intro_name assms'
  end

fun show_open ctxt thm_name assms =
  let
    val open_thm =
      (case thm_lookup' ctxt thm_name of
         NONE => thm_err thm_name
       | SOME (Open_Thm t) => t)
    val assms' =
      (case find_preds ctxt assms open_thm of
         Result.Error n => intro_err (#preds open_thm) (hd n)
       | Result.Ok r => r)
    val (pred_name, ty) = hd assms' |> fst
    val (_, ctxt00) = Proof_Context.add_fixes [(Binding.name pred_name, ty, NoSyn)] ctxt
    val ctxt' = fold save_assms assms' ctxt00
    fun after_qed [[thm]] =
        let val generalized_thm = gen_pname pred_name thm
        fun decl phi context =
          apply_morphism phi context |>
          thm_update (add_direct_proof assms generalized_thm) thm_name
        in
          Local_Theory.declaration {pervasive = false, syntax = false} decl
        end
      | after_qed thmss = many_thms_err thmss
  in
    Proof.theorem NONE after_qed [[(#prop open_thm, [])]] ctxt'
  end

fun show_open_cmd thm_name assms lthy =
  let
    val assms' = map name_of_bindfix assms
  in
    show_open lthy thm_name assms'
  end

fun show_open_switch ((thm_name, ""), assms) = show_open_cmd thm_name assms
  | show_open_switch ((thm_name, intro_name), assms) = show_intro_cmd thm_name intro_name assms





(** Closing Predicates **)

fun rename_free name typ name' =
  let
    fun rename (v as Free (n, typ0)) =
          if n = name then
            Free (name', if is_some typ then the typ else typ0)
          else v
      | rename a = a
  in
    map_aterms rename
  end

fun make_tac ctxt induct i intro_rules =
  etac induct i THEN EVERY1 (map (single #> solve_tac ctxt) intro_rules)

fun clear_hyps cname ctxt hyp_thms thm =
  let
    val cert = Thm.cterm_of ctxt
    val thm' = (*Assumption.export true ctxt' ctxt thm*) thm
      |> instantiate' [] [SOME (Syntax.read_term ctxt cname |> cert)]
    (*val () = Pretty.block [Pretty.str "have thm: ", pretty_thms ctxt [t']] |> Pretty.writeln
    val () = Pretty.block [Pretty.str "have hyps: ", pretty_thms ctxt hyp_thms] |> Pretty.writeln*)
  in
    thm' |> rule_by_tactic ctxt (REPEAT (solve_tac ctxt hyp_thms 1))
  end

fun hyps_from_assms assms named_intros =
  filter (member (fn ((b, _), a) => a = b) assms) named_intros |> map snd

fun warn_missing thm_name intro_names what =
  warning ("Cannot close open theorem " ^ quote thm_name ^ ", missing " ^ what ^
    " " ^ (commas intro_names))

fun get_missing named_intros assms =
  filter (AList.lookup (op =) named_intros #> is_none) assms

fun finish_proof pname close_name name ptyp prop induct rules named_intrs ctxt =
  let
    val goal =
      if pname <> close_name
        then rename_free pname ptyp close_name prop
        else prop
    val hyp_rules = rules |> map (fn (a, r) =>
      (hyps_from_assms a named_intrs, r))
    val tac =  (map snd named_intrs) ~~ hyp_rules
      |> map (fn (h, (hs, b)) => clear_hyps close_name ctxt (h :: hs) b)
      |> make_tac ctxt induct 1
    val thm = Goal.prove ctxt [] [] goal (K tac)
  in
    (name, thm)
  end

fun close_direct ctxt pname ptyp named_intrs close_name (name, prop, (assms, thm)) thms =
  let
    val goal = if pname <> close_name
      then rename_free pname ptyp close_name prop
      else prop
    val missing = get_missing named_intrs assms
    val hyps = hyps_from_assms assms named_intrs
    val hyp_thm = clear_hyps close_name ctxt hyps thm
    val tac = etac hyp_thm 1
  in
    if null missing then
      (name, Goal.prove ctxt [] [] goal (K tac))::thms
    else
      (warn_missing name missing "introduction rules:"; thms)
  end

fun gen_close lthy pred_name pred intro_names close_name =
  let
    val intro_specs = map (the o AList.lookup (op =) (#intros pred)) intro_names
    val ({induct, intrs, ...}, lthy') =
      make_inductive pred_name close_name (#typ pred) (intro_names ~~ intro_specs) lthy
    val named_intrs = intro_names ~~ intrs

    val lemma_names = #thms pred
    val lemmas0 = map (thm_lookup' lthy) lemma_names
      |> zip_options lemma_names

    val lemmas = filter (fn (_, Open_Thm {direct_proof = NONE, ...}) => true | _ => false) lemmas0
      |> map (fn (n, Open_Thm {prop, proofs, ...}) =>
        (n, prop, case AList.lookup (op =) proofs pred_name of NONE => [] | SOME l => l))

    val directs = filter (fn (_, Open_Thm {direct_proof = SOME _, ...}) => true | _ => false) lemmas0
      |> map (fn (n, Open_Thm {prop, direct_proof, ...}) => (n, prop, the direct_proof))

    val ptyp = #typ pred

    fun close_lemma lthy (name, prop, proofs) thms =
      let
        val rs = map (AList.lookup (op =) proofs) intro_names
          |> filter is_some
          |> map the
        val missing_assms = (flat oo map) (fn (a, _) => get_missing named_intrs a) rs
      in
        if length rs <> length intro_names then
          (warn_missing name
            (intro_names |> filter (is_none o (AList.lookup (op =) proofs))) "proofs for";
           thms)
        else if not (null missing_assms) then
          (warn_missing name missing_assms "introduction rules:"; thms)
        else
          (finish_proof pred_name close_name name ptyp prop induct rs named_intrs lthy)::thms
      end
  in
    (Pretty.writeln (Pretty.block (Pretty.breaks
      [Pretty.block ([Pretty.str "Closing inductive predicate ", color_pred_name pred_name,
          Pretty.str " with "] @ Pretty.commas (map color_intro_name intro_names) @ [Pretty.str " as ",
        color_pred_name close_name, Pretty.str "."]),
      Pretty.block ([Pretty.str "Candidates for closing: "] @
        Pretty.commas (map color_lemma_name lemma_names))])));
    (fold (close_lemma lthy') lemmas []
     |> fold (close_direct lthy' pred_name ptyp named_intrs close_name) directs,
     lthy')
  end

fun close_inductive ctxt pred_name intro_names close_name =
  let
    val pred =
      case pred_lookup' ctxt pred_name of
        NONE => error ("Undefined open predicate: " ^ pred_name)
      | SOME (Open_Predicate p) => p
    val pred_intros = #intros pred |> map fst
  in
    case find_first (not o member (op =) pred_intros) intro_names of
      SOME x => error ("No introduction rule named " ^ x ^
        " defined in open predicate " ^ pred_name)
    | NONE => gen_close ctxt pred_name pred intro_names close_name
  end

fun close_inductive_cmd ((pred_name, intro_binds), close_name) lthy =
  let
    val intro_names = map name_of_bindfix intro_binds
    val (thms, lthy') =
      close_inductive lthy pred_name intro_names close_name
    fun install (name, thm) =
      let
        val binding = Binding.qualify false close_name (Binding.name name)
        val msg = [Pretty.str "Installing ", Binding.pretty binding, Pretty.str ": "] @ [Display.pretty_thm lthy' thm]
          |> Pretty.block
      in
        (Pretty.writeln msg;
         Local_Theory.note ((binding, []), [thm]) #> snd)
      end
  in
    fold install thms lthy'
  end

end
