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
    (Context.generic -> Proof.context -> Proof.context) ->
    string -> string -> string list -> Context.generic -> Proof.state
  val show_open: local_theory ->
    (Context.generic -> Proof.context -> Proof.context) ->
    string -> string list -> Context.generic -> Proof.state
  val close_inductive: local_theory -> string -> string list -> string ->
    Context.generic -> (string * thm) list * local_theory


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

(*** Pretty-printing ***)

fun pretty_thms ctxt ts =
  map (Display.pretty_thm_item ctxt) ts |> Pretty.fbreaks |> Pretty.block

fun pretty_typs ctxt ts =
  Pretty.block (map (Syntax.pretty_typ ctxt) ts)

fun pretty_terms ctxt ts =
  Pretty.block (map (Syntax.pretty_term ctxt) ts)

fun str_typ ctxt t = Pretty.string_of (pretty_typs ctxt [t])

(** Markup **)

val mark_open_pred = Markup.free
val mark_intro = Markup.skolem
val mark_open_lemma = Markup.free
val mark_typ = Markup.bound

val pretty_pred = Pretty.str #> Pretty.mark mark_open_pred
val pretty_intro = Pretty.str #> Pretty.mark mark_intro
val pretty_lemma = Pretty.str #> Pretty.mark mark_open_lemma
fun pretty_typ ctxt = Syntax.pretty_typ ctxt #> Pretty.mark mark_typ



(*** General Utilities ***)


(** Result Datatype (Result in Rust, Either in Haskell) **)

datatype ('a, 'b) result =
  Err of 'a
| Res of 'b

fun first_res _ err [] = Err err
  | first_res f err (x::xs) =
      case f x of
        SOME r => Res r
      | NONE => first_res f err xs

fun zip_errors [] = []
  | zip_errors (Err x::xs) = x::zip_errors xs
  | zip_errors (Res _::xs) = zip_errors xs

fun zip_results [] = []
  | zip_results (Err _::xs) = zip_results xs
  | zip_results (Res x::xs) = x::zip_results xs



(*** Rewrite Helpers ***)

fun close_forms ctxt i xs As =
  let
    val commons = map #1 xs
    val _ =
      (case duplicates (op =) commons of [] => ()
      | dups => error ("Duplicate local variables " ^ commas_quote dups))
    val frees = rev (fold (Variable.add_free_names ctxt) As (rev commons))
    val types =
      map (Type_Infer.param i o rpair []) (Name.invent Name.context Name.aT (length frees))
    val uniform_typing = the o AList.lookup (op =) (frees ~~ types)

    fun abs_body lev y (Abs (x, T, b)) = Abs (x, T, abs_body (lev + 1) y b)
      | abs_body lev y (t $ u) = abs_body lev y t $ abs_body lev y u
      | abs_body lev y (t as Free (x, T)) =
          if x = y then Type.constraint (uniform_typing x) (Type.constraint T (Bound lev))
          else t
      | abs_body _ _ a = a
    fun close (y, U) B =
      let val B' = abs_body 0 y (Term.incr_boundvars 1 B)
      in if Term.is_dependent B' then Logic.all_const dummyT $ Abs (y, U, B') else B end
    fun close_form A =
      let
        val occ_frees = rev (Variable.add_free_names ctxt A [])
        val bounds = xs @ map (rpair dummyT) (subtract (op =) commons occ_frees)
      in fold_rev close bounds A end
  in map close_form As end

fun prepare vars raw_specss ctxt =
  let
    (*val (vars, vars_ctxt) = ctxt |> Proof_Context.read_vars raw_vars*)
    val (xs, params_ctxt) = ctxt |> Proof_Context.add_fixes vars

    val Asss =
      (map o map) snd raw_specss
      |> (burrow o burrow) (map (Syntax.parse_prop params_ctxt))
    val names = Variable.names_of (params_ctxt |> (fold o fold o fold) Variable.declare_term Asss)
      |> fold Name.declare xs
    val Asss' = #1 ((fold_map o fold_map o fold_map) Term.free_dummy_patterns Asss names)
    val idx = (fold o fold o fold) Term.maxidx_term Asss' ~1 + 1
    val specs =
      (fold_map
        (fn Ass => fn i => (burrow (close_forms params_ctxt i []) Ass, i + 1)) Asss' idx) |> fst
      |> flat |> burrow (Syntax.check_props params_ctxt)
    val specs_ctxt = params_ctxt |> (fold o fold) Variable.declare_term specs

    val (Ts, _) = specs_ctxt |> fold_map Proof_Context.inferred_param xs
    val params = map2 (fn (b, _, mx) => fn T => ((b, T), mx)) vars Ts
    val name_atts = map (fn ((name, atts), _) => (name, map (Attrib.check_src ctxt) atts)) (flat raw_specss)
  in ((params, name_atts ~~ specs), specs_ctxt) end


fun single_spec (a, prop) = [(a, [prop])]
fun the_spec (a, [prop]) = (a, prop)
  | the_spec _ = error "the_spec can't fail"

fun read_spec vars specs =
  prepare vars (map single_spec specs) #>> apsnd (map the_spec)

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
      if is_some typ then
        the typ
      else
        Term.fold_aterms find_typ (snd (hd intros)) NONE |> the
    val vars' = [((Binding.name close_name, ty), NoSyn)]
    fun rename_pred (Free (n, ty)) =
          Free (if n = pred_name then close_name else n, ty)
      | rename_pred x = x
    val intrs' = map (fn (b, t) => (b, Term.map_aterms rename_pred t)) intrs
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
    val thy = Proof_Context.theory_of ctxt
    val cprop = cterm_of thy prop
    val p_as_goal = Goal.init cprop
    val ind_tac = etac ind_thm 1 (* TODO: use real induction *)
  in
    case ind_tac p_as_goal |> Seq.pull of
      NONE => error "rewrite_prop: could not apply induction theorem"
    | SOME (p, _) => (prems_of p |> hd, ctxt)
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
       intros = AList.merge (op =) (op =) (a_intrs, b_intrs)} (* TODO fix op= *)
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
    val prfs =
      case AList.lookup (op =) proofs pred of
        NONE => []
      | SOME l => l
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
      AList.join (op =) (K (AList.merge (op =) (K true))) (a, b) (* TODO fix op= *)
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

val thm_lookup = Symtab.lookup o fst o Data.get

fun thm_update' f k =
  Symtab.map_default (k, empty_thm) f

fun thm_update (f:open_thm -> open_thm) k =
  Data.map (fn (a, b) => (thm_update' f k a, b))


val pred_lookup = Symtab.lookup o snd o Data.get

fun pred_update' f k =
  Symtab.map_default (k, empty_open_pred) f

fun pred_update (f: open_predicate -> open_predicate) k =
  Data.map (fn (a, b) => (a, pred_update' f k b))


fun morph_open_prf phi (assms, thm) =
  (assms, Morphism.thm phi thm)

fun apply_morphism phi context =
  let
    val (thms, preds) = Data.get context
    val thms' = thms |> Symtab.map (K
      (fn Open_Thm {prop, preds, proofs, direct_proof} =>
        Open_Thm {
          prop = Morphism.term phi prop,
          preds = preds,
          proofs = proofs |> map (fn (p, is) =>
            (p, is |> map (fn (i, prf) =>
              (i, morph_open_prf phi prf)))),
          direct_proof =
            case direct_proof of
              SOME prf => SOME (morph_open_prf phi prf)
            | NONE => NONE}))
    val preds' = preds |> Symtab.map (K
      (fn Open_Predicate {typ, thms, intros} =>
        Open_Predicate {
          typ =
            if is_some typ then
              SOME (Morphism.typ phi (the typ))
            else NONE,
          thms = thms,
          intros =
            map (fn (n, i) => (n, Morphism.term phi i)) intros}))
  in
    Data.put (thms', preds') context
  end

(*** Commands ***)

(** Opening Predicates **)

fun open_inductive n t context =
  let
    val ctxt = Context.proof_of context
    val msg = [Pretty.str "Registered open inductive predicate ", pretty_pred n] @
       (case t of
          SOME typ => [Pretty.str " with type ", pretty_typ ctxt typ]
        | NONE => [Pretty.str " without type"])
       |> Pretty.block
  in
    pred_update (pred_add_typ t ctxt msg) n context
  end

fun pred_register (b, t, _) context =
  let
    val ctxt = Context.proof_of context
    val typ =
      if is_some t
      then SOME (Syntax.read_typ ctxt (the t))
      else NONE
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

val () = Outer_Syntax.local_theory @{command_spec "open_inductive"}
          "open inductive predicate definition"
          (Parse.fixes >> open_inductive_cmd)


(** Defining Intros **)

fun add_intro ctxt pred_name intro_name prop context =
  case pred_lookup context pred_name of
    NONE => error ("No such open inductive predicate: " ^ pred_name)
  | SOME (Open_Predicate p) =>
    let
      val _ (* typecheck only*) = prepare_intro pred_name (#typ p) intro_name prop ctxt
    in
      Pretty.block [Pretty.str "Registered introduction rule ", pretty_intro intro_name,
         Pretty.str ": ", pretty_terms ctxt [prop], Pretty.str " for ", pretty_pred pred_name,
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
        val ((_, specs), _) = read_spec [(Binding.name pred_name, #typ pred, NoSyn)] [((Binding.name intro_name, []), raw_prop)] lthy
        val prop = hd specs |> snd
      in
        add_intro lthy pred_name intro_name prop context'
      end
  in
    Local_Theory.declaration {pervasive = false, syntax = false} decl lthy
  end

val ic_parser = Parse.name -- (Parse.name -- (@{keyword ":"} |-- Parse.prop))

val () = Outer_Syntax.local_theory @{command_spec "add_intro"}
          "adds intro rule to open inductive predicate"
          (ic_parser >> add_intro_cmd)


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
    Pretty.block [Pretty.str "Declared open theorem ", pretty_lemma nam, Pretty.str " as ",
        pretty_terms ctxt [prop], Pretty.str " on ",
        Pretty.commas (map pretty_pred opreds) |> Pretty.block]
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
        val ((_, specs), _) = read_spec pred_fixes [((Binding.empty, []), raw_prop)] lthy
        val prop = hd specs |> snd
      in
        open_theorem lthy n prop context'
      end
  in
    Local_Theory.declaration {pervasive = false, syntax = false} decl lthy
  end

val () = Outer_Syntax.local_theory @{command_spec "open_theorem"}
          "declares open theorem"
          (Parse.name -- ((Parse.maybe @{keyword "shows"}) |-- Parse.prop)
           >> open_theorem_cmd)



(** Proving Theorems **)

fun thm_err name = error ("No such theorem: " ^ name)

fun many_thms_err thmss ctxt = error ("More than one theorem proved? Have: " ^
  (thmss |> map (Pretty.string_of o pretty_thms ctxt) |> commas))


fun find_preds context intro_names thm =
  let
    fun get_intrs pred_name =
      case pred_lookup context pred_name of
        SOME (Open_Predicate {intros, ...}) => intros
      | _ => []
    fun match_pred intro_name pred_name =
      case filter (fst #> (curry op =) intro_name) (get_intrs pred_name) of
        [] => NONE
      | i::_ =>
        SOME ((pred_name, maybe_typ context pred_name), (intro_name, snd i))
    val intrs = map (fn iname => first_res (match_pred iname) iname (#preds thm)) intro_names
    val fails = zip_errors intrs
  in
    if not (null fails) then
      Err fails
    else
      Res (zip_results intrs |> AList.group (eq_fst (op =)))
  end

fun intro_err preds intro_name =
  error ("No introduction rule named " ^ intro_name ^ " in " ^ commas preds)

fun save_assms ((p, _), p_assms) = add_assms p_assms p

fun show_intro ctxt t_cont thm_name intro_name assms context =
  let
    val othm =
      (case thm_lookup context thm_name of
         SOME (Open_Thm t) => t
       | NONE => thm_err thm_name)
    val intro_err' = intro_err (#preds othm)
    val assms' =
      (case find_preds context (intro_name::assms) othm of
         Err n => intro_err' (hd n)
       | Res r => r)
    val (pred_name, ty) = hd assms' |> fst
    val intro_spec =  hd assms' |> snd |> hd |> snd
    val (prop, _) = rewrite_prop pred_name ty intro_name intro_spec ctxt (#prop othm)
    val (_, ctxt00) = Proof_Context.add_fixes [(Binding.name pred_name, ty, NoSyn)] ctxt
    val ctxt' = fold save_assms assms' ctxt00
    fun after_qed pred [[thm]] =
          thm_update (add_intro_proof pred intro_name assms thm) thm_name context |> t_cont
      | after_qed _ thmss = many_thms_err thmss ctxt
  in
    Proof.theorem NONE (after_qed pred_name) [[(prop, [])]] ctxt'
  end


fun name_of_bindfix (b, _, _) = Binding.name_of b

fun show_intro_cmd lemma_name intro_name assms lthy =
  let
    val context = Context.Theory (Proof_Context.theory_of lthy)
    fun cont context = Local_Theory.background_theory (K (Context.theory_of context))
    val assms' = map name_of_bindfix assms
  in
    show_intro lthy cont lemma_name intro_name assms' context
  end

fun show_open ctxt t_cont thm_name assms context =
  let
    val open_thm =
      (case thm_lookup context thm_name of
         NONE => thm_err thm_name
       | SOME (Open_Thm t) => t)
    val assms' =
      (case find_preds context assms open_thm of
         Err n => intro_err (#preds open_thm) (hd n)
       | Res r => r)
    val (pred_name, ty) = hd assms' |> fst
    val (_, ctxt00) = Proof_Context.add_fixes [(Binding.name pred_name, ty, NoSyn)] ctxt
    val ctxt' = fold save_assms assms' ctxt00
    fun after_qed [[thm]] = (thm_update (add_direct_proof assms thm) thm_name context) |> t_cont
      | after_qed thmss = many_thms_err thmss
  in
    Proof.theorem NONE after_qed [[(#prop open_thm, [])]] ctxt'
  end

fun show_open_cmd thm_name assms lthy =
  let
    (* TODO figure this out *)
    val context = Context.Theory (Proof_Context.theory_of lthy)
    (*val context = Context.Proof lthy*)
    (*fun cont context' = Local_Theory.declaration {pervasive = false, syntax = false} (fn phi => (fn context => context'))*)
    fun cont context = Local_Theory.background_theory (K (Context.theory_of context))
    val assms' = map name_of_bindfix assms
  in
    show_open lthy cont thm_name assms' context
  end

fun show_open_switch ((thm_name, ""), assms) = show_open_cmd thm_name assms
  | show_open_switch ((thm_name, intro_name), assms) = show_intro_cmd thm_name intro_name assms

val () = Outer_Syntax.local_theory_to_proof @{command_spec "show_open"}
  "shows an open theorem for an intro rule (or directly)"
  (Parse.name -- Scan.optional (@{keyword "for"} |-- Parse.name) "" --
     Scan.optional (@{keyword "assumes"} |-- Parse.fixes) []
   >> show_open_switch)



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

fun make_tac induct i intro_rules =
  etac induct i THEN EVERY1 (map (single #> solve_tac) intro_rules)

fun gen_pname pname =
  implies_intr_hyps #> Thm.generalize ([], [pname]) 2 (* TODO use correct index *)

fun clear_hyps cname ctxt hyp_thms thm =
  let
    val cert = cterm_of (Proof_Context.theory_of ctxt)
    val thm' = (*Assumption.export true ctxt' ctxt thm*) thm
      |> instantiate' [] [SOME (Syntax.read_term ctxt cname |> cert)]
    (*val () = Pretty.block [Pretty.str "have thm: ", pretty_thms ctxt [t']] |> Pretty.writeln
    val () = Pretty.block [Pretty.str "have hyps: ", pretty_thms ctxt hyp_thms] |> Pretty.writeln*)
  in
    thm' |> rule_by_tactic ctxt (REPEAT (solve_tac hyp_thms 1))
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
      (hyps_from_assms a named_intrs, gen_pname pname r))
    val tac =  (map snd named_intrs) ~~ hyp_rules
      |> map (fn (h, (hs, b)) => clear_hyps close_name ctxt (h :: hs) b)
      |> make_tac induct 1
    val thm = Goal.prove ctxt [] [] goal (K tac)
  in
    (name, thm)
  end

fun close_direct ctxt pname ptyp named_intrs close_name (name, prop, (assms, proof)) thms =
  let
    val goal = if pname <> close_name
      then rename_free pname ptyp close_name prop
      else prop
    val missing = get_missing named_intrs assms
    val hyps = hyps_from_assms assms named_intrs
    val hyp_thm = gen_pname pname proof
      |> clear_hyps close_name ctxt hyps
    val tac = etac hyp_thm 1
  in
    if missing = [] then
      (name, Goal.prove ctxt [] [] goal (K tac))::thms
    else
      (warn_missing name missing "introduction rules:"; thms)
  end

fun gen_close lthy pred_name pred intro_names close_name context =
  let
    val intro_specs = map (the o AList.lookup (op =) (#intros pred)) intro_names
    val ({induct, intrs, ...}, lthy') =
      make_inductive pred_name close_name (#typ pred) (intro_names ~~ intro_specs) lthy
    val named_intrs = intro_names ~~ intrs

    val lemma_names = #thms pred
    val lemmas0 = map (thm_lookup context) lemma_names
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
      [Pretty.block ([Pretty.str "Closing inductive predicate ", pretty_pred pred_name,
          Pretty.str " with "] @ Pretty.commas (map pretty_intro intro_names) @ [Pretty.str " as ",
        pretty_pred close_name, Pretty.str "."]),
      Pretty.block ([Pretty.str "Candidates for closing: "] @
        Pretty.commas (map pretty_lemma lemma_names))])));
    (fold (close_lemma lthy') lemmas []
     |> fold (close_direct lthy' pred_name ptyp named_intrs close_name) directs,
     lthy')
  end

fun close_inductive ctxt pred_name intro_names close_name context =
  let
    val pred =
      case pred_lookup context pred_name of
        NONE => error ("Undefined open predicate: " ^ pred_name)
      | SOME (Open_Predicate p) => p
    val pred_intros = #intros pred |> map fst
  in
    case find_first (not o member (op =) pred_intros) intro_names of
      SOME x => error ("No introduction rule named " ^ x ^
        " defined in open predicate " ^ pred_name)
    | NONE => gen_close ctxt pred_name pred intro_names close_name context
  end

fun close_inductive_cmd ((pred_name, intro_binds), close_name) lthy =
  let
    val context = Context.Proof lthy (* TODO morph! *)
    val intro_names = map name_of_bindfix intro_binds
    val (thms, lthy') =
      close_inductive lthy pred_name intro_names close_name context
    fun install (name, thm) =
      let
        val inst_name = name ^ "_" ^ close_name
        val msg = (map Pretty.str ["Installing ", inst_name, ": "]) @ [pretty_thms lthy' [thm]]
          |> Pretty.block
      in
        (Pretty.writeln msg;
         Local_Theory.note ((Binding.name inst_name, []), [thm]) #> snd)
      end
  in
    fold install thms lthy'
  end

val ci_parser =
  (Parse.name -- (@{keyword "assumes"} |-- Parse.fixes) -- (@{keyword "for"} |-- Parse.name))

val () = Outer_Syntax.local_theory @{command_spec "close_inductive"}
          "closes an inductive predicate"
          (ci_parser >> close_inductive_cmd)

end
