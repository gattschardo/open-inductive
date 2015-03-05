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

  val open_inductive: Proof.context -> string -> string option ->
    open_predicate Symtab.table -> open_predicate Symtab.table
  val add_intro: Proof.context -> string -> string -> string ->
    open_predicate Symtab.table -> open_predicate Symtab.table
  val open_theorem: Proof.context -> string -> string ->
    open_predicate Symtab.table -> open_thm Symtab.table ->
    open_predicate Symtab.table * open_thm Symtab.table
  val show_intro: Proof.context ->
    (open_thm Symtab.table -> Proof.context -> Proof.context) ->
    string -> string -> string list -> open_predicate Symtab.table ->
    open_thm Symtab.table -> Proof.state
  val show_open: Proof.context ->
    (open_thm Symtab.table -> Proof.context -> Proof.context) ->
    string -> string list -> open_predicate Symtab.table ->
    open_thm Symtab.table -> Proof.state
  val close_inductive: Proof.context -> string -> string list -> string ->
    open_predicate Symtab.table -> open_thm Symtab.table ->
    Proof.context * (string * thm) list


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
  map (Display.pretty_thm_item ctxt) ts |> Pretty.separate "\n" |> Pretty.block

fun pretty_typs ctxt ts =
  Pretty.block (map (Syntax.pretty_typ ctxt) ts)

fun pretty_terms ctxt ts =
  Pretty.block (map (Syntax.pretty_term ctxt) ts)

fun str_typ ctxt t = Pretty.string_of (pretty_typs ctxt [t |> Syntax.read_typ ctxt])

(** Markup **)

val mark_open_pred = Markup.free
val mark_intro = Markup.skolem
val mark_open_lemma = Markup.free
val mark_typ = Markup.bound

val pretty_pred = Pretty.str #> Pretty.mark mark_open_pred
val pretty_intro = Pretty.str #> Pretty.mark mark_intro
val pretty_lemma = Pretty.str #> Pretty.mark mark_open_lemma
fun pretty_typ ctxt t = Syntax.read_typ ctxt t
  |> Syntax.pretty_typ ctxt |> Pretty.mark mark_typ



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

fun make_inductive pred_name close_name t raw_intros lthy =
  let
    val bind = Binding.name
    fun bind' s = (bind s, [])
    val intros = map (fn (n, p) => (bind' n, p)) raw_intros
    val cnames = [(bind pred_name, t, NoSyn)]
    val pnames = []
    val monos = []
    val flags =
     {quiet_mode = true, verbose = false, alt_name = Binding.empty,
      coind = false, no_elim = false, no_ind = false, skip_mono = false}
    val ((vars, intrs), _) = lthy
      |> Proof_Context.set_mode Proof_Context.mode_abbrev
      |> Specification.read_spec (cnames @ pnames) intros
    val ((_, ty), syn) = hd vars
    val vars' = [((Binding.name close_name, ty), syn)]
    fun rename_pred (Free (n, ty)) =
          Free (if n = pred_name then close_name else n, ty)
      | rename_pred x = x
    val intrs' = map (fn (b, t) => (b, Term.map_aterms rename_pred t)) intrs
  in
    Inductive.gen_add_inductive_i Inductive.add_ind_def flags vars' [] intrs' monos lthy
  end

fun prepare_intro pred_name t intro s lthy =
  let
    val ({induct, ...}, lthy') = make_inductive pred_name pred_name t [(intro, s)] lthy
  in
   (lthy', induct)
  end

fun add_assms intros pred_name t ctxt =
  let
    val pred_fix = [(Binding.name pred_name, t, NoSyn)]
    val prop = map (fn (_, spec) => ((Binding.empty, []), spec)) intros
    val ((_, ps), ctxt') = ctxt
      (*|> Proof_Context.set_mode Proof_Context.mode_abbrev*)
      |> Specification.read_spec pred_fix prop
    val assm_thms = map snd ps
    val assm_names = map (fn (name, _) =>
      (Binding.name name |> Binding.qualify true pred_name, [])) intros
    val assms = map (fn (n, thm) => (n, [(thm, [])])) (assm_names ~~ assm_thms)
  in
    Proof_Context.add_assms_i Assumption.assume_export assms ctxt'
    |> snd
  end

fun rewrite_prop pred t intro_name intro_spec ctxt p =
  let
    val (ctxt', ind_thm) = prepare_intro pred t intro_name intro_spec ctxt
    val pp = Syntax.read_prop ctxt' p
    val thy = Proof_Context.theory_of ctxt
    val cp = cterm_of thy pp
    val p_as_goal = Goal.init cp
    val ind_tac = etac ind_thm 1 (* TODO: use real induction *)
  in
    case ind_tac p_as_goal |> Seq.pull of
      NONE => error "rewrite_prop: could not apply induction theorem"
    | SOME (p, _) => (prems_of p |> hd, ctxt)
  end


(*** Data Structures ***)

(** Open Predicates **)

type thm_handle = string
type intro = string * string

type open_predicate =
  {typ: string option,
   thms: thm_handle list,
   intros: intro list}

val empty_open_pred =
  {typ = NONE,
   thms = [],
   intros = []}

fun pred_add_typ t ctxt msg {typ, thms, intros} =
  if is_some typ andalso not (t = typ) then
    (if is_some t then
       error ("Can't re-type predicate, was " ^ (the typ |> str_typ ctxt) ^
         ", would become " ^ (the t |> str_typ ctxt))
     else
       error ("Can't delete type from predicate, was " ^ (the typ |> str_typ ctxt)))
  else
    (Pretty.writeln msg;
     {typ = t,
      thms = thms,
      intros = intros})

fun pred_add_intro n i {typ, thms, intros} =
  {typ = typ,
   thms = thms,
   intros = (n, i)::intros}

fun pred_add_thm t {typ, thms, intros} =
  {typ = typ,
   thms = t::thms,
   intros = intros}

val get_intro_name = fst
val get_intro_spec = snd

fun pred_merge (a, b) =
  let
    val {typ = ta, thms = a_thms, intros = a_intrs} = a
    val {typ = tb, thms = b_thms, intros = b_intrs} = b
  in
    if ta <> tb then
      a
    else
      {typ = ta,
       thms = a_thms @ b_thms |> sort_distinct string_ord,
       intros = AList.merge (op =) (op =) (a_intrs, b_intrs)}
  end

structure Open_Preds = Theory_Data
  (type T = open_predicate Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.join (K pred_merge))

val pred_lookup = Symtab.lookup o Open_Preds.get

fun pred_update' f k =
  Symtab.map_default (k, empty_open_pred) f

fun pred_update f k thy =
  Open_Preds.put (pred_update' f k (Open_Preds.get thy)) thy



(** Open Theorems **)

type open_proof = string list * Proof.context * thm
type intro_proof = string * (string * open_proof) list

type open_thm =
  {prop: string,
   preds: string list,
   proofs: intro_proof list,
   direct_proof: open_proof option}

val empty_thm =
  {prop = "",
   preds = [],
   proofs = [],
   direct_proof = NONE}

fun make_open_thm prop preds =
  {prop = prop,
   preds = preds,
   proofs = [],
   direct_proof = NONE}

fun add_intro_proof pred intro assms ctxt thm {prop, preds, proofs, direct_proof} =
  let
    val prfs =
      case AList.lookup (op =) proofs pred of
        NONE => []
      | SOME l => l
    val prfs' = AList.update (op =) (intro, (assms, ctxt, thm)) prfs
  in
    {prop = prop,
     preds = preds,
     proofs = AList.update (op =) (pred, prfs') proofs,
     direct_proof = direct_proof}
  end

fun add_direct_proof assms ctxt thm {prop, preds, proofs, ...} =
  {prop = prop,
   preds = preds,
   proofs = proofs,
   direct_proof = SOME (assms, ctxt, thm)}

fun thm_merge (a, b) =
  let
    val {prop = pa, preds = a_preds, proofs = a_prfs, direct_proof = da} = a
    val {prop = pb, preds = b_preds, proofs = b_prfs, direct_proof = db} = b
    fun merge_prfs a b =
      AList.join (op =) (K (AList.merge (op =) (K true))) (a, b)
  in
    if pa <> pb orelse a_preds <> b_preds then
      a
    else
      {prop = pa,
       preds = a_preds,
       proofs = merge_prfs a_prfs b_prfs,
       direct_proof = if is_some da then da else db}
  end

structure Open_Thms = Theory_Data
  (type T = open_thm Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.join (K thm_merge))

val thm_lookup = Symtab.lookup o Open_Thms.get

fun thm_update' k f =
  Symtab.map_default (k, empty_thm) f

fun thm_update (k:string) (f:open_thm -> open_thm) thy =
  Open_Thms.put (thm_update' k f (Open_Thms.get thy)) thy



(*** Commands ***)

(** Opening Predicates **)

fun pred_register' update ctxt n t =
  let
    val msg = [Pretty.str "Registered open inductive predicate ", pretty_pred n] @
       (case t of
          SOME typ => [Pretty.str " with type ", pretty_typ ctxt typ, Pretty.str "."]
        | NONE => [Pretty.str " without type."])
       |> Pretty.block
  in
    update (pred_add_typ t ctxt msg) n
  end

val open_inductive = pred_register' pred_update'


fun pred_register (b, t, _) thy =
  let
    val ctxt = Proof_Context.init_global thy
  in
    pred_register' pred_update ctxt (Binding.name_of b) t thy
  end


val open_inductive_cmd =
  fold (pred_register #> Local_Theory.background_theory)

val oi_parser = Parse.fixes

val () = Outer_Syntax.local_theory @{command_spec "open_inductive"}
          "open inductive predicate definition"
          (oi_parser >> open_inductive_cmd)


(** Defining Intros **)

fun gen_intro_register lookup update ctxt pred_name intro_name raw_prop tab_or_thy =
  case lookup tab_or_thy pred_name of
    NONE => error ("No such open inductive predicate: " ^ pred_name)
  | SOME p =>
    let
      val prop = Syntax.read_term ctxt raw_prop
      val _ (* typecheck only*) = prepare_intro pred_name (#typ p) intro_name raw_prop ctxt
    in
      Pretty.block [Pretty.str "Registered introduction rule ", pretty_intro intro_name,
         Pretty.str ": ", pretty_terms ctxt [prop], Pretty.str " for ", pretty_pred pred_name,
         Pretty.str "."]
       |> Pretty.writeln;
      (update (pred_add_intro intro_name raw_prop)) pred_name tab_or_thy
    end

fun add_intro ctxt name n raw_prop tab =
  gen_intro_register Symtab.lookup pred_update' ctxt name n raw_prop tab


fun add_intro_cmd (pred_name, (intro_name, prop)) lthy =
  Local_Theory.background_theory
    (gen_intro_register pred_lookup pred_update lthy pred_name intro_name prop) lthy

val ic_parser = Parse.name -- (Parse.name -- (Parse.$$$ ":" |-- Parse.prop))

val () = Outer_Syntax.local_theory @{command_spec "add_intro"}
          "adds intro rule to open inductive predicate"
          (ic_parser >> add_intro_cmd)


(** Defining Theorems **)

fun thm_reg_preds p_update nam = fold (p_update (pred_add_thm nam))

fun thm_register' p_lookup ctxt nam raw_prop tab_or_thy =
  let
    val prop = raw_prop |> Syntax.read_term ctxt
    fun known (Free (n, _)) = Long_Name.explode n |> List.last |> cons
      | known _ = I
    val opreds = Term.fold_aterms known prop []
      |> filter (p_lookup tab_or_thy #> is_some)
      |> sort_distinct string_ord
    val pred_fixes = opreds |> map (fn p =>
      (Binding.name p, p_lookup tab_or_thy p |> the |> #typ, NoSyn))
    val _ (* typecheck only *) =
      Specification.read_spec pred_fixes [((Binding.empty, []), raw_prop)] ctxt
  in
    Pretty.block [Pretty.str "Declared open theorem ", pretty_lemma nam, Pretty.str " as ",
        pretty_terms ctxt [prop], Pretty.str " on ",
        Pretty.commas (map pretty_pred opreds) |> Pretty.block]
    |> Pretty.writeln;
    opreds
  end

fun open_theorem ctxt nam raw_prop p_tab t_tab =
  let
    val opreds = thm_register' Symtab.lookup ctxt nam raw_prop p_tab
  in
    (thm_reg_preds pred_update' nam opreds p_tab,
     thm_update' nam (K (make_open_thm raw_prop opreds)) t_tab)
  end


fun thm_register nam raw_prop thy =
  let
    val ctxt = Proof_Context.init_global thy
    val opreds = thm_register' pred_lookup ctxt nam raw_prop thy
  in
    thm_reg_preds pred_update nam opreds thy
    |> thm_update nam (K (make_open_thm raw_prop opreds))
  end


fun open_theorem_cmd (n, prop) =
   Local_Theory.background_theory (thm_register n prop)

val ot_parser = Parse.name --
   ((Parse.maybe (Parse.$$$ "shows")) |-- Parse.prop)

val () = Outer_Syntax.local_theory @{command_spec "open_theorem"}
          "declares open theorem"
          (ot_parser >> open_theorem_cmd)



(** Proving Theorems **)

fun thm_err name = error ("No such theorem: " ^ name)

fun many_thms_err thmss ctxt = error ("More than one theorem proved? Have: " ^
  (thmss |> map (Pretty.string_of o pretty_thms ctxt) |> commas))


fun find_preds p_lookup p_tab intro_names thm =
  let
    fun get_intrs pred_name = p_lookup p_tab pred_name |> the |> #intros
    fun match_pred intro_name pred_name =
      case filter (get_intro_name #> (curry op =) intro_name) (get_intrs pred_name) of
        [] => NONE
      | i::_ =>
        SOME ((pred_name, p_lookup p_tab pred_name |> the |> #typ), (intro_name, get_intro_spec i))
    val intrs = map (fn iname => first_res (match_pred iname) iname (#preds thm)) intro_names
    val fails = zip_errors intrs
  in
    if fails <> [] then
      Err fails
    else
      Res (zip_results intrs |> AList.group (fn ((a, _), (b, _)) => a = b))
  end

fun intro_err preds intro_name =
  error ("No introduction rule named " ^ intro_name ^ " in " ^ commas preds)

fun save_assms ((p, t), p_assms) = add_assms p_assms p t

fun gen_show_open p_lookup t_lookup t_update ctxt t_cont thm_name intro_name assms p_tab t_tab =
  let
    val othm =
      case t_lookup t_tab thm_name of
        SOME t => t
      | NONE => thm_err thm_name
    val intro_err' = intro_err (#preds othm)
    val assms' =
      case find_preds p_lookup p_tab (intro_name::assms) othm of
        Err n => intro_err' (hd n)
      | Res r => r
    val (pred_name, t) = hd assms' |> fst
    val intro_spec =  hd assms' |> snd |> hd |> snd
    val (prop, ctxt) = #prop othm |> rewrite_prop pred_name t intro_name intro_spec ctxt
    val ctxt' = fold save_assms assms' ctxt
    fun after_qed pred [[thm]] =
          t_update thm_name (add_intro_proof pred intro_name assms ctxt' thm) t_tab |> t_cont
      | after_qed _ thmss = many_thms_err thmss ctxt
  in
    Proof.theorem NONE (after_qed pred_name) [[(prop, [])]] ctxt'
  end

val show_intro =
  gen_show_open Symtab.lookup Symtab.lookup thm_update'

val name_from_bindfix =
  (Binding.name_of o (fn (b, _, _) => b))

fun show_intro_cmd lemma_name intro_name assms lthy =
  let
    val thy = Proof_Context.theory_of lthy
    fun cont thy = Local_Theory.background_theory (K thy)
    val assms' = map name_from_bindfix assms
  in
    gen_show_open pred_lookup thm_lookup thm_update lthy cont lemma_name intro_name assms' thy thy
  end

fun gen_show_open_direct p_lookup t_lookup t_update ctxt t_cont thm_name assms p_tab t_tab =
  let
    val open_thm =
      case t_lookup t_tab thm_name of
        NONE => thm_err thm_name
      | SOME t => t
    val assms' =
      case find_preds p_lookup p_tab assms open_thm of
        Err n => intro_err (#preds open_thm) (hd n)
      | Res r => r
    val lthy' = fold save_assms assms' ctxt
    fun after_qed [[thm]] = (t_update thm_name (add_direct_proof assms lthy' thm) t_tab) |> t_cont
      | after_qed thmss = many_thms_err thmss
  in
    Proof.theorem NONE after_qed [[(#prop open_thm |> Syntax.read_prop lthy', [])]] lthy'
  end

val show_open =
  gen_show_open_direct Symtab.lookup Symtab.lookup thm_update'

fun show_open_cmd thm_name assms lthy =
  let
    val thy = Proof_Context.theory_of lthy
    fun cont t' = Local_Theory.background_theory (K t')
    val assms' = map name_from_bindfix assms
  in
    gen_show_open_direct pred_lookup thm_lookup thm_update lthy cont thm_name assms' thy thy
  end

fun show_open_switch ((thm_name, ""), assms) = show_open_cmd thm_name assms
  | show_open_switch ((thm_name, intro_name), assms) = show_intro_cmd thm_name intro_name assms

val so_parser = Parse.name -- Scan.optional (Parse.$$$ "for" |-- Parse.name) "" --
  Scan.optional (Parse.$$$ "assumes" |-- Parse.fixes) []

val () = Outer_Syntax.local_theory_to_proof @{command_spec "show_open"}
          "shows an open theorem for an intro rule (or directly)"
          (so_parser >> show_open_switch)



(** Closing Predicates **)

val elem = member (op =)

fun install_thm binding thm = Local_Theory.note ((binding, []), [thm]) #> snd

fun rename_free name typ name' =
  let
    fun rename (v as Free (n, t0)) =
          if n = name then
            Free (name', if is_some typ then the typ else t0)
          else v
      | rename x = x
  in
    map_aterms rename
  end

fun make_tac induct i intro_rules =
  etac induct i THEN (EVERY1 (map (single #> solve_tac) intro_rules))

fun read_goal ctxt bind prop =
  let
    val ((_, goals), _) = Specification.read_spec bind [((Binding.empty, []), prop)] ctxt
  in
    hd goals |> snd
  end

fun rewrite_goal ctxt pname ty cname =
  read_goal ctxt [(Binding.name pname, ty, NoSyn)]
  #> rename_free pname (if is_some ty then SOME (Syntax.read_typ ctxt (the ty)) else NONE) cname

fun gen_pname pname =
  implies_intr_hyps #> Thm.generalize ([], [pname]) 2

fun clear_hyps cname ctxt' ctxt hyp_thms thm =
  let
    val cert = cterm_of (Proof_Context.theory_of ctxt)
    val thm' = Assumption.export true ctxt' ctxt thm
      |> instantiate' [] [SOME (Syntax.read_term ctxt cname |> cert)]
    (*val () = Pretty.block [Pretty.str "have thm: ", pretty_thms ctxt [t']] |> Pretty.writeln
    val () = Pretty.block [Pretty.str "have hyps: ", pretty_thms ctxt hyp_thms] |> Pretty.writeln*)
  in
    thm' |> rule_by_tactic ctxt (REPEAT (solve_tac hyp_thms 1))
  end

fun hyps_from_assms assms named_intros =
  filter (member (fn ((b, _), a) => a = b) assms) named_intros |> map snd

fun warn_missing thm_name intro_names what =
  warning ("Cannot close open theorem \"" ^ thm_name ^ "\", missing " ^ what ^
    " " ^ (commas intro_names))

fun get_missing named_intros assms =
  filter ((AList.lookup (op =) named_intros) #> is_none) assms

fun finish_proof pname close_name name ptyp prop induct rules named_intrs ctxt =
  let
    val goal = if pname <> close_name
      then rewrite_goal ctxt pname ptyp close_name prop
      else read_goal ctxt [] prop
    val hyp_rules = rules |> map (fn (a, c, r) =>
      (hyps_from_assms a named_intrs, c, gen_pname pname r))
    fun tac _ =  (map snd named_intrs) ~~ hyp_rules
      |> map (fn (h, (hs, ctxt', b)) => clear_hyps close_name ctxt' ctxt (h :: hs) b)
      |> make_tac induct 1
    val thm = Goal.prove ctxt [] [] goal tac
  in
    (name, thm)
  end

fun close_direct ctxt pname ptyp named_intrs close_name (name, prop, (assms, ctxt', proof)) thms =
  let
    val goal = if pname <> close_name
      then rewrite_goal ctxt pname ptyp close_name prop
      else read_goal ctxt [] prop
    val missing = get_missing named_intrs assms
    val hyps = hyps_from_assms assms named_intrs
    val proof' = gen_pname pname proof
      |> clear_hyps close_name ctxt' ctxt hyps
    fun tac _ = etac proof' 1
  in
    if missing = [] then
      (name, Goal.prove ctxt [] [] goal tac)::thms
    else
      (warn_missing name missing "introduction rules:"; thms)
  end

fun gen_close t_lookup lthy pred_name pred intro_names close_name t_tab =
  let
    val intro_specs = map (the o AList.lookup (op =) (#intros pred)) intro_names
    val ({induct, intrs, ...}, lthy') =
      make_inductive pred_name close_name (#typ pred) (intro_names ~~ intro_specs) lthy
    val named_intrs = intro_names ~~ intrs

    val lemma_names = #thms pred
    val lemmas0 = map (t_lookup t_tab) lemma_names
      |> zip_options lemma_names

    val lemmas = filter (fn (_, {direct_proof = NONE, ...}) => true | _ => false) lemmas0
      |> map (fn (n, {prop, proofs, ...}) =>
        (n, prop, case AList.lookup (op =) proofs pred_name of NONE => [] | SOME l => l))

    val directs = filter (fn (_, {direct_proof = SOME _, ...}) => true | _ => false) lemmas0
      |> map (fn (n, {prop, direct_proof, ...}) => (n, prop, the direct_proof))

    val ptyp = #typ pred

    fun close_lemma lthy (name, prop, proofs) thms =
      let
        val rs = map (AList.lookup (op =) proofs) intro_names
          |> filter is_some
          |> map the
        val missing_assms = map (fn (a, _, _) => get_missing named_intrs a) rs |> List.concat
      in
        if length rs <> length intro_names then
          (warn_missing name
            (intro_names |> filter (is_none o (AList.lookup (op =) proofs))) "proofs for";
           thms)
        else if missing_assms <> [] then
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
    (lthy',
     fold (close_lemma lthy') lemmas []
     |> fold (close_direct lthy' pred_name ptyp named_intrs close_name) directs)
  end

fun check_close p_lookup t_lookup ctxt pred_name intro_names close_name p_tab =
  let
    val pred =
      case p_lookup p_tab pred_name of
        NONE => error ("Undefined open predicate: " ^ pred_name)
      | SOME p => p
    val pred_intros = #intros pred |> map get_intro_name
  in
    case find_first (not o elem pred_intros) intro_names of
      SOME x => error ("No introduction rule named " ^ x ^
        " defined in open predicate " ^ pred_name)
    | NONE => gen_close t_lookup ctxt pred_name pred intro_names close_name
  end


val close_inductive =
  check_close Symtab.lookup Symtab.lookup

fun close_inductive_cmd ((pred_name, intro_binds), close_name) lthy =
  let
    val intro_names = map name_from_bindfix intro_binds
    val thy = Proof_Context.theory_of lthy
    val (lthy', thms) =
      check_close pred_lookup thm_lookup lthy pred_name intro_names close_name thy thy
    fun install (name, thm) =
      let
        val inst_name = name ^ "_" ^ close_name
        val msg = (map Pretty.str ["Installing ", inst_name, ": "]) @ [pretty_thms lthy' [thm]]
          |> Pretty.block
      in
        (Pretty.writeln msg;
         install_thm (Binding.name inst_name) thm)
      end
  in
    fold install thms lthy'
  end

val ci_parser =
  (Parse.name -- (Parse.$$$ "assumes" |-- Parse.fixes) -- (Parse.$$$ "for" |-- Parse.name))

val () = Outer_Syntax.local_theory @{command_spec "close_inductive"}
          "closes an inductive predicate"
          (ci_parser >> close_inductive_cmd)

end
