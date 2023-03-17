(*  Title:      Constraint_Logic_Programming/clp.ML
    Author:     Kevin Kappelmann
*)

signature CONSTRAINT_LOGIC_PROGRAMMING =
sig
  include HAS_LOGGER

  (* CLP tactics *)
  type clp_tactic_binding = binding

end

functor Constraint_Logic_Programming (TI : TERM_INDEX)
  (* : CONSTRAINT_LOGIC_PROGRAMMING = *)
  =
struct

val logger = Logger.setup_new_logger Logger.root_logger "CLP"

structure Util = Constraint_Logic_Programming_Util
structure Show = SpecCheck_Show

(* CLP tactics *)
type clp_tactic_binding = binding

val eq_clp_tactic_binding = (op =)
val show_clp_tactic_binding = Binding.pretty

type clp_tactic_metadata = clp_tactic_binding

val show_clp_tactic_metadata = show_clp_tactic_binding

datatype clp_tactic = CLP_Tactic of clp_tactic_metadata * context_tactic

fun clp_tactic meta tac = CLP_Tactic (meta, tac)
fun dest_clp_tactic (CLP_Tactic (meta, tac)) = (meta, tac)
fun clp_tactic_metadata (CLP_Tactic (meta, _)) = meta

fun eq_clp_tactic clp_tacs = eq_clp_tactic_binding (apply2 clp_tactic_metadata clp_tacs)
fun show_clp_tactic (CLP_Tactic (meta, _)) = show_clp_tactic_metadata meta

val clp_tactics_code = Util.code_list_arg

(*CLP rules*)
type clp_rule = clp_tactic list * thm

fun eq_clp_rule ((tacs1, thm1), (tacs2, thm2)) =
  Thm.eq_thm (thm1, thm2) andalso List.all eq_clp_tactic (tacs1 ~~ tacs2)
  handle ListPair.UnequalLengths => false

fun show_clp_rule ctxt (tacs, thm) =
  let
    val show_term = Show.term ctxt
    val show_term_tac = Show.zip show_term show_clp_tactic
    val pretty_prem_tacs = map2 (curry show_term_tac) (Thm.prems_of thm) tacs
    val pretty_subgoals = Pretty.list "\<lbrakk>" "\<rbrakk>" pretty_prem_tacs
  in
    Pretty.block [
      pretty_subgoals,
      Show.string " \<Longrightarrow> ",
      show_term (Thm.concl_of thm)
    ]
  end

datatype clp_rules = CLP_Rules of {rules : clp_rule TI.term_index}

val empty_clp_rules = CLP_Rules {rules = TI.empty}
fun dest_clp_rules (CLP_Rules data) = data

fun merge_clp_rules (clprs1, clprs2) =
  if pointer_eq (clprs1, clprs2) then clprs1
  else
    let
      val CLP_Rules {rules = rules1} = clprs1
      val CLP_Rules {rules = rules2} = clprs2
      val merged_rules = TI.merge eq_clp_rule rules1 rules2
    in CLP_Rules {rules = merged_rules} end

structure CLP_Rules_Data = Generic_Data(
  type T = clp_rules
  val empty = empty_clp_rules
  val merge = merge_clp_rules
)

fun add_clp_rule (rule as (tacs, thm)) context =
  let
    val ctxt = Context.proof_of context
    val _ = @{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [
        Show.string "Adding CLP rule ",
        show_clp_rule ctxt rule
      ]
      |> Pretty.string_of)
    val thm' = Thm.trim_context thm
    val concl = Thm.concl_of thm' |> TI.norm_term
    val _ = @{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [
        Show.string "Normalised goal index term ",
        Show.term ctxt concl
      ]
      |> Pretty.string_of)
    fun update (clprs as CLP_Rules {rules}) =
      CLP_Rules {rules = TI.insert eq_clp_rule (concl, (tacs, thm')) rules}
      handle Term_Index_Base.INSERT =>
        (@{log Logger.WARN} ctxt (fn _ =>
          Pretty.block [
            Show.string "CLP rule ",
            Show.term ctxt concl,
            Show.string " already added"
          ]
          |> Pretty.string_of);
        clprs)
    val context = CLP_Rules_Data.map update context
  in context end

fun delete_clp_rule (rule as (_, thm)) context =
  let
    val ctxt = Context.proof_of context
    val _ = @{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [
        Show.string "Deleting CLP rule ",
        show_clp_rule ctxt rule
      ]
      |> Pretty.string_of)
    val concl = Thm.concl_of thm |> TI.norm_term
    val _ = @{log Logger.DEBUG} ctxt (fn _ =>
      Pretty.block [
        Show.string "Normalised goal index term ",
        Show.term ctxt concl
      ]
      |> Pretty.string_of)
    fun update (clprs as CLP_Rules {rules}) =
      CLP_Rules {rules = TI.delete (curry eq_clp_rule rule) concl rules}
      handle Term_Index_Base.DELETE =>
        (@{log Logger.WARN} ctxt (fn _ =>
          Pretty.block [
            Show.string "CLP rule ",
            Show.term ctxt concl,
            Show.string " not found"
          ]
          |> Pretty.string_of);
        clprs)
    val context = CLP_Rules_Data.map update context
  in context end


val print_tac_binding = @{binding "printtac"}

val print_clp_tactic =
  (fn (ctxt, thm) => TACTIC_CONTEXT ctxt (print_tac ctxt "printtac" thm))
  |> clp_tactic print_tac_binding

fun add_print_clp_rule thm =
  Thm.prems_of thm
  |> map (K print_clp_tactic)
  |> rpair thm
  |> add_clp_rule

fun delete_print_clp_rule thm =
  Thm.prems_of thm
  |> map (K print_clp_tactic)
  |> rpair thm
  |> delete_clp_rule


fun prove state = state


  (* Thm.trim_context #> (fn thm => Data.map
    (map_transfer_raw (Item_Net.update thm) o
     map_compound_lhs
       (case HOLogic.dest_Trueprop (Thm.concl_of thm) of
          Const (\<^const_name>\<open>Rel\<close>, _) $ _ $ (lhs as (_ $ _)) $ _ =>
            Item_Net.update (lhs, thm)
        | _ => I) o
     map_compound_rhs
       (case HOLogic.dest_Trueprop (Thm.concl_of thm) of
          Const (\<^const_name>\<open>Rel\<close>, _) $ _ $ _ $ (rhs as (_ $ _)) =>
            Item_Net.update (rhs, thm)
        | _ => I) o
     map_known_frees (Term.add_frees (Thm.concl_of thm)))) *)

(* val b = Thm.declaration_attribute (fn thm => fn ctxt => *)
    (* (add_transfer_thm o prep_rule (Context.proof_of ctxt)) thm ctxt) *)

(* val transfer_attribute =
  Attrib.add_del transfer_add transfer_del *)

(* fun attrib f = Thm.declaration_attribute (map_ss o f); *)
(* val unif_hint_add = attrib undefined *)
(* val unif_hint_del = attrib undefined *)

(* val _ = Theory.setup (
  Attrib.setup @{binding unif_hint} (Attrib.add_del unif_hint_add unif_hint_del)
    "declaration of unification hint") *)

  (* Attrib.setup @{binding unif_hint} (Attrib.add_del unif_hint_add unif_hint_del) *)

(* val a : attribute = c *)
(* val a : int Token.context_parser = a *)
(* val a : int Token.parser = a *)
(* type 'a parser = 'a Token.parser; *)
(* type 'a context_parser = 'a Token.context_parser; *)


end
