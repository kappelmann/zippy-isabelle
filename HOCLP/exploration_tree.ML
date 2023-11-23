(*  Title:      HOCLP/exploration_tree.ML
    Author:     Kevin Kappelmann
*)

signature EXPLORATION_TREE_ARGS =
sig
type ('c, 'ch) tree_content
type ('ac, 'ach) app_tree_content
end

signature EXPLORATION_TREE =
sig
(* include HAS_LOGGER *)
structure ETA : EXPLORATION_TREE_ARGS

datatype ('c, 'ac) tree = Tree of ('c, ('c, 'ac) app_tree) ETA.tree_content
and ('c, 'ac) app_tree = App_Tree of ('ac, ('c, 'ac) tree) ETA.app_tree_content

end

functor Exploration_Tree(A : sig
    structure FIA : FUNCTOR_INSTANCE_ARGS
    structure ETA : EXPLORATION_TREE_ARGS
  end)
  (* : EXPLORATION_TREE = *)
  =
struct

structure FIU = Functor_Instance_Util(A.FIA)
structure ETA = A.ETA

(* val logger = Logger.setup_new_logger Logger.root_logger FIU.FIA.full_name *)

datatype ('c, 'ac) tree = Tree of ('c, ('c, 'ac) app_tree) ETA.tree_content
and ('c, 'ac) app_tree = App_Tree of ('ac, ('c, 'ac) tree) ETA.app_tree_content

type ('c, 'ac) tree_internal = ('c, ('c, 'ac) app_tree) ETA.tree_content
type ('c, 'ac) app_tree_internal = ('ac, ('c, 'ac) tree) ETA.app_tree_content

end
