\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Zippy Paper Guide\<close>
theory Zippy_Paper
  imports
    Zippy_Prover_Instances
begin

text \<open>
\<^item> General Information
  \<^item> Many ML files (e.g. @{file "Gen_Zippers/Zippers5/Moves/move.ML"}) contain
    "instantiation functors" below the significant code. You may ignore these functors. They show
    that the respective structures are closed under certain polymorphic instantiations.
    They are needed, for example, when extending the zippers' data as shown in Section 2.2, Example 9.

  \<^item> Unfortunately, we are hitting some severe performance problems of the latest Poly/ML's compiler.
    To get around minute-long compilation times each time we use a function from our example
    instantiation (@{ML_structure Zippy}), we had to make some of the final instantiation's types
    opaque and some others fixed. You can see these temporary adjustments here as FIXMEs:
    @{file "Instances/Prover/Instances/zippy_prover_instance_base.ML"}.
    Likely, the slowness of Poly/ML's compiler is related to the following known issues on GitHub
    https://github.com/polyml/polyml/issues/147 and
    https://github.com/polyml/polyml/issues/206
    We will investigate this further with the Isabelle core developers.
    An annoying consequence of using opaque types is that users have to pretty print the zippers
    manually instead of using Isabelle's built-in pretty printing functionality.
    The relevant pretty printing functions are shown in the linked example files below.

\<^item> Section 2
  \<^item> Nodes @{file "Gen_Zippers/Zippers5/Alternating_Zippers/node.ML"}

\<^item> Section 2.1
  \<^item> Categories and Arrows
    @{file "../ML_Typeclasses/Gen_Typeclasses/Typeclasses_1/Categories/category.ML"}

  \<^item> Moves
    \<^item> Moves Base @{file "Gen_Zippers/Zippers5/Moves/move_base.ML"}
    \<^item> Moves @{file "Gen_Zippers/Zippers5/Moves/move.ML"}

  \<^item> Zippers
    \<^item> Zipper Moves @{file "Gen_Zippers/Zippers5/Zippers/zipper_moves.ML"}
    \<^item> Zipper Lenses @{file "Gen_Zippers/Zippers5/Zippers/zipper_optics.ML"}
    \<^item> Zipper @{file "Gen_Zippers/Zippers5/Zippers/zipper.ML"}

  \<^item> Linked Zippers
    \<^item> Linked Zipper Moves @{file "Gen_Zippers/Zippers5/Linked_Zippers/linked_zipper_moves.ML"}
    \<^item> Linked Zippers @{file "Gen_Zippers/Zippers5/Linked_Zippers/linked_zipper.ML"}

  \<^item> Alternating Zippers
    \<^item> Alternating Zipper Moves
      @{file "Gen_Zippers/Zippers5/Alternating_Zippers/alternating_zipper_moves.ML"}
    \<^item> Alternating Zippers
      @{file "Gen_Zippers/Zippers5/Alternating_Zippers/alternating_zipper.ML"}
    \<^item> Alternating Zipper Product
      @{file "Gen_Zippers/Zippers5/Alternating_Zippers/pair_alternating_zipper.ML"}

\<^item> Section 2.1.1
  \<^item> Monads
    @{file "../ML_Typeclasses/Gen_Typeclasses/Typeclasses_1/typeclass_base.ML"}

  \<^item> Kleisli Category
    @{file "../ML_Typeclasses/Gen_Typeclasses/Typeclasses_1/Categories/category_instance.ML"}

  \<^item> Generating Alternating Zippers from Node Zippers
    \<^item> Extending the Alternating Zipper
      @{file "Gen_Zippers/Zippers5/Alternating_Zippers/alternating_zipper_nodes.ML"}
    \<^item> Extending and Lifting the Input Zippers
      @{file "Gen_Zippers/Zippers5/Zippers/extend_zipper_context.ML"}

  \<^item> Generating Node Zippers
    @{file "Gen_Zippers/Zippers5/Alternating_Zippers/alternating_zipper_nodes_simple_zippers.ML"}

\<^item> Section 2.2
  \<^item> Lenses @{file "../ML_Typeclasses/Gen_Typeclasses/Typeclasses_1/Lenses/lens.ML"}

\<^item> Section 3
  \<^item> We implemented a generalisation of the state monad that also allows the state type to change
    during computation. Such states are not monads but (Atkey) indexed monads.
    \<^item> Atkey Indexed Monads @{file "../ML_Typeclasses/Gen_Typeclasses/Typeclasses_1/itypeclass_base.ML"}
    \<^item> Indexed State Monad @{file "../ML_Typeclasses/Gen_Typeclasses/Typeclasses_1/State/istate.ML"}
    \<^item> State Monad @{file "../ML_Typeclasses/Gen_Typeclasses/Typeclasses_1/State/istate.ML"}
  \<^item> Antiquotations
    \<^item> Sources
      @{file "../ML_Typeclasses/Antiquotations/ML_Eval_Antiquotation.thy"}
      @{file "../ML_Typeclasses/Antiquotations/ML_Args_Antiquotations.thy"}
      @{file "Antiquotations/ML_IMap_Antiquotation.thy"}
    \<^item> Example Configuration and Follow-Up ML-Code Generation
      @{file "Gen_Zippers/Zippers5/Moves/ML_Moves.thy"}

\<^item> Section 4. We highlight the differences/extensions to the paper description
  \<^item> The zipper uses an additional "action cluster" layer that sits between a goal cluster and
    an action. Action clusters collect related actions, e.g. one could create an action cluster for
    external provers, one for simplification actions, etc. This gives the search tree some more
    structure but is not strictly necessary (it is thus omitted in the paper).

  \<^item> Example usages can be found here @{file "Examples/Zippy_Examples.thy"}.

  \<^item> Adding Actions @{file "Instances/Actions/zippy_with_paction_base.ML"}
    \<^item> Action nodes do not store a static priority and action but, more generally,
      a "priority action" (paction) that dynamically computes a priority and action pair.
    \<^item> Action clusters store a "copy" morphism such that actions generating new children can move
      their action siblings to the newly created child while updating their siblings' goal focuses
      (since the number and order of goals may have changed in the new child).

  \<^item> Adding Goals @{file "Instances/Goals/zippy_with_goals_base.ML"}
    \<^item> Goal Clusters @{file "Instances/Prover/Goals/zippy_goal_clusters.ML"}
    \<^item> Goal Cluster @{file "Instances/Prover/Goals/zippy_goal_cluster.ML"}
    \<^item> Goal Focus @{file "Instances/Prover/Goals/zippy_focus.ML"}
    \<^item> Union Find @{file "Union_Find//imperative_union_find.ML"}

  \<^item> Lifting Tactics
    \<^item> Lifting Isabelle Tactics to Zippy Tactics @{file "Instances/Prover/Tactics/zippy_tactic.ML"}
    \<^item> Lifting Zippy Tactics to Actions @{ML Zippy.cons_move_tac}

  \<^item> The Basic Search Tree Model @{file "Instances/Prover/zippy_prover_base.ML"}
    Since there are is always exactly one goal clusters node, we do not use lists for the topmost layer.
    \<^item> List Zipper @{file "Gen_Zippers/Zippers5/Zippers/Instances/list_zipper.ML"}

  \<^item> The Basic Search Tree Model @{file "Instances/Prover/zippy_prover_base.ML"}

  \<^item> Adding Failure and State @{file "Instances/Prover/Instances/zippy_prover_instance_base.ML"}
    \<^item> Option Monad and Transformers
      @{file "../ML_Typeclasses/Gen_Typeclasses/Typeclasses_1/typeclass_base_instance.ML"}

  \<^item> Adding Positional Information
    \<^item> Extending the Alternating Zipper
      Lines 71-82 at @{file "Instances/Prover/Position/zippy_prover_with_position_base.ML"}
    \<^item> Alternating (Global) Position Zipper (from the paper)
      @{file "Gen_Zippers/Zippers5/Alternating_Zippers/Instances/alternating_global_position_zipper.ML"}
    \<^item> Unlike the paper, we store only local positional information in the final implementation,
      i.e. a list of integers. The parents' positions are stored in the zipper's parents' contexts.
      The complete positional information can hence be re-constructed from the context if needed.
      This alternating position zipper can be found here
      @{file "Gen_Zippers/Zippers5/Alternating_Zippers/Instances/alternating_local_position_zipper.ML"}

  \<^item> Running a Best-First Search
    \<^item> Postorder Depth-First Enumeration for Zippers
      @{file "Gen_Zippers/Zippers5/Zippers/Instances/dfs_postorder_enumerable_zipper_moves.ML"}
    \<^item> Postorder Depth-First Enumeration for Alternating Zippers
      @{file "Gen_Zippers/Zippers5/Alternating_Zippers/Instances/dfs_postorder_enumerable_alternating_zipper.ML"}
    \<^item> Folding the Highest-Scoring Action @{ML Zippy.gen_fold_pactions}
    \<^item> Best-First Search @{ML Zippy.repeat_fold_run_max_paction_dfs}

  \<^item> Retrieving all theorems found by the zipper @{ML Zippy.finish_gclusters_oldest_first}
\<close>

end