(*  Title:      Zippy/zippy_init_goal_clusters_mixin.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_INIT_GOAL_CLUSTERS_MIXIN =
sig
  include ZIPPY_INIT_GOAL_CLUSTERS_MIXIN_BASE
  structure Exn : ZIPPY_EXCEPTION_MIXIN
  sharing type Exn.M.t = M.t

  val init : init_gcluster
  type container2
  val init_all : (unit -> @{ParaT_args encl: "(" ")"} Exn.ME.exn) ->
    (@{ParaT_args} @{AllT_args} GCluster.L.container, GPU.F.focus) morph ->
    (@{ParaT_args} container2, @{AllT_args} GCluster.L.container) morph
end

functor Zippy_Init_Goal_Clusters_Mixin(
    structure Z : ZIPPY_ENUM_MIXIN
    structure IGC : ZIPPY_INIT_GOAL_CLUSTERS_MIXIN_BASE
    sharing type IGC.GCluster.L.container = Z.Z2.zipper
    sharing type IGC.M.t = Z.M.t
    structure Ctxt : ZIPPY_CTXT_STATE_MIXIN
    sharing type Ctxt.M.t = Z.M.t
  ) : ZIPPY_INIT_GOAL_CLUSTERS_MIXIN =
struct

open Z IGC
structure MU = Zippy_Monad_Util(M); open MU
structure Exn = Zippy_Exception_Mixin(Z.Co)
structure ZB = Zippy_Base(structure Z = Z; structure Exn = Exn)
structure GCluster = Zippy_Goal_Cluster_Mixin(GCluster)

type container2 = @{AllT_args} Z.Z2.ZM.container

local open SC Mo A
in
fun init focus = Ctxt.with_ctxt (fn ctxt => fn z =>
  let
    val state = GCluster.get_state z
    val goals = Thm.prems_of state |> List.map Term_Util.strip_subgoal
    fun init_with_args init = init (state, goals) focus
    val init = Data.get_table (Context.Proof ctxt)
      |> Data.Table.dest
      |> ZB.LF.foldlM (snd #> init_with_args)
  in init z end)

fun init_all mk_exn mk_focus = Z2.ZM.Zip.morph
  >>> Co.Co.repeat_res (id ())
    (fn z => mk_focus z >>= (fn focus => init focus z) >>= arr Co.Co.continue)
    (Z.DF_Post2.enum_zipper mk_exn)
  >>> arr Co.Co.dest_res
end
end