(*  Title:      HOCLP/zippy_goal_cluster_data.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOAL_CLUSTER_DATA =
sig
  structure L : LENS
  type ('g, 'm) gcluster_data
  val gcluster_data : ('p1, 'g * 'm, ('g, 'm) gcluster_data) L.C.cat

  val gcluster : unit -> ('p1, ('g, 'm) gcluster_data, 'g) L.slens
  val get_gcluster : ('p1, ('g, 'm) gcluster_data, 'g) L.getter
  val map_gcluster : ('p1, ('g, 'm) gcluster_data, 'g) L.smodifier

  val more : unit -> ('p1, ('g, 'm) gcluster_data, 'm) L.slens
  val get_more : ('p1, ('g, 'm) gcluster_data, 'm) L.getter
  val map_more : ('p1, ('g, 'm) gcluster_data, 'm) L.smodifier
end

structure Zippy_Goal_Cluster_Data :
  ZIPPY_GOAL_CLUSTER_DATA where type ('p1, 'g, 'b) L.C.cat = ('p1, 'g, 'b) SLens.C.cat =
struct

structure L = SLens

datatype ('g, 'm) gcluster_data = GCluster_Data of {
    gcluster : 'g,
    more : 'm
  }

fun gcluster_data (gcluster, more) = GCluster_Data {gcluster = gcluster, more = more}

fun get_gcluster (GCluster_Data {gcluster,...}) = gcluster
fun get_more (GCluster_Data {more,...}) = more

fun map_gcluster (f, (GCluster_Data {gcluster, more})) = GCluster_Data {gcluster = f gcluster, more = more}
fun map_more (f, (GCluster_Data {gcluster, more})) = GCluster_Data {gcluster = gcluster, more = f more}

fun gcluster _ = L.lens get_gcluster map_gcluster
fun more _ = L.lens get_more map_more

end

signature LIFT_ZIPPY_GOAL_CLUSTER_DATA =
sig
  structure GCD : ZIPPY_GOAL_CLUSTER_DATA
  include ZIPPY_GOAL_CLUSTER_DATA
  where type ('g, 'm) gcluster_data = ('g, 'm) GCD.gcluster_data
end

functor Lift_Zippy_Goal_Cluster_Data(
    structure AF : ARROW
    structure GCD : ZIPPY_GOAL_CLUSTER_DATA
    sharing type GCD.L.C.cat = AF.cat
    structure AT : KLEISLI_ARROW_BASE
    structure L : LENS
    where type ('p1, 'g, 'b) C.cat = ('p1, 'g, 'b) AT.cat
    val lift : ('p1, 'g, 'b) AF.cat -> ('p1, 'g, 'b) AT.cat
  ) : LIFT_ZIPPY_GOAL_CLUSTER_DATA =
struct

structure GCD = GCD
structure L = L

type ('g, 'm) gcluster_data = ('g, 'm) GCD.gcluster_data

fun gcluster_data x = x |> lift GCD.gcluster_data
fun gcluster_data_lens _ =
  L.lens_get_mk (lift (AF.&&& (GCD.get_gcluster, GCD.get_more))) gcluster_data
fun gcluster _ = L.lens_fst (gcluster_data_lens ())
fun more _ = L.lens_snd (gcluster_data_lens ())
fun get_gcluster x = x |> L.get (gcluster ())
fun map_gcluster x = x |> L.modify (gcluster ())
fun get_more x = x |> L.get (more ())
fun map_more x = x |> L.modify (more ())

end


