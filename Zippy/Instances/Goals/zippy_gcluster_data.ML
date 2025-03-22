(*  Title:      Zippy/zippy_gcluster_data.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GCLUSTER_DATA =
sig
  structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
  type ('g, 'm) gcluster_data
  val gcluster_data : (@{ParaT_args} 'g * 'm, ('g, 'm) gcluster_data) L.C.cat

  val gcluster : unit -> (@{ParaT_args} ('g, 'm) gcluster_data, 'g) L.slens
  val get_gcluster : (@{ParaT_args} ('g, 'm) gcluster_data, 'g) L.getter
  val map_gcluster : (@{ParaT_args} ('g, 'm) gcluster_data, 'g) L.smodifier

  val more : unit -> (@{ParaT_args} ('g, 'm) gcluster_data, 'm) L.slens
  val get_more : (@{ParaT_args} ('g, 'm) gcluster_data, 'm) L.getter
  val map_more : (@{ParaT_args} ('g, 'm) gcluster_data, 'm) L.smodifier
end

structure Zippy_GCluster_Data :
  ZIPPY_GCLUSTER_DATA
  where type (@{ParaT_args} 'g, 'b) L.C.cat =
    (@{ParaT_args} 'g, 'b) \<^eval>\<open>sfx_ParaT_nargs "SLens" ^ ".C.cat"\<close> =
struct

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close>

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

signature KLEISLI_ZIPPY_GCLUSTER_DATA =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI"\<close>
  include ZIPPY_GCLUSTER_DATA
  where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) K.kleisli
end

signature LIFT_ZIPPY_GCLUSTER_DATA =
sig
  structure GCD : ZIPPY_GCLUSTER_DATA
  include KLEISLI_ZIPPY_GCLUSTER_DATA
  where type ('g, 'm) gcluster_data = ('g, 'm) GCD.gcluster_data
end

functor Lift_Zippy_GCluster_Data(
    include LIFT_DATA_BASE
    structure GCD : ZIPPY_GCLUSTER_DATA
    sharing type GCD.L.C.cat = AF.cat
  ) : LIFT_ZIPPY_GCLUSTER_DATA =
struct

structure GCD = GCD
structure L = L
structure K = AT.K

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


