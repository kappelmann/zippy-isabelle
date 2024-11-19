(*  Title:      HOCLP/result_update_info.ML
    Author:     Kevin Kappelmann
*)
signature RESULT_UPDATE_INFO =
sig
  structure L : LENS
  type ('r, 'ui) cma
  val result_update_info : ('p1, 'r * 'ui, ('r, 'ui) cma) L.C.cat

  val result : unit -> ('p1, ('r2, 'ui) cma, 'r2, ('r1, 'ui) cma, 'r1) L.lens
  val update_info : unit -> ('p1, ('r, 'ui2) cma, 'ui2, ('r, 'ui1) cma, 'ui1) L.lens
  val get_result : ('p1, ('r, 'ui) cma, 'r) L.getter
  val get_update_info : ('p1, ('r, 'ui) cma, 'ui) L.getter
  val map_result : ('p1, ('r2, 'ui) cma, 'r2, ('r1, 'ui) cma, 'r1) L.modifier
  val map_update_info : ('p1, ('r, 'ui2) cma, 'ui2, ('r, 'ui1) cma, 'ui1) L.modifier
end

functor Result_Update_Info(
    structure A : LAZY_ARROW_BASE
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) A.cat
  ) : RESULT_UPDATE_INFO =
struct
structure L = L

datatype ('r, 'ui) cma = CMA of {
  result : 'r,
  update_info : 'ui
}

open A
fun result_update_info _ =
  arr (fn (result, update_info) => CMA {result = result, update_info = update_info})
  |> Lazy_Cat_Util.unlift
fun result_update_info_lens _ =
  L.lens_get_mk (A.arr (fn CMA {result, update_info} => (result, update_info))) result_update_info
fun result _ = L.lens_fst (result_update_info_lens ())
fun update_info _ = L.lens_snd (result_update_info_lens ())
fun get_result _ = L.get (result ())
  |> Lazy_Cat_Util.unlift
fun map_result _ = L.modify (result ())
  |> Lazy_Cat_Util.unlift
fun get_update_info _ = L.get (update_info ())
  |> Lazy_Cat_Util.unlift
fun map_update_info _ = L.modify (update_info ())
  |> Lazy_Cat_Util.unlift
end
