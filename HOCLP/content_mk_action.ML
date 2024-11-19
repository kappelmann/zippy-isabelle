(*  Title:      HOCLP/content_mk_action.ML
    Author:     Kevin Kappelmann
*)
signature CONTENT_MK_ACTION =
sig
  structure L : LENS
  type ('c, 'ma) cma
  val content_mk_action: ('p1, 'c * 'ma, ('c, 'ma) cma) L.C.cat

  val content : unit -> ('p1, ('c2, 'ma) cma, 'c2, ('c1, 'ma) cma, 'c1) L.lens
  val mk_action : unit -> ('p1, ('c, 'ma2) cma, 'ma2, ('c, 'ma1) cma, 'ma1) L.lens
  val get_content : ('p1, ('c, 'ma) cma, 'c) L.getter
  val get_mk_action : ('p1, ('c, 'ma) cma, 'ma) L.getter
  val map_content : ('p1, ('c2, 'ma) cma, 'c2, ('c1, 'ma) cma, 'c1) L.modifier
  val map_mk_action : ('p1, ('c, 'ma2) cma, 'ma2, ('c, 'ma1) cma, 'ma1) L.modifier
end

functor Content_Mk_Action(
    structure A : LAZY_ARROW_BASE
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) A.cat
  ) : CONTENT_MK_ACTION =
struct
structure L = L

datatype ('c, 'ma) cma = CMA of {
  content : 'c,
  mk_action : 'ma
}

open A
fun content_mk_action _ =
  arr (fn (content, mk_action) => CMA {content = content, mk_action = mk_action})
  |> Lazy_Cat_Util.unlift
fun content_mk_action_lens _ =
  L.lens_get_mk (A.arr (fn CMA {content, mk_action} => (content, mk_action))) content_mk_action
fun content _ = L.lens_fst (content_mk_action_lens ())
fun mk_action _ = L.lens_snd (content_mk_action_lens ())
fun get_content _ = L.get (content ())
  |> Lazy_Cat_Util.unlift
fun map_content _ = L.modify (content ())
  |> Lazy_Cat_Util.unlift
fun get_mk_action _ = L.get (mk_action ())
  |> Lazy_Cat_Util.unlift
fun map_mk_action _ = L.modify (mk_action ())
  |> Lazy_Cat_Util.unlift
end
