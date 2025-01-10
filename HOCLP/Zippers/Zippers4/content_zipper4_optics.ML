(*  Title:      HOCLP/content_zipper4_optics.ML
    Author:     Kevin Kappelmann
*)
functor Content_Zipper4_Optics(
    structure A : KLEISLI_ARROW_ARROW_APPLY
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) A.A.cat
    type ('p1, 'a1, 'a2, 'a3, 'a4) content
    type ('p1, 'a1, 'a2, 'a3, 'a4) container
  ) :
    ZIPPER4_OPTICS
    where type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) content
    where type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = unit
    where type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, 'a1, 'a2, 'a3, 'a4) content
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) L.C.cat
  =
struct
  structure L = L
  type ('p1, 'a1, 'a2, 'a3, 'a4) content = ('p1, 'a1, 'a2, 'a3, 'a4) content
  type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = unit
  type ('p1, 'a1, 'a2, 'a3, 'a4) zipper = ('p1, 'a1, 'a2, 'a3, 'a4) content
  open A A.A
  fun zipper x = x |> arr fst

  fun get_content x = x |> id ()
  fun get_zcontext x = x |> K ()

  val map_content = AA.app
  fun map_zcontext x = x |> arr snd

  fun content _ = L.lens get_content map_content
  fun zcontext _ = L.lens get_zcontext map_zcontext
end
