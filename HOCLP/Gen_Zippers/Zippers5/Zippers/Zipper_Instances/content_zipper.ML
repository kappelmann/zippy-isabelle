(*  Title:      HOCLP/content_zipper.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Content_Zipper" ^ "_Optics"\<close>(
    structure A : KLEISLI_ARROW_ARROW_APPLY
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) A.A.cat
    type @{T_args} content
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_OPTICS"\<close>
    where type @{T_args} content = @{T_args} content
    where type @{T_args} zcontext = unit
    where type @{T_args} zipper = @{T_args} content
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) L.C.cat
  =
struct
  structure L = L
  type @{T_args} content = @{T_args} content
  type @{T_args} zcontext = unit
  type @{T_args} zipper = @{T_args} content
  open A A.A
  fun zipper x = x |> arr fst

  fun get_content x = x |> id ()
  fun get_zcontext x = x |> K ()

  val map_content = AA.app
  fun map_zcontext x = x |> arr snd

  fun content _ = L.lens get_content map_content
  fun zcontext _ = L.lens get_zcontext map_zcontext
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Content_Zipper" ^ "_Moves"\<close>(
    structure M : MOVE_BASE
    type @{T_args} content
    val zip : (@{ParaT_args}, @{T_args} content) M.hom_move
    val unzip : (@{ParaT_args}, @{T_args} content) M.hom_move
    val up : (@{ParaT_args}, @{T_args} content) M.hom_move
    val down : (@{ParaT_args}, @{T_args} content) M.hom_move
    val left : (@{ParaT_args}, @{T_args} content) M.hom_move
    val right : (@{ParaT_args}, @{T_args} content) M.hom_move
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_MOVES"\<close>
    where type @{T_args} container = @{T_args} content
    where type @{T_args} zipper = @{T_args} content
    where type ('p1, 'a) M.t = ('p1, 'a) M.M.t
  =
\<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper" ^ "_Moves"\<close>(
  structure M = M
  type @{T_args} container = @{T_args} content
  type @{T_args} zipper = @{T_args} content
  val zip = zip
  val unzip = unzip
  val up = up
  val down = down
  val left = left
  val right = right
)

signature \<^eval>\<open>T_Args.suffix_Poly_nargs "CONTENT_ZIPPER"\<close> =
sig
  type @{T_args} content
  include \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
  where type @{T_args} ZO.content = @{T_args} content
  where type @{T_args} ZO.zcontext = unit
  where type @{T_args} ZM.container = @{T_args} content
  where type @{T_args} ZM.zipper = @{T_args} content
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Content_Zipper"\<close>(
    structure M : MOVE_BASE
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) M.cat
    type @{T_args} content
    val zip : (@{ParaT_args}, @{T_args} content) M.hom_move
    val unzip : (@{ParaT_args}, @{T_args} content) M.hom_move
    val up : (@{ParaT_args}, @{T_args} content) M.hom_move
    val down : (@{ParaT_args}, @{T_args} content) M.hom_move
    val left : (@{ParaT_args}, @{T_args} content) M.hom_move
    val right : (@{ParaT_args}, @{T_args} content) M.hom_move
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "CONTENT_ZIPPER"\<close>
    where type ('p1, 'a) M.t = ('p1, 'a) M.M.t =
struct

type @{T_args} content = @{T_args} content
structure Z = \<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper"\<close>(
  structure ZO = \<^eval>\<open>T_Args.suffix_Poly_nargs "Content_Zipper" ^ "_Optics"\<close>(
    structure A = Kleisli_Arrow_Arrow_Apply(M.M)
    structure L = L
    type @{T_args} content = @{T_args} content
  )
  structure ZM = \<^eval>\<open>T_Args.suffix_Poly_nargs "Content_Zipper" ^ "_Moves"\<close>(
    structure M = M
    type @{T_args} content = @{T_args} content
    val zip = zip
    val unzip = unzip
    val up = up
    val down = down
    val left = left
    val right = right
  )
)
open Z

end

signature \<^eval>\<open>T_Args.suffix_Poly_nargs "SINGLE_CONTENT_ZIPPER"\<close> =
  \<^eval>\<open>T_Args.suffix_Poly_nargs "CONTENT_ZIPPER"\<close>

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Single_Content_Zipper"\<close>(
    structure AE : KLEISLI_ARROW_EXCEPTION
    where type 'p1 exn = unit
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) AE.cat
    type @{T_args} content
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "SINGLE_CONTENT_ZIPPER"\<close>
    where type ('p1, 'a) M.t = ('p1, 'a) AE.K.M.t =
\<^eval>\<open>T_Args.suffix_Poly_nargs "Content_Zipper"\<close>(
  structure M = Move_Base(AE.K.M)
  structure L = L
  type @{T_args} content = @{T_args} content
  open AE
  fun zip x = x |> id ()
  fun unzip x = x |> id ()
  fun left x = x |> throw' ()
  fun right x = x |> throw' ()
  fun up x = x |> throw' ()
  fun down x = x |> throw' ()
)
