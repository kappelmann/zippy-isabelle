(*  Title:      HOCLP/content_zipper.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Content_Zipper_Optics"\<close>(
    structure A : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_ARROW_APPLY"\<close>
    structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
    where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) A.A.cat
    type @{AllT_args} content
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS"\<close>
    where type @{AllT_args} content = @{AllT_args} content
    where type @{AllT_args} zcontext = unit
    where type @{AllT_args} zipper = @{AllT_args} content
    where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) L.C.cat
  =
struct
  structure L = L
  type @{AllT_args} content = @{AllT_args} content
  type @{AllT_args} zcontext = unit
  type @{AllT_args} zipper = @{AllT_args} content
  open A A.A
  fun zipper x = x |> arr fst

  fun get_content x = x |> id ()
  fun get_zcontext x = x |> K ()

  val map_content = AA.app
  fun map_zcontext x = x |> arr snd

  fun content _ = L.lens get_content map_content
  fun zcontext _ = L.lens get_zcontext map_zcontext
end

functor \<^eval>\<open>sfx_T_nargs "Content_Zipper_Moves"\<close>(
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
    type @{AllT_args} container
    type @{AllT_args} content
    val zip : (@{ParaT_args} @{AllT_args} container, @{AllT_args} content) M.move
    val unzip : (@{ParaT_args} @{AllT_args} content, @{AllT_args} container) M.move
    val up : (@{ParaT_args} @{AllT_args} content) M.hom_move
    val down : (@{ParaT_args} @{AllT_args} content) M.hom_move
    val left : (@{ParaT_args} @{AllT_args} content) M.hom_move
    val right : (@{ParaT_args} @{AllT_args} content) M.hom_move
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close>
    where type @{AllT_args} container = @{AllT_args} container
    where type @{AllT_args} zipper = @{AllT_args} content
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) M.M.t
  =
\<^eval>\<open>sfx_T_nargs "Zipper_Moves"\<close>(
  structure M = M
  type @{AllT_args} container = @{AllT_args} container
  type @{AllT_args} zipper = @{AllT_args} content
  val zip = zip
  val unzip = unzip
  val up = up
  val down = down
  val left = left
  val right = right
)

signature \<^eval>\<open>sfx_T_nargs "CONTENT_ZIPPER"\<close> =
sig
  type @{AllT_args} container
  type @{AllT_args} content
  include \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  where type @{AllT_args} ZM.container = @{AllT_args} container
  where type @{AllT_args} ZO.content = @{AllT_args} content
  where type @{AllT_args} ZO.zcontext = unit
  where type @{AllT_args} zipper = @{AllT_args} content
end

functor \<^eval>\<open>sfx_T_nargs "Content_Zipper"\<close>(
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
    structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
    where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) M.cat
    type @{AllT_args} container
    type @{AllT_args} content
    val zip : (@{ParaT_args} @{AllT_args} container, @{AllT_args} content) M.move
    val unzip : (@{ParaT_args} @{AllT_args} content, @{AllT_args} container) M.move
    val up : (@{ParaT_args} @{AllT_args} content) M.hom_move
    val down : (@{ParaT_args} @{AllT_args} content) M.hom_move
    val left : (@{ParaT_args} @{AllT_args} content) M.hom_move
    val right : (@{ParaT_args} @{AllT_args} content) M.hom_move
  ) :
    \<^eval>\<open>sfx_T_nargs "CONTENT_ZIPPER"\<close>
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) M.M.t =
struct

type @{AllT_args} container = @{AllT_args} container
type @{AllT_args} content = @{AllT_args} content
structure Z = \<^eval>\<open>sfx_T_nargs "Zipper"\<close>(
  structure ZO = \<^eval>\<open>sfx_T_nargs "Content_Zipper_Optics"\<close>(
    structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Arrow_Apply"\<close>(M.M)
    structure L = L
    type @{AllT_args} content = @{AllT_args} content
  )
  structure ZM = \<^eval>\<open>sfx_T_nargs "Content_Zipper_Moves"\<close>(
    structure M = M
    type @{AllT_args} container = @{AllT_args} container
    type @{AllT_args} content = @{AllT_args} content
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

functor \<^eval>\<open>sfx_T_nargs "Instantiate_Content_Zipper"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i}\<close>\<close>
    structure Z : \<^eval>\<open>sfx_T_nargs "CONTENT_ZIPPER"\<close>
  ) :
    \<^eval>\<open>sfx_T_nargs "CONTENT_ZIPPER"\<close>
    where type @{AllT_args} container = (@{ParaT_args}
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) Z.container
    where type @{AllT_args} content = (@{ParaT_args}
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) Z.content
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) Z.M.t
  = Z

signature \<^eval>\<open>sfx_T_nargs "SINGLE_CONTENT_ZIPPER"\<close> =
  \<^eval>\<open>sfx_T_nargs "CONTENT_ZIPPER"\<close>

functor \<^eval>\<open>sfx_T_nargs "Single_Content_Zipper"\<close>(
    structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION"\<close>
    where type @{ParaT_args encl = "(" ")"} exn = unit
    structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
    where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) AE.cat
    type @{AllT_args} container
    type @{AllT_args} content
    val zip : (@{ParaT_args} @{AllT_args} container, @{AllT_args} content) AE.cat
    val unzip : (@{ParaT_args} @{AllT_args} content, @{AllT_args} container) AE.cat
  ) :
    \<^eval>\<open>sfx_T_nargs "SINGLE_CONTENT_ZIPPER"\<close>
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) AE.K.M.t =
\<^eval>\<open>sfx_T_nargs "Content_Zipper"\<close>(
  structure M = \<^eval>\<open>sfx_ParaT_nargs "Move_Base"\<close>(AE.K.M)
  structure L = L
  type @{AllT_args} container = @{AllT_args} container
  type @{AllT_args} content = @{AllT_args} content
  open AE
  val zip = zip
  val unzip = unzip
  fun left x = x |> throw' ()
  fun right x = x |> throw' ()
  fun up x = x |> throw' ()
  fun down x = x |> throw' ()
)
