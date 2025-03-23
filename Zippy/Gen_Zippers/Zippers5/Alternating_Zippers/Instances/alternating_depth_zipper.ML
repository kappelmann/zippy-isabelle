(*  Title:      Zippy/alternating_depth_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_DEPTH_ZIPPER"\<close> =
sig
  val init_depth : int
  include \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} Z{i}.ZM.container = int
  where type @{AllT_args} Z{i}.ZO.content = int\<close>\<close>
end

functor \<^eval>\<open>pfx_sfx_nargs "Alternating_Depth_Zipper"\<close>(
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
    structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
    where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) M.cat
  ) : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_DEPTH_ZIPPER"\<close> =
struct

val init_depth = 0

structure Z = \<^eval>\<open>sfx_T_nargs "Content_Zipper"\<close>(
  structure M = M
  structure L = L
  type @{AllT_args} container = int
  type @{AllT_args} content = int
  fun zip x = x |> M.id ()
  fun unzip x = x |> M.id ()
  fun left x = x |> M.id ()
  fun right x = x |> M.id ()
  fun up x = x |> M.id ()
  fun down x = x |> M.id ())

structure AZ : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close> =
struct
  open Z
  structure L = L
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Z{i} = Z
  structure Down{i} =
  struct
    open Z
    type @{AllT_args} from = int
    type @{AllT_args} to = int
    fun move x = x |> Z.id ()
  end
  structure Up{i} =
  struct
    open Z
    type @{AllT_args} from = int
    type @{AllT_args} to = int
    fun move x = x |> Z.id ()
  end\<close>\<close>
  structure \<^eval>\<open>"Down" ^ ML_Gen.ZipperT_nargs' ()\<close> =
  struct
    open Z
    type @{AllT_args} from = int
    type @{AllT_args} to = int
    fun move x = (x + 1) |> Z.id ()
  end
  structure Up1 =
  struct
    open Z
    type @{AllT_args} from = int
    type @{AllT_args} to = int
    fun move x = (x - 1) |> Z.id ()
  end
end
open AZ
end