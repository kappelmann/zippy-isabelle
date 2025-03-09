(*  Title:      HOCLP/alternating_depth_zippers.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_DEPTH_ZIPPERS"\<close> =
sig
  val init_depth : int
  include \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{T_args} Z{i}.ZM.container = int
  where type @{T_args} Z{i}.ZO.content = int\<close>\<close>
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Alternating_Depth_Zippers"\<close>(
    structure M : MOVE_BASE
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) M.cat
  ) : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_DEPTH_ZIPPERS"\<close> =
struct

val init_depth = 0

structure Z = \<^eval>\<open>T_Args.suffix_Poly_nargs "Content_Zipper"\<close>(
  structure M = M
  structure L = L
  type @{T_args} container = int
  type @{T_args} content = int
  fun zip x = x |> M.id ()
  fun unzip x = x |> M.id ()
  fun left x = x |> M.id ()
  fun right x = x |> M.id ()
  fun up x = x |> M.id ()
  fun down x = x |> M.id ())

structure AZ : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS"\<close> =
struct
  open Z
  structure L = L
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Z{i} = Z
  structure Down{i} =
  struct
    open Z
    type @{T_args} from = int
    type @{T_args} to = int
    fun move x = x |> Z.id ()
  end
  structure Up{i} =
  struct
    open Z
    type @{T_args} from = int
    type @{T_args} to = int
    fun move x = x |> Z.id ()
  end\<close>\<close>
  structure \<^eval>\<open>T_Args.suffix_Poly_nargs "Down"\<close> =
  struct
    open Z
    type @{T_args} from = int
    type @{T_args} to = int
    fun move x = (x + 1) |> Z.id ()
  end
  structure Up1 =
  struct
    open Z
    type @{T_args} from = int
    type @{T_args} to = int
    fun move x = (x - 1) |> Z.id ()
  end
end
open AZ
end