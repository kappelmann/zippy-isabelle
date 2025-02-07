(*  Title:      HOCLP/zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close> =
sig
  include MOVE_BASE
  type @{T_args} zipper
  structure ZM : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_MOVES"\<close>
  sharing type ZM.zipper = zipper
  sharing type ZM.M.t = M.t
  structure ZO : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_OPTICS"\<close>
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) cat
  sharing type ZO.zipper = zipper
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper"\<close>(
    structure ZM : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_MOVES"\<close>
    structure ZO : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_OPTICS"\<close>
    where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) ZM.cat
    sharing type ZO.zipper = ZM.zipper
  ) : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close> =
struct

structure ZM = ZM
structure ZO = ZO
open ZM

end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_Zipper"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i}\<close>\<close>
    structure Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
    where type @{T_args} ZM.container = (@{ParaT_args},
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{T_args} inst{i}\<close> where sep = ","\<close>) Z.ZM.container
    where type @{T_args} ZO.content = (@{ParaT_args},
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{T_args} inst{i}\<close> where sep = ","\<close>) Z.ZO.content
    where type @{T_args} ZO.zcontext = (@{ParaT_args},
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{T_args} inst{i}\<close> where sep = ","\<close>) Z.ZO.zcontext
    where type @{T_args} zipper = (@{ParaT_args},
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{T_args} inst{i}\<close> where sep = ","\<close>) Z.zipper
    where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
  = Z
