(*  Title:      HOCLP/zipper_optics.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_OPTICS"\<close> =
sig
  structure L : LENS
  type @{T_args} zipper
  type @{T_args} content
  type @{T_args} zcontext

  val zipper : (@{ParaT_args}, @{T_args} content * @{T_args} zcontext, @{T_args} zipper) L.C.cat

  val content : unit -> (@{ParaT_args}, @{T_args} zipper, @{T_args} content) L.slens
  val zcontext : unit -> (@{ParaT_args}, @{T_args} zipper, @{T_args} zcontext) L.slens
  val get_content : (@{ParaT_args}, @{T_args} zipper, @{T_args} content) L.getter
  val get_zcontext : (@{ParaT_args}, @{T_args} zipper, @{T_args} zcontext) L.getter
  val map_content : (@{ParaT_args}, @{T_args} zipper, @{T_args} content) L.smodifier
  val map_zcontext : (@{ParaT_args}, @{T_args} zipper, @{T_args} zcontext) L.smodifier
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_Zipper" ^ "_Optics"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i}\<close>\<close>
    structure Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_OPTICS"\<close>
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_OPTICS"\<close>
    where type @{T_args} content = (@{ParaT_args},
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{T_args} inst{i}\<close> where sep = ","\<close>) Z.content
    where type @{T_args} zcontext = (@{ParaT_args},
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{T_args} inst{i}\<close> where sep = ","\<close>) Z.zcontext
    where type @{T_args} zipper = (@{ParaT_args},
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{T_args} inst{i}\<close> where sep = ","\<close>) Z.zipper
  = Z
