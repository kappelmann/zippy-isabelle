(*  Title:      Zippy/zipper_optics.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS"\<close> =
sig
  structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
  type @{AllT_args} zipper
  type @{AllT_args} content
  type @{AllT_args} zcontext

  val zipper : (@{ParaT_args} @{AllT_args} content * @{AllT_args} zcontext, @{AllT_args} zipper) L.C.cat

  val content : unit -> (@{ParaT_args} @{AllT_args} zipper, @{AllT_args} content) L.slens
  val zcontext : unit -> (@{ParaT_args} @{AllT_args} zipper, @{AllT_args} zcontext) L.slens
  val get_content : (@{ParaT_args} @{AllT_args} zipper, @{AllT_args} content) L.getter
  val get_zcontext : (@{ParaT_args} @{AllT_args} zipper, @{AllT_args} zcontext) L.getter
  val map_content : (@{ParaT_args} @{AllT_args} zipper, @{AllT_args} content) L.smodifier
  val map_zcontext : (@{ParaT_args} @{AllT_args} zipper, @{AllT_args} zcontext) L.smodifier
end

functor \<^eval>\<open>sfx_T_nargs "Instantiate_Zipper_Optics"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i}\<close>\<close>
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS"\<close>
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS"\<close>
    where type @{AllT_args} content = (@{ParaT_args}
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) Z.content
    where type @{AllT_args} zcontext = (@{ParaT_args}
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) Z.zcontext
    where type @{AllT_args} zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) Z.zipper
  = Z
