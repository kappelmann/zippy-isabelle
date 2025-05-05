(*  Title:  structured_lens.ML
    Author: Kevin Kappelmann

Lenses with fixed, explicit types.
*)
signature \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close> =
sig
  (*we stick to Kleisli lenses such that getters and modifers can be typed polymorphically without
  using a unit argument (as needed for the lens)*)
  include \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
  where type (@{ParaT_args} 'a, 'b) C.cat = 'a -> 'b
  where type (@{ParaT_args} 't, 'o, 's, 'i) lens =
    (@{ParaT_args} 't, 'o, 's, 'i) \<^eval>\<open>sfx_ParaT_nargs "SLens" ^ ".lens"\<close>

  type @{AllT_args} container
  type @{AllT_args} data

  val lens : unit -> (@{ParaT_args} @{AllT_args} container, @{AllT_args} data) slens
  val getter : (@{ParaT_args} @{AllT_args} container, @{AllT_args} data) getter
  val modifier : (@{ParaT_args} @{AllT_args} container, @{AllT_args} data) smodifier
end

functor \<^eval>\<open>sfx_T_nargs "Structured_Lens"\<close>(
    type @{AllT_args} container
    type @{AllT_args} data
    val lens : unit -> (@{ParaT_args} @{AllT_args} container, @{AllT_args} data)
      \<^eval>\<open>sfx_ParaT_nargs "SLens" ^ ".slens"\<close>
  ) :
    \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
    where type @{AllT_args} container = @{AllT_args} container
    where type @{AllT_args} data = @{AllT_args} data
  =
struct

open \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close>
type @{AllT_args} container = @{AllT_args} container
type @{AllT_args} data = @{AllT_args} data

val lens = lens
fun getter x = get (lens ()) x
fun modifier x = modify (lens ()) x

end

\<^imap>\<open>\<open>{i}\<close> => \<open>
functor \<^eval>\<open>sfx_inst_T_nargs "Instantiate_Structured_Lens" {i}\<close>(
    type @{AllT_args} inst
    structure L : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  ) :
    \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
    where type @{AllT_args} container = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) L.container
    where type @{AllT_args} data = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) L.data
  = L\<close>\<close>
