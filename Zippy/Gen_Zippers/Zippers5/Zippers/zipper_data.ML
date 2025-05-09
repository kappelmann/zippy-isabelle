(*  Title:      Zippy/zipper_data.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close> =
sig
  type @{AllT_args} zipper
  type @{AllT_args} content
  type @{AllT_args} zcontext

  val zipper : @{AllT_args} content * @{AllT_args} zcontext -> @{AllT_args} zipper

  structure Co : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} container = @{AllT_args} zipper
  where type @{AllT_args} data = @{AllT_args} content

  structure ZCtxt : \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
  where type @{AllT_args} container = @{AllT_args} zipper
  where type @{AllT_args} data = @{AllT_args} zcontext
end

functor \<^eval>\<open>sfx_T_nargs "Zipper_Data"\<close>(
    type @{AllT_args} content
    type @{AllT_args} zcontext
  ) : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
  =
struct

structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens_Kleisli_Identity"\<close>

type @{AllT_args} content = @{AllT_args} content
type @{AllT_args} zcontext = @{AllT_args} zcontext
datatype @{AllT_args} zipper = Zipper of
  {content : @{AllT_args} content, zcontext : @{AllT_args} zcontext}

fun zipper (content, zcontext) = Zipper {content = content, zcontext = zcontext}

structure Base = struct open L; type @{AllT_args} container = @{AllT_args} zipper end
structure Co =
struct
  open Base
  type @{AllT_args} data = @{AllT_args} content
  fun getter (Zipper {content,...}) = content
  fun modifier (f, Zipper {content, zcontext}) = zipper (f content, zcontext)
  fun lens _ = L.mk_lens getter modifier
end

structure ZCtxt = \<^eval>\<open>sfx_T_nargs "SStructured_Lens"\<close>(
  open Base
  type @{AllT_args} data = @{AllT_args} zcontext
  fun getter (Zipper {zcontext,...}) = zcontext
  fun modifier (f, Zipper {content, zcontext}) = zipper (content, f zcontext)
  fun lens _ = L.mk_lens getter modifier
)

end

\<^imap>\<open>\<open>{i}\<close> => \<open>
functor \<^eval>\<open>sfx_inst_T_nargs "Instantiate_Zipper_Data" {i}\<close>(
    type @{AllT_args} inst
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
    where type @{AllT_args} content = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) Z.content
    where type @{AllT_args} zcontext = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) Z.zcontext
    where type @{AllT_args} zipper = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) Z.zipper
  = Z\<close>\<close>
