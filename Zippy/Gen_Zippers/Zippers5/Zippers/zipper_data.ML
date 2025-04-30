(*  Title:      Zippy/zipper_data.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close> =
sig
  structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS_KLEISLI"\<close>
  type @{AllT_args} zipper
  type @{AllT_args} content
  type @{AllT_args} zcontext

  val zipper :
    (@{ParaT_args} @{AllT_args} content * @{AllT_args} zcontext, @{AllT_args} zipper) L.C.cat

  structure CO : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  where type @{AllT_args} container = @{AllT_args} zipper
  where type @{AllT_args} data = @{AllT_args} content
  sharing type CO.lens = L.lens
  sharing type CO.K.M.t = L.K.M.t

  structure ZCTXT : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  where type @{AllT_args} container = @{AllT_args} zipper
  where type @{AllT_args} data = @{AllT_args} zcontext
  sharing type ZCTXT.lens = L.lens
  sharing type ZCTXT.K.M.t = L.K.M.t
end

functor \<^eval>\<open>sfx_T_nargs "Zipper_Data"\<close>(
    structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS_KLEISLI"\<close>
    type @{AllT_args} content
    type @{AllT_args} zcontext
  ) : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
  =
struct

structure L = L

type @{AllT_args} content = @{AllT_args} content
type @{AllT_args} zcontext = @{AllT_args} zcontext
datatype @{AllT_args} zipper = Zipper of
  {content : @{AllT_args} content, zcontext : @{AllT_args} zcontext}

local open L.K.M
in

fun zipper (content, zcontext) = pure (Zipper {content = content, zcontext = zcontext})

structure Base = struct open L; type @{AllT_args} container = @{AllT_args} zipper end
structure CO =
struct
  open Base
  type @{AllT_args} data = @{AllT_args} content
  fun getter (Zipper {content,...}) = pure content
  fun modifier (f, Zipper {content, zcontext}) = bind (f content)
    (fn content => zipper (content, zcontext))
  fun lens _ = L.mk_lens getter modifier
end

structure ZCTXT =
struct
  open Base
  type @{AllT_args} data = @{AllT_args} zcontext
  fun getter (Zipper {zcontext,...}) = pure zcontext
  fun modifier (f, Zipper {content, zcontext}) = bind (f zcontext)
    (fn zcontext => zipper (content, zcontext))
  fun lens _ = L.mk_lens getter modifier
end
end

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
