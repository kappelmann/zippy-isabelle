(*  Title:      Zippy/zippy_monad_util.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_MONAD_UTIL =
sig
  structure Mo : \<^eval>\<open>sfx_ParaT_nargs "MONAD"\<close>
  structure A : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW"\<close>
  sharing type A.K.M.t = Mo.t
  structure SC : \<^eval>\<open>sfx_ParaT_nargs "SEMI_CATEGORY"\<close>
  where type (@{ParaT_args} 'a, 'b) cat = (@{ParaT_args} 'a, 'b) A.cat
  structure C : \<^eval>\<open>sfx_ParaT_nargs "CATEGORY"\<close>
  where type (@{ParaT_args} 'a, 'b) cat = (@{ParaT_args} 'a, 'b) A.cat
  structure AA : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_APPLY"\<close>
  sharing type AA.K.M.t = Mo.t
  structure AC : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_CHOICE"\<close>
  sharing type AC.K.M.t = Mo.t
end

functor Zippy_Monad_Util(M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_BASE"\<close>) : ZIPPY_MONAD_UTIL =
struct

structure Mo = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(M)
structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(M)
structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(A)
structure C = \<^eval>\<open>sfx_ParaT_nargs "Category"\<close>(A)
structure AA = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Apply"\<close>(M)
structure AC = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Choice"\<close>(M)

end

signature ZIPPY_MONAD_EXCEPTION_UTIL =
sig
  include ZIPPY_MONAD_UTIL
  structure ME : \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close>
  sharing type ME.t = Mo.t
  structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION_REC"\<close>
  sharing type AE.K.M.t = Mo.t
  sharing type AE.exn = ME.exn
  structure AF : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_FOLD"\<close>
  sharing type AF.K.M.t = Mo.t
end

functor Zippy_Monad_Exception_Util(M : \<^eval>\<open>sfx_ParaT_nargs "MONAD_EXCEPTION_BASE"\<close>)
  : ZIPPY_MONAD_EXCEPTION_UTIL =
struct

structure ME = M
structure U = Zippy_Monad_Util(M); open U
structure AE = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception_Rec"\<close>(
  \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Exception"\<close>(ME))
structure AF = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Fold_Exception_Rec"\<close>(AE)

end

