(*  Title:      Zippy/zippy_base_enum.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_BASE_ENUM =
sig
  include ZIPPY_BASE_BASE

  (* misc *)
  structure Co : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close>
  where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) cat
  structure AE : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_EXCEPTION_REPEAT"\<close>
  sharing type AE.K.M.t = M.t
  sharing type AE.exn = Co.AE.exn

  (* enumerations *)
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure DF_Post{i} : \<^eval>\<open>sfx_T_nargs "ENUMERATE_ZIPPER"\<close>
  sharing type DF_Post{i}.Z.zipper = Z{i}.zipper
  sharing type DF_Post{i}.Z.M.t = M.t
  sharing type DF_Post{i}.Co.acoroutine = Co.acoroutine
  sharing type DF_Post{i}.Co.AE.exn = Co.AE.exn

  structure ADF_Post{i} : \<^eval>\<open>mk_name ["ENUMERATE", pfx_sfx_nargs "ALTERNATING_ZIPPER"]\<close>
  \<^imap>\<open>\<open>{j}\<close> => \<open>
  sharing type ADF_Post{i}.Z.Z{j}.zipper =
    Z\<^eval>\<open>ML_Gen.add_mod_nzippers' {j} ({i} - 1) ^ "."\<close>zipper\<close>\<close>
  sharing type ADF_Post{i}.Z.M.t = M.t
  sharing type ADF_Post{i}.Co.acoroutine = Co.acoroutine
  sharing type ADF_Post{i}.Co.AE.exn = Co.AE.exn\<close>\<close>
end

functor Zippy_Base_Enum(
    structure Z : ZIPPY_BASE_BASE
    structure Co : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close>
    where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) Z.cat
  ) : ZIPPY_BASE_ENUM =
struct

open Z
(* misc *)
structure Co = Co
structure AE = struct open Z Co.AE end

(* enumerations *)
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure DF_Post{i} = \<^eval>\<open>sfx_T_nargs "DF_Postorder_Enumerate_Zipper"\<close>(
  structure Z = Z{i}.ZM; structure Co = Co)\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure ADF_Post{i} = \<^eval>\<open>mk_name ["DF_Postorder_Enumerate", pfx_sfx_nargs "Alternating_Zipper"]\<close>(
  structure Z = \<^imap>\<open>\<open>{j}\<close> => \<open>
    \<^eval>\<open>mk_name ["Rotate", pfx_sfx_nargs "Alternating_Zipper"]\<close>(\<close> where stop = \<open>{i} - 1\<close>\<close>
    Z
    \<^imap>\<open>\<open>{j}\<close> => \<open>)\<close> where stop = \<open>{i} - 1\<close>\<close>
  \<^imap>\<open>\<open>{j}\<close> => \<open>
  structure E{j} = DF_Post\<^eval>\<open>ML_Gen.add_mod_nzippers' {j} ({i} - 1)\<close>\<close>\<close>)\<close>\<close>

end
