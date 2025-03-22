(*  Title:  icategory_util.ML
    Author: Kevin Kappelmann

Utilities on indexed categories
*)
signature \<^eval>\<open>sfx_ParaT_nargs "IARROW_EXCEPTION_REC"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_EXCEPTION"\<close>
  val repeat : (@{ParaT_args} 'i, 'i, 'a, 'a) cat -> (@{ParaT_args} 'i, 'i, 'a, 'a) cat
  val repeatn_safe : int -> (@{ParaT_args} 'i, 'i, 'a, 'a) cat -> (@{ParaT_args} 'i, 'i, 'a, 'a) cat
  val try_step : (@{ParaT_args} 'i, 'j, 'a, 'b) cat -> (@{ParaT_args} 'i, 'i, 'a, 'a) cat ->
    (@{ParaT_args} 'i, 'j, 'a, 'b) cat
end

signature \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_EXCEPTION_REC"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_EXCEPTION_REC"\<close>
  where type (@{ParaT_args} 'i, 'j, 'a, 'b) cat = (@{ParaT_args} 'i, 'j, 'a, 'b) K.kleisli
end

functor \<^eval>\<open>sfx_ParaT_nargs "IKleisli_Arrow_Exception_Rec"\<close>(
    AE : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_EXCEPTION"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_EXCEPTION_REC"\<close> =
struct
open AE
fun repeat move x = x |> try (comp (repeat move) move)
fun repeatn_safe fuel move x = x |>
  (if fuel <= 0 then id ()
  else try (comp (repeatn_safe (fuel - 1) move) move))
fun try_step f step x = x |> catch' f (comp (try_step f step) step)
end

signature \<^eval>\<open>sfx_ParaT_nargs "IARROW_FOLD"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_BASE"\<close>

  type 'a res
  val stop : 'a -> 'a res
  val continue : 'a -> 'a res
  val dest_res : 'a res -> 'a

  val fold : (@{ParaT_args} 'j, 'i, 'a, 'a) cat -> (@{ParaT_args} 'i, 'j, 'a * 'b, 'b res) cat ->
    (@{ParaT_args} 'i, 'j, 'a * 'b, 'b res) cat

  val fold_init : (@{ParaT_args} 'i, 'i, 'a, 'a) cat ->
    (@{ParaT_args} 'i, 'i, 'a * 'b, 'b res) cat ->
    (@{ParaT_args} 'i, 'i, 'a, 'b res) cat -> (@{ParaT_args} 'i, 'i, 'a, 'b res) cat
end

signature \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_FOLD"\<close> =
sig
  structure K : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI"\<close>
  include \<^eval>\<open>sfx_ParaT_nargs "IARROW_FOLD"\<close>
  where type (@{ParaT_args} 'i, 'j, 'a, 'b) cat = (@{ParaT_args} 'i, 'j, 'a, 'b) K.kleisli
end

functor \<^eval>\<open>sfx_ParaT_nargs "IKleisli_Arrow_Fold_Exception_Rec"\<close>(
    AE : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_EXCEPTION_REC"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "IKLEISLI_ARROW_FOLD"\<close> =
struct

open AE

datatype 'a res = Stop of 'a | Continue of 'a

val stop = Stop
val continue = Continue
fun dest_res (Stop x) = x
  | dest_res (Continue x) = x

local structure SC = \<^eval>\<open>sfx_ParaT_nargs "ISemi_Category"\<close>(AE)
  structure A = \<^eval>\<open>sfx_ParaT_nargs "IKleisli_Arrow"\<close>(K.M) open SC A
in

fun fold_step _ _ (_, res as Stop _) = res |> id ()
  | fold_step next cont x = x |> (AE.catch' ((next *** arr dest_res) >>> cont) (arr snd))

fun fold next update x = x |> (arr fst &&& update >>> fold_step next (fold next update))

fun fold_init next update init = AE.try_step (id () &&& init) next
  >>> fold_step next (fold next update)

end

end

