(*  Title:      Zippy/zipper_morphs.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "ZIPPER_MORPHS"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  type @{AllT_args} container
  type @{AllT_args} zipper

  structure Zip : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
  sharing type Zip.from = container
  sharing type Zip.to = zipper
  sharing type Zip.M.t = M.t
  structure Unzip : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
  sharing type Unzip.from = zipper
  sharing type Unzip.to = container
  sharing type Unzip.M.t = M.t

  structure Up : \<^eval>\<open>sfx_T_nargs "EMORPH"\<close>
  sharing type Up.from = zipper
  sharing type Up.M.t = M.t
  structure Down : \<^eval>\<open>sfx_T_nargs "EMORPH"\<close>
  sharing type Down.from = zipper
  sharing type Down.M.t = M.t
  structure Left : \<^eval>\<open>sfx_T_nargs "EMORPH"\<close>
  sharing type Left.from = zipper
  sharing type Left.M.t = M.t
  structure Right : \<^eval>\<open>sfx_T_nargs "EMORPH"\<close>
  sharing type Right.from = zipper
  sharing type Right.M.t = M.t
end

functor \<^eval>\<open>sfx_T_nargs "Zipper_Morphs"\<close>(
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
    type @{AllT_args} container
    type @{AllT_args} zipper
    val zip : (@{ParaT_args} @{AllT_args} container, @{AllT_args} zipper) M.morph
    val unzip : (@{ParaT_args} @{AllT_args} zipper, @{AllT_args} container) M.morph
    val up : (@{ParaT_args} @{AllT_args} zipper) M.emorph
    val down : (@{ParaT_args} @{AllT_args} zipper) M.emorph
    val left : (@{ParaT_args} @{AllT_args} zipper) M.emorph
    val right : (@{ParaT_args} @{AllT_args} zipper) M.emorph
  ) : \<^eval>\<open>sfx_T_nargs "ZIPPER_MORPHS"\<close> =
struct

structure Min = M
open M
type @{AllT_args} container = @{AllT_args} container
type @{AllT_args} zipper = @{AllT_args} zipper

structure Zip =
struct
  open Min
  type @{AllT_args} from = @{AllT_args} container
  type @{AllT_args} to = @{AllT_args} zipper
  val morph = zip
end
structure Unzip =
struct
  open Min
  type @{AllT_args} from = @{AllT_args} zipper
  type @{AllT_args} to = @{AllT_args} container
  val morph = unzip
end

structure Base = struct
  structure M = Min
  type @{AllT_args} data = @{AllT_args} zipper
end
structure Up = \<^eval>\<open>sfx_T_nargs "EMorph"\<close>(open Base; val morph = up)
structure Down = \<^eval>\<open>sfx_T_nargs "EMorph"\<close>(open Base; val morph = down)
structure Left = \<^eval>\<open>sfx_T_nargs "EMorph"\<close>(open Base; val morph = left)
structure Right = \<^eval>\<open>sfx_T_nargs "EMorph"\<close>(open Base; val morph = right)

end
