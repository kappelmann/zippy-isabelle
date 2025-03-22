(*  Title:      Zippy/zipper_moves.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
  type @{AllT_args} container
  type @{AllT_args} zipper

  structure Zip : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
  sharing type Zip.from = container
  sharing type Zip.to = zipper
  sharing type Zip.M.t = M.t
  structure Unzip : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
  sharing type Unzip.from = zipper
  sharing type Unzip.to = container
  sharing type Unzip.M.t = M.t

  structure Up : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
  sharing type Up.from = zipper
  sharing type Up.to = zipper
  sharing type Up.M.t = M.t
  structure Down : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
  sharing type Down.from = zipper
  sharing type Down.to = zipper
  sharing type Down.M.t = M.t
  structure Left : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
  sharing type Left.from = zipper
  sharing type Left.to = zipper
  sharing type Left.M.t = M.t
  structure Right : \<^eval>\<open>sfx_T_nargs "MOVE"\<close>
  sharing type Right.from = zipper
  sharing type Right.to = zipper
  sharing type Right.M.t = M.t
end

functor \<^eval>\<open>sfx_T_nargs "Zipper_Moves"\<close>(
    structure M : \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close>
    type @{AllT_args} container
    type @{AllT_args} zipper
    val zip : (@{ParaT_args} @{AllT_args} container, @{AllT_args} zipper) M.move
    val unzip : (@{ParaT_args} @{AllT_args} zipper, @{AllT_args} container) M.move
    val up : (@{ParaT_args} @{AllT_args} zipper) M.hom_move
    val down : (@{ParaT_args} @{AllT_args} zipper) M.hom_move
    val left : (@{ParaT_args} @{AllT_args} zipper) M.hom_move
    val right : (@{ParaT_args} @{AllT_args} zipper) M.hom_move
  ) : \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close> =
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
  val move = zip
end
structure Unzip =
struct
  open Min
  type @{AllT_args} from = @{AllT_args} zipper
  type @{AllT_args} to = @{AllT_args} container
  val move = unzip
end

structure Base = struct
  structure M = Min
  type @{AllT_args} data = @{AllT_args} zipper
end
structure Up = \<^eval>\<open>sfx_T_nargs "Hom_Move"\<close>(open Base; val move = up)
structure Down = \<^eval>\<open>sfx_T_nargs "Hom_Move"\<close>(open Base; val move = down)
structure Left = \<^eval>\<open>sfx_T_nargs "Hom_Move"\<close>(open Base; val move = left)
structure Right = \<^eval>\<open>sfx_T_nargs "Hom_Move"\<close>(open Base; val move = right)

end

functor \<^eval>\<open>sfx_T_nargs "Instantiate_Zipper_Moves"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i}\<close>\<close>
    structure Z : \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close>
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close>
    where type @{AllT_args} container = (@{ParaT_args}
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) Z.container
    where type @{AllT_args} zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) Z.zipper
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) Z.M.t
  = Z

