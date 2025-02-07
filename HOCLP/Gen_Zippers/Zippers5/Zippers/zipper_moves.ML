(*  Title:      HOCLP/zipper_moves.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_MOVES"\<close> =
sig
  include MOVE_BASE
  type @{T_args} container
  type @{T_args} zipper

  structure Zip : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
  sharing type Zip.from = container
  sharing type Zip.to = zipper
  sharing type Zip.M.t = M.t
  structure Unzip : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
  sharing type Unzip.from = zipper
  sharing type Unzip.to = container
  sharing type Unzip.M.t = M.t

  structure Up : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
  sharing type Up.from = zipper
  sharing type Up.to = zipper
  sharing type Up.M.t = M.t
  structure Down : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
  sharing type Down.from = zipper
  sharing type Down.to = zipper
  sharing type Down.M.t = M.t
  structure Left : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
  sharing type Left.from = zipper
  sharing type Left.to = zipper
  sharing type Left.M.t = M.t
  structure Right : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close>
  sharing type Right.from = zipper
  sharing type Right.to = zipper
  sharing type Right.M.t = M.t
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper" ^ "_Moves"\<close>(
    structure M : MOVE_BASE
    type @{T_args} container
    type @{T_args} zipper
    val zip : (@{ParaT_args}, @{T_args} container, @{T_args} zipper) M.move
    val unzip : (@{ParaT_args}, @{T_args} zipper, @{T_args} container) M.move
    val up : (@{ParaT_args}, @{T_args} zipper) M.hom_move
    val down : (@{ParaT_args}, @{T_args} zipper) M.hom_move
    val left : (@{ParaT_args}, @{T_args} zipper) M.hom_move
    val right : (@{ParaT_args}, @{T_args} zipper) M.hom_move
  ) : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_MOVES"\<close> =
struct

structure Min = M
open M
type @{T_args} container = @{T_args} container
type @{T_args} zipper = @{T_args} zipper

structure Zip =
struct
  open Min
  type @{T_args} from = @{T_args} container
  type @{T_args} to = @{T_args} zipper
  val move = zip
end
structure Unzip =
struct
  open Min
  type @{T_args} from = @{T_args} zipper
  type @{T_args} to = @{T_args} container
  val move = unzip
end

structure Base = struct
  structure M = Min
  type @{T_args} data = @{T_args} zipper
end
structure Up = \<^eval>\<open>T_Args.suffix_Poly_nargs "Hom_Move"\<close>(open Base; val move = up)
structure Down = \<^eval>\<open>T_Args.suffix_Poly_nargs "Hom_Move"\<close>(open Base; val move = down)
structure Left = \<^eval>\<open>T_Args.suffix_Poly_nargs "Hom_Move"\<close>(open Base; val move = left)
structure Right = \<^eval>\<open>T_Args.suffix_Poly_nargs "Hom_Move"\<close>(open Base; val move = right)

end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_Zipper" ^ "_Moves"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i}\<close>\<close>
    structure Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_MOVES"\<close>
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_MOVES"\<close>
    where type @{T_args} container = (@{ParaT_args},
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{T_args} inst{i}\<close> where sep = ","\<close>) Z.container
    where type @{T_args} zipper = (@{ParaT_args},
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{T_args} inst{i}\<close> where sep = ","\<close>) Z.zipper
    where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
  = Z

