(*  Title:      HOCLP/zipper.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPER_MOVE =
sig
  include ZIPPER_MOVE_BASE
  type 'a from
  type 'a to
  val move : ('a from, 'a to) move
end

functor Bi_Zipper_Move_Zipper_Move(
    type ('a, 'b) content
    structure ZM : ZIPPER_MOVE
  ) : BI_ZIPPER_MOVE =
struct
structure ZMB = Zipper_Move_Base(ZM.K)
open ZMB
type ('a, 'b) from = ('a, 'b) content ZM.from
type ('a, 'b) to = ('a, 'b) content ZM.to
val move = ZM.move
end

functor Zipper_Move_Bi_Zipper_Move(ZM : BI_ZIPPER_MOVE) : ZIPPER_MOVE =
struct
structure ZMB = Zipper_Move_Base(ZM.K)
open ZMB
type 'a from = ('a, unit) ZM.from
type 'a to = ('a, unit) ZM.to
val move = ZM.move
end

signature HOM_ZIPPER_MOVE =
sig
  include ZIPPER_MOVE
  sharing type from = to
end

functor Hom_Bi_Zipper_Move_Hom_Zipper_Move(type ('a, 'b) content; structure ZM : HOM_ZIPPER_MOVE)
  : HOM_BI_ZIPPER_MOVE =
  Bi_Zipper_Move_Zipper_Move(type ('a, 'b) content = ('a, 'b) content; structure ZM = ZM)
functor Hom_Zipper_Move_Hom_Bi_Zipper_Move(ZM : HOM_BI_ZIPPER_MOVE) : HOM_ZIPPER_MOVE =
  Zipper_Move_Bi_Zipper_Move(ZM)

functor Hom_Zipper_Move(
    structure ZM : ZIPPER_MOVE_BASE
    type 'a data
    val move : ('a data, 'a data) ZM.move
  ) : HOM_ZIPPER_MOVE =
  Hom_Zipper_Move_Hom_Bi_Zipper_Move(Hom_Bi_Zipper_Move(
    structure ZM = ZM
    type ('a, 'b) data = 'a data
    val move = move))

signature ZIPPER_MOVES =
sig
  include ZIPPER_MOVE_BASE

  structure Init : ZIPPER_MOVE
  sharing type Init.K.M.t = K.M.t
  structure Up : ZIPPER_MOVE
  sharing type Up.K.M.t = K.M.t
  structure Down : ZIPPER_MOVE
  sharing type Down.K.M.t = K.M.t
  structure Left : ZIPPER_MOVE
  sharing type Left.K.M.t = K.M.t
  structure Right : ZIPPER_MOVE
  sharing type Right.K.M.t = K.M.t
end

signature BI_ZIPPER_MOVES_ZIPPER_MOVES_CONTENT_ARGS =
sig
  include ZIPPER_MOVE_BASE
  type ('a, 'b) init_content
  type ('a, 'b) up_content
  type ('a, 'b) down_content
  type ('a, 'b) left_content
  type ('a, 'b) right_content
end

functor Bi_Zipper_Moves_Zipper_Moves(
    structure CA : BI_ZIPPER_MOVES_ZIPPER_MOVES_CONTENT_ARGS
    structure ZM : ZIPPER_MOVES
    sharing type CA.K.M.t = ZM.K.M.t
  ) : BI_ZIPPER_MOVES =
struct
open CA
structure Init =
  Bi_Zipper_Move_Zipper_Move(type ('a, 'b) content = ('a, 'b) init_content; structure ZM = ZM.Init)
structure Up =
  Bi_Zipper_Move_Zipper_Move(type ('a, 'b) content = ('a, 'b) up_content; structure ZM = ZM.Up)
structure Down =
  Bi_Zipper_Move_Zipper_Move(type ('a, 'b) content = ('a, 'b) down_content; structure ZM = ZM.Down)
structure Left =
  Bi_Zipper_Move_Zipper_Move(type ('a, 'b) content = ('a, 'b) left_content; structure ZM = ZM.Left)
structure Right =
  Bi_Zipper_Move_Zipper_Move(type ('a, 'b) content = ('a, 'b) right_content; structure ZM = ZM.Right)
end

functor Zipper_Moves_Bi_Zipper_Moves(ZM : BI_ZIPPER_MOVES) : ZIPPER_MOVES =
struct
structure ZMB = Zipper_Move_Base(ZM.K)
open ZMB

structure Init = Zipper_Move_Bi_Zipper_Move(ZM.Init)
structure Up = Zipper_Move_Bi_Zipper_Move(ZM.Up)
structure Down = Zipper_Move_Bi_Zipper_Move(ZM.Down)
structure Left = Zipper_Move_Bi_Zipper_Move(ZM.Left)
structure Right = Zipper_Move_Bi_Zipper_Move(ZM.Right)
end

signature HOM_ZIPPER_MOVES =
sig
  type 'a init_from
  type 'a data

  include ZIPPER_MOVES
  sharing type Init.from = init_from
  sharing type Init.to = data
  sharing type Up.from = data
  sharing type Up.to = data
  sharing type Down.from = data
  sharing type Down.to = data
  sharing type Left.from = data
  sharing type Left.to = data
  sharing type Right.from = data
  sharing type Right.to = data
end

functor Hom_Bi_Zipper_Moves_Hom_Zipper_Moves(
    type ('a, 'b) content
    structure ZM : HOM_ZIPPER_MOVES
  ) : HOM_BI_ZIPPER_MOVES =
struct
type ('a, 'b) init_from = ('a, 'b) content ZM.init_from
type ('a, 'b) data = ('a, 'b) content ZM.data
structure ZM = Bi_Zipper_Moves_Zipper_Moves(
  structure CA  =
  struct
    structure ZMB = Zipper_Move_Base(ZM.K)
    open ZMB
    type ('a, 'b) init_content = ('a, 'b) content
    type ('a, 'b) up_content = ('a, 'b) content
    type ('a, 'b) down_content = ('a, 'b) content
    type ('a, 'b) left_content = ('a, 'b) content
    type ('a, 'b) right_content = ('a, 'b) content
  end
  structure ZM = ZM)
open ZM
end

functor Hom_Zipper_Moves_Hom_Bi_Zipper_Moves(ZM : HOM_BI_ZIPPER_MOVES) : HOM_ZIPPER_MOVES =
struct
type 'a init_from = ('a, unit) ZM.init_from
type 'a data = ('a, unit) ZM.data
structure ZM = Zipper_Moves_Bi_Zipper_Moves(ZM)
open ZM
end

functor Hom_Zipper_Moves(
    structure ZM : ZIPPER_MOVE_BASE
    type 'a init_from
    type 'a data
    val init : ('a init_from, 'a data) ZM.move
    val up : ('a data, 'a data) ZM.move
    val down : ('a data, 'a data) ZM.move
    val left : ('a data, 'a data) ZM.move
    val right : ('a data, 'a data) ZM.move
  ) : HOM_ZIPPER_MOVES =
Hom_Zipper_Moves_Hom_Bi_Zipper_Moves(Hom_Bi_Zipper_Moves(
  structure ZM = ZM
  type ('a, 'b) init_from = 'a init_from
  type ('a, 'b) data = 'a data
  val init = init
  val up = up
  val down = down
  val left = left
  val right = right
))

signature ZIPPER_BASE =
sig
  type 'c content
  type 'c zcontext
  type 'c zipper
  val zipper : 'c content -> 'c zcontext -> 'c zipper

  val get_content : 'c zipper -> 'c content
  val get_zcontext : 'c zipper -> 'c zcontext

  val map_content : ('c content -> 'c content) -> 'c zipper -> 'c zipper
  val map_zcontext : ('c zcontext -> 'c zcontext) -> 'c zipper -> 'c zipper

  type 'c container
  val unzip : 'c zipper -> 'c container
end

functor Bi_Zipper_Base_Zipper_Base(type ('c1, 'c2) content; structure Z : ZIPPER_BASE)
  : BI_ZIPPER_BASE =
struct
type ('c1, 'c2) zcontext = ('c1, 'c2) content Z.zcontext
type ('c1, 'c2) zipper = ('c1, 'c2) content Z.zipper
type ('c1, 'c2) container = ('c1, 'c2) content Z.container
type ('c1, 'c2) content = ('c1, 'c2) content Z.content
val zipper = Z.zipper
val get_content = Z.get_content
val get_zcontext = Z.get_zcontext
val map_content = Z.map_content
val map_zcontext = Z.map_zcontext
val unzip = Z.unzip
end

functor Zipper_Base_Bi_Zipper_Base(Z : BI_ZIPPER_BASE) : ZIPPER_BASE =
struct
type 'c zcontext = ('c, unit) Z.zcontext
type 'c zipper = ('c, unit) Z.zipper
type 'c container = ('c, unit) Z.container
type 'c content = ('c, unit) Z.content
val zipper = Z.zipper
val get_content = Z.get_content
val get_zcontext = Z.get_zcontext
val map_content = Z.map_content
val map_zcontext = Z.map_zcontext
val unzip = Z.unzip
end

signature ZIPPER =
sig
  include ZIPPER_BASE
  include HOM_ZIPPER_MOVES
  sharing type init_from = container
  sharing type data = zipper
end

functor Bi_Zipper_Zipper(type ('c1, 'c2) content; structure Z : ZIPPER) : BI_ZIPPER =
struct
structure ZB =
  Bi_Zipper_Base_Zipper_Base(type ('c1, 'c2) content = ('c1, 'c2) content; structure Z = Z)
structure ZM =
  Hom_Bi_Zipper_Moves_Hom_Zipper_Moves(type ('c1, 'c2) content = ('c1, 'c2) content; structure ZM = Z)
open ZB
open ZM
end

functor Zipper_Bi_Zipper(Z : BI_ZIPPER) : ZIPPER =
struct
structure ZB = Zipper_Base_Bi_Zipper_Base(Z)
structure ZM = Hom_Zipper_Moves_Hom_Bi_Zipper_Moves(Z)
open ZB
open ZM
end

functor Zipper(
    structure Z : ZIPPER_BASE
    structure ZM : ZIPPER_MOVE_BASE
    val init : ('a Z.container, 'a Z.zipper) ZM.move
    val up : ('a Z.zipper, 'a Z.zipper) ZM.move
    val down : ('a Z.zipper, 'a Z.zipper) ZM.move
    val left : ('a Z.zipper, 'a Z.zipper) ZM.move
    val right : ('a Z.zipper, 'a Z.zipper) ZM.move
  ) : ZIPPER =
Zipper_Bi_Zipper(Bi_Zipper(
  structure Z = Bi_Zipper_Base_Zipper_Base(type ('a, 'b) content = 'a structure Z = Z)
  structure ZM = ZM
  val init = init
  val up = up
  val down = down
  val left = left
  val right = right
))

signature PAIR_ZIPPER_MOVE =
sig
  structure ZM1 : ZIPPER_MOVE
  structure ZM2 : ZIPPER_MOVE
  sharing type ZM1.K.M.t = ZM2.K.M.t

  include ZIPPER_MOVE
  where type 'a from = 'a ZM1.from * 'a ZM2.from
  where type 'a to = 'a ZM1.to * 'a ZM2.to
  sharing type ZM1.K.M.t = K.M.t
  sharing type ZM2.K.M.t = K.M.t
end

functor Pair_Bi_Zipper_Move_Pair_Zipper_Move(
    type ('a, 'b) content
    structure ZM : PAIR_ZIPPER_MOVE
  ) : PAIR_BI_ZIPPER_MOVE =
struct
structure ZM1 =
  Bi_Zipper_Move_Zipper_Move(type ('a, 'b) content = ('a, 'b) content; structure ZM = ZM.ZM1)
structure ZM2 =
  Bi_Zipper_Move_Zipper_Move(type ('a, 'b) content = ('a, 'b) content; structure ZM = ZM.ZM2)
structure ZM =
  Bi_Zipper_Move_Zipper_Move(type ('a, 'b) content = ('a, 'b) content; structure ZM = ZM)
open ZM
end

functor Pair_Zipper_Move_Pair_Bi_Zipper_Move(ZM : PAIR_BI_ZIPPER_MOVE) : PAIR_ZIPPER_MOVE =
struct
structure ZM1 = Zipper_Move_Bi_Zipper_Move(ZM.ZM1)
structure ZM2 = Zipper_Move_Bi_Zipper_Move(ZM.ZM2)
structure ZM = Zipper_Move_Bi_Zipper_Move(ZM)
open ZM
end

functor Pair_Zipper_Move(
    structure ZM1 : ZIPPER_MOVE
    structure ZM2 : ZIPPER_MOVE
    sharing type ZM1.K.M.t = ZM2.K.M.t
  ) : PAIR_ZIPPER_MOVE =
  Pair_Zipper_Move_Pair_Bi_Zipper_Move(Pair_Bi_Zipper_Move(
    structure ZM1 = Bi_Zipper_Move_Zipper_Move(type ('a, 'b) content = 'a; structure ZM = ZM1)
    structure ZM2 = Bi_Zipper_Move_Zipper_Move(type ('a, 'b) content = 'a; structure ZM = ZM2)))

signature PAIR_ZIPPER_MOVES =
sig
  structure ZM1 : ZIPPER_MOVES
  structure ZM2 : ZIPPER_MOVES

  include ZIPPER_MOVES
  where type 'a Init.from = 'a ZM1.Init.from * 'a ZM2.Init.from
  where type 'a Init.to = 'a ZM1.Init.to * 'a ZM2.Init.to
  where type 'a Up.from = 'a ZM1.Up.from * 'a ZM2.Up.from
  where type 'a Up.to = 'a ZM1.Up.to * 'a ZM2.Up.to
  where type 'a Down.from = 'a ZM1.Down.from * 'a ZM2.Down.from
  where type 'a Down.to = 'a ZM1.Down.to * 'a ZM2.Down.to
  where type 'a Left.from = 'a ZM1.Left.from * 'a ZM2.Left.from
  where type 'a Left.to = 'a ZM1.Left.to * 'a ZM2.Left.to
  where type 'a Right.from = 'a ZM1.Right.from * 'a ZM2.Right.from
  where type 'a Right.to = 'a ZM1.Right.to * 'a ZM2.Right.to
  sharing type ZM1.K.M.t = K.M.t
  sharing type ZM2.K.M.t = K.M.t
end

functor Pair_Bi_Zipper_Moves_Pair_Zipper_Moves(
    structure CA : BI_ZIPPER_MOVES_ZIPPER_MOVES_CONTENT_ARGS
    structure ZM : PAIR_ZIPPER_MOVES
    sharing type CA.K.M.t = ZM.K.M.t
  ) : PAIR_BI_ZIPPER_MOVES =
struct
structure ZM1 = Bi_Zipper_Moves_Zipper_Moves(structure CA = CA; structure ZM = ZM.ZM1)
structure ZM2 = Bi_Zipper_Moves_Zipper_Moves(structure CA = CA; structure ZM = ZM.ZM2)
structure ZM = Bi_Zipper_Moves_Zipper_Moves(structure CA = CA; structure ZM = ZM)
open ZM
end

functor Pair_Zipper_Moves_Pair_Bi_Zipper_Moves(ZM : PAIR_BI_ZIPPER_MOVES) : PAIR_ZIPPER_MOVES =
struct
structure ZM1 = Zipper_Moves_Bi_Zipper_Moves(ZM.ZM1)
structure ZM2 = Zipper_Moves_Bi_Zipper_Moves(ZM.ZM2)
structure ZM = Zipper_Moves_Bi_Zipper_Moves(ZM)
open ZM
end

functor Pair_Zipper_Moves(
    structure ZM1 : ZIPPER_MOVES
    structure ZM2 : ZIPPER_MOVES
    sharing type ZM1.K.M.t = ZM2.K.M.t
  ) : PAIR_ZIPPER_MOVES =
struct

structure CA =
struct
  structure ZMB = Zipper_Move_Base(ZM1.K)
  open ZMB
  type ('a, 'b) init_content = 'a
  type ('a, 'b) up_content = 'a
  type ('a, 'b) down_content = 'a
  type ('a, 'b) left_content = 'a
  type ('a, 'b) right_content = 'a
end

structure PZ = Pair_Zipper_Moves_Pair_Bi_Zipper_Moves(Pair_Bi_Zipper_Moves(
  structure ZM1 = Bi_Zipper_Moves_Zipper_Moves(structure CA = CA; structure ZM = ZM1)
  structure ZM2 = Bi_Zipper_Moves_Zipper_Moves(structure CA = CA; structure ZM = ZM2))
)
open PZ

end

functor Direction_Zipper_Moves(ZM : BI_ZIPPER_MOVE) : HOM_ZIPPER_MOVES = Hom_Zipper_Moves(
  structure ZM = ZM
  structure A = Arrow(Kleisli_Arrow_Apply(ZM.K.M))
  type 'a init_from = unit
  type 'a data = Zipper_Direction.direction
  val init = A.K Zipper_Direction.Init
  val up = A.K Zipper_Direction.Up
  val down = A.K Zipper_Direction.Down
  val left = A.K Zipper_Direction.Left
  val right = A.K Zipper_Direction.Right
)
