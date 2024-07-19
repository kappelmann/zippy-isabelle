(*  Title:      HOCLP/zipper_direction.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPER_DIRECTION =
sig
  datatype direction = Init | Left | Right | Up | Down
end

structure Zipper_Direction : ZIPPER_DIRECTION =
struct
datatype direction = Init | Left | Right | Up | Down
end
