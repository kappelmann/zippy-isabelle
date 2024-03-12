(*  Title:      HOCLP/container.ML
    Author:     Kevin Kappelmann
*)
signature CONTAINER =
sig
  type 'a container
end

structure Container : CONTAINER =
struct

type 'a container = 'a List.t

end