(*  Title:      Universal_Data/universal_data.ML
    Author:     Kevin Kappelmann

Generic Data that can hold any type of information.
*)
signature UNIVERSAL_DATA =
sig

type 'a var
val insert : 'a -> Context.generic -> 'a var * Context.generic
val put : 'a var -> 'a -> Context.generic -> Context.generic
val get : 'a var -> Context.generic -> 'a
val map : 'a var -> ('a -> 'a) -> Context.generic -> Context.generic

end

structure Universal_Data : UNIVERSAL_DATA =
struct

structure Data = Generic_Data
(
  type T = Universal.universal Inttab.table
  val empty = Inttab.empty
  val merge = Inttab.merge (K true)
)

abstype 'a var = Var of serial * 'a Universal.tag
with

fun var () = Var (serial (), Universal.tag ())

fun insert data context =
  let val (v as Var (i, tag)) = var ()
  in (v, Data.map (Inttab.update (i, Universal.tagInject tag data)) context) end

fun get (Var (i, tag)) context =
  case Inttab.lookup (Data.get context) i of
    SOME u => Universal.tagProject tag u
  | NONE => error "Universal var not found"

fun map (Var (i, tag)) f context =
  Data.map (Inttab.map_entry i (Universal.tagInject tag o f o Universal.tagProject tag)) context
  handle Match => error "Universal var not found"

fun put var data = map var (K data)

end

end
