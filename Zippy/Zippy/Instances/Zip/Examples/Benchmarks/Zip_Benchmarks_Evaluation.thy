\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zip_Benchmarks_Evaluation
  imports
    Zip_Benchmarks_Setup
begin

declare[[ML_print_depth=20000]]
ML_command\<open>
local open Zip_Benchmark.Export
in
val export_dir = \<^path>\<open>export\<close>
val export = mk_export export_dir
val get_key = fst
val modify_key = apfst
val get_data = snd
val modify_data = apsnd
fun map_data f = map f |> modify_data
fun get_pos (_, pos, _) = pos
fun get_timing (_, _, (timing, _)) = timing
fun is_success (_, _, (_, res)) = Either.cases (K false) I res
  (* |> (fn b => if b then () else writeln "OMG") *)

fun group_filename xs = AList.group (apply2 Path.file_name #> (op =)) xs
  |> map (apfst Path.file_name)
(* val ord = apply2 (snd #> fst) #> make_ord (op >) *)
(* val join = export
  |> modify_data (AList.group (K true) #> hd #> get_data #> flat
  #> maps get_data
  #> group_filename
  #> map (modify_data (flat #> group_filename
  #> map (modify_data (map (`(get_timing #> #cpu) #> apsnd get_pos)
  #> (fn [(t1, x), (t2, _)] => (t1 - t2, x))
  ))))) *)
  (* |> modify_data (maps snd #> sort ord) *)
  (* |> get_data |> maps get_data  *)
  (* |> @{print} *)
val foo = export
  |> get_data |> drop 1 |> hd
  |> get_data |> maps get_data |> maps get_data
  |> filter (get_data #> is_success)
  |> length
  |> @{print}

(* val ord = apply2 (snd #> get_timing #> #cpu) #> make_ord (op >)
val sorted = export
  |> map_data (map_data (map_data (modify_data (sort ord))))
fun get key xs = AList.lookup (apsnd Path.file_name #> uncurry match_string) xs key |> the *)
(* val word = sorted |> snd
  |> get "zippy"
  |> get "*"
  |> get "Binom"
  |> map (modify_data (`(get_pos #> Position.line_of) #> apsnd ((get_timing #> #cpu))))
  |> take 40
  |> @{print} *)
end
\<close>

end