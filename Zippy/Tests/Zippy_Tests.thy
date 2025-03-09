\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Tests
  imports
    Zippy.Zippy_Prover_Instances
begin

ML\<open>
  fun test x y z a b = Zippy.mk_actiona_node x y z a b  |> Zippy.MS.eval @{context}
    |> (fn (x : (Proof.context, unit, unit, unit, unit, unit) Zippy.ZCORE.N5.node option) => x)
  (* fun test x y z a b = Zippy.mk_actiona_node x y z a b  *)
\<close>

thm reflexive

ML\<open>
  val a = test
\<close>

end
