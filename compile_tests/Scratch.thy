theory Scratch
  imports
    Pure
begin

ML\<open>
val x = funpow 4 (fn x => x * x) 2
\<close>

ML\<open>
type ('a1, 'a2) test0 = 'a1 * 'a2
type ('a1, 'a2) test1 = (('a1, 'a2) test0, ('a1, 'a2) test0) test0
type ('a1, 'a2) test2 = (('a1, 'a2) test1, ('a1, 'a2) test1) test1
type ('a1, 'a2) test3 = (('a1, 'a2) test2, ('a1, 'a2) test2) test2
type ('a1, 'a2) test4 = (('a1, 'a2) test2, ('a1, 'a2) test2) test3
type ('a1, 'a2) test3_4 = (('a1, 'a2) test2, ('a1, 'a2) test2) test3;
\<close>

ML\<open>
fun foo (x : ('a1, 'a2) test3) : ('a1, 'a2) test3 = x
\<close>

ML\<open>
fun foo (x : ('a1, 'a2) test3_4) : ('a1, 'a2) test3_4 = x
\<close>

ML\<open>
(* fun foo (x : ('a1, 'a2) test4) : ('a1, 'a2) test4 = (x : ('a1, 'a2) test4) *)
\<close>

(* ML\<open>
signature TEST =
sig
type ('a1, 'a2) test
end

functor Inst_Test(T : TEST) : TEST =
struct
type ('a1, 'a2) test = (
    ('a1, 'a2) T.test,
    ('a1, 'a2) T.test
  ) T.test
end
\<close> *)

(* ML\<open>
structure Test : TEST =
struct
type ('a1, 'a2) test = 'a1 * 'a2
end

structure Test = Inst_Test(Test)
structure Test = Inst_Test(Test)
structure Test = Inst_Test(Test)
structure Test = Inst_Test(Test)
structure Test = Inst_Test(Test)
structure Test = Inst_Test(Test)
\<close> *)

end
