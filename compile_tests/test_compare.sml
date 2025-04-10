type ('a1, 'a2) test0 = 'a1 * 'a2;
type ('a1, 'a2) test1 = (('a1, 'a2) test0, ('a1, 'a2) test0) test0;
type ('a1, 'a2) test2 = (('a1, 'a2) test1, ('a1, 'a2) test1) test1;
type ('a1, 'a2) test3 = (('a1, 'a2) test2, ('a1, 'a2) test2) test2;
type ('a1, 'a2) test4 = (('a1, 'a2) test3, ('a1, 'a2) test3) test3;
(*size between test3 and test4*)
type ('a1, 'a2) test3_4 = (('a1, 'a2) test2, ('a1, 'a2) test2) test3;


type ('a1, 'a2) copy_test0 = 'a1 * 'a2;
type ('a1, 'a2) copy_test1 = (('a1, 'a2) copy_test0, ('a1, 'a2) copy_test0) copy_test0;
type ('a1, 'a2) copy_test2 = (('a1, 'a2) copy_test1, ('a1, 'a2) copy_test1) copy_test1;
type ('a1, 'a2) copy_test3 = (('a1, 'a2) copy_test2, ('a1, 'a2) copy_test2) copy_test2;
type ('a1, 'a2) copy_test4 = (('a1, 'a2) copy_test3, ('a1, 'a2) copy_test3) copy_test3;
type ('a1, 'a2) copy_test3_4 = (('a1, 'a2) copy_test2, ('a1, 'a2) copy_test2) copy_test3;

(*slow with polyml*)
fun foo (x : ('a1, 'a2) test3_4) : ('a1, 'a2) copy_test3_4 = x;

(*too slow with polyml; works with MLton and SML/NJ*)
(* fun foo (x : ('a1, 'a2) test4) : ('a1, 'a2) copy_test4 = x; *)

fun main () = foo;

val _ = main ()
