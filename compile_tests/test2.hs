type Test0 a1 a2 = (a1, a2)
type Test1 a1 a2 = Test0 (Test0 a1 a2) (Test0 a1 a2) 
type Test2 a1 a2 = Test1 (Test1 a1 a2) (Test1 a1 a2) 
type Test3 a1 a2 = Test2 (Test2 a1 a2) (Test2 a1 a2) 
type Test4 a1 a2 = Test3 (Test3 a1 a2) (Test3 a1 a2) 

type Copy_test0 a1 a2 = (a1, a2)
type Copy_test1 a1 a2 = Copy_test0 (Copy_test0 a1 a2) (Copy_test0 a1 a2) 
type Copy_test2 a1 a2 = Copy_test1 (Copy_test1 a1 a2) (Copy_test1 a1 a2) 
type Copy_test3 a1 a2 = Copy_test2 (Copy_test2 a1 a2) (Copy_test2 a1 a2) 
type Copy_test4 a1 a2 = Copy_test3 (Copy_test3 a1 a2) (Copy_test3 a1 a2) 

foo :: Test4 a1 a2 -> Copy_test4 a1 a2
foo x = x

main = return ()
