module GeneralizedLogic

let maximum_trust : nat = 100
let measure = (p:nat { p <= maximum_trust })

type measured_bool = 
  | T : (p:measure) -> measured_bool 
  | F : (p:measure) -> measured_bool

let mb = measured_bool
let min (x y: measure) : measure = if x <= y then x else y
let max (x y: measure) : measure = if x <= y then y else x

let ( * ) (a b: measured_bool) = match a,b with
  | (F n, F m) -> F (min n m)
  | (F n, T m) -> F n
  | (T n, F m) -> F m
  | (T n, T m) -> T (min n m)
  
let ( + ) (a b: measured_bool) = match a,b with
  | (F n, F m) -> F (max n m)
  | (F n, T m) -> T m
  | (T n, F m) -> T n
  | (T n, T m) -> T (max n m)
  
let op_Minus (x: measured_bool) = match x with
  | T n -> F n
  | F n -> T n

let not_or_lemma (x y: measured_bool) : Lemma (-(x+y) == (match x,y with
  | (F n, F m) -> T (max n m)
  | (F n, T m) -> F m
  | (T n, F m) -> F n
  | (T n, T m) -> F (max n m)
)) = ()

let and_nots_lemma (x y: measured_bool) : Lemma ((-x)*(-y) == (match x,y with
  | (F n, F m) -> T (min n m)
  | (F n, T m) -> F m
  | (T n, F m) -> F n
  | (T n, T m) -> F (min n m)
)) = ()

let or_is_commutative (x y: measured_bool)       : Lemma (x+y       == y+x) = ()
let or_is_associative (x y z: measured_bool)     : Lemma ((x+y)+z   == x+(y+z)) = ()
let and_is_commutative (x y: measured_bool)      : Lemma (x*y       == y*x) = ()
let and_is_associative (x y z: measured_bool)    : Lemma ((x*y)*z   == x*(y*z)) = ()
let or_and_distributivity (x y z: measured_bool) : Lemma (x*(y+z)   == x*y + x*z) = ()
let and_or_distributivity (x y z: measured_bool) : Lemma (x+(y*z)   == (x+y)*(x+z)) = ()

let xor (a b: measured_bool) = match a,b with
  | (F n, F m) -> F (min n m)
  | (F n, T m) -> T m
  | (T n, F m) -> T n
  | (T n, T m) -> T (min n m)
  
let imp (a b: measured_bool) = match a,b with
  | (F n, F m) -> T (min n m)
  | (F n, T m) -> T n
  | (T n, F m) -> F n
  | (T n, T m) -> T (min n m)

let eqv (a b: measured_bool) = match a,b with
  | F n, F m -> T (min n m)
  | F n, T m -> F (min n m)
  | T n, F m -> F (min n m)
  | T n, T m -> T (min n m)

let nor (a b: measured_bool) = match a,b with
  | F n, F m -> T (max n m)
  | F n, T m -> F m
  | T n, F m -> F n
  | T n, T m -> F (max n m)
  
let nand (a b: measured_bool) = match a,b with
  | F n, F m -> T (min n m)
  | F n, T m -> T n
  | T n, F m -> T m
  | T n, T m -> F (min n m)

let nor_is_not_xy (x y: measured_bool) : Lemma (-(x+y) == nor x y) = ()
let nand_is_not_xy (x y: measured_bool) : Lemma (-(x*y) == nand x y) = ()

let eqv_formula (x y: measured_bool) : Lemma (((x*y) + ((-x)*(-y))) == (match x,y with
  | (F n, F m) -> (T (min n m))
  | (F n, T m) -> (F (max n m))
  | (T n, F m) -> (F (max n m))
  | (T n, T m) -> (T (min n m))
)) = () 

let eqv_axiom (x y: measured_bool) : Lemma (eqv x y == (match x,y with
  | (F n, F m) -> (T (min n m))
  | (F n, T m) -> (F (min n m))
  | (T n, F m) -> (F (min n m))
  | (T n, T m) -> (T (min n m))
)) = () 

let imp_formula (x y: measured_bool) : Lemma (((-x)+y) == (match x,y with
  | (F n, F m) -> T n
  | (F n, T m) -> T (max n m)
  | (T n, F m) -> F (max n m)
  | (T n, T m) -> T m
)) = ()

let imp_axiom (x y: measured_bool) : Lemma (imp x y == (match x,y with
  | (F n, F m) -> T (min n m)
  | (F n, T m) -> T n
  | (T n, F m) -> F n
  | (T n, T m) -> T (min n m)
)) = ()





let zero : measured_bool = F 0
 
let one : measured_bool = T maximum_trust

let one_is_mul_identity (x: measured_bool) : Lemma (x*one == x) = ()
let zero_is_add_identity (x: measured_bool) : Lemma (x+zero == x) = ()

[@@expect_failure]
let tertium_non_datur (x: measured_bool) : Lemma ((-x)*x == one) = ()

[@@expect_failure]
let xor_is_valid (x y: measured_bool) : Lemma ((x `xor` y) == (-((x*y) + ((-x)*(-y))))) = ()
 
[@@expect_failure]
let de_morgan (x y: measured_bool) : Lemma (-(x*y) == (-x)+(-y)) = ()

[@@expect_failure]
let imp_is_valid (x y: measured_bool) : Lemma (x `imp` y == -x + y) = () 



  
