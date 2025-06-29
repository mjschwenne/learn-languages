module Part1.Lemma

open FStar.Mul
open FStar.List.Tot

let rec factorial (n:nat) : nat = 
  if n = 0 
  then 1
  else n * factorial (n - 1)

// let _ = assert (forall (x:nat). x > 2 ==> factorial x > 2)

let rec factorial_is_positive (x:nat) : u:unit{factorial x > 0} =
  if x = 0 then () 
  else factorial_is_positive (x - 1)

let rec factorial_is_positive' (x:int) : 
  Lemma (requires x >= 0)
        (ensures factorial x > 0)
= if x = 0 then ()
  else factorial_is_positive' (x - 1)

let rec factorial_is_greater_than_arg (x:int)
  : Lemma (requires x > 2)
          (ensures factorial x > x)
  = if x = 3 then ()
    else factorial_is_greater_than_arg (x - 1)

////////////////////////////////////////////////////////////////////////////////

let rec fibonacci (n:nat)
  : nat
  = if n <= 1
    then 1
    else fibonacci (n - 1) + fibonacci (n - 2)

val fibonacci_greater_than_arg (n:nat{n >= 2})
  : Lemma (fibonacci n >= n)
// So this is the "surprising" proof since it only uses the inductive hypothesis once.
let rec fibonacci_greater_than_arg n = if n = 2 then () else fibonacci_greater_than_arg (n - 1) 
// The more traditional proof would look like this:
let rec fibonacci_greater_than_arg' n = if n <= 3 then () 
  else (
    fibonacci_greater_than_arg' (n-1);
    fibonacci_greater_than_arg' (n-2)
  )

////////////////////////////////////////////////////////////////////////////////

let rec app #a (l1 l2:list a)
  : list a
  = match l1 with
    | [] -> l2
    | hd :: tl -> hd :: app tl l2

let rec length #a (l:list a)
  : nat
  = match l with
    | [] -> 0
    | _ :: tl -> 1 + length tl

val app_length (#a:Type) (l1 l2:list a)
  : Lemma (length (app l1 l2) = length l1 + length l2)
let rec app_length #a l1 l2 = 
  match l1 with  
  | [] -> ()
  | hd :: tl -> app_length tl l2

////////////////////////////////////////////////////////////////////////////////

let rec append (#a:Type) (l1 l2:list a)
  : list a
  = match l1 with
    | [] -> l2
    | hd::tl -> hd :: append tl l2

let rec reverse #a (l:list a)
  : list a
  = match l with
    | [] -> []
    | hd :: tl -> append (reverse tl) [hd]

let snoc l h = append l [h]

let rec snoc_cons #a (l:list a) (h:a) : 
  Lemma (reverse (snoc l h) == h :: reverse l)
  = match l with 
    | [] -> ()
    | hd :: tl -> snoc_cons tl h

let rec rev_involutive #a (l:list a)
  : Lemma (reverse (reverse l) == l)
  = match l with 
    | [] -> ()
    | hd :: tl -> rev_involutive tl;
                snoc_cons (reverse tl) hd

// My proof, which uses an incomplete match pattern match I 
// was expecting F* to make me go back and complete. 
let rec rev_injective (#a:Type) (l1 l2:list a)
  : Lemma (requires reverse l1 == reverse l2)
          (ensures  l1 == l2)
  = match l1, l2 with 
    | [], [] -> ()
    | hd1 :: tl1, hd2 :: tl2 -> // Lets us unfold reverse in the precondition to 
                            // append (reverse tl1) [hd1] = append (reverse tl2) [hd2] 
                            // then simplify to
                            // hd1 :: reverse (tl1) = hd2 :: reverse (tl2)  
                            snoc_cons (reverse tl1) hd1;
                            snoc_cons (reverse tl2) (hd2);
                            // Needed for the precondition on rev_injective...
                            // But why? 
                            // 
                            // Looking at my software foundations answer for the same 
                            // problem (really benefiting from the fact that some of 
                            // these exercises are common), it's so that we can derive 
                            // reverse (reverse tl1) = reverse (reverse tl2) 
                            // and that helps the smt solver prove the precondition.
                            rev_involutive tl1; 
                            rev_involutive tl2;
                            rev_injective tl1 tl2

// The first proof in the F* solution.
let rec snoc_injective (#a:Type) (l1:list a) (h1:a) (l2:list a) (h2:a)
  : Lemma (requires snoc l1 h1 == snoc l2 h2)
          (ensures  l1 == l2 /\ h1 == h2)
  = match l1, l2 with 
    | _ :: tl1, _ :: tl2 -> snoc_injective tl1 h1 tl2 h2
    | _ -> ()

let rec rev_injective' (#a:Type) (l1 l2:list a)
  : Lemma (requires reverse l1 == reverse l2)
          (ensures  l1 == l2)
  = match l1, l2 with 
    | h1 :: t1, h2 :: t2 -> snoc_injective (reverse t1) h1 (reverse t2) h2;
                        rev_injective' t1 t2
    | _, _ -> ()

// Finally, if I looked at the software foundations proof first, I may have 
// come up with this, which isn't even in inductive proof
let rev_injective'' (#a:Type) (l1 l2:list a)
  : Lemma (requires reverse l1 == reverse l2)
          (ensures  l1 == l2)
  = rev_involutive l1; rev_involutive l2

////////////////////////////////////////////////////////////////////////////////

let rec map #a #b (f: a -> b) (l:list a)
  : list b
  = match l with
    | [] -> []
    | hd::tl -> f hd :: map f tl

//write a type for find
let rec find f l =
  match l with
  | [] -> None
  | hd :: tl -> if f hd then Some hd else find f tl

////////////////////////////////////////////////////////////////////////////////

//Write a simpler type for find and prove the lemmas below
let rec find_alt f l =
  match l with
  | [] -> None
  | hd :: tl -> if f hd then Some hd else find_alt f tl

let rec find_alt_ok #a (f:a -> bool) (l:list a)
  : Lemma (match find_alt f l with
           | Some x -> f x
           | _ -> true)
  = match l with
    | [] -> ()
    | _ :: tl -> find_alt_ok f tl

////////////////////////////////////////////////////////////////////////////////

let rec fold_left #a #b (f: b -> a -> a) (l: list b) (acc:a)
  : a
  = match l with
    | [] -> acc
    | hd :: tl -> fold_left f tl (f hd acc)

let fold_left_Cons_is_rev (#a:Type) (l:list a)
  : Lemma (fold_left Cons l [] == reverse l)
  = admit()

////////////////////////////////////////////////////////////////////////////////

let rec rev_aux #a (l1 l2:list a)
  : Tot (list a) (decreases l2)
  = match l2 with
    | []     -> l1
    | hd :: tl -> rev_aux (hd :: l1) tl

let rev #a (l:list a) : list a = rev_aux [] l

let rev_is_ok #a (l:list a)
  : Lemma (rev l == reverse l)
  = admit()

////////////////////////////////////////////////////////////////////////////////

let rec fib (a b n:nat)
  : Tot nat (decreases n)
  = match n with
    | 0 -> a
    | _ -> fib b (a+b) (n-1)

let fib_tail (n:nat) : nat = fib 1 1 n

let fib_tail_is_ok (n:nat)
  : Lemma (fib_tail n == fibonacci n)
  = admit()
