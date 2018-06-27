#print nat 
#print list 
#print or 
#print and 
#print prod 

namespace hanoi

inductive unit'
|   zero : unit' 
open unit'

theorem everything_is_zero :
    ∀ u : unit', u = zero :=
λ u, @unit'.rec
    (λ u, u = zero) rfl u 
set_option pp.beta true
#check @unit'.rec
    (λ u, u = zero)
#print unit'.rec

#print or.rec

inductive and'(a b : Prop):Prop
|intro : a → b → and'

#print and'.rec  

theorem and'.left {a b: Prop}
(h : and' a b) : a :=
@and'.rec a b a
(λ (ha : a)(hb : b), ha) h

theorem and'.right{a b: Prop}
(h : and' a b) : b :=
@and'.rec a b b
(λ (ha : a)(hb : b), hb) h

inductive weird: Type
|succ (n:weird):weird 

#print weird.rec 

#print false.rec 
#print not

#reduce @nat.rec (λ n, nat) 0
    (λ prev IH, nat.succ IH) 0

#check @congr_arg

theorem no_weird(n:weird):false :=
@weird.rec(λ n:weird, false)
    (λ a b, b) n
#print nat.rec 

def nat_identity : nat → nat :=
@nat.rec(λ n, nat) 0
(λ prev IH, nat.succ IH)

theorem nat_identity_is_id 
(n: nat) :
nat_identity n = n :=
@nat.rec
    (λ n, nat_identity n = n)
    rfl 
    (λ n IH,
        show nat_identity (nat.succ n)
            = nat.succ n, from
        show nat.succ (nat_identity n)
            = nat.succ n, from
        congr_arg nat.succ IH)
    n

inductive my_ind :Type
|one : my_ind
|two : my_ind
|three (x:nat): my_ind
|four : ∀ (x:nat), my_ind
|five : ∀ (x:nat)
    (y:nat), my_ind
|six : ∀ (x:nat)
    (y:my_ind), my_ind

#print my_ind.six
#print my_ind.rec

end hanoi


