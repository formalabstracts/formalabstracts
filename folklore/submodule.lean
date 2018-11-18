
import        .banach

noncomputable theory

open set filter classical

local attribute [instance] prop_decidable

universes u v w


namespace substructure

variable { α : Type u}

class sub_add_comm_group [add_comm_group α] (D : set α) :=
(nonempty : ∃ (x : α), x ∈ D)
(closure_group : ∀ (x y : α), x ∈ D ∧ y ∈ D → x - y ∈ D)

axiom exists_sub_add_comm_group (D : set α) [add_comm_group α] [sub_add_comm_group D] :
(∃! 

#print sub_add_comm_group

class sub_ (D : set α) [add_comm_group α] [sub_add_comm_group D] :=






end substructure
