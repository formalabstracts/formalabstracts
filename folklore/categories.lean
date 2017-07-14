-- a random selection of facts about category theory, to be
-- fleshed out.

structure category :=
    (obj : Type)
    (hom : obj → obj → Type)
    (id : Π (A : obj), hom A A)
    (compose : Π {A B C : obj}, hom B C → hom A B → hom A C)

local infix ∘ := category.compose _

definition monomorphism {C : category} {X Y : C.obj} (f : C.hom X Y) :=
  ∀ (Z : C.obj) (g h : C.hom Z X), f ∘ g = f ∘ h → g = h

-- this sort of thing should probably be a type class
-- the naming convenetions do not exist yet
structure terminal_object {C : category} :=
    (terminal_object : C.obj)
    (terminal_morphism : Π (A : C.obj), C.hom A terminal_object)
    (hom_to_terminal : ∀ (A : C.obj) (f g : C.hom A terminal_object), f = g)

-- exponentials in a category
structure exponential {C : category} (A B : C.obj) :=
     (underlying_object : C.obj)
     (other_exponential_structure_for_floris_to_implement : Type)
