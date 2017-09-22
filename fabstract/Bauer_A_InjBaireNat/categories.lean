-- a random and incomplete selection of notions in category theory

import meta_data

structure category :=
    (obj : Type)
    (hom : obj → obj → Type)
    (id : Π (A : obj), hom A A)
    (compose : Π {A B C : obj}, hom B C → hom A B → hom A C)
    (id_left : Π {A B : obj} {f : hom A B}, compose (id B) f = f)
    (id_right : Π {A B : obj} {f : hom A B}, compose f (id A) = f)
    (compose_assoc : Π {A B C D : obj} (f : hom A B) (g : hom B C) (h : hom C D),
                       compose (compose h g) f = compose h (compose g f))

-- this is probably wrong
local infix ∘ := category.compose _

definition monomorphism {C : category} {X Y : C.obj} (f : C.hom X Y) :=
  ∀ (Z : C.obj) (g h : C.hom Z X), f ∘ g = f ∘ h → g = h

structure terminal_object {C : category} :=
    (terminal_object : C.obj)
    (terminal_morphism : Π (A : C.obj), C.hom A terminal_object)
    (hom_to_terminal : ∀ (A : C.obj) (f g : C.hom A terminal_object), f = g)

-- exponentials in a category
unfinished missing_exponential_structure : Type :=
{ description := "remaining properties of exponentials"
}

structure exponential {C : category} (A B : C.obj) :=
     (underlying_object : C.obj)
     (exponential_structure : missing_exponential_structure)
