-- a random selection of facts about category theory, to be
-- fleshed out.

structure category :=
  mk_category ::
    (obj : Type)
    (hom : obj -> obj -> Type)
    (id : Π (A : obj), hom A A)
    (compose : Π {A B C : obj}, hom B C -> hom A B -> hom A C)

local infix ∘ := category.compose _

definition monomorphism {C : category} {X Y : C.obj} (f : C.hom X Y) :=
  forall (Z : C.obj) (g h : C.hom Z X), f ∘ g = f ∘ h -> g = h

-- this sort of thing should probably be a type class
-- the naming convenetions do not exist yet
structure terminal_object {C : category} :=
  mk_terminal_object ::
    (terminal_object : C.obj)
    (terminal_morphism : ∀ (A : C.obj), C.hom A terminal_object)
    (hom_to_terminal : ∀ (A : C.obj) (f g : C.hom A terminal_object), f = g)
