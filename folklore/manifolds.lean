/- Differentiable manifolds -/
class_infix `category.comp `( ∘ )

class category :=
(object : Type)
(∀ ( a b : object), mor a b : Type)
( ( ∘ ) : Π a b c, mor a b → mor b c → mor a c)
(id : Π a, mor a a)
(id_left : ∀ a b, ∀ f : mor a b, f ∘ id a = f)
(id_right : ∀ a b, ∀ f : mor a b, id b ∘ f ∘ = f)
(assoc : ∀ a b c d, ∀ (f : mor a b) (g : mor b c) (h : mor c d), h ∘ (g ∘ f) = (h ∘ g) ∘ f)

