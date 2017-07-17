/- Each fabstract contains a list of results. The following type lists the
   various kinds of results. You may read the values as follows:

   * `Proof p` -- the paper contains the proof `p`
   * `Construction c` -- the paper contains the construction `c`
   * `Conjecture C` -- the paper contains the conjecture `C`

   Let us take a typical situation: you want to state that the paper
   contains a proof of some statement `S`, but you do not want to actually
   formalize the proof from the paper. In this case the fabstract would
   contain

       definition S := ⟨formalization of statement S⟩
       unfinished proof_of_S : S :=
         { description := "… describe the proof …",
           doi := […] }
       ⋮
       definition fabstract : meta_data := {
          …,
          results = […, Proof proof_of_S, …]
       }

   This way, by using `#print axioms fabstract`, you can find out precisely
   which bits of the paper have not been formalized in the fabstract. You
   can see what `proof_of_S` actually proves by inspecting its type.

   Let us take another typical situation: the paper contains a construction
   of an object `c` whose type is `T`, which is easy to formalize in Lean.
   Then you would do

       definition T := ⟨formalization of type T⟩
       definition c := ⟨formalization of construction c⟩
       ⋮
       definition fabstract : meta_data := {
          …,
          results = […, Construction c, …]
       }
-/
inductive {u} result : Type (u+1)
| Proof : Π {P : Prop}, P → result
| Construction : Π {A : Type u}, A → result
| Conjecture : Prop → result

/-
TODO: This definition forces all the results in a particular fabstract
to lie in the same universe.

Each formal abstract contains an instance of the meta_data structure,
describing the contents.
-/
structure {u} meta_data : Type (u+1) :=
    (description : string) -- short description of the contents
    (authors : list string) -- list of authors
    (doi : list string) -- references to the original article
    (results : list (result.{u})) -- the list of main results

/-
Users will want to assume that a certain objects exist,
without constructing them. These objects could be types (e.g. the
real numbers) or inhabitants of types (e.g. pi : ℝ). When we add
constants like this, we tag them with informal descriptions
(of what the structure is, or how the construction goes)
and references to the literature.
-/
structure unfinished_meta_data :=
    (description : string)
    (doi : list string)

section user_commands
open lean.parser tactic interactive

meta def add_unfinished (nm : name) (tp data : expr ff) : command :=
do eltp ← to_expr tp,
   eldt ← to_expr ``(%%data : unfinished_meta_data),
   let axm := declaration.ax nm [] eltp,
   add_decl axm,
   let meta_data_name := nm.append `_meta_data,
   add_decl $ mk_definition meta_data_name []
                  `(unfinished_meta_data) eldt

@[user_command]
meta def unfinished_cmd (meta_info : decl_meta_info) (_ : parse $ tk "unfinished") : lean.parser unit :=
do nm ← ident,
   tk ":",
   tp ← lean.parser.pexpr,
   tk ":=",
   struct ← lean.parser.pexpr,
   add_unfinished nm tp struct

end user_commands
