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
           cite := […] }
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

/- There will be many citations everywhere, so it is a good idea
   to introduce a datatype for them early on. Here are some typical
   uses case:

   * DOI "10.1000/123456" -- Digital Object Identifier https://doi.org/10.1000/123456
   * Arxiv "1234.56789" -- ArXiV entry https://arxiv.org/abs/1234.56789
   * URL "…" -- any Uniform Resource Locator
   * Reference "…" -- string description of an article, as done traditionally by journals
   * Ibidem -- use this if you refer to the primary fabstract source itself
   * Item X E -- refer to entry Ein source X, for instance:
        * Item (Arxiv "1234.56789") "Theorem 3.4" -- theorem 3.4 in ArXiV 1234.56789
        * Item Ibidem "Definition 1.2" -- definition 1.2 in the primary fabstract source

   Use your programming skills! For instance, suppose you refer a lot to entries in

      Reference "Euclid N.N., Elements (five volumes), 300 B.C., Elsevier"

   Then you need not keep writing things like

      Item (Reference "Euclid N.N., Elements (five volumes), 300 B.C., Elsevier") "Proposition IV.2"
      Item (Reference "Euclid N.N., Elements (five volumes), 300 B.C., Elsevier") "Proposition I.1"
      …

   Instead, define a shorthand:

     definition Elements x :=
       Item (Reference "Euclid N.N., Elements (five volumes), 300 B.C., Elsevier") x

   and then it is easy:

     Elements "IV.2"
     Elements "I.1"

-/
inductive cite
  | DOI : string → cite -- write evertying starting from the DOI prefix (which is 10)
  | Arxiv : string → cite -- write these as Arxiv "1707.04448"
  | URL : string → cite
  | Reference : string → cite
  | Ibidem : string → cite -- refer to original source (if fabstract has just one)
  | Item : cite → string → cite -- refer to specific item in a source

/-
TODO: This definition forces all the results in a particular fabstract
to lie in the same universe.

Each formal abstract contains an instance of the meta_data structure,
describing the contents. We insist that there be a primary source, since
giving multiple equivalent sources (say a journal paper and the ArXiv version)
makes it impossible to resolve conflicts when they arise. The primary source
is always to be taken as the official one.
-/
structure {u} meta_data : Type (u+1) :=
    (description : string) -- short description of the contents
    (authors : list string) -- list of authors
    (primary : cite) -- primary source (the most official one)
    (secondary : list cite) -- auxiliary and alternative sources (such as ArXiv equivalent)
    (results : list (result.{u})) -- the list of results

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
    (references : list cite)

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
