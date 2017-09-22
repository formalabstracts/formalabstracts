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


/- A datatype describing a person, normally an author. You may leave out
   most fields, but name has to be there. -/
structure author :=
(name : string)
(institution : string := "")
(homepage : string := "")
(email : string := "")

meta instance : has_to_format author := ⟨λ a, a.name⟩

structure document :=
(title : string)
(authors : list author)
(doi : string := "") -- write everything starting from the DOI prefix (which is 10)
(arxiv : string := "") -- write these as Arxiv "1707.04448"
(url : string := "")
(source : string := "") -- journal or book title
(year : option nat := none)
(reference : string := "") -- reference formatted with title, volume, issue, pages, year, etc


/- There will be many citations everywhere, so it is a good idea
   to introduce a datatype for them early on. Here are some typical
   uses case:

   * DOI "10.1000/123456" -- Digital Object Identifier https://doi.org/10.1000/123456
   * Arxiv "1234.56789" -- ArXiV entry https://arxiv.org/abs/1234.56789
   * URL "…" -- any Uniform Resource Locator
   * Reference "…" -- string description of an article, as done traditionally by journals
   * Ibidem -- use this if you refer to the primary fabstract source itself
   * Item X E -- refer to entry E in source X, for instance:
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
| Document : document → cite
| Website : string → cite
| Folklore : cite
| Item : cite → string → cite -- refer to specific item in a source

private meta def cite_to_format : cite → format
| (cite.Document d) := "Document"
| (cite.Website s) := s
| (cite.Folklore) := "Folklore"
| (cite.Item c s) := "(" ++ cite_to_format c ++ ") item " ++ s

meta instance : has_to_format cite := ⟨cite_to_format⟩

/-
TODO: This definition forces all the results in a particular fabstract
to lie in the same universe.

Each formal abstract contains an instance of the meta_data structure,
describing the contents. We insist that there be a primary source, since
giving multiple equivalent sources (say a journal paper and the ArXiv version)
makes it impossible to resolve conflicts when they arise. The primary source
is always to be taken as the official one.
-/
structure meta_data :=
(description : string) -- short description of the contents
(contributors : list author := []) -- list of contributors
(sources : list cite := [])

meta instance : has_to_format meta_data :=
⟨λ md, "{ description : " ++ md.description ++ "\n  contributors : " ++ to_fmt md.contributors ++ "\n  sources : " ++ to_fmt md.sources ++ " }"⟩

structure {u} fabstract extends meta_data :=
(results : list (result.{u}))


section user_commands
open lean.parser tactic interactive

@[user_attribute] meta def meta_data_tag : user_attribute unit pexpr :=
{ name := `meta_data,
  descr := "",
  parser := types.texpr,--lean.parser.pexpr,
  after_set := some (λ n _ _,
    do mdp ← meta_data_tag.get_param n,
       to_expr ``(%%mdp : meta_data) >> return ()) }

meta def get_meta_data (n : name) : tactic meta_data :=
do mdp ← meta_data_tag.get_param n,
   to_expr ``(%%mdp : meta_data) >>= eval_expr meta_data

@[user_attribute] meta def unfinished_attr : user_attribute unit unit :=
{ name := `unfinished,
  descr := "This declaration is missing a definition" }

meta def add_unfinished (nm : name) (tp data : expr ff) : command :=
do eltp ← to_expr tp,
   let axm := declaration.ax nm [] eltp,
   add_decl axm,
   unfinished_attr.set_param nm () tt,
   meta_data_tag.set_param nm data tt

@[user_command]
meta def unfinished_cmd (meta_info : decl_meta_info) (_ : parse $ tk "unfinished") : lean.parser unit :=
do nm ← ident,
   tk ":",
   tp ← lean.parser.pexpr 0,
   tk ":=",
   struct ← lean.parser.pexpr,
   add_unfinished nm tp struct


meta def print_all_unfinished : command :=
do ns ← attribute.get_instances `unfinished,
   ns.mmap (λ n, do trace n, get_meta_data n >>= trace),
   return ()

end user_commands
