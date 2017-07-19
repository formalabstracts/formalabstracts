# The fabstracts repository

The repository is organized into folders, one per fabstract, which allows a complicated
fabstract to be split into several files. The following conventions are enforced by the
curators.

### The name of the fabstract folder

The name of the folder has the form

    Author1_and_Author2_and_…_TitleAcronym

where each `AuthorN` has the form `Lastname_Initials`, and `Initials` are the initials
separated by undercores. There is currently no good convention on how to create
`TitleAcronym`. Look at the existing abstracts for conventions.

If there are very many authors, it is permissible to use `Author1_et_al_TitleAcronym`.
There is no formal definition of "very many".

### The contents of the fabstract folder

You may put arbitrary auxiliary Lean files in the folder. You *must* include a file called
`fabstract.lean` which must have the following form:

```lean
⟨other imports⟩
import meta_data
namespace Author1_and_Author2_and_…_TitleAcronym

⟨auxiliary development⟩

def fabstract : meta_data = {
  authors := …,
  primary := …,
  secondary := …,
  description := …,
  results := …
}

end Author1_and_Author2_and_…_TitleAcronym
```

The `results` field should list the main results of the paper. Consult the `result` type
in `meta_data` to see what these may be. The authors field is a list of authors, each of
which is a value of type `author` from `meta_data`.

### How to mark unfinished formalization

It is quite unlikely that you will specify the fabstract completely, because that would
require you to define *all* mathematics that the paper relies on, and that might take
years. We have therefore provided a mechanism for marking unfinished parts using the
`unfinished` keyword.

Suppose that in your formalization you need to use the space of square-integrable
measurable functions, but there is no such definition yet. You may introduce an unfinished
definition as follows:

```lean
unfinished L2 : Type :=
{ description := "The set $L_2([0,1])$ of square-integrable measurable functions on the unit interval.",
  references := […] }
```

The description should be good enough for a professional mathematician to be able to tell
what the object is supposed to be. It is very helpful to provide a list of references (see
the `cite` datatype defined in [meta_data.lean](/meta_data.lean)), but if the result is
well-known, you can leave it out.

You will of course also need some further structure on `L2`, for example the vector space
structure. You can just keep going with `unfinished`:

```lean
unfinished L2_add : L2 → L2 → L2 :=
{ description := "Addition of functions.",
  references := […] }

unfinished L2_scalar_mult : ℝ → L2 → L2 :=
{ description := "Scalar multiplication of functions.",
  references := […] }

…
```

You may of course assume well-known theorems and any other statements that you need:

```lean
unfinished Well_known_theorem :
  ⟨statement of theorem⟩ :=
{ description := "⟨informal description of theorem⟩",
  references := […] }
```

It is also quite likely that you will *not* formalize all the proofs and definitions from
the paper, because that is just too much work. You may use the same `unfinished` mechanism
again, but this time provide a reference to your paper so that people can tell how to
match the formalized entity with the corresponding one in the paper. For instance, suppose
that your paper introduces a very complicated notion of *hyper-semi-quasi-space* in
Definition 4.2, defines what it means for a hyper-semi-quasi-space to have the *McDonald
property* in Definition 5.1, and then shows that no hyper-semi-quasi-space has it in
Theorem 6.9. The minimal formalization would look like this:

```lean
unfinished hyper_semi_quasi_space : Type :=
{ description := "…",
  references := [cite.Item cite.Ibidem "Definition 4.2"] }

unfinished is_McDonald : hyper_semi_quasi_space → Prop :=
{ description := "…",
  references := [cite.Item cite.Ibidem "Definition 5.1"] }

unfinished hyper_semi_quasy_space_not_McDonald :
  ∀ X, ¬ (is_McDonald X) :=
{ description := "…",
  references := [cite.Item cite.Ibidem "Theorem 6.9"] }
```

It is always easy to check which parts of formalization are unfinished with the `#print axioms` command.
