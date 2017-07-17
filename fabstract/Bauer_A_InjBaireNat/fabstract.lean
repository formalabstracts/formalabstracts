import meta_data
       .toposes
       .realizability

run_cmd tactic.skip -- temporary fix

namespace Bauer_A_InjBaireNat

noncomputable theory

-- we construct a partial combinatory algebra based on
-- infinite-time Turing machines
unfinished J : PCA :=
{ description := "a partial-combinatory algebra constructured from infinite time turing machine",
  references := [cite.Item cite.Ibidem "Section 3",
                 cite.DOI "10.1023/A:1021180801870",
                 cite.Arxiv "math/9808093"] }

definition RT_J := RT J

definition N := RT_J.nno.underlying_object

definition Baire := (RT_J.exponent N N).underlying_object

unfinished Baire_to_N : RT_J.underlying_category.hom Baire N :=
{ description := "A morphism from N^N to N",
  references := [cite.Item cite.Ibidem "Section 4"] }

unfinished Baire_to_N_is_mono : monomorphism Baire_to_N :=
{ description := "The morphism Baire_to_N from N^Nto N is mono",
  references := [cite.Item cite.Ibidem "Section 4"] }

def fabstract : meta_data := {
  description := "We construct a realizability topos in which the reals are embedded in the natural numbers. The topos is based on infinite-time Turing machines of Joel Hamkins.",
  authors := ["Andrej Bauer"],
  primary := cite.DOI "10.1017/S0960129513000406",
  secondary := [
    cite.URL "http://math.andrej.com/2011/06/15/constructive-gem-an-injection-from-baire-space-to-natural-numbers/", -- blog
    cite.URL "https://vimeo.com/30368682" -- video of a talk about the paper
  ],
  results := [result.Construction J,
              result.Construction Baire_to_N,
              result.Proof Baire_to_N_is_mono]
}

end Bauer_A_InjBaireNat
