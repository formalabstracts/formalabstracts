import meta_data
       .toposes
       .realizability


namespace Bauer_A_InjBaireNat

noncomputable theory

def Bauer_A_InjBaireNat_paper : cite :=
cite.Document
 { title     := "An injection from the Baire space to natural numbers",
   authors   := [{name := "Bauer, Andrej"}],
   doi       := "10.1017/S0960129513000406",
   source    := "Mathematical Structures in Computer Science",
   year      := ↑2015,
   reference := "Mathematical Structures in Computer Science 25:7, 1484--1489 (2015)" }

-- we construct a partial combinatory algebra based on
-- infinite-time Turing machines
unfinished J : PCA :=
{ description := "a partial-combinatory algebra constructured from infinite time turing machine",
  sources     := [cite.Item Bauer_A_InjBaireNat_paper "Section 3",
                  cite.Document 
                  { title     := "Infinite time Turing machines",
                    authors   := [{name := "Hamkins, Joel David"}],
                    doi       := "10.1023/A:1021180801870",
                    source    := "Minds and Machines",
                    year      := ↑2002,
                    arxiv     := "math/9808093",
                    url       := "", 
                    reference := "Minds and Machines 12:4, 521--539 (2002)" } ] }

definition RT_J := RT J

definition N := RT_J.nno.underlying_object

definition Baire := (RT_J.exponent N N).underlying_object

unfinished Baire_to_N : RT_J.underlying_category.hom Baire N :=
{ description := "A morphism from N^N to N",
  sources     := [cite.Item Bauer_A_InjBaireNat_paper "Section 4"] }

unfinished Baire_to_N_is_mono : monomorphism Baire_to_N :=
{ description := "The morphism Baire_to_N from N^Nto N is mono",
  sources     := [cite.Item Bauer_A_InjBaireNat_paper "Section 4"] }

def fabstract : fabstract := 
{ description  := "We construct a realizability topos in which the reals are embedded in the natural numbers. The topos is based on infinite-time Turing machines of Joel Hamkins.",
  contributors := [{name := "Andrej Bauer", homepage := "http://www.andrej.com"}],
  sources      := [Bauer_A_InjBaireNat_paper,
                   cite.Website "http://math.andrej.com/2011/06/15/constructive-gem-an-injection-from-baire-space-to-natural-numbers/", -- blog
                   cite.Website "https://vimeo.com/30368682" -- video of a talk about the paper
  ],
  results      := [result.Construction J,
                   result.Construction Baire_to_N,
                   result.Proof Baire_to_N_is_mono] }

end Bauer_A_InjBaireNat
