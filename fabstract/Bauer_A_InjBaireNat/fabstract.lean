import meta_data
       .toposes
       .realizability

run_cmd tactic.skip -- temporary fix

namespace Bauer_A_InjBaireNat

noncomputable theory

-- we construct a partial combinatory algebra based on
-- infinite-time Turing machines
unfinished IITM : PCA :=
{
   description := "infinite time turing machine",
   doi := []
}

definition T := RT IITM

definition N := T.nno.underlying_object

definition Baire := (T.exponent N N).underlying_object

unfinished Baire_to_N : (T.underlying_category.hom Baire N) :=
  {
    description := "",
    doi := []
  }

unfinished Baire_to_N_is_mono : (monomorphism Baire_to_N) :=
  {
    description := "",
    doi := []
  }

open result
def fabstract : meta_data := {
  description := "We construct a realizability topos in which the reals are embedded in the natural numbers. The topos is based on infinite-time Turing machines of Joel Hamkins.",
  authors := ["Andrej Bauer"],
  doi := ["https://doi.org/10.1017/S0960129513000406"],
  results := [Construction IITM,
              Construction Baire_to_N,
              Proof Baire_to_N_is_mono]
}

end Bauer_A_InjBaireNat
