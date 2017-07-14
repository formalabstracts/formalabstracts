import meta_data
import folklore.categories
import folklore.toposes
import .realizability

namespace Bauer_A_InjBaireNat
noncomputable theory

-- we construct a partial combinatory algebra based on
-- infinite-time Turing machines
constant IITM : PCA

noncomputable def T := RT IITM

definition N := T.nno
definition R := dedekind_reals T

constant R_to_N : T.underlying_category.hom N.nno_object R.reals_object

axiom R_to_N_is_mono : monomorphism R_to_N

open result
meta def fabstract : meta_data := {
  description := "We construct a realizability topos in which the reals are embedded in the natural numbers. The topos is based on infinite-time Turing machines of Joel Hamkins.",
  authors := ["Andrej Bauer"],
  doi := ["https://doi.org/10.1017/S0960129513000406"],

  results := [Construction IITM,
              Construction R_to_N,
              Proof R_to_N_is_mono],
}

#print axioms fabstract

end Bauer_A_InjBaireNat
