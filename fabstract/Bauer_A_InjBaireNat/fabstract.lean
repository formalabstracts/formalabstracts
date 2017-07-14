import meta_data
import folklore.categories
import folklore.toposes
import .realizability

namespace Bauer_A_InjBaireNat
noncomputable theory

-- we construct a partial combinatory algebra based on
-- infinite-time Turing machines
axiom IITM : PCA

noncomputable def T := RT IITM

definition N := T.nno
definition R := dedekind_reals T

axiom R_to_N : T.underlying_category.hom N.nno_object R.reals_object

axiom R_to_N_is_mono : monomorphism R_to_N

meta def fabstract : meta_data := {
  authors := ["Andrej Bauer"],
  doi := ["https://doi.org/10.1017/S0960129513000406"],
  results := [`IITM, `R_to_N, `R_to_N_is_mono],
  description := "We construct a realizability topos in which the reals are embedded in the natural numbers. The topos is based on infinite-time Turing machines of Joel Hamkins."
}

end Bauer_A_InjBaireNat
