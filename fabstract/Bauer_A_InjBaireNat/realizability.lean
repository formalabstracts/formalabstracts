-- the folklore does not yet contain anything about realizability toposes,
-- so we include partial formalization here. Eventually this should be
-- moved to folklore.

import meta_data
       .toposes

run_cmd tactic.skip -- temporary fix

-- TODO (@andrejbauer): give real descriptions and dois
-- missing definition of what a PCA is
unfinished PCA : Type :=
  {
    description := "partial combinatory algebra",
    sources     := [cite.Website "https://ncatlab.org/nlab/show/partial+combinatory+algebra"]
  }


unfinished RT : (PCA → topos) :=
  {
    description := "realizability topos",
    sources     := [cite.Website "https://ncatlab.org/nlab/show/realizability+topos"]
  }
