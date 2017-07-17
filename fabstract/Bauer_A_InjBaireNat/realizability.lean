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
    references := [cite.URL "https://ncatlab.org/nlab/show/partial+combinatory+algebra"]
  }

-- TODO (@rlewis1988): fix binding power so that parens around the type aren't needed
-- missing construction of realizability topos
unfinished RT : (PCA → topos) :=
  {
    description := "realizability topos",
    references := [cite.URL "https://ncatlab.org/nlab/show/realizability+topos"]
  }
