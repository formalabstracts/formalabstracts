-- the folklore does not yet contain anything about realizability toposes,
-- so we include partial formalization here. Eventually this should be
-- moved to folklore.

import ...meta_data folklore.toposes

-- there are some issues with parsing user-defined commands right now that make this line necessary
run_cmd tactic.skip

-- TODO (@andrejbauer): give real descriptions and dois
-- missing definition of what a PCA is
undefined_const PCA : Type :=
{description := "partial combinatory algebra",
 doi := ["https://ncatlab.org/nlab/show/partial+combinatory+algebra"]}

-- missing construction of realizability topos
undefined_const RT : PCA → topos :=
{description := "realizability topos",
 doi := ["https://ncatlab.org/nlab/show/realizability+topos"]}
