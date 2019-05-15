import category_theory.category ..basic

namespace tactic
@[obviously] meta def obviously₂ :=
do t ← target,
   mk_mapp `omitted [some t] >>= exact >> skip
end tactic