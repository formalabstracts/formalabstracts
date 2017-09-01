import meta_data

namespace Wiles_A_and_Taylor_R_FermatLast

-- the statement of Fermat's Last Theorem
axiom fermat_last_theorem :
∀ (x y z n : nat), x > 0 → y > 0 → n > 2 → x ^ n + y ^ n ≠ z ^ n

def paper : document :=
{   authors := [
    {name := "Andrew Wiles"},
    {name := "Richard Tylor"}
  ],
  title := "Modular elliptic curves and Fermat's last theorem",
  doi := "10.2307/2118559"}

definition fabstract : fabstract :=
{ description := "A result in number theory conjectured by Pierre de Fermat and proved by Andrew Wiles and Richard Taylor. Colloquially referred to as Fermat's Last Theorem.",
  contributors := [{name := "Adam Kurkiewicz"}],
  sources := [cite.Document paper],
  results := [result.Proof fermat_last_theorem] }

end Wiles_A_and_Taylor_R_FermatLast
