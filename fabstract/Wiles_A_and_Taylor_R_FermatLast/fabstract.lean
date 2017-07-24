import ...meta_data

namespace Wiles_A_and_Taylor_R_FermatLast

-- the statement of Fermat's Last Theorem
axiom fermat_last_theorem :
∀ (x y z n : nat), x > 0 → y > 0 → n > 2 → x ^ n + y ^ n ≠ z ^ n

definition fabstract : meta_data :=
{ description := "A result in number theory conjectured by Pierre de Fermat and proved by Andrew Wiles and Richard Taylor. Colloquially referred to as Fermat's Last Theorem.",
  authors := [
    {name := "Andrew Wiles"},
    {name := "Richard Tylor"}
  ],
  primary := cite.DOI "10.2307/2118559",
  secondary := [cite.DOI "10.2307/2118560"],
  results := [result.Proof fermat_last_theorem] }

end Wiles_A_and_Taylor_R_FermatLast
