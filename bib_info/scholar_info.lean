import system.io data.buffer.parser meta_data

open io io.proc tactic

meta def get_bib_string [io.interface] (s : string) (n : ℕ) : io string :=
io.cmd {cmd := "python2", args := ["bib_info/scholar.py", "-c", to_string n, "-A", s, "--citation=bt"] }
   
meta def get_bib_string_tac (st : string) (n : ℕ) : tactic string :=
do s ← tactic.run_io (λ i, @get_bib_string i st n),
   trace s,
   return s

section parser
meta def parse_bracket_block : parser string :=
do parser.ch '{',
   cs ← parser.many (parser.sat (λ c, ¬ c = '}')),
   parser.ch '}',
   return cs.as_string

meta def parse_comma_block : parser string :=
do cs ← parser.many (parser.sat (λ c, ¬ c = ',')),
   parser.ch ',',
   return cs.as_string

meta def parse_until_char (c : char) : parser string :=
do cs ← parser.many (parser.sat (λ c', ¬ c' = c)),
   return cs.as_string

meta def parse_eq_line : parser (string × string) :=
do parser.many (parser.ch ' '),
   lhs ← parse_until_char '=',
   parser.ch '=',
   rhs ← parse_bracket_block,
   return (lhs, rhs)

meta def parse_eq_line' (s : string) : option (string × string) :=
match parser.run_string parse_eq_line s with
| sum.inl a := none
| sum.inr a := some a
end

meta def parse_rest : parser string :=
do cs ← parser.many (parser.sat (λ t, true)),
   return cs.as_string

meta def parse_bib_int' : parser (list string) :=
do id ← parse_comma_block,
   lns ← parser.many parse_comma_block,
   lst ← parse_rest,
   let lns := lns.append [lst],
   return lns

def {u} list.filter_option {α : Type u} : list (option α) → list α
| [] := []
| (some h::t) := h::list.filter_option t
| (none::t) := list.filter_option t

meta def parse_until_comma_or_close : parser string :=
(do s ← parse_until_char ',',
   parser.ch ',',
   return s) <|>
(do s ← parse_until_char '}',
   parser.ch ',',
   return s)

def strip_trailing_comma (s : string) : string :=
if s.back = ',' then s.pop_back else s

meta def parse_bib : parser (string × rb_map string string) :=
do parser.ch '\n' >> parser.ch '@' <|> parser.ch '@',
   tp ← parse_until_char '{',
   parser.ch '{',
   id ← parse_comma_block,
   eqs ← parser.sep_by (parser.ch '\n') (parse_until_char '\n'),
   let lns' := eqs.tail.map (parse_eq_line' ∘ strip_trailing_comma),
   return (tp, rb_map.of_list lns'.filter_option)


meta def split_char_list_single (delim : list char) : list char → list char → (list char × list char)
| acc []      := (acc, [])
| acc (h::t)  := 
let n  := delim.length,
    hd := (h::t).take n in
if hd = delim then (acc, (h::t).drop n) else split_char_list_single (acc++[h]) t

meta def split_char_list_aux (delim : list char) : list char → list (list char)
| [] := [[]]
| l  := 
let (nw, rm) := split_char_list_single delim [] l in
nw::split_char_list_aux rm

meta def split_char_list (delim inp : list char) : list (list char) :=
(split_char_list_aux delim inp).erase []

meta def split_string (delim inp : string) : list string :=
(split_char_list delim.to_list inp.to_list).map (list.as_string)

end parser

meta def rb_map.find' {α β : Type} (m : rb_map α β) [inhabited β] (a : α) : β :=
match m.find a with
| some b := b
| none := default β
end

meta def format_author_string (inp : string) : string :=
let athrs  := split_string " and " inp,
    athrs' := athrs.map (λ s, "{name := \"" ++ s ++ "\"}, ") in
(string.join athrs').popn_back 2

meta def format_citation_journal (dict : rb_map string string) : string × string :=
let jn := dict.find' "journal",
    vl := dict.find' "volume",
    nm := dict.find' "number",
    pg := dict.find' "pages",
    yr := dict.find' "year" in
(jn, jn ++ (if vl ≠ "" then " " ++ vl ++ (if nm ≠ "" then ":" ++ nm else "") else "") ++ (if pg ≠ "" then ", " ++ pg else "") ++ (if yr ≠ "" then " (" ++ yr ++ ")" else ""))

meta def format_citation_proceedings (dict : rb_map string string) : string × string :=
let jn := dict.find' "booktitle",
    vl := dict.find' "volume",
    pg := dict.find' "pages",
    yr := dict.find' "year" in
(jn, jn ++ (if vl ≠ "" then " " ++ vl else "") ++ (if pg ≠ "" then ", " ++ pg else "") ++ (if yr ≠ "" then " (" ++ yr ++ ")" else ""))

meta def format_citation_book (dict : rb_map string string) : string × string :=
let jn := dict.find' "title",
    yr := dict.find' "year",
    pb := dict.find' "publisher" in
(jn, jn ++ ". " ++ pb ++ (if yr ≠ "" then " (" ++ yr ++ ")" else ""))

-- returns (source, reference)
meta def format_citation (bibtype : string) (dict : rb_map string string) : string × string :=
if (bibtype = "article") && (dict.contains "journal") then format_citation_journal dict
else if (bibtype = "inproceedings") && (dict.contains "booktitle") then format_citation_proceedings dict
else if (bibtype = "book") && (dict.contains "title") then format_citation_book dict
else ("", "")

meta def format_document (bibtype : string) (dict : rb_map string string) : string :=
let ((src, ref), yr) := (format_citation bibtype dict, dict.find' "year") in
"             { title     := \"" ++ dict.find' "title" ++ "\",
               authors   := [" ++ format_author_string (dict.find' "author") ++ "],
               doi       := \"" ++ dict.find' "doi" ++ "\",
               source    := \"" ++ src ++ "\",
               year      := " ++ (if yr ≠ "" then "↑"++yr else "none") ++ ",
               arxiv     := \"\",
               url       := \"" ++ dict.find' "url" ++ "\", 
               reference := \"" ++ ref ++ "\" }" 


meta def format_meta_data (bibtype : string) (dict : rb_map string string) : string :=
"{ description := \"\",
  contributors := [" ++ format_author_string (dict.find' "author") ++ "],
  sources      := [cite.Document\n" ++ format_document bibtype dict ++ "] }"

meta def parse_bib_tac (search : string) (n : ℕ) : tactic (list (string × rb_map string string)) :=
do s ← get_bib_string_tac search n,
   let ls := (split_string "\n\n" s).erase "\n",
   ls ← ls.mmap (λ s, do sum.inr (t, map) ← return $ parser.run_string parse_bib s, return (t, map)), 
   return ls


meta def fill_bib_data_aux (formatter : string → rb_map string string → string) (s : pexpr) (n : ℕ) : tactic (list (string × string)) :=
 do s' ← to_expr ``(%%s : string) >>= eval_expr string,
    ls ← parse_bib_tac s' n,
    return $ ls.map (λ p, (formatter p.1 p.2, p.2.find' "title"))

@[hole_command]
meta def fill_meta_data : hole_command := 
{ name   := "Fill meta data",
  descr  := "Try to find citation data from Google Scholar, and populate a meta_data object",
  action := λ ps, match ps with
  | [s] := fill_bib_data_aux format_meta_data s 3
  | [s, n] := do n ← to_expr ``(%%n : ℕ) >>= eval_expr nat, fill_bib_data_aux format_meta_data s n
  | _ := failed
  end }

@[hole_command]
meta def fill_document : hole_command := 
{ name   := "Fill document",
  descr  := "Try to find citation data from Google Scholar, and populate a document object",
  action := λ ps, match ps with
  | [s] := fill_bib_data_aux format_document s 3
  | [s, n] := do n ← to_expr ``(%%n : ℕ) >>= eval_expr nat, fill_bib_data_aux format_document s n
  | _ := failed
  end }
