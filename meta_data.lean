-- Each formal abstract contains an instance of the meta_data structure,
-- describing the contents.
meta structure meta_data : Type :=
  mk_meta_data ::
    (description : string) -- short description of the contents
    (authors : list string) -- list of authors
    (doi : list string) -- references to the original article
    (results : list name) -- the list of main results
