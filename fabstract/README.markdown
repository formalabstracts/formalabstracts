# The fabstracts repository

The repository is organized into folders, one per fabstract, which allows a complicated
fabstract to be split into several files. The following conventions are enforced by the
curators.

### The name of the fabstract folder

The name of the folder has the form

    Author1_and_Author2_and_…_TitleAcronym

where each `AuthorN` has the form `Lastname_Initials`, and `Initials` are the initials
separated by undercores. There is currently no good convention on how to create
`TitleAcronym`. Look at the existing abstracts for conventions.

### The contents of the fabstract folder

You may put arbitrary auxiliary Lean files in the folder. You *must* include a file called
`fabstract.lean` which must have the following form:

    ⟨other imports⟩
    import meta_data
    namespace Author1_and_Author2_and_…_TitleAcronym
    
    ⟨auxiliary development⟩
    
    def fabstracts : meta_data = {
      authors := …,
      doi := …,
      description := …,
      results := …
    }
    end Author1_and_Author2_and_…_TitleAcronym

The `results` field should list the main results of the paper. Consult the `result` type
in `meta_data` to see what these may be.
