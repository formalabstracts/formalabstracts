# The fabstracts repository

The repository is organized into folders, one per fabstract, which allows a complicated
fabstract to be split into several files. The main file in the folder is called
`fabstract.lean`, and the folder itself has the format `Surname_X_Y_Title` where
`Surname_X_Y` is the author name, with initials for the names, and `Title` is an
approximate representation of the title. Of course, these policies would have to be
retaught once we gain more experience. For example, what should we do about papers with
multiple authors, and precisely do we write `Title`? Should we use a completely different
schema?

Each `fabstract.lean` must contain a `toc` (table of contents) of type `Metadata`.
