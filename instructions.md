# Instructions

Here are some guidelines for contributing to the Formal abstracts project.

## Prerequisites

* basic knowledge of and an installation of the [Lean prover](http://leanprover.github.io)
* basic knowledge of and an installation of [git](https://git-scm.com)
* a [GitHub](https://github.com) account

## Getting started

We recommend that you browse through the [`fabstracts`](./fabstracts) folder and get a
feel for what a typical fabstract looks like. The [`folklore`](./folklore) folder contains
common definitions, have a look at it as well.

Once you are ready to contribute, assuming you took care of the prerequisites (see above):

1. fork the [`formalabstracts` repository](https://github.com/formalabstracts/formalabstracts)
2. clone it to your local computer
3. run `leanpkg configure` inside the `formalabstracts` folder

## Contributing

The project has only just gotten off the ground, so there is plenty to do. We are still in
a highly experimental phase and we welcome ideas on how to get organized. Above all, we
need examples of fabstracts.

Let us run through a typical procedure, adding a fabstract:

1. Start a new branch devoted to adding the fabstract:

        git checkout -b my-best-paper

2. Add a new fabstract (see [fabstract/README.md](./fabstract/README.md)
   for instructions).

3. Run `lean --make` inside the `formalabstracts` folder to make sure everything compiles

4. Commit your changes.

5. Push the branch to your GitHub repository:

        git push origin my-best-paper

6. Issue a [pull request](https://github.com/formalabstracts/formalabstracts/pulls) in GitHub.

The maintainers may ask you to update your pull request with improvements or changes. This
is done by simply committing and pushing some more. Your pull request will always contain
the current state of the `my-best-paper` branch on GitHub.

## The review process

Once you make a pull request the project maintainers will have a look at it. They may ask
you to make questions or clarifications, so please participate in the discussion. The
maintainers follow the **`n` pairs of eyes policy** which states that every pull request
must be approved by at least `n` people, apart from the author.

* When `n = 0` anyone can push anything they want.
* When `n = 1` one other person much agree.
* When `n = 2`, well you get the point.

**Currently we are at `n = 1`.** This means, in particular, that the maintainers
themselves **do not push directly**. They too issue pull requests and wait for someone
else to accept them.
