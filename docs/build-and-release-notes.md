# Build and release: two traps worth knowing

Short operational notes. Both of these cost real time in the v1.8.0 cycle.

## `lake env lean` does not rebuild the `.olean` that dependents consume

`lake env lean Foo.lean` type-checks a source file. It does **not** necessarily rebuild
`Foo.olean`, which is what *importing* modules read.

The consequence is worse than a stale error message. A probe file that imports a module you just
edited may silently elaborate against the **pre-edit** version and report a result that looks live.
In the v1.8.0 cycle this misfired three times: universe-generalization probes reported pre-edit
behaviour and were nearly recorded as a genuine finding; and two new modules failed with
`unknown identifier` for declarations that had in fact been added.

**Rule.** After changing a module, run

```
lake build <Module>
```

explicitly before compiling or probing anything that imports it. Note that having run a *full*
`lake build` earlier is not sufficient evidence — check the specific module.

## Pages docs must be dispatched from `master`, not from a tag ref

```
gh workflow run docs.yml --ref master     # correct
gh workflow run docs.yml --ref v1.8.0     # build succeeds, DEPLOY FAILS
```

GitHub Pages deployment is restricted to the configured branch. Dispatching from a tag ref produces
a run whose *build* job succeeds and whose *deploy* job fails, which reads like a content problem
and is not.

**Rule.** Dispatch from `master`, and first verify that `master` points at the intended release SHA:

```
git rev-parse master v1.8.0    # should agree
```

A docs-only redeploy cannot disturb a release: the tag is immutable, and the deployment publishes
whatever commit the branch names.
