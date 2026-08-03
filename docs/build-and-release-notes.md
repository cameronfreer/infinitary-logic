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

## Verifying a docs deployment

The homepage stamps the commit it was built from. `docs.yml` appends `deployed_sha` to the Jekyll
config at build time, and the page renders it twice:

```html
<!-- deployed-source-sha: <sha> -->
<p><sub>Built from commit <a href=".../commit/<sha>"><code>1c35d3d</code></a>.</sub></p>
```

(The Jekyll stylesheet cache key, `assets/css/style.css?v=<sha>`, carries the same information and
remains a fallback.)

**Publication is successful when all three hold:**

1. **The workflow run succeeded** — both jobs. The run-level status flickers back to `queued` between
   the build job and the Pages deploy job, so a single mid-run poll can be misleading; check the jobs,
   or wait for the run to reach `completed`.
2. **The live `deployed-source-sha` equals the run's captured `headSha`.** A run captures `master`
   when it *starts*, and `master` may advance during the ~30-minute build — so compare against the
   run's `headSha`, not against current `master`.
3. **That commit contains the intended public changes.** A correct deployment of the wrong commit is
   still a failed publication.

One command for (1) and (2):

```bash
RUN=<run-id>
gh run view "$RUN" --json status,conclusion,headSha \
  --jq '"status=\(.status) conclusion=\(.conclusion) headSha=\(.headSha)"'
curl -s https://cameronfreer.github.io/infinitary-logic/ | grep -o "deployed-source-sha: [0-9a-f]*"
```

**The live fetch is deliberately not in CI.** Pages and CDN propagation are not synchronous with
deployment success, so a post-deploy assertion would be flaky for reasons unrelated to the release.
The marker plus this manual check is robust; an intermittently red pipeline would not be.

This catches the three real failure modes — a tag-ref dispatch whose deploy step is rejected, a
scheduled deployment that has since fallen behind, and a redispatch that was never made — without
inferring a deployment bug from a SHA mismatch that has an ordinary explanation. A live page older
than `master` is normally just a page built before the newer commits landed.
