# Release Checklist

For the initial public commit that the manuscript will link to:

1. Review `formalization.yaml`, especially authorship, the Apache-2.0 licence,
   source provenance, automation disclosure, and scope limitation. Run
   `./scripts/verify-vendored-sources.sh` to confirm that the five
   `ErgodicTheory/MeasureTheory` modules still match the immutable revision
   recorded in `NOTICE`.
2. Run `lake build`.
3. On Linux, run `./scripts/verify-comparator.sh`.
4. Commit every source, manifest, metadata, and configuration file.
5. Push the commit to a public GitHub repository and confirm that Lean CI
   passes.
6. Once the commit lands, tag and push the arXiv-facing revision:

   ```sh
   git tag arxiv-v1 && git push origin arxiv-v1
   ```

After the arXiv identifier is assigned and before Palomar submission:

7. Add the arXiv identifier to the manuscript entry in `formalization.yaml`
   and rerun its local and pinned-schema validation.
8. Commit and push that metadata update, then confirm that CI passes.
9. Record the full Palomar candidate commit with `git rev-parse HEAD`.
10. Submit that immutable 40-character SHA at
   <https://submit.palomar-registry.org/>.

Palomar ignores uncommitted changes and verifies the exact submitted commit,
not a branch or tag.
