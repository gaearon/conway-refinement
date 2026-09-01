## Blueprint review

- [ ] Every mathematically affected blueprint node and the smallest complete reopened inference
      chain were checked against Lean using `review-blueprint`; trivial nonfactoring edits were
      excluded.
- [ ] Every newly qualifying declaration was selected, and every removed node has a mathematical
      reason; the complete proof spine remains reconstructible.
- [ ] Final mathematical review checked every selected blueprint node without sampling.
- [ ] `scripts/blueprint.sh build` passes and leaves the generated README map and PDF unchanged.
