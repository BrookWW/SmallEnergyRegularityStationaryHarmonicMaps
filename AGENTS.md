# Stationary harmonic map small-energy regularity

This repository contains the closed Lean dependency tree of the small-energy
regularity theorem for stationary harmonic maps into compact embedded C²
targets and its smooth-target corollary. Preserve their arbitrary domain
dimension, explicit original weak gradient, uniform constants and full
conclusions. The TeX proof and README must agree with the actual declarations.

- Use Lean and Mathlib at the exact revisions in `lean-toolchain` and
  `lake-manifest.json`. The only direct external Lean dependency is Mathlib.
- Every mathematical `.lean` file is a module and a regular source file.
  Retain the public interfaces and exposed meaning-carrying definitions.
- Do not introduce proof holes, custom axioms, native trust bypasses, hidden
  source paths, mathematical assumption packages or resource-limit overrides.
- Build with `lake build`. Inspect existing artifacts with the documented
  scripts; those scripts do not build dependencies or update pins.
- A fresh checkout may create its own dependency artifacts with
  `lake exe cache get`. Do not modify another checkout's dependencies or caches.
- Run source, statement, axiom and public-consumer checks before publishing
  changes. A successful build alone does not establish source fidelity.
- The source inventory and compiled statement fingerprints describe the
  approved mathematical tree. Changing them requires reviewing the actual
  mathematical change, not merely regenerating fingerprints to pass a check.
- Documentation and comments describe current mathematics and public usage.
  Preserve the attribution and license of included source code.
