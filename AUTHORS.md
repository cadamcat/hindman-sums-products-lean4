# Authors and attribution

Yao Xu ([@cadamcat](https://github.com/cadamcat)) directed this formalization: he chose the target, set the acceptance criteria, and is responsible for its content.

The mathematical result is OpenAI's. This repository formalizes the theorem in [OpenAI's paper](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026/paper.pdf).

## AI-assisted development

Claude Code (Claude Opus 5.5) planned and coordinated the work, reviewed the target statement against the conjecture and the paper, and repaired defective intermediate statements. Codex CLI with GPT-6 Luna wrote most of the Lean proofs. GPT-6.1 Sol checked intermediate statements for counterexamples and wrote detailed proof designs for the hardest steps.

Before proofs were attempted, each intermediate statement was frozen with a hash of its elaborated type. A proof was accepted only with that frozen type and axioms within `propext`, `Classical.choice`, and `Quot.sound`, allowing other frozen statements that were still open. Statements were also checked for counterexamples; the few found false were repaired and frozen again. Agreement between models was not treated as verification. The Lean kernel and axiom checks provide the verification evidence.

Code adapted from OpenAI's Lean library is identified in [THIRD_PARTY.md](THIRD_PARTY.md), which also lists the imported modules and package dependencies.
