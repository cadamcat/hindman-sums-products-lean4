# Authors and attribution

Yao Xu ([@cadamcat](https://github.com/cadamcat)) is the author and maintainer of this formalization project.

The mathematical theorem was proved by OpenAI, in the paper [*Monochromatic finite sums and products in the positive integers*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026/paper.pdf). This repository formalizes the theorem; it does not claim a new mathematical solution. The formal proof follows the paper, takes the Alignment Principle and a cyclic inverse theorem from OpenAI's Lean library, and replaces the Tao–Ziegler concatenation theorem by the subgroup box-norm concatenation of Kravitz, Kuca and Leng.

The author planned, dispatched and reviewed the work, set its acceptance criteria (only the standard axioms, fidelity of every frozen statement, replay by the Lean kernel) and decided on its publication. Claude Opus 5.5 in Claude Code coordinated the work and reviewed statements, GPT-6 Luna in Codex wrote most of the Lean proofs, and GPT-6.1 Sol in Codex checked statements for counterexamples and designed proofs of the hardest steps. The resulting proofs and their dependencies were checked by the Lean kernel.

The project uses Mathlib, OpenAI's `openai/math` library and the packages it pins. Their authors and licenses are credited in [THIRD_PARTY.md](THIRD_PARTY.md) and [NOTICE](NOTICE).
