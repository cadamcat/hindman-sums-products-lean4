# Authors and attribution

Yao Xu ([@cadamcat](https://github.com/cadamcat)) is the author and maintainer of this formalization project.

The mathematical theorem was proved by OpenAI, in the paper [*Monochromatic finite sums and products in the positive integers*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026/paper.pdf). This repository formalizes the theorem; it does not claim a new mathematical solution. The formal proof follows the paper, takes the Alignment Principle and a cyclic inverse theorem from OpenAI's Lean library, and replaces the Tao–Ziegler concatenation theorem by the subgroup box-norm concatenation of Kravitz, Kuca and Leng.

The author planned, dispatched and reviewed the work. Formalization and review used Claude Opus 5.5 in Claude Code, and GPT-6 Luna and GPT-6.1 Sol in Codex. The resulting proofs and their dependencies were checked by the Lean kernel.

The project uses Mathlib, OpenAI's `openai/math` library and the packages it pins. Their authors and licenses are credited in [THIRD_PARTY.md](THIRD_PARTY.md) and [NOTICE](NOTICE).
