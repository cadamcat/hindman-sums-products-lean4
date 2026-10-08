[English](README.md) | [简体中文](README_zh.md)

# Lean 4 中的 Hindman 有限和与有限积定理

对正整数作任意有限着色，都存在一个恰有 `m` 个元素的集合，使其每个非空子集的和与积都具有同一种颜色。这是 Justin Sun Prize 目录中的 JSP-000168，也是 [Erdős 第 172 号问题](https://www.erdosproblems.com/172)的有限情形。形式化陈述即此猜想；OpenAI 论文的主定理另含一个间隔条件和一个推论，这两部分未作形式化（[详见](docs/mathematics.md)）。

- **作者：** Yao Xu ([@cadamcat](https://github.com/cadamcat))；见[作者与署名说明](AUTHORS.md)。
- **数学结果：** OpenAI，[*Monochromatic finite sums and products in the positive integers*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026/paper.pdf)。
- 本项目在 AI 协助下开发（Claude Code 和 Codex）；所有证明均由 Lean 4 内核验证。

## 主要结果

| 定理 | 陈述 |
| --- | --- |
| `HindmanSumsProducts.hindman_finite_sums_products` | 对任意 `r`、着色 `χ : ℕ → Fin r` 和 `m`，存在 `A : Finset ℕ` 与 `c : Fin r`，使得 `A.card = m`、`A` 的每个元素都为正数，并且 `A` 的每个非空子集的和与积都被着成 `c`。 |

证明见 [HindmanSumsProducts/Main.lean](HindmanSumsProducts/Main.lean)。对应的挑战陈述见 [Challenge.lean](Challenge.lean)；[Challenge.json](Challenge.json) 配置 Comparator 对这两个陈述进行比较。陈述细节及证明与论文的关系见[数学指南](docs/mathematics.md)。

## 构建与验证

环境要求：Git、Python 3 和 [elan](https://github.com/leanprover/elan)，并确保 `lake` 已加入 `PATH`。在全新检出版本的仓库根目录运行：

```sh
lake update
scripts/apply-oai-patches.sh
lake exe cache get
lake build
```

OpenAI 的 `lake update` hook 会在解析依赖并写入 `lake-manifest.json` 后报错，错误以 `iut: Lake resolved an unexpected checkout at …` 开头。随后运行补丁脚本；它会应用 OpenAI 的 Lean 4.34.1 兼容补丁，也可在再次运行 `lake update` 后重新运行。补丁会修改随后编译的依赖源码（其中 PrimeNumberTheoremAnd 的补丁最大），因此构建检查的是打过补丁的源码，而不只是 `lake-manifest.json` 中记录的版本。

若要构建定理、核对两处陈述并检查最终定理的公理，请运行 `LEAN_NUM_THREADS=4 ./scripts/verify.sh`。证明尚未完成时，脚本会报告 `sorryAx` 并以状态码 2 退出。详见[验证说明](docs/verification.md)。在一台新的 Linux 机器上，`v1.0.0` 的全新克隆按上述步骤构建成功，通过了 `leanchecker --fresh` 内核重放和 Comparator 检查，结果见[独立检查](docs/verification.md#independent-check-of-v100)。

## 固定依赖

- Lean `v4.34.1`，由 [lean-toolchain](lean-toolchain) 选定。
- [Mathlib](https://github.com/leanprover-community/mathlib4)，提交 `d13f23b723b8a846827a245b89c10fc7d3f11612`。
- OpenAI 的 [`openai/math`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean)，固定在提交 `adc7f1241b42e322a6451854ab7e4b4c146bf78a`。
- OpenAI 库固定了 [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)（提交 `c39a751132c88b6e8080b74c74023fd95b3d8be0`）和 [StrongPNT](https://github.com/math-inc/strongpnt)（提交 `2f5835c322314f55f1026ec2f139d704b7c45c69`）。
- 其余依赖版本见 [lake-manifest.json](lake-manifest.json)。

## 数学参考文献

- OpenAI，[*Monochromatic finite sums and products in the positive integers*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026/paper.pdf)，2026 年 9 月 23 日。
- N. Kravitz、B. Kuca 和 J. Leng，[*Quantitative concatenation for polynomial box norms*](https://arxiv.org/abs/2407.08636)，第 6 节。

代码署名见 [THIRD_PARTY.md](THIRD_PARTY.md)，项目许可证见 [LICENSE](LICENSE)。
