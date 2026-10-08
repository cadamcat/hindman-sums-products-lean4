import Lake
open Lake DSL

package HindmanSumsProducts where
  leanOptions := #[⟨`autoImplicit, false⟩]

-- OpenAI's library (Apache-2.0), openai/math at commit adc7f124, fetched from GitHub.
require OAI from git "https://github.com/openai/math" @ "adc7f1241b42e322a6451854ab7e4b4c146bf78a" / "lean"

@[default_target]
lean_lib HindmanSumsProducts

-- The target statement (Comparator challenge module).
lean_lib Challenge
