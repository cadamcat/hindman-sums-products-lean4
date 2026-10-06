import OAI.Combinatorics.SumProduct.Alignment.RawMenu

/-!
# The Alignment Principle, from OpenAI's library

OpenAI's `openai/math` library (Apache-2.0, commit `adc7f124`) formalizes the paper's Alignment
section in `OAI/Combinatorics/SumProduct/Alignment` (259 files) and `OAI/Geometry/NilpotentCharts`.
This module reuses its final theorem unchanged.
-/

namespace HindmanSumsProducts

/-- OpenAI's formal Alignment statement (`OAI.SourceRawMenu.Alignment`), proved in its library. -/
theorem oai_alignment : OAI.SourceRawMenu.Alignment := OAI.raw_alignment_reference

end HindmanSumsProducts
