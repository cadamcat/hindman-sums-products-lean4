import HindmanSumsProducts.InverseBridge.Linear
-- Audit (2026-10-07): the frozen value hash of `weightFiltration` changed when
-- `exists_weightFiltration` was proved, with identical source text. These kernel checks show the
-- definition is still `Classical.choose (exists_weightFiltration F hs)`; its record entry was
-- refreshed.
open HindmanSumsProducts.InverseBridge in
example {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ} (F : OAI.Erdos3.NilpotentLieFiltration L s)
    (hs : 0 < s) : weightFiltration F hs = Classical.choose (exists_weightFiltration F hs) := rfl
open HindmanSumsProducts.InverseBridge in
example {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ} (F : OAI.Erdos3.NilpotentLieFiltration L s)
    (hs : 0 < s) : weightFiltration F hs = Classical.choose (exists_weightFiltration F hs) := by
  unfold weightFiltration; rfl
