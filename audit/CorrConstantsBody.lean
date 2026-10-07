import HindmanSumsProducts.Prediction.Imported
-- Audit (2026-10-07): the frozen value hashes of `corrTemplate` and `corrConst` changed when
-- `uniform_correlation_test` was proved (f54c9eb), with `Imported.lean` unchanged since a9d9224.
-- These kernel checks show both definitions are still the `choose` terms of that theorem; their
-- record entries were refreshed.
open HindmanSumsProducts HindmanSumsProducts.Prediction in
example (m : ℕ) (J : Finset (Fin m)) (hJ : 2 ≤ J.card) :
    corrTemplate m J hJ = (uniform_correlation_test m J (nonempty_of_two_le_card hJ) hJ).choose := rfl
open HindmanSumsProducts HindmanSumsProducts.Prediction in
example (m : ℕ) (J : Finset (Fin m)) (hJ : 2 ≤ J.card) :
    corrConst m J hJ =
      (uniform_correlation_test m J (nonempty_of_two_le_card hJ) hJ).choose_spec.2.2.choose := rfl
