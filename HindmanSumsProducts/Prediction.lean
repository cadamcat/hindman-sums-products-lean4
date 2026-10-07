import HindmanSumsProducts.Prediction.Completion

/-!
# Dense models and prediction

Formal skeleton for §5 of the paper. The principal statements are available as
`HindmanSumsProducts.Prediction.dual_pseudorandomness`,
`bounded_dense_models`, `nilsequence_testing`, `energy_selection`,
`subgroup_cube_to_fine_projection`, and the separate calibration/counting completion lemmas.

The Framework lane owns `PredictionPrinciple`; this module does not define it. All terminal
parameter and model witnesses are OpenAI's `Parameters`, `Menu`, and `ModelsSystem`.
-/
