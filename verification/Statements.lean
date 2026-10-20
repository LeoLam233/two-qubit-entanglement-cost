import EC2

/-! Executable exact-statement and axiom audit for the manuscript targets. -/
set_option pp.universes true
set_option pp.fullNames true

#check @EC2.balanced_complex_rectangular_block_entropy
#check @EC2.fixed_axis_concurrence
#check @EC2.strong_superadditivity
#check @EC2.arbitrary_partner_additivity
#check @EC2.formation_tensor_power
#check @EC2.entanglement_cost_formula
#check @EC2.entanglement_cost_real_formula
#check @EC2.entanglement_cost_finite

#print axioms EC2.balanced_complex_rectangular_block_entropy
#print axioms EC2.fixed_axis_concurrence
#print axioms EC2.strong_superadditivity
#print axioms EC2.arbitrary_partner_additivity
#print axioms EC2.formation_tensor_power
#print axioms EC2.entanglement_cost_formula
#print axioms EC2.entanglement_cost_real_formula
#print axioms EC2.entanglement_cost_finite

-- Load-bearing bridges and all-rank/zero cases.
#print axioms EC2.pure_entropy_from_fixed_axis
#print axioms EC2.ConcurrenceReduction.extreme_fixedSlice_rank_or_zero
#print axioms EC2.rank_two_fixed_axis_concurrence
#print axioms EC2.ConcurrenceZeroFace.concurrence_zero_of_diagonal_marginals_antidiagonal
#print axioms EC2.Operational.FiniteLOCC.preserves_posSemidef
#print axioms EC2.Operational.FiniteLOCC.preserves_trace

-- Visible literature assumptions, not installed as axioms.
#print EC2.Entropy.RectangularHanner
#print EC2.Literature.ComplexRectangularHanner
#print EC2.Literature.WoottersFormation
#print EC2.ConcurrenceReduction.WoottersSpectralFormula
#print EC2.Operational.HHTRegularization

-- Definitions needed to compare scope, units and operational meaning.
#print EC2.Q
#print EC2.entropyBits
#print EC2.formationBits
#print EC2.concurrence
#print EC2.IsMarginalAxis
#print EC2.transverseValues
#print EC2.transverseBound
#print EC2.partnerProduct
#print EC2.marginalAB
#print EC2.marginalAux
#print EC2.qubitTensorPower
#print EC2.Operational.FiniteLOCC
#print EC2.Operational.AchievableDilutionRate
#print EC2.Operational.entanglementCost
