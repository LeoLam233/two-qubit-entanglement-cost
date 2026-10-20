import EC2.EntropyBlocks

/-! Executable statement and axiom audit for the entropy branch. -/

#check EC2.Entropy.hasDerivAt_logSpectralNorm_two
#check EC2.Entropy.hasDerivAt_spectralNorm_two
#check EC2.Entropy.hasDerivWithinAt_abs_rpow_self_zero
#check EC2.Entropy.hasDerivWithinAt_hanner_entropy_rhs
#check EC2.Entropy.balanced_rectangular_entropy_nats
#check EC2.Entropy.balanced_qubit_rectangular_entropy_nats
#check EC2.Entropy.wBits_zero
#check EC2.Entropy.wBits_one
#check EC2.Entropy.wBits_monotoneOn
#print EC2.Entropy.RectangularHanner
#print axioms EC2.Entropy.hasDerivAt_logSpectralNorm_two
#print axioms EC2.Entropy.hasDerivAt_spectralNorm_two
#print axioms EC2.Entropy.hasDerivWithinAt_abs_rpow_self_zero
#print axioms EC2.Entropy.balanced_rectangular_entropy_nats
#print axioms EC2.Entropy.balanced_qubit_rectangular_entropy_nats
#print axioms EC2.Entropy.wBits_monotoneOn
