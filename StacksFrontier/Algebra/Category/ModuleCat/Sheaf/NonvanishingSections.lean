module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NonvanishingSections.DegreeZeroLocalizationLift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NonvanishingSections.TensorRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NonvanishingSections.LocalizationMap

/-!
# Sections on the nonvanishing open of a section of an invertible sheaf

This module re-exports its three parts: `DegreeZeroLocalizationLift` evaluates degree-zero
homogeneous fractions of graded modules, `TensorRestriction` collects the calculations with
sections of tensor products and compares tensor products with restriction to an open, and
`LocalizationMap` constructs the map from degree-zero localized twisted sections to sections
over the nonvanishing open of a global section `s` of an invertible sheaf and identifies it by
the fraction formula.
-/
