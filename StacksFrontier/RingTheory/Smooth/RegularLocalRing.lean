module

public import StacksFrontier.RingTheory.Smooth.RegularLocalRing.ClosedPointRegularity
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing.LocalDimensionCriterion
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing.SeparableResidueRegular
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing.CharZeroRegularity

/-!
# Smoothness and regularity of finite type algebras over a field

This file only re-exports its four parts, one for each of Stacks 00TS, 00TT, 00TV and 00TX:

* `RegularLocalRing.ClosedPointRegularity`: over an algebraically closed field, regularity at a
  closed point equals smoothness there (Stacks 00TS, `Algebra.isSmoothAt_tfae_of_isAlgClosed`).
* `RegularLocalRing.LocalDimensionCriterion`: over an arbitrary field, smoothness at a point is
  the fibre of the differentials having the local dimension (Stacks 00TT,
  `Algebra.isSmoothAt_tfae_localKrullDim_and_isRegularLocalRing`).
* `RegularLocalRing.SeparableResidueRegular`: at a prime with separable residue field, smoothness
  is regularity (Stacks 00TV, `Algebra.isSmoothAt_iff_isRegularLocalRing`).
* `RegularLocalRing.CharZeroRegularity`: in characteristic zero, smoothness, freeness of the
  localized differentials and regularity agree (Stacks 00TX,
  `Algebra.isSmoothAt_tfae_free_kaehlerDifferential_isRegularLocalRing`).
-/
