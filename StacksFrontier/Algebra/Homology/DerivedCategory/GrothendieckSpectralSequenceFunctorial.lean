module

public import StacksFrontier.Algebra.Homology.DerivedCategory.GrothendieckSpectralSequenceFunctorial.SpectralSequenceFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.GrothendieckSpectralSequenceFunctorial.PageTwo
public import StacksFrontier.Algebra.Homology.DerivedCategory.GrothendieckSpectralSequenceFunctorial.FirstQuadrantAbutment
public import StacksFrontier.Algebra.Homology.DerivedCategory.GrothendieckSpectralSequenceFunctorial.RightHalfPlaneAbutment

/-!
# The functorial Grothendieck spectral sequence of a composition

This file re-exports its parts:

* `GrothendieckSpectralSequenceFunctorial.SpectralSequenceFunctor`: the truncation spectral
  object as a functor, read as a spectral object of the functor category, and the Grothendieck
  spectral sequence as a functor on `D⁺(𝒜)` and on `𝒜`, with its left-half-plane vanishing;
* `GrothendieckSpectralSequenceFunctorial.PageTwo`: the second-page identifications
  `plusPageTwoIso` and `natPageTwoIso`;
* `GrothendieckSpectralSequenceFunctorial.FirstQuadrantAbutment`: the abutment filtration by the
  images of the `H`-terms and the first-quadrant abutment `natAbutment`;
* `GrothendieckSpectralSequenceFunctorial.RightHalfPlaneAbutment`: the right-half-plane abutment
  `plusAbutment` and `abutsToChangeAbutmentPlus`.
-/
