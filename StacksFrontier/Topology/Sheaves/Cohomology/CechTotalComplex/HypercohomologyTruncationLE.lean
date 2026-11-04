module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyTruncationPairing
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyBrutalCollapse
public import StacksFrontier.Algebra.Homology.StupidTruncationLE
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologySingleCochains

/-!
# The quotient brutal truncations in hypercohomology

For a bounded below complex `K` of `𝒪_X`-modules the brutal truncation `σ^{≤p}K` keeps the terms
of `K` in degrees `≤ p`; it is a quotient of `K`, and the sequences

`0 ⟶ Kᵖ[-p] ⟶ σ^{≤p}K ⟶ σ^{≤p-1}K ⟶ 0`

are short exact. This file records them as sequences of bounded below complexes.

## Main definitions

* `Stacks.Cech.Hypercohomology.truncLEPlus`: `σ^{≤p}K` as a bounded below complex.
* `Stacks.Cech.Hypercohomology.truncLEπ`: the projection `K ⟶ σ^{≤p}K`.
* `Stacks.Cech.Hypercohomology.truncLESC`: the short exact sequence above.

## References

* [Stacks Project, Tag 0118](https://stacks.math.columbia.edu/tag/0118)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open StacksDraft.StupidTruncation
open Stacks.Cohomology.RightDerivedBoundary (toSC)

universe u

namespace Stacks.Cech.Hypercohomology

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))

/-- The quotient brutal truncation `σ^{≤p}K` of a bounded below complex, as a bounded below
complex. -/
def truncLEPlus (p : ℤ) : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)) :=
  ⟨K.obj.stupidTrunc (embeddingUpIntLE p), by
    obtain ⟨n, hn⟩ := K.2
    refine ⟨n, (CochainComplex.isStrictlyGE_iff _ n).2 fun j hj => ?_⟩
    by_cases hjp : j ≤ p
    · exact (CochainComplex.isZero_of_isStrictlyGE K.obj n j hj).of_iso
        (stupidTruncLEXIso K.obj p j hjp)
    · exact CochainComplex.isZero_of_isStrictlyLE (K.obj.stupidTrunc (embeddingUpIntLE p)) p j
        (by omega)⟩

/-- The terms of `σ^{≤p}K` above `p` vanish. -/
theorem isZero_truncLEPlus_X {p j : ℤ} (h : p < j) : IsZero ((truncLEPlus O K p).obj.X j) :=
  CochainComplex.isZero_of_isStrictlyLE (K.obj.stupidTrunc (embeddingUpIntLE p)) p j h

/-- The projection `K ⟶ σ^{≤p}K`. -/
def truncLEπ (p : ℤ) : K ⟶ truncLEPlus O K p :=
  ObjectProperty.homMk (K.obj.πStupidTrunc (embeddingUpIntLE p))

/-- In a retained degree `j ≤ p` the projection `K ⟶ σ^{≤p}K` is an isomorphism. -/
instance isIso_truncLEπ_f (p j : ℤ) [Fact (j ≤ p)] : IsIso ((truncLEπ O K p).hom.f j) :=
  isIso_πStupidTruncLE_f K.obj p j Fact.out

/-- The comparison `σ^{≤b}K ⟶ σ^{≤a}K` for `a ≤ b`. -/
def truncLEMap {a b : ℤ} (h : a ≤ b) : truncLEPlus O K b ⟶ truncLEPlus O K a :=
  ObjectProperty.homMk (stupidTruncLEMapLE K.obj h)

/-- The projection `K ⟶ σ^{≤b}K` followed by the comparison `σ^{≤b}K ⟶ σ^{≤a}K` is the
projection `K ⟶ σ^{≤a}K`. -/
theorem truncLEπ_truncLEMap {a b : ℤ} (h : a ≤ b) :
    truncLEπ O K b ≫ truncLEMap O K h = truncLEπ O K a :=
  ObjectProperty.hom_ext _ (π_stupidTruncLEMapLE K.obj h)

/-- The inclusion `Kᵖ[-p] ⟶ σ^{≤p}K` of the top term. -/
def truncLEι (p : ℤ) : singlePlus O (K.obj.X p) p ⟶ truncLEPlus O K p :=
  ObjectProperty.homMk (stupidTruncLEι K.obj p)

/-- **The short exact sequence `0 ⟶ Kᵖ[-p] ⟶ σ^{≤p}K ⟶ σ^{≤p'}K ⟶ 0`**, `p' + 1 = p`, of bounded
below complexes. -/
def truncLESC (p p' : ℤ) (hp : p' + 1 = p) :
    ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) :=
  ShortComplex.mk (truncLEι O K p) (truncLEMap O K (show p' ≤ p by omega))
    (ObjectProperty.hom_ext _ (stupidTruncLEShortComplex K.obj p p' hp).zero)

/-- The sequence `0 ⟶ Kᵖ[-p] ⟶ σ^{≤p}K ⟶ σ^{≤p'}K ⟶ 0`, `p' + 1 = p`, is short exact as a
sequence of complexes. -/
theorem truncLESC_shortExact (p p' : ℤ) (hp : p' + 1 = p) :
    (toSC (truncLESC O K p p' hp)).ShortExact :=
  stupidTruncLEShortComplex_shortExact K.obj p p' hp

variable {O K} in
/-- Čech cohomology computes the cohomology of the terms of `σ^{≤p}K` when it computes that of
the terms of `K`. -/
theorem cechComputesSheaf_truncLEPlus_X (hK : ∀ j, CechComputesSheaf O (K.obj.X j)) (p j : ℤ) :
    CechComputesSheaf O ((truncLEPlus O K p).obj.X j) := by
  by_cases hj : j ≤ p
  · exact cechComputesSheaf_of_iso O (stupidTruncLEXIso K.obj p j hj).symm (hK j)
  · exact cechComputesSheaf_of_isZero O (isZero_truncLEPlus_X O K (by omega))

variable {O K} in
/-- Čech cohomology computes the cohomology of the terms of `σ^{≥p}K` when it computes that of
the terms of `K`. -/
theorem cechComputesSheaf_truncPlus_X (hK : ∀ j, CechComputesSheaf O (K.obj.X j)) (p j : ℤ) :
    CechComputesSheaf O ((truncPlus O K.obj p).obj.X j) := by
  by_cases hj : p ≤ j
  · exact cechComputesSheaf_of_iso O (stupidTruncGEXIso K.obj p j hj).symm (hK j)
  · exact cechComputesSheaf_of_isZero O
      (CochainComplex.isZero_of_isStrictlyGE (K.obj.stupidTrunc (embeddingUpIntGE p)) p j
        (by omega))

variable {O} in
/-- Čech cohomology computes the cohomology of the terms of `F[-p]` when it computes that of
`F`. -/
theorem cechComputesSheaf_singlePlus_X' {F : SheafOfModules.{u} (ringSheaf O)}
    (hF : CechComputesSheaf O F) (p j : ℤ) : CechComputesSheaf O ((singlePlus O F p).obj.X j) := by
  by_cases hj : j = p
  · subst hj
    exact cechComputesSheaf_of_iso O (HomologicalComplex.singleObjXSelf (up ℤ) j F).symm hF
  · exact cechComputesSheaf_of_isZero O (HomologicalComplex.isZero_single_obj_X (up ℤ) p F j hj)

end Stacks.Cech.Hypercohomology

end
