module

public import StacksFrontier.AlgebraicGeometry.ProjAmple.Basic
public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Locality
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneCover.Basic
public import StacksFrontier.AlgebraicGeometry.TwistTensor.Basic

/-!
# Twists and ampleness on a `Proj` covered by standard opens of degree-one elements

Let `S = ⨁_{n ≥ 0} 𝒮 n` be a nonnegatively graded ring whose `Proj` is covered by the standard
opens `D₊(g)` of *some* homogeneous elements `g` of degree one. This is strictly weaker than
`S` being generated in degree one over `𝒮 0` — the degree-one elements need not generate — and
it is already enough for the whole package of [Stacks, Tag 01MU] at `d = 1`:

* the locus `W₁` of [Stacks, Tag 01MU] is all of `Proj 𝒮`, because `D₊(g) ⊆ W₁` for `g` of
  degree one;
* hence every twist `𝒪(n)` is invertible and every multiplication map
  `𝒪(n) ⊗ 𝒪(m) → 𝒪(n + m)` is an isomorphism;
* and `𝒪(1)` is ample as soon as `Proj 𝒮` is quasi-compact, which a finite such cover supplies
  because a standard open of a degree-one element is affine.

The hypothesis is the one satisfied by the weighted examples of [Stacks, Tag 01VO] and
[Stacks, Tag 01VP], where `S` is *not* generated in degree one, so that the route through
`Algebra.adjoin (𝒮 0) (𝒮 1) = ⊤` is unavailable.

## Main results

* `Stacks.ProjDegreeOneCover.compactSpace_of_iSup_basicOpen_eq_top`: a finite cover by standard
  opens of degree-one elements makes `Proj 𝒮` quasi-compact.
* `Stacks.ProjDegreeOneCover.isAmple_twistingModule_one`: **`𝒪(1)` is ample.**

## Implementation notes

Invertibility is produced by
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.isInvertible_twistingSheaf_of_ratioLocus_eq_top`
at `d = 1`, whose conclusion is stated at `(Proj 𝒮).presheaf` and `(Proj 𝒮).ringCatSheaf.2`
while ampleness is stated at `(Proj 𝒮).toRingedSpace.presheaf` and
`(structureSheafRing (Proj 𝒮).toRingedSpace).property`. The two spellings are not crossed by
`inferInstance`, so the invertibility term is applied by name at the expected type, exactly as
in the implementation notes of `StacksFrontier/AlgebraicGeometry/ProjAmple/Basic.lean`; for the
same reason `isAmple_twistingModule_one` names its invertibility argument explicitly rather
than taking it as an instance.

## References

* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
  (isInvertible_twistingSheaf_of_ratioLocus_eq_top twistMultiplicationMap)
open Stacks.AlgebraicGeometry.TwistTensor (isIso_twistMultiplicationMap_of_ratioLocus_eq_top)

universe u

namespace Stacks.ProjDegreeOneCover

variable {S σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **A finite cover of `Proj 𝒮` by standard opens of degree-one elements makes it
quasi-compact.** Each such standard open is affine, hence quasi-compact, and a finite union of
quasi-compact sets is quasi-compact. No finiteness hypothesis on `S` is used, so this also
applies to graded rings that are not of finite type over `𝒮 0`. -/
public theorem compactSpace_of_iSup_basicOpen_eq_top {ι : Type} [Finite ι] (f : ι → S)
    (hf : ∀ i, f i ∈ 𝒮 1) (hcov : (⨆ i, Proj.basicOpen 𝒮 (f i)) = ⊤) :
    CompactSpace (AlgebraicGeometry.Proj 𝒮) := by
  refine ⟨?_⟩
  have h : (Set.univ : Set (AlgebraicGeometry.Proj 𝒮)) =
      ⋃ i, (Proj.basicOpen 𝒮 (f i) : Set (AlgebraicGeometry.Proj 𝒮)) := by
    rw [← TopologicalSpace.Opens.coe_iSup, hcov]
    rfl
  rw [h]
  exact isCompact_iUnion fun i =>
    (Stacks.AlgebraicGeometry.ProjDegreeOne.isAffineOpen_basicOpen_degreeOne
      𝒮 (f i) (hf i)).isCompact

/-- A cover of `Proj 𝒮` by standard opens of degree-one elements, in the pointwise form the
ampleness argument produces, is the supremum condition
`Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.DegreeOneCover`. -/
public theorem degreeOneCover_of_forall_exists
    (hcov : ∀ x : ProjectiveSpectrum.top 𝒮, ∃ g ∈ 𝒮 1, x ∈ ProjectiveSpectrum.basicOpen 𝒮 g) :
    Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.DegreeOneCover 𝒮 := by
  refine top_le_iff.mp fun x _ => ?_
  obtain ⟨g, hg, hxg⟩ := hcov x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hg⟩, hxg⟩

/-- **`𝒪(1)` is an ample invertible sheaf on `Proj 𝒮`** when `Proj 𝒮` is quasi-compact and every
point lies in the standard open of some degree-one element. The graded ring need not be
generated in degree one. -/
public theorem isAmple_twistingModule_one (hcpt : CompactSpace (AlgebraicGeometry.Proj 𝒮))
    (hcov : ∀ x : ProjectiveSpectrum.top 𝒮, ∃ g ∈ 𝒮 1, x ∈ ProjectiveSpectrum.basicOpen 𝒮 g) :
    @AlgebraicGeometry.Scheme.Modules.IsAmple (AlgebraicGeometry.Proj 𝒮)
      (Stacks.ProjTwistSection.twistingModule 𝒮 1)
      (Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isInvertible_twistingSheaf 𝒮
        (degreeOneCover_of_forall_exists 𝒮 hcov) 1) :=
  @Stacks.ProjAmple.isAmple_twistingModule_one _ _ _ _ _ 𝒮 _
    (Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isInvertible_twistingSheaf 𝒮
      (degreeOneCover_of_forall_exists 𝒮 hcov) 1) hcpt hcov

end Stacks.ProjDegreeOneCover

end
