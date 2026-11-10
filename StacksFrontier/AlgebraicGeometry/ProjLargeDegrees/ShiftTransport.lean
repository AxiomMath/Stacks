module

public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.ShiftComposition
public import StacksFrontier.AlgebraicGeometry.ProjLargeDegrees.LocalFractions
public import StacksFrontier.RingTheory.GradedAlgebra.AddSubgroupGrading

/-!
# Bijectivity of the comparison depends only on the grading family

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a graded ring and `M` an `S`-module with a `ℤ`-graded family of
homogeneous pieces. The canonical map `𝒩 p ⟶ Γ(Proj 𝒮, M(p)~)` of Equation 01MR sends a
homogeneous element `x` to the *constant family of fractions* `y ↦ x / 1`, a family of elements
of the localized module fibers that does not mention the grading at all. Its source is the
subobject `𝒩 p` of `M` and its target is the group of sections cut out of that same family type
by the grading `M(p)`.

So the bijectivity of the map is a statement about two pieces of data only: the subobject `𝒩 p`
and the grading family `shiftedGrading 𝒩 p`. In particular `M(q)(m)` and `M(m + q)` — which are
*the same* family of subobjects, written with the two additions associated the other way
(`Stacks.GradedModule.shiftedGrading_shiftedGrading`) — give the same statement.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjLargeDegrees.constFraction`: the family `y ↦ x / 1` of fiber
  elements attached to an element of `M`.

## Main results

* `Stacks.AlgebraicGeometry.ProjLargeDegrees.moduleSections_congr`: equal gradings have equal
  groups of sections.
* `Stacks.AlgebraicGeometry.ProjLargeDegrees.coe_degreeNToGlobalSections`: the canonical global
  section of a homogeneous element is the constant family of fractions.
* `Stacks.AlgebraicGeometry.ProjLargeDegrees.bijective_degreeNToGlobalSections_iff`: bijectivity
  of the comparison, read off the constant families of fractions.
* `Stacks.AlgebraicGeometry.ProjLargeDegrees.bijective_degreeNToGlobalSections_shiftedGrading`:
  bijectivity in degree `m` for `M(q)` implies bijectivity in degree `m + q` for `M`.
* `Stacks.AlgebraicGeometry.ProjLargeDegrees.bijective_degreeNToGlobalSections_addSubgroupGrading`:
  the same for the grading re-seated in `AddSubgroup M`.

## References

* [Stacks Project, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShiftedSections
  (shiftedSectionsComponent degreeNToGlobalSections degreeNToGlobalSections_apply)
open Stacks.GradedModule (shiftedGrading)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjLargeDegrees

universe u v w t

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M]

/-- The constant family of fractions `y ↦ x / 1` of elements of the localized module fibers
attached to an element `x` of `M`. -/
def constFraction (x : M) :
    ∀ y : (⊤ : Opens (ProjectiveSpectrum.top 𝒮)), ModuleFiber (M := M) 𝒮 y.1 :=
  fun y => LocalizedModule.mk x (1 : y.1.asHomogeneousIdeal.toIdeal.primeCompl)

/-- Equal gradings have equal groups of sections. -/
theorem moduleSections_congr {𝒩₁ 𝒩₂ : ℤ → τ} [SetLike.GradedSMul 𝒮 𝒩₁]
    [SetLike.GradedSMul 𝒮 𝒩₂] (h : 𝒩₁ = 𝒩₂) (U : Opens (ProjectiveSpectrum.top 𝒮)) :
    moduleSections 𝒮 𝒩₁ U = moduleSections 𝒮 𝒩₂ U := by
  subst h
  rfl

variable (𝒩 : ℤ → τ) [DirectSum.Decomposition 𝒩] [SetLike.GradedSMul 𝒮 𝒩]

omit [DirectSum.Decomposition 𝒩] in
/-- The canonical global section of a homogeneous element is the constant family of fractions. -/
theorem coe_degreeNToGlobalSections (p : ℤ) (x : 𝒩 p) :
    (degreeNToGlobalSections 𝒮 𝒩 p x).1 = constFraction 𝒮 (x : M) :=
  funext fun y => degreeNToGlobalSections_apply 𝒮 𝒩 p x y.1

omit [DirectSum.Decomposition 𝒩] in
/-- The comparison in degree `p` is bijective exactly when distinct homogeneous elements of
degree `p` have distinct constant families of fractions and every section of `M(p)~` is such a
family. -/
theorem bijective_degreeNToGlobalSections_iff (p : ℤ) :
    Function.Bijective (degreeNToGlobalSections 𝒮 𝒩 p) ↔
      Function.Injective (fun x : 𝒩 p => constFraction 𝒮 (x : M)) ∧
        ∀ g ∈ moduleSections 𝒮 (shiftedGrading 𝒩 p) ⊤,
          ∃ x : 𝒩 p, constFraction 𝒮 (x : M) = g := by
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun x₁ x₂ hx => hinj (Subtype.ext ?_), fun g hg => ?_⟩
    · rwa [coe_degreeNToGlobalSections, coe_degreeNToGlobalSections]
    · obtain ⟨x, hx⟩ := hsurj (⟨g, hg⟩ : shiftedSectionsComponent 𝒮 𝒩 p)
      exact ⟨x, by rw [← coe_degreeNToGlobalSections, hx]⟩
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun x₁ x₂ hx => hinj ?_, fun s => ?_⟩
    · simpa only [coe_degreeNToGlobalSections] using congrArg Subtype.val hx
    · obtain ⟨x, hx⟩ := hsurj s.1 s.2
      exact ⟨x, Subtype.ext ((coe_degreeNToGlobalSections 𝒮 𝒩 p x).trans hx)⟩

omit [DirectSum.Decomposition 𝒩] in
/-- If the comparison `M(q)_m ⟶ Γ(Proj 𝒮, M(q)(m)~)` is bijective, then so is
`M_{m + q} ⟶ Γ(Proj 𝒮, M(m + q)~)`. -/
theorem bijective_degreeNToGlobalSections_shiftedGrading (q m : ℤ)
    (h : Function.Bijective (degreeNToGlobalSections 𝒮 (shiftedGrading 𝒩 q) m)) :
    Function.Bijective (degreeNToGlobalSections 𝒮 𝒩 (m + q)) := by
  rw [bijective_degreeNToGlobalSections_iff] at h ⊢
  rwa [moduleSections_congr 𝒮 (Stacks.GradedModule.shiftedGrading_shiftedGrading 𝒩 q m)] at h

omit [DirectSum.Decomposition 𝒩] in
/-- If the comparison in degree `p` for the grading `Stacks.GradedModule.addSubgroupGrading 𝒩`
re-seated in additive subgroups is bijective, then so is the comparison for `𝒩`. -/
theorem bijective_degreeNToGlobalSections_addSubgroupGrading (p : ℤ)
    (h : Function.Bijective
      (degreeNToGlobalSections 𝒮 (Stacks.GradedModule.addSubgroupGrading 𝒩) p)) :
    Function.Bijective (degreeNToGlobalSections 𝒮 𝒩 p) := by
  rw [bijective_degreeNToGlobalSections_iff] at h ⊢
  exact h

end Stacks.AlgebraicGeometry.ProjLargeDegrees

end
