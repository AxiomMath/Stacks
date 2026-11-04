module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KGroup
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.CanonicalFunctor
public import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupAffine.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularBoundedCoherentPerfect
public import StacksFrontier.CategoryTheory.Triangulated.KGroup.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two K-groups of a Noetherian regular scheme agree

Let `X` be a Noetherian regular scheme. The Grothendieck group `K₀(X) = K₀(D_perf(𝒪_X))` of
perfect complexes and the Grothendieck group `K'₀(X) = K₀(Coh(𝒪_X))` of coherent sheaves are
identified by the canonical comparison map `K₀(X) ⟶ K'₀(X)`.

## Main results

* `AlgebraicGeometry.isPerfect_eq_boundedCoherent_of_isRegular`: on a Noetherian regular scheme
  perfectness of an object of `D(𝒪_X)` is the conjunction of boundedness for the canonical
  t-structure and coherence of all cohomology sheaves, as an equality of object properties.
* `AlgebraicGeometry.exists_addEquiv_K0_coherentKZero_of_isRegular`: the comparison map
  `K₀(X) ⟶ K'₀(X)` is an isomorphism.

## Implementation notes

The comparison map of the source is the composite of the homomorphism induced by the inclusion
`D_perf(𝒪_X) ⟶ D^b_{Coh}(𝒪_X)` with the inverse of the identification
`K'₀(X) = K₀(D^b_{Coh}(𝒪_X))` of [Stacks, Tag 0FCS]. On a Noetherian regular scheme the two
subcategories coincide by [Stacks, Tag 0FDC], so that inclusion is the identity and the
comparison map is the inverse of the identification itself. It is therefore recorded here as the
unique additive homomorphism `K₀(X) ⟶ K'₀(X)` sending the class of a perfect complex which is a
coherent sheaf placed in degree zero to the class of that sheaf; uniqueness holds because the
classes of coherent sheaves generate `K'₀(X)`.

Boundedness is spelled by `DerivedCategoryB.derivedCategoryBBounded` in [Stacks, Tag 0FDC] and by
`CategoryTheory.Triangulated.TStructure.bounded` in [Stacks, Tag 0FCS]; the two are converted into
each other by `DerivedCategory.isGE_iff` and `DerivedCategory.isLE_iff`. Coherence of a sheaf of
modules also appears under two names, bridged by
`Stacks.AlgebraicGeometry.GrothendieckGroupAffine.isCoherent_iff_isCoherent'`, and the name used
here is the one cutting out the category whose Grothendieck group is `K'₀(X)`.

## References

* [Stacks Project, Tag 0FDI](https://stacks.math.columbia.edu/tag/0FDI)
* [Stacks Project, Tag 0FDC](https://stacks.math.columbia.edu/tag/0FDC)
* [Stacks Project, Tag 0FCS](https://stacks.math.columbia.edu/tag/0FCS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory StrictlyPerfect
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- **On a Noetherian regular scheme the perfect objects are the objects of `D^b_{Coh}(𝒪_X)`**,
as an equality of object properties of `D(𝒪_X)`: perfectness is boundedness for the canonical
t-structure together with coherence of every cohomology sheaf. -/
theorem isPerfect_eq_boundedCoherent_of_isRegular (X : Scheme.{u}) [IsNoetherian X]
    (hX : IsRegular X) :
    (fun K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) =>
        Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K)
      = (DerivedCategory.TStructure.t (C := SheafOfModules.{u} X.ringCatSheaf)).bounded ⊓
        fun K => ∀ n : ℤ, Stacks.SheafOfModules.coherentModules X.ringCatSheaf
          ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) n).obj K) := by
  ext K
  rw [show Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K
    ↔ _ from Stacks.AlgebraicGeometry.PerfectCohomology.isPerfect_iff_isBoundedCoherent_of_isRegular
      hX K]
  exact and_congr (and_congr (exists_congr fun a => (DerivedCategory.isGE_iff K a).symm)
    (exists_congr fun b => (DerivedCategory.isLE_iff K b).symm))
    (forall_congr' fun n =>
      (Stacks.AlgebraicGeometry.GrothendieckGroupAffine.isCoherent_iff_isCoherent' _).symm)

/-- **[Stacks, Tag 0FDI].** Let `X` be a Noetherian regular scheme. Then the canonical map
`K₀(X) ⟶ K'₀(X)` from the Grothendieck group of perfect complexes to the Grothendieck group of
coherent sheaves is an isomorphism.

Every coherent sheaf placed in degree zero is a perfect complex, the comparison map takes the
class of such a complex to the class of the sheaf, and it is the only additive homomorphism
`K₀(X) ⟶ K'₀(X)` which does so. -/
@[stacks 0FDI, sga "6 IV 2.5" "(i), special case"]
theorem exists_addEquiv_K0_coherentKZero_of_isRegular (X : Scheme.{u}) [IsNoetherian X]
    (hX : IsRegular X) :
    ∃ e : Pretriangulated.K0 (PerfectDerivedCategory X) ≃+ CoherentKZero X,
      (∀ F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf,
          ∃ K : PerfectDerivedCategory X,
            Nonempty (K.obj ≅ (DerivedCategory.singleFunctor X.Modules 0).obj F.obj)) ∧
        (∀ (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)
            (K : PerfectDerivedCategory X),
            (K.obj ≅ (DerivedCategory.singleFunctor X.Modules 0).obj F.obj) →
              e (Pretriangulated.K0.cls K) = KZero.mk _ F) ∧
          ∀ φ : Pretriangulated.K0 (PerfectDerivedCategory X) →+ CoherentKZero X,
            (∀ (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)
                (K : PerfectDerivedCategory X),
                (K.obj ≅ (DerivedCategory.singleFunctor X.Modules 0).obj F.obj) →
                  φ (Pretriangulated.K0.cls K) = KZero.mk _ F) → φ = e.toAddMonoidHom := by
  have : ObjectProperty.IsTriangulated
      (fun K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) =>
        Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K) :=
    Stacks.Perfect.BoundedLocallyFreeComplexes.perfectDerivedProperty_isTriangulated X
  obtain ⟨e, h₁, h₂⟩ := DerivedCategory.exists_addEquiv_K0_of_isWeakSerreClass
    (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)
    (isPerfect_eq_boundedCoherent_of_isRegular X hX)
  refine ⟨e.symm, h₁, fun F K hK => ?_, fun φ hφ => ?_⟩
  · exact e.symm_apply_eq.2 (h₂ F K hK).symm
  · have h : φ.comp e.toAddMonoidHom = AddMonoidHom.id _ := KZero.hom_ext fun F => by
      obtain ⟨K, ⟨iso⟩⟩ := h₁ F
      exact (congrArg φ (h₂ F K iso)).trans (hφ F K iso)
    refine AddMonoidHom.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    exact (DFunLike.congr_fun h x).trans (e.symm_apply_apply x).symm

end AlgebraicGeometry

end
