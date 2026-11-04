module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreCohomologyRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CohomologyVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricFibreSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtension
public import StacksFrontier.AlgebraicGeometry.ProjectiveCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves

/-!
# Cohomology of `ℙ¹` over a strictly henselian local ring and of a geometric fibre

Let `A` be a strictly henselian local ring with residue field `κ`, let `X = ℙ¹_A` and let
`x : Spec Ω ⟶ Spec A` be a geometric point over the closed point, through an extension `κ ⊆ Ω`
with `Ω` separably closed. The second paragraph of the proof of the proper base change theorem
([Stacks, Tag 095T]) is
`H^q(ℙ¹_A, F) = H^q(ℙ¹_κ, F|) = H^q(ℙ¹_Ω, F|)` for a sheaf `F` killed by a prime `ℓ`: the first
equality is the closed fibre computation
(`Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_closedFibre_of_injective`, which
consumes [Stacks, Tag 0A5H]), the second is [Stacks, Tag 0A5E].

In the form proved here: `H^q(ℙ¹_A, c⁻¹M)` vanishes exactly when
`H^q(ℙ¹_A ×_{Spec A} Spec Ω, c'⁻¹M)` does, for a sheaf `M` on any scheme `W` and
`c : ℙ¹_A ⟶ W` with `c⁻¹M` killed by `ℓ`, `c'` being `c` composed with the projection.

## Main results

* `Stacks.EtaleCohomology.topologicalKrullDim_closedFibre_projectiveLine` — the closed fibre of
  `ℙ¹_A` has dimension at most one.
* `Stacks.EtaleCohomology.subsingleton_H_projectiveLine_iff_geometricFibre` — the comparison,
  granted [Stacks, Tag 0A5H] and [Stacks, Tag 0A5E] as hypotheses.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.ZModSheaf

universe u

namespace Stacks.EtaleCohomology

section Torsion

/-- A sheaf killed by `ℓ` stays killed by `ℓ` under inverse image. -/
theorem zsmul_id_inverseImage_eq_zero {Y Z : Scheme.{u}} (c : Z ⟶ Y)
    {M : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (n : ℤ) (hM : n • 𝟙 M = 0) :
    n • 𝟙 ((etaleAbelianInverseImage.{u, 0} c).obj M) = 0 := by
  rw [← (etaleAbelianInverseImage.{u, 0} c).map_id, ← Functor.map_zsmul, hM, Functor.map_zero]

/-- A sheaf isomorphic to one killed by `n` is killed by `n`. -/
theorem zsmul_id_eq_zero_of_iso {Y : Scheme.{u}}
    {M M' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : M ≅ M') (n : ℤ)
    (hM : n • 𝟙 M = 0) : n • 𝟙 M' = 0 := by
  have h : n • 𝟙 M' = e.inv ≫ (n • 𝟙 M) ≫ e.hom := by
    rw [Preadditive.zsmul_comp, Category.id_comp, Preadditive.comp_zsmul, e.inv_hom_id]
  rw [h, hM, zero_comp, comp_zero]

/-- A sheaf killed by a positive integer is a torsion sheaf. -/
theorem torsionSheafProperty_of_zsmul_id_eq_zero {Y : Scheme.{u}}
    {M : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hM : (ℓ : ℤ) • 𝟙 M = 0) :
    Stacks.Torsion.torsionSheafProperty.{u + 1} Y.smallEtaleTopology M := by
  intro U x
  refine ⟨⊤, (Y.smallEtaleTopology).top_mem U, fun V g _ ↦ ⟨ℓ, hℓ, ?_⟩⟩
  rw [← natCast_zsmul]
  exact (zsmul_id_eq_zero_iff M (ℓ : ℤ)).1 hM _ _

end Torsion

section ProjectiveLine

variable (A : Type u) [CommRing A] [StrictlyHenselianLocalRing A] (Ω : Type u) [Field Ω]
  [IsSepClosed Ω] [Algebra (IsLocalRing.ResidueField A) Ω] {ℓ : ℕ}

/-- **The closed fibre of `ℙ¹_A` over a local ring has dimension at most one**. -/
theorem topologicalKrullDim_closedFibre_projectiveLine :
    topologicalKrullDim (closedFibre A (ProjectiveSpace 1 (Spec (.of A)) ↘ Spec (.of A))) ≤ 1 := by
  have e := ProjectiveSpace.baseChangeIso 1 (residueFieldPoint A)
  change topologicalKrullDim (pullback (ProjectiveSpace 1 (Spec (.of A)) ↘ Spec (.of A))
    (residueFieldPoint A) : Scheme.{u}) ≤ 1
  rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph]
  exact (topologicalKrullDim_projectiveSpace_one (IsLocalRing.ResidueField A)).le

variable [∀ Y : Scheme.{u}, HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

omit [IsSepClosed Ω] in
/-- **[Stacks, Tag 095T], second paragraph, as a vanishing statement.** Let `A` be strictly
henselian local with residue field `κ`, `X₀` the closed fibre of `ℙ¹_A`, `κ ⊆ Ω` separably
closed and `Z = X₀ ×_κ Spec Ω`. For a sheaf `M` on a scheme `W` and `c : ℙ¹_A ⟶ W` with `c⁻¹M`
killed by a prime `ℓ`, `H^q(ℙ¹_A, c⁻¹M)` vanishes exactly when `H^q(Z, M|_Z)` does, granted
[Stacks, Tag 0A5H] (`h0A5H`) and [Stacks, Tag 0A5E] (`h0A5E`). -/
theorem subsingleton_H_projectiveLine_iff_geometricFibre
    (h0A5H : ∀ (J : SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1}
        (ProjectiveSpace 1 (Spec (.of A))).smallEtaleTopology ℓ)), Injective J →
      ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
        (closedFibreInclusion A (ProjectiveSpace 1 (Spec (.of A)) ↘ Spec (.of A)))).obj
          ((SheafOfModules.toSheaf _).obj J)) q))
    (h0A5E : ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of (IsLocalRing.ResidueField A))) [IsProper f]
      (_ : topologicalKrullDim X ≤ 1) (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
      (_ : Stacks.Torsion.torsionSheafProperty.{u + 1} (smallEtaleTopology X) F) (q : ℕ),
      Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
        (scalarExtensionFst (IsLocalRing.ResidueField A) Ω f) F q))
    (hℓ : ℓ.Prime) {W : Scheme.{u}} (c : ProjectiveSpace 1 (Spec (.of A)) ⟶ W)
    (M : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hM : (ℓ : ℤ) • 𝟙 ((etaleAbelianInverseImage.{u, 0} c).obj M) = 0) (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} c).obj M) q) ↔
      Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
        (scalarExtensionFst (IsLocalRing.ResidueField A) Ω
            (closedFibreProjection A (ProjectiveSpace 1 (Spec (.of A)) ↘ Spec (.of A))) ≫
          closedFibreInclusion A (ProjectiveSpace 1 (Spec (.of A)) ↘ Spec (.of A)) ≫ c)).obj
            M) q) := by
  set π := ProjectiveSpace 1 (Spec (.of A)) ↘ Spec (.of A)
  have h₁ := subsingleton_H_inverseImage_iff_of_bijective M q (closedFibreInclusion A π ≫ c) c
    (closedFibreInclusion A π) rfl
    (bijective_etaleCohomologyRestrictionMap_closedFibre_of_injective A π ℓ h0A5H q _ hM)
  have hpr : IsProper (closedFibreProjection A π) :=
    isProper_closedFibreProjection (f := ProjectiveSpace 1 (Spec (.of A)) ↘ Spec (.of A)) A
  have hM' := zsmul_id_inverseImage_eq_zero (closedFibreInclusion A π) (ℓ : ℤ) hM
  have hM'' := zsmul_id_eq_zero_of_iso
    ((etaleAbelianInverseImageCompIso'.{u, 0} (closedFibreInclusion A π) c _ rfl).app M).symm
    (ℓ : ℤ) hM'
  have h₂ := subsingleton_H_inverseImage_iff_of_bijective M q
    (scalarExtensionFst (IsLocalRing.ResidueField A) Ω (closedFibreProjection A π) ≫
      closedFibreInclusion A π ≫ c) (closedFibreInclusion A π ≫ c)
    (scalarExtensionFst (IsLocalRing.ResidueField A) Ω (closedFibreProjection A π)) rfl
    (@h0A5E _ (closedFibreProjection A π) hpr (topologicalKrullDim_closedFibre_projectiveLine A) _
      (torsionSheafProperty_of_zsmul_id_eq_zero hℓ.pos hM'') q)
  exact h₁.symm.trans h₂.symm

end ProjectiveLine

end Stacks.EtaleCohomology

end
