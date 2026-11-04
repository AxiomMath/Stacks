module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedUnitSquare
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison

/-!
# Lifting a twisted map through the derived functor of an exact functor

Let `F : C₁ ⥤ C₂` be an exact functor between abelian categories, `RF` the total right derived
functor of `F` on homotopy categories and `u : F ⟶ RF` its unit, read on a cochain complex `A`
as `StacksDraft.DerivedUnitSquare.unitQ F u A : F(A) ⟶ RF(A)`.

Suppose a map `ζ : A ⟶ A[2]` of `D(C₁)` and a map of complexes `κ₀ : B ⟶ F(A)` are given,
together with `D₀ : F(A) ⟶ B[2]` such that `D₀ ≫ κ₀[2]` is the image of `ζ` under the functor
`F` induces on derived categories. Then `RF` of the untwisted map `ζ[-2] : A[-2] ⟶ A` lifts
through `κ₀ ≫ u_A : B ⟶ RF(A)`. This is the bookkeeping that turns the lower right triangle of
[Stacks, Tag 0FUQ], read on the ambient space through the exact direct image along a closed
immersion, into the lift of the canonical map `Ω^•_{X'/S} ⟶ Rj_*Ω^•_{E/S}` used in the proof of
[Stacks, Tag 0FUW].

## Main results

* `CategoryTheory.Functor.exists_comp_eq_map_shift_comp_shiftFunctorCompIsoId`: the lift for a
  functor commuting with the shift.
* `StacksDraft.ExactFunctorShiftedLift.unitQ_eq`: the unit of `RF`, read on a complex, is the
  comparison of `F` on derived categories with `RF`.
* `StacksDraft.ExactFunctorShiftedLift.exists_comp_unitQ_eq_map`: the lift through the unit.

## References

* [Stacks Project, Tag 0FUQ](https://stacks.math.columbia.edu/tag/0FUQ)
* [Stacks Project, Tag 0FUW](https://stacks.math.columbia.edu/tag/0FUW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
  (G : C ⥤ D) [G.CommShift ℤ]

/-- **Untwisting a lift.** Let `ζ : A ⟶ A[2]`, `κ : B ⟶ G(A)` and `D₀ : G(A) ⟶ B[2]` satisfy
`D₀ ≫ κ[2] = G(ζ)`, read through the commutation of `G` with the shift. Then `G` of the untwisted
map `ζ[-2] : A[-2] ⟶ A` factors through `κ`. -/
theorem exists_comp_eq_map_shift_comp_shiftFunctorCompIsoId {A : C} {B : D}
    (ζ : A ⟶ A⟦(2 : ℤ)⟧) (κ : B ⟶ G.obj A) (D₀ : G.obj A ⟶ B⟦(2 : ℤ)⟧)
    (h : D₀ ≫ κ⟦(2 : ℤ)⟧' = G.map ζ ≫ (G.commShiftIso (2 : ℤ)).hom.app A) :
    ∃ s : G.obj (A⟦(-2 : ℤ)⟧) ⟶ B,
      s ≫ κ = G.map (ζ⟦(-2 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId C (2 : ℤ) (-2) (by norm_num)).hom.app A) := by
  refine ⟨(G.commShiftIso (-2 : ℤ)).hom.app A ≫ D₀⟦(-2 : ℤ)⟧' ≫
    (shiftFunctorCompIsoId D (2 : ℤ) (-2) (by norm_num)).hom.app B, ?_⟩
  have hn := (shiftFunctorCompIsoId D (2 : ℤ) (-2) (by norm_num)).hom.naturality κ
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [Functor.map_comp, Functor.map_shiftFunctorCompIsoId_hom_app,
    ← Category.assoc (G.map _), Functor.commShiftIso_hom_naturality]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, ← h, Functor.map_comp_assoc, hn]

end CategoryTheory.Functor

namespace StacksDraft.ExactFunctorShiftedLift

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The total right derived functor of `F` on homotopy categories. -/
abbrev rightDerived : DerivedCategory C₁ ⥤ DerivedCategory C₂ :=
  (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ))

/-- The unit of the total right derived functor of `F`. -/
abbrev rightDerivedUnit :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ rightDerived F :=
  (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ))

/-- **The unit of the total right derived functor of an exact functor, read on a complex**, is
the comparison of `F(K)` with `F` on derived categories followed by the identification of the
latter with the total right derived functor. -/
theorem unitQ_eq (K : CochainComplex C₁ ℤ) :
    StacksDraft.DerivedUnitSquare.unitQ F (rightDerivedUnit F) K =
      F.mapDerivedCategoryFactors.inv.app K ≫
        (Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived F).hom.app
          (DerivedCategory.Q.obj K) := by
  have hfac := Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived_fac_app F
    ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K)
  have hh := F.mapDerivedCategoryFactorsh_hom_app K
  have hinv : F.mapDerivedCategoryFactorsh.inv.app
      ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K) =
      DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K) ≫
        (DerivedCategory.quotientCompQhIso C₂).hom.app _ ≫
        F.mapDerivedCategoryFactors.inv.app K ≫
        F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₁).inv.app K) := by
    rw [← cancel_epi (F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K)), Iso.hom_inv_id_app, hh]
    simp only [Functor.comp_obj, Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    simp
  simp only [StacksDraft.DerivedUnitSquare.unitQ, ← hfac, hinv]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp

/-- **The lift through the unit of the total right derived functor of an exact functor.** Let
`ζ : A ⟶ A[2]` be a map of `D(C₁)`, `κ₀ : B ⟶ F(A)` a map of complexes and `D₀ : F(A) ⟶ B[2]`
with `D₀ ≫ κ₀[2] = F(ζ)`, the right-hand side being `ζ` read through the functor `F` induces on
derived categories. Then `RF` of the untwisted map `ζ[-2] : A[-2] ⟶ A` lifts through
`κ₀ ≫ u_A : B ⟶ RF(A)`. -/
theorem exists_comp_unitQ_eq_map {A : CochainComplex C₁ ℤ} {B : CochainComplex C₂ ℤ}
    (ζ : DerivedCategory.Q.obj A ⟶ (DerivedCategory.Q.obj A)⟦(2 : ℤ)⟧)
    (κ₀ : B ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A)
    (D₀ : DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A) ⟶
      (DerivedCategory.Q.obj B)⟦(2 : ℤ)⟧)
    (h : D₀ ≫ (DerivedCategory.Q.map κ₀)⟦(2 : ℤ)⟧' =
      F.mapDerivedCategoryFactors.inv.app A ≫ F.mapDerivedCategory.map ζ ≫
        (F.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
          (F.mapDerivedCategoryFactors.hom.app A)⟦(2 : ℤ)⟧') :
    ∃ δ : (rightDerived F).obj ((DerivedCategory.Q.obj A)⟦(-2 : ℤ)⟧) ⟶ DerivedCategory.Q.obj B,
      δ ≫ DerivedCategory.Q.map κ₀ ≫
          StacksDraft.DerivedUnitSquare.unitQ F (rightDerivedUnit F) A =
        (rightDerived F).map (ζ⟦(-2 : ℤ)⟧' ≫
          (shiftFunctorCompIsoId _ (2 : ℤ) (-2) (by norm_num)).hom.app _) := by
  have h' : (F.mapDerivedCategoryFactors.hom.app A ≫ D₀) ≫
      (DerivedCategory.Q.map κ₀ ≫ F.mapDerivedCategoryFactors.inv.app A)⟦(2 : ℤ)⟧' =
      F.mapDerivedCategory.map ζ ≫ (F.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ := by
    rw [Functor.map_comp, Category.assoc, ← Category.assoc D₀, h]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
    simp
  obtain ⟨s, hs⟩ :=
    F.mapDerivedCategory.exists_comp_eq_map_shift_comp_shiftFunctorCompIsoId ζ _ _ h'
  refine ⟨(Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived F).inv.app _ ≫ s, ?_⟩
  rw [unitQ_eq, Category.assoc, ← Category.assoc (DerivedCategory.Q.map κ₀), ← Category.assoc s,
    hs, ← (Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived F).inv.naturality_assoc]
  simp

/-- `exists_comp_unitQ_eq_map`, with the hypothesis read through a second exact functor `F'` equal
to `F` and a map of complexes `κ₀'` corresponding to `κ₀` across that equality. -/
theorem exists_comp_unitQ_eq_map_of_eq (F' : C₁ ⥤ C₂) [F'.Additive] [PreservesFiniteLimits F']
    [PreservesFiniteColimits F'] (hF : F' = F) {A : CochainComplex C₁ ℤ}
    {B : CochainComplex C₂ ℤ}
    (ζ : DerivedCategory.Q.obj A ⟶ (DerivedCategory.Q.obj A)⟦(2 : ℤ)⟧)
    (κ₀ : B ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A)
    (κ₀' : B ⟶ (F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj A) (hκ : HEq κ₀' κ₀)
    (D₀ : DerivedCategory.Q.obj ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj A) ⟶
      (DerivedCategory.Q.obj B)⟦(2 : ℤ)⟧)
    (h : D₀ ≫ (DerivedCategory.Q.map κ₀')⟦(2 : ℤ)⟧' =
      F'.mapDerivedCategoryFactors.inv.app A ≫ F'.mapDerivedCategory.map ζ ≫
        (F'.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
          (F'.mapDerivedCategoryFactors.hom.app A)⟦(2 : ℤ)⟧') :
    ∃ δ : (rightDerived F).obj ((DerivedCategory.Q.obj A)⟦(-2 : ℤ)⟧) ⟶ DerivedCategory.Q.obj B,
      δ ≫ DerivedCategory.Q.map κ₀ ≫
          StacksDraft.DerivedUnitSquare.unitQ F (rightDerivedUnit F) A =
        (rightDerived F).map (ζ⟦(-2 : ℤ)⟧' ≫
          (shiftFunctorCompIsoId _ (2 : ℤ) (-2) (by norm_num)).hom.app _) := by
  subst hF
  obtain rfl := eq_of_heq hκ
  exact exists_comp_unitQ_eq_map F' ζ κ₀' D₀ h

end StacksDraft.ExactFunctorShiftedLift

end
