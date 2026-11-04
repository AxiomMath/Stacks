module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TopTruncationExt
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial

/-!
# Classes in `Ext` through a triangulated functor which is exact in degree zero

Let `Φ : D⁺(𝒜) ⥤ D(ℬ)` be a triangulated functor carrying every `X[0]` to an object living in
degree `0` only, so that `G ≅ H⁰(Φ((-)[0]))` is an exact functor `𝒜 ⥤ ℬ` (for instance `Φ` the
right derived functor of an exact functor `G`). For a class `e ∈ Ext^m_𝒜(X, Y)` and an object
`Λ` of `ℬ`, some morphism `φ : Λ[0] ⟶ Φ(X[0])` has `Φ(e) ∘ φ ≠ 0` exactly when some
`z ∈ Ext⁰_ℬ(Λ, G X)` has `G(e) ∘ z ≠ 0`
(`Stacks.TopTruncationExt.exists_comp_map_extPlus_ne_zero_iff`).

This is the case `n = 0` of `Stacks.TopTruncationExt.map_comp_topProj`, where the top-degree
projections `Φ(X[0]) ⟶ H⁰(Φ(X[0]))[0]` are isomorphisms
(`Stacks.TopTruncationExt.isIso_topProj_zero`). It reads the class of a point in top compactly
supported cohomology, an `Ext` class on a compactification, as a morphism in the bounded below
derived category of the base field (proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.TopTruncationExt.isIso_topProj_zero`.
* `Stacks.TopTruncationExt.exists_comp_map_extPlus_ne_zero_iff`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Stacks.TopTruncationExt

universe w w'

/-- **The top-degree projection of an object living in degree `0` only is an isomorphism.** -/
theorem isIso_topProj_zero {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (K : DerivedCategory B) (hK : K.IsLE 0) [K.IsGE 0] : IsIso (topProj K 0 hK) := by
  rw [DerivedCategory.isIso_iff]
  intro i
  have : K.IsLE 0 := hK
  have : (((DerivedCategory.singleFunctor B 0).obj
      ((DerivedCategory.homologyFunctor B 0).obj K))⟦(-0 : ℤ)⟧).IsLE 0 :=
    DerivedCategory.TStructure.t.isLE_shift _ 0 (-0) 0 (by simp)
  rcases lt_trichotomy i 0 with h | rfl | h
  · exact (DerivedCategory.isZero_of_isGE K 0 i h).isIso
      (DerivedCategory.isZero_of_isGE _ 0 i h) _
  · have : IsIso ((DerivedCategory.homologyFunctor B 0).map (topProj K 0 hK) ≫
        (singleShiftHomologyIso 0).hom.app _) := by
      rw [homologyFunctor_map_topProj K 0 hK]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((singleShiftHomologyIso 0).hom.app _)
  · exact (DerivedCategory.isZero_of_isLE K 0 i h).isIso
      (DerivedCategory.isZero_of_isLE _ 0 i h) _

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] [HasExt.{w} A]
  [EnoughInjectives A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B] [HasExt.{w'} B]
  (Φ : DerivedCategory.Plus A ⥤ DerivedCategory B) [Φ.CommShift ℤ] [Φ.IsTriangulated]
  (hΦ : ∀ X : A, (Φ.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)).IsLE 0)
  (hΦ' : ∀ X : A, (Φ.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)).IsGE 0)
  (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (η : topHomology Φ 0 ≅ G)

include hΦ hΦ' η in
/-- **A class through `Φ` is nonzero against some test morphism exactly when its image under
`G ≅ H⁰(Φ((-)[0]))` is nonzero against some class of degree `0`.** For `e ∈ Ext^m_𝒜(X, Y)` and
`Λ` in `ℬ`: some `φ : Λ[0] ⟶ Φ(X[0])` has `Φ(e) ∘ φ ≠ 0` if and only if some
`z ∈ Ext⁰_ℬ(Λ, G X)` has `G(e) ∘ z ≠ 0`. -/
theorem exists_comp_map_extPlus_ne_zero_iff (Λ : B) {X Y : A} {m : ℕ} (e : Ext.{w} X Y m) :
    (∃ φ : (DerivedCategory.singleFunctor B 0).obj Λ ⟶
        Φ.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X),
      φ ≫ (extPlus e).map Φ ≠ 0) ↔
      ∃ z : Ext.{w'} Λ (G.obj X) 0, z.comp (e.mapExactFunctor G) (zero_add m) ≠ 0 := by
  have : PreservesFiniteLimits (topHomology Φ 0) := preservesFiniteLimits_of_natIso η.symm
  have : PreservesFiniteColimits (topHomology Φ 0) := preservesFiniteColimits_of_natIso η.symm
  have := hΦ' X
  have := hΦ' Y
  have := isIso_topProj_zero _ (hΦ X)
  have := isIso_topProj_zero _ (hΦ Y)
  have key := map_comp_topProj Φ 0 hΦ e (m : ℤ) (show -0 + (m : ℤ) = m by simp)
    (show (m : ℤ) + -0 = m by simp)
  rw [zero_mul, Int.negOnePow_zero, one_smul] at key
  have hcomp : ∀ φ : (DerivedCategory.singleFunctor B 0).obj Λ ⟶
      Φ.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X),
      φ ≫ ((extPlus e).map Φ).comp (topProj _ 0 (hΦ Y)) (show -0 + (m : ℤ) = m by simp) =
        ShiftedHom.comp (a := (-0 : ℤ)) (φ ≫ topProj _ 0 (hΦ X))
          (e.mapExactFunctor (topHomology Φ 0) : Ext.{w'} _ _ m).hom
            (show (m : ℤ) + -0 = m by simp) := by
    intro φ
    rw [key]
    simp only [ShiftedHom.comp, Category.assoc]
  have hzero : ∀ φ : (DerivedCategory.singleFunctor B 0).obj Λ ⟶
      Φ.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X),
      φ ≫ (extPlus e).map Φ = 0 ↔
        φ ≫ ((extPlus e).map Φ).comp (topProj _ 0 (hΦ Y)) (show -0 + (m : ℤ) = m by simp) =
          0 := by
    intro φ
    simp only [ShiftedHom.comp, ← Category.assoc]
    constructor
    · intro h; rw [h]; simp
    · intro h
      have : IsIso (((topProj _ 0 (hΦ Y))⟦(m : ℤ)⟧') ≫
          (shiftFunctorAdd' (DerivedCategory B) (-0) (m : ℤ) (m : ℤ) (by simp)).inv.app _) :=
        inferInstance
      rw [Category.assoc] at h
      exact (cancel_mono _).1 (h.trans (zero_comp).symm)
  have hproj : ∀ φ : (DerivedCategory.singleFunctor B 0).obj Λ ⟶
      Φ.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X),
      ∃ ψ : Λ ⟶ (topHomology Φ 0).obj X, φ ≫ topProj _ 0 (hΦ X) =
        ShiftedHom.mk₀ (-0 : ℤ) (by simp) ((DerivedCategory.singleFunctor B 0).map ψ) := by
    intro φ
    refine ⟨(DerivedCategory.singleFunctor B 0).preimage
      ((ShiftedHom.homEquiv (-0 : ℤ) (by simp)).symm (φ ≫ topProj _ 0 (hΦ X))), ?_⟩
    rw [Functor.map_preimage]
    exact ((ShiftedHom.homEquiv (-0 : ℤ) (by simp)).apply_symm_apply _).symm
  have hmk : ∀ ψ : Λ ⟶ (topHomology Φ 0).obj X,
      (ShiftedHom.mk₀ (-0 : ℤ) (by simp) ((DerivedCategory.singleFunctor B 0).map ψ)).comp
          (e.mapExactFunctor (topHomology Φ 0) : Ext.{w'} _ _ m).hom
            (show (m : ℤ) + -0 = m by simp) =
        ((Ext.mk₀ ψ).comp (e.mapExactFunctor (topHomology Φ 0) : Ext.{w'} _ _ m)
          (zero_add m)).hom := by
    intro ψ
    rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp, ShiftedHom.mk₀_comp]
  have hη : ∀ z : Ext.{w'} Λ ((topHomology Φ 0).obj X) 0,
      z.comp (e.mapExactFunctor (topHomology Φ 0) : Ext.{w'} _ _ m) (zero_add m) = 0 ↔
        (z.comp (Ext.mk₀ (η.hom.app X)) (add_zero 0)).comp (e.mapExactFunctor G)
          (zero_add m) = 0 := by
    intro z
    rw [Ext.comp_assoc_of_second_deg_zero,
      Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor η.hom X m e,
      ← Ext.comp_assoc_of_third_deg_zero]
    constructor
    · intro h; rw [h, Ext.zero_comp]
    · intro h
      have h' := congrArg (fun x => x.comp (Ext.mk₀ (η.inv.app Y)) (add_zero m)) h
      simp only [Ext.zero_comp] at h'
      rwa [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.hom_inv_id_app,
        Ext.comp_mk₀_id] at h'
  constructor
  · rintro ⟨φ, hφ⟩
    obtain ⟨ψ, hψ⟩ := hproj φ
    refine ⟨(Ext.mk₀ ψ).comp (Ext.mk₀ (η.hom.app X)) (add_zero 0), fun h => hφ ?_⟩
    rw [hzero, hcomp, hψ, hmk, (hη _).2 h, Ext.zero_hom]
  · rintro ⟨z, hz⟩
    obtain ⟨ψ, hψ⟩ := (Ext.mk₀_bijective _ _).surjective
      (z.comp (Ext.mk₀ (η.inv.app X)) (add_zero 0))
    refine ⟨ShiftedHom.mk₀ (-0 : ℤ) (by simp) ((DerivedCategory.singleFunctor B 0).map ψ) ≫
      inv (topProj _ 0 (hΦ X)), fun h => hz ?_⟩
    rw [hzero, hcomp, Category.assoc, IsIso.inv_hom_id, Category.comp_id, hmk] at h
    have h' := (hη _).1 (Ext.ext (h.trans (Ext.zero_hom _ _ _).symm))
    rwa [hψ, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.inv_hom_id_app,
      Ext.comp_mk₀_id] at h'

end Stacks.TopTruncationExt

end
