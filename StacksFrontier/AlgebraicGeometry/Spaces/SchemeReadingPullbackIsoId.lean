module

public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeReadingOfModule
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackIdUnitLaw

/-!
# The comparison of the readings along an identity is the unitor

Let `X` be an algebraic space, `ℰ` a quasi-coherent `𝒪_X`-module and `ψ : T ⟶ X` a morphism
from an object of the big fppf site. The comparison
`AlgebraicGeometry.Space.schemeReadingPullbackIso` of the readings along the identity of `T`,
`(𝟙 T)^* ℰ_T ≅ ℰ_T`, is the identification `(𝟙 T)^* ≅ 𝟭` of
`AlgebraicGeometry.Scheme.Modules.pullbackId`.

The proof uses only the composition law of the comparisons
(`AlgebraicGeometry.Space.schemeReadingPullbackIso_comp`) at the pair `(𝟙 T, 𝟙 T)` and the unit
law of the Zariski inverse image (`AlgebraicGeometry.Scheme.Modules.pullbackComp_id_id_hom_app`):
both `φ` (the comparison) and `λ` (the unitor) satisfy `(𝟙)^*x ≫ x = μ ≫ x`, which forces
`(𝟙)^*φ = (𝟙)^*λ`, and `(𝟙)^*` is isomorphic to the identity functor.

## Main results

* `AlgebraicGeometry.Space.schemeReadingPullbackIso_id_hom`: the comparison along `𝟙 T` is the
  unitor.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) (hE : E.IsQuasicoherentOnSite)

/-- The abstract shape: a morphism `φ : F a ⟶ a` with `F φ ≫ φ = F λ ≫ φ`, for a
natural isomorphism `λ : F ≅ 𝟭`, is `λ_a`. -/
private theorem eq_of_map_comp_eq_map_comp {C₀ : Type*} [Category C₀] (F : C₀ ⥤ C₀)
    (lam : F ≅ 𝟭 C₀) {a : C₀} (φ : F.obj a ⟶ a) [IsIso φ]
    (h : F.map φ ≫ φ = F.map (lam.hom.app a) ≫ φ) : φ = lam.hom.app a := by
  have h' : F.map φ = F.map (lam.hom.app a) := (cancel_mono φ).1 h
  have n₁ := lam.hom.naturality φ
  have n₂ := lam.hom.naturality (lam.hom.app a)
  simp only [Functor.id_map] at n₁ n₂
  rw [h'] at n₁
  exact (cancel_epi (lam.hom.app (F.obj a))).1 (n₁.symm.trans n₂)

/-- **The comparison of the readings along the identity is the unitor**: for `ψ : T ⟶ X`, the
comparison `(𝟙 T)^* ℰ_T ≅ ℰ_T` of `AlgebraicGeometry.Space.schemeReadingPullbackIso` is the
component at `ℰ_T` of `AlgebraicGeometry.Scheme.Modules.pullbackId`. -/
theorem schemeReadingPullbackIso_id_hom {T : BigFppfOver B S hS}
    {ψ : representedAlgebraicSpace B S hS T ⟶ X}
    (w : representedSpaceMap B S hS (𝟙 T) ≫ ψ = ψ) :
    (schemeReadingPullbackIso E hE (𝟙 T) w).hom =
      (Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj T)).hom.app
        (schemeReading E ψ) := by
  have w'' : representedSpaceMap B S hS (𝟙 T ≫ 𝟙 T) ≫ ψ = ψ := by
    rw [Category.id_comp]; exact w
  have c := congrArg Iso.hom (schemeReadingPullbackIso_comp E hE (𝟙 T) (𝟙 T) w w w'')
  have hc := pullbackCongr_hom_app_schemeReadingPullbackIso E hE (Category.id_comp (𝟙 T)) w'' w
  have hμ : (Scheme.Modules.pullbackComp
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
          (𝟙 T : T ⟶ T).left)
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
          (𝟙 T : T ⟶ T).left)).hom.app (schemeReading E ψ) =
      (Scheme.Modules.pullback (𝟙 ((BigFppfOver.toScheme B S hS).obj T))).map
        ((Scheme.Modules.pullbackId ((BigFppfOver.toScheme B S hS).obj T)).hom.app
          (schemeReading E ψ)) :=
    Scheme.Modules.pullbackComp_id_id_hom_app _ _
  have hκ : (Scheme.Modules.pullbackCongr
        (congrArg (fun x : T ⟶ T =>
          _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) x.left)
          (Category.id_comp (𝟙 T)))).hom.app (schemeReading E ψ) = 𝟙 _ := rfl
  have hκφ : (Scheme.Modules.pullbackCongr
        (congrArg (fun x : T ⟶ T =>
          _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) x.left)
          (Category.id_comp (𝟙 T)))).hom.app (schemeReading E ψ) ≫
        (schemeReadingPullbackIso E hE (𝟙 T) w).hom = (schemeReadingPullbackIso E hE (𝟙 T) w).hom :=
    (congrArg (· ≫ (schemeReadingPullbackIso E hE (𝟙 T) w).hom) hκ).trans (Category.id_comp _)
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at c
  rw [← hc, hκφ, hμ] at c
  exact eq_of_map_comp_eq_map_comp (Scheme.Modules.pullback (𝟙 _))
    (Scheme.Modules.pullbackId _) _ c

end AlgebraicGeometry.Space

end
