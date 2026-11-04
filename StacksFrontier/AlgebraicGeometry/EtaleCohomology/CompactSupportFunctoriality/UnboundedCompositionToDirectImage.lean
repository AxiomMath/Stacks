module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportFunctoriality.UnboundedExtensionByZeroCompToDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportFunctoriality.OpenImmersionDirectImageToDirectImage
import StacksCore.Tactic.StacksAttribute

/-!
# The map `Rf_! ⟶ Rf_*` and composition, on `D(X_étale, Λ)`

The map `Rf_! ⟶ Rf_*` of [Stacks, Tag 0H6X] on `D(X_étale, Λ)` for a torsion ring `Λ`
(`Stacks.EtaleCohomology.derivedLowerShriekUnboundedToDirectImage`) is compatible with the
isomorphism `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` of [Stacks, Tag 0F7J]
(`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso`) and the composition of direct
images: compatibility (1) of the remark, whose proof the source omits.

The input is that the open immersion case `Rf̄_* ∘ b_! ≅ i_! ∘ Rf'_*` of [Stacks, Tag 0F7B] on
unbounded derived categories carries `Rb_! ⟶ Rb_*` to `Ri_! ⟶ Ri_*`. Both sides are right derived
functors of `i_! ∘ f'_* ≅ f̄_* ∘ b_!`, so this is the corresponding statement on sheaves,
`Stacks.EtaleCohomology.etaleModuleDirectImageExtensionByZeroIso_hom_comp_toDirectImage`.

## Main results

* `etaleModuleExtensionByZeroDirectImageUnboundedIso_hom_comp_toDirectImage`:
  the open immersion case of [Stacks, Tag 0F7B] on `D(P_étale, Λ)` against `Rj_! ⟶ Rj_*`.

## References

* [Stacks Project, Tag 0H6X](https://stacks.math.columbia.edu/tag/0H6X)
* [Stacks Project, Tag 0F7J](https://stacks.math.columbia.edu/tag/0F7J)
* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### An abstract rearrangement -/

section Algebra

/-- The assembly of `etaleModuleExtensionByZeroDirectImageUnboundedIso_hom_comp_toDirectImage`,
stated on variables. -/
private theorem unbounded_chain {C D : Type*} [Category* C] [Category* D] (Q : C ⥤ D)
    {k₀ k₁ k₂ k₃ k₄ k₅ k₆ : C} {e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ : D}
    (un' : Q.obj k₀ ⟶ e₁) (β : e₁ ⟶ e₂) (εi : e₂ ⟶ e₃) (lf : e₃ ⟶ e₄) (uF : Q.obj k₀ ⟶ e₂)
    (r₁ : k₀ ⟶ k₁) (fi : Q.obj k₁ ⟶ e₅) (Ei : e₅ ⟶ e₂) (εi' : e₅ ⟶ e₆) (Ri : e₆ ⟶ e₃)
    (qε : k₁ ⟶ k₂) (ui : Q.obj k₂ ⟶ e₆) (cf : k₂ ⟶ k₃) (uh : Q.obj k₃ ⟶ e₄)
    (ι : k₀ ⟶ k₄) (r₂ : k₄ ⟶ k₅) (ufb : Q.obj k₅ ⟶ e₇) (Rfac : e₇ ⟶ e₁) (Rε : e₁ ⟶ e₈)
    (lb : e₈ ⟶ e₄) (fεb : k₅ ⟶ k₆) (cb : k₆ ⟶ k₃) (Y : e₇ ⟶ e₈) (εq : Q.obj k₅ ⟶ Q.obj k₆)
    (hβ : un' ≫ β = uF) (hu : uF = Q.map r₁ ≫ fi ≫ Ei) (hn : Ei ≫ εi = εi' ≫ Ri)
    (hf : fi ≫ εi' = Q.map qε ≫ ui) (hL : ui ≫ Ri ≫ lf = Q.map cf ≫ uh)
    (hu' : un' = Q.map ι ≫ Q.map r₂ ≫ ufb ≫ Rfac) (hRb : Rfac ≫ Rε = Y)
    (hY : ufb ≫ Y ≫ lb = εq ≫ Q.map cb ≫ uh) (hεq : εq = Q.map fεb)
    (hdeg : ι ≫ r₂ ≫ fεb ≫ cb = r₁ ≫ qε ≫ cf) :
    un' ≫ β ≫ εi ≫ lf = un' ≫ Rε ≫ lb := by
  have l : un' ≫ β ≫ εi ≫ lf = Q.map (r₁ ≫ qε ≫ cf) ≫ uh := by
    rw [reassoc_of% hβ, hu, Category.assoc, Category.assoc, reassoc_of% hn, reassoc_of% hf, hL]
    simp only [Functor.map_comp, Category.assoc]
  have r : un' ≫ Rε ≫ lb = Q.map (ι ≫ r₂ ≫ fεb ≫ cb) ≫ uh := by
    rw [hu', Category.assoc, Category.assoc, Category.assoc, reassoc_of% hRb, hY, hεq]
    simp only [Functor.map_comp, Category.assoc]
  rw [l, r, hdeg]

/-- Composing a naturality square with a factorization, stated on variables. -/
private theorem unbounded_tail_chain {D : Type*} [Category* D] {a b c d e f g' : D}
    (ufb : a ⟶ b) (Y : b ⟶ c) (lb : c ⟶ d) (R₁ : b ⟶ e) (R₂ : e ⟶ c) (εq : a ⟶ f)
    (ufb' : f ⟶ e) (cq : f ⟶ g') (uh : g' ⟶ d) (hY : Y = R₁ ≫ R₂)
    (hn : ufb ≫ R₁ = εq ≫ ufb') (hL : ufb' ≫ R₂ ≫ lb = cq ≫ uh) :
    ufb ≫ Y ≫ lb = εq ≫ cq ≫ uh := by
  rw [hY, Category.assoc, reassoc_of% hn, hL]

end Algebra

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ] (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0)

/-! ### The open immersion case of [Stacks, Tag 0F7B] on `D(P_étale, Λ)` against `Rj_! ⟶ Rj_*` -/

section OpenBaseChange

variable {T Ub P Y : Scheme.{u}} (fb : T ⟶ Ub) [IsProper fb] (i : Y ⟶ Ub) [IsOpenImmersion i]
  (b : P ⟶ T) [IsOpenImmersion b] (f' : P ⟶ Y) (sq : IsPullback b f' fb i)

include hΛ in
/-- **The open immersion case of [Stacks, Tag 0F7B] on `D(P_étale, Λ)` is compatible with
`Rj_! ⟶ Rj_*`**, for a torsion ring `Λ`: `Rf̄_* b_! ≅ i_! Rf'_*` followed by `i_! ⟶ Ri_*` at
`Rf'_*` and by `Ri_* Rf'_* ≅ R(f' ≫ i)_*` is `Rf̄_*` of `b_! ⟶ Rb_*` followed by
`Rf̄_* Rb_* ≅ R(f' ≫ i)_*`. Both sides are maps out of a right derived functor of
`f̄_* ∘ b_!`, so this is the statement on sheaves
`etaleModuleDirectImageExtensionByZeroIso_hom_comp_toDirectImage`. -/
theorem etaleModuleExtensionByZeroDirectImageUnboundedIso_hom_comp_toDirectImage
    [CompactSpace Ub] :
    (etaleModuleExtensionByZeroDirectImageUnboundedIso Λ hΛ fb i b f' sq).hom ≫
        Functor.whiskerLeft (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f')
          (etaleModuleExtensionByZeroToDirectImageUnbounded Λ i) ≫
        (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ f' i (f' ≫ i) rfl).inv =
      Functor.whiskerRight (etaleModuleExtensionByZeroToDirectImageUnbounded Λ b)
          (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb) ≫
        (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ b fb (f' ≫ i) sq.w.symm).inv := by
  have := isRightDerivedFunctor_directImageExtensionByZeroUnboundedUnit' Λ hΛ fb i b f' sq
  refine Functor.rightDerived_ext _ (directImageExtensionByZeroUnboundedUnit' Λ hΛ fb i b f' sq)
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ _ _ (NatTrans.ext (funext fun K => ?_))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  let Ff := (etaleModuleDirectImage.{u, 0} Λ f').mapHomologicalComplex (ComplexShape.up ℤ)
  let Eb := (etaleModuleExtensionByZero.{u, 0} Λ b).mapHomologicalComplex (ComplexShape.up ℤ)
  let Rfb := etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ fb
  let uf := (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ f').app K
  let ub := (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ b).app K
  let εbK := (NatTrans.mapHomologicalComplex (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ b)
    (ComplexShape.up ℤ)).app K
  have hβ : (directImageExtensionByZeroUnboundedUnit' Λ hΛ fb i b f' sq).app K ≫
      (etaleModuleExtensionByZeroDirectImageUnboundedIso Λ hΛ fb i b f' sq).hom.app
        (DerivedCategory.Q.obj K) =
      (directImageExtensionByZeroUnboundedUnit Λ i f').app K := by
    simp only [etaleModuleExtensionByZeroDirectImageUnboundedIso, Functor.rightDerivedNatIso_hom,
      Functor.rightDerivedNatTrans_app, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  have hu : (directImageExtensionByZeroUnboundedUnit Λ i f').app K =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleExtensionByZero.{u, 0} Λ i))
          (ComplexShape.up ℤ)).inv.app K) ≫
        (etaleModuleExtensionByZero.{u, 0} Λ i).mapDerivedCategoryFactors.inv.app (Ff.obj K) ≫
        (etaleModuleExtensionByZero.{u, 0} Λ i).mapDerivedCategory.map uf := by
    simp only [directImageExtensionByZeroUnboundedUnit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id]
    rfl
  have hu'₁ := NatTrans.congr_app (show directImageExtensionByZeroUnboundedUnit' Λ hΛ fb i b f' sq =
      Functor.whiskerRight (NatIso.mapHomologicalComplex
          (etaleModuleDirectImageExtensionByZeroIso Λ hΛ fb i b f' sq) (ComplexShape.up ℤ)).hom
          DerivedCategory.Q ≫
        extensionByZeroDirectImageUnboundedUnit Λ fb b from rfl) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hu'₁
  have hu'₂ : (extensionByZeroDirectImageUnboundedUnit Λ fb b).app K =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDirectImage.{u, 0} Λ fb))
          (ComplexShape.up ℤ)).inv.app K) ≫
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ fb).app (Eb.obj K) ≫
        Rfb.map ((etaleModuleExtensionByZero.{u, 0} Λ b).mapDerivedCategoryFactors.inv.app K) := by
    simp only [extensionByZeroDirectImageUnboundedUnit,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id]
    rfl
  have hu' := hu'₁.trans (whisker_eq _ hu'₂)
  have hLf := conj_inv_chain _ _ _ _ _ _ _
    (etaleModuleDerivedDirectImageUnboundedLerayIso_hom_fac Λ f' i (f' ≫ i) rfl K)
    ((Functor.map_comp _ _ _).symm.trans ((congrArg DerivedCategory.Q.map
      (Iso.hom_inv_id_app _ K)).trans (CategoryTheory.Functor.map_id _ _)))
    (Iso.hom_inv_id_app _ _)
  have hLb := conj_inv_chain _ _ _ _ _ _ _
    (etaleModuleDerivedDirectImageUnboundedLerayIso_hom_fac Λ b fb (f' ≫ i) sq.w.symm K)
    ((Functor.map_comp _ _ _).symm.trans ((congrArg DerivedCategory.Q.map
      (Iso.hom_inv_id_app _ K)).trans (CategoryTheory.Functor.map_id _ _)))
    (Iso.hom_inv_id_app _ _)
  have hnfb := (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ fb).naturality εbK
  have hY : (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ fb).app (Eb.obj K) ≫
      Rfb.map (DerivedCategory.Q.map εbK ≫ ub) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ b fb (f' ≫ i) sq.w.symm).inv.app
        (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map (((etaleModuleDirectImage.{u, 0} Λ fb).mapHomologicalComplex
          (ComplexShape.up ℤ)).map εbK) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (etaleModuleDirectImageComp.{u, 0} Λ b fb (f' ≫ i) sq.w.symm)
            (ComplexShape.up ℤ)).hom.app K) ≫
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ (f' ≫ i)).app K :=
    unbounded_tail_chain _ _ _ (Rfb.map (DerivedCategory.Q.map εbK)) (Rfb.map ub) _
      ((etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ fb).app
        (((etaleModuleDirectImage.{u, 0} Λ b).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
      _ _ (Functor.map_comp _ _ _) hnfb.symm hLb.symm
  have hdeg : (NatIso.mapHomologicalComplex
          (etaleModuleDirectImageExtensionByZeroIso Λ hΛ fb i b f' sq)
            (ComplexShape.up ℤ)).hom.app K ≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDirectImage.{u, 0} Λ fb))
          (ComplexShape.up ℤ)).inv.app K ≫
        ((etaleModuleDirectImage.{u, 0} Λ fb).mapHomologicalComplex (ComplexShape.up ℤ)).map εbK ≫
        (Functor.mapHomologicalComplexCompIso
          (etaleModuleDirectImageComp.{u, 0} Λ b fb (f' ≫ i) sq.w.symm)
            (ComplexShape.up ℤ)).hom.app K =
      (Functor.mapHomologicalComplexCompIso
          (Iso.refl (etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleExtensionByZero.{u, 0} Λ i))
          (ComplexShape.up ℤ)).inv.app K ≫
        (NatTrans.mapHomologicalComplex (etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ i)
          (ComplexShape.up ℤ)).app (Ff.obj K) ≫
        (Functor.mapHomologicalComplexCompIso
          (etaleModuleDirectImageComp.{u, 0} Λ f' i (f' ≫ i) rfl)
            (ComplexShape.up ℤ)).hom.app K := by
    refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
    simp only [HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_hom_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f,
      Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f, Iso.refl_inv,
      NatTrans.id_app, Category.id_comp, εbK, Ff]
    exact etaleModuleDirectImageExtensionByZeroIso_hom_comp_toDirectImage Λ fb i b f' sq hΛ (K.X n)
  exact unbounded_chain DerivedCategory.Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hβ hu ((etaleModuleExtensionByZeroToDirectImageUnbounded Λ i).naturality uf)
    (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded_app_factors Λ i (Ff.obj K))
    hLf.symm hu'
    ((Functor.map_comp _ _ _).symm.trans (congrArg Rfb.map
      (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded_app_factors Λ b K)))
    hY rfl hdeg


end OpenBaseChange

end Stacks.EtaleCohomology

end
