module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.TwistSections
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineVeroneseNaturality
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineQuadrupleRoundTrip
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleFunctorLaws

/-!
# The inverse image of a tensor power in degree one

For `q : X₁ ⟶ X`, an invertible `ℒ` on `X` and `ε : q^*ℒ ≅ ℒ₁`, the comparison
`q^*(ℒ^{⊗ n}) ⟶ ℒ₁^{⊗ n}` of [Stacks, Tag 01CU] (`TwistSections.polPow`) is, in degree one and
through the identifications `ℒ^{⊗ 1} ≅ ℒ`, the isomorphism `ε` itself.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveDeformation.TwistSections.pullback_kappa_comp`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation.TwistSections

-- `CategoryTheory.catToReflQuiver` offers a second route from `Category` to `Quiver`; see
-- `Stacks.AlgebraicGeometry.ProjectiveDeformation.TwistSections`.
attribute [-instance] CategoryTheory.catToReflQuiver

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-- `ℒ^{⊗ 1} ≅ ℒ` of [Stacks, Tag 01CU], read from the comparison with the iterated tensor
powers and the left unitor. -/
theorem kappa_eq {T : Scheme.{u}} (M : T.Modules) [Stacks.Ample.IsInvertibleModule T M] :
    (powCompare M 1).inv ≫ (λ_ M).hom =
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.onePowIso M).hom := by
  have h : (powCompare M 1).hom ≫ (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.onePowIso M).hom =
      (λ_ M).hom := Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.powCompare_one_comp_onePowIso M
  exact (Iso.inv_comp_eq _).mpr h.symm

/-- The chase behind `pullbackIntPowIso_one_comp_onePowIso`, with every object free. -/
theorem abs_chase {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {A B L : C} {E E' : D}
    (pc : A ≅ B) (lam : A ⟶ L) (N : F.obj A ⟶ E) (pc' : E ≅ E') (lam' : E ⟶ F.obj L)
    (pIP : F.obj B ⟶ E') (hd : N ≫ pc'.hom = F.map pc.hom ≫ pIP) (hc : N ≫ lam' = F.map lam) :
    pIP ≫ pc'.inv ≫ lam' = F.map (pc.inv ≫ lam) := by
  have hp : pIP = F.map pc.inv ≫ N ≫ pc'.hom := by
    rw [hd, ← Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id, Category.id_comp]
  rw [hp, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, hc, F.map_comp]

variable {X X₁ : Scheme.{u}} (q : X₁ ⟶ X) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **The comparison of [Stacks, Tag 01CU] with inverse images in degree one** is the pullback of
`ℒ^{⊗ 1} ≅ ℒ`. -/
theorem pullbackIntPowIso_one_comp_onePowIso :
    haveI :=
      Stacks.AlgebraicGeometry.SectionRingBaseChange.isInvertible_tensorPower_of_isInvertibleModule
        X L
    (Stacks.TensorPowerPullback.pullbackIntPowIso q.toLRSHom.toShHom L 1).hom ≫
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.onePowIso
          ((Scheme.Modules.pullback q).obj L)).hom =
      (Scheme.Modules.pullback q).map
        (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.onePowIso L).hom := by
  have hd := Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.pullPowCompare_eq_powComparePull q L 1
  have hc := ProjTripleFunctorLaws.pullbackNatTensorPowIso_inv_one_comp_unitorPow q L
  unfold Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.pullPowCompare
    Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.powComparePull at hd
  rw [← kappa_eq, ← kappa_eq]
  exact abs_chase (Scheme.Modules.pullback q) (powCompare L 1) (λ_ L).hom
    (Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackNatTensorPowIso q L 1).inv
    (powCompare ((Scheme.Modules.pullback q).obj L) 1) (λ_ ((Scheme.Modules.pullback q).obj L)).hom
    _ hd hc

/-- A chase in a category, with every object free. -/
theorem abs_chase₂ {C : Type*} [Category C] {A B E F G : C} (pIP : A ⟶ B) (o' : B ⟶ E)
    (qo : A ⟶ E) (ε : E ⟶ G) (cI : B ⟶ F) (o₁ : F ⟶ G) (h1 : pIP ≫ o' = qo)
    (h2 : o' ≫ ε = cI ≫ o₁) : qo ≫ ε = (pIP ≫ cI) ≫ o₁ := by
  rw [← h1, Category.assoc, h2, Category.assoc]

variable (L₁ : X₁.Modules) [Stacks.Ample.IsInvertibleModule X₁ L₁]
  (ε : (Scheme.Modules.pullback q).obj L ≅ L₁)

/-- **In degree one the comparison `polPow` is `ε`**, through `ℒ^{⊗ 1} ≅ ℒ`. -/
theorem pullback_kappa_comp :
    (Scheme.Modules.pullback q).map ((powCompare L 1).inv ≫ (λ_ L).hom) ≫ ε.hom =
      polPow L q L₁ ε 1 ≫ (powCompare L₁ 1).inv ≫ (λ_ L₁).hom := by
  rw [kappa_eq L]
  refine Eq.trans ?_ (congrArg (fun z => polPow L q L₁ ε 1 ≫ z) (kappa_eq L₁)).symm
  have := SectionRingBaseChange.isInvertible_tensorPower_of_isInvertibleModule X L
  have := SectionRingBaseChange.isInvertible_tensorPower_of_isInvertibleModule X₁ L₁
  have := SectionRingBaseChange.isInvertible_tensorPower_of_isInvertibleModule X₁
    ((Scheme.Modules.pullback q).obj L)
  refine Eq.trans ?_ (Category.assoc _ _ _)
  exact abs_chase₂ (Stacks.TensorPowerPullback.pullbackIntPowIso q.toLRSHom.toShHom L 1).hom
    (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.onePowIso
      ((Scheme.Modules.pullback q).obj L)).hom
    _ ε.hom (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso ε 1).hom
    (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.onePowIso L₁).hom
    (pullbackIntPowIso_one_comp_onePowIso q L)
    (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso_oneIso ε)

end Stacks.AlgebraicGeometry.ProjectiveDeformation.TwistSections

end
