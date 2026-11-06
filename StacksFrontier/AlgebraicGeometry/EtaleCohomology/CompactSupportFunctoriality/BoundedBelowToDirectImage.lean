module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.IndependenceCoefficientUniverse
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusNatIsoGlue
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonCoherence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BaseChangeCube
import StacksCore.Tactic.StacksAttribute

/-!
# The map `Rf_! ⟶ Rf_*` on `D⁺_tors`

Let `f : X ⟶ Y` be a finite type separated morphism of quasi-compact and quasi-separated schemes,
`j : X ⟶ X̄` a compactification of `X` over `Y` with structure morphism `f̄ : X̄ ⟶ Y`, and `Λ` a
ring. [Stacks, Tag 0H6X] constructs a map `Rf_! K ⟶ Rf_* K`, functorial in `K`: since
`Rf_! = Rf̄_* ∘ j_!` and `Rf_* = Rf̄_* ∘ Rj_*`, it is `Rf̄_*` applied to the map `j_! ⟶ Rj_*`
induced by the canonical transformation `j_! ⟶ j_*` of [Stacks, Tag 0F4L], followed by the
composition isomorphism `Rf̄_* ∘ Rj_* ≅ Rf_*` of Cohomology on Sites, Tag 0D6E.

This file constructs the map on the bounded below derived categories and proves that it does not
depend on the compactification: along a morphism of compactifications `g : j ⟶ k` the
isomorphism `Rf_!^k ≅ Rf_!^j` of [Stacks, Tag 0F7I] carries one map to the other, and hence so
does the canonical isomorphism between the functors `Rf_!` of any two compactifications, which is
computed through a compactification dominating both.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroToDirectImagePlus`: `Rj_! ⟶ Rj_*`
  on `D⁺`, induced by the map `j_! ⟶ j_*` of [Stacks, Tag 0F4L].
* `Stacks.EtaleCohomology.derivedLowerShriekToDirectImage`: **the map `Rf_! ⟶ Rf_*` of
  [Stacks, Tag 0H6X]** on `D⁺(X_étale, Λ)`.

## Main results

* `Stacks.EtaleCohomology.derivedLowerShriekHomUniv_comp_toDirectImage`: the map is carried to
  itself by the isomorphism of a morphism of compactifications.
* `Stacks.EtaleCohomology.derivedLowerShriekCompactificationIsoUniv_hom_comp_toDirectImage`:
  **the map does not depend on the compactification** ([Stacks, Tag 0H6X]).

## References

* [Stacks Project, Tag 0H6X](https://stacks.math.columbia.edu/tag/0H6X)
* [Stacks Project, Tag 0F4L](https://stacks.math.columbia.edu/tag/0F4L)
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u w

/-! ### Comparisons of cones along a cofiltered system of isomorphisms -/

namespace CategoryTheory.IsCofiltered

variable {𝒦 : Type*} [Category* 𝒦] [IsCofiltered 𝒦] {𝒟 : Type*} [Category* 𝒟] {Φ : 𝒦 → 𝒟}
  (e : ∀ {j k : 𝒦}, (j ⟶ k) → (Φ k ≅ Φ j))

/-- **The comparisons of a cofiltered system of isomorphisms respect a compatible family of maps
to a fixed object.** If `e g ≫ τ j = τ k` for every `g : j ⟶ k`, then the comparison
`Φ j ≅ Φ k` followed by `τ k` is `τ j`. -/
lemma isoSystemComparison_hom_comp {T : 𝒟} (τ : ∀ j, Φ j ⟶ T)
    (hτ : ∀ {j k : 𝒦} (g : j ⟶ k), (e g).hom ≫ τ j = τ k) (j k : 𝒦) :
    (isoSystemComparison e j k).hom ≫ τ k = τ j := by
  simp only [isoSystemComparison, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← hτ (minToRight j k), Iso.inv_hom_id_assoc, hτ]

end CategoryTheory.IsCofiltered

/-! ### Right derived functors of natural transformations on `D⁺` -/

namespace Stacks.DerivedIndexing

open CategoryTheory.Functor

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A B C : Type*} [Category* A] [Category* B] [Category* C] [Abelian A] [Abelian B]
  [Abelian C] [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [EnoughInjectives A]

/-- The right derived functor of a composite of natural transformations is the composite. -/
theorem rightDerivedFunctorPlusNatTrans_comp {F G H : A ⥤ B} [F.Additive] [G.Additive]
    [H.Additive] (α : F ⟶ G) (β : G ⟶ H) :
    rightDerivedFunctorPlusNatTrans (α ≫ β) =
      rightDerivedFunctorPlusNatTrans α ≫ rightDerivedFunctorPlusNatTrans β := by
  unfold rightDerivedFunctorPlusNatTrans
  rw [Functor.rightDerivedNatTrans_comp]
  congr 1
  ext K
  simp [mapHomotopyCategoryPlusNatTrans_comp_app]

/-- The invariance comparison of an isomorphism is the right derived functor of its forward
half. -/
theorem rightDerivedFunctorPlusNatIso_hom_eq {F G : A ⥤ B} [F.Additive] [G.Additive]
    (e : F ≅ G) :
    (rightDerivedFunctorPlusNatIso e).hom = rightDerivedFunctorPlusNatTrans e.hom := by
  apply Functor.rightDerived_ext F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso A)
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [rightDerivedFunctorPlusNatIso_hom_fac_app, rightDerivedFunctorPlusNatTrans_app]
  congr 2

/-- The invariance comparison of an isomorphism, backwards, is the right derived functor of its
inverse half. -/
theorem rightDerivedFunctorPlusNatIso_inv_eq {F G : A ⥤ B} [F.Additive] [G.Additive]
    (e : F ≅ G) :
    (rightDerivedFunctorPlusNatIso e).inv = rightDerivedFunctorPlusNatTrans e.inv := by
  have h := rightDerivedFunctorPlusNatIso_hom_eq e.symm
  rwa [rightDerivedFunctorPlusNatIso_symm] at h

variable [EnoughInjectives B]

/-- The unit followed by `Rγ` and the comparison for `(F₁, H₁)`, for `γ : F ⋙ H ⟶ F₁ ⋙ H₁`. -/
private theorem unit_comp_natTrans_comp_rightDerivedFunctorPlusComp_app {F F₁ : A ⥤ B}
    {H H₁ : B ⥤ C} [F.Additive] [F₁.Additive] [H.Additive] [H₁.Additive]
    (γ : F ⋙ H ⟶ F₁ ⋙ H₁) (K : HomotopyCategory.Plus A) :
    (F ⋙ H).rightDerivedFunctorPlusUnith.app K ≫
        (rightDerivedFunctorPlusNatTrans γ).app (DerivedCategory.Plus.Qh.obj K) ≫
          (rightDerivedFunctorPlusComp F₁ H₁).app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatTrans γ).app K) ≫
        H₁.rightDerivedFunctorPlusUnith.app (F₁.mapHomotopyCategoryPlus.obj K) ≫
          H₁.rightDerivedFunctorPlus.map (F₁.rightDerivedFunctorPlusUnith.app K) :=
  (Category.assoc _ _ _).symm.trans
    ((CategoryTheory.eq_whisker (rightDerivedFunctorPlusNatTrans_app γ K) _).trans
      ((Category.assoc _ _ _).trans
        (CategoryTheory.whisker_eq _ (unit_comp_rightDerivedFunctorPlusComp_app F₁ H₁ K))))

/-- **The comparison of [Stacks, Tag 05T2] is natural in its first factor**, for an arbitrary
natural transformation `α : F ⟶ F'`: `R(α H)` followed by the comparison for `(F', H)` is the
comparison for `(F, H)` followed by `RH` of `Rα`. -/
theorem rightDerivedFunctorPlusComp_natTrans_whiskerRight {F F' : A ⥤ B} [F.Additive]
    [F'.Additive] (α : F ⟶ F') (H : B ⥤ C) [H.Additive] :
    rightDerivedFunctorPlusNatTrans (Functor.whiskerRight α H) ≫
        rightDerivedFunctorPlusComp F' H =
      rightDerivedFunctorPlusComp F H ≫
        Functor.whiskerRight (rightDerivedFunctorPlusNatTrans α) H.rightDerivedFunctorPlus := by
  refine (F ⋙ H).rightDerivedFunctorPlus.rightDerived_ext (F ⋙ H).rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso A) _ _ _ (NatTrans.ext (funext fun K ↦ ?_))
  have h₃ := unit_comp_rightDerivedFunctorPlusComp_app F H K
  have h₄ := rightDerivedFunctorPlusNatTrans_app α K
  have h₅ := H.rightDerivedFunctorPlusUnith.naturality ((mapHomotopyCategoryPlusNatTrans α).app K)
  have hmap : H.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K) ≫
      H.rightDerivedFunctorPlus.map
        ((rightDerivedFunctorPlusNatTrans α).app (DerivedCategory.Plus.Qh.obj K)) =
      H.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusNatTrans α).app K)) ≫
        H.rightDerivedFunctorPlus.map (F'.rightDerivedFunctorPlusUnith.app K) := by
    rw [← Functor.map_comp, h₄, Functor.map_comp]
  have hr : (F ⋙ H).rightDerivedFunctorPlusUnith.app K ≫
      (rightDerivedFunctorPlusComp F H).app (DerivedCategory.Plus.Qh.obj K) ≫
        H.rightDerivedFunctorPlus.map
          ((rightDerivedFunctorPlusNatTrans α).app (DerivedCategory.Plus.Qh.obj K)) =
      DerivedCategory.Plus.Qh.map
          (H.mapHomotopyCategoryPlus.map ((mapHomotopyCategoryPlusNatTrans α).app K)) ≫
        H.rightDerivedFunctorPlusUnith.app (F'.mapHomotopyCategoryPlus.obj K) ≫
          H.rightDerivedFunctorPlus.map (F'.rightDerivedFunctorPlusUnith.app K) :=
    (Category.assoc _ _ _).symm.trans ((CategoryTheory.eq_whisker h₃ _).trans
      ((Category.assoc _ _ _).trans ((CategoryTheory.whisker_eq _ hmap).trans
        ((Category.assoc _ _ _).symm.trans ((CategoryTheory.eq_whisker h₅.symm _).trans
          (Category.assoc _ _ _))))))
  exact (unit_comp_natTrans_comp_rightDerivedFunctorPlusComp_app (Functor.whiskerRight α H) K).trans
    hr.symm

/-- **The comparison of [Stacks, Tag 05T2] is natural in its second factor**, for an arbitrary
natural transformation `β : H ⟶ H'`. -/
theorem rightDerivedFunctorPlusComp_natTrans_whiskerLeft (F : A ⥤ B) [F.Additive] {H H' : B ⥤ C}
    [H.Additive] [H'.Additive] (β : H ⟶ H') :
    rightDerivedFunctorPlusNatTrans (Functor.whiskerLeft F β) ≫
        rightDerivedFunctorPlusComp F H' =
      rightDerivedFunctorPlusComp F H ≫
        Functor.whiskerLeft F.rightDerivedFunctorPlus (rightDerivedFunctorPlusNatTrans β) := by
  refine (F ⋙ H).rightDerivedFunctorPlus.rightDerived_ext (F ⋙ H).rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso A) _ _ _ (NatTrans.ext (funext fun K ↦ ?_))
  have h₃ := unit_comp_rightDerivedFunctorPlusComp_app F H K
  have h₄ := rightDerivedFunctorPlusNatTrans_app β (F.mapHomotopyCategoryPlus.obj K)
  have h₅ := (rightDerivedFunctorPlusNatTrans β).naturality (F.rightDerivedFunctorPlusUnith.app K)
  have hr : (F ⋙ H).rightDerivedFunctorPlusUnith.app K ≫
      (rightDerivedFunctorPlusComp F H).app (DerivedCategory.Plus.Qh.obj K) ≫
        (rightDerivedFunctorPlusNatTrans β).app
          (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
      DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusNatTrans β).app (F.mapHomotopyCategoryPlus.obj K)) ≫
        H'.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K) ≫
          H'.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K) :=
    (Category.assoc _ _ _).symm.trans ((CategoryTheory.eq_whisker h₃ _).trans
      ((Category.assoc _ _ _).trans ((CategoryTheory.whisker_eq _ h₅).trans
        ((Category.assoc _ _ _).symm.trans ((CategoryTheory.eq_whisker h₄ _).trans
          (Category.assoc _ _ _))))))
  exact (unit_comp_natTrans_comp_rightDerivedFunctorPlusComp_app (Functor.whiskerLeft F β) K).trans
    hr.symm

end Stacks.DerivedIndexing

namespace Stacks.EtaleCohomology

attribute [-instance] etaleModules_enoughInjectives_univZero

attribute [local instance 2000] etaleModules_enoughInjectives

attribute [local instance] HasDerivedCategory.standard

open Stacks.DerivedIndexing CategoryTheory.Functor

variable (Λ : Type w) [Ring Λ]

/-! ### The map `Rj_! ⟶ Rj_*` -/

section Open

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **The map `Rj_! ⟶ Rj_*` on `D⁺`** for an open immersion `j`: the right derived functor of the
canonical map `j_! ⟶ j_*` of [Stacks, Tag 0F4L]
(`Stacks.EtaleCohomology.etaleModuleExtensionByZeroToDirectImage`). -/
def etaleModuleDerivedExtensionByZeroToDirectImagePlus :
    etaleModuleDerivedExtensionByZero.{u, w} Λ j ⟶ etaleModuleDerivedDirectImage.{u, w} Λ j :=
  rightDerivedFunctorPlusNatTrans (etaleModuleExtensionByZeroToDirectImage.{u, w} Λ j)

end Open

/-! ### The map `Rf_! ⟶ Rf_*` -/

section LowerShriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (j : CompactificationOf (Over.mk f))

/-- **The map `Rf_! ⟶ Rf_*` of [Stacks, Tag 0H6X]** on `D⁺(X_étale, Λ)`. For a finite type
separated morphism `f : X ⟶ Y` and a compactification `j : X ⟶ X̄`, `f̄ : X̄ ⟶ Y` of `X` over `Y`
it is
```
Rf_! = Rf̄_* ∘ Rj_! ⟶ Rf̄_* ∘ Rj_* ≅ R(j ≫ f̄)_* = Rf_*,
```
`Rf̄_*` of the map `Rj_! ⟶ Rj_*` induced by the canonical transformation `j_! ⟶ j_*` of
[Stacks, Tag 0F4L], followed by the composition isomorphism of derived direct images
(Cohomology on Sites, Tag 0D6E). It is natural in `K`, and restricts to `D⁺_tors(X_étale, Λ)`. -/
@[stacks 0H6X "the map Rf_! ⟶ Rf_*, functorial in K, on D⁺_tors"]
def derivedLowerShriekToDirectImage :
    derivedLowerShriek.{u, w} f j Λ ⟶ etaleModuleDerivedDirectImage.{u, w} Λ f :=
  Functor.whiskerRight (etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, w} Λ j.immersion)
      (etaleModuleDerivedDirectImage.{u, w} Λ j.toBase) ≫
    (etaleModuleDerivedDirectImageComp.{u, w} Λ j.immersion j.toBase f
      (CompactificationOf.immersion_toBase j).symm).inv

end LowerShriek

/-! ### Associativity of the composition isomorphisms -/

section Assoc

/-- The composition isomorphism of derived direct images is the composition comparison of
[Stacks, Tag 05T2] after the invariance comparison of the underived composition isomorphism, for
`Λ` in any universe. -/
lemma etaleModuleDerivedDirectImageComp_hom_eq_univ {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    (etaleModuleDerivedDirectImageComp.{u, w} Λ f g fg hfg).hom =
      (rightDerivedFunctorPlusNatIso (etaleModuleDirectImageComp.{u, w} Λ f g fg hfg)).inv ≫
        rightDerivedFunctorPlusComp _ _ := by
  dsimp only [etaleModuleDerivedDirectImageComp, rightDerivedFunctorPlusCompIsoOfIso]
  simp only [rightDerivedFunctorPlusIsoOfCompIso_eq, Iso.trans_hom, Iso.symm_hom,
    rightDerivedFunctorPlusCompIso_hom]

/-- **The composition isomorphisms of derived direct images are associative**, for `Λ` in any
universe: along `T ⟶ X ⟶ Y ⟶ Z`, taking `R(fgh)_*` apart through `R(fg)_* ⋙ Rh_*` or through
`Rf_* ⋙ R(gh)_*` gives the same isomorphism with `Rf_* ⋙ Rg_* ⋙ Rh_*`. -/
theorem etaleModuleDerivedDirectImageComp_assoc_univ {T X Y Z : Scheme.{u}} (f : T ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z) (fg : T ⟶ Y) (hfg : fg = f ≫ g) (gh : X ⟶ Z) (hgh : gh = g ≫ h)
    (fgh : T ⟶ Z) (h₁ : fgh = fg ≫ h) (h₂ : fgh = f ≫ gh) :
    (etaleModuleDerivedDirectImageComp.{u, w} Λ fg h fgh h₁).hom ≫
        Functor.whiskerRight (etaleModuleDerivedDirectImageComp.{u, w} Λ f g fg hfg).hom
          (etaleModuleDerivedDirectImage.{u, w} Λ h) =
      (etaleModuleDerivedDirectImageComp.{u, w} Λ f gh fgh h₂).hom ≫
        Functor.whiskerLeft (etaleModuleDerivedDirectImage.{u, w} Λ f)
          (etaleModuleDerivedDirectImageComp.{u, w} Λ g h gh hgh).hom := by
  simp only [etaleModuleDerivedDirectImageComp_hom_eq_univ]
  have hc : (etaleModuleDirectImageComp.{u, w} Λ fg h fgh h₁).symm.hom ≫
      Functor.whiskerRight (etaleModuleDirectImageComp.{u, w} Λ f g fg hfg).symm.hom
        (etaleModuleDirectImage.{u, w} Λ h) =
      (etaleModuleDirectImageComp.{u, w} Λ f gh fgh h₂).symm.hom ≫
        Functor.whiskerLeft (etaleModuleDirectImage.{u, w} Λ f)
          (etaleModuleDirectImageComp.{u, w} Λ g h gh hgh).inv := by
    ext F : 2
    exact smallEtalePushforwardComp'_inv_app_cocycle f g h fg hfg gh hgh fgh h₁ h₂
      (ModuleCat.{max (u + 1) w} Λ) F
  simpa only [rightDerivedFunctorPlusNatIso_symm, Iso.symm_hom, Category.assoc] using
    rightDerivedFunctorPlusComp_paste _ _ _ _ hc

/-- `etaleModuleDerivedDirectImageComp_assoc_univ` read at an object. -/
theorem etaleModuleDerivedDirectImageComp_assoc_univ_app {T X Y Z : Scheme.{u}} (f : T ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z) (fg : T ⟶ Y) (hfg : fg = f ≫ g) (gh : X ⟶ Z) (hgh : gh = g ≫ h)
    (fgh : T ⟶ Z) (h₁ : fgh = fg ≫ h) (h₂ : fgh = f ≫ gh)
    (K : DerivedCategory.Plus (EtaleModules.{u, w} Λ T)) :
    (etaleModuleDerivedDirectImageComp.{u, w} Λ fg h fgh h₁).hom.app K ≫
        (etaleModuleDerivedDirectImage.{u, w} Λ h).map
          ((etaleModuleDerivedDirectImageComp.{u, w} Λ f g fg hfg).hom.app K) =
      (etaleModuleDerivedDirectImageComp.{u, w} Λ f gh fgh h₂).hom.app K ≫
        (etaleModuleDerivedDirectImageComp.{u, w} Λ g h gh hgh).hom.app
          ((etaleModuleDerivedDirectImage.{u, w} Λ f).obj K) :=
  NatTrans.congr_app
    (etaleModuleDerivedDirectImageComp_assoc_univ Λ f g h fg hfg gh hgh fgh h₁ h₂) K

end Assoc

/-! ### Independence of the compactification -/

section Independence

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- **The map `Rk_! ⟶ Rḡ_* ∘ Rj_!` of [Stacks, Tag 0F7G] is compatible with the maps
`Rj_! ⟶ Rj_*`.** For a morphism `g : j ⟶ k` of compactifications, the map of Tag 0F7G followed
by `Rḡ_*` of `Rj_! ⟶ Rj_*` is `Rk_! ⟶ Rk_*` followed by the composition isomorphism
`Rk_* ≅ Rḡ_* ∘ Rj_*`. On sheaves this is the normalization
`Stacks.EtaleCohomology.etaleModuleRefinementComparison_comp_map` of the underived comparison. -/
theorem derivedRefinementComparisonUniv_comp_toDirectImage {j k : CompactificationOf (Over.mk f)}
    (g : j ⟶ k) :
    derivedRefinementComparisonUniv Λ g ≫
        Functor.whiskerRight
          (etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, w} Λ j.immersion)
          (etaleModuleDerivedDirectImage.{u, w} Λ (CompactificationOf.Hom.map g)) =
      etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, w} Λ k.immersion ≫
        (etaleModuleDerivedDirectImageComp.{u, w} Λ j.immersion (CompactificationOf.Hom.map g)
          k.immersion (CompactificationOf.immersion_comp_map g).symm).hom := by
  have h₀ : (refinementIsoUniv Λ g).hom ≫
      Functor.whiskerRight (etaleModuleExtensionByZeroToDirectImage.{u, w} Λ j.immersion)
        (etaleModuleDirectImage.{u, w} Λ (CompactificationOf.Hom.map g)) =
      etaleModuleExtensionByZeroToDirectImage.{u, w} Λ k.immersion ≫
        (etaleModuleDirectImageComp.{u, w} Λ j.immersion (CompactificationOf.Hom.map g)
          k.immersion (CompactificationOf.immersion_comp_map g).symm).inv := by
    ext F : 2
    exact etaleModuleRefinementComparison_comp_map Λ (CompactificationOf.immersion_comp_map g) F
  rw [derivedRefinementComparisonUniv, etaleModuleDerivedDirectImageComp_hom_eq_univ,
    etaleModuleDerivedExtensionByZeroToDirectImagePlus,
    etaleModuleDerivedExtensionByZeroToDirectImagePlus, Category.assoc,
    ← rightDerivedFunctorPlusComp_natTrans_whiskerRight, rightDerivedFunctorPlusNatIso_hom_eq,
    rightDerivedFunctorPlusNatIso_inv_eq, ← Category.assoc, ← rightDerivedFunctorPlusNatTrans_comp,
    h₀, rightDerivedFunctorPlusNatTrans_comp, Category.assoc]

/-- **The map `Rf_! ⟶ Rf_*` is carried to itself by a morphism of compactifications**: for
`g : j ⟶ k`, the comparison `Rf_!^k ⟶ Rf_!^j` of [Stacks, Tag 0F7I] followed by the map
`Rf_!^j ⟶ Rf_*` is the map `Rf_!^k ⟶ Rf_*`. -/
theorem derivedLowerShriekHomUniv_comp_toDirectImage {j k : CompactificationOf (Over.mk f)}
    (g : j ⟶ k) :
    derivedLowerShriekHomUniv Λ g ≫ derivedLowerShriekToDirectImage.{u, w} Λ f j =
      derivedLowerShriekToDirectImage.{u, w} Λ f k := by
  refine NatTrans.ext (funext fun K => ?_)
  have hA := NatTrans.congr_app (derivedRefinementComparisonUniv_comp_toDirectImage Λ g) K
  have hB := etaleModuleDerivedDirectImageComp_assoc_univ_app Λ j.immersion
    (CompactificationOf.Hom.map g) k.toBase k.immersion
    (CompactificationOf.immersion_comp_map g).symm j.toBase
    (CompactificationOf.map_comp_toBase g).symm f (CompactificationOf.immersion_toBase k).symm
    (CompactificationOf.immersion_toBase j).symm K
  have hinv : inv (derivedBaseComparisonUniv Λ g) =
      (etaleModuleDerivedDirectImageComp.{u, w} Λ (CompactificationOf.Hom.map g) k.toBase
        j.toBase (CompactificationOf.map_comp_toBase g).symm).inv := by
    have hbc : derivedBaseComparisonUniv Λ g =
        (etaleModuleDerivedDirectImageComp.{u, w} Λ (CompactificationOf.Hom.map g) k.toBase
          j.toBase (CompactificationOf.map_comp_toBase g).symm).hom := by
      rw [etaleModuleDerivedDirectImageComp_hom_eq_univ]
      rfl
    exact IsIso.inv_eq_of_hom_inv_id (by rw [hbc, Iso.hom_inv_id])
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hA
  have nb := (etaleModuleDerivedDirectImageComp.{u, w} Λ (CompactificationOf.Hom.map g)
    k.toBase j.toBase (CompactificationOf.map_comp_toBase g).symm).inv.naturality
      ((etaleModuleDerivedExtensionByZeroToDirectImagePlus.{u, w} Λ j.immersion).app K)
  simp only [Functor.comp_map] at nb
  simp only [NatTrans.comp_app, derivedLowerShriekHomUniv_app, hinv,
    derivedLowerShriekToDirectImage, Functor.whiskerRight_app, Category.assoc]
  rw [← reassoc_of% nb, ← Functor.map_comp_assoc, hA, Functor.map_comp_assoc]
  congr 1
  rw [← cancel_epi ((etaleModuleDerivedDirectImageComp.{u, w} Λ k.immersion k.toBase f
    (CompactificationOf.immersion_toBase k).symm).hom.app K), reassoc_of% hB]
  simp

/-- **[Stacks, Tag 0H6X]: the map `Rf_! ⟶ Rf_*` does not depend on the compactification**, on
`D⁺_tors(X_étale, Λ)`: for any two compactifications `j₁`, `j₂` of `X` over `Y`, the canonical
isomorphism `Rf_!^{j₁} ≅ Rf_!^{j₂}` of [Stacks, Tag 0F7I], computed through a compactification
dominating both, followed by the map `Rf_!^{j₂} ⟶ Rf_*` is the map `Rf_!^{j₁} ⟶ Rf_*`. -/
@[stacks 0H6X "independence of the compactification, on D⁺_tors"]
theorem derivedLowerShriekCompactificationIsoUniv_hom_comp_toDirectImage [CompactSpace Y]
    [QuasiSeparatedSpace Y] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (j₁ j₂ : CompactificationOf (Over.mk f)) :
    (derivedLowerShriekCompactificationIsoUniv f j₁ j₂ Λ).hom ≫
        Functor.whiskerLeft (isTorsionPlus.{u, w} Λ X).ι
          (derivedLowerShriekToDirectImage.{u, w} Λ f j₂) =
      Functor.whiskerLeft (isTorsionPlus.{u, w} Λ X).ι
        (derivedLowerShriekToDirectImage.{u, w} Λ f j₁) :=
  IsCofiltered.isoSystemComparison_hom_comp _
    (fun j => Functor.whiskerLeft (isTorsionPlus.{u, w} Λ X).ι
      (derivedLowerShriekToDirectImage.{u, w} Λ f j))
    (fun g => NatTrans.ext (funext fun K =>
      NatTrans.congr_app (derivedLowerShriekHomUniv_comp_toDirectImage Λ g) K.obj)) j₁ j₂

end Independence

end Stacks.EtaleCohomology

end
