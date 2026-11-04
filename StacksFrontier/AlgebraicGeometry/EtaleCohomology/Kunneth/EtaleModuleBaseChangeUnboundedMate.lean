module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleDerivedTransportAtComplexes

/-!
# The unbounded base change map of sheaves of `Λ`-modules is the derived mate

Let `g' ≫ f = f' ≫ g` be a commutative square of schemes and `Λ` a commutative ring. The base
change map `g⁻¹Rf_* ⟶ Rf'_*(g')⁻¹` on the unbounded derived categories `D(-_étale, Λ)` of
`Stacks.EtaleCohomology.EtaleModules`,
`Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeUnbounded`, is built by descending the
degreewise base change map along the universal property of `Rf_* ⋙ g⁻¹`. On the constant ringed
topoi `(X_étale, Λ̲)`, through the equivalences
`Φ = Stacks.EtaleCohomology.etaleDerivedEquivalence`, the base change map of the square is the
mate `Stacks.CategoryTheory.BaseChange.twoSquare` of the derived adjunctions of
[Stacks, Tag 07A6] along the identification of the two composite derived pullbacks.

This file proves that **the two agree** (`etaleModuleDerivedBaseChangeUnboundedTransported_eq`):
`Φ` carries the descended base change map to the mate, through the identifications of the
derived direct and inverse images with their ringed-topos counterparts.

## The proof

Both sides are transformations out of `(Rf_* ⋙ g⁻¹) ⋙ Φ`, which is a right derived functor of
degreewise `f_*` followed by `g⁻¹ ⋙ Φ`; so it suffices to compare them after the unit, at every
complex `K`. There the descended side is computed by its defining factorization
(`etaleModuleDerivedBaseChangeUnbounded_fac`) and the mate by
`AlgebraicGeometry.RingedToposHom.TwoIso.derivedBaseChange_fac`; the identifications of the
derived images are computed at `Q K` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleDerivedTransportAtComplexes`. Both
sides become `Qh` of a degreewise map followed by the ringed-topos unit of `Rf'_*`
(`etaleModuleDerivedBaseChangeUnboundedTransported_fac`,
`etaleRingedSquareBaseChangeTransported_fac`), and the two degreewise maps agree
(`etaleModuleBaseChangeTransportedComplex_eq`) because `Θ` carries the étale base change map of
sheaves of modules to the ringed one.

## References

* [Stacks Project, Tag 0E44](https://stacks.math.columbia.edu/tag/0E44)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.ProjectionFormulaOfToposHom

-- `etaleModuleDerivedBaseChangeUnbounded` and `etaleDerivedEquivalence` are built for the
-- standard model of the derived categories.
attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] etaleRingedPullbackOnHomotopy_hasLeftDerivedFunctor
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type r) [CommRing Λ] {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
  (f' : X' ⟶ Y') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)

/-- The descended base change map, carried by `Φ` and read through the identifications of the
derived direct and inverse images with the ringed-topos ones. -/
abbrev etaleModuleDerivedBaseChangeUnboundedTransported :
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙
      etaleModuleDerivedInverseImage.{u, r} Λ g) ⋙
        (etaleDerivedEquivalence.{u, r} Λ Y').functor ⟶
      (etaleDerivedEquivalence.{u, r} Λ X).functor ⋙
        (etaleRingedDerivedPullback.{u, r} Λ g' ⋙ etaleRingedDerivedPushforward.{u, r} Λ f') :=
  Functor.whiskerRight (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ f g g' f' w) _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (etaleDerivedPushforwardIso.{u, r} Λ f').hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (etaleRingedDerivedPullbackIso.{u, r} Λ g').inv _ ≫
    (Functor.associator _ _ _).hom

/-- The mate on the ringed topoi, read on `D(X_étale, Λ)` through `Φ` and the identifications of
the derived direct and inverse images with the ringed-topos ones. -/
abbrev etaleRingedSquareBaseChangeTransported :
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙
      etaleModuleDerivedInverseImage.{u, r} Λ g) ⋙
        (etaleDerivedEquivalence.{u, r} Λ Y').functor ⟶
      (etaleDerivedEquivalence.{u, r} Λ X).functor ⋙
        (etaleRingedDerivedPullback.{u, r} Λ g' ⋙ etaleRingedDerivedPushforward.{u, r} Λ f') :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (etaleRingedDerivedPullbackIso.{u, r} Λ g).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (etaleDerivedPushforwardIso.{u, r} Λ f).hom _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (Stacks.CategoryTheory.BaseChange.twoSquare
      (derivedAdjunction (etaleRingedToposHom.{u, r} Λ f))
      (derivedAdjunction (etaleRingedToposHom.{u, r} Λ f'))
      (RingedToposHom.TwoIso.derivedPullbackSquareIso.{max (u + 1) r}
        (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)) (Iso.refl _))

/-- The chase computing the descended side, over variables. -/
private theorem chase_left {𝒞 𝒞₁ : Type*} [Category* 𝒞] [Category* 𝒞₁] (R : 𝒞₁ ⥤ 𝒞)
    {o₀ o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ o₉ : 𝒞} {e₀ e₁ e₂ e₃ e₄ e₅ : 𝒞₁}
    (A : o₀ ⟶ o₁) (B : o₁ ⟶ o₂) (C : o₂ ⟶ R.obj e₀) (P' : e₀ ⟶ e₁)
    (φ₁ : o₀ ⟶ o₃) (φ₂ : o₃ ⟶ o₄) (φ₃ : o₄ ⟶ o₅) (φ₄ : o₅ ⟶ o₂)
    (hfac : A ≫ B = φ₁ ≫ φ₂ ≫ φ₃ ≫ φ₄) (D₀ : o₅ ⟶ R.obj e₂) (ψ : e₂ ⟶ e₀)
    (hn : φ₄ ≫ C = D₀ ≫ R.map ψ) (fiI : o₃ ⟶ o₆) (θc : o₆ ⟶ o₇) (fiH : o₇ ⟶ o₄)
    (hFI : φ₂ = fiI ≫ θc ≫ fiH) (pic : o₇ ⟶ o₈) (ur₁ : o₈ ⟶ R.obj e₃) (fiH' : e₃ ⟶ e₂)
    (hAE : fiH ≫ φ₃ ≫ D₀ = pic ≫ ur₁ ≫ R.map fiH') (ψ' : e₀ ⟶ e₂) (fiI' : e₂ ⟶ e₃)
    (ci : e₃ ⟶ e₄) (cmpI : e₄ ⟶ e₅) (lg : e₅ ⟶ e₁) (hB : P' = ψ' ≫ fiI' ≫ ci ≫ cmpI ≫ lg)
    (hψ : ψ ≫ ψ' = 𝟙 _) (hfi : fiH' ≫ fiI' = 𝟙 _) (fci : o₈ ⟶ o₉) (ur₂ : o₉ ⟶ R.obj e₄)
    (hur : ur₁ ≫ R.map ci = fci ≫ ur₂) (ZL : o₆ ⟶ o₉) (hcomb : θc ≫ pic ≫ fci = ZL) :
    A ≫ B ≫ C ≫ R.map P' = φ₁ ≫ fiI ≫ ZL ≫ ur₂ ≫ R.map cmpI ≫ R.map lg := by
  rw [reassoc_of% hfac, reassoc_of% hn, hFI]
  simp only [Category.assoc]
  rw [reassoc_of% hAE, ← R.map_comp_assoc, ← R.map_comp, hB, Category.assoc, reassoc_of% hψ,
    reassoc_of% hfi]
  simp only [R.map_comp]
  rw [reassoc_of% hur, ← hcomb]
  simp only [Category.assoc]

/-- The chase computing the mate side, over variables. -/
private theorem chase_right {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Lg : 𝒟 ⥤ 𝒞)
    {o₀ o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ o₉ : 𝒞} {d₀ d₁ d₂ d₃ d₄ d₅ : 𝒟}
    (A : o₀ ⟶ o₁) (Pinv : o₁ ⟶ Lg.obj d₀) (Dm : d₀ ⟶ d₁) (BCr : Lg.obj d₁ ⟶ o₂)
    (P₀ : o₀ ⟶ Lg.obj d₂) (u₁ : d₂ ⟶ d₀) (hnP : A ≫ Pinv = P₀ ≫ Lg.map u₁)
    (φ₁ : o₀ ⟶ o₃) (fiI : o₃ ⟶ o₄) (ci : o₄ ⟶ o₅) (cmpI : o₅ ⟶ Lg.obj d₃) (fiY : d₃ ⟶ d₂)
    (hB : P₀ = φ₁ ≫ fiI ≫ ci ≫ cmpI ≫ Lg.map fiY) (pic : d₃ ⟶ d₄) (urf : d₄ ⟶ d₅)
    (rf : d₅ ⟶ d₁) (hAE : fiY ≫ u₁ ≫ Dm = pic ≫ urf ≫ rf) (gpic : o₅ ⟶ o₆)
    (cmpI₂ : o₆ ⟶ Lg.obj d₄) (hcmp : cmpI ≫ Lg.map pic = gpic ≫ cmpI₂) (BCr₀ : Lg.obj d₅ ⟶ o₇)
    (T₂ : o₇ ⟶ o₂) (hBC : Lg.map rf ≫ BCr = BCr₀ ≫ T₂) (mbcQ : o₆ ⟶ o₈) (ur₂ : o₈ ⟶ o₉)
    (T₁ : o₉ ⟶ o₇) (hFr : cmpI₂ ≫ Lg.map urf ≫ BCr₀ = mbcQ ≫ ur₂ ≫ T₁) (ZR : o₄ ⟶ o₈)
    (hcomb : ci ≫ gpic ≫ mbcQ = ZR) :
    A ≫ Pinv ≫ Lg.map Dm ≫ BCr = φ₁ ≫ fiI ≫ ZR ≫ ur₂ ≫ T₁ ≫ T₂ := by
  have hL : Lg.map fiY ≫ Lg.map u₁ ≫ Lg.map Dm = Lg.map pic ≫ Lg.map urf ≫ Lg.map rf := by
    rw [← Lg.map_comp, ← Lg.map_comp, hAE, Lg.map_comp, Lg.map_comp]
  rw [reassoc_of% hnP, hB]
  simp only [Category.assoc]
  rw [reassoc_of% hL, hBC, reassoc_of% hcmp, reassoc_of% hFr, ← hcomb]
  simp only [Category.assoc]

attribute [local instance] etaleRingedToposHom_pushforwardModules_additive

private theorem map_comp₃ {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Fn : 𝒞 ⥤ 𝒟)
    {a b c d : 𝒞} (x : a ⟶ b) (y : b ⟶ c) (z : c ⟶ d) :
    Fn.map x ≫ Fn.map y ≫ Fn.map z = Fn.map (x ≫ y ≫ z) := by
  rw [Fn.map_comp, Fn.map_comp]

/-- The localized degreewise base change map, the direct-image comparison and the pullback
comparison along `g'`, composed: the complex-level map read off the descended side. -/
abbrev etaleModuleBaseChangeTransportedComplex (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :=
  Stacks.DerivedCategorySquare.baseChangeLeftComplex (etaleRingedPushforwardCompIso.{u, r} Λ f')
    (etaleRingedPullbackCompIso.{u, r} Λ g') K
    (etaleModuleComplexBaseChangeUnbounded.{u, r} Λ f g g' f' w)

/-- **The descended base change map after the unit, read on the ringed topoi.** For a complex `K`
of sheaves of `Λ`-modules on `X_étale`, `Φ` of `g⁻¹` of the unit of `Rf_*` at `K`, followed by the
transported base change map, is `Qh` of the degreewise map
`Stacks.EtaleCohomology.etaleModuleBaseChangeTransportedComplex`, followed by the ringed-topos
unit of `Rf'_*` and by `Rf'_*` of the inverse of the comparison `L(g')^* ⟶ (g')^*`. -/
theorem etaleModuleDerivedBaseChangeUnboundedTransported_fac
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    (etaleDerivedEquivalence.{u, r} Λ Y').functor.map
        ((etaleModuleDerivedInverseImage.{u, r} Λ g).map
          ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app K)) ≫
      (etaleDerivedEquivalence.{u, r} Λ Y').functor.map
        ((etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ f g g' f' w).app
          (DerivedCategory.Q.obj K)) ≫
      (etaleDerivedPushforwardIso.{u, r} Λ f').hom.app
        ((etaleModuleDerivedInverseImage.{u, r} Λ g').obj (DerivedCategory.Q.obj K)) ≫
      (etaleRingedDerivedPushforward.{u, r} Λ f').map
        ((etaleRingedDerivedPullbackIso.{u, r} Λ g').inv.app (DerivedCategory.Q.obj K)) =
    (etaleDerivedEquivalence.{u, r} Λ Y').functor.map
        ((etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategoryFactors.hom.app
          (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
      (etaleDerivedEquivalenceFactorsIso.{u, r} Λ (X := Y')).inv.app
        (((etaleModuleInverseImage.{u, r} Λ g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (etaleModuleBaseChangeTransportedComplex Λ f g f' g' w K)) ≫
      (etaleRingedDerivedPushforwardUnit.{u, r} Λ f').app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((etaleRingedPullback.{u, r} Λ g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((etaleModulesEquivalence.{u, r} Λ X).functor.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K))) ≫
      (etaleRingedDerivedPushforward.{u, r} Λ f').map
        (@CategoryTheory.inv _ _ _ _
          ((derivedPullbackComparison (etaleRingedToposHom.{u, r} Λ g')).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
              (((etaleModulesEquivalence.{u, r} Λ X).functor.mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K)))
          (isIso_etaleRingedDerivedPullbackComparison_app.{u, r} Λ g' _)) ≫
      (etaleRingedDerivedPushforward.{u, r} Λ f').map ((etaleRingedDerivedPullback.{u, r} Λ g').map
        ((etaleDerivedEquivalenceFactorsIso.{u, r} Λ (X := X)).hom.app K)) := by
  have hfac := congrArg (etaleDerivedEquivalence.{u, r} Λ Y').functor.map
    (etaleModuleDerivedBaseChangeUnbounded_fac.{u, r} Λ f g g' f' w K)
  simp only [Functor.map_comp] at hfac
  exact chase_left (etaleRingedDerivedPushforward.{u, r} Λ f') _ _ _ _ _ _ _ _ hfac _ _
    ((etaleDerivedPushforwardIso.{u, r} Λ f').hom.naturality
      ((etaleModuleInverseImage.{u, r} Λ g').mapDerivedCategoryFactors.inv.app K)) _ _ _
    (NatIso.naturality_1 (etaleDerivedEquivalenceFactorsIso.{u, r} Λ (X := Y'))
      ((etaleModuleComplexBaseChangeUnbounded.{u, r} Λ f g g' f' w).app K)).symm _ _ _
    (etaleDerivedEquivalenceFactorsIso_hom_comp_map_unit_comp_etaleDerivedPushforwardIso_hom.{u, r}
      Λ f' (((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K))
    _ _ _ _ _ (etaleRingedDerivedPullbackIso_inv_app_Q.{u, r} Λ g' K)
    (Stacks.DerivedCategorySquare.map_comp_map_eq_id _ _ _ (Iso.inv_hom_id_app _ _))
    (Iso.hom_inv_id_app _ _) _ _
    ((etaleRingedDerivedPushforwardUnit.{u, r} Λ f').naturality
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (Stacks.DerivedCategorySquare.degreewiseInv _ _ _ _
          (etaleRingedPullbackCompIso.{u, r} Λ g') K))).symm _
    (map_comp₃ (HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) _ _ _)

private theorem inv_naturality {𝒞 : Type*} [Category* 𝒞] {a b c d : 𝒞} (x : a ⟶ b)
    (c₁ : a ⟶ c) (c₂ : b ⟶ d) (y : c ⟶ d) (c₁' : c ⟶ a) (c₂' : d ⟶ b) (h : x ≫ c₂ = c₁ ≫ y)
    (h₁ : c₁' ≫ c₁ = 𝟙 _) (h₂ : c₂ ≫ c₂' = 𝟙 _) : c₁' ≫ x = y ≫ c₂' := by
  rw [← Category.comp_id x, ← h₂, reassoc_of% h, reassoc_of% h₁]

private theorem solve_fac {𝒞 𝒞₁ : Type*} [Category* 𝒞] [Category* 𝒞₁] (R : 𝒞₁ ⥤ 𝒞)
    {o₀ o₁ o₂ o₃ : 𝒞} {e₀ e₁ : 𝒞₁} (a : o₀ ⟶ o₁) (b : o₁ ⟶ R.obj e₀) (c : e₀ ⟶ e₁)
    (d : o₀ ⟶ o₂) (e : o₂ ⟶ o₃) (k : o₃ ⟶ R.obj e₁) (d' : o₂ ⟶ o₀) (c' : e₁ ⟶ e₀)
    (h : a ≫ b ≫ R.map c = d ≫ e ≫ k) (hd : d' ≫ d = 𝟙 _) (hc : c ≫ c' = 𝟙 _) :
    d' ≫ a ≫ b = e ≫ k ≫ R.map c' := by
  simpa using inv_naturality (a ≫ b) d (R.map c) (e ≫ k) d' (R.map c') (by simpa using h) hd
    (by rw [← R.map_comp, hc, R.map_id])

/-- The complex-level map read off the mate side. -/
abbrev etaleRingedSquareBaseChangeTransportedComplex
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :=
  Stacks.DerivedCategorySquare.baseChangeRightComplex (etaleRingedPushforwardCompIso.{u, r} Λ f)
    (etaleRingedPullbackCompIso.{u, r} Λ g) K
    (RingedToposHom.TwoIso.moduleBaseChangeComplex.{max r (u + 1)}
      (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)
      (((etaleModulesEquivalence.{u, r} Λ X).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K))

/-- **The mate after the unit.** The same composite as in
`Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeUnboundedTransported_fac`, with the mate of the
derived adjunctions in place of the descended base change map, is `Qh` of the degreewise map
`Stacks.EtaleCohomology.etaleRingedSquareBaseChangeTransportedComplex`, followed by the same unit
and comparison. -/
theorem etaleRingedSquareBaseChangeTransported_fac
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    (etaleDerivedEquivalence.{u, r} Λ Y').functor.map
        ((etaleModuleDerivedInverseImage.{u, r} Λ g).map
          ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app K)) ≫
      (etaleRingedDerivedPullbackIso.{u, r} Λ g).inv.app
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj (DerivedCategory.Q.obj K)) ≫
      (etaleRingedDerivedPullback.{u, r} Λ g).map
        ((etaleDerivedPushforwardIso.{u, r} Λ f).hom.app (DerivedCategory.Q.obj K)) ≫
      Stacks.CategoryTheory.BaseChange.map (derivedAdjunction (etaleRingedToposHom.{u, r} Λ f))
        (derivedAdjunction (etaleRingedToposHom.{u, r} Λ f'))
        (RingedToposHom.TwoIso.derivedPullbackSquareIso.{max (u + 1) r}
          (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)) (Iso.refl _)
        ((etaleDerivedEquivalence.{u, r} Λ X).functor.obj (DerivedCategory.Q.obj K)) =
    (etaleDerivedEquivalence.{u, r} Λ Y').functor.map
        ((etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategoryFactors.hom.app
          (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
      (etaleDerivedEquivalenceFactorsIso.{u, r} Λ (X := Y')).inv.app
        (((etaleModuleInverseImage.{u, r} Λ g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (etaleRingedSquareBaseChangeTransportedComplex Λ f g f' g' w K)) ≫
      (etaleRingedDerivedPushforwardUnit.{u, r} Λ f').app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((etaleRingedPullback.{u, r} Λ g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((etaleModulesEquivalence.{u, r} Λ X).functor.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K))) ≫
      (etaleRingedDerivedPushforward.{u, r} Λ f').map
        (@CategoryTheory.inv _ _ _ _
          ((derivedPullbackComparison (etaleRingedToposHom.{u, r} Λ g')).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
              (((etaleModulesEquivalence.{u, r} Λ X).functor.mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K)))
          (isIso_etaleRingedDerivedPullbackComparison_app.{u, r} Λ g' _)) ≫
      (etaleRingedDerivedPushforward.{u, r} Λ f').map ((etaleRingedDerivedPullback.{u, r} Λ g').map
        ((etaleDerivedEquivalenceFactorsIso.{u, r} Λ (X := X)).hom.app K)) := by
  have iB := isIso_etaleRingedDerivedPullbackComparison_app.{u, r} Λ g
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((etaleRingedToposHom.{u, r} Λ f).pushforwardModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (((etaleModulesEquivalence.{u, r} Λ X).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)))
  have hcmp := inv_naturality _ _ _ _ _ _
    ((derivedPullbackComparison (etaleRingedToposHom.{u, r} Λ g)).naturality
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (Stacks.DerivedCategorySquare.degreewiseHom _ _ _ _
          (etaleRingedPushforwardCompIso.{u, r} Λ f) K)))
    (@IsIso.inv_hom_id _ _ _ _ _
      (isIso_etaleRingedDerivedPullbackComparison_app.{u, r} Λ g _))
    (@IsIso.hom_inv_id _ _ _ _ _ iB)
  have hFr := solve_fac (etaleRingedDerivedPushforward.{u, r} Λ f') _ _ _ _ _ _ _ _
    (RingedToposHom.TwoIso.derivedBaseChange_fac
      (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)
      (((etaleModulesEquivalence.{u, r} Λ X).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K))
    (@IsIso.inv_hom_id _ _ _ _ _ iB) (@IsIso.hom_inv_id _ _ _ _ _
      (isIso_etaleRingedDerivedPullbackComparison_app.{u, r} Λ g' _))
  exact chase_right (etaleRingedDerivedPullback.{u, r} Λ g) _ _ _ _ _ _
    ((etaleRingedDerivedPullbackIso.{u, r} Λ g).inv.naturality
      ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app K)) _ _ _ _ _
    (etaleRingedDerivedPullbackIso_inv_app_Q.{u, r} Λ g
      (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) _ _ _
    (etaleDerivedEquivalenceFactorsIso_hom_comp_map_unit_comp_etaleDerivedPushforwardIso_hom.{u, r}
      Λ f K) _ _ hcmp _ _
    (Stacks.CategoryTheory.BaseChange.map_naturality
      (derivedAdjunction (etaleRingedToposHom.{u, r} Λ f))
      (derivedAdjunction (etaleRingedToposHom.{u, r} Λ f'))
      (RingedToposHom.TwoIso.derivedPullbackSquareIso.{max (u + 1) r}
        (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)) (Iso.refl _)
      ((etaleDerivedEquivalenceFactorsIso.{u, r} Λ (X := X)).hom.app K)) _ _ _ hFr _
    (map_comp₃ (HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) _ _ _)

/-- **The two degreewise maps agree**: `Θ` carries the étale base change map of sheaves of
`Λ`-modules to the base change map of the square of constant ringed topoi, degreewise. -/
theorem etaleModuleBaseChangeTransportedComplex_eq
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    etaleModuleBaseChangeTransportedComplex Λ f g f' g' w K =
      etaleRingedSquareBaseChangeTransportedComplex Λ f g f' g' w K := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  have h :=
    map_etaleModuleBaseChange_comp_etaleRingedPullbackCompIso_inv.{u, r} Λ f g f' g' w (K.X n)
  simp only [etaleModuleBaseChangeTransportedComplex, etaleRingedSquareBaseChangeTransportedComplex,
    Stacks.DerivedCategorySquare.baseChangeLeftComplex,
    Stacks.DerivedCategorySquare.baseChangeRightComplex, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, Stacks.DerivedCategorySquare.degreewiseHom_f,
    Stacks.DerivedCategorySquare.degreewiseInv_f,
    RingedToposHom.TwoIso.moduleBaseChangeComplex_f]
  have hc' : ((etaleModuleComplexBaseChangeUnbounded.{u, r} Λ f g g' f' w).app K).f n =
      (etaleModuleBaseChange.{u, r} Λ f f' g g' w.symm).app (K.X n) := by
    have hdef : etaleModuleComplexBaseChangeUnbounded.{u, r} Λ f g g' f' w =
        (((Functor.mapHomologicalComplexCompIso (Iso.refl _) _).hom ≫
          NatTrans.mapHomologicalComplex (etaleModuleBaseChange.{u, r} Λ f f' g g' w.symm) _ ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).inv :
        ((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex _ ⋙
            (etaleModuleInverseImage.{u, r} Λ g).mapHomologicalComplex _ :
          CochainComplex (EtaleModules.{u, r} Λ X) ℤ ⥤
            CochainComplex (EtaleModules.{u, r} Λ Y') ℤ) ⟶
        ((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex _ ⋙
            (etaleModuleDirectImage.{u, r} Λ f').mapHomologicalComplex _ :
          CochainComplex (EtaleModules.{u, r} Λ X) ℤ ⥤
            CochainComplex (EtaleModules.{u, r} Λ Y') ℤ))) :=
      rfl
    rw [hdef]
    obtain ⟨β, hβ⟩ : ∃ β, β = etaleModuleBaseChange.{u, r} Λ f f' g g' w.symm := ⟨_, rfl⟩
    rw [← hβ]
    exact Stacks.DerivedCategorySquare.mapHomologicalComplexCompIso_natTrans_app_f _ _ _ _ β K n
  convert h using 2
  all_goals first
    | (simp only [Functor.mapHomologicalComplex_obj_X, Functor.comp_obj]; done)
    | (rw [hc'])

/-- **The unbounded base change map of sheaves of `Λ`-modules is the derived mate on the constant
ringed topoi.** Through `Φ = Stacks.EtaleCohomology.etaleDerivedEquivalence` and the
identifications of the derived direct and inverse images with their ringed-topos counterparts,
the descended base change map `g⁻¹Rf_* ⟶ Rf'_*(g')⁻¹` is the mate of the derived adjunctions along
the 2-commutative square of constant ringed topoi. -/
theorem etaleModuleDerivedBaseChangeUnboundedTransported_eq :
    etaleModuleDerivedBaseChangeUnboundedTransported Λ f g f' g' w =
      etaleRingedSquareBaseChangeTransported Λ f g f' g' w := by
  refine Functor.rightDerived_ext _ (Functor.whiskerRight
      (etaleModuleDerivedBaseChangeUnboundedUnit.{u, r} Λ f g) _ ≫ (Functor.associator _ _ _).hom)
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)) _ _ _ ?_
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.comp_obj]
  have hL := etaleModuleDerivedBaseChangeUnboundedTransported_fac.{u, r} Λ f g f' g' w K
  rw [etaleModuleBaseChangeTransportedComplex_eq.{u, r} Λ f g f' g' w K] at hL
  exact hL.trans (etaleRingedSquareBaseChangeTransported_fac.{u, r} Λ f g f' g' w K).symm

end Stacks.EtaleCohomology

end
