module

public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.DerivedSectionsPullback
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonAssoc

/-!
# Pullback on derived global sections of abelian sheaves, against the derived-functor units

Let `f : X' ⟶ X` be a morphism of schemes and let `K` be a bounded below complex of abelian
sheaves on `X'`. The pullback of [Stacks, Tag 0FL6] on derived global sections is assembled from
`RΓ(X, f_*K ⟶ Rf_*K)` and the identification `RΓ(X, Rf_* -) = RΓ(X', -)` of
[Stacks, Tag 01EZ] (`AlgebraicGeometry.Scheme.Hom.derivedSectionsPullback`). Read after the
derived-functor unit `Γ(X, f_*K) ⟶ RΓ(X, f_*K)`, that composite is the unit
`Γ(X', K) ⟶ RΓ(X', K)`, the two complexes of global sections being the same complex. This is
`AlgebraicGeometry.Scheme.Hom.sectionsUnit_comp_pushforwardPullback`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.pushforwardPullback`: `RΓ(X, f_*K) ⟶ RΓ(X', K)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.deRhamCohomologyPullback_apply`: the pullback map of de Rham
  cohomology through `pushforwardPullback`.
* `AlgebraicGeometry.Scheme.Hom.pushforwardPullback_naturality`: it is natural in `K`.
* `AlgebraicGeometry.Scheme.Hom.sectionsUnit_comp_pushforwardPullback`: the unit
  compatibility.
* `AlgebraicGeometry.Scheme.Hom.derivedSectionsPullback_eq_comp`: the pullback along a map of
  complexes `φ : K ⟶ f_*K'` is `RΓ(X, φ)` followed by `pushforwardPullback`.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Opposite TopologicalSpace
open Stacks.Cohomology.Leray Stacks.Cohomology.LerayLowDegree
open Stacks.Cohomology.DerivedPushforwardSections

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X' X : Scheme.{u}} (f : X' ⟶ X)

/-- **Pullback from the derived sections of a direct image**: `RΓ(X, f_*K) ⟶ RΓ(X, Rf_*K)`,
followed by the identification `RΓ(X, Rf_* -) = RΓ(X', -)` of [Stacks, Tag 01EZ]. -/
def pushforwardPullback (K : CochainComplex.Plus (AbelianSheaf X'.toRingedSpace.carrier)) :
    (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj
          ((abelianPushforward.{u, u} f.base).mapCochainComplexPlus.obj K)) ⟶
      (sectionsFunctor X'.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj K) :=
  (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
      ((Functor.mapCochainComplexPlusDerivedUnit (abelianPushforward.{u, u} f.base)).app K) ≫
    (derivedSectionsPushforwardIso f).inv.app (DerivedCategory.Plus.Q.obj K)

/-- `pushforwardPullback` is natural in the complex. -/
theorem pushforwardPullback_naturality
    {K L : CochainComplex.Plus (AbelianSheaf X'.toRingedSpace.carrier)} (a : K ⟶ L) :
    (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map
          ((abelianPushforward.{u, u} f.base).mapCochainComplexPlus.map a)) ≫
      pushforwardPullback f L =
    pushforwardPullback f K ≫
      (sectionsFunctor X'.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map a) := by
  have hu :=
    (Functor.mapCochainComplexPlusDerivedUnit (abelianPushforward.{u, u} f.base)).naturality a
  have hc := (derivedSectionsPushforwardIso f).inv.naturality (DerivedCategory.Plus.Q.map a)
  dsimp only [Functor.comp_map] at hu hc
  simp only [pushforwardPullback, ← Functor.map_comp_assoc, hu, Functor.map_comp, assoc, hc]

/-- The pullback along a map of complexes `φ : K ⟶ f_*K'` is `RΓ(X, φ)` followed by
`pushforwardPullback`. -/
theorem derivedSectionsPullback_eq_comp
    {K : CochainComplex.Plus (AbelianSheaf X.toRingedSpace.carrier)}
    {K' : CochainComplex.Plus (AbelianSheaf X'.toRingedSpace.carrier)}
    (φ : K ⟶ (abelianPushforward.{u, u} f.base).mapCochainComplexPlus.obj K') :
    derivedSectionsPullback f φ =
      (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map φ) ≫ pushforwardPullback f K' := by
  rw [derivedSectionsPullback_eq]
  rfl

/-- **The pullback map of de Rham cohomology through `pushforwardPullback`**: on `H^i`, the
pullback `f^* : H^i_{dR}(X/S) ⟶ H^i_{dR}(X'/S')` of [Stacks, Tag 0FL6] is the map induced by the
canonical map `Ω^•_{X/S} ⟶ f_*Ω^•_{X'/S'}`, followed by `pushforwardPullback`. -/
theorem deRhamCohomologyPullback_apply {S' S : Scheme.{u}} (p : X ⟶ S) (p' : X' ⟶ S')
    (g : S' ⟶ S) (hcomm : f ≫ p = p' ≫ g) (i : ℤ) (ξ : ToType (deRhamCohomology p i)) :
    (deRhamCohomologyPullback f p p' g hcomm i).hom ξ =
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).map (pushforwardPullback f
        (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras p')
          (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras p'))))).hom
        (((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).map
          ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
            (DerivedCategory.Plus.Q.map
              (deRhamAbelianPushforwardMapPlus f p p' g hcomm)))).hom ξ) := by
  have h := derivedSectionsPullback_eq_comp f
    (K' := AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras p')
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras p')))
    (deRhamAbelianPushforwardMapPlus f p p' g hcomm)
  rw [deRhamCohomologyPullback, deRhamDerivedSectionsPullback_eq]
  refine (congrArg (fun φ => ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).map
    φ).hom ξ) h).trans ?_
  rw [Functor.map_comp]
  rfl

/-- The bookkeeping of `sectionsUnit_comp_pushforwardPullback`, at variables. -/
private theorem paste {C : Type*} [Category* C] {P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ : C}
    (q : P₀ ⟶ P₁) (uG : P₁ ⟶ P₂) (rq : P₂ ⟶ P₃) (rq' : P₃ ⟶ P₂) (uF : P₂ ⟶ P₄)
    (rF : P₄ ⟶ P₅) (M : P₃ ⟶ P₅) (L : P₅ ⟶ P₆) (L' : P₄ ⟶ P₇) (rFG : P₇ ⟶ P₆)
    (uFG : P₁ ⟶ P₇) (h₀ : M = rq' ≫ uF ≫ rF)
    (h₁ : rq ≫ rq' = 𝟙 _) (h₂ : rF ≫ L = L' ≫ rFG) (h₃ : (uG ≫ uF) ≫ L' = uFG) :
    (q ≫ uG ≫ rq) ≫ M ≫ L = q ≫ uFG ≫ rFG := by
  rw [← h₃, h₀]
  simp only [assoc]
  rw [reassoc_of% h₁, h₂]

/-- **The unit compatibility of the pullback from a direct image.** The derived-functor unit
`Γ(X, f_*K) ⟶ RΓ(X, f_*K)`, followed by `pushforwardPullback`, is the unit `Γ(X', K) ⟶ RΓ(X', K)`:
the two complexes of global sections are the same complex. -/
theorem sectionsUnit_comp_pushforwardPullback
    (K : CochainComplex.Plus (AbelianSheaf X'.toRingedSpace.carrier)) :
    (Functor.mapCochainComplexPlusDerivedUnit (sectionsFunctor X.toRingedSpace.carrier ⊤)).app
        ((abelianPushforward.{u, u} f.base).mapCochainComplexPlus.obj K) ≫
      pushforwardPullback f K =
    (Functor.mapCochainComplexPlusDerivedUnit
      (sectionsFunctor X'.toRingedSpace.carrier ⊤)).app K := by
  let F := abelianPushforward.{u, u} f.base
  let G := sectionsFunctor X.toRingedSpace.carrier ⊤
  let qK := (HomotopyCategory.Plus.quotient (AbelianSheaf X'.toRingedSpace.carrier)).obj K
  have hfac : (sectionsFunctor X'.toRingedSpace.carrier ⊤).rightDerivedFunctorPlusUnith.app qK ≫
      (derivedSectionsPushforwardIso f).hom.app (DerivedCategory.Plus.Qh.obj qK) =
      G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj qK) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app qK) :=
    (Functor.rightDerivedFunctorPlusComp_fac_app F G qK).trans
      (Functor.qhMapCompIsoReflInv_comp F G qK _)
  have h₁ : (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.quotientCompQhIso (AbelianSheaf X.toRingedSpace.carrier)).hom.app
          (F.mapCochainComplexPlus.obj K)) ≫
      (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.quotientCompQhIso (AbelianSheaf X.toRingedSpace.carrier)).inv.app
          (F.mapCochainComplexPlus.obj K)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  have h₂ := (derivedSectionsPushforwardIso f).inv.naturality
    ((DerivedCategory.Plus.quotientCompQhIso (AbelianSheaf X'.toRingedSpace.carrier)).hom.app K)
  have h₃ := (Iso.comp_inv_eq ((derivedSectionsPushforwardIso f).app
    (DerivedCategory.Plus.Qh.obj qK))).2 hfac.symm
  rw [pushforwardPullback, Functor.mapCochainComplexPlusDerivedUnit_app,
    Functor.mapCochainComplexPlusDerivedUnit_app, Functor.mapCochainComplexPlusDerivedUnit_app]
  exact paste _ _ _ _ _ _ _ _ _ _ _
    (((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map_comp _ _).trans
      (congrArg (_ ≫ ·)
        ((sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map_comp
        _ _))) h₁ h₂ h₃

end AlgebraicGeometry.Scheme.Hom

end
