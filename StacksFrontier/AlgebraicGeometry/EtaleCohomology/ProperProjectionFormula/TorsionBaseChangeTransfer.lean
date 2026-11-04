module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.RingedSquare
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.RingedPullbackComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.RingedPushforwardUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedBaseChangeUnbounded
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOfToposHomExactPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaBaseChangeOfToposHom

/-!
# Invertibility of the base change map: from sheaves of `Λ`-modules to the constant ringed topoi

For a commutative square of schemes `g' ≫ f = f' ≫ g` and a commutative ring `Λ`, there are two
base change maps `g^{-1} Rf_* ⟶ Rf'_* (g')^{-1}` on unbounded derived categories: the one of the
2-commutative square of constant ringed topoi
(`Stacks.Cohomology.ProjectionFormulaOfToposHom.squareBaseChangeMap` at
`Stacks.EtaleCohomology.etaleRingedToposHomSquareTwoIso`), and the one on sheaves of `Λ`-modules
(`Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeUnbounded`). This file shows that the first
is invertible as soon as the second is.

Both maps are computed at a K-injective complex by the degreewise base change map followed by the
derived-functor unit of `Rf'_*`
(`AlgebraicGeometry.RingedToposHom.TwoIso.derivedBaseChange_fac` and
`Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeUnbounded_fac`), every other factor being
invertible there; and the equivalences `Stacks.EtaleCohomology.etaleDerivedEquivalence` carry the
étale degreewise base change map and unit to the ringed-topos ones.

## Main definitions

* `Stacks.EtaleCohomology.etaleRingedBaseChangeUnitComposite`: on the ringed side, the localized
  degreewise base change map at a complex followed by the derived-functor unit of `Rf'_*`.

## Main results

* `Stacks.EtaleCohomology.isIso_squareBaseChangeMap_iff_of_isKInjective`: on the ringed side,
  invertibility at a K-injective complex is invertibility of the localized degreewise base change
  map followed by the unit.
* `Stacks.EtaleCohomology.isIso_complexMap_comp_unit_of_isKInjective`: on the étale side, the
  same composite is invertible when the base change map is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.ProjectionFormulaOfToposHom

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

/-- Sheafification of presheaves of sets on the small model of the small étale site, at the
universe of its objects (pinning the universe that a generic instance would leave free). -/
local instance (priority := high) (Λ : Type r) [CommRing Λ] (Z : Scheme.{u}) :
    HasSheafify (RingedSite.ringedTopos.{max (u + 1) r, max (u + 1) r, max (u + 1) r}
      (etaleRingedSite.{u, r} Λ Z)).J (Type (max (u + 1) r)) :=
  instHasSheafifyType.{max (u + 1) r, max (u + 1) r} _

attribute [local instance] etaleRingedPullbackOnHomotopy_hasLeftDerivedFunctor

variable (Λ : Type r) [CommRing Λ] {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
  (f' : X' ⟶ Y') (g' : X' ⟶ X) (w : g' ≫ f = f' ≫ g)

/-- In an equation `a ≫ b ≫ c = d ≫ e` with `a`, `c` and `d` invertible, `b` is invertible exactly
when `e` is. -/
theorem isIso_iff_of_comp_eq_comp {𝒞 : Type*} [Category 𝒞] {P Q R S T : 𝒞} {a : P ⟶ Q}
    {b : Q ⟶ R} {c : R ⟶ S} {d : P ⟶ T} {e : T ⟶ S} [IsIso a] [IsIso c] [IsIso d]
    (h : a ≫ b ≫ c = d ≫ e) : IsIso b ↔ IsIso e := by
  rw [← isIso_comp_left_iff d e, ← h, isIso_comp_left_iff, isIso_comp_right_iff]

/-- The localized degreewise base change map of the square of constant ringed topoi at a complex
`K` (`AlgebraicGeometry.RingedToposHom.TwoIso.moduleBaseChangeComplex`), followed by the
derived-functor unit of `Rf'_*` at `(g')^* K`. -/
abbrev etaleRingedBaseChangeUnitComposite (K : CochainComplex (EtaleRingedModules.{u, r} Λ X) ℤ) :=
  DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (RingedToposHom.TwoIso.moduleBaseChangeComplex
        (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w) K)) ≫
    ((pushforwardOnHomotopy (etaleRingedToposHom.{u, r} Λ f')).totalRightDerivedUnit
        DerivedCategory.Qh (sourceQuasiIso
          (RingedSite.ringedTopos.{max (u + 1) r, max (u + 1) r, max (u + 1) r}
            (etaleRingedSite.{u, r} Λ X')))).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((etaleRingedToposHom.{u, r} Λ g').toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K))

/-- **On the ringed side, the base change map at a K-injective complex is invertible exactly when
the localized degreewise base change map followed by the derived-functor unit of `Rf'_*` is**:
by `AlgebraicGeometry.RingedToposHom.TwoIso.derivedBaseChange_fac`, every other factor is
invertible there. -/
theorem isIso_squareBaseChangeMap_iff_of_isKInjective
    (K : CochainComplex (EtaleRingedModules.{u, r} Λ X) ℤ) (hK : K.IsKInjective) :
    IsIso (squareBaseChangeMap.{max (u + 1) r}
        (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) ↔
      IsIso (etaleRingedBaseChangeUnitComposite Λ f g f' g' w K) := by
  have h := RingedToposHom.TwoIso.derivedBaseChange_fac
    (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w) K
  have h₁ : IsIso ((pushforwardOnHomotopy (etaleRingedToposHom.{u, r} Λ f)).totalRightDerivedUnit
      DerivedCategory.Qh (sourceQuasiIso
        (RingedSite.ringedTopos.{max (u + 1) r, max (u + 1) r, max (u + 1) r}
          (etaleRingedSite.{u, r} Λ X))) |>.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :=
    Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective _ DerivedCategory.Qh _ _ K hK
  have h₂ := isIso_etaleRingedDerivedPullbackComparison_app.{u, r} Λ g'
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)
  have h₃ := isIso_etaleRingedDerivedPullbackComparison_app.{u, r} Λ g
    ((pushforwardMapHomotopy (etaleRingedToposHom.{u, r} Λ f)).obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
  exact @isIso_iff_of_comp_eq_comp _ _ _ _ _ _ _ _ _ _ _ _ (@Functor.map_isIso _ _ _ _ _ _ _ _ h₁)
    (@Functor.map_isIso _ _ _ _ _ _ _ _ h₂) h₃ h

/-- **The base change map is invertible everywhere as soon as it is invertible at the images of
K-injective complexes of sheaves of `Λ`-modules**: every object of `D(X_étale, Λ̲)` is isomorphic
to one, and the base change map is natural. -/
theorem isIso_squareBaseChangeMap_of_isKInjective
    (h : ∀ J : CochainComplex (EtaleModules.{u, r} Λ X) ℤ, J.IsKInjective →
      IsIso (squareBaseChangeMap.{max (u + 1) r}
        (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((etaleModulesEquivalence.{u, r} Λ X).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj J)))))
    (E : DerivedCategory (SheafOfModules.{max (u + 1) r}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSite.ringedTopos.{max (u + 1) r, max (u + 1)
          r, max (u + 1) r} (etaleRingedSite.{u, r} Λ X)).O))) :
    IsIso (squareBaseChangeMap.{max (u + 1) r}
      (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w) E) := by
  obtain ⟨J, hJ, ⟨e⟩⟩ := Stacks.Cohomology.UnboundedComplexes.exists_isKInjective_iso
    (A := EtaleModules.{u, r} Λ X) DerivedCategory.Qh ((etaleDerivedEquivalence.{u, r} Λ
        X).inverse.obj E)
  let e' : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((etaleModulesEquivalence.{u, r} Λ X).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J)) ≅ E :=
    (etaleDerivedEquivalenceFactorsIso.{u, r} Λ (X := X)).app J ≪≫
    (etaleDerivedEquivalence.{u, r} Λ X).functor.mapIso
      ((DerivedCategory.quotientCompQhIso _).symm.app J ≪≫ e) ≪≫
    (etaleDerivedEquivalence.{u, r} Λ X).counitIso.app E
  have hn := Stacks.CategoryTheory.BaseChange.map_naturality
    (derivedAdjunction (etaleRingedToposHom.{u, r} Λ f))
    (derivedAdjunction (etaleRingedToposHom.{u, r} Λ f'))
    (RingedToposHom.TwoIso.derivedPullbackSquareIso.{max (u + 1) r}
      (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)) (Iso.refl _) e'.hom
  have h₀ := h J hJ
  have : IsIso (Stacks.CategoryTheory.BaseChange.map
      (derivedAdjunction (etaleRingedToposHom.{u, r} Λ f))
      (derivedAdjunction (etaleRingedToposHom.{u, r} Λ f'))
      (RingedToposHom.TwoIso.derivedPullbackSquareIso.{max (u + 1) r}
        (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)) (Iso.refl _) E) := by
    have h₁ : IsIso ((derivedPullback (etaleRingedToposHom.{u, r} Λ g)).map
        ((derivedPushforward (etaleRingedToposHom.{u, r} Λ f)).map e'.hom) ≫
      Stacks.CategoryTheory.BaseChange.map
        (derivedAdjunction (etaleRingedToposHom.{u, r} Λ f))
        (derivedAdjunction (etaleRingedToposHom.{u, r} Λ f'))
        (RingedToposHom.TwoIso.derivedPullbackSquareIso.{max (u + 1) r}
          (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)) (Iso.refl _) E) := by
      rw [hn]
      exact IsIso.comp_isIso' h₀ inferInstance
    exact (isIso_comp_left_iff _ _).1 h₁
  exact this

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- **On the étale side, the localized degreewise base change map followed by the derived-functor
unit of `Rf'_*` is invertible at a K-injective complex, when the base change map is.** -/
theorem isIso_complexMap_comp_unit_of_isKInjective (J : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    (hJ : J.IsKInjective)
    (h : IsIso ((etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ f g g' f' w).app
      (DerivedCategory.Q.obj J))) :
    IsIso (DerivedCategory.Q.map
        ((etaleModuleComplexBaseChangeUnbounded.{u, r} Λ f g g' f' w).app J) ≫
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f').app
        (((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex (ComplexShape.up ℤ)).obj J))
            := by
  have hfac := etaleModuleDerivedBaseChangeUnbounded_fac.{u, r} Λ f g g' f' w J
  have hu : IsIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app J) :=
    isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, r} Λ f J hJ
  have hl : IsIso ((etaleModuleDerivedInverseImage.{u, r} Λ g).map
      ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app J) ≫
    (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ f g g' f' w).app (DerivedCategory.Q.obj J)) :=
    IsIso.comp_isIso
  rw [hfac] at hl
  have := (isIso_comp_left_iff _ _).1 hl
  rw [← Category.assoc] at this
  exact (isIso_comp_right_iff _ _).1 this

end Stacks.EtaleCohomology

end
