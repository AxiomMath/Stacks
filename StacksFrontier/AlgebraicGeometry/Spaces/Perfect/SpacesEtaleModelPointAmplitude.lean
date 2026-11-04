module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedGlobalSectionsBoundedAbove
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointCoproducts
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardQuasiCoherence

/-!
# The direct image from a quasi-compact quasi-separated space to the point has bounded amplitude

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`,
`φ : R →+* Γ(X, 𝒪_X)` a ring map, and `f` the morphism `(X_{spaces,étale}, 𝒪_X) ⟶ (pt, R)` of
`AlgebraicGeometry.Space.spacesEtaleModelToBaseRing`. There is one integer `N` such that `Rf_*`
carries every object of the spaces-étale model whose image in `D(𝒪_X)` has quasi-coherent
cohomology in degrees `[a, c]` to an object of `D(pt, R)` living in degrees `[a, c + N]`.

This is the bound the proof of [Stacks, Tag 0CTM] applies to `E ⊗^L 𝒪_X ⊗_R M` to read off the
Tor amplitude of `RΓ(X, E)`. It is
`AlgebraicGeometry.Space.exists_isLE_rightDerived_baseRingGlobalSections` transported along the
identification of `Rf_*` followed by the abelian group at the point with a right derived functor of
global sections (`AlgebraicGeometry.Space.isRightDerivedFunctor_pointTransport`); the abelian group
at the point is exact and detects zero objects.

## Main results

* `AlgebraicGeometry.Space.exists_isLE_derivedPushforward_spacesEtaleModelToBaseRing`: the upper
  bound.
* `AlgebraicGeometry.Space.isGE_derivedPushforward_spacesEtaleModelToBaseRing`: the lower bound.

## References

* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 08F7](https://stacks.math.columbia.edu/tag/08F7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory
attribute [local instance] hasCoproducts_derivedCategory_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
  {R : Type u} [CommRing R] (φ : R →+* modelGlobalFunctions B S hS X)

/-- The abelian group at the point detects zero objects. -/
theorem isZero_of_isZero_pointAddCommGrp_obj (M : (pointRingedTopos (CommRingCat.of R)).Modules)
    (hM : IsZero ((pointAddCommGrp (R := R)).obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply (pointAddCommGrp (R := R)).map_injective
  rw [CategoryTheory.Functor.map_id, Functor.map_zero]
  exact hM.eq_of_src _ _

/-- **An object of `D(pt, R)` lives in degrees `≤ c` as soon as its image in `D(Ab)` does.** -/
theorem isLE_of_isLE_pointAddCommGrp_mapDerivedCategory
    (K : DerivedCategory (pointRingedTopos (CommRingCat.of R)).Modules) (c : ℤ)
    (hK : ((pointAddCommGrp (R := R)).mapDerivedCategory.obj K).IsLE c) : K.IsLE c := by
  rw [DerivedCategory.isLE_iff] at hK ⊢
  intro i hi
  exact isZero_of_isZero_pointAddCommGrp_obj _
    ((hK i hi).of_iso
      ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        (pointAddCommGrp (R := R)) i).app K).symm)

/-- **An object of `D(pt, R)` lives in degrees `≥ a` as soon as its image in `D(Ab)` does.** -/
theorem isGE_of_isGE_pointAddCommGrp_mapDerivedCategory
    (K : DerivedCategory (pointRingedTopos (CommRingCat.of R)).Modules) (a : ℤ)
    (hK : ((pointAddCommGrp (R := R)).mapDerivedCategory.obj K).IsGE a) : K.IsGE a := by
  rw [DerivedCategory.isGE_iff] at hK ⊢
  intro i hi
  exact isZero_of_isZero_pointAddCommGrp_obj _
    ((hK i hi).of_iso
      ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        (pointAddCommGrp (R := R)) i).app K).symm)

section Transport

variable (Rf : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules ⥤
    DerivedCategory (pointRingedTopos (CommRingCat.of R)).Modules)
  (αf : (spacesEtaleModelToBaseRing B S hS X φ).pushforwardTopos.mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
  [Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso
      (spacesEtaleModelRingedTopos B S hS X).Modules (ComplexShape.up ℤ))]

include αf in
/-- **`Rf_*` to the point is uniformly bounded above on `D_QCoh`.** For `X` quasi-compact and
quasi-separated and `Rf_*` any right derived functor of the direct image to `(pt, R)`, there is
an integer `N` such that, for every `E` on the spaces-étale model whose image in `D(𝒪_X)` has
quasi-coherent cohomology and lives in degrees `≤ c`, `Rf_*E` lives in degrees `≤ c + N`. -/
theorem exists_isLE_rightDerived_spacesEtaleModelToBaseRing
    (hZ : B.Contains (⊤_ Scheme.{u})) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    ∃ N : ℤ, ∀ E : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules,
      qcohDerivedProp B S hS X
        ((spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory.obj E) →
      ∀ c : ℤ, ((spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory.obj E).IsLE c →
      (Rf.obj E).IsLE (c + N) := by
  let e := Stacks.DerivedGlueing.mapDerivedCategoryEquivalence
    (spacesEtaleModelModulesEquiv B S hS X).functor (spacesEtaleModelModulesEquiv B S hS X).inverse
    (spacesEtaleModelModulesEquiv B S hS X).unitIso
    (spacesEtaleModelModulesEquiv B S hS X).counitIso
  have := isRightDerivedFunctor_pointTransport B S hS X φ Rf αf
  obtain ⟨N, hN⟩ := exists_isLE_rightDerived_baseRingGlobalSections B S hS hZ hXqc hXqs φ _
    (pointTransportUnit B S hS X φ Rf αf)
  refine ⟨N, fun E hE c hc => isLE_of_isLE_pointAddCommGrp_mapDerivedCategory _ _ ?_⟩
  have : ((pointAddCommGrp (R := R)).mapDerivedCategory.obj
      (Rf.obj ((e.functor ⋙ e.inverse).obj E))).IsLE (c + N) := hN _ hE c hc
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((pointAddCommGrp (R := R)).mapDerivedCategory.mapIso
      (Rf.mapIso (e.unitIso.app E).symm)) (c + N)

include αf in
/-- **`Rf_*` to the point does not lower a lower bound.** If the image of `E` in `D(𝒪_X)` lives
in degrees `≥ a`, so does `Rf_*E`, for any right derived functor `Rf_*` of the direct image to
`(pt, R)`. -/
theorem isGE_rightDerived_spacesEtaleModelToBaseRing
    (E : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules) (a : ℤ)
    (hE : ((spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory.obj E).IsGE a) :
    (Rf.obj E).IsGE a := by
  let e := Stacks.DerivedGlueing.mapDerivedCategoryEquivalence
    (spacesEtaleModelModulesEquiv B S hS X).functor (spacesEtaleModelModulesEquiv B S hS X).inverse
    (spacesEtaleModelModulesEquiv B S hS X).unitIso
    (spacesEtaleModelModulesEquiv B S hS X).counitIso
  have := isGrothendieckAbelian_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS X.1 X.2
  have hres := exists_quasiIso_isKInjective_modules B S hS X.1 X.2
  have := isRightDerivedFunctor_pointTransport B S hS X φ Rf αf
  have hcomp : ∀ I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ, I.IsKInjective →
      IsIso ((pointTransportUnit B S hS X φ Rf αf).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := fun I hI ↦
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      ((baseRingGlobalSectionsAddCommGrp B S hS X φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) hres).2 DerivedCategory.Qh _ _ I hI
  have : ((pointAddCommGrp (R := R)).mapDerivedCategory.obj
      (Rf.obj ((e.functor ⋙ e.inverse).obj E))).IsGE a :=
    Stacks.SmallDerivedCategory.isGE_obj_of_isGE _ _ _ hcomp _ a hE
  exact isGE_of_isGE_pointAddCommGrp_mapDerivedCategory _ _
    (DerivedCategory.TStructure.t.isGE_of_iso
      ((pointAddCommGrp (R := R)).mapDerivedCategory.mapIso
        (Rf.mapIso (e.unitIso.app E).symm)) a)

end Transport

/-- **`Rf_*` to the point is uniformly bounded above on `D_QCoh`**, for the chosen derived direct
image `derivedPushforward`. -/
theorem exists_isLE_derivedPushforward_spacesEtaleModelToBaseRing
    (hZ : B.Contains (⊤_ Scheme.{u})) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    ∃ N : ℤ, ∀ E : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules,
      qcohDerivedProp B S hS X
        ((spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory.obj E) →
      ∀ c : ℤ, ((spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory.obj E).IsLE c →
      ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X φ)).obj E).IsLE (c + N) :=
  exists_isLE_rightDerived_spacesEtaleModelToBaseRing B S hS X φ _
    (derivedPushforwardUnit (spacesEtaleModelToBaseRing B S hS X φ)) hZ hXqc hXqs

/-- **`Rf_*` to the point does not lower a lower bound**, for the chosen derived direct image
`derivedPushforward`. -/
theorem isGE_derivedPushforward_spacesEtaleModelToBaseRing
    (E : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules) (a : ℤ)
    (hE : ((spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory.obj E).IsGE a) :
    ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X φ)).obj E).IsGE a :=
  isGE_rightDerived_spacesEtaleModelToBaseRing B S hS X φ _
    (derivedPushforwardUnit (spacesEtaleModelToBaseRing B S hS X φ)) E a hE

end AlgebraicGeometry.Space

end
