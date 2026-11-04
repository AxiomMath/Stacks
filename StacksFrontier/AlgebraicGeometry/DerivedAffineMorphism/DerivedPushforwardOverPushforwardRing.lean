module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.RestrictScalars
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardAnyModel
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative

/-!
# Derived direct image of modules over the direct image of the structure sheaf

Let `f : X ⟶ S` be a morphism of schemes.  Direct image of `𝒪_X`-modules factors through the
category of modules over the sheaf of rings `f_* 𝒪_X` on `S`, and the factorisation is an
equality of functors: `f_*` is the direct image over `f_* 𝒪_X` followed by restriction of
scalars along `𝒪_S ⟶ f_* 𝒪_X`.  This file derives that factorisation.

The functor `Φ` constructed here is the total right derived functor of direct image over
`f_* 𝒪_X`, computed by K-injective resolutions of complexes of `𝒪_X`-modules.  Restriction of
scalars is exact, so it induces a functor `D(f_* 𝒪_X) ⥤ D(𝒪_S)`, and the main result is that
`Φ` followed by that functor is `Rf_*`.  For an affine morphism, `Φ` carries `D_QCoh(𝒪_X)`
into `D_QCoh(f_* 𝒪_X)`, so it restricts to a functor between the quasi-coherent derived
categories.

## Main definitions

* `SheafOfModules.restrictScalarsCompToSheaf` — restriction of scalars leaves the underlying
  sheaf of abelian groups unchanged.
* `Stacks.AlgebraicGeometry.DerivedAffinePushforward.derivedPushforwardOverRing` — the functor
  `Φ : D(𝒪_X) ⥤ D(f_* 𝒪_X)`, with comparison map
  `derivedPushforwardOverRingUnit`.
* `Stacks.AlgebraicGeometry.DerivedAffinePushforward.derivedQuasicoherentPushforwardOverRing` —
  the restriction of `Φ` to a functor `D_QCoh(𝒪_X) ⥤ D_QCoh(f_* 𝒪_X)`, for `f` affine.

## Main results

* `SheafOfModules.preservesFiniteLimits_restrictScalars` and
  `SheafOfModules.preservesFiniteColimits_restrictScalars` — restriction of scalars between
  categories of sheaves of modules is exact.  Together with
  `SheafOfModules.preservesFiniteColimits_toSheaf` these are what make
  `CategoryTheory.Functor.mapDerivedCategory` available for restriction of scalars.
* `derivedPushforwardOverRingCompRestrictScalarsIso` — **the factorisation of `Rf_*`**: the
  composite of `Φ` with the functor `D(f_* 𝒪_X) ⥤ D(𝒪_S)` induced by restriction of scalars
  is `Rf_*`.
* `isQuasicoherent_homologyFunctor_derivedPushforwardOverRing_of_isAffineHom` — for an affine
  morphism, the cohomology sheaves of `Φ K` are quasi-coherent over `f_* 𝒪_X` whenever those
  of `K` are quasi-coherent over `𝒪_X`.

## Implementation notes

*The derived categories are instance arguments.*  Every statement mentioning a derived
category takes `[HasDerivedCategory.{w} _]` binders rather than pinning a model by a
file-level `attribute [local instance] HasDerivedCategory.standard`.  This matches
`AlgebraicGeometry.AnyModel.derivedPushforward`, the form of `Rf_*` used here, and is
forced: a statement proved at the standard model says nothing about the locally small model
of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, since `HasDerivedCategory`
carries the localized category as data.  The other inputs — the quasi-coherence of a scalar
restriction along an affine morphism, and the comparison of cohomology with an exact functor
— mention no model and a free model respectively, so all of them agree.

*The factorisation is derived from a definitional one.*  At the level of abelian categories
`Stacks.AlgebraicGeometry.AffineQcohPushforward.restrictScalars_pushforwardModules` is an
equality of functors holding by `rfl`.  The derived statement is not formal from it, because
`Rf_*` and `Φ` are separate total right derived functors; what makes it work is that the
composite of `Φ` with an *exact* functor is again a right derived functor, recognised by
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.isRightDerivedFunctor_of_isIso_app_isKInjective`
on the K-injective complexes, followed by the uniqueness of right derived functors.

*What of [Stacks, Tag 0AVW] this file records.*  The tag has two clauses: that `Φ` is an
*equivalence* onto `D_QCoh(f_* 𝒪_X)` for an affine morphism, and that composing it with
restriction of scalars gives `Rf_*`.  The declaration below states the second, for every
morphism of schemes and on the whole derived categories.  The equivalence clause is
`isEquivalence_derivedQuasicoherentPushforwardOverRing`, in
`QuasicoherentEquivalenceOverPushforwardRing.lean` of this directory, with quasi-inverse the
derived pullback `Lg^*` along the morphism of ringed spaces `g : (X, 𝒪_X) ⟶ (S, f_* 𝒪_X)`.

That morphism is `Stacks.AlgebraicGeometry.DerivedAffinePushforward.toPushforwardStructureSpace`,
and `Φ` is literally `Rg_*` (`derivedPushforwardOverRing_eq_derivedPushforward`; both are in
`StacksFrontier/AlgebraicGeometry/DerivedAffineMorphism/RingedSpaceOverPushforwardRing.lean`): the
structure map of `g` is the identity, so `g_*` on sheaves of modules is
`pushforwardModules f.base X.ringCatSheaf` on the nose and the two total right derived functors
are the same term, comparison maps included.

*What the factorisation already buys.*
`StacksFrontier/AlgebraicGeometry/DerivedAffineMorphism/PushforwardOverRingConservative.lean`
draws from it that restriction of scalars loses no information, so that `ΦE`, `H^i(ΦE)` and
`Φα` are zero or invertible exactly when `Rf_*E`, `H^i(Rf_*E)` and `Rf_*α` are.  That is the
step "`H^i(Φ(K)) = H^i(Rf_*K)`" of the source's proof.

## References

* [Stacks Project, Tag 0AVW](https://stacks.math.columbia.edu/tag/0AVW)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe v w u

namespace SheafOfModules

/-! ### Restriction of scalars is exact -/

section Exactness

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- The underlying sheaf of abelian groups of a sheaf of modules depends right exactly on the
module: sheafification of presheaves of modules is a left adjoint, and it commutes with
passing to the underlying abelian sheaf. -/
instance preservesFiniteColimits_toSheaf (R : Sheaf J RingCat.{v}) :
    PreservesFiniteColimits (toSheaf.{v} R) := by
  have hcomp : PreservesFiniteColimits
      (PresheafOfModules.sheafification.{v} (𝟙 R.obj) ⋙ toSheaf.{v} R) :=
    preservesFiniteColimits_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf.{v} (𝟙 R.obj)).symm
  have hadj := PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj)
  have : PreservesColimitsOfSize.{0, 0}
      (PresheafOfModules.sheafification.{v} (𝟙 R.obj)) := hadj.leftAdjoint_preservesColimits
  refine ⟨fun I _ _ => ⟨fun {D} => ?_⟩⟩
  have e : (D ⋙ forget.{v} R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)) ⋙
      PresheafOfModules.sheafification.{v} (𝟙 R.obj) ≅ D :=
    NatIso.ofComponents (fun i => (asIso hadj.counit).app (D.obj i))
      (fun g => (asIso hadj.counit).hom.naturality (D.map g))
  have h₁ : PreservesColimit (D ⋙ forget.{v} R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj))
      (PresheafOfModules.sheafification.{v} (𝟙 R.obj) ⋙ toSheaf.{v} R) :=
    (hcomp.preservesFiniteColimits I).preservesColimit
  have h₂ : PreservesColimit
      ((D ⋙ forget.{v} R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)) ⋙
        PresheafOfModules.sheafification.{v} (𝟙 R.obj)) (toSheaf.{v} R) := by
    refine preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves (PresheafOfModules.sheafification.{v} (𝟙 R.obj))
        (colimit.isColimit _)) ?_
    exact isColimitOfPreserves
      (PresheafOfModules.sheafification.{v} (𝟙 R.obj) ⋙ toSheaf.{v} R) (colimit.isColimit _)
  exact preservesColimit_of_iso_diagram _ e

variable {R R' : Sheaf J RingCat.{v}} (α : R ⟶ R')

omit [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}] in
/-- Restriction of scalars leaves the underlying sheaf of abelian groups untouched: an
`R'`-module and the `R`-module it restricts to have the same sections and the same restriction
maps. -/
theorem restrictScalarsCompToSheaf :
    restrictScalars.{v} α ⋙ toSheaf.{v} R = toSheaf.{v} R' :=
  rfl

/-- Restriction of scalars between categories of sheaves of modules is left exact: it does not
change the underlying sheaf of abelian groups, and a finite limit of sheaves of modules is
detected on the underlying abelian sheaves. -/
instance preservesFiniteLimits_restrictScalars :
    PreservesFiniteLimits (restrictScalars.{v} α) := by
  have : PreservesFiniteLimits (restrictScalars.{v} α ⋙ toSheaf.{v} R) :=
    preservesFiniteLimits_of_natIso (eqToIso (restrictScalarsCompToSheaf.{v} α)).symm
  have : ReflectsFiniteLimits (toSheaf.{v} R) := { reflects := fun _ _ _ => inferInstance }
  exact preservesFiniteLimits_of_reflects_of_preserves _ (toSheaf.{v} R)

/-- Restriction of scalars between categories of sheaves of modules is right exact, by the same
argument as its left exactness. -/
instance preservesFiniteColimits_restrictScalars :
    PreservesFiniteColimits (restrictScalars.{v} α) := by
  have : PreservesFiniteColimits (restrictScalars.{v} α ⋙ toSheaf.{v} R) :=
    preservesFiniteColimits_of_natIso (eqToIso (restrictScalarsCompToSheaf.{v} α)).symm
  have : ReflectsFiniteColimits (toSheaf.{v} R) := { reflects := fun _ _ _ => inferInstance }
  exact preservesFiniteColimits_of_reflects_of_preserves _ (toSheaf.{v} R)

end Exactness

end SheafOfModules

namespace Stacks.AlgebraicGeometry.DerivedAffinePushforward

open Stacks.AlgebraicGeometry.AffineQcohPushforward
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (isRightDerivedFunctor_of_isIso_app_isKInjective)

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Direct image of `𝒪_X`-modules over `f_* 𝒪_X` is additive: it leaves the sectionwise
addition of morphisms alone. -/
instance pushforwardModules_additive :
    (pushforwardModules.{u} f.base X.ringCatSheaf).Additive where
  map_add := rfl

/-- Restriction of scalars along `𝒪_S ⟶ f_* 𝒪_X`, the functor from modules over `f_* 𝒪_X` to
`𝒪_S`-modules through which direct image factors. -/
abbrev scalarRestriction : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf) ⥤
    SheafOfModules.{u} S.ringCatSheaf :=
  SheafOfModules.restrictScalars f.toRingCatSheafHom

/-- Restriction of scalars along `𝒪_S ⟶ f_* 𝒪_X` is additive: it leaves the sectionwise
addition of morphisms alone. -/
instance scalarRestriction_additive : (scalarRestriction f).Additive where
  map_add := rfl

/-- Restriction of scalars along `𝒪_S ⟶ f_* 𝒪_X` is left exact. -/
instance scalarRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (scalarRestriction f) :=
  SheafOfModules.preservesFiniteLimits_restrictScalars.{u} _

/-- Restriction of scalars along `𝒪_S ⟶ f_* 𝒪_X` is right exact. -/
instance scalarRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (scalarRestriction f) :=
  SheafOfModules.preservesFiniteColimits_restrictScalars.{u} _

/-- The factorisation of direct image through modules over `f_* 𝒪_X`, in the spelling of
`𝒪_X`-modules used for the derived direct image.  This is
`Stacks.AlgebraicGeometry.AffineQcohPushforward.restrictScalars_pushforwardModules`, read
across the two definitionally equal spellings of direct image. -/
theorem pushforwardModules_comp_scalarRestriction :
    pushforwardModules.{u} f.base X.ringCatSheaf ⋙ scalarRestriction f =
      AlgebraicGeometry.pushforwardSheafOfModules f :=
  rfl

/-- The factorisation of direct image through modules over `f_* 𝒪_X`, as an isomorphism of
functors whose target carries the additivity instance the homotopy categories consume. -/
abbrev pushforwardModulesCompScalarRestrictionIso :
    pushforwardModules.{u} f.base X.ringCatSheaf ⋙ scalarRestriction f ≅
      AlgebraicGeometry.pushforwardSheafOfModules f :=
  Iso.refl _

section Derived

variable [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))]

/-- Degreewise direct image over `f_* 𝒪_X`, read in a chosen derived category of modules over
`f_* 𝒪_X`. -/
abbrev pushforwardOverRingToDerivedCategory :
    HomotopyCategory (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) :=
  (pushforwardModules.{u} f.base X.ringCatSheaf).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- K-injective resolutions compute the derived direct image over `f_* 𝒪_X` pointwise: the
criterion asks only for the existence of K-injective resolutions of complexes of
`𝒪_X`-modules. -/
instance pushforwardOverRing_hasPointwiseRightDerivedFunctor :
    (pushforwardOverRingToDerivedCategory.{w} f).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, w, w, u + 1, u + 1, u + 1}
      (pushforwardOverRingToDerivedCategory.{w} f)
      (AlgebraicGeometry.exists_quasiIso_isKInjective_ringCatSheaf X)).1

/-- The derived direct image over `f_* 𝒪_X` exists. -/
instance pushforwardOverRing_hasRightDerivedFunctor :
    (pushforwardOverRingToDerivedCategory.{w} f).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)) :=
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

/-- **The functor `Φ` of [Stacks, Tag 0AVW]**: the total right derived functor of direct image
over `f_* 𝒪_X`, a functor `D(𝒪_X) ⥤ D(f_* 𝒪_X)`.  On an object represented by a complex `K` it
is the complex `f_* I` for a K-injective resolution `K ⟶ I`, read as a complex of
`f_* 𝒪_X`-modules. -/
abbrev derivedPushforwardOverRing :
    DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) :=
  (pushforwardOverRingToDerivedCategory.{w} f).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))

/-- The canonical comparison from degreewise direct image over `f_* 𝒪_X` to `Φ`. -/
abbrev derivedPushforwardOverRingUnit :
    pushforwardOverRingToDerivedCategory.{w} f ⟶
      DerivedCategory.Qh ⋙ derivedPushforwardOverRing.{w} f :=
  (pushforwardOverRingToDerivedCategory.{w} f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))

/-- A K-injective complex computes `Φ`: on it the canonical comparison `f_* I ⟶ Φ I` of
`f_* 𝒪_X`-modules is invertible. -/
theorem isIso_derivedPushforwardOverRingUnit_app_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedPushforwardOverRingUnit.{w} f).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} X.ringCatSheaf)
        (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, w, w, u + 1, u + 1, u + 1}
      (pushforwardOverRingToDerivedCategory.{w} f)
      (AlgebraicGeometry.exists_quasiIso_isKInjective_ringCatSheaf X)).2
    DerivedCategory.Qh (derivedPushforwardOverRing.{w} f)
    (derivedPushforwardOverRingUnit.{w} f) I hI

end Derived

/-! ### The factorisation of the derived direct image -/

section Factorisation

variable [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)]

/-- The identification of degreewise direct image, localized to `D(𝒪_S)`, with degreewise
direct image over `f_* 𝒪_X` followed by the functor induced on derived categories by
restriction of scalars.  It is the definitional factorisation of direct image, together with
the identification of the induced functor with degreewise restriction of scalars. -/
abbrev derivedFactorisationComparison :
    AlgebraicGeometry.AnyModel.pushforwardToDerivedCategory.{w} f ≅
      pushforwardOverRingToDerivedCategory.{w} f ⋙ (scalarRestriction f).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso (pushforwardModulesCompScalarRestrictionIso f)
        (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (scalarRestriction f).mapDerivedCategoryFactorsh.symm ≪≫
    (Functor.associator _ _ _).symm

/-- The comparison exhibiting `Φ` followed by the derived restriction of scalars as a right
derived functor of degreewise direct image: it is the comparison map of `Φ`, pushed through
restriction of scalars and corrected by `derivedFactorisationComparison`. -/
abbrev derivedFactorisationUnit :
    AlgebraicGeometry.AnyModel.pushforwardToDerivedCategory.{w} f ⟶
      DerivedCategory.Qh ⋙
        (derivedPushforwardOverRing.{w} f ⋙ (scalarRestriction f).mapDerivedCategory) :=
  (derivedFactorisationComparison.{w} f).hom ≫
    Functor.whiskerRight (derivedPushforwardOverRingUnit.{w} f)
      (scalarRestriction f).mapDerivedCategory ≫
    (Functor.associator _ _ _).hom

/-- `Φ` followed by the functor `D(f_* 𝒪_X) ⥤ D(𝒪_S)` induced by restriction of scalars is a
right derived functor of degreewise direct image: its comparison map is invertible on the
K-injective complexes, because the comparison map of `Φ` is and restriction of scalars is
exact. -/
theorem isRightDerivedFunctor_derivedPushforwardOverRing_comp :
    (derivedPushforwardOverRing.{w} f ⋙ (scalarRestriction f).mapDerivedCategory
      ).IsRightDerivedFunctor (derivedFactorisationUnit.{w} f)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)) := by
  refine isRightDerivedFunctor_of_isIso_app_isKInjective.{u, w, w, u + 1, u + 1, u + 1}
    (AlgebraicGeometry.AnyModel.pushforwardToDerivedCategory.{w} f)
    (AlgebraicGeometry.exists_quasiIso_isKInjective_ringCatSheaf X)
    DerivedCategory.Qh _ _ (fun I hI => ?_)
  have := isIso_derivedPushforwardOverRingUnit_app_of_isKInjective.{w} f I hI
  simp only [derivedFactorisationUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id]
  infer_instance

/-- **The factorisation asserted by [Stacks, Tag 0AVW]**: the derived direct image `Rf_*` is
`Φ` followed by the functor `D(f_* 𝒪_X) ⥤ D(𝒪_S)` induced by restriction of scalars along
`𝒪_S ⟶ f_* 𝒪_X`.  Both functors are right derived functors of degreewise direct image, so they
agree by the uniqueness of right derived functors.

This is the second of the tag's two clauses, and the attribute carries a phrase naming it.  The
first clause — that `Φ` is an *equivalence* onto `D_QCoh(f_* 𝒪_X)` for `f` affine — is
`isEquivalence_derivedQuasicoherentPushforwardOverRing`.  The factorisation below holds for every
morphism of schemes, with no affineness needed, and is read on the whole derived categories
rather than on the quasi-coherent ones, so it is stronger than the source's clause on both
counts. -/
@[stacks 0AVW "the factorisation of Rf_* through D(f_*𝒪_X); the equivalence clause is proved in isEquivalence_derivedQuasicoherentPushforwardOverRing (QuasicoherentEquivalenceOverPushforwardRing.lean), on the whole derived categories"]
def derivedPushforwardOverRingCompRestrictScalarsIso :
    AlgebraicGeometry.AnyModel.derivedPushforward.{w} f ≅
      derivedPushforwardOverRing.{w} f ⋙ (scalarRestriction f).mapDerivedCategory :=
  have := isRightDerivedFunctor_derivedPushforwardOverRing_comp.{w} f
  Functor.rightDerivedNatIso _ _ (AlgebraicGeometry.AnyModel.derivedPushforwardUnit.{w} f)
    (derivedFactorisationUnit.{w} f)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))
    (Iso.refl _)

/-! ### Quasi-coherence -/

/-- **`Φ` carries `D_QCoh(𝒪_X)` into `D_QCoh(f_* 𝒪_X)`.**  Let `f` be affine and let `E` have
quasi-coherent cohomology sheaves.  Then the cohomology sheaves of `Φ E` are quasi-coherent as
modules over `f_* 𝒪_X`.

Restriction of scalars commutes with cohomology, being exact, so the scalar restriction of
`H^i(Φ E)` is `H^i(Rf_* E)`, which is quasi-coherent by part (1) of [Stacks, Tag 08D5] for an
affine morphism; quasi-coherence then descends through the scalar restriction by
[Stacks, Tag 01SB]. -/
theorem isQuasicoherent_homologyFunctor_derivedPushforwardOverRing_of_isAffineHom
    [IsAffineHom f] (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) i).obj E).IsQuasicoherent) (i : ℤ) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) i).obj
        ((derivedPushforwardOverRing.{w} f).obj E)).IsQuasicoherent := by
  rw [← Stacks.AlgebraicGeometry.QcohLimits.affine_isQuasicoherent_restrictScalars_iff f]
  refine (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf) i).mapIso
        ((derivedPushforwardOverRingCompRestrictScalarsIso.{w} f).app E) ≪≫
      ((scalarRestriction f).mapDerivedCategoryCompHomologyFunctorIso i).app
        ((derivedPushforwardOverRing.{w} f).obj E))
    (AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom
      f E hcoh i)

/-- **`Φ` as a functor between the quasi-coherent derived categories**, for `f` affine: the
restriction of `Φ : D(𝒪_X) ⥤ D(f_* 𝒪_X)` to the full subcategories of objects with
quasi-coherent cohomology. -/
def derivedQuasicoherentPushforwardOverRing [IsAffineHom f] :
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent
        (pushforwardRing f.base X.ringCatSheaf))).FullSubcategory :=
  ObjectProperty.lift _
    (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)) ⋙
      derivedPushforwardOverRing.{w} f)
    (fun E i => isQuasicoherent_homologyFunctor_derivedPushforwardOverRing_of_isAffineHom.{w}
      f E.obj E.property i)

end Factorisation

end Stacks.AlgebraicGeometry.DerivedAffinePushforward

end
