module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.QcohUniversalDeltaFunctor
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.BoundedBelowComparison
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDiagonalEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.QuasicoherentComplexDevissage
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffineDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffineOpenPushforwardAcyclic
public import
  StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsDerivedQuasicoherentPushforward

/-!
# Direct image and the coherator

Let `f : X ⟶ Y` be a morphism of schemes and let `Φ : D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))` be a total
right derived functor of `f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`. [Stacks, Tag 0CRX] asserts that the
square

```
D(QCoh(𝒪_X)) --i_X--> D_QCoh(𝒪_X)
     | Φ                  | Rf_*
     v                     v
D(QCoh(𝒪_Y)) --i_Y--> D_QCoh(𝒪_Y)
```

commutes, the horizontal arrows being the comparison functor of [Stacks, Tag 06VT].

The proof is the source's. The canonical map `Φ(K) ⟶ Rf_*(K)` is the transformation
`Φ ⋙ D(ι_Y) ⟶ D(ι_X) ⋙ Rf_*` induced by `f_* ⟶ Rf_*` through the universal property of the right
derived functor `Φ ⋙ D(ι_Y)`; the derived inclusion `D(ι_Y)` is a left adjoint, so it preserves
that universal property. Both sides are triangulated, so the dévissage
`Stacks.DerivedQCoh.isIso_natTrans_of_isIso_app_quasicoherentPushforward` reduces invertibility to
the complexes `j_*𝒢^•` for `j : U ⟶ X` the inclusion of an affine open. There `𝒢^•` may be taken
K-injective in `QCoh(𝒪_U)`, `j_*` being exact on quasi-coherent modules; then `j_*𝒢^•` is
K-injective in `QCoh(𝒪_X)` because `j_*` has the exact left adjoint `j^*` ([Stacks, Tag 08BJ]), so
`Φ` is computed on it by `f_*`, and `f_*j_*𝒢^• ⟶ Rf_*j_*𝒢^•` is invertible because `j` and
`g = j ≫ f` are affine morphisms
(`AlgebraicGeometry.AnyModel.isIso_derivedPushforwardUnit_app_pushforward_of_isAffineHom`).

For an affine morphism `f` the square holds with no hypothesis on `X` and `Y`: pushforward along
an affine morphism is exact on quasi-coherent modules, so the functor it induces on derived
categories is a total right derived functor of it, and the square for that model is the commuting
square of [Stacks, Tag 08D7], `AlgebraicGeometry.derivedQuasicoherentComparisonSquare`.

## Main definitions

* `AlgebraicGeometry.derivedPushforwardComparison` — the canonical map `Φ(K) ⟶ Rf_*(K)`, read in
  `D(𝒪_Y)`.
* `AlgebraicGeometry.derivedQuasicoherentComparisonSquareOfAffineDiagonal` — **the commuting
  square of [Stacks, Tag 0CRX]**, for `X` and `Y` quasi-compact with affine diagonal, an
  arbitrary `f : X ⟶ Y` and an arbitrary total right derived functor `Φ` of `f_*`.
* `AlgebraicGeometry.derivedQuasicoherentComparisonSquareOfIsRightDerivedFunctor` — the square
  for an affine morphism, with no hypothesis on `X` and `Y`.
* `AlgebraicGeometry.chosenDerivedQuasicoherentComparisonSquareOfAffineDiagonal` and
  `AlgebraicGeometry.specMapDerivedQuasicoherentComparisonSquare` — the squares at named models
  of `Φ`.

## Main results

* `AlgebraicGeometry.isIso_derivedPushforwardComparison` — **[Stacks, Tag 0CRX]**: the
  canonical map `Φ(K) ⟶ Rf_*(K)` is an isomorphism for every `K`.

## Implementation notes

The tag says "denoting `Φ` the right derived functor of `f_*`", which pins `Φ` only up to
canonical isomorphism. Taking `Φ` together with its derivation unit `ηΦ` and the universal
property as arguments states the square for every model at once.

## References

* [Stacks Project, Tag 0CRX](https://stacks.math.columbia.edu/tag/0CRX)
* [Stacks Project, Tag 08D7](https://stacks.math.columbia.edu/tag/08D7)
* [Stacks Project, Tag 08DB](https://stacks.math.columbia.edu/tag/08DB)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory
open Stacks.AlgebraicGeometry.QuasicoherentDerived

namespace AlgebraicGeometry

universe u

/-- **The square of [Stacks, Tag 0CRX] for an affine morphism.** Let `f : X ⟶ Y` be an affine
morphism of schemes and let `Φ`, with derivation unit `ηΦ`, be a total right derived functor of
`f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`. Then the square formed by `Φ`, by the restriction
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of the unbounded derived direct image, and by the comparison
functors of [Stacks, Tag 06VT] commutes.

Pushforward along an affine morphism is exact on quasi-coherent modules, so
`CategoryTheory.Functor.mapDerivedCategory` of it is itself a total right derived functor of it
(`AlgebraicGeometry.isRightDerivedFunctor_quasicoherentPushforward_mapDerivedCategory`); the
square for that model is `AlgebraicGeometry.derivedQuasicoherentComparisonSquare`, and
`CategoryTheory.Functor.rightDerivedUnique` transports it to `Φ`. -/
def derivedQuasicoherentComparisonSquareOfIsRightDerivedFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f]
    (Φ : DerivedCategory (Scheme.QuasicoherentModules X) ⥤
      DerivedCategory (Scheme.QuasicoherentModules Y))
    (ηΦ : (quasicoherentPushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh (C := Scheme.QuasicoherentModules Y) ⟶
      DerivedCategory.Qh (C := Scheme.QuasicoherentModules X) ⋙ Φ)
    [Φ.IsRightDerivedFunctor ηΦ
      (HomotopyCategory.quasiIso (Scheme.QuasicoherentModules X) (ComplexShape.up ℤ))] :
    derivedQuasicoherentComparison.{u} X ⋙ derivedQuasicoherentPushforward f ≅
      Φ ⋙ derivedQuasicoherentComparison.{u} Y :=
  derivedQuasicoherentComparisonSquare f ≪≫
    Functor.isoWhiskerRight
      (Functor.rightDerivedUnique (quasicoherentPushforward f).mapDerivedCategory Φ
        (quasicoherentPushforward f).mapDerivedCategoryFactorsh.inv ηΦ
        (HomotopyCategory.quasiIso (Scheme.QuasicoherentModules X) (ComplexShape.up ℤ)))
      (derivedQuasicoherentComparison.{u} Y)

/-- **The square of [Stacks, Tag 0CRX] for the inclusion of an affine open.** Let `X` be a
scheme with affine diagonal, let `U ⊆ X` be an affine open with inclusion `j : U ⟶ X`, and let
`Φ`, with derivation unit `ηΦ`, be a total right derived functor of
`j_* : QCoh(𝒪_U) ⥤ QCoh(𝒪_X)`. Then the square of [Stacks, Tag 0CRX] for `j` commutes.

Affineness of the diagonal makes `j` an affine morphism; that is the case of [Stacks, Tag 01SG]
recorded, without an attribute, as
`Stacks.Cohomology.QcohDelta.isAffineHom_ι_of_isAffineOpen`, so
`AlgebraicGeometry.derivedQuasicoherentComparisonSquareOfIsRightDerivedFunctor` applies. The
hypothesis of [Stacks, Tag 09T6] is this square for every affine open of `X`. -/
def affineOpenDerivedQuasicoherentComparisonSquare (X : Scheme.{u})
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    (U : X.Opens) (hU : IsAffineOpen U) :
    haveI := Stacks.Cohomology.QcohDelta.isAffineHom_ι_of_isAffineOpen X U hU
    ∀ (Φ : DerivedCategory (Scheme.QuasicoherentModules U.toScheme) ⥤
        DerivedCategory (Scheme.QuasicoherentModules X))
      (ηΦ : (quasicoherentPushforward U.ι).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh (C := Scheme.QuasicoherentModules X) ⟶
        DerivedCategory.Qh (C := Scheme.QuasicoherentModules U.toScheme) ⋙ Φ)
      [Φ.IsRightDerivedFunctor ηΦ
        (HomotopyCategory.quasiIso (Scheme.QuasicoherentModules U.toScheme)
          (ComplexShape.up ℤ))],
      derivedQuasicoherentComparison.{u} U.toScheme ⋙ derivedQuasicoherentPushforward U.ι ≅
        Φ ⋙ derivedQuasicoherentComparison.{u} X :=
  haveI := Stacks.Cohomology.QcohDelta.isAffineHom_ι_of_isAffineOpen X U hU
  fun Φ ηΦ _ => derivedQuasicoherentComparisonSquareOfIsRightDerivedFunctor U.ι Φ ηΦ

/-! ### The parameter block of the square is inhabited -/

/-- **The square above at a named morphism and a named model of `Φ`.** For `φ : R ⟶ S` a
homomorphism of commutative rings, `Spec φ` is an affine morphism, and the functor induced on
derived categories by `(Spec φ)_*` on quasi-coherent modules is a total right derived functor of
it with `CategoryTheory.Functor.mapDerivedCategoryFactorsh.inv` for a derivation unit
(`AlgebraicGeometry.isRightDerivedFunctor_quasicoherentPushforward_mapDerivedCategory`). So the
triple `(Φ, ηΦ, Φ.IsRightDerivedFunctor ηΦ …)` that
`AlgebraicGeometry.derivedQuasicoherentComparisonSquareOfIsRightDerivedFunctor` takes as a
parameter has a named inhabitant.

The square is not vacuous for a second reason: its source `D(QCoh(𝒪_{Spec S}))` is equivalent to
the unbounded derived category of `S`-modules, by `Stacks.DerivedQCoh.derivedTildeEquiv`, so it
is not a derived category of the zero category.

-/
public def specMapDerivedQuasicoherentComparisonSquare {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    derivedQuasicoherentComparison.{u} (Spec S) ⋙ derivedQuasicoherentPushforward (Spec.map φ) ≅
      (quasicoherentPushforward (Spec.map φ)).mapDerivedCategory ⋙
        derivedQuasicoherentComparison.{u} (Spec R) :=
  derivedQuasicoherentComparisonSquareOfIsRightDerivedFunctor (Spec.map φ)
    (quasicoherentPushforward (Spec.map φ)).mapDerivedCategory
    (quasicoherentPushforward (Spec.map φ)).mapDerivedCategoryFactorsh.inv

/-! ### The square for an arbitrary morphism -/

section General

open AlgebraicGeometry.AnyModel (derivedPushforward derivedPushforwardUnit)

attribute [local instance] quasiSeparatedSpace_of_isAffineHom_diagonal

variable {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
  [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
  [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Y))] (f : X ⟶ Y)

/-- **The comparison `f_* ⟶ Rf_*` on `K(QCoh(𝒪_X))`.** For a complex `𝓕^•` of quasi-coherent
`𝒪_X`-modules, the map `f_*𝓕^• ⟶ Rf_*𝓕^•` in `D(𝒪_Y)`: the derived inclusion of
`f_*𝓕^•` is the termwise direct image of the inclusion of `𝓕^•`, and the canonical comparison
of the derived direct image of all modules goes from there to `Rf_*`. -/
def quasicoherentPushforwardComparison :
    ((quasicoherentPushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) ⋙
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapDerivedCategory ⟶
    DerivedCategory.Qh ⋙
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory ⋙
        derivedPushforward.{u} f :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((quasicoherentPushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapDerivedCategoryFactorsh.hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso
          (Iso.refl (quasicoherentPushforward f ⋙
            (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι)) (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso (quasicoherentPushforwardCompιIso f).symm
          (ComplexShape.up ℤ)).symm).hom
      DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedPushforwardUnit.{u} f) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategoryFactorsh.inv
      (derivedPushforward.{u} f) ≫
    (Functor.associator _ _ _).hom

variable (Φ : DerivedCategory (Scheme.QuasicoherentModules X) ⥤
      DerivedCategory (Scheme.QuasicoherentModules Y))
    (ηΦ : (quasicoherentPushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh (C := Scheme.QuasicoherentModules Y) ⟶
      DerivedCategory.Qh (C := Scheme.QuasicoherentModules X) ⋙ Φ)
    [Φ.IsRightDerivedFunctor ηΦ
      (HomotopyCategory.quasiIso (Scheme.QuasicoherentModules X) (ComplexShape.up ℤ))]

/-- The derivation unit of `Φ` followed by the derived inclusion of the quasi-coherent
`𝒪_Y`-modules. That inclusion is a left adjoint, so this exhibits `Φ ⋙ D(ι)` as a total right
derived functor of `f_*` followed by `D(ι)`. -/
abbrev derivedInclusionUnit :
    ((quasicoherentPushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) ⋙
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapDerivedCategory ⟶
    DerivedCategory.Qh ⋙
      (Φ ⋙ (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapDerivedCategory) :=
  Functor.whiskerRight ηΦ (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapDerivedCategory ≫
    (Functor.associator _ _ _).hom

/-- `Φ` followed by the derived inclusion of the quasi-coherent `𝒪_Y`-modules is a total right
derived functor of `f_*` followed by that inclusion, with derivation unit
`AlgebraicGeometry.derivedInclusionUnit`. -/
instance isRightDerivedFunctor_comp_mapDerivedCategory :
    (Φ ⋙ (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapDerivedCategory).IsRightDerivedFunctor
      (derivedInclusionUnit f Φ ηΦ)
      (HomotopyCategory.quasiIso (Scheme.QuasicoherentModules X) (ComplexShape.up ℤ)) :=
  haveI := (Stacks.DerivedQCoh.coheratorDerivedAdjunction Y).isLeftAdjoint
  inferInstance

/-- **The canonical map `Φ(K) ⟶ Rf_*(K)` of the proof of [Stacks, Tag 0CRX]**, read in
`D(𝒪_Y)`: the transformation `Φ ⋙ D(ι_Y) ⟶ D(ι_X) ⋙ Rf_*` induced, by the universal property of
the right derived functor `Φ ⋙ D(ι_Y)`, by the comparison `f_* ⟶ Rf_*` on complexes of
quasi-coherent modules. -/
def derivedPushforwardComparison :
    Φ ⋙ (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapDerivedCategory ⟶
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory ⋙
        derivedPushforward.{u} f :=
  (Φ ⋙ (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapDerivedCategory).rightDerivedDesc
    (derivedInclusionUnit f Φ ηΦ)
    (HomotopyCategory.quasiIso (Scheme.QuasicoherentModules X) (ComplexShape.up ℤ)) _
    (quasicoherentPushforwardComparison f)

/-- **The comparison is invertible on a complex pushed forward from an affine open.** Let
`j : U ⟶ X` be the inclusion of an affine open and `𝒢^•` a complex of quasi-coherent
`𝒪_U`-modules. Replacing `𝒢^•` by a K-injective resolution `ℐ^•` in `QCoh(𝒪_U)` changes
nothing, `j_*` being exact on quasi-coherent modules; `j_*ℐ^•` is K-injective in `QCoh(𝒪_X)`
because `j_*` has the exact left adjoint `j^*` ([Stacks, Tag 08BJ]), so `Φ` is computed on it by
`f_*`; and `f_*j_*ℐ^• ⟶ Rf_*j_*ℐ^•` is invertible by
`AlgebraicGeometry.AnyModel.isIso_derivedPushforwardUnit_app_pushforward_of_isAffineHom`, `j`
and `j ≫ f` being affine morphisms. -/
theorem isIso_derivedPushforwardComparison_app_quasicoherentPushforward
    (U : X.Opens) (hU : IsAffineOpen U) :
    haveI := Stacks.Cohomology.QcohDelta.isAffineHom_ι_of_isAffineOpen X U hU
    ∀ K : CochainComplex (Scheme.QuasicoherentModules U.toScheme) ℤ,
      IsIso ((derivedPushforwardComparison f Φ ηΦ).app (DerivedCategory.Q.obj
        (((quasicoherentPushforward U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) := by
  have := Stacks.Cohomology.QcohDelta.isAffineHom_ι_of_isAffineOpen X U hU
  have : IsAffine U.toScheme := hU
  have : IsAffineHom (U.ι ≫ f) := isAffineHom_of_isAffine_of_affineDiagonal (U.ι ≫ f)
  intro K
  let jC := (quasicoherentPushforward U.ι).mapHomologicalComplex (ComplexShape.up ℤ)
  obtain ⟨I, g, hI, hg⟩ := Stacks.DerivedQCoh.exists_quasiIso_isKInjective_quasicoherentModules
    U.toScheme K
  have : QuasiIso (jC.map g) := inferInstance
  refine ((derivedPushforwardComparison f Φ ηΦ).isIso_app_iff_of_iso
    (asIso (DerivedCategory.Q.map (jC.map g)))).2 ?_
  have hjI : CochainComplex.IsKInjective (jC.obj I) :=
    @CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _ _ _ _ _
      (quasicoherentPushforward U.ι) (Stacks.DerivedQCoh.quasicoherentRestrict U) _ _
      (Stacks.DerivedQCoh.quasicoherentRestrictPushforwardAdjunction U) _ _ I hI
  let Kh := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (jC.obj I)
  refine ((derivedPushforwardComparison f Φ ηΦ).isIso_app_iff_of_iso
    ((DerivedCategory.quotientCompQhIso _).app (jC.obj I))).1 ?_
  have hηΦ : IsIso (ηΦ.app Kh) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      ((quasicoherentPushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh)
      (Stacks.DerivedQCoh.exists_quasiIso_isKInjective_quasicoherentModules X)).2
      DerivedCategory.Qh Φ ηΦ (jC.obj I) hjI
  have hfac :=
    (Φ ⋙ (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapDerivedCategory).rightDerived_fac_app
      (derivedInclusionUnit f Φ ηΦ)
      (HomotopyCategory.quasiIso (Scheme.QuasicoherentModules X) (ComplexShape.up ℤ)) _
      (quasicoherentPushforwardComparison f) Kh
  have hunit : IsIso ((derivedInclusionUnit f Φ ηΦ).app Kh) := by
    simp only [derivedInclusionUnit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Category.comp_id]
    infer_instance
  have hRf : IsIso ((derivedPushforwardUnit.{u} f).app
      (((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomotopyCategory
        (ComplexShape.up ℤ)).obj Kh)) := by
    refine ((derivedPushforwardUnit.{u} f).isIso_app_iff_of_iso
      (((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).app (jC.obj I) ≪≫
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
          ((NatIso.mapHomologicalComplex (quasicoherentPushforwardCompιIso U.ι)
            (ComplexShape.up ℤ)).app I))).2 ?_
    exact AnyModel.isIso_derivedPushforwardUnit_app_pushforward_of_isAffineHom U.ι f
      (isFlat_toShHom_opensι X U)
      (((SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) (fun n => (I.X n).2)
  have hβ : IsIso ((quasicoherentPushforwardComparison f).app Kh) := by
    simp only [quasicoherentPushforwardComparison, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app]
    infer_instance
  exact (isIso_comp_left_iff ((derivedInclusionUnit f Φ ηΦ).app Kh) _).1 (hfac.symm ▸ hβ)

/-- **The canonical map `Φ(K) ⟶ Rf_*(K)` is an isomorphism for every `K`.** This is the content
of [Stacks, Tag 0CRX]. Both functors are triangulated — `Φ` and `Rf_*` because they are right
derived functors on Grothendieck abelian categories
(`Stacks.DerivedAcyclic.isTriangulated_of_isRightDerivedFunctor`), and the derived inclusions
because the inclusions are exact — so the dévissage
`Stacks.DerivedQCoh.isIso_natTrans_of_isIso_app_quasicoherentPushforward` reduces the claim to
complexes pushed forward from an affine open, where it is
`AlgebraicGeometry.isIso_derivedPushforwardComparison_app_quasicoherentPushforward`. -/
@[stacks 0CRX "the canonical map Φ(K) ⟶ Rf_*(K) is an isomorphism for every K"]
theorem isIso_derivedPushforwardComparison : IsIso (derivedPushforwardComparison f Φ ηΦ) := by
  let := Functor.IsRightDerivedFunctor.commShift Φ ηΦ
    (HomotopyCategory.quasiIso (Scheme.QuasicoherentModules X) (ComplexShape.up ℤ)) ℤ
  have : Φ.IsTriangulated :=
    Stacks.DerivedAcyclic.isTriangulated_of_isRightDerivedFunctor (quasicoherentPushforward f) Φ ηΦ
  have : (derivedPushforward.{u} f).IsTriangulated :=
    Stacks.DerivedAcyclic.isTriangulated_of_isRightDerivedFunctor (pushforwardSheafOfModules f)
      (derivedPushforward.{u} f) (derivedPushforwardUnit.{u} f)
  exact Stacks.DerivedQCoh.isIso_natTrans_of_isIso_app_quasicoherentPushforward _
    (isIso_derivedPushforwardComparison_app_quasicoherentPushforward f Φ ηΦ)

/-- **The comparison is the one induced by `f_* ⟶ Rf_*`**: composed with the derivation unit of
`Φ`, it is the comparison `f_* ⟶ Rf_*` on complexes of quasi-coherent modules. This is the
universal property that defines it, and by `CategoryTheory.Functor.rightDerived_ext` it is the
only transformation with this property. -/
theorem derivedPushforwardComparison_fac :
    derivedInclusionUnit f Φ ηΦ ≫
        Functor.whiskerLeft DerivedCategory.Qh (derivedPushforwardComparison f Φ ηΦ) =
      quasicoherentPushforwardComparison f :=
  (Φ ⋙ (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapDerivedCategory).rightDerived_fac
    (derivedInclusionUnit f Φ ηΦ)
    (HomotopyCategory.quasiIso (Scheme.QuasicoherentModules X) (ComplexShape.up ℤ)) _
    (quasicoherentPushforwardComparison f)

/-- **The square for quasi-compact schemes with affine diagonal.** Let `f : X ⟶ Y` be a morphism
of schemes, with `X` and `Y` quasi-compact with affine diagonal, and let `Φ`, with derivation unit
`ηΦ`, be a total right derived functor of `f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`. Then the square

```
D(QCoh(𝒪_X)) --i_X--> D_QCoh(𝒪_X)
     | Φ                  | Rf_*
     v                     v
D(QCoh(𝒪_Y)) --i_Y--> D_QCoh(𝒪_Y)
```

commutes, the horizontal arrows being the comparison functors of [Stacks, Tag 06VT] and the right
edge the restriction `AlgebraicGeometry.affineDiagonalDerivedQuasicoherentPushforward` of the
unbounded derived direct image.

The isomorphism is the canonical one: after the fully faithful inclusion of `D_QCoh(𝒪_Y)` it is
`AlgebraicGeometry.derivedPushforwardComparison`, the map `Φ(K) ⟶ Rf_*(K)` induced by
`f_* ⟶ Rf_*`, which is invertible by `AlgebraicGeometry.isIso_derivedPushforwardComparison`. -/
@[stacks 0CRX "the commuting square, for any right derived functor (Φ, ηΦ) of f_*"]
def derivedQuasicoherentComparisonSquareOfAffineDiagonal :
    derivedQuasicoherentComparison.{u} X ⋙ affineDiagonalDerivedQuasicoherentPushforward f ≅
      Φ ⋙ derivedQuasicoherentComparison.{u} Y :=
  haveI := isIso_derivedPushforwardComparison f Φ ηΦ
  ((DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).fullyFaithfulι.whiskeringRight
        (DerivedCategory (Scheme.QuasicoherentModules X))).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (derivedQuasicoherentComparison.{u} X)
        (qcqsDerivedQuasicoherentPushforwardCompιIso f) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (derivedQuasicoherentComparisonCompι.{u} X)
        (derivedPushforward.{u} f) ≪≫
      (asIso (derivedPushforwardComparison f Φ ηΦ)).symm ≪≫
      Functor.isoWhiskerLeft Φ (derivedQuasicoherentComparisonCompι.{u} Y).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- **The square of [Stacks, Tag 0CRX] at the chosen model of `Φ`**: the total right derived
functor `Stacks.DerivedQCoh.derivedQuasicoherentPushforward f` of `f_*` on quasi-coherent modules,
which exists because `QCoh(𝒪_X)` is a Grothendieck abelian category ([Stacks, Tag 077P]). So the
parameter block `(Φ, ηΦ)` of
`AlgebraicGeometry.derivedQuasicoherentComparisonSquareOfAffineDiagonal` is inhabited for every
`f`. -/
def chosenDerivedQuasicoherentComparisonSquareOfAffineDiagonal :
    derivedQuasicoherentComparison.{u} X ⋙ affineDiagonalDerivedQuasicoherentPushforward f ≅
      Stacks.DerivedQCoh.derivedQuasicoherentPushforward f ⋙
        derivedQuasicoherentComparison.{u} Y :=
  derivedQuasicoherentComparisonSquareOfAffineDiagonal f
    (Stacks.DerivedQCoh.derivedQuasicoherentPushforward f)
    (Stacks.DerivedQCoh.derivedQuasicoherentPushforwardUnit f)

end General

end AlgebraicGeometry

end
