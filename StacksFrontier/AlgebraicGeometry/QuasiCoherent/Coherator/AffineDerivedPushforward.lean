module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.AffinePushforward
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.TildeFactorization
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardAnyModel
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde

/-!
# Derived pushforward along an affine morphism on quasi-coherent modules

Let `f : X ⟶ Y` be an affine morphism of schemes. Pushforward of `𝒪_X`-modules preserves
quasi-coherence, so it restricts to `f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`
(`AlgebraicGeometry.quasicoherentPushforward`), and *that* restriction is exact: left exactness is
free, pushforward on quasi-coherent modules being a right adjoint, and right exactness is
[Stacks, Tag 01XC] in the form `AlgebraicGeometry.epi_pushforward_map_of_isAffineHom`. An exact
functor induces a functor of unbounded derived categories with no derivation, so `f_*` induces
`D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))`, which is the first assertion of [Stacks, Tag 08D7].

The comparison functor of [Stacks, Tag 06VT] carries that induced functor to the restriction of
the *unbounded* derived direct image `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, which is the second
assertion of [Stacks, Tag 08D7]. Its two ingredients are the affine case of [Stacks, Tag 0G9N] —
that a complex of quasi-coherent modules computes its own derived direct image — and part (1) of
[Stacks, Tag 08D5], which is what makes the restriction of `Rf_*` to `D_QCoh` exist; both are read
at the locally small model of the derived categories, where `AlgebraicGeometry.derivedTilde` and
the comparison functor live, through
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/AffinePushforwardAnyModel.lean`.

For a morphism of *affine* schemes the induced functor is derived restriction of scalars. On the
abelian categories this is [Stacks, Tag 01I9] read through the equivalence
`AlgebraicGeometry.tildeEquiv : Mod(R) ≌ QCoh(𝒪_{Spec R})`, and deriving an isomorphism of
composites of exact functors gives the same square on `D(R)`. Composing with the comparison
functor of [Stacks, Tag 06VT] turns it into the statement about derived sheafification
`AlgebraicGeometry.derivedTilde : D(R) ⥤ D_QCoh(𝒪_{Spec R})` which is [Stacks, Tag 0DJK] and the
first assertion of [Stacks, Tag 0A9F].

## Main definitions

* `AlgebraicGeometry.quasicoherentPushforwardCompιIso` — the defining property of the restriction
  of `f_*` to quasi-coherent modules.
* `AlgebraicGeometry.mapDerivedCategoryQuasicoherentPushforwardCompιIso` — [Stacks, Tag 0G9N] for
  an affine morphism, as an isomorphism of functors on `D(QCoh(𝒪_X))`.
* `AlgebraicGeometry.derivedQuasicoherentPushforward` — `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, the
  right edge of the square of [Stacks, Tag 08D7].
* `AlgebraicGeometry.derivedQuasicoherentComparisonSquare` — **the commuting square of
  [Stacks, Tag 08D7]**.
* `AlgebraicGeometry.affinePushforwardTildeEquivIso` — for `φ : R ⟶ S`, pushforward along
  `Spec φ` on quasi-coherent modules is restriction of scalars along `φ`.
* `AlgebraicGeometry.derivedAffinePushforwardTildeEquivIso` — the same square on the unbounded
  derived categories, `D(S) ⥤ D(QCoh(𝒪_{Spec R}))`.
* `AlgebraicGeometry.derivedTildeCompIso_of_comparisonSquare` — derived sheafification carries a
  functor satisfying the commuting square of [Stacks, Tag 08D7] to derived restriction of scalars.
* `AlgebraicGeometry.derivedTildeCompDerivedQuasicoherentPushforwardIso` — **[Stacks, Tag 0DJK]**:
  that square with `Rf_*` on its right edge.

## Main results

* `AlgebraicGeometry.quasicoherentPushforward_preservesFiniteLimits` and
  `AlgebraicGeometry.quasicoherentPushforward_preservesFiniteColimits` — pushforward along an
  affine morphism is exact on quasi-coherent modules.
* `AlgebraicGeometry.isRightDerivedFunctor_quasicoherentPushforward_mapDerivedCategory` — the
  induced functor on derived categories *is* a total right derived functor of `f_*`, which is the
  first assertion of [Stacks, Tag 08D7].
* `AlgebraicGeometry.isIso_whiskerLeft_derivedPushforwardUnit` — the comparison `f_* ⟶ Rf_*` is
  invertible on the whole image of `K(QCoh(𝒪_X))`.

## Implementation notes

**Where the two halves of `@[stacks 08D7]` sit.** The tag asserts that `f_*` defines a functor
`D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))`, which is
`AlgebraicGeometry.isRightDerivedFunctor_quasicoherentPushforward_mapDerivedCategory`, and that
the square
`D(QCoh(𝒪_X)) ⟶ D_QCoh(𝒪_X) ⟶ D_QCoh(𝒪_Y)`, `D(QCoh(𝒪_X)) ⟶ D(QCoh(𝒪_Y)) ⟶ D_QCoh(𝒪_Y)`
commutes, which is `AlgebraicGeometry.derivedQuasicoherentComparisonSquare`; the attribute is on
both and on nothing else. `AlgebraicGeometry.derivedQuasicoherentPushforward` carries no
attribute: it is the functor the square is *about*, and its existence is part (1) of
[Stacks, Tag 08D5] rather than part of 08D7.

**How the square is proved, and where the model mismatch went.** Composed with the fully faithful
inclusion `D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)` the square becomes
`AlgebraicGeometry.mapDerivedCategoryQuasicoherentPushforwardCompιIso`, an isomorphism between two
lifts through the localization `DerivedCategory.Qh` of `K(QCoh(𝒪_X))`; on `K(QCoh(𝒪_X))` the two
lifts differ by the comparison map `f_* ⟶ Rf_*`, which is invertible there because the inclusion
carries a complex of quasi-coherent modules to a complex of quasi-coherent `𝒪_X`-modules.

Every input to
`Rf_*` — [Stacks, Tag 0D5W], [Stacks, Tag 0D5X], [Stacks, Tag 0D66] and `Rf_*` itself in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/` — is pinned to
`CategoryTheory.HasDerivedCategory.standard`, while `AlgebraicGeometry.derivedTilde` and
`Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparison` are read at the
locally small model; `HasDerivedCategory` carries the localized category as data, so feeding a
standard-model functor where a locally small one is wanted is a universe error and not a
definitional gap. The pin on `Rf_*` is not removable: it
enters through `AlgebraicGeometry.isLE_derivedPushforward_obj_of_isAffineHom` and the
truncation-tower convergence of [Stacks, Tag 0D6P] behind it. What removes the obstruction is not
re-binding that chain but
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/AffinePushforwardAnyModel.lean`, which
restates the two statements about `Rf_*` that this file needs — [Stacks, Tag 0G9N] and part (1) of
[Stacks, Tag 08D5], both for an affine morphism — with **no derived category in them**, as
statements about a complex and a K-injective resolution of it, and reads them back at an arbitrary
`HasDerivedCategory` binder. The functor `Rf_*` used below is therefore
`AlgebraicGeometry.AnyModel.derivedPushforward` at the locally small model, and the obstruction has
no residue: `AlgebraicGeometry.derivedTildeCompIso_of_comparisonSquare` is applied with its
hypothesis `hsq` discharged.

**The two spellings of the module category.** `AlgebraicGeometry.Scheme.Modules X` and
`SheafOfModules X.ringCatSheaf` are definitionally equal, and so are their `Category` instances,
but `CategoryTheory.Epi` is stated against one of them at a time; the transport in
`AlgebraicGeometry.quasicoherentPushforward_preservesEpimorphisms` is the explicit type ascription
`@Epi X.Modules`, which is why `AlgebraicGeometry.epi_pushforward_map_of_isAffineHom` applies. For
the same reason the direct image appearing in `quasicoherentPushforwardCompιIso` is
`AlgebraicGeometry.pushforwardSheafOfModules`, the ascription of
`RingedSpaceModuleAdjunction.modulePushforward` into the `SheafOfModules _.ringCatSheaf` view.

**Right exactness is not re-proved from [Stacks, Tag 01XC].** The vanishing `R^i f_* ℱ = 0` for
`ℱ` quasi-coherent and `f` affine is proved as
`Stacks.AffineHigherDirectImage.isZero_rightDerivedPlus_pushforward`, and would give
right exactness through the long exact sequence; but
`AlgebraicGeometry.epi_pushforward_map_of_isAffineHom` already states exactly the step needed, by
the independent route of [Stacks, Tag 01SB], so it is used instead.

## References

* [Stacks Project, Tag 08D7](https://stacks.math.columbia.edu/tag/08D7)
* [Stacks Project, Tag 0DJK](https://stacks.math.columbia.edu/tag/0DJK)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
* [Stacks Project, Tag 0A9F](https://stacks.math.columbia.edu/tag/0A9F)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.QuasicoherentDerived
open AlgebraicGeometry.AnyModel (derivedPushforward derivedPushforwardUnit)

namespace AlgebraicGeometry

universe u

/-! ### Exactness of pushforward along an affine morphism on quasi-coherent modules -/

/-- **Pushforward is left exact on quasi-coherent modules.** It is the right adjoint of
`AlgebraicGeometry.quasicoherentPullback`, so it preserves all limits it can; no hypothesis beyond
the quasi-compactness and quasi-separatedness that make it exist is needed. -/
public instance quasicoherentPushforward_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] : PreservesFiniteLimits (quasicoherentPushforward f) := by
  have : PreservesLimitsOfSize.{0, 0} (quasicoherentPushforward f) :=
    (quasicoherentPullbackPushforwardAdjunction f).rightAdjoint_preservesLimits
  infer_instance

/-- **Pushforward along an affine morphism carries an epimorphism of quasi-coherent modules to an
epimorphism.** The inclusion of the quasi-coherent modules is fully faithful and exact, so an
epimorphism of `QCoh(𝒪_X)` is an epimorphism of `𝒪_X`-modules between quasi-coherent ones and
conversely; in between, `AlgebraicGeometry.epi_pushforward_map_of_isAffineHom` is the assertion for
all modules. -/
public instance quasicoherentPushforward_preservesEpimorphisms {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] : (quasicoherentPushforward f).PreservesEpimorphisms := by
  refine ⟨fun {A B} g _ => ?_⟩
  have hA : A.obj.IsQuasicoherent := A.2
  have hB : B.obj.IsQuasicoherent := B.2
  have hg : @Epi X.Modules _ A.obj B.obj g.hom :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.map_epi g
  have hpf : Epi ((Scheme.Modules.pushforward f).map g.hom) :=
    epi_pushforward_map_of_isAffineHom f (M := A.obj) (N := B.obj) g.hom
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.epi_of_epi_map
    (f := (quasicoherentPushforward f).map g) hpf

/-- **Stacks 08D7, exactness.** Pushforward along an affine morphism is right exact on
quasi-coherent modules: it is left exact and preserves epimorphisms, hence preserves homology,
hence preserves finite colimits. -/
public instance quasicoherentPushforward_preservesFiniteColimits {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] : PreservesFiniteColimits (quasicoherentPushforward f) := by
  have : (quasicoherentPushforward f).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- **Pushforward along an affine morphism defines a derived functor
`D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))`.** This is the first assertion of [Stacks, Tag 08D7]: the functor
induced on unbounded derived categories by the exact functor
`AlgebraicGeometry.quasicoherentPushforward`, namely
`CategoryTheory.Functor.mapDerivedCategory`, is a total right derived functor of it, so no
resolutions are involved and the derived functor is computed by applying `f_*` to a representative
complex.

The structure map is `CategoryTheory.Functor.mapDerivedCategoryFactorsh.inv`, which exhibits the
induced functor as a lift through the localization `DerivedCategory.Qh`; a lift of a functor that
inverts the quasi-isomorphisms is a right derived functor for the inverse of the lifting
isomorphism. -/
@[stacks 08D7 "the derived functor"]
public theorem isRightDerivedFunctor_quasicoherentPushforward_mapDerivedCategory
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    (quasicoherentPushforward f).mapDerivedCategory.IsRightDerivedFunctor
      (quasicoherentPushforward f).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (Scheme.QuasicoherentModules X) (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    (quasicoherentPushforward f).mapDerivedCategoryFactorsh

/-! ### The commuting square of Stacks 08D7 -/

/-- **Direct image on quasi-coherent modules, followed by the inclusion, is the inclusion followed
by direct image.** `AlgebraicGeometry.quasicoherentPushforward` is *defined* as the restriction of
`f_*` to the quasi-coherent modules, so this is the defining property of that restriction. -/
public def quasicoherentPushforwardCompιIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    quasicoherentPushforward f ⋙ (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι ≅
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙ pushforwardSheafOfModules f :=
  ObjectProperty.liftCompιIso _ _ _

/-- **The comparison `f_* ⟶ Rf_*` is invertible on the whole image of `K(QCoh(𝒪_X))`.** An object
of `K(QCoh(𝒪_X))` is the homotopy class of a complex of quasi-coherent modules, and the inclusion
carries it to a complex of quasi-coherent `𝒪_X`-modules, on which
`AlgebraicGeometry.AnyModel.isIso_derivedPushforwardUnit_app_of_isAffineHom` — [Stacks, Tag 0G9N]
for an affine morphism — applies. -/
public theorem isIso_whiskerLeft_derivedPushforwardUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] :
    IsIso (Functor.whiskerLeft
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedPushforwardUnit.{u} f)) := by
  refine (NatTrans.isIso_iff_isIso_app _).2 fun L => ?_
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
  exact (NatTrans.isIso_app_iff_of_iso (derivedPushforwardUnit.{u} f)
    (((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).app M)).2
    (AnyModel.isIso_derivedPushforwardUnit_app_of_isAffineHom f
      (((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M) (fun n => (M.X n).2))

/-- **[Stacks, Tag 0G9N] for an affine morphism, as an isomorphism of functors on
`D(QCoh(𝒪_X))`.** Deriving the inclusion of the quasi-coherent modules and then taking the
unbounded derived direct image is the same as taking the derived functor of direct image on
quasi-coherent modules and then deriving the inclusion.

Both sides are functors `D(QCoh(𝒪_X)) ⥤ D(𝒪_Y)` lifting a functor on `K(QCoh(𝒪_X))` through the
localization `DerivedCategory.Qh`, so `CategoryTheory.Localization.liftNatIso` reduces the claim
to an isomorphism of the two lifted functors. On `K(QCoh(𝒪_X))` the two differ exactly by the
comparison map `f_* ⟶ Rf_*`, which is invertible there by
`AlgebraicGeometry.isIso_whiskerLeft_derivedPushforwardUnit`; the remaining steps are the
factorizations of `CategoryTheory.Functor.mapDerivedCategory` through the homotopy category and
`AlgebraicGeometry.quasicoherentPushforwardCompιIso` read on homotopy categories. -/
public def mapDerivedCategoryQuasicoherentPushforwardCompιIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] :
    (quasicoherentPushforward f).mapDerivedCategory ⋙
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapDerivedCategory ≅
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory ⋙
        derivedPushforward.{u} f :=
  haveI := isIso_whiskerLeft_derivedPushforwardUnit f
  Localization.liftNatIso DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory (ComplexShape.up ℤ))
    (((quasicoherentPushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) ⋙
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapDerivedCategory)
    (((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙ derivedPushforward.{u} f)
    _ _
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ((quasicoherentPushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso
            (Iso.refl (quasicoherentPushforward f ⋙
              (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι)) (ComplexShape.up ℤ) ≪≫
          (Functor.mapHomotopyCategoryCompIso (quasicoherentPushforwardCompιIso f).symm
            (ComplexShape.up ℤ)).symm)
        DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫
      asIso (Functor.whiskerLeft
        ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomotopyCategory
          (ComplexShape.up ℤ)) (derivedPushforwardUnit.{u} f)) ≪≫
      (Functor.associator _ _ _).symm)

/-- **The restriction of `Rf_*` to the complexes with quasi-coherent cohomology**, for `f` an
affine morphism of schemes: the functor `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` that the right edge of
the square of [Stacks, Tag 08D7] and the whole of [Stacks, Tag 0DJK] are about.

It exists because `Rf_*` carries quasi-coherent cohomology to quasi-coherent cohomology, which is
part (1) of [Stacks, Tag 08D5] for an affine morphism,
`AlgebraicGeometry.AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom`. -/
public def derivedQuasicoherentPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).FullSubcategory :=
  (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).lift
    ((DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙
      derivedPushforward.{u} f)
    (fun E n =>
      AnyModel.isQuasicoherent_homologyFunctor_derivedPushforward_of_isAffineHom f E.1 E.2 n)

/-- **Stacks 08D7, the commuting square.** For `f : X ⟶ Y` an affine morphism of schemes the
square
`D(QCoh(𝒪_X)) ⟶ D_QCoh(𝒪_X) ⟶ D_QCoh(𝒪_Y)`, `D(QCoh(𝒪_X)) ⟶ D(QCoh(𝒪_Y)) ⟶ D_QCoh(𝒪_Y)`
commutes: the comparison functor of [Stacks, Tag 06VT] carries the derived functor of direct image
on quasi-coherent modules to the restriction of the unbounded derived direct image.

The two edges are compared after the fully faithful inclusion `D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)`, where the
comparison functor becomes the derived inclusion
(`Stacks.AlgebraicGeometry.QuasicoherentDerived.derivedQuasicoherentComparisonCompι`) and the
square becomes `AlgebraicGeometry.mapDerivedCategoryQuasicoherentPushforwardCompιIso`, which is
[Stacks, Tag 0G9N] for an affine morphism. -/
@[stacks 08D7 "the commuting square"]
public def derivedQuasicoherentComparisonSquare {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    derivedQuasicoherentComparison.{u} X ⋙ derivedQuasicoherentPushforward f ≅
      (quasicoherentPushforward f).mapDerivedCategory ⋙ derivedQuasicoherentComparison.{u} Y :=
  ((DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).fullyFaithfulι.whiskeringRight
        (DerivedCategory
          (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (derivedQuasicoherentComparison.{u} X)
        (ObjectProperty.liftCompιIso _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (derivedQuasicoherentComparisonCompι.{u} X)
        (derivedPushforward.{u} f) ≪≫
      (mapDerivedCategoryQuasicoherentPushforwardCompιIso f).symm ≪≫
      Functor.isoWhiskerLeft (quasicoherentPushforward f).mapDerivedCategory
        (derivedQuasicoherentComparisonCompι.{u} Y).symm ≪≫
      (Functor.associator _ _ _).symm)

/-! ### A morphism of affine schemes: pushforward is restriction of scalars -/

section Affine

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- **Stacks 01I9 on quasi-coherent modules.** Pushforward along `Spec φ : Spec S ⟶ Spec R`
carries the quasi-coherent sheaf associated to an `S`-module to the one associated to that module
with its scalars restricted along `φ`.

This is `AlgebraicGeometry.pushforwardTildeIso` with both sides read inside the quasi-coherent
modules: the inclusion of the quasi-coherent modules is fully faithful, and composing either side
with it gives back the two sides of that isomorphism, so the isomorphism descends. -/
public def affinePushforwardTildeEquivIso :
    (tildeEquiv (R := S)).functor ⋙ quasicoherentPushforward (Spec.map φ) ≅
      ModuleCat.restrictScalars φ.hom ⋙ (tildeEquiv (R := R)).functor :=
  ((SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).fullyFaithfulι.whiskeringRight
      (ModuleCat.{u} S)).preimageIso
    (show ((tildeEquiv (R := S)).functor ⋙ quasicoherentPushforward (Spec.map φ)) ⋙
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι ≅
      (ModuleCat.restrictScalars φ.hom ⋙ (tildeEquiv (R := R)).functor) ⋙
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι from
      pushforwardTildeIso R S φ)

/-- **Derived pushforward between affine schemes on the quasi-coherent derived categories is
derived restriction of scalars.** The `~` edge of [Stacks, Tag 06Z0] followed by the derived
functor of pushforward on quasi-coherent modules is restriction of scalars on `D(S)` followed by
the `~` edge over `R`.

Every functor in sight is exact, so each composite is the functor induced on derived categories by
the corresponding composite of abelian functors, and the square is
`AlgebraicGeometry.affinePushforwardTildeEquivIso` derived. -/
public def derivedAffinePushforwardTildeEquivIso :
    (Stacks.DerivedQCoh.derivedTildeEquiv.{u, u} S).functor ⋙
        (quasicoherentPushforward (Spec.map φ)).mapDerivedCategory ≅
      (ModuleCat.restrictScalars φ.hom).mapDerivedCategory ⋙
        (Stacks.DerivedQCoh.derivedTildeEquiv.{u, u} R).functor :=
  Functor.mapDerivedCategoryCompIsoOfCompIso (affinePushforwardTildeEquivIso φ) ≪≫
    (Functor.mapDerivedCategoryCompIsoOfCompIso
      (Iso.refl (ModuleCat.restrictScalars φ.hom ⋙ (tildeEquiv (R := R)).functor))).symm

/-- **Derived sheafification carries a derived pushforward satisfying the square of
[Stacks, Tag 08D7] to derived restriction of scalars.** Let `φ : R ⟶ S` and let
`P : D_QCoh(𝒪_{Spec S}) ⥤ D_QCoh(𝒪_{Spec R})` be any functor for which the square of
[Stacks, Tag 08D7] commutes, that is, for which `P` agrees, after the comparison functor of
[Stacks, Tag 06VT], with the derived functor of pushforward on quasi-coherent modules. Then
`derivedTilde S ⋙ P ≅ (restriction of scalars along φ, derived) ⋙ derivedTilde R`.

This is the hypothesis `hP` of
`AlgebraicGeometry.derivedTilde_comp_rightAdjointIsoDerivedHom`, and therefore of
[Stacks, Tag 0A9F], reduced to the commuting square of [Stacks, Tag 08D7]. The proof is the
factorization `Stacks.DerivedQCoh.derivedTildeEquivCompComparisonIso` of derived sheafification
through the `~` edge and the comparison functor, the hypothesis, and
`AlgebraicGeometry.derivedAffinePushforwardTildeEquivIso`; nothing else enters, and in particular
no model of the derived categories is chosen beyond the locally small ones at which
`AlgebraicGeometry.derivedTilde` is stated.

Note that the hypothesis is *not* that `P` is the restriction of a total right derived functor of
pushforward of all modules — that is the assertion the square makes about it, and it is the half
of [Stacks, Tag 08D7] which this file does not prove; see the implementation notes. -/
public def derivedTildeCompIso_of_comparisonSquare
    (P : (DerivedCategoryB.derivedCategoryB (A := (Spec S).Modules)
        (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory)
    (hsq : derivedQuasicoherentComparison.{u} (Spec S) ⋙ P ≅
      (quasicoherentPushforward (Spec.map φ)).mapDerivedCategory ⋙
        derivedQuasicoherentComparison.{u} (Spec R)) :
    derivedTilde S ⋙ P ≅
      (ModuleCat.restrictScalars φ.hom).mapDerivedCategory ⋙ derivedTilde R :=
  Functor.isoWhiskerRight (Stacks.DerivedQCoh.derivedTildeEquivCompComparisonIso S).symm P ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Stacks.DerivedQCoh.derivedTildeEquiv.{u, u} S).functor hsq ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedAffinePushforwardTildeEquivIso φ)
      (derivedQuasicoherentComparison.{u} (Spec R)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (ModuleCat.restrictScalars φ.hom).mapDerivedCategory
      (Stacks.DerivedQCoh.derivedTildeEquivCompComparisonIso R)

/-- **Stacks 0DJK.** Let `φ : R ⟶ S` and let `f = Spec φ : Spec S ⟶ Spec R`. Then the square
`D(S) ⟶ D_QCoh(𝒪_{Spec S}) ⟶^{Rf_*} D_QCoh(𝒪_{Spec R})`,
`D(S) ⟶^{restriction of scalars} D(R) ⟶ D_QCoh(𝒪_{Spec R})`
commutes: derived direct image along a morphism of affine schemes corresponds, under derived
sheafification, to derived restriction of scalars.

This is `AlgebraicGeometry.derivedTildeCompIso_of_comparisonSquare` with its hypothesis `hsq`
discharged by `AlgebraicGeometry.derivedQuasicoherentComparisonSquare`, the commuting square of
[Stacks, Tag 08D7]. It is also the first assertion of [Stacks, Tag 0A9F]. -/
@[stacks 0DJK, stacks 0A9F "Rf_* is derived restriction of scalars"]
public def derivedTildeCompDerivedQuasicoherentPushforwardIso :
    derivedTilde S ⋙ derivedQuasicoherentPushforward (Spec.map φ) ≅
      (ModuleCat.restrictScalars φ.hom).mapDerivedCategory ⋙ derivedTilde R :=
  derivedTildeCompIso_of_comparisonSquare φ (derivedQuasicoherentPushforward (Spec.map φ))
    (derivedQuasicoherentComparisonSquare (Spec.map φ))

end Affine

end AlgebraicGeometry

end
