module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeMapSections
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeDerivedSections

/-!
# Sections of the top higher direct image over an affine open

Let `f : X ⟶ Y` be a quasi-compact quasi-separated morphism of schemes, let `V ⊆ Y` be an affine
open, let `F` be a quasi-coherent `𝒪_X`-module and let `d` be an integer above which `Rf_*(F[0])`
has no cohomology. Then

> `Γ(V, H^d(Rf_*(F[0]))) ≅ H^d(RΓ(f⁻¹V, F[0]))`,

which is [Stacks, Tag 01XK] read over an affine open of the target and in the top degree: the
module of sections of the top higher direct image over `V` is the top cohomology of `F` on the
inverse image `f⁻¹V`.

**The identification is built as the composite of two natural factors, and nothing else.** Writing
`D := Rf_*(F[0])`:

* the degeneration of derived sections over an affine open, `topDegreeDerivedSectionsIso` of
  `StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/TopDegreeDerivedSections.lean`, taken at the
  identity morphism of `Y`, where `𝟙 Y ⁻¹ᵁ V = V` is affine. It reads
  `H^d(RΓ(V, D)) ≅ Γ(V, H^d D)`, and its forward direction is the canonical map
  `topDegreeDerivedSectionsMap`, so it is natural in `D`;
* the Leray comparison for derived sections, `derivedSectionsPushforwardIso` of
  `StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/LerayForDerivedSections.lean`
  ([Stacks, Tag 0D5W] over an open), a natural isomorphism of functors
  `Rf_* ⋙ RΓ(V, -) ≅ RΓ(f⁻¹V, -)` with no hypothesis on `f`, evaluated at `F[0]` and read through
  `H^d`.

Because both factors are natural, so is the composite, and
`topDirectImageSectionsIsoDerivedSections_hom` and
`topDirectImageSectionsIsoDerivedSections_inv` express it through them, so a consumer may rewrite
with the naturality of either factor on its own.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.affineSectionsTopDegreeIso` —
  `H^d(RΓ(V, D)) ≅ Γ(V, H^d D)` for an affine open `V ⊆ Y` and `D` in `D(𝒪_Y)` with
  quasi-coherent cohomology and no cohomology above `d`; the first factor.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedSectionsTopDirectImageMap` — the canonical
  map `H^d(RΓ(f⁻¹V, F[0])) ⟶ Γ(V, H^d(Rf_*(F[0])))`, the Leray comparison followed by the
  degeneration.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDirectImageSectionsIsoDerivedSections` —
  `Γ(V, H^d(Rf_*(F[0]))) ≅ H^d(RΓ(f⁻¹V, F[0]))`, the composite of the two factors.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.affineSectionsTopDegreeIso_hom` — the first
  factor's forward direction is the canonical `topDegreeDerivedSectionsMap` at `𝟙 Y`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDirectImageSectionsIsoDerivedSections_hom` and
  `…_inv` — the composite, read through its two factors.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_derivedSectionsTopDirectImageMap` — the
  canonical map is an isomorphism.

## Implementation notes

*Why the identity morphism of `Y` appears.* `topDegreeDerivedSectionsIso` is stated for a
morphism `f : X ⟶ Y` and an open `V ⊆ Y` whose inverse image `f⁻¹V` is affine, and its target is
sections over `f⁻¹V` with scalars restricted along `f^♯`. At `f = 𝟙 Y` the inverse image is `V`
itself and the restriction of scalars is along the identity, so
`Stacks.Cohomology.DerivedSectionsLeray.preimageSections (𝟙 Y) V` is
`Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen Y V` and
`Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections (𝟙 Y) V` is
`Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen Y V`, both by `rfl`. That is what
lets the two factors be composed: the Leray comparison speaks of `derivedSectionsOverOpen Y V`,
the degeneration of `derivedPreimageSections (𝟙 Y) V`, and the terms agree.

*The hypothesis `hLE` is an explicit argument.* `Rf_*(F[0])` having no cohomology above `d` is
specific to the situation in which the identification is used, so it is an argument of every
declaration here; in the situation of [Stacks, Tag 0EX3] it is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isLE_derivedPushforward_baseChange`. The
quasi-coherence of the cohomology sheaves of `Rf_*(F[0])`, by contrast, is
[Stacks, Tag 01XJ] in the form
`Stacks.AffineHigherDirectImage.isQuasicoherent_homologyFunctor_derivedPushforward`,
and is supplied here from `f` being quasi-compact and quasi-separated and `F` quasi-coherent.

*Two spellings of the modules on a scheme.* `X.Modules` and
`SheafOfModules.{u} (structureSheafRing X.toRingedSpace)` are equal types whose `Category` and
`Abelian` instances are different terms, as `DerivedModelCrossing.lean` records. The objects below
are written with `(DerivedCategory.singleFunctor X.Modules 0).obj F`, the spelling
[Stacks, Tag 01XJ] and the base-change files use, while the functors of sections and their
derived functors are written at the `structureSheafRing` spelling they are stated in; the crossing
happens in argument position only, as it does in `StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/AffinePushforwardBounds.lean`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction
open DerivedCategory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.Cohomology.DerivedSectionsLeray
  (derivedPreimageSections derivedSectionsOverOpen derivedSectionsPushforwardIso lerayComparison
    sectionsOverOpen)

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The degeneration of derived sections over an affine open -/

/-- **`H^d(RΓ(V, D)) ≅ Γ(V, H^d D)` over an affine open.** Let `V ⊆ Y` be an affine open and let
`D` be an object of `D(𝒪_Y)` whose cohomology sheaves are quasi-coherent and which has no
cohomology above `d`. Then the degree-`d` cohomology of the derived sections of `D` over `V` is
the module of sections over `V` of the degree-`d` cohomology sheaf of `D`.

This is `topDegreeDerivedSectionsIso` at the identity morphism of `Y`, where the inverse image
`𝟙 Y ⁻¹ᵁ V` is `V` and the restriction of scalars along the identity is invisible; see this
module's implementation notes. Its forward direction is the canonical map, by
`affineSectionsTopDegreeIso_hom`, so the identification is natural in `D`. -/
public def affineSectionsTopDegreeIso (Y : Scheme.{u}) (V : Y.Opens) (hV : IsAffineOpen V) (d : ℤ)
    (D : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hcoh : ∀ i : ℤ, ((homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).obj D).IsQuasicoherent)
    (hD : D.IsLE d) :
    (homologyFunctor (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V))) d).obj
        ((derivedSectionsOverOpen Y.toRingedSpace V).obj D) ≅
      (sectionsOverOpen Y.toRingedSpace V).obj
        ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) d).obj D) :=
  topDegreeDerivedSectionsIso (𝟙 Y) V hV d D hcoh hD

/-- The forward direction of `affineSectionsTopDegreeIso` is the canonical map
`topDegreeDerivedSectionsMap` at the identity morphism of `Y`: the truncation `D ⟶ τ_{≥ d}D`
followed by `τ_{≥ d}D ≅ H^d(D)[-d]`, read through `RΓ(V, -)` and `H^d`. This is what makes the
first factor usable through its naturality rather than as an opaque isomorphism. -/
public theorem affineSectionsTopDegreeIso_hom (Y : Scheme.{u}) (V : Y.Opens)
    (hV : IsAffineOpen V) (d : ℤ)
    (D : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hcoh : ∀ i : ℤ, ((homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).obj D).IsQuasicoherent)
    (hD : D.IsLE d) :
    (affineSectionsTopDegreeIso Y V hV d D hcoh hD).hom =
      topDegreeDerivedSectionsMap (𝟙 Y) V d D hD :=
  rfl

/-! ### The identification over an affine open -/

variable {X Y : Scheme.{u}}

/-- **The canonical map `H^d(RΓ(f⁻¹V, F[0])) ⟶ Γ(V, H^d(Rf_*(F[0])))`.** It is the composite of
the Leray comparison `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison` of
[Stacks, Tag 0D5W], which carries derived sections over `f⁻¹V` to derived sections over `V` of the
derived direct image and is natural in the argument with no hypothesis on `f`, read through `H^d`,
with the canonical degeneration map `topDegreeDerivedSectionsMap` at the identity morphism of `Y`.

`hLE` says that `Rf_*(F[0])` has no cohomology above `d`; it is an explicit argument, discharged
by `isLE_derivedPushforward_baseChange` in the situation of [Stacks, Tag 0EX3]. -/
public def derivedSectionsTopDirectImageMap (f : X ⟶ Y) (V : Y.Opens) (F : X.Modules) (d : ℤ)
    (hLE : ((derivedPushforward f.toLRSHom.toShHom).obj
      ((singleFunctor X.Modules 0).obj F)).IsLE d) :
    (homologyFunctor (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V))) d).obj
        ((derivedPreimageSections f.toLRSHom.toShHom V).obj
          ((singleFunctor X.Modules 0).obj F)) ⟶
      (sectionsOverOpen Y.toRingedSpace V).obj
        ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) d).obj
          ((derivedPushforward f.toLRSHom.toShHom).obj
            ((singleFunctor X.Modules 0).obj F))) :=
  (homologyFunctor (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V))) d).map
      ((lerayComparison f.toLRSHom.toShHom V).app ((singleFunctor X.Modules 0).obj F)) ≫
    topDegreeDerivedSectionsMap (𝟙 Y) V d _ hLE

/-- **[Stacks, Tag 01XK] over an affine open, in the top degree.** Let `f : X ⟶ Y` be a
quasi-compact quasi-separated morphism of schemes, let `V ⊆ Y` be an affine open, let `F` be a
quasi-coherent `𝒪_X`-module and let `d` be an integer such that `Rf_*(F[0])` has no cohomology
above `d`. Then

> `Γ(V, H^d(Rf_*(F[0]))) ≅ H^d(RΓ(f⁻¹V, F[0]))`.

It is the composite of the inverse of `affineSectionsTopDegreeIso`, the degeneration of derived
sections over the affine open `V`, with the degree-`d` cohomology of the Leray comparison
`Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsPushforwardIso` of [Stacks, Tag 0D5W] at
`F[0]`. Both factors are natural, and `topDirectImageSectionsIsoDerivedSections_hom` and
`topDirectImageSectionsIsoDerivedSections_inv` name them, so the naturality of each is available
to a consumer separately.

The quasi-coherence of the cohomology sheaves of `Rf_*(F[0])` that the first factor needs is
[Stacks, Tag 01XJ], in the form
`Stacks.AffineHigherDirectImage.isQuasicoherent_homologyFunctor_derivedPushforward`. `hLE` is an
explicit argument; in the
situation of [Stacks, Tag 0EX3] it is `isLE_derivedPushforward_baseChange`. -/
public def topDirectImageSectionsIsoDerivedSections (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] (V : Y.Opens) (hV : IsAffineOpen V) (F : X.Modules) [F.IsQuasicoherent]
    (d : ℤ)
    (hLE : ((derivedPushforward f.toLRSHom.toShHom).obj
      ((singleFunctor X.Modules 0).obj F)).IsLE d) :
    (sectionsOverOpen Y.toRingedSpace V).obj
        ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) d).obj
          ((derivedPushforward f.toLRSHom.toShHom).obj
            ((singleFunctor X.Modules 0).obj F))) ≅
      (homologyFunctor (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V))) d).obj
        ((derivedPreimageSections f.toLRSHom.toShHom V).obj
          ((singleFunctor X.Modules 0).obj F)) :=
  (affineSectionsTopDegreeIso Y V hV d _
      (Stacks.AffineHigherDirectImage.isQuasicoherent_homologyFunctor_derivedPushforward f F)
      hLE).symm ≪≫
    (homologyFunctor (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V))) d).mapIso
      ((derivedSectionsPushforwardIso f.toLRSHom.toShHom V).app
        ((singleFunctor X.Modules 0).obj F))

/-- **The identification, read through its two factors.** The forward direction of
`topDirectImageSectionsIsoDerivedSections` is the inverse of the degeneration
`affineSectionsTopDegreeIso` followed by the degree-`d` cohomology of the component of the Leray
isomorphism of [Stacks, Tag 0D5W] at `F[0]`.

Both factors are natural — the second is a component of a natural isomorphism of functors on
`D(𝒪_X)`, the first is inverse to a canonical map natural in the object of `D(𝒪_Y)` — so this
equation is what passes that naturality to the composite. -/
public theorem topDirectImageSectionsIsoDerivedSections_hom (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] (V : Y.Opens) (hV : IsAffineOpen V) (F : X.Modules) [F.IsQuasicoherent]
    (d : ℤ)
    (hLE : ((derivedPushforward f.toLRSHom.toShHom).obj
      ((singleFunctor X.Modules 0).obj F)).IsLE d) :
    (topDirectImageSectionsIsoDerivedSections f V hV F d hLE).hom =
      (affineSectionsTopDegreeIso Y V hV d _
          (Stacks.AffineHigherDirectImage.isQuasicoherent_homologyFunctor_derivedPushforward f F)
          hLE).inv ≫
        (homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V))) d).map
          ((derivedSectionsPushforwardIso f.toLRSHom.toShHom V).hom.app
            ((singleFunctor X.Modules 0).obj F)) :=
  rfl

/-- The backward direction of `topDirectImageSectionsIsoDerivedSections` is the canonical map
`derivedSectionsTopDirectImageMap`: the Leray comparison of [Stacks, Tag 0D5W] read through `H^d`,
followed by the canonical degeneration map `topDegreeDerivedSectionsMap`. -/
public theorem topDirectImageSectionsIsoDerivedSections_inv (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] (V : Y.Opens) (hV : IsAffineOpen V) (F : X.Modules) [F.IsQuasicoherent]
    (d : ℤ)
    (hLE : ((derivedPushforward f.toLRSHom.toShHom).obj
      ((singleFunctor X.Modules 0).obj F)).IsLE d) :
    (topDirectImageSectionsIsoDerivedSections f V hV F d hLE).inv =
      derivedSectionsTopDirectImageMap f V F d hLE :=
  rfl

/-- **The canonical map `H^d(RΓ(f⁻¹V, F[0])) ⟶ Γ(V, H^d(Rf_*(F[0])))` is an isomorphism** for a
quasi-compact quasi-separated `f`, an affine open `V ⊆ Y`, a quasi-coherent `F` and a `d` above
which `Rf_*(F[0])` has no cohomology. Both of its factors are: the Leray comparison by
[Stacks, Tag 0D5W] and the degeneration by `isIso_topDegreeDerivedSectionsMap`. It is the backward
direction of `topDirectImageSectionsIsoDerivedSections`, by
`topDirectImageSectionsIsoDerivedSections_inv`. -/
public theorem isIso_derivedSectionsTopDirectImageMap (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] (V : Y.Opens) (hV : IsAffineOpen V) (F : X.Modules) [F.IsQuasicoherent]
    (d : ℤ)
    (hLE : ((derivedPushforward f.toLRSHom.toShHom).obj
      ((singleFunctor X.Modules 0).obj F)).IsLE d) :
    IsIso (derivedSectionsTopDirectImageMap f V F d hLE) :=
  (topDirectImageSectionsIsoDerivedSections f V hV F d hLE).isIso_inv

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
