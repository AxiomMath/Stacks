module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwaySections
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.CategoryTheory.Sites.Modules.RestrictScalarsSheafification
public import StacksFrontier.CategoryTheory.Sites.Modules.Tensor
public import StacksFrontier.RingTheory.Localization.AwayTensorBaseChange

/-!
# Inverting a global section and changing the base ring

Let `(𝒞, 𝒪)` be a ringed site, let `𝒪'` be another sheaf of rings on the same site, let
`φ : 𝒪 ⟶ 𝒪'`, and let `f` be a global section of `𝒪` with image `f'` in `𝒪'`. This file proves
the identification wanted by [Stacks, Tag 099B] and by the lower row of [Stacks, Tag 099H],

`𝒪_f ⊗_𝒪 𝒪' ≅ 𝒪'_{f'}`.

Neither side of that isomorphism is a tensor product or a localization *as presented*: both are
sheafifications. The proof rewrites each of them as the sheafification of an explicit presheaf
over `𝒪` and then identifies those two presheaves, which is a statement with no sheafification
in it: the sectionwise base change `𝒪(U)[1/f|_U] ⊗_{𝒪(U)} 𝒪'(U) ≅ 𝒪'(U)[1/f'|_U]`.

## Main definitions

* `AlgebraicGeometry.RingedSite.baseChangeRingedSite`: the same site with another structure
  sheaf, and `AlgebraicGeometry.RingedSite.baseChangeGlobalSection`,
  `AlgebraicGeometry.RingedSite.baseChangeRingSheafMap` the image of a global section and the
  underlying map of sheaves of rings.
* `AlgebraicGeometry.RingedSite.restrictScalarsAwayModuleIsoSheafification`: **`𝒪'_{f'}`, read
  over `𝒪`, is the sheafification over `𝒪` of the presheaf `U ↦ 𝒪'(U)[1/f'|_U]` of sectionwise
  localizations of `𝒪'`.**
* `AlgebraicGeometry.RingedSite.restrictScalarsUnitIsoSheafification`: `𝒪'`, read over `𝒪`, is
  the sheafification over `𝒪` of the presheaf of rings `𝒪'` read over `𝒪`.
* `AlgebraicGeometry.RingedSite.awayTensorIsoSheafification`: **`𝒪_f ⊗_𝒪 𝒪'` is the
  sheafification over `𝒪` of the tensor product of the presheaf `U ↦ 𝒪(U)[1/f|_U]` with the
  presheaf of rings `𝒪'`.**
* `AlgebraicGeometry.RingedSite.awaySectionsBaseChangeMap`: the map of sections
  `𝒪(U)[1/f|_U] ⟶ 𝒪'(U)[1/f'|_U]`, and
  `AlgebraicGeometry.RingedSite.sectionwiseBaseChangeApp` the comparison out of the tensor
  product of sections, with `sectionwiseBaseChangeApp_tmul` its value on a pure tensor.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_sectionwiseBaseChangeApp` and
  `AlgebraicGeometry.RingedSite.sectionwiseBaseChangeIso`: **the sectionwise base change
  `𝒪(U)[1/f|_U] ⊗_{𝒪(U)} 𝒪'(U) ≅ 𝒪'(U)[1/f'|_U]`, as an isomorphism of presheaves of
  `𝒪`-modules.**
* `AlgebraicGeometry.RingedSite.awayTensorIsoBaseChangeAwayModule`:
  **`𝒪_f ⊗_𝒪 𝒪' ≅ 𝒪'_{f'}`** as sheaves of `𝒪`-modules.
* `AlgebraicGeometry.RingedSite.baseChangeGlobalSection_prodGlobalSection`: the image of
  `f_S = ∏_{i ∈ S} f_i` is `f'_S`, and
  `AlgebraicGeometry.RingedSite.awayLocalizationTensorObjIso` the identification above read at
  every subset `S ⊆ Fin r`, i.e. **objectwise on the system the extended alternating Čech
  complex is built from**. This family is not itself natural in `S`; see the note below for what
  is, and where.

## Implementation notes

The two ringed sites have the same underlying site, so `𝒪'_{f'}` is again a sheaf on `𝒞` and the
comparison lives in `SheafOfModules 𝒪.ringSheaf`; `baseChangeRingedSite` pins the implicit
ringed site down once, as `AlgebraicGeometry.RingedSite.awayRingedSite` does for the iterated
localization of `AwayBaseChange.lean`.

The first two of the three isomorphisms of sheafifications are
`AlgebraicGeometry.RingedSite.awaySheafificationIsoAwayModule` of `AwaySections.lean` — which
presents `𝒪'_{f'}` as a sheafification *over `𝒪'`* — respectively the counit of Mathlib's
sheafification adjunction, which presents the sheaf `𝒪'` as the sheafification of its own
underlying presheaf over `𝒪'`, each followed by
`AlgebraicGeometry.SheafOfModules.restrictScalarsSheafificationIso`, which moves the
sheafification across the change of scalars. That second step is what was missing: the two
sheafifications are formed over different sheaves of rings. The third is those two together
with `PresheafOfModules.sheafificationTensorIso` ([Stacks, Tag 0GMW]), which
carries the tensor product of two sheafifications to the sheafification of the tensor product.

### The sectionwise statement

Over one object the statement is the commutative algebra of
`IsLocalization.Away.bijective_tensorBaseChangeMap` in
`StacksFrontier/RingTheory/Localization/AwayTensorBaseChange.lean`: both
`𝒪(U)[1/f|_U] ⊗_{𝒪(U)} 𝒪'(U)` and `𝒪'(U)[1/f'|_U]` are localizations of the `𝒪(U)`-module
`𝒪'(U)` at the powers of `f|_U`, so a map between them commuting with the two maps out of
`𝒪'(U)` is invertible.

What that does *not* give is the comparison as a map of *presheaves*: the `Algebra` and
`IsScalarTower` instances it needs are chosen one object at a time, so the map has to be written
down uniformly in `U` and its naturality proved. It is `TensorProduct.lift` of
`(a, b) ↦ ψ_U a * j_U b`, with `ψ_U = awaySectionsBaseChangeMap` the map induced by `φ` on the
localizations and `j_U` the localization map of `𝒪'`; naturality is checked on pure tensors, and
reduces to the naturality of `j` and of `ψ`, the latter being a comparison of two ring maps out
of a localization and so settled on the image of `𝒪(U)`.

The `Algebra`-instance reseating that `AwaySections.lean` documents — the module structure
carried by a presheaf of modules is `RingHom.toModule` of a structure map, not the `Algebra`
instance of a localization — is arranged here once, by the block of `local instance`s before
`awaySectionsBaseChangeMap`, rather than at every use. They are stated at the module-valued
spellings of the rings of sections, which is what makes them legitimate instances: `φ` does not
occur in `Algebra 𝒪(U) 𝒪'(U)` but does occur in the presheaf of `𝒪`-modules `𝒪'` is read as.

An alternative route, which avoids sections entirely, is open since
`Stacks.SheafOfModules.ChangeOfRings.extendRestrictScalarsAdjunction` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExtendScalarsAdjunction.lean` ([Stacks, Tag
03CZ]): `𝒪_f ⊗_𝒪 𝒪'` is extension of scalars applied to `𝒪_f`, and
`AlgebraicGeometry.RingedSite.existsUnique_lift_unitToAwayModule` — the universal property of
`𝒪_f` as a sheaf of `𝒪`-*modules* — then compares it with `𝒪'_{f'}` by lifting in both
directions. It was not taken: it needs that every power of `f'` acts bijectively on the
extension of scalars, and the sections of that extension of scalars are the sheafification of an
abstract left adjoint, so there is nothing to compute with, whereas the sectionwise route has
Mathlib's localization API at every step.

### What this family is and is not: naturality in `S`

`awayLocalizationTensorObjIso` is a family of isomorphisms indexed by the subsets of `Fin r`, not
a natural transformation. Naturality in `S` would say that for `S ⊆ T` the square against the two
Čech transition maps — `AlgebraicGeometry.RingedSite.awayModuleTransition` base changed on one
side, the transition map of the system over `𝒪'` on the other — commutes. It is not proved for
*this* family, and the reason is the shape of the family: the isomorphism is the composite of
three isomorphisms of sheafifications, so the square would have to be pushed down to the
presheaves, where both legs compute on pure tensors, and the transition maps are chosen by a
universal property (`AlgebraicGeometry.RingedSite.eq_awayTransition`) rather than written down,
so each would first have to be identified with the sheafification of an explicit map of
presheaves of localizations.

The natural isomorphism itself *is* available, by another route and elsewhere:
`Stacks.Sheaves.CechFlatNeighbourhood.awayLocalizationBaseChangeIso` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatNeighbourhoodCech.lean` is
`(S ↦ 𝒪_{f_S}) ⋙ (- ⊗_𝒪 𝒪') ≅ (S ↦ 𝒪'_{f'_S}) ⋙ restrictScalars`, obtained from the
presentation of both systems as the colimit of the Koszul systems
(`AlgebraicGeometry.RingedSite.isColimitKoszulPowerFunctorCocone`), which are constant in `S`, so
that the comparison carries no `S`-dependence at all. Together with
`CategoryTheory.AlternatingCech.complexMapIso` and
`Stacks.Sheaves.CechFlatNeighbourhood.tensorExtendedAlternatingCechIso` that restates the lower
row of [Stacks, Tag 099H] as `Č(𝒪')`, which is what this file was wanted for there.

What the two routes give is not the same thing, and this one is not superseded: the sectionwise
formula `𝒪(U)[1/f] ⊗_{𝒪(U)} 𝒪'(U) ≅ 𝒪'(U)[1/f'|_U]` and the identification
`awayTensorIsoBaseChangeAwayModule` at a single global section are what [Stacks, Tag 099B] needs
of the base change, and the Koszul route produces neither. The two isomorphisms of sheaves are
not compared with each other anywhere.

Nothing here carries a `stacks` attribute. The identification is asserted without proof inside
the *proof* of [Stacks, Tag 099H] ("observe that the second complex is the tensor product of the
first complex with `𝒪'`"), so it is not the statement of a tag; the nearest tags that do have
statements, [Stacks, Tag 03DB] (limits and colimits in `Mod(𝒪)`) and [Stacks, Tag 03CZ] (the
restriction/extension of scalars adjunction), state neither this nor the sectionwise base
change. The tags that consume them are [Stacks, Tag 099B] and [Stacks, Tag 099H].

## References

* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
* [Stacks Project, Tag 099H](https://stacks.math.columbia.edu/tag/099H)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped TensorProduct

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  (O' : Sheaf X.J CommRingCat.{u})

/-- The ringed site with the same underlying site and with structure sheaf `𝒪'`. -/
abbrev baseChangeRingedSite : RingedSite.{u, u, u} := { C := X.C, J := X.J, O := O' }

variable (φ : X.O ⟶ O')

/-- The underlying map `𝒪 ⟶ 𝒪'` of sheaves of rings, with commutativity forgotten. -/
abbrev baseChangeRingSheafMap :
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseChangeRingedSite X O').O) :=
  (sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).map φ

/-- The image in `𝒪'` of a global section of `𝒪`. -/
def baseChangeGlobalSection (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    Presheaf.globalSections ((baseChangeRingedSite X O').O.obj ⋙ forget CommRingCat.{u}) :=
  h ≫ Functor.whiskerRight φ.hom (forget CommRingCat.{u})

omit [HasWeakSheafify X.J CommRingCat] in
/-- The value over `U` of the image in `𝒪'` of a global section `h` of `𝒪` is the image under
`φ` of the value of `h` over `U`. -/
theorem globalSectionVal_baseChangeGlobalSection
    (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) (U : X.Cᵒᵖ) :
    globalSectionVal (baseChangeGlobalSection X O' φ h) U =
      (φ.hom.app U).hom (globalSectionVal h U) := rfl

/-- **`𝒪'_{f'}`, read as a sheaf of `𝒪`-modules, is the sheafification over `𝒪` of the presheaf
`U ↦ 𝒪'(U)[1/f'|_U]` of sectionwise localizations of `𝒪'`.**

`AlgebraicGeometry.RingedSite.awaySheafificationIsoAwayModule` presents `𝒪'_{f'}` as that
sheafification *over `𝒪'`*, and
`AlgebraicGeometry.SheafOfModules.restrictScalarsSheafificationIso` moves the sheafification
across the change of scalars. -/
def restrictScalarsAwayModuleIsoSheafification
    (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    (SheafOfModules.restrictScalars (baseChangeRingSheafMap X O' φ)).obj
        (awayModule (baseChangeRingedSite X O') (baseChangeGlobalSection X O' φ h)) ≅
      (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj
        ((PresheafOfModules.restrictScalars (baseChangeRingSheafMap X O' φ).hom).obj
          (awayModulePresheaf (baseChangeRingedSite X O')
            (baseChangeGlobalSection X O' φ h))) :=
  ((SheafOfModules.restrictScalars (baseChangeRingSheafMap X O' φ)).mapIso
      (awaySheafificationIsoAwayModule (baseChangeRingedSite X O')
        (baseChangeGlobalSection X O' φ h)).symm).trans
    (AlgebraicGeometry.SheafOfModules.restrictScalarsSheafificationIso
      (baseChangeRingSheafMap X O' φ)
      (awayModulePresheaf (baseChangeRingedSite X O') (baseChangeGlobalSection X O' φ h)))

section Tensor

open AlgebraicGeometry.SheafOfModules

/-- The ring map associated to the identity of the presheaf of rings `𝒪` is an isomorphism. -/
noncomputable local instance isIso_associatedRingMap_id :
    IsIso (associatedRingMap X.J (𝟙 X.O.obj)) := by
  rw [show associatedRingMap X.J (𝟙 X.O.obj) =
    𝟙 (X.O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) from rfl]
  exact IsIso.id _

/-- `𝒪'`, read as a sheaf of `𝒪`-modules, is the sheafification over `𝒪` of the presheaf of
rings `𝒪'` read as a presheaf of `𝒪`-modules: the sheafification of a sheaf is that sheaf,
and the change of scalars passes across the sheafification. -/
def restrictScalarsUnitIsoSheafification :
    (SheafOfModules.restrictScalars (baseChangeRingSheafMap X O' φ)).obj
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (baseChangeRingedSite X O').O)) ≅
      (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj
        ((PresheafOfModules.restrictScalars (baseChangeRingSheafMap X O' φ).hom).obj
          (PresheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf (baseChangeRingedSite X O').O).obj)) :=
  ((SheafOfModules.restrictScalars (baseChangeRingSheafMap X O' φ)).mapIso
      ((asIso ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
            (baseChangeRingedSite X O').O).obj)).counit)).app
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (baseChangeRingedSite X O').O))).symm).trans
    (restrictScalarsSheafificationIso (baseChangeRingSheafMap X O' φ)
      (PresheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (baseChangeRingedSite X O').O).obj))

/-- **`𝒪_f ⊗_𝒪 𝒪'` is the sheafification of the tensor product of the two presheaves** — the
presheaf `U ↦ 𝒪(U)[1/f|_U]` of sectionwise localizations and the presheaf of rings `𝒪'` read
over `𝒪`.

Both factors are sheafifications — the first by
`AlgebraicGeometry.RingedSite.awaySheafificationIsoAwayModule`, the second by
`AlgebraicGeometry.RingedSite.restrictScalarsUnitIsoSheafification` — and
`PresheafOfModules.sheafificationTensorIso` ([Stacks, Tag 0GMW]) carries the
tensor product of two sheafifications to the sheafification of the tensor product. -/
def awayTensorIsoSheafification
    (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj
        ((SheafOfModules.restrictScalars (baseChangeRingSheafMap X O' φ)).obj
          (SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf (baseChangeRingedSite X O').O)))).obj
        (awayModule X h) ≅
      (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj
        (MonoidalCategoryStruct.tensorObj (awayModulePresheaf X h)
          ((PresheafOfModules.restrictScalars (baseChangeRingSheafMap X O' φ).hom).obj
            (PresheafOfModules.unit
              (Stacks.SheafOfModules.Tensor.ringSheaf (baseChangeRingedSite X O').O).obj))) :=
  ((((Stacks.SheafOfModules.Tensor.sheafTensor X.O).mapIso (awaySheafificationIsoAwayModule X
    h).symm).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj _).mapIso
        (restrictScalarsUnitIsoSheafification X O' φ))).trans
    ((PresheafOfModules.sheafificationTensorIso.{u, u, u, u, u}
      X.J (Osharp := X.O) (𝟙 X.O.obj)).app
      (awayModulePresheaf X h,
        (PresheafOfModules.restrictScalars (baseChangeRingSheafMap X O' φ).hom).obj
          (PresheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf (baseChangeRingedSite X O').O).obj)))

/-! ### The sectionwise base change -/

section SectionwiseBaseChange

variable (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- The presheaf of rings `𝒪'`, read as a presheaf of `𝒪`-modules: the presheaf whose
sheafification over `𝒪` is `𝒪'` read over `𝒪`
(`AlgebraicGeometry.RingedSite.restrictScalarsUnitIsoSheafification`). -/
abbrev baseChangeUnitPresheaf :
    PresheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj :=
  (PresheafOfModules.restrictScalars (baseChangeRingSheafMap X O' φ).hom).obj
    (PresheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseChangeRingedSite X O').O).obj)

/-- The presheaf `U ↦ 𝒪(U)[1/f|_U] ⊗_{𝒪(U)} 𝒪'(U)` of `𝒪`-modules, whose sheafification over
`𝒪` is `𝒪_f ⊗_𝒪 𝒪'` (`AlgebraicGeometry.RingedSite.awayTensorIsoSheafification`). -/
abbrev awayTensorPresheaf :
    PresheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj :=
  MonoidalCategoryStruct.tensorObj (awayModulePresheaf X h) (baseChangeUnitPresheaf X O' φ)

/-- The presheaf `U ↦ 𝒪'(U)[1/f'|_U]` of sectionwise localizations of `𝒪'`, read as a presheaf
of `𝒪`-modules, whose sheafification over `𝒪` is `𝒪'_{f'}` read over `𝒪`
(`AlgebraicGeometry.RingedSite.restrictScalarsAwayModuleIsoSheafification`). -/
abbrev baseChangeAwayPresheaf :
    PresheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj :=
  (PresheafOfModules.restrictScalars (baseChangeRingSheafMap X O' φ).hom).obj
    (awayModulePresheaf (baseChangeRingedSite X O') (baseChangeGlobalSection X O' φ h))

/-! The comparison below is a map of modules of sections, so the three rings of sections
`𝒪(U)`, `𝒪'(U)` and `𝒪'(U)[1/f'|_U]` have to be `𝒪(U)`-algebras in a way that *agrees with the
module structures the presheaves of modules carry*, which are restrictions of scalars along ring
maps and not the `Algebra` instances of a localization. The instances below are therefore the
`RingHom.toAlgebra` of the structure maps, which have the module structures of the presheaves on
the nose; they are `local`, they are stated at the module-valued spellings of the rings of
sections so that `φ` is determined by the type, and they are given low priority so that the
module structures continue to be found where they already were. This is the reseating that
`AwaySections.lean` documents, arranged once instead of at every use. -/

/-- The ring of sections over `U` of the presheaf of sectionwise localizations, read as a
commutative ring. -/
local instance commRingAwayModulePresheafObj (U : X.Cᵒᵖ) :
    CommRing ↥((awayModulePresheaf X h).obj U) :=
  inferInstanceAs (CommRing ↥((awayPresheaf h).obj U))

/-- The module of sections over `U` of `𝒪'` read over `𝒪`, as a commutative ring. -/
local instance commRingBaseChangeUnitPresheafObj (U : X.Cᵒᵖ) :
    CommRing ↥((baseChangeUnitPresheaf X O' φ).obj U) :=
  inferInstanceAs (CommRing ↥(O'.obj.obj U))

/-- `𝒪(U)[1/f|_U]` is an `𝒪(U)`-algebra through the localization map. -/
local instance (priority := low) algebraAwayModulePresheafObj (U : X.Cᵒᵖ) :
    Algebra ↥(X.O.obj.obj U) ↥((awayModulePresheaf X h).obj U) :=
  ((toAwayPresheaf h).app U).hom.toAlgebra

/-- `𝒪'(U)` is an `𝒪(U)`-algebra through `φ`. -/
local instance (priority := low) algebraBaseChangeUnitPresheafObj (U : X.Cᵒᵖ) :
    Algebra ↥(X.O.obj.obj U) ↥((baseChangeUnitPresheaf X O' φ).obj U) :=
  (φ.hom.app U).hom.toAlgebra

/-- `𝒪'(U)[1/f'|_U]` is an `𝒪'(U)`-algebra through the localization map. -/
local instance (priority := low) algebraBaseChangeAwayOverUnit (U : X.Cᵒᵖ) :
    Algebra ↥((baseChangeUnitPresheaf X O' φ).obj U)
      ↥((awayPresheaf (baseChangeGlobalSection X O' φ h)).obj U) :=
  ((toAwayPresheaf (baseChangeGlobalSection X O' φ h)).app U).hom.toAlgebra

/-- `𝒪'(U)[1/f'|_U]` is an `𝒪(U)`-algebra through `φ` and the localization map. -/
local instance (priority := low) algebraBaseChangeAwayOverBase (U : X.Cᵒᵖ) :
    Algebra ↥(X.O.obj.obj U) ↥((awayPresheaf (baseChangeGlobalSection X O' φ h)).obj U) :=
  (((toAwayPresheaf (baseChangeGlobalSection X O' φ h)).app U).hom.comp
    (φ.hom.app U).hom).toAlgebra

/-- The two `𝒪(U)`-algebra structures on `𝒪'(U)[1/f'|_U]` agree: the second is the first
composed with `φ`. -/
local instance isScalarTowerBaseChangeAway (U : X.Cᵒᵖ) :
    IsScalarTower ↥(X.O.obj.obj U) ↥((baseChangeUnitPresheaf X O' φ).obj U)
      ↥((awayPresheaf (baseChangeGlobalSection X O' φ h)).obj U) :=
  .of_algebraMap_eq fun _ => rfl

/-- Over every object, `𝒪(U)[1/f|_U]` is the localization of `𝒪(U)` away from the value of `f`
there: `AlgebraicGeometry.RingedSite.isLocalizationAway_awayPresheaf`, at the reseated
algebra. -/
local instance isLocalizationAwayModulePresheafObj (U : X.Cᵒᵖ) :
    IsLocalization.Away (globalSectionVal h U) ↥((awayModulePresheaf X h).obj U) :=
  isLocalizationAway_awayPresheaf h U

/-- Over every object, `𝒪'(U)[1/f'|_U]` is the localization of `𝒪'(U)` away from the image of
the value of `f` there, the image being the value of `f'`. -/
local instance isLocalizationAwayBaseChange (U : X.Cᵒᵖ) :
    IsLocalization.Away
      (algebraMap ↥(X.O.obj.obj U) ↥((baseChangeUnitPresheaf X O' φ).obj U)
        (globalSectionVal h U))
      ↥((awayPresheaf (baseChangeGlobalSection X O' φ h)).obj U) :=
  isLocalizationAway_awayPresheaf (X := baseChangeRingedSite X O')
    (baseChangeGlobalSection X O' φ h) U

/-- The map of sections `𝒪(U)[1/f|_U] ⟶ 𝒪'(U)[1/f'|_U]` induced by `φ`: the unique ring map
compatible with the two localization maps. -/
def awaySectionsBaseChangeMap (U : X.Cᵒᵖ) :
    ↥((awayModulePresheaf X h).obj U) →+*
      ↥((awayPresheaf (baseChangeGlobalSection X O' φ h)).obj U) :=
  IsLocalization.Away.map _ _
    (algebraMap ↥(X.O.obj.obj U) ↥((baseChangeUnitPresheaf X O' φ).obj U))
    (globalSectionVal h U)

omit [HasWeakSheafify X.J CommRingCat] in
/-- On the image of `𝒪(U)` the map of sections is `φ` followed by the localization map. -/
theorem awaySectionsBaseChangeMap_toAwayPresheaf (U : X.Cᵒᵖ) (x : ↥(X.O.obj.obj U)) :
    awaySectionsBaseChangeMap X O' φ h U (((toAwayPresheaf h).app U).hom x) =
      ((toAwayPresheaf (baseChangeGlobalSection X O' φ h)).app U).hom ((φ.hom.app U).hom x) :=
  IsLocalization.Away.map_algebraMap _ x

/-- **The sectionwise base change over one object**: the map
`𝒪(U)[1/f|_U] ⊗_{𝒪(U)} 𝒪'(U) ⟶ 𝒪'(U)[1/f'|_U]` carrying `a ⊗ b` to the product of the image of
`a` with the image of `b`. -/
def sectionwiseBaseChangeApp (U : X.Cᵒᵖ) :
    (awayTensorPresheaf X O' φ h).obj U ⟶ (baseChangeAwayPresheaf X O' φ h).obj U :=
  ConcreteCategory.ofHom
    (C := ModuleCat ↥(((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj U))
    (IsLocalization.Away.tensorBaseChangeMap
      (R := ↥(X.O.obj.obj U)) (A := ↥((awayModulePresheaf X h).obj U))
      (T := ↥((baseChangeUnitPresheaf X O' φ).obj U))
      (B := ↥((awayPresheaf (baseChangeGlobalSection X O' φ h)).obj U))
      (globalSectionVal h U))

omit [HasWeakSheafify X.J CommRingCat] in
/-- On a pure tensor the sectionwise base change is the product of the two images. -/
theorem sectionwiseBaseChangeApp_tmul (U : X.Cᵒᵖ) (a : ↥((awayModulePresheaf X h).obj U))
    (t : ↥((baseChangeUnitPresheaf X O' φ).obj U)) :
    (sectionwiseBaseChangeApp X O' φ h U).hom (a ⊗ₜ[↥(X.O.obj.obj U)] t) =
      awaySectionsBaseChangeMap X O' φ h U a *
        ((toAwayPresheaf (baseChangeGlobalSection X O' φ h)).app U).hom t :=
  IsLocalization.Away.tensorBaseChangeMap_tmul
    (R := ↥(X.O.obj.obj U)) (A := ↥((awayModulePresheaf X h).obj U))
    (T := ↥((baseChangeUnitPresheaf X O' φ).obj U))
    (B := ↥((awayPresheaf (baseChangeGlobalSection X O' φ h)).obj U))
    (globalSectionVal h U) a t

/-- **Over every object the sectionwise base change is invertible.** Both
`𝒪(U)[1/f|_U] ⊗_{𝒪(U)} 𝒪'(U)` and `𝒪'(U)[1/f'|_U]` are localizations of the `𝒪(U)`-module
`𝒪'(U)` at the powers of `f|_U`, and the comparison commutes with the two maps out of `𝒪'(U)`:
this is `IsLocalization.Away.bijective_tensorBaseChangeMap`. -/
instance isIso_sectionwiseBaseChangeApp (U : X.Cᵒᵖ) :
    IsIso (sectionwiseBaseChangeApp X O' φ h U) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact IsLocalization.Away.bijective_tensorBaseChangeMap
    (R := ↥(X.O.obj.obj U)) (A := ↥((awayModulePresheaf X h).obj U))
    (T := ↥((baseChangeUnitPresheaf X O' φ).obj U))
    (B := ↥((awayPresheaf (baseChangeGlobalSection X O' φ h)).obj U))
    (globalSectionVal h U)

section Naturality

variable {U V : X.Cᵒᵖ} (g : U ⟶ V)

omit [HasWeakSheafify X.J CommRingCat] in
/-- Restriction commutes with the localization map of `𝒪'`: the naturality of
`AlgebraicGeometry.RingedSite.toAwayPresheaf` over the base-changed ringed site. -/
theorem toAwayPresheaf_baseChange_naturality (y : ↥(O'.obj.obj U)) :
    ((awayPresheaf (baseChangeGlobalSection X O' φ h)).map g).hom
        (((toAwayPresheaf (baseChangeGlobalSection X O' φ h)).app U).hom y) =
      ((toAwayPresheaf (baseChangeGlobalSection X O' φ h)).app V).hom
        ((O'.obj.map g).hom y) :=
  (NatTrans.naturality_apply (toAwayPresheaf (baseChangeGlobalSection X O' φ h)) g y).symm

omit [HasWeakSheafify X.J CommRingCat] in
/-- The same naturality, with the sections of `𝒪'` spelled as the sections of `𝒪'` read over
`𝒪`, which is the spelling the comparison of presheaves of modules uses. -/
theorem toAwayPresheaf_baseChangeUnit_naturality
    (t : ↥((baseChangeUnitPresheaf X O' φ).obj U)) :
    ((awayPresheaf (baseChangeGlobalSection X O' φ h)).map g).hom
        (((toAwayPresheaf (baseChangeGlobalSection X O' φ h)).app U).hom t) =
      ((toAwayPresheaf (baseChangeGlobalSection X O' φ h)).app V).hom
        ((baseChangeUnitPresheaf X O' φ).map g t) :=
  toAwayPresheaf_baseChange_naturality X O' φ h g t

omit [HasWeakSheafify X.J CommRingCat] in
/-- **The map of sections is natural in the object.** Both composites are ring maps out of
`𝒪(U)[1/f|_U]`, so it is enough to compare them on the image of `𝒪(U)`, where both are `φ`
followed by restriction and by the localization map of `𝒪'`. -/
theorem awaySectionsBaseChangeMap_naturality (a : ↥((awayModulePresheaf X h).obj U)) :
    awaySectionsBaseChangeMap X O' φ h V (((awayPresheaf h).map g).hom a) =
      ((awayPresheaf (baseChangeGlobalSection X O' φ h)).map g).hom
        (awaySectionsBaseChangeMap X O' φ h U a) := by
  have key : (awaySectionsBaseChangeMap X O' φ h V).comp
        (show ↥((awayModulePresheaf X h).obj U) →+* ↥((awayModulePresheaf X h).obj V) from
          ((awayPresheaf h).map g).hom) =
      ((awayPresheaf (baseChangeGlobalSection X O' φ h)).map g).hom.comp
        (awaySectionsBaseChangeMap X O' φ h U) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (globalSectionVal h U)) (RingHom.ext ?_)
    intro x
    show awaySectionsBaseChangeMap X O' φ h V
        (((awayPresheaf h).map g).hom (((toAwayPresheaf h).app U).hom x)) =
      ((awayPresheaf (baseChangeGlobalSection X O' φ h)).map g).hom
        (awaySectionsBaseChangeMap X O' φ h U (((toAwayPresheaf h).app U).hom x))
    have hA : ((awayPresheaf h).map g).hom (((toAwayPresheaf h).app U).hom x) =
        ((toAwayPresheaf h).app V).hom ((X.O.obj.map g).hom x) :=
      (NatTrans.naturality_apply (toAwayPresheaf h) g x).symm
    have hphi : (O'.obj.map g).hom ((φ.hom.app U).hom x) =
        (φ.hom.app V).hom ((X.O.obj.map g).hom x) :=
      (NatTrans.naturality_apply φ.hom g x).symm
    rw [hA, awaySectionsBaseChangeMap_toAwayPresheaf, awaySectionsBaseChangeMap_toAwayPresheaf,
      toAwayPresheaf_baseChange_naturality, hphi]
  exact RingHom.congr_fun key a

omit [HasWeakSheafify X.J CommRingCat] in
/-- **The sectionwise base change is natural in the object.** Two maps out of a tensor product
agree as soon as they agree on pure tensors, where this is the naturality of the map of sections
and of the localization map of `𝒪'`. -/
theorem sectionwiseBaseChangeApp_naturality :
    (awayTensorPresheaf X O' φ h).map g ≫
        (ModuleCat.restrictScalars
          (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.map g).hom).map
          (sectionwiseBaseChangeApp X O' φ h V) =
      sectionwiseBaseChangeApp X O' φ h U ≫ (baseChangeAwayPresheaf X O' φ h).map g := by
  refine ModuleCat.MonoidalCategory.tensor_ext fun a t => ?_
  show awaySectionsBaseChangeMap X O' φ h V (((awayPresheaf h).map g).hom a) *
        ((toAwayPresheaf (baseChangeGlobalSection X O' φ h)).app V).hom
          ((baseChangeUnitPresheaf X O' φ).map g t) =
      ((awayPresheaf (baseChangeGlobalSection X O' φ h)).map g).hom
        (awaySectionsBaseChangeMap X O' φ h U a *
          ((toAwayPresheaf (baseChangeGlobalSection X O' φ h)).app U).hom t)
  rw [map_mul, awaySectionsBaseChangeMap_naturality, toAwayPresheaf_baseChangeUnit_naturality]

end Naturality

/-- **The sectionwise base change, as an isomorphism of presheaves of `𝒪`-modules**:

`𝒪(U)[1/f|_U] ⊗_{𝒪(U)} 𝒪'(U) ≅ 𝒪'(U)[1/f'|_U]`, naturally in `U`.

This is the one statement that `awayTensorIsoSheafification` and
`restrictScalarsAwayModuleIsoSheafification` left between their two sheafifications. -/
def sectionwiseBaseChangeIso :
    awayTensorPresheaf X O' φ h ≅ baseChangeAwayPresheaf X O' φ h :=
  PresheafOfModules.isoMk (fun U => asIso (sectionwiseBaseChangeApp X O' φ h U))
    fun {_ _} g => sectionwiseBaseChangeApp_naturality X O' φ h g

/-- **`𝒪_f ⊗_𝒪 𝒪' ≅ 𝒪'_{f'}`**, as sheaves of `𝒪`-modules: the identification wanted by
[Stacks, Tag 099B] and by the lower row of [Stacks, Tag 099H], for one global section.

Both sides are sheafifications over `𝒪` of explicit presheaves —
`awayTensorIsoSheafification` and `restrictScalarsAwayModuleIsoSheafification` — and
`sectionwiseBaseChangeIso` identifies those two presheaves. -/
def awayTensorIsoBaseChangeAwayModule :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj
        ((SheafOfModules.restrictScalars (baseChangeRingSheafMap X O' φ)).obj
          (SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf (baseChangeRingedSite X O').O)))).obj
        (awayModule X h) ≅
      (SheafOfModules.restrictScalars (baseChangeRingSheafMap X O' φ)).obj
        (awayModule (baseChangeRingedSite X O') (baseChangeGlobalSection X O' φ h)) :=
  (awayTensorIsoSheafification X O' φ h).trans
    (((PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).mapIso
        (sectionwiseBaseChangeIso X O' φ h)).trans
      (restrictScalarsAwayModuleIsoSheafification X O' φ h).symm)

end SectionwiseBaseChange

section CechSystem

variable {r : ℕ} (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

omit [HasWeakSheafify X.J CommRingCat] in
/-- **The image of `f_S` is `f'_S`**: `φ` is a map of sheaves of rings, so it carries the
product over `S` of the `f_i` to the product of their images. -/
theorem baseChangeGlobalSection_prodGlobalSection (S : Finset (Fin r)) :
    baseChangeGlobalSection X O' φ (prodGlobalSection f S) =
      prodGlobalSection (X := baseChangeRingedSite X O')
        (fun i => baseChangeGlobalSection X O' φ (f i)) S :=
  globalSections_ext (baseChangeRingedSite X O') fun U => by
    rw [globalSectionVal_baseChangeGlobalSection, globalSectionVal_prodGlobalSection,
      globalSectionVal_prodGlobalSection, map_prod]
    exact Finset.prod_congr rfl fun i _ =>
      (globalSectionVal_baseChangeGlobalSection X O' φ (f i) U).symm

/-- **`𝒪_{f_S} ⊗_𝒪 𝒪' ≅ 𝒪'_{f'_S}`, at every subset `S` of `Fin r`**: the termwise
identification of the two rows of [Stacks, Tag 099H]'s square, read at the system of
localizations that the extended alternating Čech complex is built from.

This is `AlgebraicGeometry.RingedSite.awayTensorIsoBaseChangeAwayModule` at `f_S`, together with
`baseChangeGlobalSection_prodGlobalSection` to say that the global section inverted on the right
is `f'_S` and not merely the image of `f_S`.

It is a *family* of isomorphisms and not a natural transformation: naturality in `S` is not
proved for it, for the reason given in the note on this family in the module docstring.  The
natural isomorphism that restates the lower row of [Stacks, Tag 099H] as `Č(𝒪')` is
`Stacks.Sheaves.CechFlatNeighbourhood.awayLocalizationBaseChangeIso` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatNeighbourhoodCech.lean`, which is obtained from
the colimit of the Koszul systems instead. -/
def awayLocalizationTensorObjIso (S : Finset (Fin r)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj
        ((SheafOfModules.restrictScalars (baseChangeRingSheafMap X O' φ)).obj
          (SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf (baseChangeRingedSite X O').O)))).obj
        ((awayLocalizationFunctor X f).obj S) ≅
      (SheafOfModules.restrictScalars (baseChangeRingSheafMap X O' φ)).obj
        ((awayLocalizationFunctor (baseChangeRingedSite X O')
          (fun i => baseChangeGlobalSection X O' φ (f i))).obj S) :=
  (awayTensorIsoBaseChangeAwayModule X O' φ (prodGlobalSection f S)).trans
    (eqToIso (congrArg
      (fun h => (SheafOfModules.restrictScalars (baseChangeRingSheafMap X O' φ)).obj
        (awayModule (baseChangeRingedSite X O') h))
      (baseChangeGlobalSection_prodGlobalSection X O' φ f S)))

end CechSystem

end Tensor

end AlgebraicGeometry.RingedSite

end
