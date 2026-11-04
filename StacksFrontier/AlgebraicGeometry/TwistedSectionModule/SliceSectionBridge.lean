module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricConstruction
public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.DivisionMultiplicativity
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Basic
public import StacksFrontier.AlgebraicGeometry.TensorPowerTrivialize.Power
public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.UnitScalarSupplement

/-!
# The slice-unit bridge computes the restriction of a global section

Stacks Tag 0B5L's comparison map on an open `V` lands in `twistSections (ℱ|_V) (L|_V) 0`, a
morphism out of the monoidal unit of the modules on the slice site over `V`, and
`Stacks.SheafInternalHom.SliceRestriction.schemeOpenUnitHomAddEquiv` reads such a morphism as a
section of `ℱ` over `V`. Every consumer on the `Proj` side instead holds a *global* section and
restricts it, through `Stacks.TensorPowerTrivialize.resTop` and
`Stacks.SectionProduct.globalSection`. **This file relates the two readings.**

A morphism out of the monoidal unit of `X.Modules` is carried to the slice site as
`ε ≫ (ℱ|_V)`, with `ε` the lax unit of
`Stacks.SheafInternalHom.SliceRestriction.schemeOverFunctorMonoidal`; that composite is what
`Stacks.TwistedSections.mapTwistSections` is in degree zero. The result proved here is

`schemeOpenUnitHomAddEquiv V ℱ (ε ≫ (ℱ|_V) t) = resTop ℱ (globalSection t) V`

**on the nose, with no factor.** The lax unit contributes a function
`Stacks.TwistedSections.sliceUnitRatio X V` on `V`, depending on neither `ℱ` nor `t`, and
`Stacks.TwistedSections.sliceUnitRatio_eq_one` computes it to be `1`.

## Main definitions

* `Stacks.TwistedSections.unitOneOpen`: the section `1` of the free rank-one sheaf over an
  arbitrary open. `Stacks.SectionRingGeometric.unitOne` is its value at `⊤`, and keeps its own
  name and type, having consumers throughout the ample development.
* `Stacks.TwistedSections.sliceUnitSection`: the section of the monoidal unit over `V` attached to
  the lax unit of restriction to `V`.
* `Stacks.TwistedSections.sliceUnitRatio`: that section read as a function on `V`, through
  `Stacks.SectionRingGeometric.unitComparison`.

## Main results

* `Stacks.SectionRingGeometric.tensorUnitHomAddEquiv_comp`: the carrier comparison is natural —
  the section of `f ≫ g` is `g` applied to the section of `f`. By `rfl`.
* `Stacks.SectionRingGeometric.isUnit_unitScalar`: **the function of an invertible endomorphism of
  the monoidal unit is invertible**, since the scalar is multiplicative and the scalar of the
  identity is `1`.
* `Stacks.TwistedSections.laxUnit_overFunctor_eq`: **the lax unit of restriction to a slice site
  is the comparison "sheafification commutes with restriction to a slice site"**,
  `Stacks.SheafOfModules.SliceRestriction.sliceComparison`. The other two factors of
  `CategoryTheory.Localization.Monoidal.functorMonoidalOfComp_ε` are identities. Stated for an
  arbitrary object of an arbitrary site, which is what makes it usable at an *iterated* slice.
* `Stacks.TwistedSections.overUnitSection_eq` and `overTensorUnitHomAddEquiv_eps_comp`: **the
  whole bridge at an arbitrary site**; the scheme statements below are instantiations of them at
  the site of opens of `X`, and the instantiation at the *slice* site over `V` is what Stacks Tag
  0B5I's compatibility with shrinking the open consumes.
* `Stacks.TwistedSections.sliceUnitRatio_eq_one`: **the lax unit of the restriction is an
  identity on sections.** This is the coherence for `ε` that the division layer was recorded as
  unable to avoid; see the implementation notes.
* `Stacks.TwistedSections.schemeOpenUnitHomAddEquiv_eps_comp` and
  `schemeOpenUnitHomAddEquiv_mapTwistSections`: **the comparison**, in the two spellings the
  consumers use.
* `Stacks.TwistedSections.sliceUnitScalar_eq`: **the scalar of the division multiplicativity is a
  restricted global function.** `Stacks.TwistedSections.sliceUnitScalar L V e`, the function on
  `V` that `Stacks.TwistedSections.openDivision_gsmul_unitComp` produces, is the restriction to
  `V` of `Stacks.SectionRingGeometric.schemeUnitScalar X e`. This is the second of the two steps
  that piece (iii) of Stacks Tag 0B5I was recorded as still owing.

## Implementation notes

**How the ratio is pinned down.** This file previously recorded that computing the ratio would be
a coherence for the lax unit `ε` of
`Stacks.SheafInternalHom.SliceRestriction.overFunctorMonoidal` that nothing needed. It *is* that
coherence, and the division layer does need it — shrinking the open `V` turns an identity between
two multiples of one section, where a common factor cancels, into an identity between multiples
at two different opens, where it does not. The chase is short, because two of the three factors
of `CategoryTheory.Localization.Monoidal.functorMonoidalOfComp_ε` are identities:

* `η (sheafify)` is the **hom of the chosen unit comparison** of
  `CategoryTheory.Localization.Monoidal.toMonoidalCategory`, and
  `Stacks.SheafInternalHom.monoidalCategory` localizes at `Iso.refl _`;
* `ε (restrict ⋙ sheafify)` is `ε (sheafify) ≫ sheafify.map (ε (restrict))`, whose first factor is
  an identity for the same reason and whose second is the image of one, Mathlib's
  `PresheafOfModules.pushforward₀OfCommRingCat` being monoidal with `εIso := Iso.refl _`.

So `ε` of the restriction *is*
`Stacks.SheafOfModules.SliceRestriction.sliceComparison` at the presheaf unit, and that is the
morphism **adjoint to the restricted sheafification unit**: on the unit image of a local section
it is the restricted unit itself. Reading it as a section conjugates by
`Stacks.SectionRingGeometric.unitComparison`, which is the sheafification **counit**, so the two
unit images cancel against it and the section is `1`. The only non-formal inputs are
`PresheafOfModules.sheafifyCounitIso_inv_apply`,
`sheafifyCounitIso_hom_sheafifyUnit_apply` and
`sheafificationAdjunction_unit_comp_homEquiv_symm`, all already in the library; nothing is reproved and
the tensorator `μ`, which has no component formula, is never mentioned.

**Why the proofs are elementwise.** The target of
`(ℱ|_V) (unitComparison X).hom` is `(ℱ|_V) (unitModule X)`, which is the free rank-one sheaf of
the slice site only up to unfolding `AlgebraicGeometry.Scheme.Modules`; a composite through that
object is not type-correct at `implicit` transparency, and every `rw` touching it fails with
`motive is not type correct`. So no morphism is ever composed across that identification here:
everything is done on sections, where `AlgebraicGeometry.Scheme.Modules.Hom.app` and
`Stacks.TensorPowerTrivialize.resTop_app` keep all the types on the `X` side.

**No new bijectivity lemma for sections of an isomorphism.** `Scheme.Modules.app_inv_app_hom` and
`app_hom_app_inv` already exist, in
`StacksFrontier/AlgebraicGeometry/Variety/Projective/HyperplaneDegreeOneSurjective.lean`, which this
file cannot import without pulling in the whole `Chow` development; the two one-line `congrArg`
terms are therefore written out where they are used rather than duplicated as declarations.

## References

* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite Limits
open Stacks.GradedSections (powSections)
open Stacks.TensorPowers (natTensorPow)
open Stacks.TensorPowerTrivialize (resTop resTop_app resTop_globalSection_comp)
open Stacks.SheafOfModules.TensorSheafification

universe v u w

namespace Stacks.SectionRingGeometric

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory

/-- **The carrier comparison is natural.** The section over a terminal object attached to a
composite `f ≫ g` is `g`, read on sections there, applied to the section attached to `f`. Both
sides are the value at `1` of a composite of morphisms of presheaves of modules, so this is
`rfl`. -/
theorem tensorUnitHomAddEquiv_comp {T : C} (hT : IsTerminal T)
    {F G : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)}
    (f : 𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶ F) (g : F ⟶ G) :
    tensorUnitHomAddEquiv 𝒪 h𝒪 hT G (f ≫ g)
      = ConcreteCategory.hom (g.val.app (op T)) (tensorUnitHomAddEquiv 𝒪 h𝒪 hT F f) :=
  rfl

/-- **The function of an invertible endomorphism of the monoidal unit is invertible.** The scalar
of a composite is the product of the scalars and the scalar of the identity is `1`, so the scalar
of the inverse inverts it. -/
theorem isUnit_unitScalar (T : C) (b : 𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶
      𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) [IsIso b] :
    IsUnit (unitScalarOnSite 𝒪 h𝒪 T b) :=
  ⟨⟨unitScalarOnSite 𝒪 h𝒪 T b, unitScalarOnSite 𝒪 h𝒪 T (inv b),
      (unitScalarOnSite_comp 𝒪 h𝒪 T b (inv b)).symm.trans
        ((congrArg (unitScalarOnSite 𝒪 h𝒪 T) (IsIso.hom_inv_id b)).trans
          (unitScalarOnSite_id 𝒪 h𝒪 T)),
      (unitScalarOnSite_comp 𝒪 h𝒪 T (inv b) b).symm.trans
        ((congrArg (unitScalarOnSite 𝒪 h𝒪 T) (IsIso.inv_hom_id b)).trans
          (unitScalarOnSite_id 𝒪 h𝒪 T))⟩,
    rfl⟩

end Site

end Stacks.SectionRingGeometric

namespace Stacks.TwistedSections

open Stacks.SheafInternalHom.SliceRestriction (schemeOpenRestriction schemeOverFunctorMonoidal
  schemeOpenUnitHomAddEquiv)
open Stacks.SheafOfModules.SliceRestriction (sliceRingPresheaf isSheaf_sliceRingPresheaf
  sliceStructureSheaf sliceComparison sliceFunctor sliceSheafify sliceUnit)
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)
open Stacks.SectionProduct (globalSection)
open Stacks.SectionRingGeometric (unitScalarOnSite tensorUnitHomAddEquiv unitModule unitComparison
  unitOne schemeUnitScalar)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive
  Stacks.SectionRingGeometric.presheafMonoidalPreadditiveStructure
  Stacks.SectionRingGeometric.sheafifyAdditive
  Stacks.SectionRingGeometric.tensorLeftAdditive
  Stacks.SectionRingGeometric.tensorRightAdditive
  Stacks.SheafInternalHom.SliceRestriction.schemeOverFunctorMonoidal
  Stacks.SheafInternalHom.SliceRestriction.sliceCompSheafifyMonoidal

/-! ### The lax unit of a restriction to a slice site, on an arbitrary ringed site

Everything about the lax unit holds for restriction to a slice site over an arbitrary object of
an arbitrary site, and is proved there; the scheme statements below are instantiations. The
generality is what makes the bridge available at an *iterated* slice site, where restriction from
`V` to `V' ≤ V` is read as restriction to the object `Over.mk (homOfLE hV')` of the site
`(X.Opens)/V`.
-/

section Site

open Stacks.SheafInternalHom.SliceRestriction (overTensorUnitHomAddEquiv)
open Stacks.SheafOfModules.SliceRestriction (overFunctor)
open Stacks.SheafOfModules (sheafifyFunctor)

attribute [local instance] Stacks.SheafInternalHom.SliceRestriction.overFunctorMonoidal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The presheaf of modules underlying the free rank-one sheaf. This is the source of
`PresheafOfModules.sheafifyUnit` at the monoidal unit, and naming it is what keeps the element
`1` at a spelling the rewrites of this section can see — the same device as
`Stacks.TwistedSections.unitOneOpen` on a scheme. -/
abbrev unitUnderlying : PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj :=
  (SheafOfModules.forget (structureSheaf 𝒪 h𝒪) ⋙
    PresheafOfModules.restrictScalars (𝟙 (structureSheaf 𝒪 h𝒪).obj)).obj
      (SheafOfModules.unit (structureSheaf 𝒪 h𝒪))

/-- **The section `1` of the free rank-one sheaf over an object of the site**, at the spelling
`PresheafOfModules.sheafifyUnit` consumes. -/
def overUnitOne (U : C) : (unitUnderlying 𝒪 h𝒪).obj (op U) := (1 : 𝒪.obj (op U))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- Restricting the section `1` gives the section `1`: the restriction maps of the free rank-one
sheaf are those of the structure presheaf, which are ring homomorphisms. -/
theorem map_overUnitOne {A B : C} (f : B ⟶ A) :
    (unitUnderlying 𝒪 h𝒪).map f.op (overUnitOne 𝒪 h𝒪 A) = overUnitOne 𝒪 h𝒪 B :=
  PresheafOfModules.unit_map_one _ _

/-- **The global section of the identity of the monoidal unit is the unit image of `1`.**
`Stacks.SectionRingGeometric.tensorUnitHomAddEquiv` conjugates by
`AlgebraicGeometry.SheafOfModules.unitIso`, which is the sheafification counit, so its inverse
*is* the sheafification unit on sections. -/
theorem tensorUnitHomAddEquiv_id_eq {T : C} (hT : IsTerminal T) :
    tensorUnitHomAddEquiv 𝒪 h𝒪 hT (𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) (𝟙 _)
      = PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
        (𝟙 (structureSheaf 𝒪 h𝒪).obj) (unitUnderlying 𝒪 h𝒪)) (op T) (overUnitOne 𝒪 h𝒪 T) :=
  (rfl : tensorUnitHomAddEquiv 𝒪 h𝒪 hT (𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) (𝟙 _)
      = PresheafOfModules.Hom.app
        (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).inv.val (op T)
        (overUnitOne 𝒪 h𝒪 T)).trans
    (PresheafOfModules.sheafifyCounitIso_inv_apply (𝟙 (structureSheaf 𝒪 h𝒪).obj)
      (SheafOfModules.unit (structureSheaf 𝒪 h𝒪)) (op T) (overUnitOne 𝒪 h𝒪 T))

variable (U : C) [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- **The lax unit of the presheaf-level restriction followed by sheafification is the
identity.** Both factors have an identity lax unit: Mathlib's
`PresheafOfModules.pushforward₀OfCommRingCat` is monoidal with `εIso := Iso.refl _`, and
sheafification is the monoidal localization functor of
`CategoryTheory.Localization.Monoidal.toMonoidalCategory`, whose `εIso` is the inverse of the
chosen unit comparison — here `Iso.refl _`, since `Stacks.SheafInternalHom.monoidalCategory`
localizes at that comparison. So the lax unit of the composite is `𝟙 ≫ (-)^#(𝟙)`. -/
theorem laxUnit_sliceCompSheafify_eq_id :
    Functor.LaxMonoidal.ε (sliceFunctor 𝒪 U ⋙ sliceSheafify 𝒪 h𝒪 U) = CategoryStruct.id _ :=
  (Category.id_comp _).trans ((sliceSheafify 𝒪 h𝒪 U).map_id _)

/-- **The lax unit of restriction to a slice site is the comparison "sheafification commutes with
restriction".** `Stacks.SheafInternalHom.SliceRestriction.overFunctorMonoidal` is
`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp`, whose lax unit is
`ε G ≫ e.inv.app (𝟙_) ≫ F.map (η L)` with `e` the lifting isomorphism
`Stacks.SheafOfModules.SliceRestriction.sliceSheafifyIso`. The outer two factors are identities —
`η L` because the localized monoidal structure is taken at the unit comparison `Iso.refl _`, and
`ε G` by `laxUnit_sliceCompSheafify_eq_id` — so only the middle factor survives, and `e.inv` is
`Stacks.SheafOfModules.SliceRestriction.sliceComparison` by construction. -/
theorem laxUnit_overFunctor_eq :
    Functor.LaxMonoidal.ε (overFunctor 𝒪 h𝒪 U) =
      (sliceComparison 𝒪 h𝒪 U).app
        (𝟙_ (PresheafOfModules.{w} (structureRingPresheaf 𝒪))) :=
  let : (sheafifyFunctor 𝒪 h𝒪).Monoidal := Stacks.SheafInternalHom.sheafifyMonoidal 𝒪 h𝒪
  have key : Functor.LaxMonoidal.ε (overFunctor 𝒪 h𝒪 U) =
      Functor.LaxMonoidal.ε (sliceFunctor 𝒪 U ⋙ sliceSheafify 𝒪 h𝒪 U) ≫
        ((sliceComparison 𝒪 h𝒪 U).app
            (𝟙_ (PresheafOfModules.{w} (structureRingPresheaf 𝒪))) ≫
          (overFunctor 𝒪 h𝒪 U).map (Functor.OplaxMonoidal.η
            (sheafifyFunctor 𝒪 h𝒪))) := rfl
  by
  rw [key, laxUnit_sliceCompSheafify_eq_id]
  erw [Category.id_comp, (overFunctor 𝒪 h𝒪 U).map_id, Category.comp_id]

/-- **The slice comparison undoes the slice sheafification unit.** The comparison is the
morphism adjoint to `Stacks.SheafOfModules.SliceRestriction.sliceUnit`
(`sliceComparison_app`), and a morphism out of a sheafification agrees with the morphism it
transposes from on the unit image of a local section. -/
theorem sliceComparison_app_sheafifyUnit_apply
    (P : PresheafOfModules.{w} (structureRingPresheaf 𝒪)) (W : (Over U)ᵒᵖ)
    (x : ((sliceFunctor 𝒪 U).obj P).obj W) :
    PresheafOfModules.Hom.app
        ((sliceComparison 𝒪 h𝒪 U).app P).val W
        (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
          (𝟙 (sliceStructureSheaf 𝒪 h𝒪 U).obj)
          ((sliceFunctor 𝒪 U).obj P)) W x)
      = PresheafOfModules.Hom.app (sliceUnit 𝒪 h𝒪 U P) W x :=
  PresheafOfModules.hom_congr_apply'
    (PresheafOfModules.sheafificationAdjunction_unit_comp_homEquiv_symm
      (𝟙 (sliceStructureSheaf 𝒪 h𝒪 U).obj) (sliceUnit 𝒪 h𝒪 U P)) W x

/-- **The section of the monoidal unit over `U` attached to the lax unit of restriction to the
slice site over `U`.** The lax unit is a morphism `𝟙_ ⟶ 𝟙_|_U` out of the monoidal unit of the
modules on the slice site, so the bridge
`Stacks.SheafInternalHom.SliceRestriction.overTensorUnitHomAddEquiv` reads it as a section. -/
def overUnitSection : (𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))).val.obj (op U) :=
  overTensorUnitHomAddEquiv 𝒪 h𝒪 U (𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)))
    (Functor.LaxMonoidal.ε (overFunctor 𝒪 h𝒪 U))

/-- **The slice-unit section is the unit image of the function `1`.** Reading the lax unit as a
section over `U` means conjugating it by the comparison of the monoidal unit with the free
rank-one sheaf — which is the sheafification counit, so its inverse *is* the sheafification unit
on sections — and evaluating at the terminal object of the slice site on `1`. By
`laxUnit_overFunctor_eq` and `sliceComparison_app_sheafifyUnit_apply` the lax unit then carries
that unit image to the unit image of `1` on the site. -/
theorem overUnitSection_eq_sheafifyUnit_one :
    overUnitSection 𝒪 h𝒪 U =
      PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
        (𝟙 (structureSheaf 𝒪 h𝒪).obj) (unitUnderlying 𝒪 h𝒪)) (op U) (overUnitOne 𝒪 h𝒪 U) :=
  (rfl : overUnitSection 𝒪 h𝒪 U =
      PresheafOfModules.Hom.app
        ((AlgebraicGeometry.SheafOfModules.unitIso (sliceRingPresheaf 𝒪 U)
            (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)).inv ≫
          Functor.LaxMonoidal.ε (overFunctor 𝒪 h𝒪 U)).val
        (op (Over.mk (𝟙 U))) (overUnitOne 𝒪 h𝒪 U)).trans
    (((congrArg (fun z => PresheafOfModules.Hom.app
          (Functor.LaxMonoidal.ε (overFunctor 𝒪 h𝒪 U)).val (op (Over.mk (𝟙 U))) z)
        (PresheafOfModules.sheafifyCounitIso_inv_apply
          (𝟙 (sliceStructureSheaf 𝒪 h𝒪 U).obj)
          (SheafOfModules.unit (sliceStructureSheaf 𝒪 h𝒪 U)) (op (Over.mk (𝟙 U)))
          (overUnitOne 𝒪 h𝒪 U))).trans
      (congrArg (fun φ : (𝟙_ (SheafOfModules.{w} (sliceStructureSheaf 𝒪 h𝒪 U))) ⟶
          (overFunctor 𝒪 h𝒪 U).obj (𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) =>
        PresheafOfModules.Hom.app φ.val (op (Over.mk (𝟙 U)))
          (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
            (𝟙 (sliceStructureSheaf 𝒪 h𝒪 U).obj)
            ((sliceFunctor 𝒪 U).obj
              (𝟙_ (PresheafOfModules.{w} (structureRingPresheaf 𝒪)))))
            (op (Over.mk (𝟙 U))) (overUnitOne 𝒪 h𝒪 U)))
        (laxUnit_overFunctor_eq 𝒪 h𝒪 U))).trans
      (sliceComparison_app_sheafifyUnit_apply 𝒪 h𝒪 U
        (𝟙_ (PresheafOfModules.{w} (structureRingPresheaf 𝒪))) (op (Over.mk (𝟙 U)))
        (overUnitOne 𝒪 h𝒪 U)))

/-- **The slice-unit section is the restriction of the global section of the identity.** Both
sides are the unit image of the function `1`, by `overUnitSection_eq_sheafifyUnit_one` and
`tensorUnitHomAddEquiv_id_eq`, and the unit is a morphism of presheaves of modules, so it
commutes with the restriction that carries `1` to `1`. There is no factor, which is the coherence
for the lax unit `ε` of
`Stacks.SheafInternalHom.SliceRestriction.overFunctorMonoidal`. -/
theorem overUnitSection_eq {T : C} (hT : IsTerminal T) :
    overUnitSection 𝒪 h𝒪 U
      = (𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))).val.map (hT.from U).op
          (tensorUnitHomAddEquiv 𝒪 h𝒪 hT
            (𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) (𝟙 _)) :=
  (overUnitSection_eq_sheafifyUnit_one 𝒪 h𝒪 U).trans
    (((congrArg (fun z : (unitUnderlying 𝒪 h𝒪).obj (op U) =>
          PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
            (𝟙 (structureSheaf 𝒪 h𝒪).obj) (unitUnderlying 𝒪 h𝒪)) (op U) z)
        (map_overUnitOne (𝒪 := 𝒪) (h𝒪 := h𝒪) (f := hT.from U)).symm).trans
      (PresheafOfModules.naturality_apply
        (PresheafOfModules.sheafifyUnit (𝟙 (structureSheaf 𝒪 h𝒪).obj) (unitUnderlying 𝒪 h𝒪))
        (hT.from U).op (overUnitOne 𝒪 h𝒪 T))).trans
      (congrArg (fun z =>
          (𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))).val.map (hT.from U).op z)
        (tensorUnitHomAddEquiv_id_eq 𝒪 h𝒪 hT).symm))

/-- **The slice-unit bridge computes the restriction of the global section.** For `u` a morphism
out of the monoidal unit, carrying `u` to the slice site over `U` by the lax unit of the
restriction and reading the result as a section of the target over `U` gives exactly the
restriction to `U` of the global section of `u`: the lax unit contributes no factor, by
`overUnitSection_eq`.

**This is the statement the division layer consumes, and the generality is the point.** At the
site of opens of a scheme it is `Stacks.TwistedSections.schemeOpenUnitHomAddEquiv_eps_comp`; at
the *slice* site over an open `V` it is the same statement for a further open `V' ≤ V`, which is
what reading Stacks Tag 0B5L's comparison map over the smaller open as a section of `ℱ` over `V'`
needs. -/
theorem overTensorUnitHomAddEquiv_eps_comp {T : C} (hT : IsTerminal T)
    (F : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
    (u : 𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶ F) :
    overTensorUnitHomAddEquiv 𝒪 h𝒪 U F
        (Functor.LaxMonoidal.ε (overFunctor 𝒪 h𝒪 U) ≫ (overFunctor 𝒪 h𝒪 U).map u)
      = F.val.map (hT.from U).op (tensorUnitHomAddEquiv 𝒪 h𝒪 hT F u) :=
  (rfl : overTensorUnitHomAddEquiv 𝒪 h𝒪 U F
        (Functor.LaxMonoidal.ε (overFunctor 𝒪 h𝒪 U) ≫ (overFunctor 𝒪 h𝒪 U).map u)
      = PresheafOfModules.Hom.app u.val (op U) (overUnitSection 𝒪 h𝒪 U)).trans
    (((congrArg (fun z => PresheafOfModules.Hom.app u.val (op U) z)
        (overUnitSection_eq 𝒪 h𝒪 U hT)).trans
      (PresheafOfModules.naturality_apply u.val (hT.from U).op
        (tensorUnitHomAddEquiv 𝒪 h𝒪 hT
          (𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) (𝟙 _)))).trans
      (congrArg (fun z => F.val.map (hT.from U).op z)
        ((Stacks.SectionRingGeometric.tensorUnitHomAddEquiv_comp 𝒪 h𝒪 hT
            (𝟙 (𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)))) u).symm.trans
          (congrArg (fun z => tensorUnitHomAddEquiv 𝒪 h𝒪 hT F z) (Category.id_comp u)))))

end Site

variable {X : Scheme.{u}}

/-- **The section `1` of the free rank-one sheaf of modules over an open.** -/
def unitOneOpen (X : Scheme.{u}) (V : X.Opens) : Γ(unitModule X, V) := (1 : Γ(X, V))

/-- The global section `Stacks.SectionRingGeometric.unitOne` is `unitOneOpen` at `⊤`. -/
theorem unitOne_eq_unitOneOpen (X : Scheme.{u}) : unitOne X = unitOneOpen X ⊤ := rfl

/-- **Scaling the section `1` is the inclusion of the functions on `V`.** The module structure on
the sections of the free rank-one sheaf is the multiplication of the ring of sections, so this is
`mul_one`. -/
theorem smul_unitOneOpen {V : X.Opens} (r : Γ(X, V)) :
    r • unitOneOpen X V = (r : Γ(unitModule X, V)) :=
  mul_one r

/-- **Restricting the section `1` gives the section `1`**: the restriction map of the free
rank-one sheaf is the restriction map of the structure sheaf, a ring homomorphism. -/
theorem resTop_unitOne (V : X.Opens) :
    resTop (unitModule X) (unitOne X) V = unitOneOpen X V :=
  PresheafOfModules.unit_map_one _ _

/-- **The restriction to `V` of the global section of the identity of the monoidal unit is `1`**,
read through `Stacks.SectionRingGeometric.unitComparison`. -/
theorem app_unitComparison_hom_resTop_id (V : X.Opens) :
    Scheme.Modules.Hom.app (unitComparison X).hom V
        (resTop (𝟙_ X.Modules) (globalSection X _ (𝟙 (𝟙_ X.Modules))) V)
      = unitOneOpen X V := by
  have h0 : globalSection X (𝟙_ X.Modules) (𝟙 (𝟙_ X.Modules))
      = Scheme.Modules.Hom.app (unitComparison X).inv ⊤ (unitOne X) := by
    rw [show globalSection X (𝟙_ X.Modules) (𝟙 (𝟙_ X.Modules))
        = Scheme.Modules.Hom.app ((unitComparison X).inv ≫ 𝟙 (𝟙_ X.Modules)) ⊤ (unitOne X) from
      Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv_apply X _ _, Category.comp_id]
  rw [h0, resTop_app, resTop_unitOne]
  exact congrArg
    (fun φ : unitModule X ⟶ unitModule X =>
      Scheme.Modules.Hom.app φ V (unitOneOpen X V)) (unitComparison X).inv_hom_id

/-- **The section of the monoidal unit over `V` attached to the lax unit of restriction to `V`.**
This is `Stacks.TwistedSections.overUnitSection` at the site of opens of `X`. -/
def sliceUnitSection (X : Scheme.{u}) (V : X.Opens) : Γ(𝟙_ X.Modules, V) :=
  overUnitSection X.presheaf (isSheaf_structureRingPresheaf X) V

/-- **The function on `V` by which the slice-unit bridge differs from restricting a global
section.** It is `sliceUnitSection` read through
`Stacks.SectionRingGeometric.unitComparison`, and `sliceUnitRatio_eq_one` computes it to be
`1`. -/
def sliceUnitRatio (X : Scheme.{u}) (V : X.Opens) : Γ(X, V) :=
  Scheme.Modules.Hom.app (unitComparison X).hom V (sliceUnitSection X V)

/-! ### The lax unit of the restriction, computed on sections -/

/-- `sliceUnitSection` is the restriction of the global section of the identity. This is
`Stacks.TwistedSections.overUnitSection_eq` at the site of opens of `X`, whose terminal object is
`⊤`. -/
theorem sliceUnitSection_eq (V : X.Opens) :
    sliceUnitSection X V
      = resTop (𝟙_ X.Modules) (globalSection X _ (𝟙 (𝟙_ X.Modules))) V :=
  overUnitSection_eq X.presheaf (isSheaf_structureRingPresheaf X) V isTerminalTop

/-- **The ratio is `1`: the lax unit of the restriction is an identity on sections.** This is
the coherence for the lax unit `ε` of
`Stacks.SheafInternalHom.SliceRestriction.schemeOverFunctorMonoidal` that the division layer was
recorded as unable to avoid. By `sliceUnitSection_eq` the slice-unit section is the restriction
of the global section of the identity, and `app_unitComparison_hom_resTop_id` reads that as the
function `1`. Every statement of the form
`X.presheaf.map _ (sliceUnitRatio X V) = sliceUnitRatio X V'` follows. -/
theorem sliceUnitRatio_eq_one (V : X.Opens) : sliceUnitRatio X V = 1 :=
  (congrArg (fun z : Γ(𝟙_ X.Modules, V) =>
      Scheme.Modules.Hom.app (unitComparison X).hom V z) (sliceUnitSection_eq V)).trans
    (app_unitComparison_hom_resTop_id V)

/-- **The slice-unit bridge computes the restriction of the global section.** For `u` a morphism
out of the monoidal unit of `X.Modules`, carrying `u` to the slice site over `V` by the lax unit
of the restriction and reading the result as a section of the target over `V` gives exactly the
restriction to `V` of the global section of `u`: the lax unit contributes no factor. This is
`Stacks.TwistedSections.overTensorUnitHomAddEquiv_eps_comp` at the site of opens of `X`. -/
theorem schemeOpenUnitHomAddEquiv_eps_comp (V : X.Opens) (M : X.Modules)
    (u : 𝟙_ X.Modules ⟶ M) :
    schemeOpenUnitHomAddEquiv V M
        (Functor.LaxMonoidal.ε (schemeOpenRestriction X V) ≫ (schemeOpenRestriction X V).map u)
      = resTop M (globalSection X M u) V :=
  overTensorUnitHomAddEquiv_eps_comp X.presheaf (isSheaf_structureRingPresheaf X) V
    isTerminalTop M u

/-- **The same, in the `mapTwistSections` spelling.** A twisted section of degree zero is a
morphism out of the monoidal unit, and carrying it along a monoidal functor is the lax unit
followed by its image. -/
theorem schemeOpenUnitHomAddEquiv_mapTwistSections (V : X.Opens) (M L : X.Modules)
    (t : twistSections M L 0) :
    schemeOpenUnitHomAddEquiv V M (mapTwistSections (schemeOpenRestriction X V) t)
      = resTop M (globalSection X M t) V := by
  rw [show mapTwistSections (schemeOpenRestriction X V) t
        = Functor.LaxMonoidal.ε (schemeOpenRestriction X V) ≫
          (schemeOpenRestriction X V).map t from
      congrArg (fun z => Functor.LaxMonoidal.ε (schemeOpenRestriction X V) ≫ z)
        (Category.comp_id ((schemeOpenRestriction X V).map t))]
  exact schemeOpenUnitHomAddEquiv_eps_comp V M t

/-! ### The scalar of the division multiplicativity -/

section Scalar


/-- **Composing with a degree-zero section multiplies the section over `V` by its slice scalar.**
This is `Stacks.SectionRingGeometric.globalSection_unitComp_onSite` on the slice site over `V`,
with the degree-zero section carried there by `Stacks.TwistedSections.mapTwistSections_unitComp`.
-/
theorem schemeOpenUnitHomAddEquiv_unitComp (L : X.Modules) (V : X.Opens)
    (e : powSections L 0) (F : X.Modules) (w : 𝟙_ X.Modules ⟶ F) :
    schemeOpenUnitHomAddEquiv V F
        (mapTwistSections (schemeOpenRestriction X V) (L := L) (m := 0) (e ≫ w))
      = sliceUnitScalar L V e • schemeOpenUnitHomAddEquiv V F
          (mapTwistSections (schemeOpenRestriction X V) (L := L) (m := 0) w) := by
  rw [mapTwistSections_unitComp (schemeOpenRestriction X V) (F := F) (L := L) e (m := 0) w]
  exact Stacks.SectionRingGeometric.globalSection_unitComp_onSite (sliceRingPresheaf X.presheaf V)
    (isSheaf_sliceRingPresheaf X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) V)
    Over.mkIdTerminal (mapPowSections (schemeOpenRestriction X V) e) _

/-- The two readings of the scalar agree after multiplication by the restriction of any global
section of the form `globalSection X F w`. Both sides of
`schemeOpenUnitHomAddEquiv_unitComp` are computed by
`schemeOpenUnitHomAddEquiv_mapTwistSections`, and on the `X` side composing with `e` multiplies
the global section by `Stacks.SectionRingGeometric.schemeUnitScalar`. -/
theorem smul_resTop_globalSection_eq (L : X.Modules) (V : X.Opens) (e : powSections L 0)
    (F : X.Modules) (w : 𝟙_ X.Modules ⟶ F) :
    Stacks.ProjGlobalSectionsAppTop.resTop V (schemeUnitScalar X e)
        • resTop F (globalSection X F w) V
      = sliceUnitScalar L V e • resTop F (globalSection X F w) V := by
  have hsm : resTop F (schemeUnitScalar X e • globalSection X F w) V
      = Stacks.ProjGlobalSectionsAppTop.resTop V (schemeUnitScalar X e)
        • resTop F (globalSection X F w) V :=
    Scheme.Modules.map_smul F (homOfLE (le_top : V ≤ ⊤)) (schemeUnitScalar X e)
      (globalSection X F w)
  have h1 := schemeOpenUnitHomAddEquiv_unitComp L V e F w
  rw [schemeOpenUnitHomAddEquiv_mapTwistSections V F L (e ≫ w),
    schemeOpenUnitHomAddEquiv_mapTwistSections V F L w,
    show globalSection X F (e ≫ w : twistSections F L 0) =
        schemeUnitScalar X e • globalSection X F w from
      Stacks.SectionRingGeometric.schemeGlobalSection_unitComp X e w,
    hsm] at h1
  exact h1

/-- **The scalar of the division multiplicativity is a restricted global function.**
`Stacks.TwistedSections.sliceUnitScalar L V e` — the function on `V` that
`Stacks.TwistedSections.openDivision_gsmul_unitComp` produces as the multiplier — is the
restriction to `V` of the global function `Stacks.SectionRingGeometric.schemeUnitScalar X e`
attached to the same endomorphism of the monoidal unit of `X.Modules`.

This is the identification piece (iii) of Stacks Tag 0B5I was recorded as still owing. It is read
off `smul_resTop_globalSection_eq` at the monoidal unit and the identity, where the global section
being multiplied is the one `app_unitComparison_hom_resTop_id` identifies with `1`. -/
theorem sliceUnitScalar_eq (L : X.Modules) (V : X.Opens) (e : powSections L 0) :
    sliceUnitScalar L V e
      = Stacks.ProjGlobalSectionsAppTop.resTop V (schemeUnitScalar X e) := by
  have h1 := smul_resTop_globalSection_eq L V e (𝟙_ X.Modules) (𝟙 (𝟙_ X.Modules))
  have h2 := congrArg (Scheme.Modules.Hom.app (unitComparison X).hom V) h1
  rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul,
    app_unitComparison_hom_resTop_id V, smul_unitOneOpen, smul_unitOneOpen] at h2
  exact h2.symm

end Scalar

end Stacks.TwistedSections

end
