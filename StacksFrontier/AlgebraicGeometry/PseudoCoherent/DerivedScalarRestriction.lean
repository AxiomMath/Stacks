module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRestrict
public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageRingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence

/-!
# Restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X` on derived categories

Let `f : X ⟶ S` be a morphism of schemes. The inverse image `f⁻¹𝒪_S` is a sheaf of rings on the
space of `X`, the inverse-image ringed space `(X, f⁻¹𝒪_S)` is
`AlgebraicGeometry.RingedSpace.inverseImage S.toRingedSpace f.base`, and the morphism of schemes
supplies a map of sheaves of rings `f⁻¹𝒪_S ⟶ 𝒪_X` adjoint to `f^♯`. Restriction of scalars along
that map turns an `𝒪_X`-module into an `f⁻¹𝒪_S`-module without changing its underlying sheaf of
abelian groups; in particular it is exact, so it induces a functor on unbounded derived
categories with no resolution and no acyclicity argument at all.

This file constructs that functor and the comparison isomorphism identifying it with termwise
restriction of scalars. It is what makes the relative notions of Stacks 0DI0 — an object of
`D(𝒪_X)` regarded as an object of `D(f⁻¹𝒪_S)` — expressible.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.inverseImageRingToStructure` is the map of sheaves of rings
  `f⁻¹𝒪_S ⟶ 𝒪_X`, viewed in `RingCat`.
* `AlgebraicGeometry.Scheme.Hom.scalarRestriction` is restriction of scalars along it,
  `Mod(𝒪_X) ⥤ Mod(f⁻¹𝒪_S)`.
* `AlgebraicGeometry.Scheme.Hom.derivedScalarRestriction` is the induced functor
  `D(𝒪_X) ⥤ D(f⁻¹𝒪_S)`.
* `AlgebraicGeometry.Scheme.Hom.derivedScalarRestrictionFactors` is the comparison isomorphism
  saying that it is computed termwise.
* `AlgebraicGeometry.Scheme.Hom.derivedScalarRestrictionSigma` bundles the previous two, which is
  the shape Stacks 0DI0 consumes.

## Main results

* `AlgebraicGeometry.RingedSpace.exactFunctor_restrictScalars`: restriction of scalars along any
  map of sheaves of rings whose target is the structure sheaf of a ringed space is exact.
* `AlgebraicGeometry.Scheme.Hom.exactFunctor_scalarRestriction`: the instance of that for
  `f⁻¹𝒪_S ⟶ 𝒪_X`, which is what makes the derived functor exist.
* `AlgebraicGeometry.Scheme.Hom.isRightDerivedFunctor_derivedScalarRestriction`: the induced
  functor is a right derived functor of restriction of scalars, so writing it without an `R` is
  justified.

## Implementation notes

Exactness of `SheafOfModules.restrictScalars` is not available in Mathlib and is proved here.
The argument is the only one available: `SheafOfModules.toSheaf` is faithful and exact, and
restriction of scalars commutes with it *on the nose*, since it changes only the scalars and
leaves the underlying sheaf of abelian groups alone. So
`CategoryTheory.Limits.preservesFiniteLimits_of_reflects_of_preserves` and its colimit
counterpart transfer exactness from `SheafOfModules.toSheaf` on the target to restriction of
scalars. The one non-formal input is that `SheafOfModules.toSheaf` preserves finite colimits,
which is `Stacks.SheafOfModules.FlatShortExact.toSheafColim`; left exactness of
  `SheafOfModules.toSheaf` is a
global instance.

Every binder is written at the `StrictlyPerfect.OXMod` spelling of the category of
`𝒪`-modules, as in `StacksFrontier/AlgebraicGeometry/PseudoCoherent/DerivedRestrict.lean`, so that
all instance synthesis happens in this file; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/PushforwardOXMod.lean` for why that matters. In
particular no fourth spelling of the structure sheaf of rings is introduced: the target of
`AlgebraicGeometry.Scheme.Hom.inverseImageRingToStructure` is
`StrictlyPerfect.structureSheafOfRings X.toRingedSpace`, which is definitionally
`X.ringCatSheaf`.

`CategoryTheory.Limits.PreservesFiniteColimits` is data rather than a proposition, so there is
no way to state that a rebuilt `CategoryTheory.Functor.mapDerivedCategory` *equals* the functor
defined here. `AlgebraicGeometry.Scheme.Hom.derivedScalarRestriction` is therefore the canonical
name for it and consumers should transport along an isomorphism rather than reconstruct it.

The two derived categories are hypotheses with independent universes, as everywhere in this
development; instantiating both at `HasDerivedCategory.standard` recovers the form Stacks 0DI0
is stated in.

## References

* [Stacks Project, Definition 36.60.2 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Section 20.49 (Tag 09V5)](https://stacks.math.columbia.edu/tag/09V5)
* [Stacks Project, Definition 20.46.4 (Tag 08CB)](https://stacks.math.columbia.edu/tag/08CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace StrictlyPerfect

universe d d' u

namespace AlgebraicGeometry

/-! ### Exactness of restriction of scalars -/

namespace RingedSpace

/-- `SheafOfModules.toSheaf` at the structure sheaf of rings of a ringed space preserves finite
colimits. This is `Stacks.SheafOfModules.FlatShortExact.toSheafColim`, restated at the
`StrictlyPerfect.structureSheafOfRings` spelling so that it can be used where the categories of
the pseudo-coherence development appear. -/
public theorem preservesFiniteColimits_toSheaf (Y : RingedSpace.{u, u}) :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{u, u, u, u} (structureSheafOfRings.{u} Y)) :=
  Stacks.SheafOfModules.FlatShortExact.toSheafColim Y

/-- Restriction of scalars along a map of sheaves of rings is additive: it changes only the
module structure, not the underlying sheaf of abelian groups. Mathlib has this as an instance,
but instance search does not find it once the sheaves of rings are the structure sheaves of a
scheme and of its inverse-image ringed space, so it is restated here at binders where the
synthesis succeeds. -/
public theorem additive_restrictScalars (Y : RingedSpace.{u, u})
    {R : Sheaf (Opens.grothendieckTopology Y.carrier) RingCat.{u}}
    (a : R ⟶ structureSheafOfRings.{u} Y) :
    (SheafOfModules.restrictScalars.{u, u, u, u} a).Additive :=
  inferInstance

/-- **Restriction of scalars along a map of sheaves of rings into the structure sheaf of a
ringed space is exact.**

Restriction of scalars does not change the underlying sheaf of abelian groups: the composite of
`SheafOfModules.restrictScalars a` with `SheafOfModules.toSheaf` on the source is *equal* to
`SheafOfModules.toSheaf` on the target. Since `SheafOfModules.toSheaf` is faithful and exact,
exactness transfers.

The finite-colimit hypothesis on the source is `preservesFiniteColimits_toSheaf` whenever the
source sheaf of rings is itself the structure sheaf of a ringed space, which is the only case
used; it is a hypothesis rather than an instance because `SheafOfModules.toSheaf` has no such
global instance. -/
public theorem exactFunctor_restrictScalars (Y : RingedSpace.{u, u})
    {R : Sheaf (Opens.grothendieckTopology Y.carrier) RingCat.{u}}
    (a : R ⟶ structureSheafOfRings.{u} Y)
    (hR : PreservesFiniteColimits (SheafOfModules.toSheaf.{u, u, u, u} R)) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{u, u, u, u} a) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{u, u, u, u} a) := by
  have := hR
  have := preservesFiniteColimits_toSheaf Y
  have hlim : PreservesFiniteLimits (SheafOfModules.restrictScalars.{u, u, u, u} a ⋙
      SheafOfModules.toSheaf.{u, u, u, u} R) := by
    change PreservesFiniteLimits
      (SheafOfModules.toSheaf.{u, u, u, u} (structureSheafOfRings.{u} Y))
    infer_instance
  have hcolim : PreservesFiniteColimits (SheafOfModules.restrictScalars.{u, u, u, u} a ⋙
      SheafOfModules.toSheaf.{u, u, u, u} R) := by
    change PreservesFiniteColimits
      (SheafOfModules.toSheaf.{u, u, u, u} (structureSheafOfRings.{u} Y))
    infer_instance
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _
      (SheafOfModules.toSheaf.{u, u, u, u} R),
    preservesFiniteColimits_of_reflects_of_preserves _
      (SheafOfModules.toSheaf.{u, u, u, u} R)⟩

end RingedSpace

/-! ### Restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X` -/

namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The map of sheaves of rings `f⁻¹𝒪_S ⟶ 𝒪_X` attached to a morphism of schemes `f : X ⟶ S`:
the morphism `AlgebraicGeometry.inverseImageStructureMap f` adjoint to `f^♯`, viewed in
`RingCat`. Its source is the structure sheaf of the inverse-image ringed space
`AlgebraicGeometry.RingedSpace.inverseImage S.toRingedSpace f.base` and its target is
`X.ringCatSheaf`. -/
public def inverseImageRingToStructure :
    structureSheafOfRings.{u} (RingedSpace.inverseImage S.toRingedSpace f.base) ⟶
      structureSheafOfRings.{u} X.toRingedSpace :=
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map (inverseImageStructureMap f)

/-- **Restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X`**, `Mod(𝒪_X) ⥤ Mod(f⁻¹𝒪_S)`: an
`𝒪_X`-module regarded as a module over the inverse image of the structure sheaf of the base.
The underlying sheaf of abelian groups is unchanged. -/
public def scalarRestriction : OXMod.{u, u} X.toRingedSpace ⥤
    OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace f.base) :=
  SheafOfModules.restrictScalars (inverseImageRingToStructure f)

/-- Restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X` is additive. -/
public instance additive_scalarRestriction : (scalarRestriction f).Additive :=
  RingedSpace.additive_restrictScalars X.toRingedSpace (inverseImageRingToStructure f)

/-- **Restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X` is exact.** This is
`AlgebraicGeometry.RingedSpace.exactFunctor_restrictScalars`, whose finite-colimit hypothesis is
discharged by `AlgebraicGeometry.RingedSpace.preservesFiniteColimits_toSheaf` at the
inverse-image ringed space. It is what makes
`AlgebraicGeometry.Scheme.Hom.derivedScalarRestriction` exist. -/
public theorem exactFunctor_scalarRestriction :
    PreservesFiniteLimits (scalarRestriction f) ∧
      PreservesFiniteColimits (scalarRestriction f) :=
  RingedSpace.exactFunctor_restrictScalars X.toRingedSpace (inverseImageRingToStructure f)
    (RingedSpace.preservesFiniteColimits_toSheaf
      (RingedSpace.inverseImage S.toRingedSpace f.base))

/-- Restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X` is left exact. -/
public instance preservesFiniteLimits_scalarRestriction :
    PreservesFiniteLimits (scalarRestriction f) :=
  (exactFunctor_scalarRestriction f).1

/-- Restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X` is right exact. -/
public instance preservesFiniteColimits_scalarRestriction :
    PreservesFiniteColimits (scalarRestriction f) :=
  (exactFunctor_scalarRestriction f).2

/-! ### The induced functor on derived categories -/

section Derived

variable [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)]
  [HasDerivedCategory.{d'} (OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace f.base))]

/-- **Restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X` on derived categories**,
`D(𝒪_X) ⥤ D(f⁻¹𝒪_S)`.

Restriction of scalars is exact
(`AlgebraicGeometry.Scheme.Hom.exactFunctor_scalarRestriction`), so it induces a functor on
unbounded derived categories with no resolution at all. This is the canonical name for that
functor; see the implementation notes on why a consumer must not rebuild it. -/
public def derivedScalarRestriction :
    DerivedCategory (OXMod.{u, u} X.toRingedSpace) ⥤
      DerivedCategory (OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace f.base)) :=
  (scalarRestriction f).mapDerivedCategory

/-- Derived restriction of scalars commutes with the shift. -/
public instance commShiftDerivedScalarRestriction :
    (derivedScalarRestriction f).CommShift ℤ :=
  inferInstanceAs ((scalarRestriction f).mapDerivedCategory.CommShift ℤ)

/-- Derived restriction of scalars is a triangulated functor. -/
public instance isTriangulated_derivedScalarRestriction :
    (derivedScalarRestriction f).IsTriangulated :=
  inferInstanceAs ((scalarRestriction f).mapDerivedCategory.IsTriangulated)

/-- Derived restriction of scalars is a right derived functor of restriction of scalars passed
to homotopy categories, with unit
`CategoryTheory.Functor.mapDerivedCategoryFactorsh.inv`. Since restriction of scalars is exact,
no resolution intervenes; this is what justifies writing the functor without an `R`. -/
public theorem isRightDerivedFunctor_derivedScalarRestriction :
    (derivedScalarRestriction f).IsRightDerivedFunctor
      (scalarRestriction f).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (OXMod.{u, u} X.toRingedSpace) (ComplexShape.up ℤ)) :=
  Stacks.ClosedImmersion.isRightDerivedFunctor_mapDerivedCategory (scalarRestriction f)

/-- **The comparison isomorphism.** On an object in the image of the localization functor
`DerivedCategory.Q`, derived restriction of scalars is computed degreewise by
`AlgebraicGeometry.Scheme.Hom.scalarRestriction`.

This is `CategoryTheory.Functor.mapDerivedCategoryFactors`, and it is what pins the functor
down: for a localization functor an isomorphism `DerivedCategory.Q ⋙ F ≅ DerivedCategory.Q ⋙ G`
forces `F ≅ G`. -/
public def derivedScalarRestrictionFactors :
    DerivedCategory.Q ⋙ derivedScalarRestriction f ≅
      (scalarRestriction f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (scalarRestriction f).mapDerivedCategoryFactors

/-- **Derived restriction of scalars together with its comparison isomorphism**, bundled.

This is the shape in which Stacks 0DI0 uses the functor: the datum of a functor
`D(𝒪_X) ⥤ D(f⁻¹𝒪_S)` whose restriction along `DerivedCategory.Q` is termwise restriction of
scalars. The first component is
`AlgebraicGeometry.Scheme.Hom.derivedScalarRestriction` and the second is
`AlgebraicGeometry.Scheme.Hom.derivedScalarRestrictionFactors`, both by `rfl`, so a statement
phrased through either spelling is the same statement. -/
public def derivedScalarRestrictionSigma :
    Σ' F : DerivedCategory (OXMod.{u, u} X.toRingedSpace) ⥤
      DerivedCategory (OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace f.base)),
      DerivedCategory.Q ⋙ F ≅
        (scalarRestriction f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  ⟨derivedScalarRestriction f, derivedScalarRestrictionFactors f⟩

/-- The first component of the bundled form is the functor. -/
@[simp]
public theorem derivedScalarRestrictionSigma_fst :
    (derivedScalarRestrictionSigma f).1 =
      derivedScalarRestriction f :=
  rfl

/-- The second component of the bundled form is the comparison isomorphism. -/
@[simp]
public theorem derivedScalarRestrictionSigma_snd :
    (derivedScalarRestrictionSigma f).2 =
      derivedScalarRestrictionFactors f :=
  rfl

end Derived

end Scheme.Hom

end AlgebraicGeometry

end
