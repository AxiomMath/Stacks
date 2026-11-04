module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Shift.Adjunction
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.CompactPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional

/-!
# Derived pullback on the quasi-coherent derived categories, and the restricted adjunction

Let `f : X ⟶ Y` be a morphism of schemes. [Stacks, Tag 079W] gives the adjunction
`Lf^* ⊣ Rf_*` on the unbounded derived categories of sheaves of modules, and
`StacksFrontier/AlgebraicGeometry/Duality/QuasiCoherentPushforwardAdjoint.lean` restricts `Rf_*` to
the full subcategories `D_QCoh` of complexes with quasi-coherent cohomology, given that it
preserves quasi-coherence of cohomology. This file does the same for `Lf^*` and restricts the
adjunction itself:

  `Lf^* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)  ⊣  Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`.

The only mathematical input beyond Tag 079W is the `Lf^*` analogue of the hypothesis `hpush` of
that file: that `Lf^*` preserves quasi-coherence of cohomology. Everything else is formal, an
adjunction between ambient categories restricting along fully faithful inclusions with which
both functors commute by construction.

This is what the hypothesis `adj` of
`Duality.DerivedPushforward.isLeftAdjoint_quasiCoherentDerivedPushforward_of_compactPullback`
was standing in for, and the last statement below discharges it: the Stacks route to
[Stacks, Tag 0A9E] now asks for Tag 08D5 for `Rf_*` and for `Lf^*`, Tag 09IS and Tag 09UA, and
for no adjunction.

## Main definitions

All in the namespace `Stacks.Duality`.

* `derivedPullback` — the unbounded derived pullback `Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)` of a morphism of
  schemes, which is `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` of the
  underlying morphism of ringed spaces read in the scheme spelling of the categories.
* `quasiCoherentDerivedPullback` — its restriction `D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`, given that
  `Lf^*` preserves quasi-coherence of cohomology.
* `quasiCoherentDerivedAdjunction` — **the restriction of Tag 079W to the quasi-coherent derived
  categories**: `Lf^* ⊣ Rf_*` on `D_QCoh`.

## Main results

* `Stacks.Duality.commShift_quasiCoherentDerivedPullback` — the restricted `Lf^*` commutes with
  the shift, as the unique such structure compatible with the restricted adjunction.
* `isLeftAdjoint_quasiCoherentDerivedPushforward_of_compactDerivedPullback`, in the namespace
  `Stacks.Duality.DerivedPushforward` — [Stacks, Tag 0A9E] with the adjunction hypothesis of
  `isLeftAdjoint_quasiCoherentDerivedPushforward_of_compactPullback` discharged: what is left is
  Tag 08D5 on both sides, Tag 09IS on both sides and Tag 09UA.

## Implementation notes

*The model of the derived categories.* The statements of this file are at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, as those of
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/CompactPullback.lean` are, and for the
reason given there: it is the only model at which `D_QCoh(𝒪_X)` has the direct sums Brown
representability needs, and `HasDerivedCategory.standard` makes that hypothesis false rather than
unavailable. No declaration here mentions `HasDerivedCategory.standard`.

Unlike `Stacks.Duality.derivedPushforward`, `derivedPullback` is *not* stated at a free
`[HasDerivedCategory.{w}]` binder, and this is forced rather than a choice. Tag 079W is a
statement about ringed spaces, so its derived categories are spelled
`DerivedCategory (SheafOfModules (structureSheafRing X.toSheafedSpace))`; a
binder `[HasDerivedCategory.{w} X.Modules]` is not found for that goal, so instance search falls
to the global locally small instance and the morphism universe comes out as `u` whatever the
binder says. Writing both spellings as binders would give two routes to one instance appearing in
the type of `derivedPullback`, which is the hazard that makes two separately clean modules
mutually unimportable. Since the quasi-coherent results are only available at the locally small
model anyway, the model is fixed here instead. `derivedPullback` does normalize the spelling of
the two categories to `X.Modules` and `Y.Modules`, which is what lets `hpull` below be stated
exactly parallel to `hpush`.

*Why the two compatibility isomorphisms are the identity.* Both restrictions are
`ObjectProperty.lift` of the composite of the inclusion with the ambient functor, so
`ObjectProperty.liftCompιIso` — which is `Iso.refl` — is exactly the datum
`CategoryTheory.Adjunction.restrictFullyFaithful` asks for. Nothing has to be checked: the
restricted adjunction is the ambient one conjugated by fully faithful inclusions.

*Compatibility of the restricted `Lf^*` with the shift* is obtained from the restricted
adjunction through `CategoryTheory.Adjunction.leftAdjointCommShift`, and not from the ambient
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback_commShift` of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/Triangulated.lean`: that instance is
stated under a file-level
`attribute [local instance] HasDerivedCategory.standard` and so bakes the standard model into its
type, where it is of no use here. The adjunction route needs no new input, since the restricted
`Rf_*` commutes with the shift by
`Stacks.Duality.DerivedPushforward.commShift_quasiCoherentDerivedPushforward`, and it delivers the
unique structure compatible with the adjunction.

No `@[stacks]` attribute is attached. Tag 079W is already carried, for an arbitrary morphism of
ringed spaces, by `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction` and its two
compatibility statements; the restriction here is a consequence of it and not a further part of
its statement. Tags 08D5, 09IS, 09UA and 0A9E remain hypotheses below.

## References

* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### Derived pullback of sheaves of modules on schemes -/

/-- The unbounded derived pullback `Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)` along a morphism of schemes. This is
[Stacks, Tag 079W]'s derived pullback of the underlying morphism of ringed spaces, with the two
derived categories spelled in the scheme form; it needs no hypothesis on `f`, the K-flat
complexes being a resolving datum for `f^*`. -/
abbrev derivedPullback : DerivedCategory Y.Modules ⥤ DerivedCategory X.Modules :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom

/-- **The adjunction `Lf^* ⊣ Rf_*` on the unbounded derived categories**, for an arbitrary
morphism of schemes: [Stacks, Tag 079W] read through `derivedPullback` and
`Stacks.Duality.derivedPushforward`, whose underlying functor it is by definition. -/
def derivedAdjunction : derivedPullback f ⊣ derivedPushforward f :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f.toLRSHom.toShHom

/-! ### The restriction of `Lf^*` to quasi-coherent cohomology -/

variable (hpull : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPullback f).obj K.obj)).IsQuasicoherent)

/-- Derived pullback restricted to the complexes with quasi-coherent cohomology, given that it
preserves quasi-coherence of the cohomology sheaves. This is the `Lf^*` counterpart of
`Stacks.Duality.quasiCoherentDerivedPushforward`. -/
abbrev quasiCoherentDerivedPullback :
    quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ derivedPullback f) hpull

/-- The restriction of `Lf^*` to the quasi-coherent derived categories is compatible with the
inclusions: `(restricted Lf^*) ⋙ ι ≅ ι ⋙ Lf^*`, by definition of the restriction. -/
abbrev quasiCoherentDerivedPullbackCompιIso :
    quasiCoherentDerivedPullback f hpull ⋙
        (DerivedCategoryB.derivedCategoryB (A := X.Modules)
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ≅
      (DerivedCategoryB.derivedCategoryB (A := Y.Modules)
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι ⋙ derivedPullback f :=
  (DerivedCategoryB.derivedCategoryB (A := X.Modules)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)).liftCompιIso _ hpull

/-! ### The restricted adjunction -/

variable (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)

/-- **The adjunction `Lf^* ⊣ Rf_*` on the quasi-coherent derived categories.** Let `f : X ⟶ Y` be
a morphism of schemes and suppose both derived pullback and derived direct image preserve
quasi-coherence of cohomology, so that each restricts to the full subcategories `D_QCoh`. Then
the restrictions are again adjoint.

This is [Stacks, Tag 079W] restricted along the inclusions `D_QCoh ⥤ D` by
`CategoryTheory.Adjunction.restrictFullyFaithful`; the two compatibility isomorphisms it asks for
are the identity, because each restriction is by definition the lift of the composite of the
inclusion with the ambient functor. -/
def quasiCoherentDerivedAdjunction :
    quasiCoherentDerivedPullback f hpull ⊣ quasiCoherentDerivedPushforward f hpush :=
  Adjunction.restrictFullyFaithful (derivedAdjunction f)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (quasiCoherentDerivedPullbackCompιIso f hpull).symm
    (DerivedPushforward.quasiCoherentDerivedPushforwardCompιIso f hpush).symm

/-- The restriction of `Lf^*` to the quasi-coherent derived categories commutes with the shift:
the restriction of `Rf_*` does, and a left adjoint of a functor commuting with the shift carries
a unique compatible such structure. -/
@[instance_reducible]
def commShift_quasiCoherentDerivedPullback :
    (quasiCoherentDerivedPullback f hpull).CommShift ℤ :=
  (quasiCoherentDerivedAdjunction f hpull hpush).leftAdjointCommShift ℤ

end Stacks.Duality

namespace Stacks.Duality.DerivedPushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hpull : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPullback f).obj K.obj)).IsQuasicoherent)
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)

/-- **The Stacks proof of [Stacks, Tag 0A9E], with the adjunction hypothesis discharged.** Let
`f : X ⟶ Y` be a morphism of schemes. Suppose

* derived direct image preserves quasi-coherence of cohomology ([Stacks, Tag 08D5], the argument
  `hpush`);
* derived pullback preserves quasi-coherence of cohomology (the argument `hpull`, the `Lf^*`
  half of [Stacks, Tag 08D5]);
* `D_QCoh(𝒪_X)` and `D_QCoh(𝒪_Y)` each have a compact weak generator ([Stacks, Tag 09IS]);
* `Lf^*` carries the generator of `D_QCoh(𝒪_Y)` to a compact object ([Stacks, Tag 09UA]).

Then the restricted derived direct image has a right adjoint — the twisted inverse image `f^×`.

Compared with `isLeftAdjoint_quasiCoherentDerivedPushforward_of_compactPullback` this supplies
the left adjoint and its compatibility with the shift instead of assuming them: the left adjoint
is `Stacks.Duality.quasiCoherentDerivedPullback`, the adjunction is
`Stacks.Duality.quasiCoherentDerivedAdjunction`, and the compatibility with the shift is
`Stacks.Duality.commShift_quasiCoherentDerivedPullback`. -/
theorem isLeftAdjoint_quasiCoherentDerivedPushforward_of_compactDerivedPullback
    (sourceGenerator : quasiCoherentDerivedCategory X) [IsCompactObject.{u} sourceGenerator]
    (hsourceGenerator : (ObjectProperty.singleton sourceGenerator).IsWeakTriangulatedGenerator)
    (targetGenerator : quasiCoherentDerivedCategory Y) [IsCompactObject.{u} targetGenerator]
    (htargetGenerator : (ObjectProperty.singleton targetGenerator).IsWeakTriangulatedGenerator)
    (hpullback : IsCompactObject.{u}
      ((quasiCoherentDerivedPullback f hpull).obj targetGenerator)) :
    (quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint :=
  let := commShift_quasiCoherentDerivedPullback f hpull hpush
  isLeftAdjoint_quasiCoherentDerivedPushforward_of_compactPullback f hpush
    (quasiCoherentDerivedAdjunction f hpull hpush) sourceGenerator hsourceGenerator
    targetGenerator htargetGenerator hpullback

end Stacks.Duality.DerivedPushforward

end
