module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRestrictOpenFunctorial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras
public import StacksFrontier.AlgebraicGeometry.Modules.MonoRestrictLocality
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictOpenSpellings
public import StacksFrontier.AlgebraicGeometry.RestrictionExact.OverExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction to an open subspace, and Mathlib's restriction along the open immersion

`SheafOfModules.openSubspaceRestriction` is restriction of sheaves of modules to an open
subspace written as the slice restriction followed by the transport to the open subspace. It is
the spelling at which the exterior algebra crosses restriction definitionally
(`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRestrictOpenFunctorial`), while a
splitting of a restricted short complex of `𝒪_X`-modules lives at
`AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι`. This file connects the two and records
the exactness that the cokernel has to cross.

## Main results

* `SheafOfModules.openSubspaceRestriction_eq_overFunctorComp`: the composite spelling is the
  slice restriction followed by `Stacks.SheafOfModules.openSubspaceEquiv`, which is the source of
  `AlgebraicGeometry.SheafOfModules.overFunctorIsoSiteRestrict`.
* `SheafOfModules.openSubspaceRestrictionIsoRestrictFunctor`: **restriction to the open
  subspace is Mathlib's restriction along the open immersion `U.ι`**, as an isomorphism of
  functors — the chain of
  `Stacks.SheafOfModules.RestrictOpen.overFunctorIsoRestrictFunctor` read at the composite
  spelling.
* `SheafOfModules.openSubspaceRestrictionIsoModuleRestriction_hom_app_val_app` and
  `…_inv_app_val_app`: **the comparison is the identity on local sections**, by `rfl`, cheaply.
  This is what lets a construction conjugated by the comparison keep the sectionwise description
  of the construction it conjugates.
* `SheafOfModules.mono_restrictFunctor_map_of_mono_openSubspaceRestriction_map`: **monomorphy
  transports** from the composite spelling to `AlgebraicGeometry.Scheme.Modules.restrictFunctor`,
  which is the form `Stacks.AlgebraicGeometry.Modules.mono_of_mono_restrict_cover` consumes.
* `SheafOfModules.isIso_restrictFunctor_map_of_isIso_openSubspaceRestriction_map`: **invertibility
  transports** the same way, which is the form
  `AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_restrictFunctor_map` consumes.
* `CategoryTheory.ShortComplex.nonempty_splitting_of_natIso`: **a splitting transports along an
  isomorphism of the functors a short complex is mapped by**, so that the splitting of
  [Stacks, Section 0FMK] — which is produced at
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι` — can be read at the composite
  spelling, where the exterior algebra crosses.
* `SheafOfModules.additive_openSubspaceRestriction` and
  `preservesZeroMorphisms_openSubspaceRestriction`: restriction to an open subspace is additive
  and preserves zero morphisms, both by `rfl`, which is what makes a short complex and a
  splitting of one restrict.
* `SheafOfModules.preservesFiniteColimits_openSubspaceRestriction`: **restriction to an open
  subspace is right exact**, so a cokernel crosses it
  (`CategoryTheory.Limits.PreservesCokernel.iso`). This is the cokernel crossing of
  [Stacks, Section 0FMK]; it needs no new argument, each half of the composite being a
  pushforward of sheaves of modules along a continuous functor of sites and those are right
  exact.
* `SheafOfModules.preservesFiniteLimits_openSubspaceRestriction`: **restriction to an open
  subspace is left exact** as well, so it is exact and an image crosses it.
* `CategoryTheory.Limits.mapImageSubobjectIso` and its three compatibilities: **a functor
  preserving the limits and colimits that build images carries an image subobject to the image
  subobject of the mapped morphism**, as an isomorphism of the underlying objects. This is what
  the graded piece of the wedge filtration needs, that piece being an `imageSubobject` rather
  than an ambient quotient.

## References

* [Stacks Project, Tag 01AD](https://stacks.math.columbia.edu/tag/01AD)
* [Stacks Project, Section 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules.PushforwardSheafification
open Stacks.SheafOfModules (openSubspaceEquiv openSubspaceEquiv_functor)

universe u

namespace CategoryTheory.ShortComplex

/-- **A splitting of a short complex transports along an isomorphism of the functors it is
mapped by.** `CategoryTheory.ShortComplex.Splitting.map` carries a splitting along one additive
functor and `CategoryTheory.ShortComplex.Splitting.ofIso` along an isomorphism of short
complexes; `CategoryTheory.ShortComplex.mapNatIso` turns the isomorphism of functors into the
second, so no transport of the splitting data itself is needed.

It is stated at a generic pair of additive functors, and not at the two spellings of restriction
to an open, because the hypothesis and the conclusion then fix the ambient category between
them: at the binders of a scheme the two spellings of the category of `𝒪_X`-modules make
instance synthesis fail for `Additive` of whichever functor is not the one the short complex is
written against, each of the two instances being available only at its own spelling. -/
theorem nonempty_splitting_of_natIso {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (T : ShortComplex C) {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G)
    (h : Nonempty (T.map G).Splitting) : Nonempty (T.map F).Splitting :=
  h.elim fun sp => ⟨sp.ofIso (T.mapNatIso e).symm⟩

end CategoryTheory.ShortComplex

namespace CategoryTheory.Limits

section MapImageSubobject

variable {A B : Type*} [Category A] [Category B] [HasEqualizers A] [HasImages A]
  [StrongEpiCategory B] [HasImages B] (L : A ⥤ B)
  [∀ {X Y Z : A} (f : X ⟶ Z) (g : Y ⟶ Z), PreservesLimit (cospan f g) L]
  [∀ {X Y Z : A} (f : X ⟶ Y) (g : X ⟶ Z), PreservesColimit (span f g) L]

/-- **A functor preserving the limits and colimits that build images carries an image subobject
to the image subobject of the mapped morphism.** `CategoryTheory.PreservesImage.iso` is the same
statement for the *chosen* image `CategoryTheory.Limits.image`; this reads it at the underlying
object of `CategoryTheory.Limits.imageSubobject`, through
`CategoryTheory.Limits.imageSubobjectIso` at each end.

The subobject-level form of this — an equality of subobjects of `L.obj Y` rather than an
isomorphism of objects — is already in the library as `map_imageSubobject_eq`
(`StacksFrontier/CategoryTheory/Abelian/InverseSystem.lean`, in the root namespace), proved from
the same `CategoryTheory.PreservesImage.iso`. It is not what a *comparison morphism* can be
built from: a morphism into the restricted graded piece of a filtration has to land in an
object, and the graded piece is the underlying object of an `imageSubobject`. Hence this
orientation, with the three compatibilities below.

Stated at a generic pair of categories, which is both cheap and what makes it usable: the
declaration costs 393 heartbeats here against the default budget of 200,000, and its
instantiation at the restriction of a graded piece of the wedge filtration costs 15,679. -/
def mapImageSubobjectIso {X Y : A} (f : X ⟶ Y) :
    L.obj (imageSubobject f : A) ≅ (imageSubobject (L.map f) : B) :=
  L.mapIso (imageSubobjectIso f) ≪≫ (CategoryTheory.PreservesImage.iso L f).symm ≪≫
    (imageSubobjectIso (L.map f)).symm

/-- **The comparison is compatible with the inclusions of the two images into the ambient
object**: followed by the inclusion of the image of `L.map f`, it is `L` applied to the
inclusion of the image of `f`. This is what identifies a subobject of the restricted ambient
object with the restriction of a subobject. Costs 485 heartbeats. -/
theorem mapImageSubobjectIso_hom_arrow {X Y : A} (f : X ⟶ Y) :
    (mapImageSubobjectIso L f).hom ≫ (imageSubobject (L.map f)).arrow =
      L.map (imageSubobject f).arrow := by
  simp [mapImageSubobjectIso, ← Functor.map_comp]

/-- The same compatibility read along the inverse comparison; it is
`CategoryTheory.Limits.mapImageSubobjectIso_hom_arrow` moved across the isomorphism, and costs
273 heartbeats. -/
theorem mapImageSubobjectIso_inv_comp_map_arrow {X Y : A} (f : X ⟶ Y) :
    (mapImageSubobjectIso L f).inv ≫ L.map (imageSubobject f).arrow =
      (imageSubobject (L.map f)).arrow :=
  (Iso.inv_comp_eq _).mpr (mapImageSubobjectIso_hom_arrow L f).symm

/-- **The comparison is compatible with the factorizations through the two images**: `L` applied
to the factorization of `f` through its image, followed by the comparison, is the factorization
of `L.map f` through its image. Together with
`CategoryTheory.Limits.mapImageSubobjectIso_hom_arrow` this says the comparison is an
isomorphism of factorizations, which is what pins a morphism onto the restricted image down.
Both sides are monomorphic after the ambient inclusion, so this is that cancellation; it costs
429 heartbeats. -/
theorem map_factorThruImageSubobject_comp_mapImageSubobjectIso_hom {X Y : A} (f : X ⟶ Y) :
    L.map (factorThruImageSubobject f) ≫ (mapImageSubobjectIso L f).hom =
      factorThruImageSubobject (L.map f) := by
  rw [← cancel_mono (imageSubobject (L.map f)).arrow, Category.assoc,
    mapImageSubobjectIso_hom_arrow, ← L.map_comp, imageSubobject_arrow_comp,
    imageSubobject_arrow_comp]

end MapImageSubobject

end CategoryTheory.Limits

namespace SheafOfModules

section RingedSpace

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)

/-- **The composite spelling of restriction to an open subspace is the slice restriction
followed by `Stacks.SheafOfModules.openSubspaceEquiv`.** The second leg of
`SheafOfModules.openSubspaceRestriction` is spelled as a pushforward of sheaves of modules and
the forward functor of the equivalence is that pushforward
(`Stacks.SheafOfModules.openSubspaceEquiv_functor`), so this is that identification whiskered
with the slice restriction. -/
theorem openSubspaceRestriction_eq_overFunctorComp :
    openSubspaceRestriction U =
      SheafOfModules.overFunctor (structureSheafRing X) U ⋙ (openSubspaceEquiv U).functor :=
  congrArg (fun F => SheafOfModules.overFunctor (structureSheafRing X) U ⋙ F)
    (openSubspaceEquiv_functor U).symm

/-- **Restriction to the open subspace is restriction along the open-image functor of `U`.**
`Stacks.Cohomology.HigherDirectImage.moduleRestriction` is the spelling at which the tensor
product of sheaves of modules crosses restriction
(`Stacks.SheafOfModules.TensorPower.restrictTensorSheafIso` and its naturality), and the
composite spelling is the one at which the exterior algebra does; this is the comparison
between them, in the shape that lets a crossing proved for one be conjugated into a crossing for
the other.

It is the first half of the chain that
`SheafOfModules.openSubspaceRestrictionIsoRestrictFunctor` completes:
`AlgebraicGeometry.SheafOfModules.overFunctorIsoSiteRestrict` lands in
`AlgebraicGeometry.SheafOfModules.siteRestrict`, which is `moduleRestriction` on the nose
(`Stacks.SheafOfModules.RestrictOpen.siteRestrict_eq_moduleRestriction`).

The two functors are in fact *equal*, and `rfl` proves it — but only just, and only at the
functor level. Against the default budget of 200,000 heartbeats, the functor equality costs
**180,067**, which passes with no room to spare, and the corresponding equality of a *morphism*,
`(openSubspaceRestriction U).map φ = (moduleRestriction X U).map φ`, costs **206,562** and so
**fails**. A statement mixing the two spellings around data as heavy as an exterior algebra or a
tensor product is further past the budget still (393,221 for the exterior-power crossing restated
at `moduleRestriction`). An isomorphism of functors conjugates such a crossing
for nothing, which is why this is the arrow that exists here rather than the equality. -/
def openSubspaceRestrictionIsoModuleRestriction :
    openSubspaceRestriction U ≅ Stacks.Cohomology.HigherDirectImage.moduleRestriction X U :=
  eqToIso (openSubspaceRestriction_eq_overFunctorComp U) ≪≫
    AlgebraicGeometry.SheafOfModules.overFunctorIsoSiteRestrict X U

/-- **The comparison between the two spellings of restriction is the identity on local
sections.** Both functors read the sections of `M` over the image in `X` of an open of `U`, and
both changes of scalars are identities, so this is `rfl` — for 5,119 heartbeats, against the
default budget of 200,000.

This is what makes the comparison usable where a sectionwise computation is wanted: a
construction conjugated by it (`SheafOfModules.openSubspaceTensorIso`, say) still has the
sectionwise description of the construction it conjugates. Note the contrast with the *functor*
equality `openSubspaceRestriction U = moduleRestriction X U`, which is also `rfl` but costs
180,067 and so cannot be used. -/
@[simp]
theorem openSubspaceRestrictionIsoModuleRestriction_hom_app_val_app
    (M : SheafOfModules.{u} (structureSheafRing X)) (V : (Opens ↥U)ᵒᵖ)
    (y : ((openSubspaceRestriction U).obj M).val.obj V) :
    ((openSubspaceRestrictionIsoModuleRestriction U).hom.app M).val.app V y = y :=
  rfl

/-- **The inverse comparison is the identity on local sections too**, for the same reason. -/
@[simp]
theorem openSubspaceRestrictionIsoModuleRestriction_inv_app_val_app
    (M : SheafOfModules.{u} (structureSheafRing X)) (V : (Opens ↥U)ᵒᵖ)
    (y : ((Stacks.Cohomology.HigherDirectImage.moduleRestriction X U).obj M).val.obj V) :
    ((openSubspaceRestrictionIsoModuleRestriction U).inv.app M).val.app V y = y :=
  rfl

/-- **Restriction to an open subspace is right exact.** Both halves of the composite are
pushforwards of sheaves of modules along a continuous functor of sites, and those preserve
finite colimits. With `CategoryTheory.Limits.PreservesCokernel.iso` this is the compatibility of
a cokernel with restriction to an open that the localization of [Stacks, Section 0FMK] needs. -/
@[sga "4 IV 11.2.2" "right exactness"]
instance preservesFiniteColimits_openSubspaceRestriction :
    PreservesFiniteColimits (openSubspaceRestriction U) :=
  inferInstance

/-- **Restriction to an open subspace is left exact**, hence exact, hence preserves images:
`CategoryTheory.Limits.mapImageSubobjectIso` applies to it. Both halves of the composite are
pushforwards of sheaves of modules along a continuous functor of sites, and those preserve
finite limits.

Registered here because the instance for the first half,
`Stacks.AlgebraicGeometry.RestrictionExact.preservesFiniteLimits_overFunctor`, lives in a module
this file did not previously import; with that import the composite needs no argument of its
own. Note that the same fact is also in the library as a *theorem* rather than an instance,
`SheafOfModules.preservesFiniteLimits_overFunctor`
(`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentClosure.lean`), which instance search does
not see — searching for the composite's left exactness therefore fails even though the fact is
present twice over. -/
@[sga "4 IV 11.2.2" "left exactness", sga "6 I 1.3" "partial"]
instance preservesFiniteLimits_openSubspaceRestriction :
    PreservesFiniteLimits (openSubspaceRestriction U) :=
  inferInstance

/-- **Restriction to an open subspace is additive.** Addition of morphisms of sheaves of modules
is computed on local sections and restriction only changes which opens those are read over, so
this is `rfl`. It is what makes a splitting of a short complex restrict. -/
instance additive_openSubspaceRestriction : (openSubspaceRestriction U).Additive where
  map_add := rfl

/-- Restriction to an open subspace preserves zero morphisms, which is what makes a short
complex restrict. Registered explicitly: at the binders of a scheme the two spellings of the
category of modules on the open subscheme keep instance search from finding it through the
composite. -/
instance preservesZeroMorphisms_openSubspaceRestriction :
    (openSubspaceRestriction U).PreservesZeroMorphisms :=
  inferInstance

end RingedSpace

section Scheme

variable (X : Scheme.{u}) (U : X.Opens)

/-- **Restriction of `𝒪_X`-modules to the open subspace `U` is Mathlib's restriction along the
open immersion `U.ι`.** The composite spelling is the slice restriction followed by the
transport to the open subspace
(`SheafOfModules.openSubspaceRestriction_eq_overFunctorComp`), and that is the source of
`Stacks.SheafOfModules.RestrictOpen.overFunctorIsoRestrictFunctor`. -/
def openSubspaceRestrictionIsoRestrictFunctor :
    openSubspaceRestriction (X := X.toRingedSpace) U ≅ Scheme.Modules.restrictFunctor U.ι :=
  eqToIso (openSubspaceRestriction_eq_overFunctorComp (X := X.toRingedSpace) U) ≪≫
    Stacks.SheafOfModules.RestrictOpen.overFunctorIsoRestrictFunctor X U

/-- **Monomorphy transports from restriction to the open subspace to Mathlib's restriction along
the open immersion.** The two functors are isomorphic, so a restricted morphism is a
monomorphism for one exactly when it is for the other
(`CategoryTheory.MorphismProperty.arrow_mk_iso_iff` along `CategoryTheory.Arrow.isoOfNatIso`);
this is the form `Stacks.AlgebraicGeometry.Modules.mono_of_mono_restrict_cover` consumes. -/
theorem mono_restrictFunctor_map_of_mono_openSubspaceRestriction_map {M N : X.Modules}
    (φ : M ⟶ N)
    (h : Mono ((openSubspaceRestriction (X := X.toRingedSpace) U).map φ)) :
    Mono ((Scheme.Modules.restrictFunctor U.ι).map φ) :=
  ((MorphismProperty.monomorphisms _).arrow_mk_iso_iff
    (Arrow.isoOfNatIso (openSubspaceRestrictionIsoRestrictFunctor X U) (Arrow.mk φ))).1 h

/-- **Invertibility transports from restriction to the open subspace to Mathlib's restriction
along the open immersion.** The two functors are isomorphic, so a restricted morphism is an
isomorphism for one exactly when it is for the other; this is the form
`AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_restrictFunctor_map` consumes, and it is what
makes invertibility of a morphism of `𝒪_X`-modules checkable on the opens over which a
construction crossing `SheafOfModules.openSubspaceRestriction` has been identified.

`CategoryTheory.NatIso.isIso_map_iff` already says exactly this for an arbitrary isomorphism of
functors. -/
theorem isIso_restrictFunctor_map_of_isIso_openSubspaceRestriction_map {M N : X.Modules}
    (φ : M ⟶ N)
    (h : IsIso ((openSubspaceRestriction (X := X.toRingedSpace) U).map φ)) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ) :=
  (NatIso.isIso_map_iff (openSubspaceRestrictionIsoRestrictFunctor X U) φ).mp h

end Scheme

end SheafOfModules

end
