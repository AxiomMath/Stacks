module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeCompObject
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkBridge
public import StacksFrontier.AlgebraicGeometry.Perfect.ScalarRestrictionStalk
public import StacksFrontier.Topology.Sheaves.Modules.StalkRestrictScalarsDerived

/-!
# The coefficient-stalk bridge for an arbitrary object

Let `f : X ⟶ S` be a morphism of schemes and `x` a point of `X`. The Tor-dimension conjunct of
relative perfectness (Stacks 0DI0) reads an object `E` of `D(𝒪_X)` over `f^{-1}𝒪_S` on the
inverse-image ringed space, and the stalkwise criterion of Stacks 09U9 turns that into a condition
at the stalk ring `(f^{-1}𝒪_S)_x`. Everything that consumes such a bound — the fibrewise criterion
of Stacks 0DJH, the base-change transfer of Stacks 0C0V — instead reads it over the local ring
`𝒪_{S, f x}` of the base. This file assembles the ingredients of that identification for an
**arbitrary** object `E` and proves it, as
`AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeCanonical_derivedStalk_relative_iff`; see "How the
bridge is assembled, and the route that does not work" below for which route carries it.

`AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeCanonical_stalk_relative_iff` of
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkBridge` is the identification for
the single object `𝒪_X[0]`, which is all that condition (2) of Stacks 069C needs. Extending it to a
variable `E` is what lets the stalkwise criterion be entered for an object that is not a module in
degree zero, which is what the Tor clause of Stacks 0DJZ needs.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.stalkOverBase`: the stalk at `x`, read over the local ring
  `𝒪_{S, f x}` of the base along the stalk map of `f`.
* `AlgebraicGeometry.Scheme.Hom.stalkOverBaseIso`: reading an `𝒪_X`-module over `f^{-1}𝒪_S` and
  then taking the stalk at `x` is `stalkOverBase`, read over `(f^{-1}𝒪_S)_x` along the comparison
  `(f^{-1}𝒪_S)_x ≅ 𝒪_{S, f x}`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.ringStalkMap_eq_comp`: the stalk of the structural map
  `f^{-1}𝒪_S ⟶ 𝒪_X` factors as the comparison `(f^{-1}𝒪_S)_x ≅ 𝒪_{S, f x}`, the stalk map of `f`,
  and the comparison of the `RingCat`- and `CommRingCat`-valued stalks of `𝒪_X`.

## Main results, continued

* `AlgebraicGeometry.Scheme.Hom.derivedStalkScalarRestrictionObjIso`: the stalk at `x` of `E` read
  over `f^{-1}𝒪_S` is the derived stalk of `E`, read over `(f^{-1}𝒪_S)_x` along the stalk of the
  structural map.
* `AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeCanonical_derivedStalk_relative_iff`: **the
  coefficient-stalk bridge at an arbitrary object.** The stalk at `x` of the derived restriction of
  scalars of `E` has Tor amplitude in `[a, b]` over `(f^{-1}𝒪_S)_x` exactly when the derived stalk
  of `E` at `x`, read over `𝒪_{S, f x}`, has Tor amplitude in `[a, b]`.

## How the bridge is assembled, and the route that does not work

The bridge is **not** assembled from `stalkOverBase` and `stalkOverBaseIso`, the two declarations
this module was originally built around. It is assembled from

* `StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_restrictScalars_comp_obj_iff`
  (`StacksFrontier/AlgebraicGeometry/Perfect/RelativeTorAmplitudeCompObject.lean`), the coefficient
  crossing for `τ = σ ∘ ρ` with `ρ` a ring isomorphism, at an arbitrary object. It mentions
  `ModuleCat.restrictScalars` only at *individual* ring homomorphisms, and it is applied to the
  Tor-amplitude *predicate*, so the derived functor of a composite of restrictions of scalars is
  never formed; and
* `AlgebraicGeometry.SheafOfModules.derivedStalkFunctorRestrictScalarsCompIso`
  (`StacksFrontier/Topology/Sheaves/Modules/StalkRestrictScalarsDerived.lean`), which splits the
  derived stalk of a restriction of scalars into its two derived functors.

**The route through `stalkOverBase` does not work.** At a *fixed* morphism of
sheaves of rings instance search does not find the exactness of the restriction of scalars along
the stalk map: the implicit `Ring` arguments that the fixed spelling carries, baked in when the
`abbrev` was declared, agree with the ones instance search offers only at default transparency,
whereas instance search runs at reducible transparency. Four approaches fail — the
splitting by `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` directly; re-stating the
instance in the consuming file; registering the theorems of
`StacksFrontier.AlgebraicGeometry.Perfect.ScalarRestrictionStalk` with `attribute [local instance]`;
and seating the factors of `stalkOverBase` and passing both of them explicitly to
`CategoryTheory.Limits.comp_preservesFiniteLimits`. The last of these reports the instance for the
inner pair of restrictions of scalars as not found even when a syntactically identical one has just
been seated in the same file.

What fixed it is stating the splitting at a **variable** sheaf of rings, where there is no fixed
spelling to disagree with, and instantiating the proved statement here — instantiation runs no
instance search. That is the same device, and for the same reason, as the one the implementation
notes of `StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkBridge` record for
`AlgebraicGeometry.Scheme.Hom.stalkObjRingIso`, whose sheaf of rings is a variable so that the
`Module` instances on its two carriers are findable.

`stalkOverBase` and `stalkOverBaseIso` are kept: they are the module-level content of the
factorisation, and `stalkOverBaseIso` is what pins the two spellings against each other.

## Implementation notes

The three exactness facts for the two restrictions of scalars appearing in `stalkOverBase` are
seated as `local instance`s, for the reason recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Perfect.ScalarRestrictionStalk`: Mathlib's instances are not found
once `StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons` is in the import
closure, and naming them weakens nothing.

Everything is read at `CategoryTheory.HasDerivedCategory.standard`, as in
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkBridge`, because that is the model
the stalkwise criterion of Stacks 09U9 is stated at.

## References

* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 20.48.8 (Tag 09U9)](https://stacks.math.columbia.edu/tag/09U9)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Lemma 15.85.9 (Tag 0DJH)](https://stacks.math.columbia.edu/tag/0DJH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-! ### The factorisation of the coefficient map -/

/-- **The stalk of the structural map `f^{-1}𝒪_S ⟶ 𝒪_X` factors through the local rings.** Read
in `RingCat`, it is the comparison `(f^{-1}𝒪_S)_x ≅ 𝒪_{S, f x}`, followed by the stalk map of `f`,
followed by the inverse of the comparison between the `CommRingCat`- and `RingCat`-valued stalks
of `𝒪_X`.

This is `AlgebraicGeometry.Scheme.Hom.commStalkRingEquiv_comp_ringStalkMap` with the latter
comparison moved to the other side of the equation. -/
public theorem ringStalkMap_eq_comp :
    (SemilinearStalk.ringStalkMap (inverseImageRingToStructure f).hom x).hom
      = ((SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom.comp
            (f.stalkMap x).hom).comp (inverseImageStalkRingEquiv f x).toRingHom :=
  RingHom.ext fun r =>
    ((SemilinearStalk.commStalkRingEquiv X.presheaf x).symm_apply_apply _).symm.trans
      (congrArg (SemilinearStalk.commStalkRingEquiv X.presheaf x).symm
        (DFunLike.congr_fun (commStalkRingEquiv_comp_ringStalkMap f x) r))

/-! ### Exactness of a restriction of scalars, seated for an arbitrary ring homomorphism

`StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits` and its finite-colimit
companion are already instances, and `ModuleCat.restrictScalars` is additive on the nose. Instance
search nonetheless fails to find them at the four ring homomorphisms used below, for the reason
recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Perfect.ScalarRestrictionStalk`. The three facts are therefore
re-seated here for a *variable* ring homomorphism at high priority, so that every spelling of the
ring instances on the two stalk rings is covered by one instance each; nothing is weakened. -/

/-- Restriction of scalars along any ring homomorphism is additive: on underlying abelian groups
it does not move the morphism. -/
local instance (priority := 10000) additive_restrictScalars_any
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    (ModuleCat.restrictScalars.{u} φ).Additive :=
  ⟨fun {_ _} {_ _} => rfl⟩

/-- Restriction of scalars along any ring homomorphism preserves finite limits. -/
local instance (priority := 10000) preservesFiniteLimits_restrictScalars_any
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u} φ) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits φ

/-- Restriction of scalars along any ring homomorphism preserves finite colimits. -/
local instance (priority := 10000) preservesFiniteColimits_restrictScalars_any
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{u} φ) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits φ

/-! ### The stalk read over the local ring of the base -/

/-- **The stalk at `x` of an `𝒪_X`-module, read over the local ring `𝒪_{S, f x}`** along the stalk
map of `f`. The `RingCat`-valued stalk ring of `𝒪_X` is first identified with the local ring
`𝒪_{X, x}` by `SemilinearStalk.commStalkRingEquiv`, and the result is then read over
`𝒪_{S, f x}`.

**Its descent to the derived categories cannot presently be formed.** `CategoryTheory.Functor.mapDerivedCategory` asks for the three exactness instances, and
instance search does not find them for this composite: the second factor,
`ModuleCat.restrictScalars (SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom`,
carries the `NonAssocSemiring` of the target stalk ring through `CommRing.toCommSemiring`, whereas
the one `ModuleCat.restrictScalars` is applied at in the goal comes from
`RingCat.instRingObjForgetRingHomCarrier`; the two agree only at default transparency, so the
exactness instance for the composite is rejected under `implicit` transparency. The isomorphism
`stalkOverBaseIso` below is unaffected — it names both spellings itself, which is what pins them —
so the natural isomorphism is available even though the derived functor of its right-hand side is
not. The coefficient crossing is nonetheless finished, and by exactly the device this note
predicted would be needed — the analogue, for a *variable* sheaf of rings, of
`AlgebraicGeometry.Scheme.Hom.stalkObjRingIso`, namely
`AlgebraicGeometry.SheafOfModules.derivedStalkFunctorRestrictScalarsCompIso`. It is used in
`hasTorAmplitudeCanonical_derivedStalk_relative_iff` below, which never forms the derived functor
of this composite. -/
public abbrev stalkOverBase :
    OXMod.{u, u} X.toRingedSpace ⥤ ModuleCat.{u} (ToType (S.presheaf.stalk (f.base x))) :=
  AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafOfRings.{u} X.toRingedSpace) x ⋙
    ModuleCat.restrictScalars.{u}
      (SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom ⋙
    ModuleCat.restrictScalars.{u} (f.stalkMap x).hom

/-- **Restriction of scalars along the stalk of the structural map, split into three steps.** The
natural isomorphism of functors on modules that `ringStalkMap_eq_comp` gives, obtained by applying
`ModuleCat.restrictScalarsComp'` twice. -/
public def restrictScalarsRingStalkMapFactorsIso :
    ModuleCat.restrictScalars.{u}
        (SemilinearStalk.ringStalkMap (inverseImageRingToStructure f).hom x).hom ≅
      (ModuleCat.restrictScalars.{u}
            (SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom ⋙
          ModuleCat.restrictScalars.{u} (f.stalkMap x).hom) ⋙
        ModuleCat.restrictScalars.{u} (inverseImageStalkRingEquiv f x).toRingHom :=
  ModuleCat.restrictScalarsComp'.{u} (inverseImageStalkRingEquiv f x).toRingHom
      ((SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom.comp
        (f.stalkMap x).hom) _ (ringStalkMap_eq_comp f x) ≪≫
    Functor.isoWhiskerRight
      (ModuleCat.restrictScalarsComp'.{u} (f.stalkMap x).hom
        (SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom _ rfl)
      (ModuleCat.restrictScalars.{u} (inverseImageStalkRingEquiv f x).toRingHom)

/-- **The stalk of a restriction of scalars, read over the local ring of the base.** Reading an
`𝒪_X`-module over `f^{-1}𝒪_S` and taking the stalk at `x` is `stalkOverBase`, read over
`(f^{-1}𝒪_S)_x` along the comparison `(f^{-1}𝒪_S)_x ≅ 𝒪_{S, f x}`.

`AlgebraicGeometry.Scheme.Hom.stalkFunctorScalarRestrictionIso` is the same statement with the
coefficient ring left as `(f^{-1}𝒪_S)_x`; what is added here is the factorisation
`restrictScalarsRingStalkMapFactorsIso` of the coefficient map. -/
public def stalkOverBaseIso :
    scalarRestriction f ⋙
        AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u}
            (RingedSpace.inverseImage S.toRingedSpace f.base)) x ≅
      stalkOverBase f x ⋙
        ModuleCat.restrictScalars.{u} (inverseImageStalkRingEquiv f x).toRingHom :=
  stalkFunctorScalarRestrictionIso f x ≪≫
    Functor.isoWhiskerLeft
      (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafOfRings.{u} X.toRingedSpace) x)
      (restrictScalarsRingStalkMapFactorsIso f x) ≪≫
    (Functor.associator _ _ _).symm


/-! ### Stacks 09U9 for the Tor clause of relative perfectness, at an arbitrary object

`AlgebraicGeometry.Scheme.Hom.locallyHasFiniteRelativeTorDimension_iff_exists_cover` is the
criterion below for the single object `𝒪_X[0]`. The two reductions it is built from —
`AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_iff_of_tensor_eq`, which pins the
family of certificates, and `Stacks.Thickenings.hasTorAmplitude_restrictModules_iff_forall_stalk`,
which is Stacks 09U9 on an open subspace of the bare ringed space `(X, f^{-1}𝒪_S)` with the stalks
read upstairs — are both stated for an arbitrary object, so the criterion holds for one. -/

/-- The stalk ring of the inverse-image ringed space is commutative, at every point. -/
local instance commRing_stalk_inverseImage_at (y : X) :
    CommRing (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafOfRings.{u}
        (RingedSpace.inverseImage S.toRingedSpace f.base)).obj y)) :=
  RingedSpace.commRing_stalk_structureSheafOfRings _ _

/-- **Stacks 09U9 for the Tor clause of relative perfectness.** For a family of certificates
pinned to the genuine tensor product of sheaves of modules, an object `E` of `D(𝒪_X)` read over
`f^{-1}𝒪_S` locally has finite Tor dimension exactly when `X` has an open covering on each member
`U` of which there is a *single* interval `[a, b]` containing the Tor amplitude of the stalk at `y`
of `E` read over `f^{-1}𝒪_S`, over the stalk ring `(f^{-1}𝒪_S)_y`, for every `y ∈ U`.

The interval has to be uniform on each member of the covering, and that is not a defect of the
statement: part (3) of Stacks 08CG quantifies the interval existentially per member, and the
stalkwise criterion of Stacks 09U9 that enters the covering is stated at a fixed interval. -/
public theorem locallyHasFiniteTorDimension_derivedScalarRestriction_iff_exists_cover
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f D)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    RingedSpace.LocallyHasFiniteTorDimension
        (RingedSpace.inverseImage S.toRingedSpace f.base) D
        ((derivedScalarRestriction f).obj E) ↔
      ∃ (I : Type u) (U : I → TopologicalSpace.Opens
          (RingedSpace.inverseImage S.toRingedSpace f.base).carrier),
        iSup U = ⊤ ∧ ∀ i : I, ∃ a b : ℤ, ∀ y : X, y ∈ U i →
          HasTorAmplitudeCanonical
            (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
              (structureSheafOfRings.{u}
                (RingedSpace.inverseImage S.toRingedSpace f.base)).obj y))
            ((AlgebraicGeometry.SheafOfModules.stalkFunctor
                (structureSheafOfRings.{u}
                  (RingedSpace.inverseImage S.toRingedSpace f.base)) y).mapDerivedCategory.obj
              ((derivedScalarRestriction f).obj E)) a b := by
  refine Iff.trans (RingedSpace.locallyHasFiniteTorDimension_iff_of_tensor_eq _ D hD _) ?_
  exact exists_congr fun I => exists_congr fun U => and_congr_right fun _ =>
    forall_congr' fun i => exists_congr fun a => exists_congr fun b =>
      Stacks.Thickenings.hasTorAmplitude_restrictModules_iff_forall_stalk _ (U i) _ a b

/-- **A single interval bounding every stalk gives the Tor clause of relative perfectness.** If one
interval `[a, b]` contains the Tor amplitude of the stalk at `y` of `E` read over `f^{-1}𝒪_S`, over
`(f^{-1}𝒪_S)_y`, for *every* point `y` of `X`, then `E` read over `f^{-1}𝒪_S` locally has finite
Tor dimension, for every family of certificates pinned to the genuine tensor product.

The covering is the one-member covering by `X` itself, which is all the source's proof of
Stacks 0DJZ produces: its interval comes from a *finite* affine open covering and is therefore
uniform on the whole of `X`. -/
public theorem locallyHasFiniteTorDimension_derivedScalarRestriction_of_exists_uniform_bound
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f D)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (h : ∃ a b : ℤ, ∀ y : X,
      HasTorAmplitudeCanonical
        (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (structureSheafOfRings.{u}
            (RingedSpace.inverseImage S.toRingedSpace f.base)).obj y))
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafOfRings.{u}
              (RingedSpace.inverseImage S.toRingedSpace f.base)) y).mapDerivedCategory.obj
          ((derivedScalarRestriction f).obj E)) a b) :
    RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage S.toRingedSpace f.base) D
      ((derivedScalarRestriction f).obj E) := by
  obtain ⟨a, b, hamp⟩ := h
  refine (locallyHasFiniteTorDimension_derivedScalarRestriction_iff_exists_cover f D hD E).mpr
    ⟨PUnit.{u + 1}, fun _ => ⊤,
      le_antisymm le_top fun z _ =>
        TopologicalSpace.Opens.mem_iSup.mpr ⟨PUnit.unit, trivial⟩,
      fun _ => ⟨a, b, fun y _ => hamp y⟩⟩

/-! ### The coefficient-stalk bridge at an arbitrary object -/

/-- The stalk ring of the structure sheaf of `X` is commutative, at every point. -/
local instance commRing_stalk_structure_at (y : X) :
    CommRing (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafOfRings.{u} X.toRingedSpace).obj y)) :=
  RingedSpace.commRing_stalk_structureSheafOfRings _ _

/-- **The derived stalk of the derived restriction of scalars, split.** The stalk at `x` of `E`
read over `f^{-1}𝒪_S` is the derived stalk of `E`, read over `(f^{-1}𝒪_S)_x` along the stalk of the
structural map.

The splitting of the right-hand side into its two derived functors is
`AlgebraicGeometry.SheafOfModules.derivedStalkFunctorRestrictScalarsCompIso`, instantiated at
`AlgebraicGeometry.inverseImageRingToStructure f`. It cannot be assembled here: at this fixed
morphism of sheaves of rings instance search does not find the exactness of the restriction of
scalars along the stalk map, for the reason recorded in the implementation notes above. Stated at a
variable sheaf of rings it is provable, and instantiating a proved statement runs no instance
search. -/
public def derivedStalkScalarRestrictionObjIso
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u}
            (RingedSpace.inverseImage S.toRingedSpace f.base)) x).mapDerivedCategory.obj
        ((derivedScalarRestriction f).obj E) ≅
      (ModuleCat.restrictScalars.{u}
          (SemilinearStalk.ringStalkMap
            (inverseImageRingToStructure f).hom x).hom).mapDerivedCategory.obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} X.toRingedSpace) x).mapDerivedCategory.obj E) :=
  ((derivedScalarRestrictionCompDerivedStalkIso f x).app E).symm ≪≫
    (derivedStalkFunctorScalarRestrictionIso f x).app E ≪≫
    (AlgebraicGeometry.SheafOfModules.derivedStalkFunctorRestrictScalarsCompIso
      (inverseImageRingToStructure f) x).app E

/-- **The coefficient-stalk bridge at an arbitrary object.** The stalk at `x` of the derived
restriction of scalars of `E` has Tor amplitude in `[a, b]` over `(f^{-1}𝒪_S)_x` exactly when the
derived stalk of `E` at `x`, read over `𝒪_{S, f x}`, has Tor amplitude in `[a, b]`.

`AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeCanonical_stalk_relative_iff` in the sibling module
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkBridge` is this statement for the
single object `𝒪_X[0]`, which is all condition (2) of Stacks 069C needs; what is added here is an
arbitrary `E`, which is what the Tor clause of Stacks 0DJZ needs.

The object is identified by `derivedStalkScalarRestrictionObjIso`, and the coefficient crossing is
the factorisation `ringStalkMap_eq_comp` fed to
`StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_restrictScalars_comp_obj_iff`. Note that
`stalkOverBase` is not used: the crossing is applied to the predicate, so the derived functor of
that composite is never formed. -/
public theorem hasTorAmplitudeCanonical_derivedStalk_relative_iff
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (a b : ℤ) :
    HasTorAmplitudeCanonical
        (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (structureSheafOfRings.{u}
            (RingedSpace.inverseImage S.toRingedSpace f.base)).obj x))
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafOfRings.{u}
              (RingedSpace.inverseImage S.toRingedSpace f.base)) x).mapDerivedCategory.obj
          ((derivedScalarRestriction f).obj E)) a b ↔
      HasTorAmplitudeCanonical (ToType (S.presheaf.stalk (f.base x)))
        ((ModuleCat.restrictScalars.{u}
            ((SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom.comp
              (f.stalkMap x).hom)).mapDerivedCategory.obj
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafOfRings.{u} X.toRingedSpace) x).mapDerivedCategory.obj E)) a b := by
  refine Iff.trans ⟨fun h =>
      AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
        (derivedStalkScalarRestrictionObjIso f x E) a b h,
    fun h => AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      (derivedStalkScalarRestrictionObjIso f x E).symm a b h⟩ ?_
  exact StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_restrictScalars_comp_obj_iff
    ((SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom.comp (f.stalkMap x).hom)
    (inverseImageStalkRingEquiv f x).toRingHom
    (SemilinearStalk.ringStalkMap (inverseImageRingToStructure f).hom x).hom
    (inverseImageStalkRingEquiv f x) rfl (ringStalkMap_eq_comp f x) _ a b

end AlgebraicGeometry.Scheme.Hom

end
