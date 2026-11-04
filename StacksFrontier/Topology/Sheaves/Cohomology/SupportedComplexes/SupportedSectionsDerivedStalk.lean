module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.ClosedImmersionStalkOnImage
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetDerivedEquivalence
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SubsingletonSectionsStalk
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SubsingletonSpaceDerivedModules

/-!
# The sections supported at a closed point are the derived stalk there

Let `X` be a ringed space, let `x ∈ X` be a point whose singleton is closed, write
`i : ({x}, 𝒪_X|_{\{x\}}) ⟶ (X, 𝒪_X)` for the inclusion, and let `K` be an object of `D(𝒪_X)`
whose cohomology sheaves are supported on `{x}`.  The sections of `K` supported on `{x}`,
`R𝓗_{\{x\}}(K)`, live on the one-point space, and this file identifies their stalk at the point
with the derived stalk of `K` at `x` on `X`:

`(R𝓗_{\{x\}}(K))_x ≅ K_x`.

This is the comparison recorded as missing in the implementation notes of
`Stacks.Cohomology.SupportedComplexes.derivedSectionsIsoStalkAtClosedPoint`, which reduces
`RΓ(X, K)` to sections on the one-point space `({x}, 𝒪_X|_{\{x\}})` but stops there: the stalk it
produces is that of `𝒪_X|_{\{x\}}`, not of `𝒪_X`.  Supplying the comparison completes that
reduction to `RΓ(X, K) ≅ K_x`, and — more importantly downstream — makes
`Stacks.Cohomology.SupportedComplexes.isoOfStalkModuleDerivedIsoOfSupported` usable from a bare
isomorphism of derived stalks: two complexes supported at `x` with isomorphic derived stalks at
`x` are isomorphic.

The mechanism is Stacks 00AE read on the image of a closed embedding, carried to the derived
category: `i_*` is exact, so `(i_* M)_x ≅ M_x` with scalars restricted along the germ map, which
is `Stacks.ClosedImmersion.derivedStalkPushforwardModuleFunctorIso`; and `i_* R𝓗_{\{x\}}(K) ≅ K`
for `K` supported on `{x}`, which is Stacks 0AEF(2) in the form
`Stacks.Cohomology.SupportedComplexes.derivedPushforwardSupportedSectionsIso`.  The germ map of
`i` is invertible — `i⁻¹𝒪_X = 𝒪_X|_{\{x\}}` — so the restriction of scalars can be transported,
and every statement below is also given with its scalars in the local ring `𝒪_{X,x}`.

## Main definitions

* `Stacks.Cohomology.SupportedComplexes.pointInclusionStalkRingMap`: the germ map
  `𝒪_{X,x} ⟶ (𝒪_X|_{\{x\}})_x` of the inclusion of the closed point, in the `RingCat` spelling
  the module-sheaf cluster uses.
* `Stacks.Cohomology.SupportedComplexes.localRingStalkRingEquiv`: the `CommRingCat`-valued stalk
  `𝒪_{X,x}` is the `RingCat`-valued one, as a ring isomorphism.
* `Stacks.Cohomology.SupportedComplexes.localRingGerm`: the germ map
  `𝒪_{X,x} ⟶ (𝒪_X|_{\{x\}})_x` read out of the one-point space, as a ring homomorphism.
* `Stacks.Cohomology.SupportedComplexes.derivedStalkAtPoint`: **the derived stalk at `x` as a
  functor into `D(Mod(𝒪_{X,x}))`.**
* `Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsStalkIso`: **the comparison**
  `(R𝓗_{\{x\}}(K))_x ≅ K_x`, with the scalars of the left-hand side restricted along the germ map
  of the inclusion.
* `Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsStalkIsoOverLocalRing`: the same
  with both sides read over `𝒪_{X,x}`.
* `Stacks.Cohomology.SupportedComplexes.stalkModuleEquivalenceInverseIso` and
  `Stacks.Cohomology.SupportedComplexes.stalkModuleDerivedEquivalenceInverseIso`: the quasi-inverse
  of the identification `D(Mod(𝒪_{X,x})) ≌ D(Mod(𝒪_X|_{\{x\}}))` is the stalk at the point.
* `Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsDerivedStalkIso`: **the form the
  transport of isomorphisms consumes** — the image of `R𝓗_{\{x\}}(K)` under that quasi-inverse is
  the derived stalk of `K` at `x`.
* `Stacks.Cohomology.SupportedComplexes.derivedSectionsIsoDerivedStalk`: `RΓ(X, K) ≅ K_x`, and
  `Stacks.Cohomology.SupportedComplexes.homologyIsoDerivedStalk` the same in each degree.
* `Stacks.Cohomology.SupportedComplexes.isoOfDerivedStalkIsoOfSupported`: **an isomorphism of
  derived stalks at `x` of two complexes supported at `x` is an isomorphism of the complexes.**
* `Stacks.Cohomology.SupportedComplexes.isoOfRingCatDerivedStalkIsoOfSupported`: the same with the
  derived stalks read over the `RingCat`-valued stalk of the structure sheaf.

## Main results

* `Stacks.Cohomology.SupportedComplexes.isIso_pointInclusionStalkRingMap`: the germ map of the
  inclusion of the closed point is invertible.
* `Stacks.Cohomology.SupportedComplexes.stalkMap_closedSubsetInclusion_eq`: that germ map is the
  inverse of `AlgebraicGeometry.RingedSpace.inverseImageStalkIso`.
* `Stacks.Cohomology.SupportedComplexes.localRingGerm_eq`: the two routes from `𝒪_{X,x}` to
  `(𝒪_X|_{\{x\}})_x` — through the sections of the one-point space, and through the germ map of
  the inclusion — agree.
* `Stacks.Cohomology.SupportedComplexes.sectionsAtPointGerm_eq`: the germ map
  `Γ(X, 𝒪_X) ⟶ (𝒪_X|_{\{x\}})_x` of
  `Stacks.Cohomology.SupportedComplexes.sectionsAtPointGerm` factors through `𝒪_{X,x}`.

## Implementation notes

Two ring homomorphisms `𝒪_{X,x} ⟶ (𝒪_X|_{\{x\}})_x` are in play and they have to be identified
once, in `localRingGerm_eq`, before any of the comparisons can be chained: the germ on the
one-point space composed with
`Stacks.Cohomology.SupportedComplexes.pointBaseRingEquiv` (which is how the identification
`D(Mod(𝒪_{X,x})) ≌ D(Mod(𝒪_X|_{\{x\}}))` reads the local ring), and the germ map of the inclusion
(which is what the computation of the stalk of a pushforward restricts scalars along).  The proof
injects along `Stacks.RingedSpace.ringStalkCommIso` at the point, where
`Stacks.RingedSpace.stalkRingMap_comp_ringStalkCommIso` turns the second into the
`CommRingCat`-valued stalk map of the inclusion, and that map is the inverse of
`AlgebraicGeometry.RingedSpace.inverseImageStalkIso` — which is exactly the isomorphism
`Stacks.Cohomology.SupportedComplexes.pointBaseRingEquiv` is built from, so the two cancel.

The `RingCat`-valued stalk of the structure sheaf and the `CommRingCat`-valued one are different
objects; `localRingStalkRingEquiv` is `Stacks.RingedSpace.ringStalkCommIso` read as a `RingEquiv`,
and restriction of scalars along it is how a derived stalk — which the stalk functor on sheaves
of modules produces over the `RingCat` stalk — is read in `D(Mod(𝒪_{X,x}))`.  Writing it as a
`RingEquiv` between the carriers rather than as a categorical isomorphism keeps the two `Ring`
instances on the carrier from being compared, which is what makes `ModuleCat.restrictScalars`
elaborate at the spelling `ModuleCat.{u} (X.presheaf.stalk x)` that
`Stacks.Cohomology.SupportedComplexes.stalkModuleDerivedEquivalence` is stated at.

The derived statements are the underived ones carried along
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso`, with
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` splitting the composites and
`ModuleCat.restrictScalarsComp'` fusing the successive restrictions of scalars; every functor
occurring is exact, restriction of scalars and the stalk functors unconditionally and the
pushforward because `{x}` is closed.  They are stated at
`CategoryTheory.HasDerivedCategory.standard`, the model the surrounding cluster uses.
`AlgebraicGeometry.SheafOfModules.derivedStalkFunctor` is by definition `mapDerivedCategory` of
the stalk functor, so the two spellings of each derived stalk are the same term.

`stalkModuleDerivedEquivalenceInverseIso` is stated for the quasi-inverse rather than for the
functor because that is the direction
`Stacks.Cohomology.SupportedComplexes.isoOfStalkModuleDerivedIsoOfSupported` consumes: it asks
for an isomorphism of the images of `R𝓗_{\{x\}}(K)` and `R𝓗_{\{x\}}(L)` in `D(Mod(𝒪_{X,x}))`,
and `isoOfDerivedStalkIsoOfSupported` is that transport fed with the derived-stalk comparison at
`K` and at `L`.  `isoOfRingCatDerivedStalkIsoOfSupported` performs the change of rings for a
caller whose isomorphism arrives over the `RingCat`-valued stalk; the conversion has to be done
here because a file that puts a `CommRing` instance on that stalk — as anything written at
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing` must — opens a second `Ring` path on the
carrier, and the `Additive` instance for the restriction of scalars is then no longer
synthesizable there.

Nothing here is tagged.  The identification of the stalk of a pushforward on the image is
Stacks 00AE, the equivalence onto the supported complexes is Stacks 0AEF(2), and the reduction of
`RΓ(X, -)` at a closed point is a step in the proof of Stacks 0G02; the composite below is a
clause of none of the three.

## References

* [Stacks Project, Tag 0G02](https://stacks.math.columbia.edu/tag/0G02)
* [Stacks Project, Tag 0AEF](https://stacks.math.columbia.edu/tag/0AEF)
* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.GlobalKunneth

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) (x : X.carrier)

/-! ### The germ map of the inclusion of a point -/

/-- The germ map `𝒪_{X,x} ⟶ (𝒪_X|_{\{x\}})_x` of the inclusion of the singleton on `x`, in the
`RingCat` spelling of the structure sheaf that the module-sheaf cluster is written in. -/
public abbrev pointInclusionStalkRingMap :
    TopCat.Presheaf.stalk (C := RingCat.{u}) (structureSheafRing X).obj x ⟶
      TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafRing (closedSubsetRingedSpace X ({x} : Set X.carrier))).obj
        (singletonPoint X x) :=
  Stacks.RingedSpace.stalkRingMap (closedSubsetInclusion X ({x} : Set X.carrier))
    (singletonPoint X x)

/-- **The germ map of the inclusion of a point is invertible**: it is a germ map of
`AlgebraicGeometry.RingedSpace.inverseImageProjection`, the Stacks Project's
`i⁻¹𝒪_X = 𝒪_X|_Z`. -/
public theorem isIso_pointInclusionStalkRingMap : IsIso (pointInclusionStalkRingMap X x) :=
  AlgebraicGeometry.RingedSpace.isIso_stalkRingMap_inverseImageProjection X
    (ClosedImmersionSheaves.closedSubsetInclusion ({x} : Set X.carrier)) (singletonPoint X x)

/-- **The `CommRingCat`-valued stalk map of the inclusion of a point is the inverse of
`AlgebraicGeometry.RingedSpace.inverseImageStalkIso`.** This is the identity extracted from the
proof of `AlgebraicGeometry.RingedSpace.isIso_stalkMap_inverseImageProjection`: the two agree on
every germ by `AlgebraicGeometry.RingedSpace.germ_inverseImageStalkIso_inv`. -/
public theorem stalkMap_closedSubsetInclusion_eq :
    (closedSubsetInclusion X ({x} : Set X.carrier)).hom.stalkMap (singletonPoint X x) =
      (AlgebraicGeometry.RingedSpace.inverseImageStalkIso X
        (ClosedImmersionSheaves.closedSubsetInclusion ({x} : Set X.carrier))
        (singletonPoint X x)).inv :=
  (TopCat.Presheaf.stalk_hom_ext _ (fun U hU =>
    AlgebraicGeometry.RingedSpace.germ_inverseImageStalkIso_inv X
      (ClosedImmersionSheaves.closedSubsetInclusion ({x} : Set X.carrier))
      (singletonPoint X x) U hU)).symm

/-- **The local ring at `x` is the `RingCat`-valued stalk of the structure sheaf there**, as a
ring isomorphism: `Stacks.RingedSpace.ringStalkCommIso` read as a `RingEquiv` and inverted, so
that restriction of scalars along it carries a module over the `RingCat` stalk — which is what the
stalk functor on sheaves of modules produces — to an `𝒪_{X,x}`-module. -/
public def localRingStalkRingEquiv :
    X.presheaf.stalk x ≃+*
      TopCat.Presheaf.stalk (C := RingCat.{u}) (structureSheafRing X).obj x :=
  (Stacks.RingedSpace.ringStalkCommIso X x).ringCatIsoToRingEquiv.symm

/-- The germ map `𝒪_{X,x} ⟶ (𝒪_X|_{\{x\}})_x` as the identification
`Stacks.Cohomology.SupportedComplexes.pointBaseRingEquiv` of the local ring with the sections of
the one-point space, followed by the germ there.  This is the homomorphism the quasi-inverse of
`Stacks.Cohomology.SupportedComplexes.stalkModuleEquivalence` restricts scalars along; it agrees
with the germ map of the inclusion by
`Stacks.Cohomology.SupportedComplexes.localRingGerm_eq`. -/
public def localRingGerm :
    X.presheaf.stalk x →+*
      TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafRing (closedSubsetRingedSpace X ({x} : Set X.carrier))).obj
        (singletonPoint X x) :=
  (Stacks.Cohomology.SubsingletonSections.structureGerm
      (closedSubsetRingedSpace X ({x} : Set X.carrier)) (singletonPoint X x) ⊤ trivial).comp
    (pointBaseRingEquiv X x).symm.toRingHom

/-- **The two germ maps `𝒪_{X,x} ⟶ (𝒪_X|_{\{x\}})_x` agree.**  On the left, the local ring is
identified with `Γ({x}, 𝒪_X|_{\{x\}})` and the germ of the one-point space is taken; on the
right, the local ring is identified with the `RingCat`-valued stalk and the germ map of the
inclusion is taken.

Both sides are injected along `Stacks.RingedSpace.ringStalkCommIso` at the point, where
`Stacks.RingedSpace.stalkRingMap_comp_ringStalkCommIso` replaces the germ map of the inclusion by
the `CommRingCat`-valued stalk map, which is the inverse of
`AlgebraicGeometry.RingedSpace.inverseImageStalkIso` — the very isomorphism
`Stacks.Cohomology.SupportedComplexes.pointBaseRingEquiv` is built from. -/
public theorem localRingGerm_eq :
    localRingGerm X x =
      (pointInclusionStalkRingMap X x).hom.comp (localRingStalkRingEquiv X x).toRingHom := by
  refine RingHom.ext fun t => ?_
  obtain ⟨s, rfl⟩ : ∃ s, pointBaseRingEquiv X x s = t :=
    ⟨_, (pointBaseRingEquiv X x).apply_symm_apply t⟩
  have hL : localRingGerm X x (pointBaseRingEquiv X x s) =
      (TopCat.Presheaf.germ (C := RingCat.{u})
        (structureSheafRing (closedSubsetRingedSpace X ({x} : Set X.carrier))).obj ⊤
        (singletonPoint X x) trivial).hom s := by
    rw [show localRingGerm X x (pointBaseRingEquiv X x s) =
        Stacks.Cohomology.SubsingletonSections.structureGerm
            (closedSubsetRingedSpace X ({x} : Set X.carrier)) (singletonPoint X x) ⊤ trivial
          ((pointBaseRingEquiv X x).symm (pointBaseRingEquiv X x s)) from rfl,
      RingEquiv.symm_apply_apply]
  rw [RingHom.comp_apply, hL]
  have hinj : Function.Injective (Stacks.RingedSpace.ringStalkCommIso
      (closedSubsetRingedSpace X ({x} : Set X.carrier)) (singletonPoint X x)).hom.hom :=
    ((ConcreteCategory.isIso_iff_bijective (Stacks.RingedSpace.ringStalkCommIso
      (closedSubsetRingedSpace X ({x} : Set X.carrier)) (singletonPoint X x)).hom).mp
      inferInstance).1
  apply hinj
  rw [Stacks.RingedSpace.ringStalkCommIso_germ
    (closedSubsetRingedSpace X ({x} : Set X.carrier)) (singletonPoint X x) ⊤ trivial s]
  have hsq : (Stacks.RingedSpace.ringStalkCommIso
        (closedSubsetRingedSpace X ({x} : Set X.carrier)) (singletonPoint X x)).hom.hom
      ((pointInclusionStalkRingMap X x).hom
        ((Stacks.RingedSpace.ringStalkCommIso X x).inv.hom (pointBaseRingEquiv X x s))) =
      ((closedSubsetInclusion X ({x} : Set X.carrier)).hom.stalkMap (singletonPoint X x)).hom
        ((Stacks.RingedSpace.ringStalkCommIso X x).hom.hom
          ((Stacks.RingedSpace.ringStalkCommIso X x).inv.hom (pointBaseRingEquiv X x s))) :=
    ConcreteCategory.congr_hom
      (Stacks.RingedSpace.stalkRingMap_comp_ringStalkCommIso
        (closedSubsetInclusion X ({x} : Set X.carrier)) (singletonPoint X x)) _
  have hhi : (Stacks.RingedSpace.ringStalkCommIso X x).hom.hom
      ((Stacks.RingedSpace.ringStalkCommIso X x).inv.hom (pointBaseRingEquiv X x s)) =
      pointBaseRingEquiv X x s :=
    ConcreteCategory.congr_hom (Stacks.RingedSpace.ringStalkCommIso X x).inv_hom_id _
  have he : pointBaseRingEquiv X x s =
      (AlgebraicGeometry.RingedSpace.inverseImageStalkIso X
          (ClosedImmersionSheaves.closedSubsetInclusion ({x} : Set X.carrier))
          (singletonPoint X x)).hom.hom
        (((closedSubsetRingedSpace X ({x} : Set X.carrier)).presheaf.germ ⊤
          (singletonPoint X x) trivial).hom s) := rfl
  rw [show (localRingStalkRingEquiv X x).toRingHom (pointBaseRingEquiv X x s) =
      (Stacks.RingedSpace.ringStalkCommIso X x).inv.hom (pointBaseRingEquiv X x s) from rfl,
    hsq, hhi, stalkMap_closedSubsetInclusion_eq, he]
  exact (ConcreteCategory.congr_hom
    (AlgebraicGeometry.RingedSpace.inverseImageStalkIso X
      (ClosedImmersionSheaves.closedSubsetInclusion ({x} : Set X.carrier))
      (singletonPoint X x)).hom_inv_id _).symm

/-! ### The derived stalk at a point, over the local ring -/

/-- **The derived stalk at `x`, as a functor into `D(Mod(𝒪_{X,x}))`**: the derived stalk functor
of `AlgebraicGeometry.SheafOfModules`, whose values are modules over the `RingCat`-valued stalk,
followed by restriction of scalars along
`Stacks.Cohomology.SupportedComplexes.localRingStalkRingEquiv`.  This is the spelling in which the
derived stalk can be compared with the image of a supported complex under the quasi-inverse of
`Stacks.Cohomology.SupportedComplexes.stalkModuleDerivedEquivalence`. -/
public def derivedStalkAtPoint :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} (X.presheaf.stalk x)) :=
  AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheafRing X) x ⋙
    (ModuleCat.restrictScalars (localRingStalkRingEquiv X x).toRingHom).mapDerivedCategory

/-! ### The stalk of the sections supported at a closed point -/

/-- **The stalk at the point of the sections supported at a closed point is the derived stalk
there.** For `x` a point of a ringed space `X` whose singleton is closed and `K` an object of
`D(𝒪_X)` whose cohomology sheaves are supported on `{x}`,

`(R𝓗_{\{x\}}(K))_x ≅ K_x`,

the left-hand side being the derived stalk on the one-point space `({x}, 𝒪_X|_{\{x\}})` with its
scalars restricted along the germ map of the inclusion, which is the shape the computation of the
stalk of a pushforward produces.

Both inputs are about the inclusion `i` of `{x}`: the stalk of `i_*` on the image is
`Stacks.ClosedImmersion.derivedStalkPushforwardModuleFunctorIso`, and `i_* R𝓗_{\{x\}}(K) ≅ K` for
`K` supported there is [Stacks, Tag 0AEF] part (2) in the form
`Stacks.Cohomology.SupportedComplexes.derivedPushforwardSupportedSectionsIso`. -/
public def derivedSupportedSectionsStalkIso
    (hx : IsClosed ({x} : Set X.carrier))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hK : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X)
      ({x} : Set X.carrier) K) :
    (ModuleCat.restrictScalars (pointInclusionStalkRingMap X x).hom).mapDerivedCategory.obj
        ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctor
            (structureSheafRing (closedSubsetRingedSpace X ({x} : Set X.carrier)))
            (singletonPoint X x)).obj
          ((derivedSupportedSectionsOnClosed X ({x} : Set X.carrier) hx).obj K)) ≅
      (AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheafRing X) x).obj K :=
  letI := pushforward_preservesFiniteLimits X ({x} : Set X.carrier)
  letI := pushforward_preservesFiniteColimits X ({x} : Set X.carrier) hx
  ((Stacks.ClosedImmersion.derivedStalkPushforwardModuleFunctorIso
        (closedSubsetInclusion X ({x} : Set X.carrier)) (singletonPoint X x)
        (closedSubsetInclusion_isClosedEmbedding X ({x} : Set X.carrier) hx).isInducing).app
      ((derivedSupportedSectionsOnClosed X ({x} : Set X.carrier) hx).obj K)).symm ≪≫
    (AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheafRing X) x).mapIso
      (derivedPushforwardSupportedSectionsIso X ({x} : Set X.carrier) hx K hK)

/-- **The comparison with both sides read over the local ring.**
`Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsStalkIso` with its scalars
transported to `𝒪_{X,x}`: the germ map of the inclusion is invertible, so the restriction of
scalars on the left can be replaced by one along
`Stacks.Cohomology.SupportedComplexes.localRingGerm`, which is the restriction of scalars the
identification `D(Mod(𝒪_{X,x})) ≌ D(Mod(𝒪_X|_{\{x\}}))` reads sections with.

The two restrictions of scalars are fused by `ModuleCat.restrictScalarsComp'`, the factorisation
being `Stacks.Cohomology.SupportedComplexes.localRingGerm_eq`. -/
public def derivedSupportedSectionsStalkIsoOverLocalRing
    (hx : IsClosed ({x} : Set X.carrier))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hK : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X)
      ({x} : Set X.carrier) K) :
    (ModuleCat.restrictScalars (localRingGerm X x)).mapDerivedCategory.obj
        ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctor
            (structureSheafRing (closedSubsetRingedSpace X ({x} : Set X.carrier)))
            (singletonPoint X x)).obj
          ((derivedSupportedSectionsOnClosed X ({x} : Set X.carrier) hx).obj K)) ≅
      (derivedStalkAtPoint X x).obj K :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
        (ModuleCat.restrictScalarsComp' (localRingStalkRingEquiv X x).toRingHom
          (pointInclusionStalkRingMap X x).hom (localRingGerm X x)
          (localRingGerm_eq X x))).app _ ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
        (ModuleCat.restrictScalars (pointInclusionStalkRingMap X x).hom)
        (ModuleCat.restrictScalars (localRingStalkRingEquiv X x).toRingHom)).app _ ≪≫
    (ModuleCat.restrictScalars
        (localRingStalkRingEquiv X x).toRingHom).mapDerivedCategory.mapIso
      (derivedSupportedSectionsStalkIso X x hx K hK)

/-! ### The quasi-inverse of the identification at the point is the stalk there -/

/-- **The quasi-inverse of `Mod(𝒪_{X,x}) ≌ Mod(𝒪_X|_{\{x\}}) ` is the stalk at the point.** That
quasi-inverse is sections on the one-point space with scalars carried to `𝒪_{X,x}`, and sections
on a space with at most one point are the stalk by
`Stacks.Cohomology.SubsingletonSections.sectionsIsoStalkFunctor`; the two restrictions of scalars
are fused by `ModuleCat.restrictScalarsComp'`. -/
public def stalkModuleEquivalenceInverseIso :
    (stalkModuleEquivalence X x).inverse ≅
      AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafRing (closedSubsetRingedSpace X ({x} : Set X.carrier)))
          (singletonPoint X x) ⋙
        ModuleCat.restrictScalars (localRingGerm X x) :=
  Functor.isoWhiskerRight
      (Stacks.Cohomology.SubsingletonSections.sectionsIsoStalkFunctor
        (closedSubsetRingedSpace X ({x} : Set X.carrier)) (singletonPoint X x) ⊤ trivial)
      (ModuleCat.restrictScalars (pointBaseRingEquiv X x).symm.toRingHom) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ModuleCat.restrictScalarsComp' _ _ _ rfl).symm

/-- **The derived form**: the quasi-inverse of
`Stacks.Cohomology.SupportedComplexes.stalkModuleDerivedEquivalence` is the derived stalk at the
point of the one-point space, with scalars in `𝒪_{X,x}`.  Both functors of the abelian
identification are exact, so the comparison descends along
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso`, and the composite splits by
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso`. -/
public def stalkModuleDerivedEquivalenceInverseIso :
    (stalkModuleDerivedEquivalence X x).inverse ≅
      AlgebraicGeometry.SheafOfModules.derivedStalkFunctor
          (structureSheafRing (closedSubsetRingedSpace X ({x} : Set X.carrier)))
          (singletonPoint X x) ⋙
        (ModuleCat.restrictScalars (localRingGerm X x)).mapDerivedCategory :=
  Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (stalkModuleEquivalenceInverseIso X x) ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafRing (closedSubsetRingedSpace X ({x} : Set X.carrier)))
        (singletonPoint X x))
      (ModuleCat.restrictScalars (localRingGerm X x))

/-- **The image of `R𝓗_{\{x\}}(K)` in `D(Mod(𝒪_{X,x}))` is the derived stalk of `K` at `x`.**
For `K` in `D(𝒪_X)` with cohomology sheaves supported on the closed point `x`, the quasi-inverse
of the identification `D(Mod(𝒪_{X,x})) ≌ D(Mod(𝒪_X|_{\{x\}}))` carries the sections of `K`
supported on `{x}` to `K_x`.

This is `Stacks.Cohomology.SupportedComplexes.stalkModuleDerivedEquivalenceInverseIso` at
`R𝓗_{\{x\}}(K)` followed by
`Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsStalkIsoOverLocalRing`.  It is what
makes `Stacks.Cohomology.SupportedComplexes.isoOfStalkModuleDerivedIsoOfSupported` usable: that
transport demands an isomorphism of the images of two supported complexes, and this rewrites each
image as a derived stalk. -/
public def derivedSupportedSectionsDerivedStalkIso
    (hx : IsClosed ({x} : Set X.carrier))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hK : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X)
      ({x} : Set X.carrier) K) :
    (stalkModuleDerivedEquivalence X x).inverse.obj
        ((derivedSupportedSectionsOnClosed X ({x} : Set X.carrier) hx).obj K) ≅
      (derivedStalkAtPoint X x).obj K :=
  (stalkModuleDerivedEquivalenceInverseIso X x).app
      ((derivedSupportedSectionsOnClosed X ({x} : Set X.carrier) hx).obj K) ≪≫
    derivedSupportedSectionsStalkIsoOverLocalRing X x hx K hK

/-- **An isomorphism of derived stalks at a closed point is a global isomorphism, for complexes
supported there.** For `K` and `L` in `D(𝒪_X)` whose cohomology sheaves are supported on the
closed point `x`, an isomorphism `K_x ≅ L_x` in `D(Mod(𝒪_{X,x}))` yields `K ≅ L`.

This is `Stacks.Cohomology.SupportedComplexes.isoOfStalkModuleDerivedIsoOfSupported`, whose input
is an isomorphism of the images of `R𝓗_{\{x\}}(K)` and `R𝓗_{\{x\}}(L)` in `D(Mod(𝒪_{X,x}))`, fed
through `Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsDerivedStalkIso` at `K` and
at `L`. -/
public def isoOfDerivedStalkIsoOfSupported
    (hx : IsClosed ({x} : Set X.carrier))
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hK : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X)
      ({x} : Set X.carrier) K)
    (hL : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X)
      ({x} : Set X.carrier) L)
    (φ : (derivedStalkAtPoint X x).obj K ≅ (derivedStalkAtPoint X x).obj L) :
    K ≅ L :=
  isoOfStalkModuleDerivedIsoOfSupported X x hx K L hK hL
    (derivedSupportedSectionsDerivedStalkIso X x hx K hK ≪≫ φ ≪≫
      (derivedSupportedSectionsDerivedStalkIso X x hx L hL).symm)

/-- **The same with the derived stalks read over the `RingCat`-valued stalk of the structure
sheaf.** For `K` and `L` in `D(𝒪_X)` whose cohomology sheaves are supported on the closed point
`x`, an isomorphism of their derived stalks at `x` as complexes of modules over
`TopCat.Presheaf.stalk (C := RingCat) (structureSheafRing X).obj x` — which is the ring
`AlgebraicGeometry.SheafOfModules.derivedStalkFunctor` produces its values over — yields
`K ≅ L`.

This is `Stacks.Cohomology.SupportedComplexes.isoOfDerivedStalkIsoOfSupported`, whose input is an
isomorphism in `D(Mod(𝒪_{X,x}))`: the two rings differ by
`Stacks.Cohomology.SupportedComplexes.localRingStalkRingEquiv`, and the conversion is restriction
of scalars along it. -/
public def isoOfRingCatDerivedStalkIsoOfSupported
    (hx : IsClosed ({x} : Set X.carrier))
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hK : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X)
      ({x} : Set X.carrier) K)
    (hL : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X)
      ({x} : Set X.carrier) L)
    (ψ : (AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheafRing X) x).obj K ≅
      (AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheafRing X) x).obj L) :
    K ≅ L :=
  isoOfDerivedStalkIsoOfSupported X x hx K L hK hL
    ((ModuleCat.restrictScalars
      (localRingStalkRingEquiv X x).toRingHom).mapDerivedCategory.mapIso ψ)

/-! ### Derived global sections of a complex supported at a closed point -/

/-- The germ map `Γ(X, 𝒪_X) ⟶ 𝒪_{X,x}` of the structure sheaf, in the `RingCat` spelling. -/
public abbrev structureSheafGermTop :
    (structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)) →+*
      TopCat.Presheaf.stalk (C := RingCat.{u}) (structureSheafRing X).obj x :=
  (TopCat.Presheaf.germ (C := RingCat.{u}) (structureSheafRing X).obj ⊤ x trivial).hom

/-- **The germ `Γ(X, 𝒪_X) ⟶ (𝒪_X|_{\{x\}})_x` factors through the local ring at `x`.** The
homomorphism `Stacks.Cohomology.SupportedComplexes.sectionsAtPointGerm`, along which the
reduction of `RΓ(X, -)` at a closed point reads its values, is the germ of the structure sheaf of
`X` followed by the germ map of the inclusion of `{x}`. This is the germ square
`Stacks.RingedSpace.stalkRingMap_germ` of the inclusion at the open `⊤`. -/
public theorem sectionsAtPointGerm_eq :
    sectionsAtPointGerm X x =
      (pointInclusionStalkRingMap X x).hom.comp (structureSheafGermTop X x) :=
  RingHom.ext fun r =>
    (Stacks.RingedSpace.stalkRingMap_germ (closedSubsetInclusion X ({x} : Set X.carrier))
      (singletonPoint X x) ⊤ trivial r).symm

/-- **Derived global sections of a complex supported at a closed point are its derived stalk
there.** For `x` a point of a ringed space `X` whose singleton is closed and `K` an object of
`D(𝒪_X)` whose cohomology sheaves are supported on `{x}`,

`RΓ(X, K) ≅ K_x`

in `D(Mod(Γ(X, 𝒪_X)))`, the derived stalk being read as a complex of `Γ(X, 𝒪_X)`-modules along
the germ of the structure sheaf.

This is `Stacks.Cohomology.SupportedComplexes.derivedSectionsIsoStalkAtClosedPoint` — the
reduction to sections on the one-point space performed in the proof of [Stacks, Tag 0G02] —
composed with `Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsStalkIso`, the two
restrictions of scalars being fused along
`Stacks.Cohomology.SupportedComplexes.sectionsAtPointGerm_eq`. It is the statement the
implementation notes of `derivedSectionsIsoStalkAtClosedPoint` record as owed. -/
public def derivedSectionsIsoDerivedStalk
    (hx : IsClosed ({x} : Set X.carrier))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hK : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X)
      ({x} : Set X.carrier) K) :
    (baseSections X).obj K ≅
      (ModuleCat.restrictScalars (structureSheafGermTop X x)).mapDerivedCategory.obj
        ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheafRing X) x).obj K) :=
  derivedSectionsIsoStalkAtClosedPoint X x hx K hK ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
        (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafRing (closedSubsetRingedSpace X ({x} : Set X.carrier)))
          (singletonPoint X x))
        (ModuleCat.restrictScalars (sectionsAtPointGerm X x))).app _ ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
        (ModuleCat.restrictScalarsComp' (structureSheafGermTop X x)
          (pointInclusionStalkRingMap X x).hom (sectionsAtPointGerm X x)
          (sectionsAtPointGerm_eq X x))).app _ ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
        (ModuleCat.restrictScalars (pointInclusionStalkRingMap X x).hom)
        (ModuleCat.restrictScalars (structureSheafGermTop X x))).app _ ≪≫
    (ModuleCat.restrictScalars (structureSheafGermTop X x)).mapDerivedCategory.mapIso
      (derivedSupportedSectionsStalkIso X x hx K hK)

/-- **The reduction to the derived stalk in each degree**: `H^n(X, K) ≅ H^n(K_x)` for `K` with
cohomology sheaves supported on the closed point `x`. -/
public def homologyIsoDerivedStalk
    (hx : IsClosed ({x} : Set X.carrier))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hK : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X)
      ({x} : Set X.carrier) K) (n : ℤ) :
    (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)))) n).obj
        ((baseSections X).obj K) ≅
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)))) n).obj
        ((ModuleCat.restrictScalars (structureSheafGermTop X x)).mapDerivedCategory.obj
          ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctor
            (structureSheafRing X) x).obj K)) :=
  (DerivedCategory.homologyFunctor _ n).mapIso
    (derivedSectionsIsoDerivedStalk X x hx K hK)

end Stacks.Cohomology.SupportedComplexes

end
