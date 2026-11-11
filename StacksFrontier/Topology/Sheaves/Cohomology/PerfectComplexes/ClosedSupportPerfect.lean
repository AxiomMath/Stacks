module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SheafLevel
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedApproximation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalCriterion
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.FiniteFreeRepresentation
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportedCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardAndRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.KInjectiveRestriction
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZeroExact
public import StacksFrontier.Topology.Sheaves.Stalk.Restrict
public import StacksFrontier.AlgebraicGeometry.Conormal.RestrictPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import StacksCore.Tactic.StacksAttribute

/-!
# Perfectness of a derived direct image with closed support

Let `X` be a ringed space, `U ⊆ X` an open subspace and `j : U ⟶ X` the inclusion. If an object
`E` of the derived category of `𝒪_U`-modules is perfect and all of its cohomology sheaves are
supported on a subset of `U` whose image in `X` is closed, then `Rj_* E` is a perfect object of
the derived category of `𝒪_X`-modules. This is Stacks 08DP.

## Main results

* `Stacks.Cohomology.ClosedSupportPerfect.isPerfect_derivedPushforward_of_closedSupport` is the
  tag.
* `Stacks.Cohomology.ClosedSupportPerfect.isStrictlyPerfect_modulePullback` is Stacks 09U6 at
  `RingedSpace.{u, u}`, over the strictly perfect vocabulary of chapter 20; see the note at that
  declaration.

## Implementation notes

The local criterion for perfectness (Stacks 08CN) reduces the statement to exhibiting, on an
open covering of `X`, strictly perfect models for the restrictions of a complex representing
`Rj_* E`. The covering used has two kinds of member:

* the images in `X` of the members of a covering of `U` on which `E` has strictly perfect
  models. On such an image the model is transported from `U` by the base-change isomorphism of
  Stacks 08FE for the Cartesian square relating the two restrictions, together with Stacks 09U6
  for the pullback of a strictly perfect complex along the isomorphism of ringed spaces
  identifying a nested open with its image.
* the complement of the closed support, on which the zero complex is a model: this is where
  Stacks 08DF enters, identifying `Rj_* E` with the extension by zero of `E` and hence making
  its cohomology supported on the closed set, so that its restriction to the complement
  vanishes.

Three spellings of the structure sheaf of rings of a ringed space meet in this file:
`structureSheafRing X` (used by the pushforward and pullback functors, and so by Stacks 08FE),
`StrictlyPerfect.structureSheafOfRings X` (used by `StrictlyPerfect.OXMod` and so by Stacks 08CM,
08CN and the strictly perfect vocabulary), and
`ExtensionByZeroModules.resRing U (structureSheafRing X)` for the restriction to an open subspace
(used by Stacks 08DF). All three unfold to `(sheafCompose _ (forget₂ CommRingCat RingCat)).obj _`,
and the first two are verbatim copies of each other; but both are semireducible definitions, so a
goal mixing two of them is not type-correct at `implicit` transparency and neither a rewrite motive
nor instance search bridges them. Instead of relaxing the transparency globally, the first two are
made reducible at `implicit` transparency by `attribute [local implicit_reducible]`, and the third
-- which also involves Mathlib's semireducible `sheafCompose` and so cannot be reached that way --
is handled by taking the one hypothesis whose statement mentions both spellings,
`Functor.IsRightDerivedFunctor`, as an explicit argument of
`isIso_extensionByZeroToDerivedPushforward_app_of_supported'`, so that the identification is
discharged once by an application's own defeq check.

The lemmas of the section "Supports and vanishing in the derived category" are `private` helpers
of Stacks 08DF in
`StacksFrontier/Topology/Sheaves/Cohomology/SupportedComplexes/PushforwardAndRestriction.lean`; they
are restated here because they are not exported, and making them public would let that section be
deleted.  `structureSheafHom_id` is the identity counterpart of
`RingedSpaceModuleAdjunction.structureSheafHom_comp`, which that file does not record.

## References

* [Stacks Project, Tag 08DP](https://stacks.math.columbia.edu/tag/08DP)
* [Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF), extension by zero and
  derived pushforward agree on objects with closed support.
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE), derived pushforward and
  restriction to an open.
* [Stacks Project, Tag 08CN](https://stacks.math.columbia.edu/tag/08CN), the local criterion for
  perfectness.
* [Stacks Project, Tag 09U6](https://stacks.math.columbia.edu/tag/09U6), pullback of a strictly
  perfect complex.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace StrictlyPerfect
open CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open CategoryTheory.Pretriangulated ZeroObject ExtensionByZeroModules
open Stacks.Cohomology.SupportedComplexes (exactFunctorHomologyIso exactFunctorDerivedHomologyIso)


/- The `open` is restricted to names rather than wholesale: `PushforwardRestriction` also declares
a `CohomologySupportedOn` of its own, and an unrestricted `open` would shadow the `08DA`-tagged
`AlgebraicGeometry.CohomologySupportedOn` this file means by the name. -/
open Stacks.Cohomology.PushforwardRestriction (extensionByZeroToDerivedPushforward
  isIso_extensionByZeroToDerivedPushforward_app_of_supported
  isZero_derived_of_homology_isZero isZero_sheafOfModules_of_stalk_isZero
  isZero_jStar_obj_of_stalk_isZero isZero_stalk_jShriek_of_supported
  cohomologySupportedOn_jShriek cohomologySupportedOn_of_iso
  isZero_derived_restrict_compl_of_supported)

namespace Stacks.Cohomology.ClosedSupportPerfect

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings CategoryTheory.Functor.sheafPushforwardContinuous

/-- The inclusion of a nested open `W ⊆ U ⊆ X` into `X`. -/
abbrev nestedOpenInclusion {X : RingedSpace.{u, u}}
    (U : Opens X) (W : Opens (X.restrict U.isOpenEmbedding)) :
    (X.restrict U.isOpenEmbedding).restrict W.isOpenEmbedding ⟶ X :=
  (X.restrict U.isOpenEmbedding).ofRestrict W.isOpenEmbedding ≫
    X.ofRestrict U.isOpenEmbedding

/-- The image of a nested open `W ⊆ U` under the composite open immersion into `X` is the
image of `W` under the open embedding of `U`. -/
theorem opensFunctor_nestedOpenInclusion_obj_top {X : RingedSpace.{u, u}}
    (U : Opens X) (W : Opens (X.restrict U.isOpenEmbedding)) :
    (SheafedSpace.IsOpenImmersion.opensFunctor (nestedOpenInclusion U W)).obj ⊤ =
      U.isOpenEmbedding.functor.obj W := by
  apply Opens.ext
  simp only [SheafedSpace.IsOpenImmersion.opensFunctor, IsOpenMap.coe_functor_obj,
    Opens.coe_top, Set.image_univ]
  ext x
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z.1, z.2, hz⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

/-- A covering of `U` by nested opens gives a covering of `U` by their images in `X`. -/
theorem nestedOpenImage_iSup {X : RingedSpace.{u, u}} (U : Opens X)
    {I : Type u} (W : I → Opens (X.restrict U.isOpenEmbedding))
    (hW : (⨆ i, W i) = ⊤) :
    (⨆ i, (SheafedSpace.IsOpenImmersion.opensFunctor
      (nestedOpenInclusion U (W i))).obj ⊤) = U := by
  simp only [opensFunctor_nestedOpenInclusion_obj_top]
  apply Opens.ext
  rw [Opens.coe_iSup]
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, y, -, rfl⟩
    exact y.2
  · intro hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
      (show (⟨x, hx⟩ : (Opens.toTopCat _).obj U) ∈ (⨆ i, W i) by rw [hW]; trivial)
    exact ⟨i, ⟨x, hx⟩, hi, rfl⟩

/-- The nested open immersion and the open immersion of its image have the same range. -/
theorem range_nestedOpenInclusion_eq {X : RingedSpace.{u, u}}
    (U : Opens X) (W : Opens (X.restrict U.isOpenEmbedding)) :
    Set.range (SheafedSpace.forgetToPresheafedSpace.map
        (nestedOpenInclusion U W)).base =
      Set.range (SheafedSpace.forgetToPresheafedSpace.map (X.ofRestrict
        ((SheafedSpace.IsOpenImmersion.opensFunctor
          (nestedOpenInclusion U W)).obj ⊤).isOpenEmbedding)).base := by
  have h1 : Set.range (nestedOpenInclusion U W).hom.base =
      ((SheafedSpace.IsOpenImmersion.opensFunctor
        (nestedOpenInclusion U W)).obj ⊤ : Set X) := by
    simp [SheafedSpace.IsOpenImmersion.opensFunctor]
  exact h1.trans (Opens.set_range_inclusion' _).symm

/-- A nested open subspace `W ⊆ U ⊆ X` is isomorphic, as a ringed space, to the restriction
of `X` to the image of `W` in `X`. -/
noncomputable def nestedOpenToAmbientIso {X : RingedSpace.{u, u}}
    (U : Opens X) (W : Opens (X.restrict U.isOpenEmbedding)) :
    (X.restrict U.isOpenEmbedding).restrict W.isOpenEmbedding ≅
      X.restrict ((SheafedSpace.IsOpenImmersion.opensFunctor
        (nestedOpenInclusion U W)).obj ⊤).isOpenEmbedding :=
  (SheafedSpace.fullyFaithfulForgetToPresheafedSpace (C := CommRingCat.{u})).preimageIso
    (PresheafedSpace.IsOpenImmersion.isoOfRangeEq _ _ (range_nestedOpenInclusion_eq U W))

/-- The isomorphism `nestedOpenToAmbientIso` is compatible with the two immersions into `X`. -/
theorem nestedOpenToAmbientIso_hom_fac {X : RingedSpace.{u, u}}
    (U : Opens X) (W : Opens (X.restrict U.isOpenEmbedding)) :
    (nestedOpenToAmbientIso U W).hom ≫
        X.ofRestrict ((SheafedSpace.IsOpenImmersion.opensFunctor
          (nestedOpenInclusion U W)).obj ⊤).isOpenEmbedding =
      nestedOpenInclusion U W := by
  apply SheafedSpace.forgetToPresheafedSpace.map_injective
  rw [Functor.map_comp]
  simp only [nestedOpenToAmbientIso, Functor.FullyFaithful.preimageIso_hom]
  exact PresheafedSpace.IsOpenImmersion.lift_fac _ _
    (range_nestedOpenInclusion_eq U W).le

/-! ### Pullback of strictly perfect complexes

Tag 09U6 is carried by `Stacks.StrictlyPerfect.Pullback.isStrictlyPerfect_modulePullback`
(in `StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.PullbackOnRingedSpaces`),
at `RingedSpace.{u, u}` over the same vocabulary. The statement is proved again here, on the
finite-free comparison `RingedSpace.finiteFreeIsoFree` of this development, and is left
untagged. -/

/-- Pullback of sheaves of modules along a morphism of ringed spaces is a left adjoint. -/
instance modulePullback_isLeftAdjoint {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    (modulePullback f).IsLeftAdjoint :=
  (modulePullbackPushforwardAdjunction f).isLeftAdjoint

/-- Pullback of sheaves of modules carries a finite free module to a finite free module: both
are the free module on `ULift (Fin n)`, and pullback preserves free modules. -/
noncomputable def modulePullbackFiniteFreeIso {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (n : ℕ) :
    (modulePullback f).obj (finiteFree Y n) ≅ finiteFree X n :=
  letI : (SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f
  letI : (opensMap f).Final := CategoryTheory.final_of_representablyFlat _
  (modulePullback f).mapIso (RingedSpace.finiteFreeIsoFree Y n) ≪≫
    SheafOfModules.pullbackObjFreeIso (structureSheafHom f) (ULift.{u} (Fin n)) ≪≫
    (RingedSpace.finiteFreeIsoFree X n).symm

/-- Pullback of sheaves of modules preserves "is a direct summand of a finite free module":
the given retract of `𝒪_Y^{⊕n}` maps to a retract of its pullback, which is `𝒪_X^{⊕n}`. -/
theorem isDirectSummandOfFiniteFree_modulePullback {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    {A : OXMod.{u, u} Y} (h : IsDirectSummandOfFiniteFree A) :
    IsDirectSummandOfFiniteFree ((modulePullback f).obj A) := by
  obtain ⟨n, ⟨ρ⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract A).mp h
  exact (isDirectSummandOfFiniteFree_iff_retract _).mpr
    ⟨n, ⟨(ρ.map (modulePullback f)).trans (modulePullbackFiniteFreeIso f n).retract⟩⟩

/-- **Stacks 09U6** at `RingedSpace.{u, u}`. The termwise pullback of a strictly perfect
complex along a morphism of ringed spaces is strictly perfect. -/
theorem isStrictlyPerfect_modulePullback {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (P : CochainComplex (OXMod.{u, u} Y) ℤ) (hP : IsStrictlyPerfect P) :
    IsStrictlyPerfect
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) where
  bounded := hP.bounded.subset fun _ hi hzero =>
    hi (Functor.map_isZero (modulePullback f) hzero)
  directSummand i := isDirectSummandOfFiniteFree_modulePullback f (hP.directSummand i)

/-! ### Restriction along an open immersion as a pullback

`RingedSpaceModuleAdjunction.modulePullback` along `X.ofRestrict` and
`Stacks.Cohomology.HigherDirectImage.moduleRestriction` are both left adjoint to pushforward
along the open immersion, so they agree. This is what makes the exactness of restriction
available for the pullback functor, and hence makes the pullback functor an exact right derived
functor of itself. -/

/-- Pullback along the inclusion of an open subspace is ordinary restriction: both are left
adjoint to the pushforward. -/
noncomputable def pullbackOpenRestrictionIso (X : RingedSpace.{u, u}) (U : Opens X) :
    modulePullback (X.ofRestrict U.isOpenEmbedding) ≅
      HigherDirectImage.moduleRestriction X U := by
  change modulePullback (X.ofRestrict U.isOpenEmbedding) ≅ jStar U (structureSheafRing X)
  exact Adjunction.leftAdjointUniq
    (modulePullbackPushforwardAdjunction (X.ofRestrict U.isOpenEmbedding))
    (jStarAdjunction U (structureSheafRing X))

/-- Pullback along an open immersion preserves finite colimits, because restriction does. -/
noncomputable instance pullbackOpen_preservesFiniteColimits (X : RingedSpace.{u, u})
    (U : Opens X) :
    PreservesFiniteColimits (modulePullback (X.ofRestrict U.isOpenEmbedding)) := by
  have : (HigherDirectImage.moduleRestriction X U).PreservesHomology :=
    HigherDirectImage.moduleRestriction_preservesHomology X U
  have : PreservesFiniteColimits (HigherDirectImage.moduleRestriction X U) :=
    (HigherDirectImage.moduleRestriction X U).preservesFiniteColimits_of_preservesHomology
  exact preservesFiniteColimits_of_natIso
    (F := HigherDirectImage.moduleRestriction X U)
    (G := modulePullback (X.ofRestrict U.isOpenEmbedding))
    (pullbackOpenRestrictionIso X U).symm

/-- The derived functor of restriction along an open immersion: restriction is exact, so it is
its own right derived functor. -/
noncomputable abbrev derivedRestrictionAlongOpen (X : RingedSpace.{u, u}) (U : Opens X) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing (X.restrict U.isOpenEmbedding))) :=
  (modulePullback (X.ofRestrict U.isOpenEmbedding)).mapDerivedCategory

/-- The canonical unit exhibiting `derivedRestrictionAlongOpen` as a right derived functor. -/
noncomputable abbrev derivedRestrictionAlongOpenUnit (X : RingedSpace.{u, u}) (U : Opens X) :
    (modulePullback (X.ofRestrict U.isOpenEmbedding)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedRestrictionAlongOpen X U :=
  (modulePullback (X.ofRestrict U.isOpenEmbedding)).mapDerivedCategoryFactorsh.inv

/-- `derivedRestrictionAlongOpen X U`, with unit `derivedRestrictionAlongOpenUnit X U`, is a right
derived functor of restriction to `U` with respect to quasi-isomorphisms. -/
instance derivedRestrictionAlongOpen_isRightDerived (X : RingedSpace.{u, u}) (U : Opens X) :
    (derivedRestrictionAlongOpen X U).IsRightDerivedFunctor
      (derivedRestrictionAlongOpenUnit X U)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    (modulePullback (X.ofRestrict U.isOpenEmbedding)).mapDerivedCategoryFactorsh

/-! ### Pushforward along an isomorphism of ringed spaces -/

/-- The structure-sheaf comparison of the identity is the identity. -/
theorem structureSheafHom_id (X : RingedSpace.{u, u}) :
    structureSheafHom (𝟙 X) = 𝟙 (structureSheafRing X) := by
  apply (fullyFaithfulSheafToPresheaf _ _).map_injective
  ext U : 2
  rfl

/-- An isomorphism of ringed spaces induces an equivalence of the categories of modules, with
the two pushforwards as the two functors. -/
noncomputable def modulePushforwardEquivalenceOfIso {X Y : RingedSpace.{u, u}} (e : X ≅ Y) :
    SheafOfModules.{u} (structureSheafRing X) ≌ SheafOfModules.{u} (structureSheafRing Y) :=
  CategoryTheory.Equivalence.mk (modulePushforward e.hom) (modulePushforward e.inv)
    (modulePushforwardComp e.hom e.inv ≪≫
        eqToIso (congrArg modulePushforward e.hom_inv_id) ≪≫
        modulePushforwardId X).symm
    (modulePushforwardComp e.inv e.hom ≪≫
      eqToIso (congrArg modulePushforward e.inv_hom_id) ≪≫
      modulePushforwardId Y)

/-- Pushforward of modules along an isomorphism of ringed spaces is an equivalence. -/
noncomputable instance modulePushforwardIso_isEquivalence {X Y : RingedSpace.{u, u}}
    (e : X ≅ Y) : (modulePushforward e.hom).IsEquivalence :=
  (modulePushforwardEquivalenceOfIso e).isEquivalence_functor

/-- Pushforward of modules along an isomorphism of ringed spaces preserves finite limits. -/
noncomputable instance modulePushforwardIso_preservesFiniteLimits {X Y : RingedSpace.{u, u}}
    (e : X ≅ Y) : PreservesFiniteLimits (modulePushforward e.hom) :=
  inferInstance

/-- Pushforward of modules along an isomorphism of ringed spaces preserves finite colimits. -/
noncomputable instance modulePushforwardIso_preservesFiniteColimits {X Y : RingedSpace.{u, u}}
    (e : X ≅ Y) : PreservesFiniteColimits (modulePushforward e.hom) := by
  have : PreservesColimitsOfSize.{u, u} (modulePushforward e.hom) :=
    (modulePushforward e.hom).asEquivalence.toAdjunction.leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits _

/-- The derived functor of pushforward along an isomorphism of ringed spaces. -/
noncomputable abbrev derivedPushforwardAlongIso {X Y : RingedSpace.{u, u}} (e : X ≅ Y) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) :=
  (modulePushforward e.hom).mapDerivedCategory

/-- The canonical unit exhibiting `derivedPushforwardAlongIso` as a right derived functor. -/
noncomputable abbrev derivedPushforwardAlongIsoUnit {X Y : RingedSpace.{u, u}} (e : X ≅ Y) :
    (modulePushforward e.hom).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedPushforwardAlongIso e :=
  (modulePushforward e.hom).mapDerivedCategoryFactorsh.inv

/-- `derivedPushforwardAlongIso e`, with unit `derivedPushforwardAlongIsoUnit e`, is a right
derived functor of pushforward along `e` with respect to quasi-isomorphisms. -/
instance derivedPushforwardAlongIso_isRightDerived {X Y : RingedSpace.{u, u}} (e : X ≅ Y) :
    (derivedPushforwardAlongIso e).IsRightDerivedFunctor
      (derivedPushforwardAlongIsoUnit e)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    (modulePushforward e.hom).mapDerivedCategoryFactorsh

/-- Pushforward along an isomorphism is pullback along its inverse: both are left adjoint to
pushforward along the inverse. -/
noncomputable def modulePushforwardIso_pullbackInverse {X Y : RingedSpace.{u, u}} (e : X ≅ Y) :
    modulePushforward e.hom ≅ modulePullback e.inv :=
  Adjunction.leftAdjointUniq
    ((modulePushforwardEquivalenceOfIso e).toAdjunction :
      modulePushforward e.hom ⊣ modulePushforward e.inv)
    (modulePullbackPushforwardAdjunction e.inv)

/-! ### Comparing the derived functors on complexes -/

/-- The two spellings of restriction to an open subspace agree: the pseudo-coherence
development's `restrictModules` and the higher-direct-image development's
`moduleRestriction` are the same pushforward. -/
theorem restrictModules_eq_moduleRestriction (X : RingedSpace.{u, u}) (U : Opens X) :
    RingedSpace.restrictModules X U = HigherDirectImage.moduleRestriction X U := rfl

/-- Restriction of `𝒪_X`-modules to an open subspace, named at the `structureSheafRing` spelling
of the structure sheaf that this file uses throughout.

This is `AlgebraicGeometry.RingedSpace.restrictModules` and nothing else -- the body is that
functor -- but its *declared type* names the structure sheaf as `structureSheafRing` rather than
as `StrictlyPerfect.structureSheafOfRings`, and that is what makes it usable here. The two names
are one definition, identified for this file by the `implicit_reducible` attribute above; but
that attribute reaches `default`/`implicit` transparency, whereas typeclass resolution runs at
`instances` transparency, which it does not reach. So an instance proved for a functor whose
type is spelled with `structureSheafOfRings` is invisible to a goal spelled with
`structureSheafRing`, even though the two goals are the same goal. Giving the functor its own
name here gives it its own discrimination-tree key and its own instance at this file's spelling,
which is what lets `NatIso.mapHomologicalComplex` below find both of the instances it needs at
once. -/
noncomputable def restrictModulesRing (X : RingedSpace.{u, u}) (U : Opens X) :
    SheafOfModules.{u} (structureSheafRing X) ⥤
      SheafOfModules.{u} (structureSheafRing (X.restrict U.isOpenEmbedding)) :=
  RingedSpace.restrictModules X U

/-- Restriction to an open subspace does not change the sections of a morphism, so it preserves
zero morphisms. This is `RingedSpace.restrictModules_preservesZeroMorphisms` restated at this
file's spelling of the structure sheaf. -/
noncomputable instance restrictModulesRing_preservesZeroMorphisms (X : RingedSpace.{u, u})
    (U : Opens X) : (restrictModulesRing X U).PreservesZeroMorphisms :=
  inferInstanceAs (Functor.PreservesZeroMorphisms (RingedSpace.restrictModules X U))

/-- Pullback along the inclusion of an open subspace is the restriction functor of the
pseudo-coherence development. -/
noncomputable def pullbackOpenRestrictModulesIso (X : RingedSpace.{u, u}) (U : Opens X) :
    modulePullback (X.ofRestrict U.isOpenEmbedding) ≅ restrictModulesRing X U :=
  pullbackOpenRestrictionIso X U ≪≫ eqToIso (restrictModules_eq_moduleRestriction X U).symm

/-- The derived restriction of the class of a complex is the class of the restricted
complex. -/
noncomputable def derivedRestrictionComplexIso (X : RingedSpace.{u, u}) (U : Opens X)
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (derivedRestrictionAlongOpen X U).obj
        ((DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing X))).obj F) ≅
      (DerivedCategory.Q (C := SheafOfModules.{u}
        (structureSheafRing (X.restrict U.isOpenEmbedding)))).obj
        (RingedSpace.restrictComplex F U) :=
  (modulePullback (X.ofRestrict U.isOpenEmbedding)).mapDerivedCategoryFactors.app F ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
      (pullbackOpenRestrictModulesIso X U) (ComplexShape.up ℤ)).app F)

/-- The derived pushforward along an isomorphism of the class of a complex is the class of the
termwise pullback along the inverse. -/
noncomputable def derivedPushforwardIsoComplexIso {X Y : RingedSpace.{u, u}} (e : X ≅ Y)
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (derivedPushforwardAlongIso e).obj
        ((DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing X))).obj F) ≅
      (DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing Y))).obj
        (((modulePullback e.inv).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) :=
  (modulePushforward e.hom).mapDerivedCategoryFactors.app F ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
      (modulePushforwardIso_pullbackInverse e) (ComplexShape.up ℤ)).app F)

/-! ### Supports and vanishing in the derived category

The vanishing and support lemmas are hosted in
`StacksFrontier/Topology/Sheaves/Cohomology/SupportedComplexes/PushforwardAndRestriction.lean` and
the comparison of an exact functor with homology in
`StacksFrontier/Topology/Sheaves/Cohomology/SupportedComplexes/ClosedSubsetPushforward.lean`; this
module imports both and takes the names from them by the `open`s above. What remains here is the
exactness of restriction and extension by zero, and the form of Stacks 08DF part (2) that takes
the right-derived-functor datum explicitly. -/

variable {Y : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology Y) RingCat.{u})

-- Exactness of `j^*` was reproved here. It is now an unconditional global instance pair,
-- `ExtensionByZeroModules.jStar_preservesFiniteLimits` and `jStar_preservesFiniteColimits`,
-- so the local copies are gone and synthesis finds those.

/-- Extension by zero preserves finite colimits: it is a left adjoint. -/
noncomputable instance jShriek_preservesFiniteColimits (V : Opens Y) :
    PreservesFiniteColimits (jShriek V O) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- **Stacks 08DF, part (2)**, restated with the right-derived-functor datum as an explicit
argument.

Stacks 08DF is stated over `ExtensionByZeroModules.resRing U O`, the restriction of a sheaf of
rings to an open subspace, while a ringed space supplies the structure sheaf of the open
subspace as `structureSheafRing (X.restrict U.isOpenEmbedding)`. The two are
definitionally equal, but only at default transparency: `sheafCompose` is a semireducible
definition, so neither instance search nor a rewrite motive can bridge them, and the
`Functor.IsRightDerivedFunctor` hypothesis -- whose statement mentions both the localization
functor and the class of quasi-isomorphisms, each carrying one of the two spellings -- is
therefore not found. Taking it as an explicit argument moves the identification to the call
site, where it is checked once, by the application's own defeq check. -/
theorem isIso_extensionByZeroToDerivedPushforward_app_of_supported'
    (U : Opens Y) (T : Set Y) (hT : IsClosed T) (hTU : T ⊆ U)
    [(jPush U O).Additive]
    (Rj : DerivedCategory (SheafOfModules.{u} (resRing U O)) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (αj : (jPush U O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    (hRj : Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (resRing U O)) (ComplexShape.up ℤ)))
    (F : DerivedCategory (SheafOfModules.{u} (resRing U O)))
    (hF : CohomologySupportedOn (resRing U O) ((fun x : Usp U ↦ x.1) ⁻¹' T) F) :
    IsIso ((extensionByZeroToDerivedPushforward O U Rj αj).app F) :=
  have := hRj
  isIso_extensionByZeroToDerivedPushforward_app_of_supported O U T hT hTU Rj αj F hF

/-- The cohomology of a derived pushforward is supported on `T`, for an object whose own
cohomology is supported on the preimage of `T` in the open subspace: extension by zero preserves
the support, and on such an object it agrees with the derived pushforward.

The companion of `isIso_extensionByZeroToDerivedPushforward_app_of_supported'`, and stated here
for the same reason. The comparison this transports along is an isomorphism only by that lemma,
whose statement carries the identification of `ExtensionByZeroModules.resRing U O` with the
structure sheaf of the open subspace; that identification holds at default transparency only, so
each use of it is a defeq check of two whole sheaves of rings. Spending it inside the long proof
of Stacks 08DP exhausted that proof's elaboration budget, while here it has its own. -/
private theorem cohomologySupportedOn_derivedPushforward_obj_of_supported'
    (U : Opens Y) (T : Set Y) (hT : IsClosed T) (hTU : T ⊆ U)
    [(jPush U O).Additive]
    (Rj : DerivedCategory (SheafOfModules.{u} (resRing U O)) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (αj : (jPush U O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    (hRj : Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (resRing U O)) (ComplexShape.up ℤ)))
    (F : DerivedCategory (SheafOfModules.{u} (resRing U O)))
    (hF : CohomologySupportedOn (resRing U O) ((fun x : Usp U ↦ x.1) ⁻¹' T) F) :
    CohomologySupportedOn O T (Rj.obj F) :=
  have : IsIso ((extensionByZeroToDerivedPushforward O U Rj αj).app F) :=
    isIso_extensionByZeroToDerivedPushforward_app_of_supported' O U T hT hTU Rj αj hRj F hF
  cohomologySupportedOn_of_iso O T
    (asIso ((extensionByZeroToDerivedPushforward O U Rj αj).app F))
    (cohomologySupportedOn_jShriek O U T F hF)

/-! ### Stacks 08DP -/

/-- Pushforward along the inclusion of an open subspace of a ringed space is additive.

This is `modulePushforward_additive`, reached across the identification of
`ExtensionByZeroModules.jPush` with `modulePushforward` along the open inclusion. That
identification is the `resRing`/`structureSheafRing` one again, so the `change` below is a defeq
check of two whole sheaves of rings; as an instance here it is checked once, rather than inside
each proof that needs the additivity. -/
private instance jPush_additive_of_ringedSpace (X : RingedSpace.{u, u}) (U : Opens X) :
    (jPush U (structureSheafRing X)).Additive := by
  change (modulePushforward (X.ofRestrict U.isOpenEmbedding)).Additive
  exact modulePushforward_additive (X.ofRestrict U.isOpenEmbedding)

/-- On an open subspace where a complex becomes acyclic, the zero complex is a strictly perfect
local model for it.

The local model that
`AlgebraicGeometry.RingedSpace.isPerfect_of_strictlyPerfect_local_models` asks for over the
open set on which the restriction vanishes. Separated from the proof of Stacks 08DP
below because every step of it identifies `ExtensionByZeroModules.jStar` with restriction and
`structureSheafRing` with `StrictlyPerfect.structureSheafOfRings`, and those identifications hold
at default transparency only: run inside that proof they exhaust its elaboration budget between
them, whereas here they have their own. -/
private theorem exists_strictlyPerfect_model_of_isZero_restrict (X : RingedSpace.{u, u})
    (S : Set X) (hS : IsClosed S) (V : Opens X) (hV : V = ⟨Sᶜ, hS.isOpen_compl⟩)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hK : CohomologySupportedOn (structureSheafRing X) S K)
    (G : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (eG : DerivedCategory.Q.obj G ≅ K) :
    ∃ P : CochainComplex (SheafOfModules.{u} (structureSheafRing (X.restrict V.isOpenEmbedding))) ℤ,
      IsStrictlyPerfect P ∧
        Nonempty (DerivedCategory.Q.obj P ≅
          DerivedCategory.Q.obj (RingedSpace.restrictComplex G V)) := by
  have hzV : IsZero ((jStar V (structureSheafRing X)).mapDerivedCategory.obj K) := by
    rw [hV]
    exact isZero_derived_restrict_compl_of_supported (structureSheafRing X) S hS K hK
  have hzG := hzV.of_iso ((jStar V (structureSheafRing X)).mapDerivedCategory.mapIso eG)
  let QX := DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing X))
  let Pzero : CochainComplex
      (SheafOfModules.{u} (structureSheafRing (X.restrict V.isOpenEmbedding))) ℤ := 0
  refine ⟨Pzero, StrictlyPerfect.isStrictlyPerfect_of_forall_isZero fun n =>
    Functor.map_isZero (HomologicalComplex.eval
      (SheafOfModules.{u} (structureSheafRing (X.restrict V.isOpenEmbedding)))
      (ComplexShape.up ℤ) n) (isZero_zero _), ⟨?_⟩⟩
  let QV := DerivedCategory.Q (C := SheafOfModules.{u}
    (structureSheafRing (X.restrict V.isOpenEmbedding)))
  have eQ : (jStar V (structureSheafRing X)).mapDerivedCategory.obj (QX.obj G) ≅
      QV.obj (RingedSpace.restrictComplex G V) := by
    change (jStar V (structureSheafRing X)).mapDerivedCategory.obj (QX.obj G) ≅
        QV.obj ((((jStar V (structureSheafRing X)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G))
    exact ((jStar V (structureSheafRing X)).mapDerivedCategoryFactors).app G
  exact IsZero.iso (Functor.map_isZero QV (isZero_zero _)) (hzG.of_iso eQ.symm)

/-- On a nested open `W ⊆ U`, a strictly perfect local model of a complex representing `E`
transports to a strictly perfect local model, on the image of `W` in `X`, of a complex
representing the derived pushforward of `E`. -/
private theorem exists_strictlyPerfect_model_on_nestedOpen (X : RingedSpace.{u, u}) (U : Opens X)
    (W : Opens (X.restrict U.isOpenEmbedding))
    (Rj : DerivedCategory (SheafOfModules.{u} (structureSheafRing
      (X.restrict U.isOpenEmbedding))) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (αj : (modulePushforward (X.ofRestrict U.isOpenEmbedding)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [Rj.IsRightDerivedFunctor αj (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing
      (X.restrict U.isOpenEmbedding))))
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing
      (X.restrict U.isOpenEmbedding))) ℤ)
    (eFE : DerivedCategory.Q.obj F ≅ E)
    (G : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (eG : DerivedCategory.Q.obj G ≅ Rj.obj E)
    (P : CochainComplex (SheafOfModules.{u} (structureSheafRing
      ((X.restrict U.isOpenEmbedding).restrict W.isOpenEmbedding))) ℤ)
    (hP : IsStrictlyPerfect P) (eP : P ⟶ RingedSpace.restrictComplex F W) (heP : QuasiIso eP) :
    ∃ P' : CochainComplex (SheafOfModules.{u} (structureSheafRing (X.restrict
        ((SheafedSpace.IsOpenImmersion.opensFunctor
          (nestedOpenInclusion U W)).obj ⊤).isOpenEmbedding))) ℤ,
      IsStrictlyPerfect P' ∧ Nonempty (DerivedCategory.Q.obj P' ≅
        DerivedCategory.Q.obj (RingedSpace.restrictComplex G
          ((SheafedSpace.IsOpenImmersion.opensFunctor (nestedOpenInclusion U W)).obj ⊤))) := by
  let B : Opens X := (SheafedSpace.IsOpenImmersion.opensFunctor (nestedOpenInclusion U W)).obj ⊤
  let eIso := nestedOpenToAmbientIso U W
  let iMap := (X.restrict U.isOpenEmbedding).ofRestrict W.isOpenEmbedding
  let fMap := X.ofRestrict U.isOpenEmbedding
  let jMap := X.ofRestrict B.isOpenEmbedding
  have hc : iMap ≫ fMap = eIso.hom ≫ jMap := (nestedOpenToAmbientIso_hom_fac U W).symm
  have hsquare : IsPullback iMap eIso.hom fMap jMap :=
    IsPullback.of_vert_isIso_mono (CommSq.mk hc)
  let bc := derivedPushforwardRestrictIso fMap iMap jMap eIso.hom hsquare
    Rj (derivedPushforwardAlongIso eIso)
    (derivedRestrictionAlongOpen (X.restrict U.isOpenEmbedding) W)
    (derivedRestrictionAlongOpen X B) αj
    (derivedPushforwardAlongIsoUnit eIso)
    (derivedRestrictionAlongOpenUnit (X.restrict U.isOpenEmbedding) W)
    (derivedRestrictionAlongOpenUnit X B)
  refine ⟨_, isStrictlyPerfect_modulePullback eIso.inv P hP, ⟨?_⟩⟩
  let QW := DerivedCategory.Q (C := SheafOfModules.{u}
    (structureSheafRing ((X.restrict U.isOpenEmbedding).restrict W.isOpenEmbedding)))
  have : IsIso (QW.map eP) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso
      (C := SheafOfModules.{u} (structureSheafRing ((X.restrict U.isOpenEmbedding).restrict
        W.isOpenEmbedding))) eP).2 heP
  exact (derivedPushforwardIsoComplexIso eIso P).symm ≪≫
    (derivedPushforwardAlongIso eIso).mapIso
      (asIso (QW.map eP) ≪≫ (derivedRestrictionComplexIso
        (X.restrict U.isOpenEmbedding) W F).symm) ≪≫
    (bc.app ((DerivedCategory.Q (C := SheafOfModules.{u}
      (structureSheafRing (X.restrict U.isOpenEmbedding)))).obj F)).symm ≪≫
    (derivedRestrictionAlongOpen X B).mapIso ((Rj.mapIso eFE) ≪≫ eG.symm) ≪≫
    derivedRestrictionComplexIso X B G

/-- If the opens `B i` cover `U` and `S ⊆ U` is closed, then the `B i` together with the
complement of `S` cover the whole space. -/
private theorem iSup_sumElim_compl_eq_top {Z : Type*} [TopologicalSpace Z] {I : Type*} (U : Opens Z)
    (B : I → Opens Z) (hB : (⨆ i, B i) = U) {S : Set Z} (hS : IsClosed S)
    (hSU : S ⊆ (U : Set Z)) :
    (⨆ j, Sum.elim B (fun _ : Unit => (⟨Sᶜ, hS.isOpen_compl⟩ : Opens Z)) j) = ⊤ := by
  ext x
  simp only [Opens.coe_iSup, Set.mem_iUnion]
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  by_cases hxU : x ∈ (U : Set Z)
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, B i by rwa [hB])
    exact ⟨Sum.inl i, by simpa using hi⟩
  · exact ⟨Sum.inr (), by simpa using fun h : x ∈ S => hxU (hSU h)⟩

/-- **Stacks 08DP.** The derived pushforward of a perfect object on an open subspace is perfect
if its cohomology is supported on a subset closed in the ambient space. -/
@[stacks 08DP]
theorem isPerfect_derivedPushforward_of_closedSupport
    (X : RingedSpace.{u, u}) (U : Opens X) (T : Set (X.restrict U.isOpenEmbedding).carrier)
    (hT : IsClosed ((X.ofRestrict U.isOpenEmbedding).hom.base '' T))
    (Rj : DerivedCategory (SheafOfModules.{u} (structureSheafRing
      (X.restrict U.isOpenEmbedding))) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (αj : (modulePushforward (X.ofRestrict U.isOpenEmbedding)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj)
    [hRj : Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing
      (X.restrict U.isOpenEmbedding))))
    (hE : RingedSpace.IsPerfect (X := X.restrict U.isOpenEmbedding) E)
    (hET : CohomologySupportedOn
      (structureSheafRing (X.restrict U.isOpenEmbedding)) T E) :
    RingedSpace.IsPerfect (X := X) (Rj.obj E) := by
  obtain ⟨F, hF, ⟨eFE⟩⟩ := (RingedSpace.isPerfect_iff E).1 hE
  obtain ⟨I, W, hW, hmodels⟩ := (RingedSpace.isPerfectComplex_iff F).1 hF
  let G : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ :=
    (DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing X))).objPreimage (Rj.obj E)
  let eG : DerivedCategory.Q.obj G ≅ Rj.obj E :=
    (DerivedCategory.Q (C := SheafOfModules.{u} (structureSheafRing X))).objObjPreimageIso
      (Rj.obj E)
  let B : I → Opens X := fun i =>
    (SheafedSpace.IsOpenImmersion.opensFunctor (nestedOpenInclusion U (W i))).obj ⊤
  let S : Set X := (X.ofRestrict U.isOpenEmbedding).hom.base '' T
  let V : Opens X := ⟨Sᶜ, hT.isOpen_compl⟩
  let Cov : I ⊕ Unit → Opens X := Sum.elim B (fun _ => V)
  have hSU : S ⊆ (U : Set X) := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  have hcover : (⨆ j, Cov j) = ⊤ :=
    iSup_sumElim_compl_eq_top U B (nestedOpenImage_iSup U W hW) hT hSU
  apply RingedSpace.isPerfect_of_strictlyPerfect_local_models X (Rj.obj E)
  refine ⟨G, ⟨eG⟩, I ⊕ Unit, Cov, hcover, ?_⟩
  rintro (i | -)
  · obtain ⟨P, hP, ⟨eP, heP⟩⟩ := hmodels i
    exact exists_strictlyPerfect_model_on_nestedOpen X U (W i) Rj αj E F eFE G eG P hP eP heP
  · have hpre : ((fun x : (X.restrict U.isOpenEmbedding).carrier => x.1) ⁻¹' S) = T := by
      ext x
      constructor
      · rintro ⟨y, hy, hxy⟩
        simpa [Subtype.ext hxy] using hy
      · exact fun hx => ⟨x, hx, rfl⟩
    have hsource : CohomologySupportedOn
        (structureSheafRing (X.restrict U.isOpenEmbedding))
        ((fun x : (X.restrict U.isOpenEmbedding).carrier => x.1) ⁻¹' S) E := by
      rwa [hpre]
    exact exists_strictlyPerfect_model_of_isZero_restrict X S hT V rfl (Rj.obj E)
      (cohomologySupportedOn_derivedPushforward_obj_of_supported'
        (structureSheafRing X) U S hT hSU Rj αj hRj E hsource) G eG

end Stacks.Cohomology.ClosedSupportPerfect

end
