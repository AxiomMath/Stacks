module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.Dimension
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.CohenMacaulayLocus
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.DoubleRestriction
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.DoubleRestrictionDescent
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.GroupoidSituation
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.RestrictionProperties
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.SliceDimensionDrop
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.SliceSituation
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.SourceFiberIdentity
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Restriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Composition
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FppfLocalTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocusOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
import StacksFrontier.AlgebraicGeometry.Descent.GermSourceAndTarget.Flat
import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeNeTop
public import StacksFrontier.Data.ENat.WithBotNatCast

/-!
# A maximal slice of a Cohen–Macaulay groupoid scheme

Let `(U, R, s, t, c, e, i)` be a groupoid scheme over a scheme `S` with stabilizer group
scheme `G → U`, and assume `s` and `t` are Cohen–Macaulay and locally of finite presentation.
At every finite type point `u` of `U` there is an affine slice `g : U' ⟶ U`, an immersion
through `u` locally of finite presentation, whose restricted groupoid again has Cohen–Macaulay
source and target maps locally of finite presentation and for which the source fibre has, at
the identity arrow, exactly the dimension of the stabilizer fibre.

## Main results

* `AlgebraicGeometry.exists_affine_slice_dim_eq_stabilizer` is the slice, with all six
  conclusions of the source.

## Implementation notes

The slice is produced by minimising the dimension of the restricted source fibre at the
identity arrow over all affine Cohen–Macaulay slices through `u`: the inequality
`dim(G'_u) ≤ dim_{e(u)}(F'_u)` always holds, and strict inequality would let Tag 0461 produce
a strictly smaller slice, contradicting minimality. This replaces the source's induction on
`dim_{e(u)}(F_u)`, which is finite because `s` is locally of finite type; well-foundedness of
`<` on `WithBot ℕ∞` does the same work.

Cohen--Macaulayness of a morphism carries its locally Noetherian fibre witness, so it is
bundled as `cohenMacaulayLocallyOfFinitePresentation`, a morphism property stable under base
change and composition; this is what lets the restricted source and target maps be obtained
from the single morphism `h : U' ×_{g,U,t} R ⟶ U` by Tags 04MP and 04MV, and what lets Tag
04MX descend the property along a composition of slices.

## References

* [Stacks Project, Tag 04MZ](https://stacks.math.columbia.edu/tag/04MZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

open Set Topology

private theorem localDim_eq_of_isOpenEmbedding {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X → Y) (hf : Topology.IsOpenEmbedding f) (x : X) :
    topologicalKrullDimAt X x = topologicalKrullDimAt Y (f x) :=
  hf.topologicalKrullDimAt_eq x |>.symm

private theorem locallyOfFiniteType_of_locallyOfFinitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    LocallyOfFiniteType f := by
  refine ⟨fun {U} hU {V} hV hVU => ?_⟩
  exact RingHom.FiniteType.of_finitePresentation
    (f.finitePresentation_appLE hU hV hVU)

private theorem stabilizerFiber_dim_eq_localDim
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [LocallyOfFinitePresentation G.source.left] (x : G.objects.left)
    (p : (stabilizer G).hom.fiber x) :
    topologicalKrullDim ((stabilizer G).hom.fiber x) =
      topologicalKrullDimAt ((stabilizer G).hom.fiber x) p := by
  let f := (stabilizer G).hom
  let Z := f.fiber x
  let k := G.objects.left.residueField x
  let : LocallyOfFiniteType G.source.left :=
    locallyOfFiniteType_of_locallyOfFinitePresentation G.source.left
  let : IsImmersion (stabilizerArrow G) := AlgebraicGeometry.stabilizerArrow_isImmersion G
  let : LocallyOfFiniteType (stabilizerArrow G) := inferInstance
  have hs : stabilizerArrow G ≫ G.source.left = f := by
    have h := congrArg Over.Hom.left
      (stabilizerArrowHom_source G (𝟙 (stabilizer G)))
    simpa [f, stabilizerArrowHom, stabilizerArrow] using h
  let : LocallyOfFiniteType f := by
    rw [← hs]
    infer_instance
  let : Z.Over (Spec (.of k)) := ⟨f.fiberToSpecResidueField x⟩
  let : GrpObj (Z.asOver (Spec (.of k))) := by
    change GrpObj (Over.mk (f.fiberToSpecResidueField x))
    let : GrpObj (Over.mk f) := by
      change GrpObj (stabilizer G)
      exact (AlgebraicGeometry.stabilizerGroupStructure G).1
    exact Over.grpObjMkPullbackSnd
  let : LocallyOfFiniteType (Z ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (pullback.snd f (G.objects.left.fromSpecResidueField x))
    infer_instance
  exact AlgebraicGeometry.topologicalKrullDim_eq_topologicalKrullDimAt_of_groupScheme k Z p

private noncomputable def stabilizerFiberToSourceFiber
    {S : Scheme.{u}} (G : GroupoidScheme S) (x : G.objects.left) :
    ((stabilizer G).hom.fiber x) ⟶ G.source.left.fiber x := by
  let hs : stabilizerArrow G ≫ G.source.left = (stabilizer G).hom := by
    have h := congrArg Over.Hom.left
      (stabilizerArrowHom_source G (𝟙 (stabilizer G)))
    simpa [stabilizerArrowHom, stabilizerArrow] using h
  exact pullback.map (stabilizer G).hom (G.objects.left.fromSpecResidueField x)
    G.source.left (G.objects.left.fromSpecResidueField x) (stabilizerArrow G)
    (𝟙 _) (𝟙 _) hs.symm (by simp)

private theorem stabilizerFiberToSourceFiber_comp
    {S : Scheme.{u}} (G : GroupoidScheme S) (x : G.objects.left) :
    stabilizerFiberToSourceFiber G x ≫ G.source.left.fiberι x =
      (stabilizer G).hom.fiberι x ≫ stabilizerArrow G := by
  dsimp [stabilizerFiberToSourceFiber, Scheme.Hom.fiberι, Scheme.Hom.fiber,
    pullback.map]
  rw [pullback.lift_fst]

private theorem stabilizerFiberToSourceFiber_isEmbedding
    {S : Scheme.{u}} (G : GroupoidScheme S) (x : G.objects.left) :
    Topology.IsEmbedding (stabilizerFiberToSourceFiber G x) := by
  have hsource : Topology.IsEmbedding (G.source.left.fiberι x) := by
    exact (show IsPreimmersion (G.source.left.fiberι x) from inferInstance).isEmbedding
  have hcomp : Topology.IsEmbedding
      (stabilizerFiberToSourceFiber G x ≫ G.source.left.fiberι x) := by
    rw [stabilizerFiberToSourceFiber_comp]
    let : IsImmersion (stabilizerArrow G) := AlgebraicGeometry.stabilizerArrow_isImmersion G
    change Topology.IsEmbedding
      ((stabilizerArrow G) ∘ ((stabilizer G).hom.fiberι x))
    exact (show Topology.IsEmbedding (stabilizerArrow G) from
      (AlgebraicGeometry.stabilizerArrow_isImmersion G).isEmbedding).comp
        (show IsPreimmersion ((stabilizer G).hom.fiberι x) from inferInstance).isEmbedding
  exact hsource.of_comp_iff.mp hcomp

private theorem stabilizerFiber_dim_le_sourceFiber_localDim
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [LocallyOfFinitePresentation G.source.left] (x : G.objects.left)
    (p : (stabilizer G).hom.fiber x) (q : G.source.left.fiber x)
    (hpq : stabilizerFiberToSourceFiber G x p = q) :
    topologicalKrullDim ((stabilizer G).hom.fiber x) ≤
      topologicalKrullDimAt (G.source.left.fiber x) q := by
  have hgrp := stabilizerFiber_dim_eq_localDim G x p
  have hle := topologicalKrullDimAt_le_of_isEmbedding
    (stabilizerFiberToSourceFiber_isEmbedding G x) p
  rw [hpq] at hle
  exact hgrp ▸ hle

/-- The identity section of the stabilizer lies over each point `x`. -/
private theorem stabilizer_hom_stabilizerOne {S : Scheme.{u}} (G : GroupoidScheme S)
    (x : G.objects.left) : (stabilizer G).hom ((stabilizerOne G).left x) = x := by
  have h := (stabilizerOne G).w
  change (stabilizerOne G).left ≫ (stabilizer G).hom = 𝟙 _ at h
  exact congrArg (fun f => f x) h

private noncomputable def stabilizerFiberIdentityPoint
    {S : Scheme.{u}} (G : GroupoidScheme S) (x : G.objects.left) :
    (stabilizer G).hom.fiber x :=
  stabilizer_hom_stabilizerOne G x ▸ (stabilizer G).hom.asFiber ((stabilizerOne G).left x)

private theorem stabilizerOne_arrow_eq_identity
    {S : Scheme.{u}} (G : GroupoidScheme S) :
    (stabilizerOne G).left ≫ stabilizerArrow G = G.identity.left := by
  have hh : (stabilizerOne G).left ≫ stabilizerArrow G =
      𝟙 G.objects.left ≫ G.identity.left := by
    exact congrArg Over.Hom.left (pullback.lift_fst _ _ _)
  simpa only [Category.id_comp] using hh

private theorem stabilizerFiberToSourceFiber_maps_identity
    {S : Scheme.{u}} (G : GroupoidScheme S) (x : G.objects.left) :
    stabilizerFiberToSourceFiber G x (stabilizerFiberIdentityPoint G x) =
      sourceFiberIdentity G x := by
  let a := (stabilizerOne G).left x
  have ha : (stabilizer G).hom a = x := stabilizer_hom_stabilizerOne G x
  let p : (stabilizer G).hom.fiber x := ha ▸ (stabilizer G).hom.asFiber a
  have hp : (stabilizer G).hom.fiberι x p = a := by
    exact fiberι_cast_asFiber _ a ha
  have hs : G.source.left (G.identity.left x) = x := by
    have he := congrArg Over.Hom.left G.source_identity
    change G.identity.left ≫ G.source.left = 𝟙 _ at he
    exact congrArg (fun f => f x) he
  let q : G.source.left.fiber x := hs ▸ G.source.left.asFiber (G.identity.left x)
  have hq : G.source.left.fiberι x q = G.identity.left x := by
    exact fiberι_cast_asFiber _ (G.identity.left x) hs
  change stabilizerFiberToSourceFiber G x p = q
  apply (G.source.left.fiberι x).isEmbedding.injective
  change (stabilizerFiberToSourceFiber G x ≫ G.source.left.fiberι x) p =
    G.source.left.fiberι x q
  rw [stabilizerFiberToSourceFiber_comp]
  rw [Scheme.Hom.comp_apply, hp, hq]
  change ((stabilizerOne G).left ≫ stabilizerArrow G) x = G.identity.left x
  rw [stabilizerOne_arrow_eq_identity]

private theorem stabilizerFiber_dim_le_sourceFiberIdentity_localDim
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [LocallyOfFinitePresentation G.source.left] (x : G.objects.left) :
    topologicalKrullDim ((stabilizer G).hom.fiber x) ≤
      topologicalKrullDimAt (G.source.left.fiber x) (sourceFiberIdentity G x) := by
  exact stabilizerFiber_dim_le_sourceFiber_localDim G x
    (stabilizerFiberIdentityPoint G x) (sourceFiberIdentity G x)
    (stabilizerFiberToSourceFiber_maps_identity G x)

private theorem stabilizerFiber_dim_lt_sourceFiberIdentity_localDim_of_ne
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [LocallyOfFinitePresentation G.source.left] (x : G.objects.left)
    (hne : topologicalKrullDim ((stabilizer G).hom.fiber x) ≠
      topologicalKrullDimAt (G.source.left.fiber x) (sourceFiberIdentity G x)) :
    topologicalKrullDim ((stabilizer G).hom.fiber x) <
      topologicalKrullDimAt (G.source.left.fiber x) (sourceFiberIdentity G x) := by
  exact (stabilizerFiber_dim_le_sourceFiberIdentity_localDim G x).lt_of_ne hne

private theorem restrictionArrowsToArrows_isImmersion
    {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) [IsImmersion g.left] :
    IsImmersion (restrictionArrowsToArrows G g).left := by
  change IsImmersion
    ((pullback.fst (pullback.snd g G.target) (pullback.fst G.source g)).left ≫
      (pullback.snd g G.target).left)
  have hg : IsImmersion ((Over.forget S).map g) := by
    change IsImmersion g.left
    infer_instance
  have htarget : IsImmersion (pullback.snd g G.target).left := by
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      ((IsPullback.of_hasPullback g G.target).map (Over.forget S)) hg
  have hsource : IsImmersion (pullback.fst G.source g).left := by
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      ((IsPullback.of_hasPullback G.source g).flip.map (Over.forget S)) hg
  let : IsImmersion (pullback.snd g G.target).left := htarget
  let : IsImmersion (pullback.fst G.source g).left := hsource
  let : IsImmersion
      (pullback.fst (pullback.snd g G.target) (pullback.fst G.source g)).left := by
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      ((IsPullback.of_hasPullback (pullback.snd g G.target)
        (pullback.fst G.source g)).flip.map (Over.forget S)) hsource
  exact IsImmersion.comp _ _

private theorem restrictedSourceFiberMap_isEmbedding
    (D : SliceSituation) [IsImmersion D.g.left] :
    Topology.IsEmbedding (D.sliceIdentityPoints.sourceFiberMap) := by
  have hsource : Topology.IsEmbedding (D.groupoid.source.left.fiberι D.u) := by
    exact (show IsPreimmersion (D.groupoid.source.left.fiberι D.u) from inferInstance).isEmbedding
  have hcomp : Topology.IsEmbedding
      (D.sliceIdentityPoints.sourceFiberMap ≫ D.groupoid.source.left.fiberι D.u) := by
    rw [D.sliceIdentityPoints.sourceFiberMap_arrow]
    let : IsImmersion (restrictionArrowsToArrows D.groupoid D.g).left :=
      restrictionArrowsToArrows_isImmersion D.groupoid D.g
    change Topology.IsEmbedding
      ((restrictionArrowsToArrows D.groupoid D.g).left ∘
        (D.restrictedSource.fiberι D.u'))
    exact (show Topology.IsEmbedding
        ((restrictionArrowsToArrows D.groupoid D.g).left) from
          (restrictionArrowsToArrows_isImmersion D.groupoid D.g).isEmbedding).comp
        (show IsPreimmersion (D.restrictedSource.fiberι D.u') from inferInstance).isEmbedding
  exact hsource.of_comp_iff.mp hcomp

private theorem restrictedSourceFiber_dim_le_sourceFiber_localDim
    (D : SliceSituation) [IsImmersion D.g.left]
    (p : D.restrictedSourceFiber) :
    topologicalKrullDimAt D.restrictedSourceFiber p ≤
      topologicalKrullDimAt D.sourceFiber (D.sliceIdentityPoints.sourceFiberMap p) := by
  exact topologicalKrullDimAt_le_of_isEmbedding
    (restrictedSourceFiberMap_isEmbedding D) p

private theorem restrictionMapArrows_isImmersion
    (D : SliceSituation) [IsImmersion D.g.left] :
    IsImmersion D.restriction.hom.mapArrows.left := by
  rw [D.restriction.mapArrows_eq]
  have heq : IsIso ((eqToHom D.restriction.arrows_eq).left) := by
    have h : IsIso ((Over.forget D.S).map (eqToHom D.restriction.arrows_eq)) := inferInstance
    change IsIso ((Over.forget D.S).map (eqToHom D.restriction.arrows_eq))
    exact h
  let : IsIso ((eqToHom D.restriction.arrows_eq).left) := heq
  let : IsOpenImmersion (eqToHom D.restriction.arrows_eq).left := by
    infer_instance
  let : IsImmersion (eqToHom D.restriction.arrows_eq).left := inferInstance
  let : IsImmersion
      (restrictionArrowsToArrows D.groupoid D.g).left :=
    restrictionArrowsToArrows_isImmersion D.groupoid D.g
  change IsImmersion
    ((eqToHom D.restriction.arrows_eq).left ≫
      (restrictionArrowsToArrows D.groupoid D.g).left)
  exact IsImmersion.comp _ _

private theorem restrictedStabilizerFiberMap_isEmbedding
    (D : SliceSituation) [IsImmersion D.g.left] :
    Topology.IsEmbedding (D.sliceIdentityPoints.stabilizerFiberMap) := by
  let : IsImmersion (stabilizerArrow D.restrictedGroupoid) :=
    AlgebraicGeometry.stabilizerArrow_isImmersion D.restrictedGroupoid
  let : IsImmersion D.restriction.hom.mapArrows.left :=
    restrictionMapArrows_isImmersion D
  have hsource : Topology.IsEmbedding
      ((stabilizer D.groupoid).hom.fiberι D.u ≫ stabilizerArrow D.groupoid) := by
    exact (show Topology.IsEmbedding (stabilizerArrow D.groupoid) from
      (AlgebraicGeometry.stabilizerArrow_isImmersion D.groupoid).isEmbedding).comp
        (show IsPreimmersion ((stabilizer D.groupoid).hom.fiberι D.u) from
          inferInstance).isEmbedding
  have hcomp : Topology.IsEmbedding
      (D.sliceIdentityPoints.stabilizerFiberMap ≫
        (stabilizer D.groupoid).hom.fiberι D.u ≫ stabilizerArrow D.groupoid) := by
    rw [D.sliceIdentityPoints.stabilizerFiberMap_arrow]
    change Topology.IsEmbedding
      (D.restriction.hom.mapArrows.left ∘
        (stabilizerArrow D.restrictedGroupoid ∘
          (stabilizer D.restrictedGroupoid).hom.fiberι D.restrictedObjectPoint))
    exact (show Topology.IsEmbedding D.restriction.hom.mapArrows.left from
      (restrictionMapArrows_isImmersion D).isEmbedding).comp
        ((show Topology.IsEmbedding (stabilizerArrow D.restrictedGroupoid) from
          (AlgebraicGeometry.stabilizerArrow_isImmersion D.restrictedGroupoid).isEmbedding).comp
          (show IsPreimmersion
            ((stabilizer D.restrictedGroupoid).hom.fiberι D.restrictedObjectPoint) from
              inferInstance).isEmbedding)
  exact hsource.of_comp_iff.mp hcomp

private theorem restrictedStabilizerFiber_dim_le_stabilizerFiber
    (D : SliceSituation) [IsImmersion D.g.left] :
    topologicalKrullDim D.restrictedStabilizerFiber ≤
      topologicalKrullDim D.stabilizerFiber := by
  exact (restrictedStabilizerFiberMap_isEmbedding D).isInducing.topologicalKrullDim_le

private theorem exists_affine_open_nbhd_le {X : Scheme.{u}} (W : X.Opens) (x : X)
    (hx : x ∈ W) :
    ∃ V : X.Opens, IsAffine V.toScheme ∧ x ∈ V ∧ V ≤ W := by
  obtain ⟨V, hV, hxV, hVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
  rcases hV with ⟨V, hV, rfl⟩
  exact ⟨V, hV, hxV, hVW⟩

/- `natCast_ne_top_withBot` was re-proved here. It is public in
`StacksFrontier/Data/ENat/WithBotNatCast.lean:23`, the module that exists for exactly this --
its docstring records that several modules had each proved the `WithBot ℕ∞` form for
themselves. The uses below name that one. -/


private theorem sourceFiberIdentity_has_finite_dimension_bound
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [LocallyOfFinitePresentation G.source.left] (x : G.objects.left) :
    ∃ n : ℕ, topologicalKrullDimAt (G.source.left.fiber x)
      (sourceFiberIdentity G x) ≤ (n : WithBot ℕ∞) := by
  let k := G.objects.left.residueField x
  let f := G.source.left.fiberToSpecResidueField x
  let : LocallyOfFiniteType f := by
    change LocallyOfFiniteType
      (pullback.snd G.source.left (G.objects.left.fromSpecResidueField x))
    infer_instance
  exact exists_topologicalKrullDimAt_le (G.source.left.fiber x) k f
    (sourceFiberIdentity G x)

private theorem dimension_lt_nat_of_add_one_eq {a b : WithBot ℕ∞} {n : ℕ}
    (hab : a + 1 = b) (hb : b ≤ (n : WithBot ℕ∞)) : a < n := by
  apply (ENat.WithBot.add_one_le_natCast_iff).mp
  rw [hab]
  exact hb

/-- A Cohen--Macaulay morphism is flat: flatness of the stalk map at a point is the first
conjunct of Cohen--Macaulayness there, and flatness of a morphism is flatness of every stalk
map. -/
@[stacks 045R "flatness of a Cohen-Macaulay morphism"]
theorem flat_of_isCohenMacaulay {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (hcm : Scheme.Hom.IsCohenMacaulay f hf) : Flat f := by
  rw [Flat.iff_flat_stalkMap]
  intro x
  exact hcm x |>.1

private theorem source_flat_of_isCohenMacaulay {S : Scheme.{u}}
    (G : GroupoidScheme S)
    (hs : ∃ hf : ∀ y : G.objects.left,
      IsLocallyNoetherian (G.source.left.fiber y),
      Scheme.Hom.IsCohenMacaulay G.source.left hf) : Flat G.source.left := by
  rcases hs with ⟨hf, hcm⟩
  exact flat_of_isCohenMacaulay G.source.left hf hcm

private theorem target_flat_of_isCohenMacaulay {S : Scheme.{u}}
    (G : GroupoidScheme S)
    (ht : ∃ hf : ∀ y : G.objects.left,
      IsLocallyNoetherian (G.target.left.fiber y),
      Scheme.Hom.IsCohenMacaulay G.target.left hf) : Flat G.target.left := by
  rcases ht with ⟨hf, hcm⟩
  exact flat_of_isCohenMacaulay G.target.left hf hcm

private theorem openImmersion_cohenMacaulayAt {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsOpenImmersion i] (x : X) :
    let hf : ∀ y : Y, IsLocallyNoetherian (i.fiber y) := fun y => by
      let : LocallyOfFiniteType (i.fiberToSpecResidueField y) := by
        change LocallyOfFiniteType (pullback.snd i (Y.fromSpecResidueField y))
        infer_instance
      exact LocallyOfFiniteType.isLocallyNoetherian (i.fiberToSpecResidueField y)
    Scheme.Hom.IsCohenMacaulayAt i hf x := by
  let hf : ∀ y : Y, IsLocallyNoetherian (i.fiber y) := fun y => by
    let : LocallyOfFiniteType (i.fiberToSpecResidueField y) := by
      change LocallyOfFiniteType (pullback.snd i (Y.fromSpecResidueField y))
      infer_instance
    exact LocallyOfFiniteType.isLocallyNoetherian (i.fiberToSpecResidueField y)
  change AlgebraicGeometry.IsFlatAt i.toLRSHom.toShHom x ∧
    IsCohenMacaulayLocalRing ((i.fiber (i x)).presheaf.stalk (i.asFiber x))
  constructor
  · exact (Flat.iff_flat_stalkMap i).mp inferInstance x
  · let g := i.fiberToSpecResidueField (i x)
    have hsurj : Function.Surjective g := by
      intro z
      refine ⟨i.asFiber x, ?_⟩
      dsimp [g]
      exact Subsingleton.elim _ _
    have : IsOpenImmersion g := by
      change IsOpenImmersion (pullback.snd i (Y.fromSpecResidueField (i x)))
      infer_instance
    have : Flat g := inferInstance
    have : Surjective g := (surjective_iff g).2 hsurj
    have : Epi g.base := (TopCat.epi_iff_surjective _).mpr hsurj
    have : IsIso g := IsOpenImmersion.isIso g
    have hgz : g (i.asFiber x) = IsLocalRing.closedPoint (Y.residueField (i x)) := by
      dsimp [g]
      exact Scheme.Hom.fiberToSpecResidueField_apply i (i x) (i.asFiber x)
    have eCongr :
        (Spec (Y.residueField (i x))).presheaf.stalk (g (i.asFiber x)) ≅
          (Spec (Y.residueField (i x))).presheaf.stalk
            (IsLocalRing.closedPoint (Y.residueField (i x))) := by
      rw [hgz]
    let e : (i.fiber (i x)).presheaf.stalk (i.asFiber x) ≃+* _ :=
      ((asIso (g.stalkMap (i.asFiber x))).commRingCatIsoToRingEquiv).symm.trans
        eCongr.commRingCatIsoToRingEquiv |>.trans
        (AlgebraicGeometry.stalkClosedPointIso (Y.residueField (i x))).commRingCatIsoToRingEquiv
    let A := (i.fiber (i x)).presheaf.stalk (i.asFiber x)
    let : IsLocallyNoetherian (i.fiber (i x)) := hf (i x)
    have hdim : ringKrullDim A = 0 := by
      rw [ringKrullDim_eq_of_ringEquiv e]
      exact ringKrullDim_eq_zero_of_field _
    have hmax : Module.IsMaximalCohenMacaulay A A :=
      Module.isMaximalCohenMacaulay_self_of_ringKrullDim_eq_zero hdim
    have hI : IsLocalRing.maximalIdeal A • (⊤ : Submodule A A) ≠ ⊤ := by
      simpa [smul_eq_mul, Ideal.mul_top] using
        (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    have hdepthSup :
        (Module.depthSup A (IsLocalRing.maximalIdeal A) A : WithBot ℕ∞) = ringKrullDim A := by
      change (Module.depth A (IsLocalRing.maximalIdeal A) A : WithBot ℕ∞) = ringKrullDim A
        at hmax
      rw [Module.depth, ite_eq_right hI, ← Module.depthSup_eq_iSup] at hmax
      exact hmax
    change IsCohenMacaulayModule A A
    change Module.depthSup A (IsLocalRing.maximalIdeal A) A =
      (Module.supportDim A A : WithBot ℕ∞)
    rw [Module.supportDim_self_eq_ringKrullDim]
    exact hdepthSup

private abbrev cohenMacaulayLocallyOfFinitePresentation : MorphismProperty Scheme.{u} :=
  (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) ⊓
    cohenMacaulayWithLocallyNoetherianFibers

private theorem cohenMacaulayLocallyOfFinitePresentation_baseChange :
    cohenMacaulayLocallyOfFinitePresentation.{u}.IsStableUnderBaseChange := by
  let : (cohenMacaulayWithLocallyNoetherianFibers :
      MorphismProperty Scheme.{u}).RespectsIso :=
    AlgebraicGeometry.cohenMacaulayWithLocallyNoetherianFibers_isLocalAtTarget_fppf.toRespects
  let : MorphismProperty.RespectsIso
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    @MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ _
      locallyOfFinitePresentation_isStableUnderBaseChange
  have : cohenMacaulayLocallyOfFinitePresentation.{u}.RespectsIso :=
    MorphismProperty.RespectsIso.inf (@LocallyOfFinitePresentation)
      cohenMacaulayWithLocallyNoetherianFibers
  apply MorphismProperty.IsStableUnderBaseChange.of_forall_exists_isPullback
  intro X Y Z f g _ hg
  let : LocallyOfFinitePresentation g := hg.1
  let : Flat g := flat_of_isCohenMacaulay g hg.2.choose hg.2.choose_spec
  refine ⟨pullback g f, pullback.snd g f, pullback.fst g f,
    (IsPullback.of_hasPullback g f).flip, inferInstance, ?_⟩
  refine ⟨isLocallyNoetherian_fiber_of_locallyOfFiniteType (pullback.snd g f), ?_⟩
  intro x
  exact (Set.ext_iff.mp
    (AlgebraicGeometry.isCohenMacaulayAt_pullback_locus g f) x).mpr
      (hg.2.choose_spec ((pullback.fst g f) x))

private theorem cohenMacaulayLocallyOfFinitePresentation_comp
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : cohenMacaulayLocallyOfFinitePresentation f)
    (hg : cohenMacaulayLocallyOfFinitePresentation g) :
    cohenMacaulayLocallyOfFinitePresentation (f ≫ g) := by
  let : LocallyOfFinitePresentation f := hf.1
  let : LocallyOfFinitePresentation g := hg.1
  refine ⟨inferInstance, isLocallyNoetherian_fiber_of_locallyOfFiniteType (f ≫ g), ?_⟩
  exact AlgebraicGeometry.isCohenMacaulay_comp f g hf.2.choose hg.2.choose _
    hf.2.choose_spec hg.2.choose_spec

private theorem restrictedGroupoid_cohenMacaulayLocallyOfFinitePresentation
    (D : SliceSituation.{u})
    (h : cohenMacaulayLocallyOfFinitePresentation D.sourceMap.left) :
    cohenMacaulayLocallyOfFinitePresentation D.restrictedGroupoid.source.left ∧
      cohenMacaulayLocallyOfFinitePresentation D.restrictedGroupoid.target.left := by
  let := cohenMacaulayLocallyOfFinitePresentation_baseChange.{u}
  exact ⟨AlgebraicGeometry.restriction_source_mem D.groupoid D.g D.restriction _ h,
    AlgebraicGeometry.restriction_target_mem D.groupoid D.g D.restriction _ h⟩

private lemma isOpen_flatLocus {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] :
    IsOpen {x : X | AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom x} := by
  let := Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_unit X
  have hset : {x : X | AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom x} =
      {x : X | AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom
        (SheafOfModules.unit X.ringCatSheaf) x} := by
    ext x
    exact AlgebraicGeometry.MorphismOfGerms.flat_stalkMap_iff_isFlatOverAt_unit f x
  rw [hset]
  exact AlgebraicGeometry.isOpen_setOf_flatOverAt f (SheafOfModules.unit X.ringCatSheaf)

private lemma flat_open_restriction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : X.Opens) (hV : ∀ x ∈ V, AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom x) :
    Flat (V.ι ≫ f) := by
  rw [Flat.iff_flat_stalkMap]
  intro x
  rw [Scheme.Hom.stalkMap_comp]
  change ((V.ι.stalkMap x).hom.comp (f.stalkMap (V.ι x)).hom).Flat
  exact (hV (V.ι x) x.2).comp
    ((Flat.iff_flat_stalkMap V.ι).mp inferInstance x)

private lemma isOpen_cohenMacaulayLocus {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f]
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) :
    IsOpen {x : X | Scheme.Hom.IsCohenMacaulayAt f hf x} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  let V : X.Opens := ⟨{x | AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom x},
    isOpen_flatLocus f⟩
  let : Flat (V.ι ≫ f) := flat_open_restriction f V (fun _ h => h)
  let hfV := isLocallyNoetherian_fiber_of_locallyOfFiniteType (V.ι ≫ f)
  let hι := isLocallyNoetherian_fiber_of_locallyOfFiniteType V.ι
  let W : V.toScheme.Opens :=
    ⟨{z | Scheme.Hom.IsCohenMacaulayAt (V.ι ≫ f) hfV z},
      AlgebraicGeometry.isOpen_setOf_isCohenMacaulayAt (V.ι ≫ f)⟩
  refine ⟨V.ι '' (W : Set V.toScheme), ?_,
    V.ι.isOpenEmbedding.isOpenMap _ W.2, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact AlgebraicGeometry.isCohenMacaulayAt_right_of_comp_of_flatAt V.ι f hf hfV z hz
      ((Flat.iff_flat_stalkMap V.ι).mp inferInstance z)
  · let z : V.toScheme := ⟨x, hx.1⟩
    refine ⟨z, ?_, rfl⟩
    exact AlgebraicGeometry.isCohenMacaulayAt_comp V.ι f hι hf hfV z
      (openImmersion_cohenMacaulayAt V.ι z) hx

private theorem exists_open_cm_near_point
    (D : FlatLocallyFinitelyPresentedGroupoidSituation)
    (x : D.fiberProduct)
    (hf : ∀ y : D.groupoid.objects.left, IsLocallyNoetherian (D.h.fiber y))
    (hcm : Scheme.Hom.IsCohenMacaulayAt D.h hf x) :
    ∃ W : D.U'.Opens,
      (pullback.fst D.g D.groupoid.target.left) x ∈ W ∧
      ∃ hfW : ∀ y : D.groupoid.objects.left,
        IsLocallyNoetherian ((((pullback.fst D.g D.groupoid.target.left) ⁻¹ᵁ W).ι ≫ D.h).fiber y),
        Scheme.Hom.IsCohenMacaulay
          (((pullback.fst D.g D.groupoid.target.left) ⁻¹ᵁ W).ι ≫ D.h) hfW := by
  let f := D.h
  let : LocallyOfFinitePresentation f := by
    change LocallyOfFinitePresentation
      (pullback.snd D.g D.groupoid.target.left ≫ D.groupoid.source.left)
    infer_instance
  let hf0 : ∀ y : D.groupoid.objects.left, IsLocallyNoetherian (f.fiber y) := hf
  let p := pullback.fst D.g D.groupoid.target.left
  let V : D.fiberProduct.Opens :=
    ⟨{z | Scheme.Hom.IsCohenMacaulayAt f hf0 z},
      isOpen_cohenMacaulayLocus f hf0⟩
  let hfV : ∀ y : D.groupoid.objects.left,
      IsLocallyNoetherian ((V.ι ≫ f).fiber y) :=
    fun y => isLocallyNoetherian_fiber_of_locallyOfFiniteType (V.ι ≫ f) y
  let hfι : ∀ y : D.fiberProduct, IsLocallyNoetherian (V.ι.fiber y) :=
    fun y => isLocallyNoetherian_fiber_of_locallyOfFiniteType V.ι y
  have hV : Scheme.Hom.IsCohenMacaulay (V.ι ≫ f)
      hfV := by
    intro z
    have hz : Scheme.Hom.IsCohenMacaulayAt f hf0 (V.ι z) := z.2
    have hVι : Scheme.Hom.IsCohenMacaulayAt V.ι hfι z := openImmersion_cohenMacaulayAt V.ι z
    exact AlgebraicGeometry.isCohenMacaulayAt_comp V.ι f
      hfι hf0 hfV
      z hVι hz
  obtain ⟨W, hW⟩ :=
    AlgebraicGeometry.exists_open_with_preimage_maximal_cohenMacaulayLocus D
  have hVW : V ≤ p ⁻¹ᵁ W := (mem_upperBounds.mp hW.2) V ⟨hfV, hV⟩
  have hxV : x ∈ V := hcm
  have hxW : p x ∈ W := hVW hxV
  exact ⟨W, hxW, hW.1⟩

private theorem sourceMap_locallyOfFinitePresentation (D : SliceSituation.{u})
    [LocallyOfFinitePresentation D.g.left]
    [LocallyOfFinitePresentation D.groupoid.source.left] :
    LocallyOfFinitePresentation D.sourceMap.left := by
  let : LocallyOfFinitePresentation (pullback.snd D.g D.groupoid.target).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      ((IsPullback.of_hasPullback D.g D.groupoid.target).map (Over.forget D.S))
      (inferInstance : LocallyOfFinitePresentation D.g.left)
  change LocallyOfFinitePresentation
    ((pullback.snd D.g D.groupoid.target).left ≫ D.groupoid.source.left)
  infer_instance

private theorem openImmersion_cohenMacaulayLocallyOfFinitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    cohenMacaulayLocallyOfFinitePresentation f := by
  exact ⟨inferInstance, isLocallyNoetherian_fiber_of_locallyOfFiniteType f,
    openImmersion_cohenMacaulayAt f⟩

private noncomputable abbrev cohenMacaulayFlatSituation
    {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects)
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left]
    [LocallyOfFinitePresentation g.left]
    (hs : ∃ hf : ∀ y : G.objects.left,
      IsLocallyNoetherian (G.source.left.fiber y),
      Scheme.Hom.IsCohenMacaulay G.source.left hf)
    (ht : ∃ hf : ∀ y : G.objects.left,
      IsLocallyNoetherian (G.target.left.fiber y),
      Scheme.Hom.IsCohenMacaulay G.target.left hf) :
    FlatLocallyFinitelyPresentedGroupoidSituation := by
  let : Flat G.source.left := source_flat_of_isCohenMacaulay G hs
  let : Flat G.target.left := target_flat_of_isCohenMacaulay G ht
  exact ⟨S, G, U'.left, g.left⟩

private theorem exists_open_cohenMacaulay_slice
    (D : SliceSituation.{u})
    [LocallyOfFinitePresentation D.g.left]
    [LocallyOfFinitePresentation D.groupoid.source.left]
    [LocallyOfFinitePresentation D.groupoid.target.left]
    (hs : ∃ hf : ∀ y : D.groupoid.objects.left,
      IsLocallyNoetherian (D.groupoid.source.left.fiber y),
      Scheme.Hom.IsCohenMacaulay D.groupoid.source.left hf)
    (ht : ∃ hf : ∀ y : D.groupoid.objects.left,
      IsLocallyNoetherian (D.groupoid.target.left.fiber y),
      Scheme.Hom.IsCohenMacaulay D.groupoid.target.left hf)
    (x : D.arrowSource.left)
    (hx : (pullback.fst D.g D.groupoid.target).left x = D.u')
    (hf : ∀ y : D.groupoid.objects.left,
      IsLocallyNoetherian (D.sourceMap.left.fiber y))
    (hcm : Scheme.Hom.IsCohenMacaulayAt D.sourceMap.left hf x) :
    ∃ W : D.U'.left.Opens, D.u' ∈ W ∧
      cohenMacaulayLocallyOfFinitePresentation
        ((((pullback.fst D.g D.groupoid.target).left) ⁻¹ᵁ W).ι ≫ D.sourceMap.left) := by
  let A := cohenMacaulayFlatSituation D.groupoid D.g hs ht
  let e : D.arrowSource.left ≅ A.fiberProduct :=
    PreservesPullback.iso (Over.forget D.S) D.g D.groupoid.target
  let : LocallyOfFinitePresentation A.h := by
    change LocallyOfFinitePresentation
      (pullback.snd D.g.left D.groupoid.target.left ≫ D.groupoid.source.left)
    infer_instance
  have he : e.hom ≫ A.h = D.sourceMap.left := by
    change e.hom ≫ pullback.snd D.g.left D.groupoid.target.left ≫
      D.groupoid.source.left = _
    have H := congrArg (fun k => k ≫ D.groupoid.source.left)
      (PreservesPullback.iso_hom_snd (Over.forget D.S) D.g D.groupoid.target)
    exact (Category.assoc _ _ _).symm.trans H
  have hep : e.hom ≫ pullback.fst D.g.left D.groupoid.target.left =
      (pullback.fst D.g D.groupoid.target).left :=
    PreservesPullback.iso_hom_fst (Over.forget D.S) D.g D.groupoid.target
  let hfA := isLocallyNoetherian_fiber_of_locallyOfFiniteType A.h
  have hc : Scheme.Hom.IsCohenMacaulayAt (e.hom ≫ A.h)
      (isLocallyNoetherian_fiber_of_locallyOfFiniteType (e.hom ≫ A.h)) x := by
    simpa only [he] using hcm
  have hcA : Scheme.Hom.IsCohenMacaulayAt A.h hfA (e.hom x) :=
    AlgebraicGeometry.isCohenMacaulayAt_right_of_comp_of_flatAt e.hom A.h hfA _ x hc
      ((Flat.iff_flat_stalkMap e.hom).mp inferInstance x)
  obtain ⟨W, hxW, hW⟩ := exists_open_cm_near_point A (e.hom x) hfA hcA
  have hxW' : D.u' ∈ W := by
    change (e.hom ≫ pullback.fst D.g.left D.groupoid.target.left) x ∈ W at hxW
    rw [hep] at hxW
    exact hx ▸ hxW
  let V : D.arrowSource.left.Opens :=
    ((pullback.fst D.g D.groupoid.target).left) ⁻¹ᵁ W
  let V₀ : A.fiberProduct.Opens := (pullback.fst A.g A.groupoid.target.left) ⁻¹ᵁ W
  have hV : V ≤ e.hom ⁻¹ᵁ V₀ := by
    intro z hz
    change (e.hom ≫ pullback.fst D.g.left D.groupoid.target.left) z ∈ W
    rwa [hep]
  let j := e.hom.resLE V₀ V hV
  let : IsOpenImmersion j := by
    let : IsOpenImmersion (j ≫ V₀.ι) := by
      dsimp only [j]
      rw [Scheme.Hom.resLE_comp_ι]
      infer_instance
    exact IsOpenImmersion.of_comp j V₀.ι
  have hj : j ≫ (V₀.ι ≫ A.h) = V.ι ≫ D.sourceMap.left := by
    dsimp only [j]
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, he]
  have hP : cohenMacaulayLocallyOfFinitePresentation (j ≫ (V₀.ι ≫ A.h)) :=
    cohenMacaulayLocallyOfFinitePresentation_comp
      (openImmersion_cohenMacaulayLocallyOfFinitePresentation j) ⟨inferInstance, hW⟩
  exact ⟨W, hxW', hj ▸ hP⟩

private theorem pullback_comp_left_square {C : Type*} [Category C] [HasPullbacks C]
    {U V R X : C} (g : U ⟶ X) (t : R ⟶ X) (j : V ⟶ U) :
    let q := pullback.lift (pullback.fst (j ≫ g) t ≫ j)
      (pullback.snd (j ≫ g) t) (by simp [Category.assoc, pullback.condition])
    IsPullback q (pullback.fst (j ≫ g) t) (pullback.fst g t) j := by
  dsimp
  apply IsPullback.of_right (h₁₂ := pullback.snd g t) (h₂₂ := g)
    (s := by simpa only [pullback.lift_snd] using
      (IsPullback.of_hasPullback (j ≫ g) t).flip)
    (t := (IsPullback.of_hasPullback g t).flip)
  exact pullback.lift_fst _ _ _

private theorem cohenMacaulay_sourceMap_open_refinement (D : SliceSituation.{u})
    {U'' : Over D.S} (j : U'' ⟶ D.U') [IsOpenImmersion j.left]
    (W : D.U'.left.Opens) (hjW : Set.range j.left ⊆ W)
    (hW : cohenMacaulayLocallyOfFinitePresentation
      ((((pullback.fst D.g D.groupoid.target).left) ⁻¹ᵁ W).ι ≫ D.sourceMap.left)) :
    cohenMacaulayLocallyOfFinitePresentation
      ((pullback.snd (j ≫ D.g) D.groupoid.target ≫ D.groupoid.source).left) := by
  let q : pullback (j ≫ D.g) D.groupoid.target ⟶ pullback D.g D.groupoid.target :=
    pullback.lift (pullback.fst (j ≫ D.g) D.groupoid.target ≫ j)
      (pullback.snd (j ≫ D.g) D.groupoid.target)
      (by simp [Category.assoc, pullback.condition])
  have hq : IsPullback q (pullback.fst (j ≫ D.g) D.groupoid.target)
      (pullback.fst D.g D.groupoid.target) j :=
    pullback_comp_left_square D.g D.groupoid.target j
  let : IsOpenImmersion q.left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (hq.flip.map (Over.forget D.S)) (inferInstance : IsOpenImmersion j.left)
  let V : (pullback D.g D.groupoid.target).left.Opens :=
    ((pullback.fst D.g D.groupoid.target).left) ⁻¹ᵁ W
  have hqV : Set.range q.left ⊆ (V : Set (pullback D.g D.groupoid.target).left) := by
    rintro _ ⟨z, rfl⟩
    have hp := congrArg (fun k => k.left z) (pullback.lift_fst
      (pullback.fst (j ≫ D.g) D.groupoid.target ≫ j)
      (pullback.snd (j ≫ D.g) D.groupoid.target)
      (show (pullback.fst (j ≫ D.g) D.groupoid.target ≫ j) ≫ D.g =
        pullback.snd (j ≫ D.g) D.groupoid.target ≫ D.groupoid.target by
        simp [Category.assoc, pullback.condition]))
    change (pullback.fst D.g D.groupoid.target).left (q.left z) ∈ W
    exact hp.symm ▸ hjW ⟨_, rfl⟩
  have hqRange : Set.range q.left ⊆ Set.range V.ι := by
    simpa only [Scheme.Opens.range_ι] using hqV
  let r := IsOpenImmersion.lift V.ι q.left hqRange
  have hr : r ≫ V.ι = q.left := IsOpenImmersion.lift_fac _ _ _
  let : IsOpenImmersion (r ≫ V.ι) := by rw [hr]; infer_instance
  let : IsOpenImmersion r := IsOpenImmersion.of_comp r V.ι
  have hqr' : q ≫ (pullback.snd D.g D.groupoid.target ≫ D.groupoid.source) =
      pullback.snd (j ≫ D.g) D.groupoid.target ≫ D.groupoid.source :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ D.groupoid.source) (pullback.lift_snd _ _ _))
  have hqr : q.left ≫ D.sourceMap.left =
      (pullback.snd (j ≫ D.g) D.groupoid.target ≫ D.groupoid.source).left :=
    congrArg Over.Hom.left hqr'
  have hP := cohenMacaulayLocallyOfFinitePresentation_comp
    (openImmersion_cohenMacaulayLocallyOfFinitePresentation r) hW
  have hcomp : r ≫ V.ι ≫ D.sourceMap.left =
      (pullback.snd (j ≫ D.g) D.groupoid.target ≫ D.groupoid.source).left :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ D.sourceMap.left) hr).trans hqr)
  exact hcomp ▸ hP

private theorem isFiniteTypePoint_of_immersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsImmersion f] (x : X)
    (hx : AlgebraicGeometry.IsFiniteTypePoint (f x)) :
    AlgebraicGeometry.IsFiniteTypePoint x := by
  have hres : Function.Surjective (f.residueFieldMap x) := by
    have h := (X.residue_surjective x).comp (f.stalkMap_surjective x)
    change Function.Surjective (f.stalkMap x ≫ X.residue x) at h
    rw [← Scheme.residue_residueFieldMap] at h
    intro z
    obtain ⟨b, hb⟩ := h z
    exact ⟨Y.residue (f x) b, hb⟩
  let : IsIso (f.residueFieldMap x) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨(f.residueFieldMap x).hom.injective, hres⟩
  let : LocallyOfFiniteType (Y.fromSpecResidueField (f x)) := hx.1
  let : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    infer_instance
  let : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    locallyOfFiniteType_of_comp (X.fromSpecResidueField x) f
  exact ((AlgebraicGeometry.finiteType_specField_tfae (X.fromSpecResidueField x)).out 2 1).mp
    (inferInstance : LocallyOfFiniteType (X.fromSpecResidueField x))

section

private lemma fiber_localDim_le {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : a ≫ f' = f ≫ b) (ha : Topology.IsEmbedding a)
    (y : Y) (y' : Y') (hy : b y = y')
    (p : f.fiber y) (q : f'.fiber y')
    (hp : a (f.fiberι y p) = f'.fiberι y' q) :
    topologicalKrullDimAt (f.fiber y) p ≤ topologicalKrullDimAt (f'.fiber y') q := by
  let F : f.fiber y → f' ⁻¹' {y'} := fun z =>
    ⟨a (f.fiberι y z), by
      change (a ≫ f') (f.fiberι y z) = y'
      rw [h, Scheme.Hom.comp_apply]
      exact (congrArg b (f.fiberHomeo y z).2).trans hy⟩
  have hF : Topology.IsEmbedding F := by
    exact Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
      (ha.comp (f.fiberι y).isEmbedding)
  have hq : F p = f'.fiberHomeo y' q := Subtype.ext hp
  have hle := topologicalKrullDimAt_le_of_isEmbedding hF p
  rw [hq, ← topologicalKrullDimAt_eq_of_homeomorph (f'.fiberHomeo y') q] at hle
  exact hle

private lemma fiber_localDim_eq {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    [IsIso a] [IsIso b] (h : a ≫ f' = f ≫ b)
    (y : Y) (y' : Y') (hy : b y = y')
    (p : f.fiber y) (q : f'.fiber y')
    (hp : a (f.fiberι y p) = f'.fiberι y' q) :
    topologicalKrullDimAt (f.fiber y) p = topologicalKrullDimAt (f'.fiber y') q := by
  apply le_antisymm (fiber_localDim_le f f' a b h a.homeomorph.isEmbedding y y' hy p q hp)
  apply fiber_localDim_le f' f (inv a) (inv b) ?_
    (inv a).homeomorph.isEmbedding y' y ?_ q p ?_
  · apply (cancel_mono b).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← h, IsIso.inv_hom_id_assoc]
  · rw [← hy, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
    rfl
  · rw [← hp, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
    rfl

private lemma restriction_target_arrow {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) :
    restrictionTarget G g ≫ g = restrictionArrowsToArrows G g ≫ G.target :=
  (GroupoidScheme.restriction_condition' G g).symm

private noncomputable def restrictionLift {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' T : Over S} (g : U' ⟶ G.objects) (s t : T ⟶ U') (a : T ⟶ G.arrows)
    (hs : s ≫ g = a ≫ G.source) (ht : t ≫ g = a ≫ G.target) :
    T ⟶ restrictionArrows G g :=
  pullback.lift (pullback.lift t a ht) (pullback.lift a s hs.symm)
    ((pullback.lift_snd _ _ _).trans (pullback.lift_fst _ _ _).symm)

private lemma restrictionLift_source {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' T : Over S} (g : U' ⟶ G.objects) (s t : T ⟶ U') (a : T ⟶ G.arrows)
    (hs : s ≫ g = a ≫ G.source) (ht : t ≫ g = a ≫ G.target) :
    restrictionLift G g s t a hs ht ≫ restrictionSource G g = s :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ pullback.snd G.source g) (pullback.lift_snd _ _ _)).trans
      (pullback.lift_snd _ _ _))

private lemma restrictionLift_target {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' T : Over S} (g : U' ⟶ G.objects) (s t : T ⟶ U') (a : T ⟶ G.arrows)
    (hs : s ≫ g = a ≫ G.source) (ht : t ≫ g = a ≫ G.target) :
    restrictionLift G g s t a hs ht ≫ restrictionTarget G g = t :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ pullback.fst g G.target) (pullback.lift_fst _ _ _)).trans
      (pullback.lift_fst _ _ _))

private lemma restrictionLift_arrow {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' T : Over S} (g : U' ⟶ G.objects) (s t : T ⟶ U') (a : T ⟶ G.arrows)
    (hs : s ≫ g = a ≫ G.source) (ht : t ≫ g = a ≫ G.target) :
    restrictionLift G g s t a hs ht ≫ restrictionArrowsToArrows G g = a :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ pullback.snd g G.target) (pullback.lift_fst _ _ _)).trans
      (pullback.lift_snd _ _ _))

private lemma restrictedObjectPoint_map (D : SliceSituation.{u}) :
    (eqToHom D.restriction.objects_eq).left D.restrictedObjectPoint = D.u' := by
  change ((eqToHom D.restriction.objects_eq.symm ≫
    eqToHom D.restriction.objects_eq).left) D.u' = D.u'
  simp

private lemma restriction_fiber_dim_eq (D : SliceSituation.{u}) [IsImmersion D.g.left] :
    topologicalKrullDimAt (D.restrictedGroupoid.source.left.fiber D.restrictedObjectPoint)
        (sourceFiberIdentity D.restrictedGroupoid D.restrictedObjectPoint) =
      topologicalKrullDimAt D.restrictedSourceFiber
        D.sliceIdentityPoints.restrictedSourceIdentity := by
  let eA : D.restrictedGroupoid.arrows.left ≅ (restrictionArrows D.groupoid D.g).left :=
    (Over.forget D.S).mapIso (eqToIso D.restriction.arrows_eq)
  let eO : D.restrictedGroupoid.objects.left ≅ D.U'.left :=
    (Over.forget D.S).mapIso (eqToIso D.restriction.objects_eq)
  have hsource : eA.hom ≫ D.restrictedSource =
      D.restrictedGroupoid.source.left ≫ eO.hom := by
    have h := congrArg (fun f => (f ≫ eqToHom D.restriction.objects_eq).left)
      D.restriction.source_eq
    simpa [Category.assoc, eA, eO, SliceSituation.restrictedSource,
      SliceSituation.restrictedGroupoid] using h.symm
  apply fiber_localDim_eq _ _ eA.hom eO.hom hsource
    _ _ (restrictedObjectPoint_map D)
  apply (restrictionArrowsToArrows_isImmersion D.groupoid D.g).isEmbedding.injective
  rw [D.sliceIdentityPoints.restrictedSourceIdentity_fiberι,
    D.sliceIdentityPoints.restrictedIdentity_arrow]
  rw [show D.restrictedGroupoid.source.left.fiberι D.restrictedObjectPoint
      (sourceFiberIdentity D.restrictedGroupoid D.restrictedObjectPoint) =
      D.restrictedGroupoid.identity.left D.restrictedObjectPoint from
        fiberι_cast_asFiber _ _ _]
  change ((D.restriction.groupoid.identity ≫ eqToHom D.restriction.arrows_eq ≫
    restrictionArrowsToArrows D.groupoid D.g).left) D.restrictedObjectPoint = _
  rw [← D.restriction.mapArrows_eq]
  rw [← D.restriction.hom.map_identity, D.restriction.mapObjects_eq]
  change D.groupoid.identity.left
    (D.g.left ((eqToHom D.restriction.objects_eq).left D.restrictedObjectPoint)) = _
  rw [restrictedObjectPoint_map, D.mapsTo]

private lemma refinement_dim_le (D : SliceSituation.{u}) [IsImmersion D.g.left]
    {V : Over D.S} (j : V ⟶ D.U') [IsImmersion j.left] (v : V.left)
    (hv : j.left v = D.u') :
    let E : SliceSituation := ⟨D.S, D.groupoid, V, j ≫ D.g, D.u, v,
      (congrArg D.g.left hv).trans D.mapsTo⟩
    topologicalKrullDimAt E.restrictedSourceFiber
        E.sliceIdentityPoints.restrictedSourceIdentity ≤
      topologicalKrullDimAt D.restrictedSourceFiber
        D.sliceIdentityPoints.restrictedSourceIdentity := by
  dsimp only
  let E : SliceSituation := ⟨D.S, D.groupoid, V, j ≫ D.g, D.u, v,
    (congrArg D.g.left hv).trans D.mapsTo⟩
  let a := restrictionArrowsToArrows D.groupoid (j ≫ D.g)
  let s := restrictionSource D.groupoid (j ≫ D.g)
  let t := restrictionTarget D.groupoid (j ≫ D.g)
  have hs : (s ≫ j) ≫ D.g = a ≫ D.groupoid.source := by
    rw [Category.assoc]
    exact AlgebraicGeometry.GroupoidScheme.restriction_condition _ _
  have ht : (t ≫ j) ≫ D.g = a ≫ D.groupoid.target := by
    rw [Category.assoc]
    exact restriction_target_arrow _ _
  let l := restrictionLift D.groupoid D.g (s ≫ j) (t ≫ j) a hs ht
  have hl : l ≫ restrictionArrowsToArrows D.groupoid D.g = a :=
    restrictionLift_arrow _ _ _ _ _ _ _
  have hls : l ≫ restrictionSource D.groupoid D.g = s ≫ j :=
    restrictionLift_source _ _ _ _ _ _ _
  have : IsImmersion (j ≫ D.g).left := IsImmersion.comp j.left D.g.left
  have hem : Topology.IsEmbedding l.left := by
    have hl' := congrArg Over.Hom.left hl
    apply (restrictionArrowsToArrows_isImmersion D.groupoid D.g).isEmbedding.of_comp_iff.mp
    change Topology.IsEmbedding (l ≫ restrictionArrowsToArrows D.groupoid D.g).left
    rw [hl]
    exact (restrictionArrowsToArrows_isImmersion D.groupoid (j ≫ D.g)).isEmbedding
  apply fiber_localDim_le E.restrictedSource D.restrictedSource l.left j.left
    (congrArg Over.Hom.left hls) hem v D.u' hv
  apply (restrictionArrowsToArrows_isImmersion D.groupoid D.g).isEmbedding.injective
  rw [D.sliceIdentityPoints.restrictedSourceIdentity_fiberι,
    D.sliceIdentityPoints.restrictedIdentity_arrow,
    E.sliceIdentityPoints.restrictedSourceIdentity_fiberι]
  change ((l ≫ restrictionArrowsToArrows D.groupoid D.g).left)
    E.sliceIdentityPoints.restrictedIdentity = _
  rw [hl]
  exact E.sliceIdentityPoints.restrictedIdentity_arrow

private lemma exists_restriction_lift {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' T : Over S} (g : U' ⟶ G.objects) (R : GroupoidScheme.Restriction G g)
    (s t : T ⟶ R.groupoid.objects) (a : T ⟶ G.arrows)
    (hs : a ≫ G.source = s ≫ R.hom.mapObjects)
    (ht : a ≫ G.target = t ≫ R.hom.mapObjects) :
    ∃ l : T ⟶ R.groupoid.arrows,
      l ≫ R.groupoid.source = s ∧ l ≫ R.groupoid.target = t ∧
        l ≫ R.hom.mapArrows = a := by
  let e := Classical.choice (R.evaluation_fullyFaithful T)
  let f : (R.hom.evaluation T).obj s ⟶ (R.hom.evaluation T).obj t := ⟨a, hs, ht⟩
  let l := e.preimage f
  exact ⟨l.arrow, l.source_eq, l.target_eq,
    congrArg GroupoidScheme.EvaluationHom.arrow (e.map_preimage f)⟩

private lemma restriction_mapObjects_point (D : SliceSituation.{u}) :
    D.restriction.hom.mapObjects.left D.restrictedObjectPoint = D.u := by
  rw [D.restriction.mapObjects_eq]
  change D.g.left ((eqToHom D.restriction.objects_eq).left D.restrictedObjectPoint) = D.u
  rw [restrictedObjectPoint_map, D.mapsTo]

/-- The map on objects of the restriction to an immersion `g` is again an immersion. -/
private lemma restriction_mapObjects_isImmersion (D : SliceSituation.{u}) [IsImmersion D.g.left] :
    IsImmersion D.restriction.hom.mapObjects.left := by
  let eO : D.restrictedGroupoid.objects.left ≅ D.U'.left :=
    (Over.forget D.S).mapIso (eqToIso D.restriction.objects_eq)
  rw [D.restriction.mapObjects_eq]
  exact IsImmersion.comp eO.hom D.g.left

private lemma composite_restriction_dim_le (D : SliceSituation.{u})
    [IsImmersion D.g.left] {V : Over D.S}
    (j : V ⟶ D.restrictedGroupoid.objects) [IsImmersion j.left]
    (v : V.left) (hv : j.left v = D.restrictedObjectPoint) :
    let E : SliceSituation := ⟨D.S, D.restrictedGroupoid, V, j,
      D.restrictedObjectPoint, v, hv⟩
    let K : SliceSituation := ⟨D.S, D.groupoid, V,
      j ≫ D.restriction.hom.mapObjects, D.u, v,
      (congrArg D.restriction.hom.mapObjects.left hv).trans
        (restriction_mapObjects_point D)⟩
    topologicalKrullDimAt K.restrictedSourceFiber
        K.sliceIdentityPoints.restrictedSourceIdentity ≤
      topologicalKrullDimAt E.restrictedSourceFiber
        E.sliceIdentityPoints.restrictedSourceIdentity := by
  dsimp only
  let E : SliceSituation := ⟨D.S, D.restrictedGroupoid, V, j,
    D.restrictedObjectPoint, v, hv⟩
  let K : SliceSituation := ⟨D.S, D.groupoid, V,
    j ≫ D.restriction.hom.mapObjects, D.u, v,
    (congrArg D.restriction.hom.mapObjects.left hv).trans (restriction_mapObjects_point D)⟩
  let s := restrictionSource D.groupoid K.g
  let t := restrictionTarget D.groupoid K.g
  let a := restrictionArrowsToArrows D.groupoid K.g
  obtain ⟨l, hls, hlt, hla⟩ := exists_restriction_lift D.groupoid D.g D.restriction
    (s ≫ j) (t ≫ j) a
    ((AlgebraicGeometry.GroupoidScheme.restriction_condition D.groupoid K.g).symm.trans
      (Category.assoc _ _ _).symm)
    ((restriction_target_arrow D.groupoid K.g).symm.trans (Category.assoc _ _ _).symm)
  let m := restrictionLift D.restrictedGroupoid j s t l hls.symm hlt.symm
  have hms : m ≫ restrictionSource D.restrictedGroupoid j = s :=
    restrictionLift_source _ _ _ _ _ _ _
  have hma : m ≫ restrictionArrowsToArrows D.restrictedGroupoid j ≫
      D.restriction.hom.mapArrows = a :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ D.restriction.hom.mapArrows)
        (restrictionLift_arrow D.restrictedGroupoid j s t l hls.symm hlt.symm)).trans hla)
  have himo := restriction_mapObjects_isImmersion D
  let : IsImmersion K.g.left :=
    @IsImmersion.comp _ _ _ j.left D.restriction.hom.mapObjects.left inferInstance himo
  have htEmb : Topology.IsEmbedding
      (restrictionArrowsToArrows D.restrictedGroupoid j ≫
        D.restriction.hom.mapArrows).left :=
    (restrictionMapArrows_isImmersion D).isEmbedding.comp
      (restrictionArrowsToArrows_isImmersion D.restrictedGroupoid j).isEmbedding
  have hmEmb : Topology.IsEmbedding m.left := by
    apply htEmb.of_comp_iff.mp
    change Topology.IsEmbedding
      (m ≫ restrictionArrowsToArrows D.restrictedGroupoid j ≫
        D.restriction.hom.mapArrows).left
    rw [hma]
    exact (restrictionArrowsToArrows_isImmersion D.groupoid K.g).isEmbedding
  apply fiber_localDim_le K.restrictedSource E.restrictedSource m.left (𝟙 V.left)
    (by
      change (m ≫ restrictionSource D.restrictedGroupoid j).left = s.left ≫ 𝟙 _
      rw [hms, Category.comp_id]) hmEmb v v rfl
  apply htEmb.injective
  rw [K.sliceIdentityPoints.restrictedSourceIdentity_fiberι,
    E.sliceIdentityPoints.restrictedSourceIdentity_fiberι]
  change ((m ≫ restrictionArrowsToArrows D.restrictedGroupoid j ≫
    D.restriction.hom.mapArrows).left) K.sliceIdentityPoints.restrictedIdentity = _
  rw [hma, K.sliceIdentityPoints.restrictedIdentity_arrow]
  change D.groupoid.identity.left D.u = D.restriction.hom.mapArrows.left
    ((restrictionArrowsToArrows D.restrictedGroupoid j).left
      E.sliceIdentityPoints.restrictedIdentity)
  rw [E.sliceIdentityPoints.restrictedIdentity_arrow]
  change D.groupoid.identity.left D.u =
    (D.restriction.groupoid.identity ≫ D.restriction.hom.mapArrows).left
      D.restrictedObjectPoint
  rw [← D.restriction.hom.map_identity]
  change D.groupoid.identity.left D.u = D.groupoid.identity.left
    (D.restriction.hom.mapObjects.left D.restrictedObjectPoint)
  rw [restriction_mapObjects_point]

private lemma cohenMacaulay_sourceMap_comp (D : SliceSituation.{u})
    (hD : cohenMacaulayLocallyOfFinitePresentation D.sourceMap.left)
    {V : Over D.S} (j : V ⟶ D.restrictedGroupoid.objects)
    (hj : cohenMacaulayLocallyOfFinitePresentation
      (pullback.snd j D.restrictedGroupoid.target ≫ D.restrictedGroupoid.source).left) :
    cohenMacaulayLocallyOfFinitePresentation
      (pullback.snd (j ≫ D.restriction.hom.mapObjects) D.groupoid.target ≫
        D.groupoid.source).left := by
  let := cohenMacaulayLocallyOfFinitePresentation_baseChange.{u}
  let : MorphismProperty.IsLocalAtTarget
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
    Stacks.Descent.locallyOfFinitePresentation_isLocalAtTarget_fpqc.of_le
      Scheme.fppfPrecoverage_le_fpqcPrecoverage
  let : MorphismProperty.IsLocalAtTarget
      cohenMacaulayLocallyOfFinitePresentation.{u} Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.inf (@LocallyOfFinitePresentation)
      cohenMacaulayWithLocallyNoetherianFibers
  let o : D.restriction.groupoid.objects ⟶ D.U' := eqToHom D.restriction.objects_eq
  let a : D.restriction.groupoid.arrows ⟶ restrictionArrows D.groupoid D.g :=
    eqToHom D.restriction.arrows_eq
  have ho : IsIso o := by dsimp only [o]; infer_instance
  have ha : IsIso a := by dsimp only [a]; infer_instance
  let j₀ : V ⟶ D.U' := j ≫ o
  have hs : a ≫ restrictionSource D.groupoid D.g =
      D.restriction.groupoid.source ≫ o := by
    rw [D.restriction.source_eq]
    dsimp only [a, o]
    simp
  have ht : D.restriction.groupoid.target ≫ o =
      a ≫ restrictionTarget D.groupoid D.g := by
    rw [D.restriction.target_eq]
    dsimp only [a, o]
    simp
  let q : pullback j D.restriction.groupoid.target ⟶
      pullback j₀ (restrictionTarget D.groupoid D.g) :=
    pullback.map j D.restriction.groupoid.target j₀
      (restrictionTarget D.groupoid D.g) (𝟙 _) a o (by simp [j₀]) ht
  have hqiso : IsIso q :=
    @pullback.map_isIso _ _ _ _ _ _ _ _ j D.restriction.groupoid.target _ j₀
      (restrictionTarget D.groupoid D.g) _ (𝟙 _) a o (by simp [j₀]) ht
      inferInstance ha ho
  have hq : q ≫ secondSourceMap D.groupoid D.g j₀ =
      (pullback.snd j D.restriction.groupoid.target ≫
        D.restriction.groupoid.source) ≫ o := by
    have h1 : q ≫ pullback.snd j₀ (restrictionTarget D.groupoid D.g) =
        pullback.snd j D.restriction.groupoid.target ≫ a :=
      pullback.lift_snd _ _ _
    calc q ≫ secondSourceMap D.groupoid D.g j₀
        = (q ≫ pullback.snd j₀ (restrictionTarget D.groupoid D.g)) ≫
            restrictionSource D.groupoid D.g := (Category.assoc _ _ _).symm
      _ = (pullback.snd j D.restriction.groupoid.target ≫ a) ≫
            restrictionSource D.groupoid D.g :=
          congrArg (· ≫ restrictionSource D.groupoid D.g) h1
      _ = pullback.snd j D.restriction.groupoid.target ≫
            (a ≫ restrictionSource D.groupoid D.g) := Category.assoc _ _ _
      _ = pullback.snd j D.restriction.groupoid.target ≫
            (D.restriction.groupoid.source ≫ o) :=
          congrArg (pullback.snd j D.restriction.groupoid.target ≫ ·) hs
      _ = (pullback.snd j D.restriction.groupoid.target ≫
            D.restriction.groupoid.source) ≫ o := (Category.assoc _ _ _).symm
  have hinv : secondSourceMap D.groupoid D.g j₀ =
      inv q ≫ (pullback.snd j D.restriction.groupoid.target ≫
        D.restriction.groupoid.source) ≫ o :=
    (IsIso.inv_hom_id_assoc q (secondSourceMap D.groupoid D.g j₀)).symm.trans
      (congrArg (inv q ≫ ·) hq)
  let : IsIso (inv q).left :=
    inferInstanceAs (IsIso ((Over.forget D.S).map (inv q)))
  let : IsIso o.left := inferInstanceAs (IsIso ((Over.forget D.S).map o))
  have key : (inv q).left ≫ (pullback.snd j D.restriction.groupoid.target ≫
        D.restriction.groupoid.source).left ≫ o.left =
      (secondSourceMap D.groupoid D.g j₀).left :=
    congrArg Over.Hom.left hinv.symm
  have hsecond : cohenMacaulayLocallyOfFinitePresentation
      (secondSourceMap D.groupoid D.g j₀).left := by
    have hP := cohenMacaulayLocallyOfFinitePresentation_comp
      (openImmersion_cohenMacaulayLocallyOfFinitePresentation (inv q).left)
      (cohenMacaulayLocallyOfFinitePresentation_comp hj
        (openImmersion_cohenMacaulayLocallyOfFinitePresentation o.left))
    exact key ▸ hP
  let f := D.sourceMap.left
  let : LocallyOfFinitePresentation f := hD.1
  let : Flat f := flat_of_isCohenMacaulay f hD.2.choose hD.2.choose_spec
  let W : D.groupoid.objects.left.Opens := ⟨Set.range f, f.isOpenMap.isOpen_range⟩
  have hfW : Set.range f ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    exact Subset.rfl
  let fW := IsOpenImmersion.lift W.ι f hfW
  have hfac : fW ≫ W.ι = f := IsOpenImmersion.lift_fac _ _ _
  have sq := IsOpenImmersion.isPullback_lift_id f W.ι hfW
  let : Flat fW := MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip
    (inferInstance : Flat f)
  let : LocallyOfFinitePresentation fW :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip
      (inferInstance : LocallyOfFinitePresentation f)
  let : Surjective fW := ⟨by
    intro y
    obtain ⟨x, hx⟩ := y.2
    refine ⟨x, W.ι.isOpenEmbedding.injective ?_⟩
    change (fW ≫ W.ι) x = _
    rw [hfac]
    exact hx⟩
  obtain ⟨k, hk, hPk⟩ := AlgebraicGeometry.descent_to_open_image
    D.groupoid D.g j₀ Scheme.fppfPrecoverage
    cohenMacaulayLocallyOfFinitePresentation W fW hfac rfl
    fW.singleton_mem_fppfPrecoverage hsecond
  have hP := cohenMacaulayLocallyOfFinitePresentation_comp hPk
    (openImmersion_cohenMacaulayLocallyOfFinitePresentation W.ι)
  rw [hk] at hP
  have hg : j ≫ D.restriction.hom.mapObjects = j₀ ≫ D.g := by
    rw [D.restriction.mapObjects_eq]
    exact (Category.assoc _ _ _).symm
  let P' (k : V ⟶ D.groupoid.objects) : Prop :=
    cohenMacaulayLocallyOfFinitePresentation
      (pullback.snd k D.groupoid.target ≫ D.groupoid.source).left
  have hh : P' (j₀ ≫ D.g) := hP
  exact (congrArg P' hg).mpr hh

private lemma zero_le_localDim {X : Type*} [TopologicalSpace X] (x : X) :
    0 ≤ topologicalKrullDimAt X x := by
  rw [topologicalKrullDimAt]
  refine le_iInf fun U => ?_
  have hne : topologicalKrullDim U.1 ≠ ⊥ := by
    rw [Ne, topologicalKrullDim_eq_bot_iff_isEmpty]
    exact fun h => h.elim ⟨x, U.2.1⟩
  generalize topologicalKrullDim U.1 = d at hne ⊢
  cases d with
  | bot => exact (hne rfl).elim
  | coe a => simp

private lemma exists_nat_eq_of_bounds {d : WithBot ℕ∞} (h0 : 0 ≤ d)
    {n : ℕ} (hn : d ≤ n) : ∃ m : ℕ, d = m := by
  cases d with
  | bot => simp at h0
  | coe a =>
    have ha : a ≠ ⊤ := by
      intro h
      subst a
      exact (natCast_ne_top_withBot n) (top_le_iff.mp hn)
    obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp ha
    exact ⟨m, rfl⟩

private structure AffineCohenMacaulaySlice {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.objects.left) where
  U' : Over S
  g : U' ⟶ G.objects
  point : U'.left
  mapsTo : g.left point = u
  affine : IsAffine U'.left
  immersion : IsImmersion g.left
  locallyOfFinitePresentation : LocallyOfFinitePresentation g.left
  sourceProperty : cohenMacaulayLocallyOfFinitePresentation
    (pullback.snd g G.target ≫ G.source).left

private noncomputable abbrev AffineCohenMacaulaySlice.situation {S : Scheme.{u}}
    {G : GroupoidScheme S} {u : G.objects.left} (A : AffineCohenMacaulaySlice G u) :
    SliceSituation := ⟨S, G, A.U', A.g, u, A.point, A.mapsTo⟩

private noncomputable abbrev AffineCohenMacaulaySlice.dimension {S : Scheme.{u}}
    {G : GroupoidScheme S} {u : G.objects.left} (A : AffineCohenMacaulaySlice G u) :
    WithBot ℕ∞ := topologicalKrullDimAt A.situation.restrictedSourceFiber
      A.situation.sliceIdentityPoints.restrictedSourceIdentity

private lemma affineCohenMacaulaySlice_nonempty {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.objects.left) [LocallyOfFinitePresentation G.source.left]
    (hs : ∃ hf : ∀ y, IsLocallyNoetherian (G.source.left.fiber y),
      Scheme.Hom.IsCohenMacaulay G.source.left hf) :
    Nonempty (AffineCohenMacaulaySlice G u) := by
  obtain ⟨W, hW, huW, -⟩ := exists_affine_open_nbhd_le ⊤ u (by trivial)
  let V : Over S := Over.mk (W.ι ≫ G.objects.hom)
  let g : V ⟶ G.objects := Over.homMk W.ι
  let : IsOpenImmersion g.left := (inferInstance : IsOpenImmersion W.ι)
  let : IsOpenImmersion (pullback.snd g G.target).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      ((IsPullback.of_hasPullback g G.target).map (Over.forget S))
      (inferInstance : IsOpenImmersion W.ι)
  exact ⟨⟨V, g, ⟨u, huW⟩, rfl, hW, inferInstance, inferInstance,
    cohenMacaulayLocallyOfFinitePresentation_comp
      (openImmersion_cohenMacaulayLocallyOfFinitePresentation (pullback.snd g G.target).left)
      ⟨inferInstance, hs⟩⟩⟩

private lemma exists_affineCohenMacaulaySlice_smaller {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.objects.left)
    [LocallyOfFinitePresentation G.source.left] [LocallyOfFinitePresentation G.target.left]
    (hu : AlgebraicGeometry.IsFiniteTypePoint u)
    (hs : ∃ hf : ∀ y, IsLocallyNoetherian (G.source.left.fiber y),
      Scheme.Hom.IsCohenMacaulay G.source.left hf)
    (ht : ∃ hf : ∀ y, IsLocallyNoetherian (G.target.left.fiber y),
      Scheme.Hom.IsCohenMacaulay G.target.left hf)
    (hdim : topologicalKrullDim ((stabilizer G).hom.fiber u) <
      topologicalKrullDimAt (G.source.left.fiber u) (sourceFiberIdentity G u)) :
    ∃ A : AffineCohenMacaulaySlice G u, A.dimension <
      topologicalKrullDimAt (G.source.left.fiber u) (sourceFiberIdentity G u) := by
  obtain ⟨n, hn⟩ := sourceFiberIdentity_has_finite_dimension_bound G u
  obtain ⟨m, hm⟩ := exists_nat_eq_of_bounds (zero_le_localDim _) hn
  obtain ⟨U', g, u', hgu, hAffine, hImm, hLfp, hx, hdrop⟩ :=
    exists_affine_slice_dim_sub_one G u hs ht hu hdim
  let D : SliceSituation := ⟨S, G, U', g, u, u', hgu⟩
  let := hImm
  let := hLfp
  obtain ⟨x, hx₁, hx₂, hf, hcm⟩ := hx
  obtain ⟨W, huW, hW⟩ := exists_open_cohenMacaulay_slice D hs ht x hx₁ hf hcm
  obtain ⟨B, hB, huB, hBW⟩ := exists_affine_open_nbhd_le W u' huW
  let V : Over S := Over.mk (B.ι ≫ U'.hom)
  let j : V ⟶ U' := Over.homMk B.ι
  let : IsOpenImmersion j.left := (inferInstance : IsOpenImmersion B.ι)
  let v : V.left := ⟨u', huB⟩
  have hjW : Set.range j.left ⊆ W := by
    rintro _ ⟨z, rfl⟩
    exact hBW z.2
  have hp := cohenMacaulay_sourceMap_open_refinement D j W hjW hW
  let A : AffineCohenMacaulaySlice G u :=
    ⟨V, j ≫ g, v, hgu, hB, IsImmersion.comp j.left g.left,
      locallyOfFinitePresentation_comp j.left g.left, hp⟩
  refine ⟨A, (refinement_dim_le D j v rfl).trans_lt ?_⟩
  rw [hm]
  exact dimension_lt_nat_of_add_one_eq hdrop (le_of_eq hm)

end

/-- **Stacks Project, Tag 04MZ.** Let `(U, R, s, t, c, e, i)` be a groupoid scheme whose source
and target maps are Cohen--Macaulay and locally of finite presentation, and let `u` be a finite
type point of `U`. Then there are an affine scheme `U'` and a morphism `g : U' ⟶ U` which is an
immersion through `u` and locally of finite presentation, such that `h : U' ×_{g,U,t} R ⟶ U`
and the source and target maps of the restricted groupoid are again Cohen--Macaulay and locally
of finite presentation, and the restricted source fibre `F'_u` has at the identity arrow exactly
the dimension of the restricted stabilizer fibre `G'_u`. -/
@[stacks 04MZ]
public theorem exists_affine_slice_dim_eq_stabilizer {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.objects.left)
    (hu : AlgebraicGeometry.IsFiniteTypePoint u)
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left]
    (hs : ∃ hf : ∀ y : G.objects.left,
      IsLocallyNoetherian (G.source.left.fiber y),
      Scheme.Hom.IsCohenMacaulay G.source.left hf)
    (_ht : ∃ hf : ∀ y : G.objects.left,
      IsLocallyNoetherian (G.target.left.fiber y),
      Scheme.Hom.IsCohenMacaulay G.target.left hf) :
    ∃ (U' : Over S) (g : U' ⟶ G.objects) (u' : U'.left)
      (hgu : g.left u' = u),
      let D : SliceSituation :=
        { S := S, groupoid := G, U' := U', g := g,
          u := u, u' := u', mapsTo := hgu }
      IsAffine U'.left ∧
      IsImmersion g.left ∧
      LocallyOfFinitePresentation g.left ∧
      LocallyOfFinitePresentation D.sourceMap.left ∧
      (∃ hf : ∀ y : G.objects.left,
        IsLocallyNoetherian (D.sourceMap.left.fiber y),
        Scheme.Hom.IsCohenMacaulay D.sourceMap.left hf) ∧
      LocallyOfFinitePresentation D.restrictedGroupoid.source.left ∧
      (∃ hf : ∀ y : D.restrictedGroupoid.objects.left,
        IsLocallyNoetherian (D.restrictedGroupoid.source.left.fiber y),
        Scheme.Hom.IsCohenMacaulay D.restrictedGroupoid.source.left hf) ∧
      LocallyOfFinitePresentation D.restrictedGroupoid.target.left ∧
      (∃ hf : ∀ y : D.restrictedGroupoid.objects.left,
        IsLocallyNoetherian (D.restrictedGroupoid.target.left.fiber y),
        Scheme.Hom.IsCohenMacaulay D.restrictedGroupoid.target.left hf) ∧
      topologicalKrullDimAt D.restrictedSourceFiber
          D.sliceIdentityPoints.restrictedSourceIdentity =
        topologicalKrullDim D.restrictedStabilizerFiber := by
  classical
  have hnonempty := affineCohenMacaulaySlice_nonempty G u hs
  obtain ⟨d, ⟨A, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := WithBot ℕ∞)).has_min
      (Set.range (AffineCohenMacaulaySlice.dimension (G := G) (u := u)))
      (Set.range_nonempty _)
  let D := A.situation
  let : IsImmersion D.g.left := A.immersion
  have hP := restrictedGroupoid_cohenMacaulayLocallyOfFinitePresentation D A.sourceProperty
  let : LocallyOfFinitePresentation D.restrictedGroupoid.source.left := hP.1.1
  let : LocallyOfFinitePresentation D.restrictedGroupoid.target.left := hP.2.1
  have himo := restriction_mapObjects_isImmersion D
  let := himo
  have hfinite : AlgebraicGeometry.IsFiniteTypePoint D.restrictedObjectPoint :=
    isFiniteTypePoint_of_immersion D.restriction.hom.mapObjects.left
      D.restrictedObjectPoint (by rw [restriction_mapObjects_point]; exact hu)
  have heq : topologicalKrullDimAt
      (D.restrictedGroupoid.source.left.fiber D.restrictedObjectPoint)
      (sourceFiberIdentity D.restrictedGroupoid D.restrictedObjectPoint) =
        topologicalKrullDim D.restrictedStabilizerFiber := by
    by_contra hne
    have hlt := stabilizerFiber_dim_lt_sourceFiberIdentity_localDim_of_ne
      D.restrictedGroupoid D.restrictedObjectPoint (Ne.symm hne)
    obtain ⟨E, hE⟩ := exists_affineCohenMacaulaySlice_smaller D.restrictedGroupoid
      D.restrictedObjectPoint hfinite hP.1.2 hP.2.2 hlt
    let : IsImmersion E.g.left := E.immersion
    let : LocallyOfFinitePresentation E.g.left := E.locallyOfFinitePresentation
    let : LocallyOfFinitePresentation D.g.left := A.locallyOfFinitePresentation
    have hfpo : LocallyOfFinitePresentation D.restriction.hom.mapObjects.left := by
      rw [D.restriction.mapObjects_eq]
      exact locallyOfFinitePresentation_comp
        ((Over.forget S).mapIso (eqToIso D.restriction.objects_eq)).hom D.g.left
    let := hfpo
    let K : AffineCohenMacaulaySlice G u :=
      ⟨E.U', E.g ≫ D.restriction.hom.mapObjects, E.point,
        (congrArg D.restriction.hom.mapObjects.left E.mapsTo).trans
          (restriction_mapObjects_point D), E.affine,
        @IsImmersion.comp _ _ _ E.g.left D.restriction.hom.mapObjects.left
          E.immersion himo,
        @locallyOfFinitePresentation_comp _ _ _ E.g.left
          D.restriction.hom.mapObjects.left E.locallyOfFinitePresentation hfpo,
        cohenMacaulay_sourceMap_comp D A.sourceProperty E.g E.sourceProperty⟩
    apply hmin K.dimension ⟨K, rfl⟩
    have hcomp := composite_restriction_dim_le D E.g E.point E.mapsTo
    have hstrict := hcomp.trans_lt hE
    rw [restriction_fiber_dim_eq D] at hstrict
    exact hstrict
  refine ⟨A.U', A.g, A.point, A.mapsTo, A.affine, A.immersion,
    A.locallyOfFinitePresentation, A.sourceProperty.1, A.sourceProperty.2,
    hP.1.1, hP.1.2, hP.2.1, hP.2.2, ?_⟩
  exact (restriction_fiber_dim_eq D).symm.trans heq

end AlgebraicGeometry

end
