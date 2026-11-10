module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSmoothLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization

/-!
# Towards étale-smooth locality on source and target

Let `S` be a scheme contained in a big fppf site `B` and let `P` be a property of morphisms
of algebraic spaces over `S`. Stacks 0CG2 asserts that if `P` is étale local on the source,
smooth local on the target and stable under postcomposition with open immersions, then `P` is
étale-smooth local on source and target in the sense of
`AlgebraicGeometry.Space.IsEtaleSmoothLocalOnSourceAndTarget`.

This file proves the parts of that assertion which follow from the two locality hypotheses
alone: the first two clauses of the conclusion, and the forward implication of the third.
What remains is the descent half of the third clause, which the source proves by reducing to
schemes and invoking Stacks 0CF1; see the implementation notes.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isSmooth_id_presheaf`: the identity of a presheaf on the big fppf
  site of `S` is smooth. That it is étale is
  `AlgebraicGeometry.Space.isEtale_id` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RelativeNormalization.lean`.
* `AlgebraicGeometry.Space.mem_precoverage_pair_etale` and
  `AlgebraicGeometry.Space.mem_precoverage_pair_smooth`: any single étale, resp. smooth,
  morphism of algebraic spaces is a member of a two-element étale, resp. smooth, covering
  family of its target, the second member being the identity. This is what makes a locality
  hypothesis phrased with coverings yield a statement about a single morphism.
* `AlgebraicGeometry.Space.isSmoothCovering_const_id` and
  `AlgebraicGeometry.Space.isEtaleCovering_const_id`: the constant family at an algebraic space
  with the identity as every structure map is a smooth, resp. étale, covering of it.
* `AlgebraicGeometry.Space.comp_of_isEtale`: the étale case of Stacks 06EQ. A property local
  at the source for the étale topology is stable under precomposition with an étale morphism.
* `AlgebraicGeometry.Space.pullbackSnd_of_isSmooth`: the smooth case of Stacks 06EM. A
  property local at the target for the smooth topology is stable under smooth base change.
* `AlgebraicGeometry.Space.exists_etale_smooth_neighborhood_of_prop`: the forward implication
  of the locality clause of `IsEtaleSmoothLocalOnSourceAndTarget`.

## Implementation notes

The two locality hypotheses are Mathlib's `CategoryTheory.MorphismProperty.IsLocalAtSource`
and `CategoryTheory.MorphismProperty.IsLocalAtTarget` for the precoverages of Stacks 03YH.
Those classes speak only about *covering families*, whereas the first two clauses of
`IsEtaleSmoothLocalOnSourceAndTarget` speak about a *single* étale or smooth morphism, which
need not be surjective and so need not cover anything on its own. The gap is closed by
`mem_precoverage_pair_etale` and `mem_precoverage_pair_smooth`: adjoining the identity to a
single morphism produces a family which is jointly surjective for free, and whose members are
all étale, resp. smooth, because the identity is. So no appeal to Stacks 06EQ or 06EM as
separate results is needed, and the dependence of Stacks 0CG2 on them is only apparent.

The index type of a covering family is a free universe parameter of
`AlgebraicGeometry.Space.Topology.precoverage`; it is instantiated at `u + 1` here, matching
the type of `AlgebraicGeometry.Space.points`.

The forward implication of the locality clause takes the target neighbourhood to be the
identity of `Y` and the source neighbourhood to be the identity of `X ×_Y Y`; the morphism
whose property is asserted is then the smooth base change of `f` along the identity, which is
`pullbackSnd_of_isSmooth`. The point above the given one is produced from the section of the
first projection induced by `f`, using functoriality of
`AlgebraicGeometry.Space.pointsMap`.

The converse implication is *not* proved here, and is not reachable from the hypotheses
available in this development. The argument of Stacks 0CG2 combines the given neighbourhoods
into one square with a *surjective* left vertical arrow and then reduces to schemes. The left
vertical arrow of such a square is a composite of an étale morphism with the base change of a
smooth morphism, hence smooth and not étale, so neither locality hypothesis applies to it: a
property which is étale local on the source is in general not smooth local on the source.
Breaking that deadlock is exactly the content of Stacks 0CF1, whose proof refines a smooth
morphism étale-locally through affine space (Stacks 054L) and tracks the resulting largest
open locus (Stacks 0CEY). Neither of those is available here or in Mathlib.

## References

* [Stacks Project, Tag 0CG2](https://stacks.math.columbia.edu/tag/0CG2)
* [Stacks Project, Tag 06EQ](https://stacks.math.columbia.edu/tag/06EQ)
* [Stacks Project, Tag 06EM](https://stacks.math.columbia.edu/tag/06EM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The identity is étale and smooth -/

/-- A property of scheme morphisms which holds for the étale morphisms holds on every étale
chart of an identity: in a commuting square of two étale charts of `F` over the identity, the
morphism of the site factors one chart through the other, hence is étale. -/
public theorem holdsOnEveryEtaleChart_id_presheaf (P : MorphismProperty Scheme.{u})
    (hP : (@Etale.{u} : MorphismProperty Scheme.{u}) ≤ P)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    HoldsOnEveryEtaleChart B S hS P (𝟙 F) := by
  intro U V a b h ha hb hsq
  exact hP _ _ _ (etale_of_comp_etale_chart B S hS ha hb (by simpa using hsq))

/-- The identity of a presheaf on the big fppf site of `S` is smooth, because an étale
morphism of schemes is smooth. -/
public theorem isSmooth_id_presheaf (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    IsSmooth B S hS (𝟙 F) := by
  refine holdsOnEveryEtaleChart_id_presheaf B S hS _ ?_ F
  intro _ _ g hg
  have := hg
  infer_instance

/-! ### Completing a single morphism to a covering family -/

variable {B S hS}

/-- Both members of the two-element family `{X, Y}` indexed by `ULift Bool` are algebraic
spaces. -/
private theorem pair_isAlgebraicSpace {X Y : AlgebraicSpaces B S hS} (i : ULift.{u + 1, 0} Bool) :
    IsAlgebraicSpace B S hS (bif i.down then X else Y).obj := by
  rcases i with ⟨_ | _⟩
  exacts [Y.property, X.property]

/-- The two-element family consisting of an étale morphism `f : X ⟶ Y` of algebraic spaces
and the identity of `Y` is an étale covering family of `Y`. Joint surjectivity is carried by
the identity alone, so no surjectivity of `f` is needed. -/
public theorem mem_precoverage_pair_etale {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) :
    Presieve.ofArrows (fun i : ULift.{u + 1, 0} Bool => bif i.down then X else Y)
        (fun i => match i with | ⟨true⟩ => f | ⟨false⟩ => 𝟙 Y) ∈
      (Topology.precoverage.{u, u + 1} .etale B S hS) Y := by
  refine ⟨ULift.{u + 1, 0} Bool, _, _, rfl, Y.property, pair_isAlgebraicSpace, Y.property,
    pair_isAlgebraicSpace, ?_, ?_⟩
  · rintro ⟨(_ | _)⟩
    · exact isEtale_id B S hS Y.obj
    · exact hf
  · refine Set.eq_univ_iff_forall.mpr fun x => Set.mem_iUnion.mpr ⟨⟨false⟩, ?_⟩
    exact ⟨x, congrFun (pointsMap_id B S hS Y.obj) x⟩

/-- The two-element family consisting of a smooth morphism `b : Y' ⟶ Y` of algebraic spaces
and the identity of `Y` is a smooth covering family of `Y`. Joint surjectivity is carried by
the identity alone, so no surjectivity of `b` is needed. -/
public theorem mem_precoverage_pair_smooth {Y' Y : AlgebraicSpaces B S hS} (b : Y' ⟶ Y)
    (hb : IsSmooth B S hS b.hom) :
    Presieve.ofArrows (fun i : ULift.{u + 1, 0} Bool => bif i.down then Y' else Y)
        (fun i => match i with | ⟨true⟩ => b | ⟨false⟩ => 𝟙 Y) ∈
      (Topology.precoverage.{u, u + 1} .smooth B S hS) Y := by
  refine ⟨ULift.{u + 1, 0} Bool, _, _, rfl, Y.property, pair_isAlgebraicSpace, Y.property,
    pair_isAlgebraicSpace, ?_, ?_⟩
  · rintro ⟨(_ | _)⟩
    · exact isSmooth_id_presheaf B S hS Y.obj
    · exact hb
  · refine Set.eq_univ_iff_forall.mpr fun x => Set.mem_iUnion.mpr ⟨⟨false⟩, ?_⟩
    exact ⟨x, congrFun (pointsMap_id B S hS Y.obj) x⟩

variable (B S hS)


/-- The constant family at an algebraic space over `S`, with the identity as every structure
map, is an étale covering of it. Joint surjectivity is carried by any one member, so the index
type only has to be nonempty. -/
public theorem isEtaleCovering_const_id {I : Type v} [Nonempty I]
    (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z) :
    IsEtaleCovering B S hS (fun _ : I => Z) (fun _ => 𝟙 Z) := by
  refine ⟨hZ, fun _ => hZ, fun _ => isEtale_id B S hS Z, ?_⟩
  refine Set.eq_univ_iff_forall.mpr fun x =>
    Set.mem_iUnion.mpr ⟨Classical.arbitrary I, ?_⟩
  exact ⟨x, congrFun (pointsMap_id B S hS Z) x⟩

variable {B S hS}

/-! ### The clauses of étale-smooth locality which the locality hypotheses already give -/

variable {P : MorphismProperty (AlgebraicSpaces B S hS)}

/-- **Stacks 06EQ, the étale case.** A property of morphisms of algebraic spaces over `S`
which is local at the source for the étale topology is stable under precomposition with an
étale morphism. This is the first clause of
`AlgebraicGeometry.Space.IsEtaleSmoothLocalOnSourceAndTarget`. -/
public theorem comp_of_isEtale
    [P.IsLocalAtSource (Topology.precoverage.{u, u + 1} .etale B S hS)]
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsEtale B S hS f.hom) (hg : P g) : P (f ≫ g) :=
  MorphismProperty.IsLocalAtSource.comp (mem_precoverage_pair_etale f hf) f
    (.mk (ULift.up true)) hg

/-- **Stacks 06EM, the smooth case.** A property of morphisms of algebraic spaces over `S`
which is local at the target for the smooth topology is stable under base change along a
smooth morphism. This is the second clause of
`AlgebraicGeometry.Space.IsEtaleSmoothLocalOnSourceAndTarget`. -/
public theorem pullbackSnd_of_isSmooth
    [P.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .smooth B S hS)]
    {X Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : P f) (b : Y' ⟶ Y)
    (hb : IsSmooth B S hS b.hom) :
    P (ObjectProperty.homMk (pullback.snd f.hom b.hom) :
      AlgebraicSpaces.fiberProduct B S hS f b ⟶ Y') := by
  rw [← (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).isoPullback_hom_snd,
    P.cancel_left_of_respectsIso]
  exact MorphismProperty.IsLocalAtTarget.pullbackSnd (mem_precoverage_pair_smooth b hb)
    (.mk (ULift.up true)) hf

/-- The forward implication of the locality clause of
`AlgebraicGeometry.Space.IsEtaleSmoothLocalOnSourceAndTarget`: a morphism with the property
has, near every point of its source, an étale neighbourhood over a smooth target
neighbourhood on which the property holds. The neighbourhoods may be taken to be the
identity of `Y` and the identity of `X ×_Y Y`. -/
public theorem exists_etale_smooth_neighborhood_of_prop
    [P.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .smooth B S hS)]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : P f)
    (x : points B S hS X.1) :
    ∃ (V U : AlgebraicSpaces B S hS)
      (b : V ⟶ Y)
      (e : U ⟶ AlgebraicSpaces.fiberProduct B S hS f b)
      (u : points B S hS U.1),
      IsSmooth B S hS b.hom ∧
        IsEtale B S hS e.hom ∧
        pointsMap B S hS U.1
          (e ≫ (ObjectProperty.homMk (pullback.fst f.hom b.hom) :
            AlgebraicSpaces.fiberProduct B S hS f b ⟶ X)).hom u = x ∧
        P (e ≫ (ObjectProperty.homMk (pullback.snd f.hom b.hom) :
          AlgebraicSpaces.fiberProduct B S hS f b ⟶ V)) := by
  refine ⟨Y, AlgebraicSpaces.fiberProduct B S hS f (𝟙 Y), 𝟙 Y, 𝟙 _,
    pointsMap B S hS X.1 (pullback.lift (𝟙 X.1) f.hom (by simp)) x,
    isSmooth_id_presheaf B S hS Y.1, isEtale_id B S hS _, ?_, ?_⟩
  · change pointsMap B S hS _ (pullback.fst f.hom (𝟙 Y.obj))
        (pointsMap B S hS X.obj (pullback.lift (𝟙 X.obj) f.hom (by simp)) x) = x
    rw [← Function.comp_apply (f := pointsMap B S hS _ (pullback.fst f.hom (𝟙 Y.obj))),
      ← pointsMap_comp, pullback.lift_fst]
    exact congrFun (pointsMap_id B S hS X.obj) x
  · simpa using pullbackSnd_of_isSmooth f hf (𝟙 Y) (isSmooth_id_presheaf B S hS Y.1)

end AlgebraicGeometry.Space

end
