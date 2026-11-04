module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSmoothLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalOnSourceAndTarget

/-!
# A criterion for smooth locality on the source and target (Stacks 06FB)

Let `S` be a scheme contained in a big fppf site `B` and let `P` be a property of morphisms of
algebraic spaces over `S`. If `P` is local at the source and local at the target for the smooth
topology of **Stacks 03YH**, and is preserved by postcomposition with a smooth morphism, then
`P` is smooth local on the source-and-target in the sense of
`AlgebraicGeometry.Space.IsSmoothLocalOnSourceAndTarget` (**Stacks 06F8**).

This is the converse of **Stacks 06F9**, which extracts the two locality statements and the
postcomposition statement from smooth locality on the source-and-target. Together they say the
two formulations agree, and this direction is the one that is used to *verify* smooth locality
on the source-and-target for a concrete property.

## Main results

* `AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget`: **Stacks 06FB**.
* `AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget_forall_isAlgebraicSpace`: the same
  criterion for a property of the *category* `AlgebraicGeometry.AlgebraicSpaces` rather than of
  morphisms of presheaves.

## Implementation notes

The two locality hypotheses are Mathlib's `CategoryTheory.MorphismProperty.IsLocalAtSource` and
`CategoryTheory.MorphismProperty.IsLocalAtTarget` for
`AlgebraicGeometry.Space.Topology.precoverage` at the smooth topology, taken as instance
arguments. They are conditions on a property of the category
`AlgebraicGeometry.AlgebraicSpaces` of **Stacks 02X2**, while `P` is a property of morphisms of
presheaves, so they are imposed on the inverse image of `P` along the inclusion of that
category; the conclusion is stated for `P` itself, with algebraicity carried by explicit
hypotheses in each clause, which is the shape of Stacks 06F8.

The first two clauses of the conclusion are about a *single* smooth morphism, which need not be
surjective, whereas the locality hypotheses speak about covering families. The gap is closed by
`AlgebraicGeometry.Space.mem_precoverage_pair_smooth`, which adjoins the identity to a single
smooth morphism to make a smooth covering family; the second clause is then exactly
`AlgebraicGeometry.Space.pullbackSnd_of_isSmooth`. The index type of a covering family is a free
universe parameter of the precoverage, instantiated at `u + 1` throughout, matching the type of
`AlgebraicGeometry.Space.points`: the covering family built in the last clause is indexed by the
points of the source.

Stacks 06F8 takes a property of morphisms of *presheaves*, with algebraicity carried by explicit
hypotheses, whereas several properties of morphisms of algebraic spaces are defined as
properties of the category `AlgebraicGeometry.AlgebraicSpaces` instead.
`isSmoothLocalOnSourceAndTarget_forall_isAlgebraicSpace` bridges the two: the presheaf-level
property it feeds to the criterion is `U` of the morphism of algebraic spaces determined by any
witnesses of algebraicity of the source and target, which on morphisms whose source and target
*are* algebraic spaces is equal to `U`, and that equality is what transports the two locality
hypotheses.

## References

* [Stacks Project, Tag 06FB](https://stacks.math.columbia.edu/tag/06FB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 06FB.** A property of morphisms of algebraic spaces over `S` which is local at the
source and at the target for the smooth topology, and is preserved by postcomposition with a
smooth morphism, is smooth local on the source-and-target. -/
@[stacks 06FB]
theorem isSmoothLocalOnSourceAndTarget
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    [hSource : (P.inverseImage (ObjectProperty.ι
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))).IsLocalAtSource
      (Topology.precoverage.{u, u + 1} .smooth B S hS)]
    [hTarget : (P.inverseImage (ObjectProperty.ι
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))).IsLocalAtTarget
      (Topology.precoverage.{u, u + 1} .smooth B S hS)]
    (hcomp : ∀ {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (_hX : IsAlgebraicSpace B S hS X)
      (_hY : IsAlgebraicSpace B S hS Y)
      (_hZ : IsAlgebraicSpace B S hS Z)
      (f : X ⟶ Y) (g : Y ⟶ Z),
      P f → IsSmooth B S hS g → P (f ≫ g)) :
    IsSmoothLocalOnSourceAndTarget B S hS P := by
  classical
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    P.inverseImage (ObjectProperty.ι fun F => IsAlgebraicSpace B S hS F)
  let : Q.IsLocalAtSource (Topology.precoverage.{u, u + 1} .smooth B S hS) := hSource
  let : Q.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .smooth B S hS) := hTarget
  refine ⟨?_, ?_, ?_⟩
  · intro X Y Z hX hY hZ f g hf hg
    let X' : AlgebraicSpaces B S hS := ⟨X, hX⟩
    let Y' : AlgebraicSpaces B S hS := ⟨Y, hY⟩
    let Z' : AlgebraicSpaces B S hS := ⟨Z, hZ⟩
    let f' : X' ⟶ Y' := ObjectProperty.homMk f
    let g' : Y' ⟶ Z' := ObjectProperty.homMk g
    have hg' : Q g' := hg
    exact MorphismProperty.IsLocalAtSource.comp (P := Q)
      (mem_precoverage_pair_smooth f' hf) f' (.mk (ULift.up true)) hg'
  · intro X Y Y' hX hY hY' f g hf hg
    let Xₐ : AlgebraicSpaces B S hS := ⟨X, hX⟩
    let Yₐ : AlgebraicSpaces B S hS := ⟨Y, hY⟩
    let Y'ₐ : AlgebraicSpaces B S hS := ⟨Y', hY'⟩
    exact pullbackSnd_of_isSmooth (P := Q) (ObjectProperty.homMk f : Xₐ ⟶ Yₐ) hf
      (ObjectProperty.homMk g : Y'ₐ ⟶ Yₐ) hg
  · intro X Y hX hY f
    refine ⟨fun hf x => ⟨X, Y, hX, hY, 𝟙 X, 𝟙 Y, f, x, isSmooth_id_presheaf B S hS X,
      isSmooth_id_presheaf B S hS Y, congrFun (pointsMap_id B S hS X) x, by simp, hf⟩,
      fun hLoc => ?_⟩
    choose U V hU hV a b h u ha hb hu hcomm hh using hLoc
    let X' : AlgebraicSpaces B S hS := ⟨X, hX⟩
    let Y' : AlgebraicSpaces B S hS := ⟨Y, hY⟩
    let UA : points B S hS X → AlgebraicSpaces B S hS := fun x => ⟨U x, hU x⟩
    let aa : (x : points B S hS X) → UA x ⟶ X' := fun x => ObjectProperty.homMk (a x)
    have hR : Presieve.ofArrows UA aa ∈
        (Topology.precoverage.{u, u + 1} .smooth B S hS).coverings X' := by
      refine ⟨points B S hS X, UA, aa, rfl, hX, hU, hX, hU, ha, ?_⟩
      exact Set.eq_univ_iff_forall.mpr fun z =>
        Set.mem_iUnion.mpr ⟨z, Set.mem_range.mpr ⟨u z, hu z⟩⟩
    show Q (ObjectProperty.homMk f : X' ⟶ Y')
    apply MorphismProperty.IsLocalAtSource.of_forall_comp hR
    rintro U₀ a₀ ⟨x⟩
    show P (a x ≫ f)
    rw [← hcomm x]
    exact hcomp (hU x) (hV x) hY (h x) (b x) (hh x) (hb x)

/-- **Stacks 06FB** for a property `U` of morphisms of the category of algebraic spaces over
`S`, rather than of morphisms of presheaves: if `U` is local at the source and at the target for
the smooth topology and is preserved by postcomposition with a smooth morphism, then the
presheaf-level property asserting `U` of the morphism of algebraic spaces determined by any
witnesses of algebraicity is smooth local on the source-and-target. -/
theorem isSmoothLocalOnSourceAndTarget_forall_isAlgebraicSpace
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : MorphismProperty (AlgebraicSpaces B S hS))
    [hSource : U.IsLocalAtSource (Topology.precoverage.{u, u + 1} .smooth B S hS)]
    [hTarget : U.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .smooth B S hS)]
    (hcomp : ∀ {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z),
      U f → IsSmooth B S hS g.hom → U (f ≫ g)) :
    IsSmoothLocalOnSourceAndTarget B S hS
      (fun X Y f =>
        ∀ (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y),
          U (ObjectProperty.homMk f :
            (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ (⟨Y, hY⟩ : AlgebraicSpaces B S hS))) := by
  let P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun X Y f =>
      ∀ (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y),
        U (ObjectProperty.homMk f :
          (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ (⟨Y, hY⟩ : AlgebraicSpaces B S hS))
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    P.inverseImage (ObjectProperty.ι fun F => IsAlgebraicSpace B S hS F)
  have hQU : Q = U := by
    ext X Y f
    exact ⟨fun hf => hf X.property Y.property, fun hf _ _ => hf⟩
  let : Q.IsLocalAtSource (Topology.precoverage.{u, u + 1} .smooth B S hS) := hQU ▸ hSource
  let : Q.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .smooth B S hS) := hQU ▸ hTarget
  exact isSmoothLocalOnSourceAndTarget B S hS P fun hX hY hZ f g hf hg hX' hZ' =>
    hcomp (ObjectProperty.homMk f : (⟨_, hX'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hY⟩)
      (ObjectProperty.homMk g : (⟨_, hY⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hZ'⟩)
      (hf hX' hY) hg

end AlgebraicGeometry.Space

end
