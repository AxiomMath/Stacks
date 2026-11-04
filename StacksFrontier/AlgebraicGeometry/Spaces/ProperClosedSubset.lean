module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspaceDescent

/-!
# Closed subsets of an algebraic space proper over a base

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of
finite type, and let `T` be a closed subset of the set of points of `X`. For `T` to be *proper
over `Y`* is condition (1) of Stacks 0CZC, that the reduced induced closed subspace of `X` on
`T` is proper over `Y`; that is `AlgebraicGeometry.Space.IsProperOver`, defined in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperClosedSubset` and re-exported here.
This file proves that the condition is inherited by smaller closed subsets.

`AlgebraicGeometry.Space.IsProperOver` is the *space-level* notion; the scheme-level one is
`AlgebraicGeometry.IsProperOver`.

## Main results

* `AlgebraicGeometry.Space.isProperOver_of_subset` is Stacks 0CZE: a closed subset of a closed
  subset proper over the base is proper over the base.
* `AlgebraicGeometry.Space.reducedClosedSubspace_mono`: the reduced closed subspace is
  monotone in the closed set of points, through
  `AlgebraicGeometry.Space.atlasReducedSubscheme_mono`,
  `AlgebraicGeometry.Space.invariantSubspace_mono` and
  `AlgebraicGeometry.Space.subschemePoints_mono`.

## Implementation notes

The source definition says that `T` is proper over `Y` when the equivalent conditions of
Stacks 0CZC hold, and `AlgebraicGeometry.Space.IsProperOver` is condition (1) of that lemma:
properness of `Z ⟶ Y` for `Z` the reduced induced closed subspace on `T`. Conditions (2) and
(3) quantify over closed subspaces of `X` with point set `T`; they are not used here, and the
equivalence itself is Stacks 0CZC, which this file does not prove.

`AlgebraicGeometry.Space.IsProper` takes only the morphism: algebraicity of neither end is in
its signature, each of its three conjuncts quantifying over the algebraic spaces mapping to the
target instead. So condition (1) is written directly on the inclusion of the reduced closed
subspace followed by `f`, and `AlgebraicGeometry.Space.IsProperOver` carries no descent
hypothesis. Algebraicity of that subspace,
`AlgebraicGeometry.Space.isAlgebraicSpace_reducedClosedSubspace`, is unconditional and is what
the proof of Stacks 0CZE uses, not the definition.

Algebraicity of `Y` and the hypothesis that `f` is locally of finite type are recorded in the
binders of `AlgebraicGeometry.Space.IsProperOver`, as in the source and as in the scheme-level
`AlgebraicGeometry.IsProperOver`, even though the body uses neither. The source remarks
that the lemma justifying the definition is false without finite type, so the terminology is
not to be used for an `f` which is not locally of finite type.

Unlike the scheme-level notion, the space-level one is not an application of a predicate on
morphisms to a canonical closed subscheme: a closed subspace of an algebraic space is a
subfunctor rather than an ideal sheaf, the reduced induced structure is constructed on an
étale chart, and properness is the three-fold conjunction
`AlgebraicGeometry.Space.IsProper` rather than a Mathlib class. So
`AlgebraicGeometry.Space.IsProperOver` is an abbreviation for that conjunction applied to the
inclusion of `AlgebraicGeometry.Space.reducedClosedSubspace` followed by `f`, and a client may
use the three conjuncts directly.

Monotonicity of the reduced closed subspace in the closed set is proved on the chart and
transported, which is possible because `AlgebraicGeometry.Space.reducedClosedSubspace` takes
its chart from the atlas clause of the algebraic-space hypothesis, so the two closed sets are
handled at the *same* chart; no comparison of charts is needed. On the chart the statement is
the antitonicity of the vanishing ideal, Stacks 01J3, followed by monotonicity of the
subfunctor cut out by a subscheme of the chart.

Stacks 0CZE is proved by composing: the inclusion of the smaller reduced closed subspace into
the larger one is a closed immersion, because it is a base change of a closed immersion along
a monomorphism, hence proper by Stacks 04XZ, and Stacks 04XY finishes. The source leaves the
proof to the reader.

## References

* [Stacks Project, Tag 0CZC](https://stacks.math.columbia.edu/tag/0CZC)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 0CZE](https://stacks.math.columbia.edu/tag/0CZE)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Monotonicity of the reduced closed subspace -/

section Monotone

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}

/-- The functor of points of a subscheme of an object of the site is monotone in that
subscheme: factoring through the smaller subscheme is factoring through the larger one. -/
theorem subschemePoints_mono (Z₁ Z₂ : Subobject ((BigFppfOver.toScheme B S hS).obj U))
    (h : Z₁ ≤ Z₂) : subschemePoints B S hS Z₁ ≤ subschemePoints B S hS Z₂ := by
  intro T x hx
  rw [mem_subschemePoints_iff] at hx ⊢
  exact Subobject.factors_of_le _ h hx

/-- The subfunctor of `X` cut out by a subscheme of a chart is monotone in that subscheme. -/
theorem invariantSubspace_mono (φ : yoneda.obj U ⟶ X)
    (Z₁ Z₂ : Subobject ((BigFppfOver.toScheme B S hS).obj U)) (h : Z₁ ≤ Z₂) :
    invariantSubspace B S hS φ Z₁ ≤ invariantSubspace B S hS φ Z₂ := by
  intro T x hx T' g f hf
  exact subschemePoints_mono B S hS Z₁ Z₂ h _ (hx T' g f hf)

/-- The reduced induced closed subscheme of a chart is monotone in the closed set of points of
`X` it lies over: the vanishing ideal is antitone, and a smaller ideal cuts out a larger closed
subscheme. -/
theorem atlasReducedSubscheme_mono (φ : yoneda.obj U ⟶ X) (T' T : Set (points B S hS X))
    (hT' : _root_.IsClosed T') (hT : _root_.IsClosed T) (hsub : T' ⊆ T) :
    atlasReducedSubscheme B S hS φ T' hT' ≤ atlasReducedSubscheme B S hS φ T hT := by
  have hpt : atlasPointSet B S hS φ T' ⊆ atlasPointSet B S hS φ T := fun _ hx => hsub hx
  have hid : atlasVanishingIdeal B S hS φ T hT ≤ atlasVanishingIdeal B S hS φ T' hT' :=
    Scheme.IdealSheafData.vanishingIdeal_antimono hpt
  exact Subobject.mk_le_mk_of_comm (Scheme.IdealSheafData.inclusion hid)
    (Scheme.IdealSheafData.inclusion_subschemeι hid)

/-- **The reduced closed subspace is monotone in the closed set of points.** Both sides are
computed at the chart furnished by the algebraic-space hypothesis, so this is
`AlgebraicGeometry.Space.atlasReducedSubscheme_mono` at that one chart. -/
theorem reducedClosedSubspace_mono (hX : IsAlgebraicSpace B S hS X)
    (T' T : Set (points B S hS X)) (hT' : _root_.IsClosed T') (hT : _root_.IsClosed T)
    (hsub : T' ⊆ T) :
    reducedClosedSubspace B S hS X hX T' hT' ≤ reducedClosedSubspace B S hS X hX T hT :=
  invariantSubspace_mono B S hS _ _ _
    (atlasReducedSubscheme_mono B S hS _ T' T hT' hT hsub)

end Monotone

/-! ### Closed subsets proper over the base -/

section ProperOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The inclusion of a closed subspace of `X` into a larger subfunctor of `X` is a closed
immersion: it is the base change of the inclusion of the closed subspace along the inclusion
of the larger subfunctor, which is a monomorphism.

Only the closed immersion `W.ι` is assumed; algebraicity of `W` is not needed, which is what
distinguishes this from `AlgebraicGeometry.Space.isClosedImmersion_homOfLe`, whose hypothesis
is a bundled `AlgebraicGeometry.Space.ClosedSubspaces`. -/
theorem isClosedImmersion_homOfLe' {W Z : Subfunctor X}
    (hW : IsClosedImmersion B S hS W.ι) (hle : W ≤ Z) :
    IsClosedImmersion B S hS (Subfunctor.homOfLe hle) := by
  let P := MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have : (MorphismProperty.presheaf P).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange P
  have hsq : CommSq (𝟙 W.toFunctor) (Subfunctor.homOfLe hle) W.ι Z.ι := ⟨by simp⟩
  exact (MorphismProperty.presheaf P).of_isPullback
    (IsPullback.of_horiz_isIso_mono hsq) hW

/-- **Stacks 0CZE.** A closed subset of a closed subset proper over the base is proper over the
base.

The reduced closed subspace on the smaller set is a subfunctor of the one on the larger set, so
the inclusion between them is a closed immersion and hence proper; composing with properness
over `Y` of the larger one gives the result. -/
@[stacks 0CZE]
theorem isProperOver_of_subset (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (T' T : Set (points B S hS X)) (hT' : _root_.IsClosed T') (hT : _root_.IsClosed T)
    (hsub : T' ⊆ T) (hproper : IsProperOver B S hS hX hY f hf T hT) :
    IsProperOver B S hS hX hY f hf T' hT' := by
  have hle := reducedClosedSubspace_mono B S hS hX T' T hT' hT hsub
  have hci : IsClosedImmersion B S hS (Subfunctor.homOfLe hle) :=
    isClosedImmersion_homOfLe' B S hS
      (isClosedImmersion_ι_reducedClosedSubspace B S hS hX T' hT') hle
  have hgp := isProper_of_isClosedImmersion B S hS
    (isAlgebraicSpace_reducedClosedSubspace B S hS X hX T' hT')
    (isAlgebraicSpace_reducedClosedSubspace B S hS X hX T hT) (Subfunctor.homOfLe hle) hci
  have hcomp := isProper_comp' B S hS (Subfunctor.homOfLe hle)
    ((reducedClosedSubspace B S hS X hX T hT).ι ≫ f)
    (isAlgebraicSpace_reducedClosedSubspace B S hS X hX T hT) hY hgp hproper
  show IsProper B S hS _
  simpa only [← Category.assoc, Subfunctor.homOfLe_ι] using hcomp

end ProperOver

end AlgebraicGeometry.Space

end
