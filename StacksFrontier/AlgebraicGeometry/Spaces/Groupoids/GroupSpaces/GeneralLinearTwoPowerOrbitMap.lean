module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.GeneralLinearTwoPowerContraction

/-!
# The orbit map of a rational point of a power of the projective line

Let `k` be a field, `B` a big fppf site containing `Spec k` and `x` a `k`-rational point of
`(ℙ¹_k)^m`.  This file constructs the *orbit map* of `x`,

`(GL₂)^m ⟶ (ℙ¹_k)^m, g ↦ g · x`,

as a morphism of functors of points, and identifies its value at the `k`-point of the group
named by an `m`-tuple `M` of invertible matrices: it is `x` followed by the automorphism
`AlgebraicGeometry.Space.projectiveLinePowerFunctorMatrixAut` that `M` gives.

The contraction step of [Stacks, Tag 0AEM] needs exactly this.  [Stacks, Tag 0AEJ] gives a
statement — that `f` carries the translate `M · C` of a contracted piece into something finite —
only for the `k`-points `M` of an *open neighbourhood* `U` of the identity, while the orbit
density which the step consumes is a statement about the `k`-points of the whole group.  The
passage from one to the other is a rigidity argument *on the group*: the two morphisms

`(GL₂)^m ⟶ Z, g ↦ f(g · x)` and `g ↦ f(g · y)`

agree at every `k`-point of `U`, the `k`-points of a nonempty open subspace of the irreducible
`(GL₂)^m` are dense, and `(GL₂)^m` is reduced, so the two morphisms are equal and the agreement
holds at *every* `k`-point of the group.  Those two morphisms are the orbit maps of `x` and of
`y` followed by `f`, and without them there is nothing on the group for a rigidity argument to
act on.

## Main definitions

* `AlgebraicGeometry.Space.generalLinearTwoPowerGraphSection`: the section `g ↦ (g, x)` of the
  projection `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m ⟶ (GL₂)^m` attached to a rational point `x`.
* `AlgebraicGeometry.Space.generalLinearTwoPowerOrbitMap`: **the orbit map** `g ↦ g · x`.

## Main results

* `AlgebraicGeometry.Space.comp_generalLinearTwoPowerGraphSection`: over the `k`-point named by
  `M` the section `g ↦ (g, x)` is `x` followed by the fibre of the product over that point.
* `AlgebraicGeometry.Space.comp_generalLinearTwoPowerOrbitMap`: **the value of the orbit map at
  the `k`-point named by `M` is `M · x`.**

## Implementation notes

The section is built from the product decomposition
`AlgebraicGeometry.Space.isLimitBinaryFanFunctorProjections` of the functor of points of
`(GL₂)^m ×_{Spec k} (ℙ¹_k)^m`, pairing the identity of the group with the constant morphism at
`x`; the base is terminal among presheaves on the site, so "constant at `x`" is the structure
morphism followed by `x`.  The identification at a `k`-point is then the uniqueness part of that
product decomposition together with the two already proved components of
`AlgebraicGeometry.Space.projectiveLinePowerPointSection`.

## References

* [Stacks Project, Tag 0AEJ](https://stacks.math.columbia.edu/tag/0AEJ)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (k : Type u) [Field k] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (CommRingCat.of k))) (m : ℕ)
  (x : baseFunctor k B hk ⟶ projectiveLinePower k B hk (Fin m))

/-- **The section `g ↦ (g, x)` of the projection `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m ⟶ (GL₂)^m`**
attached to a `k`-rational point `x` of `(ℙ¹_k)^m`: the pair of the identity of the group and
the constant morphism at `x`, taken through the product decomposition
`AlgebraicGeometry.Space.isLimitBinaryFanFunctorProjections`. -/
def generalLinearTwoPowerGraphSection :
    generalLinearTwoPowerFunctor k B hk m ⟶
      yoneda.obj (generalLinearTwoPowerProjectiveLinePowerSiteObject k B hk m) :=
  (isLimitBinaryFanFunctorProjections k B hk m).lift
    (BinaryFan.mk (𝟙 (generalLinearTwoPowerFunctor k B hk m))
      (toBaseFunctor k B hk (generalLinearTwoPowerFunctor k B hk m) ≫ x))

/-- The section `g ↦ (g, x)` followed by the projection `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m ⟶ (GL₂)^m`
is the identity of `(GL₂)^m`. -/
@[reassoc]
theorem generalLinearTwoPowerGraphSection_comp_generalLinearTwoPowerFunctorProjection :
    generalLinearTwoPowerGraphSection k B hk m x ≫
        generalLinearTwoPowerFunctorProjection k B hk m =
      𝟙 (generalLinearTwoPowerFunctor k B hk m) :=
  (isLimitBinaryFanFunctorProjections k B hk m).fac _ ⟨WalkingPair.left⟩

/-- The section `g ↦ (g, x)` followed by the projection `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m ⟶ (ℙ¹_k)^m`
is the constant morphism at `x`: the structure morphism of `(GL₂)^m` followed by `x`. -/
@[reassoc]
theorem generalLinearTwoPowerGraphSection_comp_projectiveLinePowerFunctorProjection :
    generalLinearTwoPowerGraphSection k B hk m x ≫
        projectiveLinePowerFunctorProjection k B hk m =
      toBaseFunctor k B hk (generalLinearTwoPowerFunctor k B hk m) ≫ x :=
  (isLimitBinaryFanFunctorProjections k B hk m).fac _ ⟨WalkingPair.right⟩

/-- **The orbit map of a `k`-rational point `x` of `(ℙ¹_k)^m`**: the morphism of functors of
points `(GL₂)^m ⟶ (ℙ¹_k)^m` given by `g ↦ g · x`. -/
def generalLinearTwoPowerOrbitMap :
    generalLinearTwoPowerFunctor k B hk m ⟶ projectiveLinePower k B hk (Fin m) :=
  generalLinearTwoPowerGraphSection k B hk m x ≫ generalLinearTwoPowerAction k B hk m

variable (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k)

/-- **Over the `k`-point of `(GL₂)^m` named by `M` the section `g ↦ (g, x)` is `x` followed by
the fibre of `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` over that point.**  Both sides have the `k`-point `M`
as their component in the group and `x` as their component in `(ℙ¹_k)^m`. -/
theorem comp_generalLinearTwoPowerGraphSection :
    yoneda.map (generalLinearTwoPowerSitePoint k B hk m M) ≫
        generalLinearTwoPowerGraphSection k B hk m x =
      x ≫ projectiveLinePowerPointSection k B hk m M := by
  have hb₁ : x ≫ (base_isTerminal k B hk).from (projectiveLinePower k B hk (Fin m)) =
      𝟙 (baseFunctor k B hk) := (base_isTerminal k B hk).hom_ext _ _
  have hb₂ : yoneda.map (generalLinearTwoPowerSitePoint k B hk m M) ≫
      toBaseFunctor k B hk (generalLinearTwoPowerFunctor k B hk m) =
      𝟙 (baseFunctor k B hk) := (base_isTerminal k B hk).hom_ext _ _
  refine BinaryFan.IsLimit.hom_ext (isLimitBinaryFanFunctorProjections k B hk m) ?_ ?_
  · show yoneda.map (generalLinearTwoPowerSitePoint k B hk m M) ≫
        generalLinearTwoPowerGraphSection k B hk m x ≫
          generalLinearTwoPowerFunctorProjection k B hk m =
      (x ≫ projectiveLinePowerPointSection k B hk m M) ≫
        generalLinearTwoPowerFunctorProjection k B hk m
    rw [generalLinearTwoPowerGraphSection_comp_generalLinearTwoPowerFunctorProjection,
      Category.comp_id, Category.assoc,
      projectiveLinePowerPointSection_comp_generalLinearTwoPowerFunctorProjection,
      ← Category.assoc, hb₁, Category.id_comp]
  · show yoneda.map (generalLinearTwoPowerSitePoint k B hk m M) ≫
        generalLinearTwoPowerGraphSection k B hk m x ≫
          projectiveLinePowerFunctorProjection k B hk m =
      (x ≫ projectiveLinePowerPointSection k B hk m M) ≫
        projectiveLinePowerFunctorProjection k B hk m
    rw [generalLinearTwoPowerGraphSection_comp_projectiveLinePowerFunctorProjection,
      ← Category.assoc, hb₂, Category.id_comp, Category.assoc,
      projectiveLinePowerPointSection_comp_projectiveLinePowerFunctorProjection,
      Category.comp_id]

/-- **The value of the orbit map of `x` at the `k`-point of `(GL₂)^m` named by `M` is `M · x`**:
the orbit map evaluated at `M` is `x` followed by the automorphism of `(ℙ¹_k)^m` that `M` gives.

This is what makes the two morphisms `g ↦ f(g · x)` and `g ↦ f(g · y)` on the group usable: an
identity between them specializes, at each `k`-point `M` of the group, to the identity
`f(M · x) = f(M · y)` between morphisms out of the base. -/
theorem comp_generalLinearTwoPowerOrbitMap :
    yoneda.map (generalLinearTwoPowerSitePoint k B hk m M) ≫
        generalLinearTwoPowerOrbitMap k B hk m x =
      x ≫ (projectiveLinePowerFunctorMatrixAut k B hk m M).hom := by
  rw [generalLinearTwoPowerOrbitMap, ← Category.assoc,
    comp_generalLinearTwoPowerGraphSection k B hk m x M, Category.assoc,
    projectiveLinePowerPointSection_comp_generalLinearTwoPowerAction]

end AlgebraicGeometry.Space

end
