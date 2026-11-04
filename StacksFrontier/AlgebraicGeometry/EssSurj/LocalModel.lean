module

public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
public import StacksFrontier.AlgebraicGeometry.Gluing.Punctured

/-!
# A model over an affine open neighbourhood avoiding the other closed points

Let `S` be a scheme, let `s : I → S` be a finite injective family of closed points and fix an
index `i`.  A scheme of finite presentation over the local scheme `Spec 𝒪_{S, s i}` is the base
change of a scheme of finite presentation over *some* affine open neighbourhood of `s i`, and the
neighbourhood may be taken to avoid every other member of the family.

This composes two known results:

* `AlgebraicGeometry.LimitFPObjectDescent.exists_model_of_finitePresentation`, which is
  [Stacks, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM) part (1), applied to
  `AlgebraicGeometry.isLimitSpecStalkCone` — the identification `Spec 𝒪_{S, s i} = lim W`;
* `AlgebraicGeometry.exists_affineOpenNhds_le_avoiding`, the shrinking half of residue item (3)
  of [Stacks, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA).

Shrinking the stage is free: the comparison between the iterated base change and the direct one
is `AlgebraicGeometry.overPullbackCompIso`, taken at the cone's own compatibility equation.  The
join half of residue item (3) is free as well — `AlgebraicGeometry.AffineOpenNhds` is an
`CategoryTheory.IsCofiltered` instance, so `CategoryTheory.IsCofiltered.min` refines the stage
the descent lands on against any prescribed neighbourhood with nothing to prove.

## Main results

* `AlgebraicGeometry.exists_affineOpenNhds_model_avoiding`: the statement above.
* `AlgebraicGeometry.exists_affineOpenNhds_model_avoiding_le`: the same, with the neighbourhood
  additionally inside a prescribed one.

## Implementation notes

Every instance Tag 01ZM asks of the system of affine open neighbourhoods is discharged by
instance search at this pin, including `CategoryTheory.EssentiallySmall` of the index category:
the index category is a full subcategory of `TopologicalSpace.OpenNhds`, which is a preorder on a
`Type u`, and the cofiltered and affine-transition instances are
`StacksDraft.AlgebraicGeometry.F3.StalkAffineNhdsLimit.Basic`'s.

No `@[stacks]` attribute is attached: Tag 0BPA has no statement in this repository, and Tag 0E8Q's
`equivalence` label has the single `CategoryTheory.Functor.IsEquivalence` assertion as its
covering set, so no lemma below can earn part of it.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA)
* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S)
  (hs : ∀ i, s i ∈ closedPoints S)

/-- Carrying a model from a stage of the system of affine open neighbourhoods to a smaller
stage: the comparison between the iterated base change and the direct one, taken at the cone's
own compatibility equation. -/
noncomputable def shrinkModelIso {x : S} {W W' : AffineOpenNhds S x} (e : W ⟶ W')
    (Z : Over (Scheme.Opens.toScheme (X := S) W'.obj.1)) :
    (Over.pullback ((specStalkCone S x).π.app W)).obj
        ((Over.pullback ((affineOpenNhdsDiagram S x).map e)).obj Z) ≅
      (Over.pullback ((specStalkCone S x).π.app W')).obj Z :=
  overPullbackCompIso ((affineOpenNhdsDiagram S x).map e) ((specStalkCone S x).π.app W)
    ((specStalkCone S x).π.app W') ((specStalkCone S x).w e) Z

/-- A model over some stage `W₁` of the system of affine open neighbourhoods of `x` is carried
along every map `W ⟶ W₁` by base change. -/
private theorem exists_model_of_hom (x : S) (B : Over (Spec (S.presheaf.stalk x)))
    (hB : FinitePresentation B.hom) :
    ∃ W₁ : AffineOpenNhds S x, ∀ W : AffineOpenNhds S x, (W ⟶ W₁) →
      ∃ Z : Over (Scheme.Opens.toScheme (X := S) W.obj.1), FinitePresentation Z.hom ∧
        Nonempty (B ≅ (Over.pullback
          (Scheme.Opens.fromSpecStalkOfMem (X := S) W.obj.1 x W.obj.2)).obj Z) := by
  obtain ⟨W₁, Z₁, hZ₁, ⟨β₁⟩⟩ := LimitFPObjectDescent.exists_model_of_finitePresentation
    (affineOpenNhdsDiagram S x) (specStalkCone S x) (isLimitSpecStalkCone S x) B hB
  exact ⟨W₁, fun W e => ⟨(Over.pullback ((affineOpenNhdsDiagram S x).map e)).obj Z₁,
    LimitFPObjectDescent.finitePresentation_overPullback _ _ hZ₁,
    ⟨β₁ ≪≫ (shrinkModelIso e Z₁).symm⟩⟩⟩

include hs in
/-- **A scheme of finite presentation over `Spec 𝒪_{S, s i}` has a model over an affine open
neighbourhood of `s i` avoiding every other point of the family.**  This is the form the gluing
step of Tag 0BPA consumes: the chart it glues onto the open complement is this `W`, and the
avoidance is what makes the two charts cover
`AlgebraicGeometry.complementOfOtherClosedPoints`.

Tag 01ZM part (1) produces a model over some neighbourhood; the shrinking lemma then replaces it
by one avoiding the other points, and the model is carried along by base change. -/
theorem exists_affineOpenNhds_model_avoiding (hinj : Function.Injective s) (i : I)
    (B : Over (Spec (S.presheaf.stalk (s i)))) (hB : FinitePresentation B.hom) :
    ∃ (W : AffineOpenNhds S (s i)) (Z : Over (Scheme.Opens.toScheme (X := S) W.obj.1)),
      (∀ j, j ≠ i → s j ∉ W.obj.1) ∧ FinitePresentation Z.hom ∧
        Nonempty (B ≅ (Over.pullback
          (Scheme.Opens.fromSpecStalkOfMem (X := S) W.obj.1 (s i) W.obj.2)).obj Z) := by
  obtain ⟨W₁, hW₁⟩ := exists_model_of_hom (s i) B hB
  obtain ⟨W, hleW₁, havoid⟩ := exists_affineOpenNhds_le_avoiding s hs hinj i W₁
  obtain ⟨Z, hZ, hBZ⟩ := hW₁ W (ObjectProperty.homMk (homOfLE hleW₁))
  exact ⟨W, Z, havoid, hZ, hBZ⟩

include hs in
/-- **The same, with the neighbourhood inside a prescribed one.**  The join is free: the system
of affine open neighbourhoods is cofiltered, so a common refinement of the stage the descent
lands on and the prescribed neighbourhood exists unconditionally. -/
theorem exists_affineOpenNhds_model_avoiding_le (hinj : Function.Injective s) (i : I)
    (W₀ : AffineOpenNhds S (s i)) (B : Over (Spec (S.presheaf.stalk (s i))))
    (hB : FinitePresentation B.hom) :
    ∃ (W : AffineOpenNhds S (s i)) (Z : Over (Scheme.Opens.toScheme (X := S) W.obj.1)),
      W.obj.1 ≤ W₀.obj.1 ∧ (∀ j, j ≠ i → s j ∉ W.obj.1) ∧ FinitePresentation Z.hom ∧
        Nonempty (B ≅ (Over.pullback
          (Scheme.Opens.fromSpecStalkOfMem (X := S) W.obj.1 (s i) W.obj.2)).obj Z) := by
  obtain ⟨W₁, hW₁⟩ := exists_model_of_hom (s i) B hB
  obtain ⟨W, hleW₁, havoid⟩ := exists_affineOpenNhds_le_avoiding s hs hinj i
    (IsCofiltered.min W₁ W₀)
  obtain ⟨Z, hZ, hBZ⟩ := hW₁ W
    ((ObjectProperty.homMk (homOfLE hleW₁) : W ⟶ IsCofiltered.min W₁ W₀) ≫
      IsCofiltered.minToLeft W₁ W₀)
  exact ⟨W, Z,
    le_trans hleW₁ (leOfHom ((affineOpenNhds S (s i)).ι.map (IsCofiltered.minToRight W₁ W₀))),
    havoid, hZ, hBZ⟩

end AlgebraicGeometry

end
