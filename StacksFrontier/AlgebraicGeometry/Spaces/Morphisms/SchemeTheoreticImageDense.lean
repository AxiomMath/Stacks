module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImagePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# The support of the scheme-theoretic image

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`. The scheme-theoretic image of Stacks 082X is a closed subspace of `Y` through which
`f` factors, so its set of points contains the closure `T` of the image of the point map of
`f`; that inclusion is unconditional. Equality is the assertion that the scheme-theoretic image
has no superfluous component, and it holds as soon as the scheme-theoretic image commutes with
étale base change of the target, which is the content of Stacks 082Z.

The complement of `T` is open, hence carries an open subspace `W` of `Y` with exactly that set
of points by Stacks 03BZ, and the inclusion of an open subspace is étale. The fibre product
`X ×_Y W` has no points at all: a point of it is a point of `X` and a point of `W` with a
common image in `Y`, while the image of the point map of `f` lies in `T`. A morphism whose
source has no points has the empty closed subspace of `Y` as scheme-theoretic image, so
compatibility with the base change along the inclusion of `W` forces the inverse image of the
scheme-theoretic image of `f` along that inclusion to have no points either. By Stacks 03H4
that inverse image has as point set the preimage of the point set of the scheme-theoretic
image, so the latter misses the complement of `T`.

## Main results

* `AlgebraicGeometry.Space.range_pointsMap_ι_schemeTheoreticImage_eq_closure`: the set of
  points of the scheme-theoretic image of a morphism of algebraic spaces is the closure of the
  image of its point map.
* `AlgebraicGeometry.Space.denseRange_pointsMap_toSchemeTheoreticImage`: the factorization of a
  morphism through its scheme-theoretic image is dense on points.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- Pullbacks of presheaves on the big fppf site, supplied directly: instance search for
`HasLimit (cospan f g)` in this functor category times out under Lean v4.35.0. -/
local instance (priority := high) {P Q R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : P ⟶ R)
    (g : Q ⟶ R) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit (self := functorCategoryHasLimitsOfShape) (cospan f g)

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The set of points of the scheme-theoretic image of `f : X ⟶ Y` misses the image of the
point map of a morphism `g : V ⟶ Y` of algebraic spaces whose base change of `f` has no points,
provided the scheme-theoretic image of `f` is compatible with the base change along `g`.

Indeed that compatibility identifies the inverse image along `g` of the scheme-theoretic image
of `f` with the scheme-theoretic image of the base change, which is the empty closed subspace
of `V`; and the point set of an inverse image is the preimage of the point set by Stacks
03H4. -/
private theorem preimage_range_pointsMap_ι_schemeTheoreticImage_eq_empty
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : V ⟶ Y)
    (hV : IsAlgebraicSpace B S hS V)
    (hempty : IsEmpty (points B S hS (pullback f g)))
    (hbc : schemeTheoreticImageSubfunctor B S hS (pullback.snd f g) =
      (schemeTheoreticImageSubfunctor B S hS f).preimage g) :
    pointsMap B S hS V g ⁻¹'
        Set.range (pointsMap B S hS (schemeTheoreticImageSubfunctor B S hS f).toFunctor
          (schemeTheoreticImageSubfunctor B S hS f).ι) = ∅ := by
  have hle : (schemeTheoreticImageSubfunctor B S hS f).preimage g ≤
      (⊥ : Subfunctor V).sheafify (BigFppfOver.topology B S hS) := by
    rw [← hbc]
    exact schemeTheoreticImageSubfunctor_le_sheafify_bot_of_isEmpty_points B S hS
      (pullback.snd f g) hV hempty
  rw [← Set.image_univ (f := pointsMap B S hS
      (schemeTheoreticImageSubfunctor B S hS f).toFunctor
      (schemeTheoreticImageSubfunctor B S hS f).ι),
    preimage_image_pointsMap_of_isPullback B S hS
      (Subfunctor.isPullback_preimage g (schemeTheoreticImageSubfunctor B S hS f)) Set.univ,
    Set.preimage_univ, Set.image_univ]
  exact range_pointsMap_ι_eq_empty_of_le_sheafify_bot B S hS hle

/-- The set of points of the scheme-theoretic image of a morphism of algebraic spaces over `S`
is the closure of the image of its point map, provided the scheme-theoretic image is compatible
with étale base change of the target.

The closure is contained in the point set because the scheme-theoretic image is a closed
subspace through which the morphism factors. Conversely a point of the image outside the
closure lies in the open subspace of Stacks 03BZ cut out by the complement of the closure,
whose fibre product with the morphism has no points; compatibility with the base change along
its étale inclusion then exhibits that point in the empty point set of an inverse image of the
scheme-theoretic image. -/
theorem range_pointsMap_ι_schemeTheoreticImage_eq_closure (f : X ⟶ Y)
    (_hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (h3 : ∀ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (g : V ⟶ Y),
      IsAlgebraicSpace B S hS V → IsEtale B S hS g →
        schemeTheoreticImageSubfunctor B S hS (pullback.snd f g) =
          (schemeTheoreticImageSubfunctor B S hS f).preimage g) :
    Set.range (pointsMap B S hS (schemeTheoreticImageSubfunctor B S hS f).toFunctor
        (schemeTheoreticImageSubfunctor B S hS f).ι) =
      closure (Set.range (pointsMap B S hS X f)) := by
  refine Set.Subset.antisymm ?_
    (closure_range_pointsMap_subset_range_pointsMap_schemeTheoreticImage B S hS f hY)
  -- The open subspace of `Y` on the complement of the closure of the image.
  set W := openSubspaceOfPoints B S hS Y (closure (Set.range (pointsMap B S hS X f)))ᶜ
  have hW : IsOpenSubspace B S hS W :=
    isOpenSubspace_openSubspaceOfPoints B S hS hY
      (closure (Set.range (pointsMap B S hS X f)))ᶜ isClosed_closure.isOpen_compl
  have hWrange : Set.range (pointsMap B S hS W.toFunctor W.ι) =
      (closure (Set.range (pointsMap B S hS X f)))ᶜ :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  -- A point of `X ×_Y W` would give a point of `X` whose image lies both in the closure of the
  -- image of `f` and in its complement.
  have hempty : IsEmpty (points B S hS (pullback f W.ι)) := by
    refine ⟨fun w => ?_⟩
    have hmem : pointsMap B S hS W.toFunctor W.ι
        (pointsMap B S hS (pullback f W.ι) (pullback.snd f W.ι) w) ∈
          (closure (Set.range (pointsMap B S hS X f)))ᶜ := by
      rw [← hWrange]
      exact Set.mem_range_self _
    have hclosure : pointsMap B S hS X f
        (pointsMap B S hS (pullback f W.ι) (pullback.fst f W.ι) w) ∈
          closure (Set.range (pointsMap B S hS X f)) :=
      subset_closure (Set.mem_range_self _)
    rw [pointsMap_apply_comm B S hS (pullback.condition (f := f) (g := W.ι)) w] at hclosure
    exact hmem hclosure
  have hpre := preimage_range_pointsMap_ι_schemeTheoreticImage_eq_empty B S hS f W.ι hW.1 hempty
    (h3 W.toFunctor W.ι hW.1 (isEtale_ι_of_isOpenSubspace hW))
  rw [Set.eq_empty_iff_forall_notMem] at hpre
  intro x hx
  by_contra hxT
  obtain ⟨w, rfl⟩ : x ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) := by
    rw [hWrange]
    exact hxT
  exact hpre w hx

/-- The factorization of a morphism of algebraic spaces over `S` through its scheme-theoretic
image has dense image on points, provided the scheme-theoretic image is compatible with étale
base change of the target.

The inclusion of the scheme-theoretic image is a topological embedding on points by Stacks
0ABJ, so the closure of the image of the factorization is the preimage of the closure of the
image of the morphism, which is the whole point set of the scheme-theoretic image. -/
theorem denseRange_pointsMap_toSchemeTheoreticImage (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (h3 : ∀ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (g : V ⟶ Y),
      IsAlgebraicSpace B S hS V → IsEtale B S hS g →
        schemeTheoreticImageSubfunctor B S hS (pullback.snd f g) =
          (schemeTheoreticImageSubfunctor B S hS f).preimage g) :
    DenseRange (pointsMap B S hS X (toSchemeTheoreticImage B S hS f)) := by
  have hι : Topology.IsEmbedding (pointsMap B S hS
      (schemeTheoreticImageSubfunctor B S hS f).toFunctor
      (schemeTheoreticImageSubfunctor B S hS f).ι) :=
    isEmbedding_pointsMap_of_isImmersion B S hS hY _
      (isImmersion_of_isClosedImmersion B S hS
        (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS f hY).2)
  refine dense_iff_closure_eq.2 ?_
  rw [hι.toIsInducing.closure_eq_preimage_closure_image, ← Set.range_comp, ← pointsMap_comp,
    toSchemeTheoreticImage_ι,
    ← range_pointsMap_ι_schemeTheoreticImage_eq_closure B S hS f hX hY h3, Set.preimage_range]

end AlgebraicGeometry.Space

end
