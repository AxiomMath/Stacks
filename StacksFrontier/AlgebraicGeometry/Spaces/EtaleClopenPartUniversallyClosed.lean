module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleClopenPart
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fold5.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedImage

/-!
# The open-and-closed part cut out by an étale morphism is universally closed over the base

`StacksFrontier/AlgebraicGeometry/Spaces/EtaleClopenPart.lean` produces the two pieces
`W ⨿ V` of Stacks 082H from a morphism `z : Z ⟶ P` which is étale onto `P` and finite over
the base `k₁ : P ⟶ Zu`: the piece `V` is the open-and-closed subspace cut out by the image of
`|Z|`, and `W` is the one cut out by its complement. It stops short of the remaining clause of
Stacks 082H, that `V ⟶ Zu` be finite.

This file supplies the *universally closed* half of that clause, unconditionally. The morphism
`z` factors through `V`, surjectively on points, and `z ≫ k₁` is universally closed because it
is finite; so `V.ι ≫ k₁` is universally closed by the first assertion of Stacks 08AJ
(`AlgebraicGeometry.Space.universallyClosed_of_isSurjective`).

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isSurjective_lift_openSubspaceOfPoints_range`: the factorisation of
  a morphism through the open subspace cut out by the image of its points is surjective on
  points.
* `AlgebraicGeometry.Space.universallyClosed_ι_openSubspaceOfPoints_range_comp`: if `z ≫ k` is
  universally closed then so is the composite of `k` with the inclusion of the subspace cut
  out by the image of `|Z|`.
* `AlgebraicGeometry.Space.universallyClosed_ι_openSubspaceOfPoints_range_comp_of_isFinite`:
  the same with the hypothesis in the form Stacks 082H supplies it, finiteness of `z ≫ k`.
* `AlgebraicGeometry.Space.exists_clopen_part_universallyClosed_of_isEtale_of_isFinite`: the
  conclusion of Stacks 082H with its finiteness clause weakened to universal closedness,
  deduced from an étale `z : Z ⟶ P` which is finite over a separated base together with the
  two conditions on the fibre.

## Implementation notes

What is still missing from the conclusion of Stacks 082H is *affineness* of `V ⟶ Zu`, not its
universal closedness. The source obtains finiteness by presenting `V` as the quotient of `Z`
by the étale equivalence relation `Z ×_V Z` and invoking Tag 03BM to see that `V` is an affine
scheme; Tag 03GN then gives properness of `V ⟶ Zu` and Tag 01WN finiteness. Of those three
tags, 03GN is the one this file removes from the critical path: its space-level form is Tag
08AJ, which applies to `V` without knowing that `V` is a scheme, so the universally closed
half of properness needs no affineness at all. Tags 03BM and 01WN remain.

Nothing here carries the tag 082H. The hypotheses are an étale morphism onto `P` which is
finite over the base and two conditions on points; none of them is an existential, and none
contains any part of the conclusion — the finiteness hypothesis is on `z ≫ k₁`, out of `Z`,
while the conclusion speaks of `V.ι ≫ k₁`, out of the image of `Z`. What 082H asserts and this
file does not prove is the *existence* of such a `z` after an étale base change, which is
steps 1 to 5 of the source proof.

## References

* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 03GN](https://stacks.math.columbia.edu/tag/03GN)
* [Stacks Project, Tag 082H](https://stacks.math.columbia.edu/tag/082H)
* [Stacks Project, Tag 08AJ](https://stacks.math.columbia.edu/tag/08AJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The factorisation through the subspace cut out by the image -/

/-- **The factorisation of a morphism through the subspace cut out by the image of its points
is surjective on points.** A morphism `z : Z ⟶ P` of presheaves on the big fppf site of `S`
factors through the subfunctor of `P` cut out by the image of `|Z|`
(`AlgebraicGeometry.Space.range_le_openSubspaceOfPoints_range_pointsMap`), and the resulting
morphism is surjective on points.

The point set of that subfunctor is exactly the image of `|Z|`, so a point of it is the image
of a point of `|Z|`; the inclusion is a monomorphism, hence injective on points, which turns
that equality of images into surjectivity of the factorisation. -/
theorem isSurjective_lift_openSubspaceOfPoints_range
    {Z P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (z : Z ⟶ P) :
    IsSurjective B S hS
      (Subfunctor.lift z (range_le_openSubspaceOfPoints_range_pointsMap z)) := by
  intro v
  have hmem : pointsMap B S hS
      (openSubspaceOfPoints B S hS P (Set.range (pointsMap B S hS Z z))).toFunctor
      (openSubspaceOfPoints B S hS P (Set.range (pointsMap B S hS Z z))).ι v
      ∈ Set.range (pointsMap B S hS Z z) :=
    (range_pointsMap_ι_openSubspaceOfPoints B S hS
      (Set.range (pointsMap B S hS Z z))).le ⟨v, rfl⟩
  obtain ⟨ζ, hζ⟩ := hmem
  refine ⟨ζ, pointsMap_injective_of_mono B S hS
    (openSubspaceOfPoints B S hS P (Set.range (pointsMap B S hS Z z))).ι ?_⟩
  rw [← pointsMap_comp_apply, Subfunctor.lift_ι, hζ]

/-! ### Universal closedness of the piece over the base -/

/-- **The subspace cut out by the image of a morphism is universally closed over the base as
soon as the morphism is.** For `z : Z ⟶ P` and `k : P ⟶ U` morphisms of algebraic spaces over
`S` with `z ≫ k` universally closed, the inclusion of the subspace of `P` cut out by the image
of `|Z|`, composed with `k`, is universally closed.

This is the first assertion of Stacks 08AJ applied to the factorisation of `z` through that
subspace, which is surjective on points by
`AlgebraicGeometry.Space.isSurjective_lift_openSubspaceOfPoints_range`. -/
theorem universallyClosed_ι_openSubspaceOfPoints_range_comp
    {Z P U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) (hU : IsAlgebraicSpace B S hS U)
    (z : Z ⟶ P) (k : P ⟶ U)
    (hV : IsAlgebraicSpace B S hS
      (openSubspaceOfPoints B S hS P (Set.range (pointsMap B S hS Z z))).toFunctor)
    (hzk : UniversallyClosed B S hS (z ≫ k)) :
    UniversallyClosed B S hS
      ((openSubspaceOfPoints B S hS P (Set.range (pointsMap B S hS Z z))).ι ≫ k) :=
  universallyClosed_of_isSurjective B S hS hZ hV hU
    (Subfunctor.lift z (range_le_openSubspaceOfPoints_range_pointsMap z)) (z ≫ k) _
    (by rw [← Category.assoc, Subfunctor.lift_ι])
    (isSurjective_lift_openSubspaceOfPoints_range B S hS z) hzk

/-- **The subspace cut out by the image of a morphism finite over the base is universally
closed over the base.** This is
`AlgebraicGeometry.Space.universallyClosed_ι_openSubspaceOfPoints_range_comp` with the
hypothesis in the form Stacks 082H supplies it: there `z ≫ k` is the morphism `Z₁ ⟶ U` of
step 5, which Tag 02LN produces as a finite morphism.

The finiteness hypothesis is on `z ≫ k`, out of `Z`; the conclusion is about the composite of
`k` with the inclusion of the image of `|Z|`, out of a different object. -/
theorem universallyClosed_ι_openSubspaceOfPoints_range_comp_of_isFinite
    {Z P U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) (hU : IsAlgebraicSpace B S hS U)
    (z : Z ⟶ P) (k : P ⟶ U)
    (hV : IsAlgebraicSpace B S hS
      (openSubspaceOfPoints B S hS P (Set.range (pointsMap B S hS Z z))).toFunctor)
    (hzk : IsFinite B S hS (z ≫ k)) :
    UniversallyClosed B S hS
      ((openSubspaceOfPoints B S hS P (Set.range (pointsMap B S hS Z z))).ι ≫ k) :=
  universallyClosed_ι_openSubspaceOfPoints_range_comp B S hS hZ hU z k hV
    (universallyClosed_of_isFinite B S hS hZ hU hzk)

/-! ### The conclusion of Stacks 082H with finiteness weakened to universal closedness -/

/-- **The conclusion of Stacks 082H with its finiteness clause weakened to universal
closedness.** Let `P` be an algebraic space over `S` with two morphisms `k₁` and `k₂` — in the
application to Stacks 082H the two projections of `U ×_Y X` — let `u` be a point of the target
of `k₁` and `x` finitely many points of the target of `k₂`. Suppose `z : Z ⟶ P` is étale, is
finite over the base through `k₁`, that `k₁` is separated, and that the points of `|Z|` over
`u` account for exactly the points over the `x i`, those of `|P|` outside the image of `|Z|`
accounting for none. Then `P` decomposes into two subfunctors which are open and closed
subspaces, locally cover `P`, are locally disjoint, satisfy the two conditions on the fibre in
the exact shape Stacks 082H states them, and the second of which is universally closed over
the base.

The decomposition is `AlgebraicGeometry.Space.exists_clopen_part_of_isClopen_pointSet` at the
image of `|Z|`, which is open and closed by
`AlgebraicGeometry.Space.isClopen_range_pointsMap_of_isEtale_of_isFinite`; the universal
closedness is
`AlgebraicGeometry.Space.universallyClosed_ι_openSubspaceOfPoints_range_comp_of_isFinite`.

What Stacks 082H asserts and this does not is the existence of such a `z` after an étale base
change of `Y`; see the module documentation. -/
theorem exists_clopen_part_universallyClosed_of_isEtale_of_isFinite
    {Z P Zu Zx : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) (hP : IsAlgebraicSpace B S hS P)
    (hZu : IsAlgebraicSpace B S hS Zu) (k₁ : P ⟶ Zu) (k₂ : P ⟶ Zx)
    (u : points B S hS Zu) {n : ℕ} (x : Fin n → points B S hS Zx)
    (z : Z ⟶ P) (hze : IsEtale B S hS z) (hzf : IsFinite B S hS (z ≫ k₁))
    (hk : IsSeparated B S hS k₁)
    (hVpts : ∀ ζ : points B S hS Z, pointsMap B S hS Z (z ≫ k₁) ζ = u →
      ∃ i, pointsMap B S hS Z (z ≫ k₂) ζ = x i)
    (hWpts : ∀ p : points B S hS P, p ∉ Set.range (pointsMap B S hS Z z) →
      pointsMap B S hS P k₁ p = u → ∀ i, pointsMap B S hS P k₂ p ≠ x i) :
    ∃ (W V : Subfunctor P) (_ : IsOpenSubspace B S hS W)
      (_ : IsOpenSubspace B S hS V),
      IsClosedSubspace B S hS W ∧ IsClosedSubspace B S hS V ∧
      (W ⊔ V).sheafify (BigFppfOver.topology B S hS) = ⊤ ∧
      W ⊓ V = (⊥ : Subfunctor P).sheafify (BigFppfOver.topology B S hS) ∧
      UniversallyClosed B S hS (V.ι ≫ k₁) ∧
      (∀ v : points B S hS V.toFunctor,
        pointsMap B S hS V.toFunctor (V.ι ≫ k₁) v = u →
          ∃ i, pointsMap B S hS V.toFunctor (V.ι ≫ k₂) v = x i) ∧
      (∀ w : points B S hS W.toFunctor,
        pointsMap B S hS W.toFunctor (W.ι ≫ k₁) w = u →
          ∀ i, pointsMap B S hS W.toFunctor (W.ι ≫ k₂) w ≠ x i) := by
  have hclopen : _root_.IsClopen (Set.range (pointsMap B S hS Z z)) :=
    isClopen_range_pointsMap_of_isEtale_of_isFinite B S hS hZ hP hZu z k₁ hze hzf hk
  have hTo : _root_.IsOpen (Set.range (pointsMap B S hS Z z)) := hclopen.2
  have hTc : _root_.IsClosed (Set.range (pointsMap B S hS Z z)) := hclopen.1
  have hVs : IsOpenSubspace B S hS
      (openSubspaceOfPoints B S hS P (Set.range (pointsMap B S hS Z z))) :=
    isOpenSubspace_openSubspaceOfPoints B S hS hP _ hTo
  have hWs : IsOpenSubspace B S hS
      (openSubspaceOfPoints B S hS P (Set.range (pointsMap B S hS Z z))ᶜ) :=
    isOpenSubspace_openSubspaceOfPoints B S hS hP _ hTc.isOpen_compl
  refine ⟨openSubspaceOfPoints B S hS P (Set.range (pointsMap B S hS Z z))ᶜ,
    openSubspaceOfPoints B S hS P (Set.range (pointsMap B S hS Z z)), hWs, hVs,
    isClosedSubspace_openSubspaceOfPoints B S hS hP _ hTc.isOpen_compl hTo.isClosed_compl,
    isClosedSubspace_openSubspaceOfPoints B S hS hP _ hTo hTc,
    sheafify_sup_openSubspaceOfPoints_eq_top B S hS _ hTo hTc,
    inf_openSubspaceOfPoints_eq_sheafify_bot B S hS _,
    universallyClosed_ι_openSubspaceOfPoints_range_comp_of_isFinite B S hS hZ hZu z k₁
      hVs.1 hzf, ?_, ?_⟩
  · intro v hv
    rw [pointsMap_comp_apply] at hv ⊢
    obtain ⟨ζ, hζ⟩ :=
      (range_pointsMap_ι_openSubspaceOfPoints B S hS (Set.range (pointsMap B S hS Z z))).le
        ⟨v, rfl⟩
    rw [← hζ, ← pointsMap_comp_apply] at hv
    obtain ⟨i, hi⟩ := hVpts ζ hv
    exact ⟨i, by rw [← hζ, ← pointsMap_comp_apply]; exact hi⟩
  · intro w hw i
    rw [pointsMap_comp_apply] at hw ⊢
    exact hWpts _
      ((range_pointsMap_ι_openSubspaceOfPoints B S hS (Set.range (pointsMap B S hS Z z))ᶜ).le
        ⟨w, rfl⟩) hw i

end AlgebraicGeometry.Space

end
