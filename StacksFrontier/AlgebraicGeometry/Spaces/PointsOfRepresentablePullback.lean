module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented

/-!
# The points of a fibre product of representable presheaves

For two morphisms `f : U₁ ⟶ U₃` and `g : U₂ ⟶ U₃` of the big fppf site of `S`, the fibre
product of the represented presheaves is again represented, by the fibre product taken in the
site, whose underlying scheme is the fibre product of the underlying schemes. Consequently the
point space of `yoneda.obj U₁ ×_{yoneda.obj U₃} yoneda.obj U₂` is homeomorphic to the scheme
`U₁ ×_{U₃} U₂`, compatibly with both projections.

## Main definitions

* `AlgebraicGeometry.Space.pullbackPointsHomeomorph`: the homeomorphism from the points of the
  presheaf fibre product to the scheme fibre product.

## Main results

* `AlgebraicGeometry.Space.pointsToScheme_pointsMap_pullback_fst` and
  `AlgebraicGeometry.Space.pointsToScheme_pointsMap_pullback_snd`: the homeomorphism commutes
  with the two projections.
* `AlgebraicGeometry.Space.isClosed_points_pullback_iff`: a subset of the points of the
  presheaf fibre product is closed exactly when its image in the scheme fibre product is.
* `AlgebraicGeometry.Space.notMem_image_pointsMap_pullback_snd_iff`: a point of `U₂` misses the
  image of a subset under the second projection on points exactly when the corresponding scheme
  point misses the image of the transported subset.

## Implementation notes

Both comparison isomorphisms are Mathlib's `CategoryTheory.Limits.PreservesPullback.iso`: for
`yoneda`, which preserves all limits, and for `AlgebraicGeometry.BigFppfOver.toScheme`, which
preserves fibre products because it is a composite of `CategoryTheory.Over.forget` with the
inclusion of a full subcategory closed under them. The homeomorphism is the composite of these
with `AlgebraicGeometry.Space.schemePointsHomeomorph`.

`AlgebraicGeometry.Space.pointTopology` is a plain definition rather than an instance, so it is
made a local instance here.

## References

* [Stacks Project, Tag 03BV](https://stacks.math.columbia.edu/tag/03BV)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {U₁ U₂ U₃ : BigFppfOver B S hS}

/-- The points of the fibre product of two represented presheaves on the big fppf site of `S`,
with the point topology, are homeomorphic to the fibre product of the underlying schemes. -/
noncomputable def pullbackPointsHomeomorph (f : U₁ ⟶ U₃) (g : U₂ ⟶ U₃) :
    points B S hS (pullback (yoneda.map f) (yoneda.map g)) ≃ₜ
      (pullback ((BigFppfOver.toScheme B S hS).map f)
        ((BigFppfOver.toScheme B S hS).map g) : Scheme.{u}) :=
  ((pointsHomeomorphOfIso B S hS (PreservesPullback.iso yoneda f g)).symm.trans
    (schemePointsHomeomorph B S hS (pullback f g))).trans
      (Scheme.homeoOfIso (PreservesPullback.iso (BigFppfOver.toScheme B S hS) f g))

/-- `AlgebraicGeometry.Space.pullbackPointsHomeomorph` sends a point to the image under the
scheme comparison isomorphism of the scheme point of its transport to `pullback f g`. -/
theorem pullbackPointsHomeomorph_apply (f : U₁ ⟶ U₃) (g : U₂ ⟶ U₃)
    (x : points B S hS (pullback (yoneda.map f) (yoneda.map g))) :
    pullbackPointsHomeomorph B S hS f g x =
      (PreservesPullback.iso (BigFppfOver.toScheme B S hS) f g).hom
        (pointsToScheme B S hS (pullback f g)
          (pointsMap B S hS _ (PreservesPullback.iso yoneda f g).inv x)) :=
  rfl

/-- The homeomorphism of `AlgebraicGeometry.Space.pullbackPointsHomeomorph` commutes with the
first projection. -/
theorem pointsToScheme_pointsMap_pullback_fst (f : U₁ ⟶ U₃) (g : U₂ ⟶ U₃)
    (x : points B S hS (pullback (yoneda.map f) (yoneda.map g))) :
    pointsToScheme B S hS U₁
        (pointsMap B S hS _ (pullback.fst (yoneda.map f) (yoneda.map g)) x) =
      pullback.fst ((BigFppfOver.toScheme B S hS).map f)
        ((BigFppfOver.toScheme B S hS).map g) (pullbackPointsHomeomorph B S hS f g x) := by
  rw [pullbackPointsHomeomorph_apply, ← Scheme.Hom.comp_apply,
    PreservesPullback.iso_hom_fst, ← pointsToScheme_pointsMap_yoneda,
    ← pointsMap_comp_apply, PreservesPullback.iso_inv_fst]

/-- The homeomorphism of `AlgebraicGeometry.Space.pullbackPointsHomeomorph` commutes with the
second projection. -/
theorem pointsToScheme_pointsMap_pullback_snd (f : U₁ ⟶ U₃) (g : U₂ ⟶ U₃)
    (x : points B S hS (pullback (yoneda.map f) (yoneda.map g))) :
    pointsToScheme B S hS U₂
        (pointsMap B S hS _ (pullback.snd (yoneda.map f) (yoneda.map g)) x) =
      pullback.snd ((BigFppfOver.toScheme B S hS).map f)
        ((BigFppfOver.toScheme B S hS).map g) (pullbackPointsHomeomorph B S hS f g x) := by
  rw [pullbackPointsHomeomorph_apply, ← Scheme.Hom.comp_apply,
    PreservesPullback.iso_hom_snd, ← pointsToScheme_pointsMap_yoneda,
    ← pointsMap_comp_apply, PreservesPullback.iso_inv_snd]

/-- A subset of the points of a fibre product of represented presheaves is closed exactly when
its image in the fibre product of the underlying schemes is closed. -/
theorem isClosed_points_pullback_iff (f : U₁ ⟶ U₃) (g : U₂ ⟶ U₃)
    (C : Set (points B S hS (pullback (yoneda.map f) (yoneda.map g)))) :
    IsClosed C ↔ IsClosed (pullbackPointsHomeomorph B S hS f g '' C) :=
  ((pullbackPointsHomeomorph B S hS f g).isClosed_image).symm

/-- Under the comparisons, a point of `U₂` lies outside the image of a subset of the points of
the fibre product under the second projection exactly when the corresponding scheme point lies
outside the image of the transported subset. -/
theorem notMem_image_pointsMap_pullback_snd_iff (f : U₁ ⟶ U₃) (g : U₂ ⟶ U₃)
    (C : Set (points B S hS (pullback (yoneda.map f) (yoneda.map g))))
    (y : points B S hS (yoneda.obj U₂)) :
    y ∉ pointsMap B S hS _ (pullback.snd (yoneda.map f) (yoneda.map g)) '' C ↔
      pointsToScheme B S hS U₂ y ∉
        pullback.snd ((BigFppfOver.toScheme B S hS).map f)
          ((BigFppfOver.toScheme B S hS).map g) '' (pullbackPointsHomeomorph B S hS f g '' C) := by
  refine not_congr ⟨?_, ?_⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨pullbackPointsHomeomorph B S hS f g x, ⟨x, hx, rfl⟩,
      (pointsToScheme_pointsMap_pullback_snd B S hS f g x).symm⟩
  · rintro ⟨w, ⟨x, hx, rfl⟩, hxy⟩
    refine ⟨x, hx, (injective_pointsToScheme B S hS U₂) ?_⟩
    rw [pointsToScheme_pointsMap_pullback_snd, hxy]

end AlgebraicGeometry.Space

end
