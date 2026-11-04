module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.DenseRationalPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ContractedPieceRationalPoints

/-!
# Rational points off a closed subset are dense in the point space of a represented space

Let `X` be a presheaf on the big fppf site over an algebraically closed field `K`, represented
by an object `U` of the site. The point space of `X`, with
`AlgebraicGeometry.Space.pointTopology`, is homeomorphic to the underlying space of the scheme
`U`. When `U` is irreducible and locally of finite type over `K`, the closed points of the point
space off a proper closed subset are dense, and every closed point of the point space is the
image of a rational point of `X`.

## Main results

* `AlgebraicGeometry.Space.mem_closedPoints_pointsHomeomorph_iff`: a point of the point space of
  a represented presheaf is closed exactly when the corresponding point of the scheme is.
* `AlgebraicGeometry.Space.dense_setOf_isClosed_singleton_notMem`: in the point space of a
  presheaf represented by an irreducible object of the site locally of finite type over the
  field, the closed points off a proper closed subset are dense.
* `AlgebraicGeometry.Space.exists_rationalPoint_range_pointsMap_eq_singleton`: a closed point of
  such a point space is the whole image on points of a rational point of the presheaf.
* `AlgebraicGeometry.Space.dense_setOf_exists_rationalPoint_notMem`: the points off a proper
  closed subset which are the image of a rational point are dense.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (K : Type u) [Field K] [IsAlgClosed K]
  (hK : B.Contains (Spec (CommRingCat.of K)))

section Represented

variable (U : BigFppfOver B (Spec (CommRingCat.of K)) hK)
  {X : (BigFppfOver B (Spec (CommRingCat.of K)) hK)ᵒᵖ ⥤ Type u} (e : X ≅ yoneda.obj U)

/-- The point space of a presheaf isomorphic to the functor of points of an object of the site
is homeomorphic to the point space of the representing scheme. -/
noncomputable def pointsHomeomorphSchemeOfIso :
    points B (Spec (CommRingCat.of K)) hK X ≃ₜ
      (BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).obj U :=
  (pointsHomeomorphOfIso B (Spec (CommRingCat.of K)) hK e).trans
    (schemePointsHomeomorph B (Spec (CommRingCat.of K)) hK U)

omit [IsAlgClosed K] in
/-- A point of the point space of a represented presheaf is closed exactly when the
corresponding point of the representing scheme is. -/
theorem mem_closedPoints_pointsHomeomorph_iff
    (p : points B (Spec (CommRingCat.of K)) hK X) :
    pointsHomeomorphSchemeOfIso B K hK U e p ∈
        closedPoints ((BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).obj U) ↔
      IsClosed {p} := by
  rw [mem_closedPoints_iff, ← Set.image_singleton]
  exact (pointsHomeomorphSchemeOfIso B K hK U e).isClosed_image

include e in
omit [IsAlgClosed K] in
/-- In the point space of a presheaf represented by an irreducible object of the site locally of
finite type over the field, the closed points off a proper closed subset are dense. -/
theorem dense_setOf_isClosed_singleton_notMem
    (hft : LocallyOfFiniteType (B.inclusion.map U.hom))
    (hirr : PreirreducibleSpace
      ((BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).obj U))
    {Z : Set (points B (Spec (CommRingCat.of K)) hK X)} (hZ : IsClosed Z)
    (hZ' : ∃ p, p ∉ Z) :
    Dense {p : points B (Spec (CommRingCat.of K)) hK X | IsClosed {p} ∧ p ∉ Z} := by
  let := hirr
  have hjac : JacobsonSpace ((BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).obj U) :=
    jacobsonSpace_of_locallyOfFiniteType_over_field (B.inclusion.map U.hom)
  set E := pointsHomeomorphSchemeOfIso B K hK U e with hEdef
  have himg : IsClosed (E '' Z) := E.isClosed_image.2 hZ
  obtain ⟨p₀, hp₀⟩ := hZ'
  have hne : ∃ x, x ∉ E '' Z := ⟨E p₀, fun hx ↦ hp₀ (E.injective.mem_set_image.1 hx)⟩
  exact ((dense_closedPoints_diff himg hne).preimage E.isOpenMap).mono fun p hp ↦
    ⟨(mem_closedPoints_pointsHomeomorph_iff B K hK U e p).1 hp.1, fun hpz ↦ hp.2 ⟨p, hpz, rfl⟩⟩

include e in
/-- A closed point of the point space of a presheaf represented by an object of the site locally
of finite type over an algebraically closed field is the whole image on points of a rational
point of the presheaf. -/
theorem exists_rationalPoint_range_pointsMap_eq_singleton
    (hft : LocallyOfFiniteType (B.inclusion.map U.hom))
    (p : points B (Spec (CommRingCat.of K)) hK X) (hp : IsClosed {p}) :
    ∃ ξ : yoneda.obj (Over.mk (𝟙 (B.obj hK)) :
        BigFppfOver B (Spec (CommRingCat.of K)) hK) ⟶ X,
      p ∈ Set.range (pointsMap B (Spec (CommRingCat.of K)) hK _ ξ) ∧
        Set.range (pointsMap B (Spec (CommRingCat.of K)) hK _ ξ) ⊆ {p} := by
  let := hft
  set E := pointsHomeomorphSchemeOfIso B K hK U e with hEdef
  have hclosed : IsClosed {E p} := by
    rw [← Set.image_singleton]
    exact E.isClosedMap _ hp
  have key : ∀ ζ, pointsMap B (Spec (CommRingCat.of K)) hK _
      (rationalPointOfClosedPoint B K hK U hft (E p) hclosed ≫ e.inv) ζ = p := fun ζ ↦ by
    rw [pointsMap_comp B (Spec (CommRingCat.of K)) hK _
      (rationalPointOfClosedPoint B K hK U hft (E p) hclosed) e.inv, Function.comp_apply,
      pointsMap_rationalPointOfClosedPoint]
    exact E.symm_apply_apply p
  refine ⟨rationalPointOfClosedPoint B K hK U hft (E p) hclosed ≫ e.inv,
    ⟨(schemePointsHomeomorph B (Spec (CommRingCat.of K)) hK
      (Over.mk (𝟙 (B.obj hK)))).symm (IsLocalRing.closedPoint K), key _⟩, ?_⟩
  rintro w ⟨ζ, rfl⟩
  exact key ζ

include e in
/-- The points off a proper closed subset of the point space of a represented space which are the
image of a rational point are dense. -/
theorem dense_setOf_exists_rationalPoint_notMem
    (hft : LocallyOfFiniteType (B.inclusion.map U.hom))
    (hirr : PreirreducibleSpace
      ((BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).obj U))
    {Z : Set (points B (Spec (CommRingCat.of K)) hK X)} (hZ : IsClosed Z)
    (hZ' : ∃ p, p ∉ Z) :
    Dense {p : points B (Spec (CommRingCat.of K)) hK X |
      (∃ ξ : yoneda.obj (Over.mk (𝟙 (B.obj hK)) :
          BigFppfOver B (Spec (CommRingCat.of K)) hK) ⟶ X,
        p ∈ Set.range (pointsMap B (Spec (CommRingCat.of K)) hK _ ξ) ∧
          Set.range (pointsMap B (Spec (CommRingCat.of K)) hK _ ξ) ⊆ {p}) ∧ p ∉ Z} := by
  exact (dense_setOf_isClosed_singleton_notMem B K hK U e hft hirr hZ hZ').mono fun p hp ↦
    ⟨exists_rationalPoint_range_pointsMap_eq_singleton B K hK U e hft p hp.1, hp.2⟩

end Represented

end AlgebraicGeometry.Space

end
