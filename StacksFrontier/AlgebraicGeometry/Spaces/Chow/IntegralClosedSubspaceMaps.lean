module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Cycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Decency

/-!
# Integral closed subspaces under immersions

An irreducible closed set of points of a decent algebraic space `X` over `S` carries a unique
reduced closed subspace structure, and that subspace is integral; this gives the integral
closed subspace of `X` attached to an irreducible closed set of points, as data rather than as
a witness to the surjectivity statement of Stacks 0ENF.

Two maps between integral closed subspaces are built from it. Along a closed immersion
`i : Y ⟶ X` an integral closed subspace of `Y` is carried to the integral closed subspace of
`X` on its image, which is again irreducible and closed. Along an arbitrary morphism
`j : U ⟶ X` an integral closed subspace of `U` is carried to the integral closed subspace of
`X` on the closure of its image. Both preserve the δ-dimension of Stacks 0EDX, because the
generic point is carried to a generic point and the dimension function of Situation 0EDT does
not see an immersion.

## Main definitions

* `AlgebraicGeometry.Space.integralClosedSubspaceOfPoints`: the integral closed subspace on an
  irreducible closed set of points.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.pushforward`: the image of an integral closed
  subspace along a closed immersion.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.closureImage`: the closure of the image of an
  integral closed subspace along a morphism.

## Main results

* `AlgebraicGeometry.Space.subspacePointSet_integralClosedSubspaceOfPoints` and
  `AlgebraicGeometry.Space.eq_integralClosedSubspaceOfPoints`: the point set of the subspace is
  the given set, and the subspace is the only integral closed subspace with that point set.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.subspacePointSet_pushforward`,
  `AlgebraicGeometry.Space.IntegralClosedSubspace.injective_pushforward`,
  `AlgebraicGeometry.Space.IntegralClosedSubspace.deltaDimension_pushforward` and
  `AlgebraicGeometry.Space.IntegralClosedSubspace.exists_pushforward_eq`: the effect on point
  sets, injectivity, invariance of the δ-dimension, and that every integral closed subspace
  supported inside the image arises this way.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.subspacePointSet_closureImage`,
  `AlgebraicGeometry.Space.IntegralClosedSubspace.injective_closureImage` and
  `AlgebraicGeometry.Space.IntegralClosedSubspace.deltaDimension_closureImage`: the same for the
  second map.

## Implementation notes

The construction of the subspace is that of the surjectivity half of Stacks 0ENF: the reduced
closed subspace of Stacks 03IQ on the given set of points, reduced and closed by Stacks 03IQ
itself, decent by Stacks 03KF because its inclusion is representable, and with irreducible
point space because the Stacks 0ABJ embedding makes that space homeomorphic to the given
irreducible set. Decency of the ambient space is the only hypothesis that is not automatic, and
for a good algebraic space over the base of Situation 0EDT it is
`AlgebraicGeometry.Space.BaseSpaceDimensionSituation.isDecentSpace_of_isGood`.

Uniqueness, `AlgebraicGeometry.Space.eq_integralClosedSubspaceOfPoints`, is
`AlgebraicGeometry.Space.injective_integralClosedSubspaceSupport` and needs no decency; it is
what makes both maps below injective, since each is described by its effect on point sets.

The two maps are not stated with the same hypotheses on the morphism because they need
different amounts of it: the image of a closed set under a closed immersion is closed, so no
closure is needed there, whereas for the second map the morphism is arbitrary and the closure
is taken. Injectivity of the second needs the morphism to be an immersion, so that a closed
subset of the source is recovered from the closure of its image by intersecting with the
image.

## References

* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03KF](https://stacks.math.columbia.edu/tag/03KF)
* [Stacks Project, Tag 0ABJ](https://stacks.math.columbia.edu/tag/0ABJ)
* [Stacks Project, Tag 0EDX](https://stacks.math.columbia.edu/tag/0EDX)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section OfPoints

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The integral closed subspace of a decent algebraic space over `S` supported on an
irreducible closed set of points: the reduced closed subspace of Stacks 03IQ on that set. -/
noncomputable def integralClosedSubspaceOfPoints (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X) (T : IrreducibleCloseds (points B S hS X)) :
    IntegralClosedSubspace B S hS X where
  subspace := reducedClosedSubspace B S hS X hX (T : Set (points B S hS X)) T.isClosed
  isClosedSubspace :=
    isClosedSubspace_reducedClosedSubspace B S hS X hX (T : Set (points B S hS X)) T.isClosed
  isIntegralSpace := by
    have hcl := isClosedSubspace_reducedClosedSubspace B S hS X hX
      (T : Set (points B S hS X)) T.isClosed
    have hpts := range_pointsMap_ι_reducedClosedSubspace B S hS X hX
      (T : Set (points B S hS X)) T.isClosed
    refine ⟨hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X hX
        (T : Set (points B S hS X)) T.isClosed,
      isDecentSpace_of_relativelyRepresentable B S hS hcl.1 _ hcl.2.1 hXdec, ?_⟩
    exact ((isEmbedding_pointsMap_of_isImmersion B S hS hX _
        (isImmersion_of_isClosedImmersion B S hS hcl.2)).toHomeomorph.trans
      (Homeomorph.setCongr hpts)).irreducibleSpace_iff.2 (Subtype.irreducibleSpace T.isIrreducible)

/-- The point set of the integral closed subspace attached to an irreducible closed set of
points is that set. -/
@[simp]
theorem subspacePointSet_integralClosedSubspaceOfPoints (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X) (T : IrreducibleCloseds (points B S hS X)) :
    subspacePointSet B S hS X (integralClosedSubspaceOfPoints B S hS hX hXdec T).subspace =
      (T : Set (points B S hS X)) :=
  range_pointsMap_ι_reducedClosedSubspace B S hS X hX (T : Set (points B S hS X)) T.isClosed

/-- An integral closed subspace is determined by its set of points: it is the subspace attached
to that set. -/
theorem eq_integralClosedSubspaceOfPoints (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X) (Z : IntegralClosedSubspace B S hS X)
    (T : IrreducibleCloseds (points B S hS X))
    (hT : subspacePointSet B S hS X Z.subspace = (T : Set (points B S hS X))) :
    Z = integralClosedSubspaceOfPoints B S hS hX hXdec T :=
  injective_integralClosedSubspaceSupport B S hS hX
    (IrreducibleCloseds.ext
      (hT.trans (subspacePointSet_integralClosedSubspaceOfPoints B S hS hX hXdec T).symm))

end OfPoints

section Pushforward

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The map on points of a closed immersion into an algebraic space over `S` is a closed
embedding: it is an embedding by Stacks 0ABJ and its image is closed by Stacks 04CD. -/
theorem isClosedEmbedding_pointsMap_of_isClosedImmersion (hX : IsAlgebraicSpace B S hS X)
    {i : Y ⟶ X} (hi : IsClosedImmersion B S hS i) :
    Topology.IsClosedEmbedding (pointsMap B S hS Y i) :=
  ⟨isEmbedding_pointsMap_of_isImmersion B S hS hX i
      (isImmersion_of_isClosedImmersion B S hS hi),
    isClosed_range_pointsMap_of_isClosedImmersion B S hS hX i hi⟩

/-- The image of the point set of an integral closed subspace of `Y` under a closed immersion
`i : Y ⟶ X` is an irreducible closed subset of `|X|`. -/
noncomputable def IntegralClosedSubspace.imagePoints (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {i : Y ⟶ X} (hi : IsClosedImmersion B S hS i)
    (Z : IntegralClosedSubspace B S hS Y) :
    IrreducibleCloseds (points B S hS X) where
  carrier := pointsMap B S hS Y i '' subspacePointSet B S hS Y Z.subspace
  isIrreducible' :=
    (isIrreducible_range_pointsMap_integralClosedSubspace B S hS Z).image _
      (continuous_pointsMap B S hS i).continuousOn
  isClosed' := (isClosedEmbedding_pointsMap_of_isClosedImmersion B S hS hX hi).isClosedMap _
    (isClosed_range_pointsMap_integralClosedSubspace B S hS hY Z)

/-- The image of an integral closed subspace of `Y` along a closed immersion `i : Y ⟶ X`, as an
integral closed subspace of `X`. -/
noncomputable def IntegralClosedSubspace.pushforward (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X) {i : Y ⟶ X}
    (hi : IsClosedImmersion B S hS i) (Z : IntegralClosedSubspace B S hS Y) :
    IntegralClosedSubspace B S hS X :=
  integralClosedSubspaceOfPoints B S hS hX hXdec
    (IntegralClosedSubspace.imagePoints B S hS hX hY hi Z)

/-- The point set of the image of an integral closed subspace along a closed immersion is the
image of its point set. -/
@[simp]
theorem IntegralClosedSubspace.subspacePointSet_pushforward (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X) {i : Y ⟶ X}
    (hi : IsClosedImmersion B S hS i) (Z : IntegralClosedSubspace B S hS Y) :
    subspacePointSet B S hS X
        (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi Z).subspace =
      pointsMap B S hS Y i '' subspacePointSet B S hS Y Z.subspace :=
  subspacePointSet_integralClosedSubspaceOfPoints B S hS hX hXdec _

/-- Taking the image along a closed immersion is injective on integral closed subspaces: the
map on points is injective, and an integral closed subspace is determined by its point set. -/
theorem IntegralClosedSubspace.injective_pushforward (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X) {i : Y ⟶ X}
    (hi : IsClosedImmersion B S hS i) :
    Function.Injective (IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi) := by
  intro Z W h
  have hinj := (isClosedEmbedding_pointsMap_of_isClosedImmersion B S hS hX hi).injective
  have key : pointsMap B S hS Y i '' subspacePointSet B S hS Y Z.subspace =
      pointsMap B S hS Y i '' subspacePointSet B S hS Y W.subspace := by
    rw [← IntegralClosedSubspace.subspacePointSet_pushforward B S hS hX hY hXdec hi Z,
      ← IntegralClosedSubspace.subspacePointSet_pushforward B S hS hX hY hXdec hi W, h]
  exact injective_integralClosedSubspaceSupport B S hS hY
    (IrreducibleCloseds.ext (hinj.image_injective key))

/-- An integral closed subspace of `X` whose point set lies in the image of a closed immersion
`i : Y ⟶ X` is the image of an integral closed subspace of `Y`.

Its point set pulls back to an irreducible closed subset of `|Y|`: closedness is continuity, and
irreducibility holds because the map on points is an embedding, so an open subset of `|Y|` is
the inverse image of an open subset of `|X|`. -/
theorem IntegralClosedSubspace.exists_pushforward_eq (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X)
    (hYdec : IsDecentSpace B S hS Y) {i : Y ⟶ X} (hi : IsClosedImmersion B S hS i)
    (W : IntegralClosedSubspace B S hS X)
    (hW : subspacePointSet B S hS X W.subspace ⊆ Set.range (pointsMap B S hS Y i)) :
    ∃ Z : IntegralClosedSubspace B S hS Y,
      IntegralClosedSubspace.pushforward B S hS hX hY hXdec hi Z = W := by
  have hemb := isClosedEmbedding_pointsMap_of_isClosedImmersion B S hS hX hi
  have hWirr := isIrreducible_range_pointsMap_integralClosedSubspace B S hS W
  have himg : pointsMap B S hS Y i ''
      (pointsMap B S hS Y i ⁻¹' subspacePointSet B S hS X W.subspace) =
      subspacePointSet B S hS X W.subspace := Set.image_preimage_eq_of_subset hW
  have hirr : IsIrreducible
      (pointsMap B S hS Y i ⁻¹' subspacePointSet B S hS X W.subspace) := by
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := hWirr.1
      obtain ⟨y, hy⟩ := hW hx
      exact ⟨y, by rw [Set.mem_preimage, hy]; exact hx⟩
    · intro V₁ V₂ hV₁ hV₂ ⟨y₁, hy₁T, hy₁V⟩ ⟨y₂, hy₂T, hy₂V⟩
      obtain ⟨O₁, hO₁, hO₁eq⟩ := hemb.isInducing.isOpen_iff.1 hV₁
      obtain ⟨O₂, hO₂, hO₂eq⟩ := hemb.isInducing.isOpen_iff.1 hV₂
      obtain ⟨x, hxT, hxO₁, hxO₂⟩ := hWirr.2 O₁ O₂ hO₁ hO₂
        ⟨pointsMap B S hS Y i y₁, hy₁T, by rw [← hO₁eq] at hy₁V; exact hy₁V⟩
        ⟨pointsMap B S hS Y i y₂, hy₂T, by rw [← hO₂eq] at hy₂V; exact hy₂V⟩
      obtain ⟨y, rfl⟩ := hW hxT
      refine ⟨y, hxT, ?_, ?_⟩
      · rw [← hO₁eq]; exact hxO₁
      · rw [← hO₂eq]; exact hxO₂
  set T : IrreducibleCloseds (points B S hS Y) :=
    ⟨pointsMap B S hS Y i ⁻¹' subspacePointSet B S hS X W.subspace, hirr,
      (isClosed_range_pointsMap_integralClosedSubspace B S hS hX W).preimage
        (continuous_pointsMap B S hS i)⟩ with hTdef
  have hZpts : subspacePointSet B S hS Y
      (integralClosedSubspaceOfPoints B S hS hY hYdec T).subspace =
      (T : Set (points B S hS Y)) :=
    subspacePointSet_integralClosedSubspaceOfPoints B S hS hY hYdec T
  refine ⟨integralClosedSubspaceOfPoints B S hS hY hYdec T, ?_⟩
  refine (eq_integralClosedSubspaceOfPoints B S hS hX hXdec W _ ?_).symm
  have hgoal : subspacePointSet B S hS X W.subspace = pointsMap B S hS Y i ''
      subspacePointSet B S hS Y
        (integralClosedSubspaceOfPoints B S hS hY hYdec T).subspace := by
    rw [hZpts]
    exact himg.symm
  exact hgoal

end Pushforward

section ClosureImage

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The closure of the image of the point set of an integral closed subspace of `U` under a
morphism `j : U ⟶ X`, as an irreducible closed subset of `|X|`. -/
noncomputable def IntegralClosedSubspace.closurePoints (j : U ⟶ X)
    (W : IntegralClosedSubspace B S hS U) : IrreducibleCloseds (points B S hS X) where
  carrier := closure (pointsMap B S hS U j '' subspacePointSet B S hS U W.subspace)
  isIrreducible' :=
    ((isIrreducible_range_pointsMap_integralClosedSubspace B S hS W).image _
      (continuous_pointsMap B S hS j).continuousOn).closure
  isClosed' := isClosed_closure

/-- The closure of the image of an integral closed subspace of `U` along a morphism
`j : U ⟶ X`, as an integral closed subspace of `X`. -/
noncomputable def IntegralClosedSubspace.closureImage (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X) (j : U ⟶ X) (W : IntegralClosedSubspace B S hS U) :
    IntegralClosedSubspace B S hS X :=
  integralClosedSubspaceOfPoints B S hS hX hXdec
    (IntegralClosedSubspace.closurePoints B S hS j W)

/-- The point set of the closure of the image of an integral closed subspace is the closure of
the image of its point set. -/
@[simp]
theorem IntegralClosedSubspace.subspacePointSet_closureImage (hX : IsAlgebraicSpace B S hS X)
    (hXdec : IsDecentSpace B S hS X) (j : U ⟶ X) (W : IntegralClosedSubspace B S hS U) :
    subspacePointSet B S hS X
        (IntegralClosedSubspace.closureImage B S hS hX hXdec j W).subspace =
      closure (pointsMap B S hS U j '' subspacePointSet B S hS U W.subspace) :=
  subspacePointSet_integralClosedSubspaceOfPoints B S hS hX hXdec _

/-- The point set of an integral closed subspace of `U` is recovered from the closure of its
image along an immersion `j : U ⟶ X` by intersecting with the image of `|U|`: the map on points
is inducing, so the closure of a set of `|U|` is the inverse image of the closure of its
image. -/
theorem IntegralClosedSubspace.image_subspacePointSet_eq_inter
    (hX : IsAlgebraicSpace B S hS X) (hU : IsAlgebraicSpace B S hS U) {j : U ⟶ X}
    (hj : IsImmersion B S hS j) (W : IntegralClosedSubspace B S hS U) :
    closure (pointsMap B S hS U j '' subspacePointSet B S hS U W.subspace) ∩
        Set.range (pointsMap B S hS U j) =
      pointsMap B S hS U j '' subspacePointSet B S hS U W.subspace := by
  have hind := (isEmbedding_pointsMap_of_isImmersion B S hS hX j hj).isInducing
  have hcl : IsClosed (subspacePointSet B S hS U W.subspace) :=
    isClosed_range_pointsMap_integralClosedSubspace B S hS hU W
  have h : subspacePointSet B S hS U W.subspace = pointsMap B S hS U j ⁻¹'
      closure (pointsMap B S hS U j '' subspacePointSet B S hS U W.subspace) := by
    rw [← hind.closure_eq_preimage_closure_image, hcl.closure_eq]
  rw [← Set.image_preimage_eq_inter_range, ← h]

end ClosureImage

section DeltaDimension

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- An integral closed subspace of `X` whose point set is the closure of the image of the point
set of an integral closed subspace `W` of `U` under an immersion `j : U ⟶ X` has the δ-dimension
of `W`. -/
private theorem deltaDimension_eq_of_subspacePointSet_eq_closure_image (sX : X ⟶ D.space)
    (hsX : IsLocallyOfFiniteType D.site D.base D.base_mem sX)
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hU : IsAlgebraicSpace D.site D.base D.base_mem U) {j : U ⟶ X}
    (hj : IsImmersion D.site D.base D.base_mem j)
    (W : IntegralClosedSubspace D.site D.base D.base_mem U)
    (V : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hV : subspacePointSet D.site D.base D.base_mem X V.subspace =
      closure (pointsMap D.site D.base D.base_mem U j ''
        subspacePointSet D.site D.base D.base_mem U W.subspace)) :
    deltaDimension D sX V = deltaDimension D (j ≫ sX) W := by
  have hgen := isGenericPoint_pointsMap_genericPoint D.site D.base D.base_mem hU W
  have hgenX : IsGenericPoint
      (pointsMap D.site D.base D.base_mem U j
        (pointsMap D.site D.base D.base_mem W.subspace.toFunctor W.subspace.ι
          (W.genericPoint D.site D.base D.base_mem)))
      (subspacePointSet D.site D.base D.base_mem X V.subspace) := by
    rw [hV, IsGenericPoint, ← hgen, closure_image_closure
      (continuous_pointsMap D.site D.base D.base_mem j), Set.image_singleton]
  rw [deltaDimension_eq_of_isGenericPoint D sX hX _ _ hgenX]
  exact (D.deltaValue_comp_of_isLocallyQuasiFinite hU hX j sX
    (isLocallyQuasiFinite_of_isImmersion D.site D.base D.base_mem j hj) hsX _).symm

/-- The δ-dimension of the image of an integral closed subspace along a closed immersion over
the base is its δ-dimension: the inclusion carries the generic point to a generic point, and the
dimension function of Situation 0EDT does not see an immersion. -/
theorem IntegralClosedSubspace.deltaDimension_pushforward (sX : X ⟶ D.space)
    (hsX : IsLocallyOfFiniteType D.site D.base D.base_mem sX)
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X) {i : Y ⟶ X}
    (hi : IsClosedImmersion D.site D.base D.base_mem i)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    deltaDimension D sX
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX hY hXdec hi Z) =
      deltaDimension D (i ≫ sX) Z :=
  deltaDimension_eq_of_subspacePointSet_eq_closure_image D sX hsX hX hY
    (isImmersion_of_isClosedImmersion D.site D.base D.base_mem hi) Z _
    (by
      rw [IntegralClosedSubspace.subspacePointSet_pushforward D.site D.base D.base_mem hX hY
        hXdec hi Z]
      exact ((isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX
        hi).isClosedMap _ (isClosed_range_pointsMap_integralClosedSubspace D.site D.base
          D.base_mem hY Z)).closure_eq.symm)

/-- The δ-dimension of the closure of the image of an integral closed subspace along an
immersion over the base is its δ-dimension: the closure of the image of the point set is the
closure of the image of the generic point, and the dimension function of Situation 0EDT does not
see an immersion. -/
theorem IntegralClosedSubspace.deltaDimension_closureImage (sX : X ⟶ D.space)
    (hsX : IsLocallyOfFiniteType D.site D.base D.base_mem sX)
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hU : IsAlgebraicSpace D.site D.base D.base_mem U)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X) {j : U ⟶ X}
    (hj : IsImmersion D.site D.base D.base_mem j)
    (W : IntegralClosedSubspace D.site D.base D.base_mem U) :
    deltaDimension D sX
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX hXdec j W) =
      deltaDimension D (j ≫ sX) W :=
  deltaDimension_eq_of_subspacePointSet_eq_closure_image D sX hsX hX hU hj W _
    (IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem hX hXdec j W)

/-- Taking the closure of the image along an immersion is injective on integral closed
subspaces: the point set is recovered from the closure of its image, and an integral closed
subspace is determined by its point set. -/
theorem IntegralClosedSubspace.injective_closureImage
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hU : IsAlgebraicSpace D.site D.base D.base_mem U)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X) {j : U ⟶ X}
    (hj : IsImmersion D.site D.base D.base_mem j) :
    Function.Injective
      (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX hXdec j) := by
  intro W₁ W₂ h
  have hinj := (isEmbedding_pointsMap_of_isImmersion D.site D.base D.base_mem hX j hj).injective
  have hcl : closure (pointsMap D.site D.base D.base_mem U j ''
        subspacePointSet D.site D.base D.base_mem U W₁.subspace) =
      closure (pointsMap D.site D.base D.base_mem U j ''
        subspacePointSet D.site D.base D.base_mem U W₂.subspace) := by
    rw [← IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem hX hXdec
        j W₁,
      ← IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem hX hXdec
        j W₂, h]
  have key : pointsMap D.site D.base D.base_mem U j ''
        subspacePointSet D.site D.base D.base_mem U W₁.subspace =
      pointsMap D.site D.base D.base_mem U j ''
        subspacePointSet D.site D.base D.base_mem U W₂.subspace := by
    rw [← IntegralClosedSubspace.image_subspacePointSet_eq_inter D.site D.base D.base_mem hX hU
        hj W₁,
      ← IntegralClosedSubspace.image_subspacePointSet_eq_inter D.site D.base D.base_mem hX hU
        hj W₂, hcl]
  exact injective_integralClosedSubspaceSupport D.site D.base D.base_mem hU
    (IrreducibleCloseds.ext (hinj.image_injective key))

end DeltaDimension

end AlgebraicGeometry.Space

end
