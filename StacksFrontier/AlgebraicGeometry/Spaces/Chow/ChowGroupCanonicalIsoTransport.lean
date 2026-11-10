module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrimeDivisorIsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCycleOfGoodIsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardClosedImmersionSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace

/-!
# Pushforward along an isomorphism on the Chow groups at the canonical embeddings

In Situation 0EDT let `e : X ≅ Y` be an isomorphism of good algebraic spaces over the base.
This file descends the pushforward of cycles along `e` to the Chow groups
`AlgebraicGeometry.Space.chowGroupCanonical` of Stacks 0EQ6, that is, it proves that `e_*` carries
cycles rationally equivalent to zero at the canonical embeddings of Stacks 0ENK to cycles
rationally equivalent to zero at the canonical embeddings, and so induces

  `e_* : CH_k(X) ⟶ CH_k(Y)`.

This is the case of **Stacks 0EQC** — proper pushforward factors through rational equivalence —
in which the proper morphism is an isomorphism.  The statement is run on **presentations** rather
than on classes.  A cycle rationally equivalent to zero at the canonical embeddings *is* a
locally finite sum `∑_j (i_j)_* div(f_j)`, and an isomorphism carries that datum to a datum of
the same shape on `Y`: the family `{e(W_j)}` is locally finite because `|X| → |Y|` is a
homeomorphism, δ-dimensions are preserved by
`AlgebraicGeometry.Space.IntegralClosedSubspace.deltaDimension_pushforward`, and each summand is
again a principal divisor at the canonical embeddings by
`AlgebraicGeometry.Space.isPrincipalDivisorCycleOfGood_cycleGroupClosedPushforward_of_iso`.

## Main results

* `AlgebraicGeometry.Space.isIso_of_comp_ι_eq_of_iso`: a morphism from an integral closed
  subspace `W ⊆ X` to an integral closed subspace `W' ⊆ Y` over an isomorphism `e : X ≅ Y`, whose
  point set is the image of that of `W`, is an isomorphism.  This is
  `AlgebraicGeometry.Space.isIso_of_comp_ι_eq_of_subspacePointSet` for an isomorphism of ambient
  spaces in place of the inclusion of a closed subspace.
* `AlgebraicGeometry.Space.cycleGroupClosedPushforward_integralClosedSubspacePushforward_of_iso`:
  pushing a cycle on `W` out to `X` and then along `e` is pushing it along the comparison
  morphism `W ⟶ W'` and then out to `Y`.
* `isRationallyEquivalentToZeroCanonical_cycleGroupClosedPushforward_of_iso`:
  **the descent.**  The pushforward along an isomorphism of good algebraic spaces over the base of
  a cycle rationally equivalent to zero at the canonical embeddings is rationally equivalent to
  zero at the canonical embeddings.
* `AlgebraicGeometry.Space.chowGroupCanonicalPushforwardOfIso`: the induced homomorphism
  `CH_k(X) ⟶ CH_k(Y)`, and
  `AlgebraicGeometry.Space.chowGroupCanonicalPushforwardOfIso_chowClassCanonical`, that it carries
  the class of a cycle to the class of its pushforward.

## Implementation notes

The summand of the transported presentation on the image `W' = e(W)` of a member is the
pushforward of the given summand along the comparison morphism `m : W ⟶ W'`, which exists by
`AlgebraicGeometry.Space.IntegralClosedSubspace.exists_hom_closureImage` — the image along a
closed immersion being the closure of the image,
`AlgebraicGeometry.Space.IntegralClosedSubspace.closureImage_eq_pushforward` — and is an
isomorphism by `AlgebraicGeometry.Space.isIso_of_comp_ι_eq_of_iso`.

The identity of cycles is functoriality: both `e_* ∘ (i_W)_*` and `(i_{W'})_* ∘ m_*` are the
pushforward along a single closed immersion, by
`AlgebraicGeometry.Space.cycleClosedPushforward_comp`, and the two closed immersions are equal
because `m ≫ i_{W'} = i_W ≫ e`.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The comparison morphism to the image of an integral closed subspace -/

section Comparison

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hYdec : IsDecentSpace B S hS Y) (e : X ≅ Y)

/-- The point map of the inverse of an isomorphism undoes the point map of the isomorphism. -/
private theorem pointsMap_inv_pointsMap_hom (a : points B S hS X) :
    pointsMap B S hS Y e.inv (pointsMap B S hS X e.hom a) = a := by
  have h := congrFun (pointsMap_comp B S hS X e.hom e.inv) a
  rw [e.hom_inv_id, pointsMap_id] at h
  exact h.symm

include hX in
/-- **An integral closed subspace is isomorphic to its image under an isomorphism.**  For
`e : X ≅ Y` an isomorphism of algebraic spaces over `S`, `W ⊆ X` and `W' ⊆ Y` integral closed
subspaces with `|W'|` the image of `|W|`, any morphism `m : W ⟶ W'` over `e` is an isomorphism. -/
theorem isIso_of_comp_ι_eq_of_iso (W : IntegralClosedSubspace B S hS X)
    (W' : IntegralClosedSubspace B S hS Y)
    (hpts : subspacePointSet B S hS Y W'.subspace =
      pointsMap B S hS X e.hom '' subspacePointSet B S hS X W.subspace)
    (m : W.subspace.toFunctor ⟶ W'.subspace.toFunctor)
    (hm : m ≫ W'.subspace.ι = W.subspace.ι ≫ e.hom) :
    IsIso m := by
  have hrange : Set.range (pointsMap B S hS W'.subspace.toFunctor
        (W'.subspace.ι ≫ e.inv)) =
      subspacePointSet B S hS X W.subspace := by
    rw [pointsMap_comp, Set.range_comp]
    change pointsMap B S hS Y e.inv '' subspacePointSet B S hS Y W'.subspace = _
    rw [hpts, Set.image_image]
    simp only [pointsMap_inv_pointsMap_hom, Set.image_id']
  obtain ⟨n, hn⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hX
    W'.isClosedSubspace.1 W.subspace W.isClosedSubspace W'.isIntegralSpace.1
    (W'.subspace.ι ≫ e.inv)).2 (by rw [hrange])
  refine ⟨⟨n, ?_, ?_⟩⟩
  · refine (cancel_mono W.subspace.ι).1 ?_
    rw [Category.id_comp, Category.assoc, hn, ← Category.assoc, hm, Category.assoc,
      e.hom_inv_id, Category.comp_id]
  · refine (cancel_mono W'.subspace.ι).1 ?_
    rw [Category.id_comp, Category.assoc, hm, ← Category.assoc, hn, Category.assoc,
      e.inv_hom_id, Category.comp_id]

/-- **The comparison morphism to the image of an integral closed subspace under an
isomorphism.**  For `e : X ≅ Y` an isomorphism of algebraic spaces over `S` with `Y` decent and
`W ⊆ X` an integral closed subspace, there is a morphism from `W` to its image `e(W) ⊆ Y` over
`e`. -/
theorem exists_hom_pushforward_of_iso (W : IntegralClosedSubspace B S hS X) :
    ∃ m : W.subspace.toFunctor ⟶ (IntegralClosedSubspace.pushforward B S hS hY hX hYdec
        (isClosedImmersion_of_isIso B S hS e.hom) W).subspace.toFunctor,
      m ≫ (IntegralClosedSubspace.pushforward B S hS hY hX hYdec
          (isClosedImmersion_of_isIso B S hS e.hom) W).subspace.ι =
        W.subspace.ι ≫ e.hom := by
  rw [← IntegralClosedSubspace.closureImage_eq_pushforward B S hS hY hX hYdec
    (isClosedImmersion_of_isIso B S hS e.hom) W]
  exact IntegralClosedSubspace.exists_hom_closureImage B S hS hY hYdec e.hom W

/-- The comparison morphism to the image of an integral closed subspace under an isomorphism is
an isomorphism: the point set of the image is the image of the point set. -/
theorem isIso_of_comp_ι_eq_pushforward_of_iso (W : IntegralClosedSubspace B S hS X)
    {m : W.subspace.toFunctor ⟶ (IntegralClosedSubspace.pushforward B S hS hY hX hYdec
      (isClosedImmersion_of_isIso B S hS e.hom) W).subspace.toFunctor}
    (hm : m ≫ (IntegralClosedSubspace.pushforward B S hS hY hX hYdec
        (isClosedImmersion_of_isIso B S hS e.hom) W).subspace.ι =
      W.subspace.ι ≫ e.hom) :
    IsIso m :=
  isIso_of_comp_ι_eq_of_iso B S hS hX e W _
    (IntegralClosedSubspace.subspacePointSet_pushforward B S hS hY hX hYdec
      (isClosedImmersion_of_isIso B S hS e.hom) W) m hm

end Comparison

/-! ### The pushforward of a cycle carried out to the ambient space -/

section CyclePushforward

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (e : X ≅ Y)

/-- **Carrying a cycle out and across an isomorphism.**  For `e : X ≅ Y` an isomorphism of good
algebraic spaces over the base, `W ⊆ X` an integral closed subspace, `W' ⊆ Y` an integral closed
subspace and `m : W ⟶ W'` a closed immersion over `e`, pushing a cycle on `W` out to `X` and then
along `e` is pushing it along `m` and then out to `Y`. -/
theorem cycleGroupClosedPushforward_integralClosedSubspacePushforward_of_iso
    (hcomp : e.hom ≫ sY = sX) (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem Y)
    {m : W.subspace.toFunctor ⟶ W'.subspace.toFunctor}
    (hmi : IsClosedImmersion D.site D.base D.base_mem m)
    (hm : m ≫ W'.subspace.ι = W.subspace.ι ≫ e.hom) (k : ℤ)
    (c : CycleGroup D (W.subspace.ι ≫ sX) k) :
    cycleGroupClosedPushforward D hY.1 hX.1 (D.isDecentSpace_of_isGood sY hY)
          (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) sY hY.2.2 sX hcomp k
          (integralClosedSubspacePushforward D sX hX W k c) =
      integralClosedSubspacePushforward D sY hY W' k
        (cycleGroupClosedPushforward D W'.isClosedSubspace.1 W.isClosedSubspace.1
          (isDecentSpace_of_isGood D (W'.subspace.ι ≫ sY)
            (isGood_integralClosedSubspace D sY hY W'))
          hmi (W'.subspace.ι ≫ sY) (isGood_integralClosedSubspace D sY hY W').2.2
          (W.subspace.ι ≫ sX) (by rw [← Category.assoc, hm, Category.assoc, hcomp]) k c) := by
  refine Subtype.ext ?_
  change cycleClosedPushforward D hY.1 hX.1 (D.isDecentSpace_of_isGood sY hY) _
      (cycleClosedPushforward D hX.1 W.isClosedSubspace.1
        (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 c.1) =
    cycleClosedPushforward D hY.1 W'.isClosedSubspace.1
      (D.isDecentSpace_of_isGood sY hY) W'.isClosedSubspace.2
      (cycleClosedPushforward D W'.isClosedSubspace.1 W.isClosedSubspace.1 _ hmi c.1)
  rw [← cycleClosedPushforward_comp D hY.1 hX.1 W.isClosedSubspace.1
      (D.isDecentSpace_of_isGood sY hY) (D.isDecentSpace_of_isGood sX hX)
      W.isClosedSubspace.2 (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) c.1,
    ← cycleClosedPushforward_comp D hY.1 W'.isClosedSubspace.1 W.isClosedSubspace.1
      (D.isDecentSpace_of_isGood sY hY) _ hmi W'.isClosedSubspace.2 c.1]
  exact cycleClosedPushforward_congr D hY.1 W.isClosedSubspace.1
    (D.isDecentSpace_of_isGood sY hY) _ _ hm.symm c.1

end CyclePushforward

/-! ### The descent to the Chow groups at the canonical embeddings -/

section Descent

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (e : X ≅ Y) (hcomp : e.hom ≫ sY = sX)

/-- **Pushforward along an isomorphism preserves rational equivalence at the canonical
embeddings.**  For `e : X ≅ Y` an isomorphism of good algebraic spaces over the base and
`α ∈ Z_k(X)` rationally equivalent to zero in the canonical reading of part (2) of Stacks 0EQ6,
the cycle `e_*α ∈ Z_k(Y)` is rationally equivalent to zero in the canonical reading.

This is the case of Stacks 0EQC in which the proper morphism is an isomorphism. -/
theorem isRationallyEquivalentToZeroCanonical_cycleGroupClosedPushforward_of_iso (k : ℤ)
    {α : CycleGroup D sX k}
    (hα : IsRationallyEquivalentToZeroCanonical.{v} D sX hX k α) :
    IsRationallyEquivalentToZeroCanonical.{v} D sY hY k
      (cycleGroupClosedPushforward D hY.1 hX.1 (D.isDecentSpace_of_isGood sY hY)
        (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) sY hY.2.2 sX hcomp k α) := by
  classical
  obtain ⟨J, W, hWfin, c, hdim, hprin, rfl⟩ := hα
  have himage : ∀ A : Set (points D.site D.base D.base_mem X),
      pointsMap D.site D.base D.base_mem X e.hom '' A =
        pointsMap D.site D.base D.base_mem Y e.inv ⁻¹' A := by
    exact congrFun (Set.image_eq_preimage_of_inverse (pointsMap_inv_pointsMap_hom _ _ _ e)
      (pointsMap_inv_pointsMap_hom _ _ _ e.symm))
  choose m hm using fun j : J => exists_hom_pushforward_of_iso D.site D.base D.base_mem hX.1
    hY.1 (D.isDecentSpace_of_isGood sY hY) e (W j)
  have hmiso : ∀ j, IsIso (m j) := fun j =>
    isIso_of_comp_ι_eq_pushforward_of_iso D.site D.base D.base_mem hX.1 hY.1
      (D.isDecentSpace_of_isGood sY hY) e (W j) (hm j)
  have hmi : ∀ j, IsClosedImmersion D.site D.base D.base_mem (m j) := fun j =>
    isClosedImmersion_of_isIso D.site D.base D.base_mem (m j)
  have hmcomp : ∀ j, m j ≫
      ((IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY.1 hX.1
            (D.isDecentSpace_of_isGood sY hY)
            (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom)
            (W j)).subspace.ι ≫ sY) =
      (W j).subspace.ι ≫ sX := fun j => by
    rw [← Category.assoc, hm j, Category.assoc, hcomp]
  refine ⟨J, fun j => IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY.1 hX.1
      (D.isDecentSpace_of_isGood sY hY)
      (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) (W j), ?_,
    fun j => cycleGroupClosedPushforward D
      (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY.1 hX.1
        (D.isDecentSpace_of_isGood sY hY)
        (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom)
        (W j)).isClosedSubspace.1 (W j).isClosedSubspace.1
      (isDecentSpace_of_isGood D
        ((IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY.1 hX.1
          (D.isDecentSpace_of_isGood sY hY)
          (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom)
          (W j)).subspace.ι ≫ sY)
        (isGood_integralClosedSubspace D sY hY
          (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY.1 hX.1
            (D.isDecentSpace_of_isGood sY hY)
            (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) (W j))))
      (hmi j)
      ((IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY.1 hX.1
        (D.isDecentSpace_of_isGood sY hY)
        (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom)
        (W j)).subspace.ι ≫ sY)
      (isGood_integralClosedSubspace D sY hY
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY.1 hX.1
          (D.isDecentSpace_of_isGood sY hY)
          (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) (W j))).2.2
      ((W j).subspace.ι ≫ sX)
      (hmcomp j) k (c j),
    fun j => ?_, fun j => ?_, Subtype.ext (funext fun T' => ?_)⟩
  · refine (hWfin.preimage_continuous
      (continuous_pointsMap D.site D.base D.base_mem e.inv)).subset fun j => Eq.subset ?_
    rw [IntegralClosedSubspace.subspacePointSet_pushforward, himage]
  · rw [IntegralClosedSubspace.deltaDimension_pushforward D sY hY.2.2 hY.1 hX.1
      (D.isDecentSpace_of_isGood sY hY)
      (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) (W j), hcomp]
    exact hdim j
  · exact isPrincipalDivisorCycleOfGood_cycleGroupClosedPushforward_of_iso D
      ((W j).subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX (W j)) _
      (isGood_integralClosedSubspace D sY hY _) (W j).isIntegralSpace
      (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY.1 hX.1
        (D.isDecentSpace_of_isGood sY hY)
        (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom)
        (W j)).isIntegralSpace (asIso (m j)) (hmcomp j) k (hprin j)
  · obtain ⟨T, rfl⟩ := IntegralClosedSubspace.surjective_pushforward_of_iso D.site D.base
      D.base_mem hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX)
      (D.isDecentSpace_of_isGood sY hY) e T'
    change cycleClosedPushforward D hY.1 hX.1 (D.isDecentSpace_of_isGood sY hY)
        (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom)
        (cycleFamilySum D sX hX W hWfin k c).1 _ = _
    rw [cycleClosedPushforward_apply_pushforward, cycleFamilySum_apply, cycleFamilySum_apply]
    refine finsum_congr fun j => ?_
    rw [← cycleGroupClosedPushforward_integralClosedSubspacePushforward_of_iso D sX hX sY hY e
      hcomp (W j) _ (hmi j) (hm j) k (c j)]
    exact (cycleClosedPushforward_apply_pushforward D hY.1 hX.1
      (D.isDecentSpace_of_isGood sY hY)
      (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) _ T).symm

/-- **Pushforward along an isomorphism on the Chow groups at the canonical embeddings.**  The
homomorphism `e_* : CH_k(X) ⟶ CH_k(Y)` induced by an isomorphism `e : X ≅ Y` of good algebraic
spaces over the base, on the Chow groups
`AlgebraicGeometry.Space.chowGroupCanonical` of Stacks 0EQ6. -/
def chowGroupCanonicalPushforwardOfIso (k : ℤ) :
    chowGroupCanonical.{v} D sX hX k →+ chowGroupCanonical.{v} D sY hY k :=
  chowGroupCanonicalLift.{v} D sX hX k
    ((chowClassCanonical.{v} D sY hY k).comp
      (cycleGroupClosedPushforward D hY.1 hX.1 (D.isDecentSpace_of_isGood sY hY)
        (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) sY hY.2.2 sX hcomp k))
    fun _ hα => (chowClassCanonical_eq_zero_iff.{v} D sY hY k _).2
      (isRationallyEquivalentToZeroCanonical_cycleGroupClosedPushforward_of_iso.{v} D sX hX sY hY
        e hcomp k hα)

/-- The induced map on Chow groups carries the class of a cycle to the class of its
pushforward. -/
@[simp]
theorem chowGroupCanonicalPushforwardOfIso_chowClassCanonical (k : ℤ)
    (α : CycleGroup D sX k) :
    chowGroupCanonicalPushforwardOfIso.{v} D sX hX sY hY e hcomp k
        (chowClassCanonical.{v} D sX hX k α) =
      chowClassCanonical.{v} D sY hY k
        (cycleGroupClosedPushforward D hY.1 hX.1 (D.isDecentSpace_of_isGood sY hY)
          (isClosedImmersion_of_isIso D.site D.base D.base_mem e.hom) sY hY.2.2 sX hcomp k α) :=
  rfl

end Descent

end AlgebraicGeometry.Space

end
