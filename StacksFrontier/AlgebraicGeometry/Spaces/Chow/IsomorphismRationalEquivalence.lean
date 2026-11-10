module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowLocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.OpenRestrictionFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundle.ZeroLocusGysinDatum

/-!
# Rational equivalence along a surjective open immersion

In Situation 0EDT let `X/B` be good and let `j : U → X` be an open immersion over the base which
is surjective on points, for instance an isomorphism. Restriction of cycles `α ↦ α|_U` preserves
rational equivalence (part of Stacks 0EQ7), and in this case it also reflects it: if `α|_U ∼_rat 0`
then `α ∼_rat 0`. This is the localization sequence `CH_k(Y) → CH_k(X) → CH_k(U) → 0` of
Stacks 0EQ7 for the empty closed complement `Y`, on which every cycle vanishes.

Since flat pullback along an open immersion is restriction (Stacks 0EPY), the same holds for the
flat pullback of cycles along an isomorphism of good algebraic spaces over the base. The case
used in the proof of Stacks 0ERH is the restriction `p|_{o(X)} : o(X) → X` of the projection of a
vector bundle `p : E → X` to its zero locus, which is an isomorphism with inverse the zero
section: a `k`-cycle `β` on `X` is rationally equivalent to zero if and only if `(p|_{o(X)})^*β`
is.

## Main results

* `AlgebraicGeometry.Space.CycleGroup.eq_zero_of_isEmpty_points`: a good algebraic space with
  no points has no nonzero cycles.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZero_of_cycleGroupRestrict`: restriction along
  an open immersion which is surjective on points reflects rational equivalence.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZero_cycleGroupRestrict_iff`: so it preserves
  and reflects it.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZero_flatPullbackMap_iff_of_isIso`: flat
  pullback along an isomorphism of good algebraic spaces preserves and reflects rational
  equivalence.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZero_flatPullbackMap_vectorBundleZeroLocus_iff`:
  for a vector bundle `p : E → X` with zero locus `o(X)`, `(p|_{o(X)})^*β ∼_rat 0` if and only if
  `β ∼_rat 0`.

## References

* [Stacks Project, Tag 0EQ7](https://stacks.math.columbia.edu/tag/0EQ7)
* [Stacks Project, Tag 0EPY](https://stacks.math.columbia.edu/tag/0EPY)
* [Stacks Project, Tag 0ERH](https://stacks.math.columbia.edu/tag/0ERH)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Empty

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)

/-- **A space with no points has no nonzero cycles**: an integral closed subspace has a generic
point, which would be a point of the space. -/
theorem CycleGroup.eq_zero_of_isEmpty_points (hX : IsEmpty (points D.site D.base D.base_mem X))
    {k : ℤ} (α : CycleGroup D sX k) : α = 0 :=
  Subtype.ext (funext fun W => (hX.false (pointsMap D.site D.base D.base_mem
    W.subspace.toFunctor W.subspace.ι (W.genericPoint D.site D.base D.base_mem))).elim)

end Empty

section Restrict

variable (D : BaseSpaceDimensionSituation.{u})
    {X U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sU : U ⟶ D.space) (hU : D.IsGood sU)
    {j : U ⟶ X} (hj : IsOpenImmersion D.site D.base D.base_mem j) (hjc : j ≫ sX = sU)

/-- **Restriction along a surjective open immersion reflects rational equivalence.** Let
`j : U → X` be an open immersion of good algebraic spaces over the base which is surjective on
points. If the restriction `α|_U` of a `k`-cycle `α` on `X` is rationally equivalent to zero,
then so is `α`.

This is Stacks 0EQ7 for the reduced closed subspace `Y ⊆ X` on the empty set of points, the
complement of `|U| = |X|`: `α ∼_rat i_*γ` for some `γ ∈ Z_k(Y)`, and `Z_k(Y) = 0`. -/
theorem isRationallyEquivalentToZero_of_cycleGroupRestrict
    (hsurj : Function.Surjective (pointsMap D.site D.base D.base_mem U j)) (k : ℤ)
    {α : CycleGroup D sX k}
    (h : IsRationallyEquivalentToZero.{v} D sU hU k
      (cycleGroupRestrict D sX hX sU hU hj hjc k α)) :
    IsRationallyEquivalentToZero.{v} D sX hX k α := by
  obtain ⟨Y, hY, hYpt, -⟩ := (existsUnique_reducedClosedSubspace D.site D.base D.base_mem X hX.1
    ∅ isClosed_empty).exists
  have hYgood := isGood_ι_of_isClosedSubspace D sX hX Y hY
  have hcompl : Set.range (pointsMap D.site D.base D.base_mem Y.toFunctor Y.ι) =
      (Set.range (pointsMap D.site D.base D.base_mem U j))ᶜ := by
    rw [hYpt, hsurj.range_eq, Set.compl_univ]
  have hYempty : IsEmpty (points D.site D.base D.base_mem Y.toFunctor) :=
    ⟨fun y => (Set.mem_empty_iff_false _).1 (hYpt ▸ Set.mem_range_self y)⟩
  obtain ⟨γ, hγ⟩ := exists_rationallyEquivalent_add_cycleGroupClosedPushforward_of_restrict.{v}
    D sX hX (Y.ι ≫ sX) hYgood sU hU hY.2 rfl hj hjc hcompl k α 0 (by
      change IsRationallyEquivalentToZero.{v} D sU hU k (_ - _)
      rwa [map_zero, sub_zero])
  rw [CycleGroup.eq_zero_of_isEmpty_points D (Y.ι ≫ sX) hYempty γ, map_zero, add_zero] at hγ
  change IsRationallyEquivalentToZero.{v} D sX hX k (α - 0) at hγ
  rwa [sub_zero] at hγ

/-- **Restriction along a surjective open immersion preserves and reflects rational
equivalence**: for an open immersion `j : U → X` of good algebraic spaces over the base which is
surjective on points, `α|_U ∼_rat 0` if and only if `α ∼_rat 0`. -/
theorem isRationallyEquivalentToZero_cycleGroupRestrict_iff
    (hsurj : Function.Surjective (pointsMap D.site D.base D.base_mem U j)) (k : ℤ)
    (α : CycleGroup D sX k) :
    IsRationallyEquivalentToZero.{v} D sU hU k (cycleGroupRestrict D sX hX sU hU hj hjc k α) ↔
      IsRationallyEquivalentToZero.{v} D sX hX k α :=
  ⟨isRationallyEquivalentToZero_of_cycleGroupRestrict D sX hX sU hU hj hjc hsurj k,
    isRationallyEquivalentToZero_cycleGroupRestrict D sX hX sU hU hj hjc k⟩

end Restrict

section Iso

variable (D : BaseSpaceDimensionSituation.{u})
    {X U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sU : U ⟶ D.space) (hU : D.IsGood sU)

/-- **Flat pullback along an isomorphism preserves and reflects rational equivalence.** For an
isomorphism `j : U → X` of good algebraic spaces over the base, flat of relative dimension `0`,
`j^*α ∼_rat 0` if and only if `α ∼_rat 0`, for every `k`-cycle `α` on `X`.

The flat pullback along `j`, an open immersion, is the restriction of cycles
(`AlgebraicGeometry.Space.flatPullbackMap_eq_cycleGroupRestrict`), and `j` is surjective on
points. -/
theorem isRationallyEquivalentToZero_flatPullbackMap_iff_of_isIso (j : U ⟶ X) [IsIso j]
    (hjc : j ≫ sX = sU) (hflat : IsFlat D.site D.base D.base_mem j)
    (hr : HasRelativeDimension 0 D.site D.base D.base_mem j) (k n : ℤ)
    (hkn : k + ((0 : ℕ) : ℤ) = n) (α : CycleGroup D sX k) :
    IsRationallyEquivalentToZero.{v} D sU hU n
        (flatPullbackMap D sU hU sX hX j hjc 0 hflat hr k n hkn α) ↔
      IsRationallyEquivalentToZero.{v} D sX hX k α := by
  have hj := isOpenImmersion_of_isIso D.site D.base D.base_mem j
  obtain rfl : k = n := by simpa using hkn
  have heq : flatPullbackMap D sU hU sX hX j hjc 0 hflat hr k k hkn α =
      cycleGroupRestrict D sX hX sU hU hj hjc k α :=
    Subtype.ext (flatPullbackMap_eq_cycleGroupRestrict D sX hX sU hU hj hjc k k hkn α)
  rw [heq]
  exact isRationallyEquivalentToZero_cycleGroupRestrict_iff D sX hX sU hU hj hjc
    (pointsHomeomorphOfIso D.site D.base D.base_mem (asIso j)).surjective k α

end Iso

section VectorBundle

variable (D : BaseSpaceDimensionSituation.{u}) (W : AlgebraicSpaces D.site D.base D.base_mem)
  (F : SheafOfModules.{u} (structureRingSheaf D.site D.base D.base_mem W))
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F]
  (sW : W.1 ⟶ D.space) (hW : D.IsGood sW)

/-- The restriction `p|_{o(X)} : o(X) → X` of the projection of a vector bundle to its zero
locus is an isomorphism, with inverse the zero section. -/
instance isIso_vectorBundleZeroLocus_ι_comp :
    IsIso ((vectorBundleZeroLocus D.site D.base D.base_mem W F).1.ι ≫
      (vectorBundleProjection D.site D.base D.base_mem W F).hom) :=
  (vectorBundleZeroLocusIso D.site D.base D.base_mem W F).isIso_inv

/-- **A cycle is rationally equivalent to zero if and only if its flat pullback to the zero
locus of a vector bundle is.** Let `p : E → X` be the vector bundle of a finite locally free
`𝒪_X`-module on a good algebraic space `X/B`, with zero locus `o(X) ⊆ E`. The restriction
`p|_{o(X)} : o(X) → X` of the projection is an isomorphism, with inverse the zero section; so
for every `k`-cycle `β` on `X`, `(p|_{o(X)})^*β ∼_rat 0` if and only if `β ∼_rat 0`.

In the proof of Stacks 0ERH, `(p|_{o(X)})^*β` is the Gysin pullback `o^*p^*β` of Stacks 0ERE. -/
theorem isRationallyEquivalentToZero_flatPullbackMap_vectorBundleZeroLocus_iff
    (hflat : IsFlat D.site D.base D.base_mem
      ((vectorBundleZeroLocus D.site D.base D.base_mem W F).1.ι ≫
        (vectorBundleProjection D.site D.base D.base_mem W F).hom))
    (hr : HasRelativeDimension 0 D.site D.base D.base_mem
      ((vectorBundleZeroLocus D.site D.base D.base_mem W F).1.ι ≫
        (vectorBundleProjection D.site D.base D.base_mem W F).hom))
    (k n : ℤ) (hkn : k + ((0 : ℕ) : ℤ) = n) (β : CycleGroup D sW k) :
    IsRationallyEquivalentToZero.{v} D _ (isGood_vectorBundleZeroLocus D W F sW hW) n
        (flatPullbackMap D _ (isGood_vectorBundleZeroLocus D W F sW hW) sW hW
          ((vectorBundleZeroLocus D.site D.base D.base_mem W F).1.ι ≫
            (vectorBundleProjection D.site D.base D.base_mem W F).hom)
          (Category.assoc _ _ _) 0 hflat hr k n hkn β) ↔
      IsRationallyEquivalentToZero.{v} D sW hW k β :=
  isRationallyEquivalentToZero_flatPullbackMap_iff_of_isIso D sW hW _
    (isGood_vectorBundleZeroLocus D W F sW hW) _ (Category.assoc _ _ _) hflat hr k n hkn β

end VectorBundle

end AlgebraicGeometry.Space

end
