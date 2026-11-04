module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatDimensionFunctor
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeRankLocus
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeRankLocusDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericRankDecomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange

/-!
# The generic-rank decomposition after an arbitrary base change

Situation Stacks 05MP fixes a smooth morphism `f : X ⟶ S` with geometrically irreducible
fibres and a quasi-coherent `𝒪_X`-module `F` of finite type; Situation Stacks 05MT fixes a
morphism locally of finite type, a quasi-coherent module of finite type and a dimension bound
`n`, and produces the functor `F_n` of flatness in dimensions `≥ n`. This file places the first
situation inside the second at a chosen dimension `d` and transports the pointwise equivalence
of Stacks 05UE, proved over the base, to every scheme `T` over `S`.

The point is that all the hypotheses of that equivalence are stable under base change: the
base change `X_T ⟶ T` of a smooth morphism is smooth, its fibres are again geometrically
irreducible, its relative dimension is again `d`, and `F_T` is again of finite presentation.
Applying the equivalence to `X_T ⟶ T` and `F_T` rather than to `f` and `F` therefore gives the
two directions over `T`, with no new geometry.

## Main results

All names below are in the namespace `AlgebraicGeometry.FreeAtGenericPointsSituation`.

* `toFlatDimensionSituation`: the situation of Stacks 05MT attached to a situation of
  Stacks 05MP and a dimension `d`.
* `relativeDimension_baseChangeMap`, `geometricallyIrreducibleFibers_baseChangeMap` and
  `finitePresentation_baseChangeMap`: the hypotheses of Stacks 05UE after an arbitrary base
  change. Finite presentation of the base-changed module is
  `AlgebraicGeometry.pullbackObj_isFinitePresentation`.
* `exists_mem_baseRankLocus`: **the forward direction of Stacks 05UE over an arbitrary `T`**,
  that flatness of `F_T` in dimensions `≥ d` puts every point of `T` in the image of the
  free-rank locus for some rank.
* `isFlatInDimensionsGEAfterBaseChange_of_forall_exists_mem_baseRankLocus`: **the converse
  over an arbitrary `T`**.
* `isFlatInDimensionsGEAfterBaseChange_iff_forall_exists_mem_baseRankLocus`: the two
  together, the statement that a value of `F_d` is nonempty exactly when the images of the
  free-rank loci cover `T`.
* `isFlatInDimensionsGEAfterBaseChange_of_condition`: the inclusion `H_p ⊆ F_d` of the source.

## Implementation notes

The two loci-flavoured statements are phrased with
`AlgebraicGeometry.FreeAtGenericPointsSituation.baseRankLocus`, the image in `T` of the locus
in `X_T` where `F_T` is free of rank `r`, rather than with the raw generic-point condition.
That image is open and, by
`AlgebraicGeometry.FreeAtGenericPointsSituation.mem_baseRankLocus_iff`, contains a point `t`
exactly when `F_T` is free of rank `r` near the generic point of `X_t`. Phrased this way the
pair of directions says that a value of `F_d` is nonempty exactly when those open sets, one
for each rank, cover `T`, which is the form in which the coproduct decomposition uses them.

Finite presentation of `X_T ⟶ T` is where affineness of `X` and `S` enters: a morphism of
affine schemes is affine, hence so is every base change of it, hence `X_T ⟶ T` is quasi-compact
and quasi-separated. Local finite presentation needs no affineness, being stable under base
change from the smooth `f`.

## References

* [Stacks Project, Tag 05UE](https://stacks.math.columbia.edu/tag/05UE)
* [Stacks Project, Tag 05MP](https://stacks.math.columbia.edu/tag/05MP)
* [Stacks Project, Tag 05MT](https://stacks.math.columbia.edu/tag/05MT)
* [Stacks Project, Tag 0555](https://stacks.math.columbia.edu/tag/0555)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace FreeAtGenericPointsSituation

variable (D : FreeAtGenericPointsSituation.{u})

/-! ### The hypotheses of Stacks 05UE after a base change -/

/-- The base change of the smooth family of the situation is smooth. -/
instance smooth_baseChangeMap (T : Over D.S) : Smooth (D.baseChangeMap T) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback D.f T.hom) inferInstance

/-- Every fibre of a base change of the family is geometrically irreducible. -/
theorem geometricallyIrreducibleFibers_baseChangeMap (T : Over D.S) (t : T.left) :
    GeometricallyIrreducible ((D.baseChangeMap T).fiberToSpecResidueField t) :=
  (GeometricallyIrreducible.iff_geometricallyIrreducible_fiber (D.baseChangeMap T)).mp
    (D.geometricallyIrreducible_baseChangeMap T) t

/-- Relative dimension `d` is inherited by the base change of the family. -/
theorem relativeDimension_baseChangeMap {d : ℕ} (hd : RelativeDimension D.f d)
    (T : Over D.S) : RelativeDimension (D.baseChangeMap T) d :=
  RelativeDimension.of_isPullback (IsPullback.of_hasPullback D.f T.hom) hd

/-- The base change of the family is affine when `X` and `S` are, hence quasi-compact. -/
instance isAffineHom_baseChangeMap [IsAffine D.X] [IsAffine D.S] (T : Over D.S) :
    IsAffineHom (D.baseChangeMap T) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback D.f T.hom) inferInstance

/-- The base change of the family is of finite presentation when `X` and `S` are affine: it is
locally of finite presentation because `f` is smooth, and quasi-compact and quasi-separated
because it is an affine morphism. -/
theorem finitePresentation_baseChangeMap [IsAffine D.X] [IsAffine D.S] (T : Over D.S) :
    FinitePresentation (D.baseChangeMap T) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-! ### The situation of Stacks 05MT attached to the situation of Stacks 05MP -/

/-- **Stacks Project, Tag 05MT.** The situation in which the functor `F_d` of flatness in
dimensions `≥ d` is defined, attached to the smooth situation of Stacks 05MP and a dimension
`d`: the same morphism, the same module, and the dimension bound `d`. -/
noncomputable def toFlatDimensionSituation (d : ℕ) : FlatDimensionSituation.{u} where
  S := D.S
  X := D.X
  f := D.f
  F := D.F
  n := d

/-- The base of `D.toFlatDimensionSituation d` is the base `D.S`. -/
@[simp] theorem toFlatDimensionSituation_S (d : ℕ) : (D.toFlatDimensionSituation d).S = D.S :=
  rfl

/-- The morphism of `D.toFlatDimensionSituation d` is the smooth morphism `D.f`. -/
@[simp] theorem toFlatDimensionSituation_f (d : ℕ) :
    (D.toFlatDimensionSituation d).f = D.f := rfl

/-- The dimension bound of `D.toFlatDimensionSituation d` is `d`. -/
@[simp] theorem toFlatDimensionSituation_n (d : ℕ) : (D.toFlatDimensionSituation d).n = d :=
  rfl

/-- The condition tested by `F_d` over `T` is flatness of `F_T` over `T` in dimensions `≥ d`,
for the base-changed morphism and module of the smooth situation. -/
theorem isFlatInDimensionsGEAfterBaseChange_iff (d : ℕ) (T : Over D.S) :
    (D.toFlatDimensionSituation d).IsFlatInDimensionsGEAfterBaseChange T ↔
      IsFlatOverInDimensionsGE (D.baseChangeMap T) (D.baseChangeModule T) d :=
  Iff.rfl

/-! ### The two directions of Stacks 05UE over an arbitrary scheme over the base -/

/-- **The forward direction of Stacks Project, Tag 05UE, over an arbitrary `T`.** If `F_T` is
flat over `T` in dimensions `≥ d`, then every point `t` of `T` lies in the image of the locus
where `F_T` is free of some rank `r`; equivalently `F_T` is free of rank `r` near the generic
point of the fibre `X_t`. -/
theorem exists_mem_baseRankLocus [IsAffine D.X] [IsAffine D.S] [D.F.IsFinitePresentation]
    {d : ℕ} (hd : RelativeDimension D.f d) (T : Over D.S)
    (hflat : (D.toFlatDimensionSituation d).IsFlatInDimensionsGEAfterBaseChange T)
    (t : T.left) : ∃ r : ℕ, t ∈ D.baseRankLocus r T := by
  obtain ⟨ξ, hξ⟩ := D.exists_isGenericPoint_fiber_baseChangeMap T t
  obtain ⟨r, hr⟩ := exists_freeAtPointOfRank_of_isFlatOverInDimensionsGE
    (D.baseChangeMap T) (D.finitePresentation_baseChangeMap T)
    (D.geometricallyIrreducibleFibers_baseChangeMap T)
    (D.relativeDimension_baseChangeMap hd T) (D.baseChangeModule T) hflat t ξ hξ
  refine ⟨r, (D.baseChangeMap T).fiberι t ξ, hr, ?_⟩
  have hmem : (D.baseChangeMap T).fiberι t ξ ∈ Set.range ((D.baseChangeMap T).fiberι t) :=
    ⟨ξ, rfl⟩
  rwa [Scheme.Hom.range_fiberι] at hmem

/-- **The converse direction of Stacks Project, Tag 05UE, over an arbitrary `T`.** If every
point of `T` lies in the image of the free-rank locus for some rank, then `F_T` is flat over
`T` in dimensions `≥ d`. -/
theorem isFlatInDimensionsGEAfterBaseChange_of_forall_exists_mem_baseRankLocus
    [D.F.IsFinitePresentation] {d : ℕ} (hd : RelativeDimension D.f d) (T : Over D.S)
    (h : ∀ t : T.left, ∃ r : ℕ, t ∈ D.baseRankLocus r T) :
    (D.toFlatDimensionSituation d).IsFlatInDimensionsGEAfterBaseChange T := by
  refine isFlatOverInDimensionsGE_of_forall_exists_freeAtPointOfRank (D.baseChangeMap T)
    (D.geometricallyIrreducibleFibers_baseChangeMap T)
    (D.relativeDimension_baseChangeMap hd T) (D.baseChangeModule T) ?_
  intro t ξ hξ
  obtain ⟨r, hr⟩ := h t
  exact ⟨r, (D.mem_baseRankLocus_iff r T t).mp hr ξ hξ⟩

/-- **Stacks Project, Tag 05UE, over an arbitrary `T`.** A value of the functor `F_d` is
nonempty exactly when the images of the free-rank loci cover `T`. -/
theorem isFlatInDimensionsGEAfterBaseChange_iff_forall_exists_mem_baseRankLocus
    [IsAffine D.X] [IsAffine D.S] [D.F.IsFinitePresentation] {d : ℕ}
    (hd : RelativeDimension D.f d) (T : Over D.S) :
    (D.toFlatDimensionSituation d).IsFlatInDimensionsGEAfterBaseChange T ↔
      ∀ t : T.left, ∃ r : ℕ, t ∈ D.baseRankLocus r T :=
  ⟨fun hflat ↦ D.exists_mem_baseRankLocus hd T hflat,
    D.isFlatInDimensionsGEAfterBaseChange_of_forall_exists_mem_baseRankLocus hd T⟩

/-- **The inclusion `H_p ⊆ F_d` of Stacks Project, Tag 05UE.** If `F_T` is free of rank `p`
near the generic point of every fibre over `T`, then `F_T` is flat over `T` in dimensions
`≥ d`. -/
theorem isFlatInDimensionsGEAfterBaseChange_of_condition [D.F.IsFinitePresentation] {d : ℕ}
    (hd : RelativeDimension D.f d) (p : ℕ) (T : Over D.S) (h : D.Condition p T) :
    (D.toFlatDimensionSituation d).IsFlatInDimensionsGEAfterBaseChange T :=
  D.isFlatInDimensionsGEAfterBaseChange_of_forall_exists_mem_baseRankLocus hd T fun t ↦
    ⟨p, (D.condition_iff_baseRankLocus_eq_univ p T).mp h ▸ Set.mem_univ t⟩

end FreeAtGenericPointsSituation

end AlgebraicGeometry

end
