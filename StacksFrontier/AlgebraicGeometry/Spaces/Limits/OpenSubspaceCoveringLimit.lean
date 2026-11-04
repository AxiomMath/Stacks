module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform

/-!
# A monotone family of open subspaces covering a limit is everything at one stage

Let `X = limit D` be the limit of a cofiltered inverse system `D` of quasi-compact algebraic
spaces over a scheme `S` with affine transition morphisms, and let `K i ⊆ D i` be open
subspaces which grow along the transition morphisms, in the sense that the inverse image of
`K i` in `D j` is contained in `K j` whenever `j` maps to `i`. If every point of `X` lies in
the inverse image of some `K i`, then `K i` is the whole of `D i` for some `i`.

## Main results

* `AlgebraicGeometry.Space.exists_eq_top_of_covering_limit`: the statement above.
* `AlgebraicGeometry.Space.eq_top_of_range_pointsMap_eq_univ`: an open subspace whose points
  are all of the points of the ambient algebraic space is the whole subfunctor.

## Implementation notes

This is the step by which "some stage is a scheme" is reached from "the schematic loci of the
stages jointly see every point of the limit": applied to `K i = schematicLocus (D i)`, whose
monotonicity is `AlgebraicGeometry.Space.preimage_schematicLocus_le`, it says that the
schematic locus of some stage is everything, which is to say that that stage is a scheme.

The argument is in three moves. The inverse images in `|X|` of the point sets of the `K i`
form a *directed* family of opens — directed because the index category is cofiltered and the
`K i` grow — and `|X|` is quasi-compact, the projection to a stage being affine and hence
quasi-compact over a quasi-compact stage. A directed open cover of a quasi-compact space has a
single member equal to the whole space, so the inverse image of one `K j` is already all of
`|X|`. Descending that covering to a later stage is
`AlgebraicGeometry.Space.exists_stage_preimage_eq_univ`, and monotonicity turns the result
into the statement that `K k` has every point of `D k`. An open subspace with every point is
the whole subfunctor, because the identity then factors through it
(`AlgebraicGeometry.Space.factorsThrough_openSubspace_iff_points`, Stacks 03IE).

The hypotheses `hSize` and `hHomSize` are inherited from
`AlgebraicGeometry.Space.exists_stage_preimage_eq_univ` and from Stacks 07SF, and are the
standing size hypotheses of this part of the development.

## References

* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Points of a subfunctor -/

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The points of a subfunctor are among the points of any larger subfunctor. -/
private theorem range_pointsMap_ι_subset {A₁ A₂ : Subfunctor F} (h : A₁ ≤ A₂) :
    Set.range (pointsMap B S hS A₁.toFunctor A₁.ι) ⊆
      Set.range (pointsMap B S hS A₂.toFunctor A₂.ι) := by
  rw [← Subfunctor.homOfLe_ι h, pointsMap_comp, Set.range_comp]
  exact Set.image_subset_range _ _

/-- An open subspace whose points are all the points of the ambient algebraic space is the
whole subfunctor: the identity then factors through it by Stacks 03IE. -/
theorem eq_top_of_range_pointsMap_eq_univ (hF : IsAlgebraicSpace B S hS F)
    (U : Subfunctor F) (hU : IsOpenSubspace B S hS U)
    (hpts : Set.range (pointsMap B S hS U.toFunctor U.ι) = Set.univ) : U = ⊤ := by
  obtain ⟨g, hg⟩ :=
    (factorsThrough_openSubspace_iff_points B S hS hF hF U hU (𝟙 F)).mpr (by
      rw [hpts]; exact Set.subset_univ _)
  refine top_unique fun T x _ => ?_
  have hx : (g.app T x).val = x := congrArg (fun k => k.app T x) hg
  rw [← hx]
  exact (g.app T x).property

/-! ### The covering statement -/

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The limit of a cofiltered inverse system of quasi-compact algebraic spaces over `S` with
affine transition morphisms is quasi-compact: the projection to a stage is affine, hence
quasi-compact, and the base change of that projection along the identity of the stage is the
limit itself. -/
theorem isQuasiCompactSpace_limit (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj i)) :
    IsQuasiCompactSpace B S hS (limit D) := by
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  have hlim : IsAlgebraicSpace B S hS (limit D) :=
    isAlgebraicSpace_limit B S hS D hSize hHomSize hD hAffine
  have hqc : IsQuasiCompact B S hS (limit.π D i₀) :=
    isQuasiCompact_of_isAffineHom' B S hS (limit.π D i₀) hlim (hD i₀)
      (isAffineHom_limitπ B S hS D hSize hHomSize hAffine i₀)
  exact isQuasiCompactSpace_of_iso B S hS
    (asIso (pullback.snd (𝟙 (D.obj i₀)) (limit.π D i₀)))
    (hqc (D.obj i₀) (hD i₀) (hCompact i₀) (𝟙 (D.obj i₀)))

/-- **A monotone family of open subspaces which covers the limit is everything at a stage.**
Let `X = limit D` be the limit of a cofiltered inverse system of quasi-compact algebraic
spaces over `S` with affine transition morphisms, and let `K i` be open subspaces of the
stages whose inverse images grow: the inverse image of `K i` in `D j` lies in `K j` for every
`f : j ⟶ i`. If every point of `X` lies in the inverse image of some `K i`, then `K i = ⊤`
for some `i`.

Quasi-separatedness of the stages is not needed. -/
theorem exists_eq_top_of_covering_limit (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (K : ∀ i, Subfunctor (D.obj i)) (hK : ∀ i, IsOpenSubspace B S hS (K i))
    (hmon : ∀ {i j : I} (f : j ⟶ i), (K i).preimage (D.map f) ≤ K j)
    (hpoint : ∀ x : points B S hS (limit D), ∃ i,
      pointsMap B S hS (limit D) (limit.π D i) x ∈
        Set.range (pointsMap B S hS (K i).toFunctor (K i).ι)) :
    ∃ i, K i = ⊤ := by
  classical
  have _ : Nonempty I := IsCofiltered.nonempty
  have hlim : IsAlgebraicSpace B S hS (limit D) :=
    isAlgebraicSpace_limit B S hS D hSize hHomSize hD hAffine
  -- The point set of each `K i`, and its inverse image in the limit.
  set R : ∀ i, Set (points B S hS (D.obj i)) :=
    fun i => Set.range (pointsMap B S hS (K i).toFunctor (K i).ι) with hR
  have hRopen : ∀ i, IsOpen (R i) := fun i =>
    isOpen_range_pointsMap_of_isOpenImmersion B S hS (K i).ι (hK i).2
  set W : I → Set (points B S hS (limit D)) :=
    fun i => pointsMap B S hS (limit D) (limit.π D i) ⁻¹' R i with hW
  have hWopen : ∀ i, IsOpen (W i) := fun i =>
    (hRopen i).preimage (continuous_pointsMap B S hS (limit.π D i))
  -- `W` grows along the transition morphisms.
  have hstep : ∀ {i j : I} (f : j ⟶ i), W i ⊆ W j := by
    intro i j f x hx
    have hfac : pointsMap B S hS (limit D) (limit.π D i) x =
        pointsMap B S hS (D.obj j) (D.map f)
          (pointsMap B S hS (limit D) (limit.π D j) x) := by
      rw [← Function.comp_apply (f := pointsMap B S hS (D.obj j) (D.map f)), ← pointsMap_comp,
        limit.w]
    have hmem : pointsMap B S hS (limit D) (limit.π D j) x ∈
        Set.range (pointsMap B S hS ((K i).preimage (D.map f)).toFunctor
          ((K i).preimage (D.map f)).ι) := by
      rw [range_pointsMap_preimage_ι, Set.mem_preimage, ← hfac]
      exact hx
    exact range_pointsMap_ι_subset B S hS (hmon f) hmem
  -- The family is directed, and the limit is quasi-compact.
  have hdir : Directed (· ⊆ ·) W := fun i i' =>
    ⟨IsCofiltered.min i i', hstep (IsCofiltered.minToLeft i i'),
      hstep (IsCofiltered.minToRight i i')⟩
  have hcover : (Set.univ : Set (points B S hS (limit D))) ⊆ ⋃ i, W i := by
    intro x _
    obtain ⟨i, hi⟩ := hpoint x
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have _ : CompactSpace (points B S hS (limit D)) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS (limit D) hlim).mp
      (isQuasiCompactSpace_limit B S hS D hSize hHomSize hD hAffine hCompact)
  obtain ⟨j, hj⟩ := isCompact_univ.elim_directed_cover W hWopen hcover hdir
  -- Descend that covering to a later stage.
  obtain ⟨k, g, hk⟩ := exists_stage_preimage_eq_univ B S hS D hSize hHomSize hD hAffine
    hCompact j (V := R j) (hRopen j) (Set.univ_subset_iff.mp hj)
  refine ⟨k, eq_top_of_range_pointsMap_eq_univ B S hS (hD k) (K k) (hK k) ?_⟩
  refine Set.univ_subset_iff.mp ?_
  rw [← hk, ← range_pointsMap_preimage_ι]
  exact range_pointsMap_ι_subset B S hS (hmon g)

end AlgebraicGeometry.Space

end
