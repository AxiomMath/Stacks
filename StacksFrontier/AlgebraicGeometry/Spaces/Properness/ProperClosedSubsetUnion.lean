module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDiagonalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable

/-!
# Finite unions of closed subsets proper over the base

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, and let `T i`, for `i` in a finite index type, be closed subsets of the points of `X`. If
each `T i` is proper over `Y` then so is their union. This is Stacks 0CZH.

The source argument forms the disjoint union of the reduced induced closed subspaces on the
`T i` and transports properness along its surjection onto the reduced induced closed subspace
`Z` on the union. The argument here does the same bookkeeping without forming a coproduct. The
reduced induced subspace `Z i` on `T i` maps to `Z` by Stacks 03JJ, its points lying in the
union, and the resulting morphisms `u i : Z i ⟶ Z` are jointly surjective on points. Each of
the three clauses of properness of `Z ⟶ Y` is then read off that finite jointly surjective
family:

* quasi-compactness, because the point space of a base change of `Z ⟶ Y` is the union of the
  images of the point spaces of the corresponding base changes of the `Z i ⟶ Y`, each compact
  by Stacks 03E4;
* universal closedness, because the image of a closed set in such a base change is the finite
  union of the images of its preimages in those base changes, each closed by hypothesis;
* separatedness, because the relative diagonal of `Z ⟶ Y` is universally closed by the same
  finite-cover argument. The `u i` are closed immersions by Stacks 0AGC, hence so are the two
  comparison morphisms through which `Z i ×_Y Z i ⟶ Z ×_Y Z` factors, hence so is the
  composite of `u i` with the relative diagonal of `Z ⟶ Y`; and a relative diagonal which is
  universally closed and locally of finite type is a closed immersion by Stacks 04Y0.

## Main results

* `AlgebraicGeometry.Space.isProperOver_iUnion`: **Stacks 0CZH**.

## Implementation notes

The index type is an arbitrary finite type, so the empty union is covered: the empty set is
proper over `Y` because its reduced induced subspace is initial.

Comparison morphisms between fibre products are produced as witnesses of existence statements
(`AlgebraicGeometry.Space.exists_pullback_comparison` and its first-factor counterpart) rather
than written out, so that the only facts available about them downstream are the two
compatibilities with the projections and the cartesian square they sit in.

The topology on the point sets is `AlgebraicGeometry.Space.pointTopology`, installed as a local
instance, so closedness of the `T i` is closedness in the topology detected by scheme-valued
points.

## References

* [Stacks Project, Tag 0CZH](https://stacks.math.columbia.edu/tag/0CZH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Comparison morphisms between fibre products -/

/-- A base change of a closed immersion of presheaves on the big fppf site of `S` is a closed
immersion. Unlike `AlgebraicGeometry.Space.isClosedImmersion_of_isPullback` this is stated for
a cartesian square of presheaves, with no algebraicity hypothesis on its corners. -/
private theorem isClosedImmersion_snd_of_isPullback
    {F G H P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ H} {g : G ⟶ H} {fst : P ⟶ F} {snd : P ⟶ G}
    (sq : IsPullback fst snd f g) (hf : IsClosedImmersion B S hS f) :
    IsClosedImmersion B S hS snd :=
  (MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback sq hf

/-- **The comparison morphism `W ×_Y A' ⟶ W ×_Y A` along `e : A' ⟶ A`.** It is compatible with
both projections, and the square it makes with `e` over the projections to `A' ` and `A` is
cartesian, so it inherits every base-change-stable property of `e`. -/
private theorem exists_pullback_comparison
    {W Y A A' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : W ⟶ Y) (f : A ⟶ Y) (e : A' ⟶ A) :
    ∃ r : pullback g (e ≫ f) ⟶ pullback g f,
      r ≫ pullback.fst g f = pullback.fst g (e ≫ f) ∧
        r ≫ pullback.snd g f = pullback.snd g (e ≫ f) ≫ e ∧
          IsPullback r (pullback.snd g (e ≫ f)) (pullback.snd g f) e := by
  refine ⟨pullback.lift (pullback.fst g (e ≫ f)) (pullback.snd g (e ≫ f) ≫ e)
    (by rw [Category.assoc]; exact pullback.condition), pullback.lift_fst _ _ _,
    pullback.lift_snd _ _ _, ?_⟩
  apply IsPullback.of_right (p := pullback.lift_snd _ _ _)
    (t := IsPullback.of_hasPullback g f)
  simpa only [Category.assoc, pullback.lift_fst] using IsPullback.of_hasPullback g (e ≫ f)

/-- **The comparison morphism `A' ×_Y W ⟶ A ×_Y W` along `e : A' ⟶ A`**, the first-factor
counterpart of `AlgebraicGeometry.Space.exists_pullback_comparison`. -/
private theorem exists_pullback_comparison'
    {W Y A A' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : W ⟶ Y) (f : A ⟶ Y) (e : A' ⟶ A) :
    ∃ r : pullback (e ≫ f) g ⟶ pullback f g,
      r ≫ pullback.fst f g = pullback.fst (e ≫ f) g ≫ e ∧
        r ≫ pullback.snd f g = pullback.snd (e ≫ f) g ∧
          IsPullback (pullback.fst (e ≫ f) g) r e (pullback.fst f g) := by
  refine ⟨pullback.lift (pullback.fst (e ≫ f) g ≫ e) (pullback.snd (e ≫ f) g)
    (by rw [Category.assoc]; exact pullback.condition), pullback.lift_fst _ _ _,
    pullback.lift_snd _ _ _, ?_⟩
  apply IsPullback.flip
  apply IsPullback.of_right (p := pullback.lift_fst _ _ _)
    (t := (IsPullback.of_hasPullback f g).flip)
  simpa only [Category.assoc, pullback.lift_snd] using
    (IsPullback.of_hasPullback (e ≫ f) g).flip

/-! ### Properness from a finite jointly surjective family -/

/-- **A jointly surjective family stays jointly surjective after base change.** If the
`e i : A i ⟶ A` are jointly surjective on points, then so are the comparison morphisms
`W ×_Y A i ⟶ W ×_Y A`: a point of `W ×_Y A` has an image in `A`, that image comes from some
`A i`, and Stacks 03H4 lifts the resulting pair back to `W ×_Y A i`. -/
private theorem iUnion_range_pointsMap_eq_univ_of_jointlySurjective
    {A Y W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : IsAlgebraicSpace B S hS A) (hY : IsAlgebraicSpace B S hS Y)
    (hW : IsAlgebraicSpace B S hS W)
    {ι : Type v} (Ai : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hAi : ∀ i, IsAlgebraicSpace B S hS (Ai i)) (e : ∀ i, Ai i ⟶ A)
    (hcover : ∀ z : points B S hS A, ∃ i x, pointsMap B S hS (Ai i) (e i) x = z)
    (f : A ⟶ Y) (g : W ⟶ Y)
    (r : ∀ i, pullback g (e i ≫ f) ⟶ pullback g f)
    (hr : ∀ i, IsPullback (r i) (pullback.snd g (e i ≫ f)) (pullback.snd g f) (e i)) :
    ⋃ i, Set.range (pointsMap B S hS (pullback g (e i ≫ f)) (r i)) = Set.univ := by
  refine Set.eq_univ_of_forall fun p => ?_
  obtain ⟨i, zi, hzi⟩ := hcover (pointsMap B S hS (pullback g f) (pullback.snd g f) p)
  have hPalg : IsAlgebraicSpace B S hS (pullback g f) :=
    isAlgebraicSpace_pullback B S hS g f hW hA hY
  have hPialg : IsAlgebraicSpace B S hS (pullback g (e i ≫ f)) :=
    isAlgebraicSpace_pullback B S hS g (e i ≫ f) hW (hAi i) hY
  have hsq : IsPullback
      (ObjectProperty.homMk (r i) :
        (⟨pullback g (e i ≫ f), hPialg⟩ : AlgebraicSpaces B S hS) ⟶ ⟨pullback g f, hPalg⟩)
      (ObjectProperty.homMk (pullback.snd g (e i ≫ f)) :
        (⟨pullback g (e i ≫ f), hPialg⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Ai i, hAi i⟩)
      (ObjectProperty.homMk (pullback.snd g f) :
        (⟨pullback g f, hPalg⟩ : AlgebraicSpaces B S hS) ⟶ ⟨A, hA⟩)
      (ObjectProperty.homMk (e i) :
        (⟨Ai i, hAi i⟩ : AlgebraicSpaces B S hS) ⟶ ⟨A, hA⟩) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) (hr i)
  obtain ⟨p', hp', -⟩ := exists_point_of_isPullback B S hS hsq p zi hzi.symm
  exact Set.mem_iUnion.mpr ⟨i, p', hp'⟩

/-- **Quasi-compactness from a finite jointly surjective family.** If the `e i : A i ⟶ A` are
jointly surjective on points and each composite `A i ⟶ Y` is quasi-compact, then `A ⟶ Y` is
quasi-compact: the point space of a base change of `A ⟶ Y` is the union of the images of the
point spaces of the corresponding base changes of the `A i ⟶ Y`, which are compact by
Stacks 03E4. -/
private theorem isQuasiCompact_of_finite_cover
    {A Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : IsAlgebraicSpace B S hS A) (hY : IsAlgebraicSpace B S hS Y)
    {ι : Type v} [Finite ι] (Ai : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hAi : ∀ i, IsAlgebraicSpace B S hS (Ai i)) (e : ∀ i, Ai i ⟶ A)
    (hcover : ∀ z : points B S hS A, ∃ i x, pointsMap B S hS (Ai i) (e i) x = z)
    (f : A ⟶ Y) (hqc : ∀ i, IsQuasiCompact B S hS (e i ≫ f)) :
    IsQuasiCompact B S hS f := by
  intro W hW hWqc g
  choose r _hrfst _hrsnd hrsq using fun i => exists_pullback_comparison B S hS g f (e i)
  refine (isQuasiCompactSpace_iff_compactSpace_points B S hS (pullback g f)
    (isAlgebraicSpace_pullback B S hS g f hW hA hY)).mpr (isCompact_univ_iff.mp ?_)
  rw [← iUnion_range_pointsMap_eq_univ_of_jointlySurjective B S hS hA hY hW Ai hAi e hcover
    f g r hrsq]
  refine isCompact_iUnion fun i => ?_
  have : CompactSpace (points B S hS (pullback g (e i ≫ f))) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS (pullback g (e i ≫ f))
      (isAlgebraicSpace_pullback B S hS g (e i ≫ f) hW (hAi i) hY)).mp (hqc i W hW hWqc g)
  exact isCompact_range (continuous_pointsMap B S hS (r i))

/-- **Universal closedness from a finite jointly surjective family.** If the
`e i : A i ⟶ A` are jointly surjective on points and each composite `A i ⟶ Y` is universally
closed, then `A ⟶ Y` is universally closed: in a base change along `g : W ⟶ Y` the image of a
closed set is the finite union of the images of its preimages in the base changes of the
`A i ⟶ Y`, and each of those images is closed by hypothesis. -/
private theorem universallyClosed_of_finite_cover
    {A Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : IsAlgebraicSpace B S hS A) (hY : IsAlgebraicSpace B S hS Y)
    {ι : Type v} [Finite ι] (Ai : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hAi : ∀ i, IsAlgebraicSpace B S hS (Ai i)) (e : ∀ i, Ai i ⟶ A)
    (hcover : ∀ z : points B S hS A, ∃ i x, pointsMap B S hS (Ai i) (e i) x = z)
    (f : A ⟶ Y) (hclosed : ∀ i, UniversallyClosed B S hS (e i ≫ f)) :
    UniversallyClosed B S hS f := by
  intro W hW g C hC
  choose r hrfst _hrsnd hrsq using fun i => exists_pullback_comparison B S hS g f (e i)
  have hcov := iUnion_range_pointsMap_eq_univ_of_jointlySurjective B S hS hA hY hW Ai hAi e
    hcover f g r hrsq
  have himage : pointsMap B S hS (pullback g f) (pullback.fst g f) '' C =
      ⋃ i, pointsMap B S hS (pullback g (e i ≫ f)) (pullback.fst g (e i ≫ f)) ''
        (pointsMap B S hS (pullback g (e i ≫ f)) (r i) ⁻¹' C) := by
    have hfst : ∀ i, pointsMap B S hS (pullback g (e i ≫ f)) (pullback.fst g (e i ≫ f)) =
        pointsMap B S hS (pullback g f) (pullback.fst g f) ∘
          pointsMap B S hS (pullback g (e i ≫ f)) (r i) := fun i => by
      rw [← hrfst i, pointsMap_comp]
    simp_rw [hfst, Set.image_comp, Set.image_preimage_eq_inter_range]
    rw [← Set.image_iUnion, ← Set.inter_iUnion, hcov, Set.inter_univ]
  rw [himage]
  exact isClosed_iUnion_of_finite fun i =>
    hclosed i W hW g _ (hC.preimage (continuous_pointsMap B S hS (r i)))

/-! ### Stacks 0CZH -/

/-- **Stacks 0CZH.** A finite union of closed subsets of the points of `X`, each proper over
`Y`, is proper over `Y`. -/
@[stacks 0CZH]
theorem isProperOver_iUnion {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    {ι : Type v} [Finite ι] (T : ι → Set (points B S hS X))
    (hT : ∀ i, IsClosed (T i))
    (hproper : ∀ i, IsProperOver B S hS hX hY f hf (T i) (hT i)) :
    IsProperOver B S hS hX hY f hf (⋃ i, T i) (isClosed_iUnion_of_finite hT) := by
  classical
  have hU : IsClosed (⋃ i, T i) := isClosed_iUnion_of_finite hT
  let Z : Subfunctor X := reducedClosedSubspace B S hS X hX (⋃ i, T i) hU
  let Zi : ι → Subfunctor X := fun i => reducedClosedSubspace B S hS X hX (T i) (hT i)
  have hZAlg : IsAlgebraicSpace B S hS Z.toFunctor :=
    (isClosedSubspace_reducedClosedSubspace' B S hS hX (⋃ i, T i) hU).1
  have hZCI : IsClosedImmersion B S hS Z.ι :=
    (isClosedSubspace_reducedClosedSubspace' B S hS hX (⋃ i, T i) hU).2
  have hZrange : Set.range (pointsMap B S hS Z.toFunctor Z.ι) = ⋃ i, T i :=
    range_pointsMap_ι_reducedClosedSubspace B S hS X hX (⋃ i, T i) hU
  have hZiAlg : ∀ i, IsAlgebraicSpace B S hS (Zi i).toFunctor := fun i =>
    (isClosedSubspace_reducedClosedSubspace' B S hS hX (T i) (hT i)).1
  have hZiCI : ∀ i, IsClosedImmersion B S hS (Zi i).ι := fun i =>
    (isClosedSubspace_reducedClosedSubspace' B S hS hX (T i) (hT i)).2
  have hZiRed : ∀ i, HasEtaleLocalProperty B S hS (Zi i).toFunctor
      (fun W : Scheme.{u} => IsReduced W) := fun i =>
    hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X hX (T i) (hT i)
  have hZirange : ∀ i, Set.range (pointsMap B S hS (Zi i).toFunctor (Zi i).ι) = T i := fun i =>
    range_pointsMap_ι_reducedClosedSubspace B S hS X hX (T i) (hT i)
  have hlift : ∀ i, ∃ w : (Zi i).toFunctor ⟶ Z.toFunctor, w ≫ Z.ι = (Zi i).ι := by
    intro i
    refine (exists_lift_reducedClosedSubspace_iff_pointsMap_range_subset B S hS X hX
      (⋃ i, T i) hU (hZiAlg i) (hZiRed i) (Zi i).ι).2 ?_
    rw [hZirange i]
    exact Set.subset_iUnion T i
  choose u hu using hlift
  have huCI : ∀ i, IsClosedImmersion B S hS (u i) := fun i =>
    isClosedImmersion_of_comp_of_isSeparated B S hS (u i) Z.ι
      (by rw [hu i]; exact hZiCI i)
      (isSeparated_of_isClosedImmersion B S hS Z.ι hZCI)
  have hqLFT : IsLocallyOfFiniteType B S hS (Z.ι ≫ f) :=
    isLocallyOfFiniteType_comp B S hS hZAlg hX hY Z.ι f
      (isLocallyOfFiniteType_ι_reducedClosedSubspace B S hS X hX (⋃ i, T i) hU) hf
  have hqPieces : ∀ i, IsProper B S hS (u i ≫ Z.ι ≫ f) := by
    intro i
    rw [← Category.assoc, hu i]
    exact hproper i
  have hcover : ∀ z : points B S hS Z.toFunctor, ∃ i zi,
      pointsMap B S hS (Zi i).toFunctor (u i) zi = z := by
    intro z
    have hzU : pointsMap B S hS Z.toFunctor Z.ι z ∈ ⋃ i, T i := by
      rw [← hZrange]; exact ⟨z, rfl⟩
    obtain ⟨i, hzT⟩ := Set.mem_iUnion.mp hzU
    have hzmem : pointsMap B S hS Z.toFunctor Z.ι z ∈
        Set.range (pointsMap B S hS (Zi i).toFunctor (Zi i).ι) := by
      rw [hZirange i]; exact hzT
    obtain ⟨zi, hzieq⟩ := hzmem
    refine ⟨i, zi, pointsMap_injective_of_mono B S hS Z.ι ?_⟩
    calc pointsMap B S hS Z.toFunctor Z.ι (pointsMap B S hS (Zi i).toFunctor (u i) zi)
        = pointsMap B S hS (Zi i).toFunctor (u i ≫ Z.ι) zi := by rw [pointsMap_comp]; rfl
      _ = pointsMap B S hS (Zi i).toFunctor (Zi i).ι zi := by rw [hu i]
      _ = pointsMap B S hS Z.toFunctor Z.ι z := hzieq
  have hD : IsAlgebraicSpace B S hS (pullback (Z.ι ≫ f) (Z.ι ≫ f)) :=
    isAlgebraicSpace_pullback B S hS (Z.ι ≫ f) (Z.ι ≫ f) hZAlg hZAlg hY
  have hdiagCI : ∀ i, IsClosedImmersion B S hS (u i ≫ pullback.diagonal (Z.ι ≫ f)) := by
    intro i
    obtain ⟨m₂, hm₂fst, hm₂snd, hm₂sq⟩ :=
      exists_pullback_comparison B S hS (Z.ι ≫ f) (Z.ι ≫ f) (u i)
    obtain ⟨m₁, hm₁fst, hm₁snd, hm₁sq⟩ :=
      exists_pullback_comparison' B S hS (u i ≫ Z.ι ≫ f) (Z.ι ≫ f) (u i)
    have heq : pullback.diagonal (u i ≫ Z.ι ≫ f) ≫ m₁ ≫ m₂ =
        u i ≫ pullback.diagonal (Z.ι ≫ f) := by
      apply pullback.hom_ext <;>
        simp [hm₁fst, hm₂fst, hm₂snd, reassoc_of% hm₁snd]
    rw [← heq]
    exact isClosedImmersion_comp B S hS _ _ (hqPieces i).1
      (isClosedImmersion_comp B S hS m₁ m₂
        (isClosedImmersion_snd_of_isPullback B S hS hm₁sq (huCI i))
        (isClosedImmersion_snd_of_isPullback B S hS hm₂sq.flip (huCI i)))
  have hqSep : IsSeparated B S hS (Z.ι ≫ f) :=
    isSeparated_of_diagonal_charts B S hS (Z.ι ≫ f)
      (presheaf_locallyOfFiniteType_pullbackDiagonal B S hS (Z.ι ≫ f) hZAlg)
      ((presheaf_universallyClosed_iff B S hS hZAlg hD
          (relativelyRepresentable_pullbackDiagonal B S hS (Z.ι ≫ f) hZAlg)).2
        (universallyClosed_of_finite_cover B S hS hZAlg hD (fun i => (Zi i).toFunctor)
          hZiAlg u hcover (pullback.diagonal (Z.ι ≫ f)) fun i =>
            universallyClosed_of_isClosedImmersion B S hS (hZiAlg i) hD _ (hdiagCI i)))
  have hqQC : IsQuasiCompact B S hS (Z.ι ≫ f) :=
    isQuasiCompact_of_finite_cover B S hS hZAlg hY (fun i => (Zi i).toFunctor) hZiAlg u
      hcover (Z.ι ≫ f) fun i => (hqPieces i).2.1.2
  have hqUC : UniversallyClosed B S hS (Z.ι ≫ f) :=
    universallyClosed_of_finite_cover B S hS hZAlg hY (fun i => (Zi i).toFunctor) hZiAlg u
      hcover (Z.ι ≫ f) fun i => (hqPieces i).2.2
  exact ⟨hqSep, ⟨hqLFT, hqQC⟩, hqUC⟩

end AlgebraicGeometry.Space

end
