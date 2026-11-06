module

public import StacksFrontier.AlgebraicGeometry.Spaces.ContractedPieceConstantValue
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.GeneralLinearTwoPowerOrbitRigidity
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ProjectiveLineKernelPairAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ProjectiveLinePowerClosedPointFibre

/-!
# The contraction process of Stacks 0AEM over an algebraically closed field

Over an algebraically closed field `K` every morphism from a finite power of the projective line
to an algebraic space separated and locally of finite type over `Spec K` factors through the
projection onto some subset of the coordinates by a morphism all of whose fibres on points are
finite. This file assembles that from the pieces, and is the whole of the contraction process
the proof of [Stacks, Tag 0AEM] runs over the algebraic closure.

**One step.** Suppose the fibres of `g : (ℙ¹_K)^m ⟶ Z` on points are not all finite. Then

* some *closed* point of `|Z|` has an infinite fibre
  (`AlgebraicGeometry.Space.exists_isClosed_singleton_infinite_fibre_projectiveLinePower`);
* above it sits an irreducible closed subset of `|(ℙ¹_K)^m|` whose reduced closed subspace `C`
  is carried into that one point, together with two *distinct* `K`-rational points `x ≠ y` of
  `(ℙ¹_K)^m` factoring through `C`
  (`Space.exists_reducedClosedSubspace_pair_ne_of_infinite_fibre_projectiveLinePower`);
* the one point is a `K`-rational point of `Z`
  (`AlgebraicGeometry.Space.exists_rationalPoint_comp_eq_of_range_pointsMap_subset_singleton`),
  which is the hypothesis `hconst` the contraction step is stated with;
* therefore `f(M · x) = f(M · y)` for every `m`-tuple `M` of invertible two-by-two matrices
  (`AlgebraicGeometry.Space.comp_matrixAut_eq_of_contractedPiece`, which spends
  [Stacks, Tag 0AEJ] and the rigidity of the group action);
* and therefore `g` factors through the projection onto the set `S` of coordinates on which `x`
  and `y` agree
  (`AlgebraicGeometry.Space.exists_coordinateProjection_comp_eq_of_comp_matrixAut_eq`, the
  orbit-density exercise). That set is a *proper* subset, since `x ≠ y`.

**The iteration** is
`AlgebraicGeometry.Space.exists_coordinateProjection_finite_fibres_of_contraction_step`, whose
hypothesis `step` is the above read on the power indexed by a subset `I ⊆ Fin n` of the
coordinates. Reindexing that power by `Fin (Nat.card I)` is done by hand with two mutually
inverse `CategoryTheory.Limits.Pi.map'`s along the chosen bijection, so that the subset produced
by the step at `Fin (Nat.card I)` is transported back to a subset of `I` and the projections
compose on the nose.

## Main results

* `AlgebraicGeometry.Space.exists_coordinateProjection_ne_univ_of_not_forall_finite`: **one
  contraction step**, at the power indexed by `Fin m`.
* `AlgebraicGeometry.Space.exists_subsetProjection_ne_of_not_forall_finite`: the same at the
  power indexed by a subset of `Fin n`, which is the shape the iteration consumes.
* `AlgebraicGeometry.Space.exists_coordinateProjection_finite_fibres_of_isAlgClosed`: **the
  contraction process of [Stacks, Tag 0AEM] over an algebraically closed field.**

## References

* [Stacks Project, Tag 0AEJ](https://stacks.math.columbia.edu/tag/0AEJ)
* [Stacks Project, Tag 0AEL](https://stacks.math.columbia.edu/tag/0AEL)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (K : Type u) [Field K] [IsAlgClosed K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (CommRingCat.of K)))

/-! ### One contraction step -/

/-- **One contraction step of [Stacks, Tag 0AEM].** Let `K` be algebraically closed, let `Z` be
an algebraic space over `Spec K` separated and locally of finite type over `Spec K`, and let
`g : (ℙ¹_K)^m ⟶ Z` have a fibre on points which is not finite. Then `g` factors through the
projection onto a *proper* subset of the coordinates.

The subset is the set of coordinates on which the two distinct rational points of the contracted
piece agree. -/
theorem exists_coordinateProjection_ne_univ_of_not_forall_finite (m : ℕ)
    {Z : (BigFppfOver B (Spec (CommRingCat.of K)) hK)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of K)) hK Z)
    (z : Z ⟶ baseFunctor K B hK)
    (hz_sep : IsSeparated B (Spec (CommRingCat.of K)) hK z)
    (hz_lft : IsLocallyOfFiniteType B (Spec (CommRingCat.of K)) hK z)
    (g : projectiveLinePower K B hK (Fin m) ⟶ Z)
    (hnot : ¬ ∀ w : points B (Spec (CommRingCat.of K)) hK Z,
      {p : points B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK (Fin m)) |
        pointsMap B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK (Fin m)) g p =
          w}.Finite) :
    ∃ S : Finset (Fin m), S ≠ Finset.univ ∧
      ∃ g' : projectiveLinePower K B hK S ⟶ Z, g = coordinateProjection K B hK m S ≫ g' := by
  classical
  obtain ⟨w, hwclosed, hwinf⟩ :=
    exists_isClosed_singleton_infinite_fibre_projectiveLinePower K B hK (Fin m) hZ z hz_sep g
      hnot
  obtain ⟨C, hCclosed, x, y, hCirr, hCrange, hx, hy, hxy⟩ :=
    exists_reducedClosedSubspace_pair_ne_of_infinite_fibre_projectiveLinePower B K hK m g w
      hwclosed hwinf
  obtain ⟨lx, hlx⟩ := hx
  obtain ⟨ζ, hζ⟩ := exists_rationalPoint_comp_eq_of_range_pointsMap_subset_singleton K B hK hZ z
    hz_lft
    (isAlgebraicSpace_reducedClosedSubspace B (Spec (CommRingCat.of K)) hK
      (projectiveLinePower K B hK (Fin m))
      (isAlgebraicSpace_projectiveLinePowerFin K B hK m) C hCclosed)
    (hasEtaleLocalProperty_isReduced_reducedClosedSubspace B (Spec (CommRingCat.of K)) hK
      (projectiveLinePower K B hK (Fin m))
      (isAlgebraicSpace_projectiveLinePowerFin K B hK m) C hCclosed)
    (_ ≫ g) w hwclosed hCrange lx
  have hagree := fun M => comp_matrixAut_eq_of_contractedPiece K B hK m z g
    (reducedClosedSubspace B (Spec (CommRingCat.of K)) hK
      (projectiveLinePower K B hK (Fin m))
      (isAlgebraicSpace_projectiveLinePowerFin K B hK m) C hCclosed) ζ x y hZ hz_sep hz_lft
    (isClosedSubspace_reducedClosedSubspace B (Spec (CommRingCat.of K)) hK
      (projectiveLinePower K B hK (Fin m))
      (isAlgebraicSpace_projectiveLinePowerFin K B hK m) C hCclosed)
    hζ
    (preirreducibleSpace_points_reducedClosedSubspace B (Spec (CommRingCat.of K)) hK
      (projectiveLinePower K B hK (Fin m))
      (isAlgebraicSpace_projectiveLinePowerFin K B hK m) C hCclosed hCirr.2)
    ⟨lx, hlx⟩ hy M
  letI : DecidablePred fun i : Fin m =>
      x ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) i =
        y ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) i :=
    fun _ => Classical.propDecidable _
  refine ⟨Finset.univ.filter fun i =>
      x ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) i =
        y ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) i, ?_, ?_⟩
  · obtain ⟨j, hj⟩ : ∃ j : Fin m,
        x ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) j ≠
          y ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) j := by
      by_contra hcon
      exact hxy (Pi.hom_ext _ _ fun i => not_not.1 fun h => hcon ⟨i, h⟩)
    intro hfull
    have hmem : j ∈ Finset.univ.filter fun i =>
        x ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) i =
          y ≫ Pi.π (fun _ : Fin m => projectiveLineFunctor K B hK) i := by
      rw [hfull]
      exact Finset.mem_univ j
    exact hj (Finset.mem_filter.1 hmem).2
  · exact exists_coordinateProjection_comp_eq_of_comp_matrixAut_eq K B hK m hZ z hz_sep g x y hxy
      _ (fun i => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) hagree

/-! ### The step at the power indexed by a subset of the coordinates -/

/-- **One contraction step of [Stacks, Tag 0AEM] at the power indexed by a subset `I ⊆ Fin n` of
the coordinates**, which is the shape the iteration
`AlgebraicGeometry.Space.exists_coordinateProjection_finite_fibres_of_contraction_step`
consumes.

The power indexed by `I` is reindexed by `Fin (Nat.card I)` along the chosen bijection, by two
mutually inverse reindexing morphisms; the subset of `Fin (Nat.card I)` the step at that power
produces is carried back to a subset of `I` of the same cardinality, which is therefore a proper
subset, and the projections compose on the nose. -/
theorem exists_subsetProjection_ne_of_not_forall_finite {n : ℕ} (I : Finset (Fin n))
    {Z : (BigFppfOver B (Spec (CommRingCat.of K)) hK)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of K)) hK Z)
    (z : Z ⟶ baseFunctor K B hK)
    (hz_sep : IsSeparated B (Spec (CommRingCat.of K)) hK z)
    (hz_lft : IsLocallyOfFiniteType B (Spec (CommRingCat.of K)) hK z)
    (g : projectiveLinePower K B hK I ⟶ Z)
    (hnot : ¬ ∀ w : points B (Spec (CommRingCat.of K)) hK Z,
      {p : points B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK I) |
        pointsMap B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK I) g p =
          w}.Finite) :
    ∃ (J : Finset (Fin n)) (hJI : J ⊆ I), J ≠ I ∧
      ∃ g' : projectiveLinePower K B hK J ⟶ Z, g = subsetProjection K B hK hJI ≫ g' := by
  classical
  set m := Nat.card I with hm
  set e : I ≃ Fin m := Finite.equivFin I with he
  -- the two reindexing morphisms between the power indexed by `I` and the one indexed by `Fin m`
  have hPQ : Pi.map' (fun i : Fin m => e.symm i)
        (fun _ => 𝟙 (projectiveLineFunctor K B hK)) ≫
      Pi.map' (fun i : I => e i) (fun _ => 𝟙 (projectiveLineFunctor K B hK)) =
    𝟙 (projectiveLinePower K B hK I) := by
    refine Pi.hom_ext _ _ fun a => ?_
    rw [Category.assoc, Pi.map'_comp_π, Category.comp_id, Pi.map'_comp_π, Category.comp_id,
      Category.id_comp, e.symm_apply_apply]
  have hQP : Pi.map' (fun i : I => e i) (fun _ => 𝟙 (projectiveLineFunctor K B hK)) ≫
      Pi.map' (fun i : Fin m => e.symm i) (fun _ => 𝟙 (projectiveLineFunctor K B hK)) =
    𝟙 (projectiveLinePower K B hK (Fin m)) := by
    refine Pi.hom_ext _ _ fun a => ?_
    rw [Category.assoc, Pi.map'_comp_π, Category.comp_id, Pi.map'_comp_π, Category.comp_id,
      Category.id_comp, e.apply_symm_apply]
  -- the fibres of the reindexed morphism are not all finite either
  have hnot' : ¬ ∀ w : points B (Spec (CommRingCat.of K)) hK Z,
      {p : points B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK (Fin m)) |
        pointsMap B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK (Fin m))
          (Pi.map' (fun i : I => e i) (fun _ => 𝟙 (projectiveLineFunctor K B hK)) ≫ g) p =
            w}.Finite := by
    intro hfin
    refine hnot fun w => ?_
    have hid := pointsMap_comp B (Spec (CommRingCat.of K)) hK
      (projectiveLinePower K B hK I)
      (Pi.map' (fun i : Fin m => e.symm i) (fun _ => 𝟙 (projectiveLineFunctor K B hK)))
      (Pi.map' (fun i : I => e i) (fun _ => 𝟙 (projectiveLineFunctor K B hK)))
    rw [hPQ, pointsMap_id] at hid
    have hsub : {p : points B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK I) |
          pointsMap B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK I) g p = w} ⊆
        pointsMap B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK (Fin m))
            (Pi.map' (fun i : I => e i) (fun _ => 𝟙 (projectiveLineFunctor K B hK))) ''
          {p : points B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK (Fin m)) |
            pointsMap B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK (Fin m))
              (Pi.map' (fun i : I => e i) (fun _ => 𝟙 (projectiveLineFunctor K B hK)) ≫ g) p =
                w} := by
      intro p hp
      refine ⟨pointsMap B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK I)
        (Pi.map' (fun i : Fin m => e.symm i)
          (fun _ => 𝟙 (projectiveLineFunctor K B hK))) p, ?_, ?_⟩
      · show pointsMap B (Spec (CommRingCat.of K)) hK _ _ _ = w
        rw [pointsMap_comp B (Spec (CommRingCat.of K)) hK _ _ g, Function.comp_apply,
          ← Function.comp_apply (f := pointsMap B (Spec (CommRingCat.of K)) hK
            (projectiveLinePower K B hK (Fin m))
            (Pi.map' (fun i : I => e i) (fun _ => 𝟙 (projectiveLineFunctor K B hK)))),
          ← hid]
        exact hp
      · rw [← Function.comp_apply (f := pointsMap B (Spec (CommRingCat.of K)) hK
          (projectiveLinePower K B hK (Fin m))
          (Pi.map' (fun i : I => e i) (fun _ => 𝟙 (projectiveLineFunctor K B hK)))), ← hid]
        rfl
    exact Set.Finite.subset ((hfin w).image _) hsub
  obtain ⟨S, hSne, g', hg'⟩ := exists_coordinateProjection_ne_univ_of_not_forall_finite K B hK m
    hZ z hz_sep hz_lft
    (Pi.map' (fun i : I => e i) (fun _ => 𝟙 (projectiveLineFunctor K B hK)) ≫ g) hnot'
  -- the subset of `I` the step produces
  refine ⟨S.image fun t : Fin m => ((e.symm t : I) : Fin n), ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hj
    exact (e.symm t).2
  · have hinj : Function.Injective fun t : Fin m => ((e.symm t : I) : Fin n) :=
      fun a b h => e.symm.injective (Subtype.ext h)
    have hcard : (S.image fun t : Fin m => ((e.symm t : I) : Fin n)).card < I.card := by
      rw [Finset.card_image_of_injective S hinj]
      have hIcard : I.card = m := by
        rw [hm, Nat.card_eq_fintype_card, Fintype.card_coe]
      rw [hIcard]
      calc S.card < (Finset.univ : Finset (Fin m)).card :=
            Finset.card_lt_card (lt_of_le_of_ne (Finset.subset_univ S) hSne)
        _ = m := Finset.card_univ.trans (Fintype.card_fin m)
    exact fun hcon => absurd (hcon ▸ hcard) (lt_irrefl _)
  · refine ⟨Pi.map' (fun s : S =>
      (⟨((e.symm (s : Fin m) : I) : Fin n), Finset.mem_image_of_mem _ s.2⟩ :
        (S.image fun t : Fin m => ((e.symm t : I) : Fin n)))) (fun _ => 𝟙 _) ≫ g', ?_⟩
    have hkey : Pi.map' (fun i : Fin m => e.symm i)
            (fun _ => 𝟙 (projectiveLineFunctor K B hK)) ≫
          coordinateProjection K B hK m S =
        subsetProjection K B hK
            (show (S.image fun t : Fin m => ((e.symm t : I) : Fin n)) ⊆ I from fun j hj => by
              obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hj
              exact (e.symm t).2) ≫
          Pi.map' (fun s : S =>
            (⟨((e.symm (s : Fin m) : I) : Fin n), Finset.mem_image_of_mem _ s.2⟩ :
              (S.image fun t : Fin m => ((e.symm t : I) : Fin n)))) (fun _ => 𝟙 _) := by
      refine Pi.hom_ext _ _ fun s => ?_
      rw [Category.assoc, Pi.map'_comp_π, Category.comp_id, Pi.map'_comp_π, Category.comp_id,
        Category.assoc, Pi.map'_comp_π, Category.comp_id, Pi.map'_comp_π, Category.comp_id]
    calc g = (Pi.map' (fun i : Fin m => e.symm i)
            (fun _ => 𝟙 (projectiveLineFunctor K B hK)) ≫
          Pi.map' (fun i : I => e i) (fun _ => 𝟙 (projectiveLineFunctor K B hK))) ≫ g := by
          rw [hPQ, Category.id_comp]
      _ = Pi.map' (fun i : Fin m => e.symm i) (fun _ => 𝟙 (projectiveLineFunctor K B hK)) ≫
            (Pi.map' (fun i : I => e i) (fun _ => 𝟙 (projectiveLineFunctor K B hK)) ≫ g) :=
          Category.assoc _ _ _
      _ = Pi.map' (fun i : Fin m => e.symm i) (fun _ => 𝟙 (projectiveLineFunctor K B hK)) ≫
            coordinateProjection K B hK m S ≫ g' := by rw [hg']
      _ = (Pi.map' (fun i : Fin m => e.symm i) (fun _ => 𝟙 (projectiveLineFunctor K B hK)) ≫
            coordinateProjection K B hK m S) ≫ g' := (Category.assoc _ _ _).symm
      _ = _ := by rw [hkey, Category.assoc]

/-! ### The contraction process -/

/-- **The contraction process of [Stacks, Tag 0AEM] over an algebraically closed field.** Let
`K` be algebraically closed, let `Z` be an algebraic space over `Spec K` separated and locally
of finite type over `Spec K` and let `w : (ℙ¹_K)^n ⟶ Z`. Then `w` factors through the projection
onto the coordinates in some subset `I ⊆ Fin n` by a morphism all of whose fibres on points are
finite.

This is
`AlgebraicGeometry.Space.exists_coordinateProjection_finite_fibres_of_contraction_step` with its
hypothesis `step` discharged by
`AlgebraicGeometry.Space.exists_subsetProjection_ne_of_not_forall_finite`. -/
theorem exists_coordinateProjection_finite_fibres_of_isAlgClosed (n : ℕ)
    {Z : (BigFppfOver B (Spec (CommRingCat.of K)) hK)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of K)) hK Z)
    (z : Z ⟶ baseFunctor K B hK)
    (hz_sep : IsSeparated B (Spec (CommRingCat.of K)) hK z)
    (hz_lft : IsLocallyOfFiniteType B (Spec (CommRingCat.of K)) hK z)
    (w : projectiveLinePower K B hK (Fin n) ⟶ Z) :
    ∃ (I : Finset (Fin n)) (g : projectiveLinePower K B hK I ⟶ Z),
      w = coordinateProjection K B hK n I ≫ g ∧
        ∀ y : points B (Spec (CommRingCat.of K)) hK Z,
          {p : points B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK I) |
            pointsMap B (Spec (CommRingCat.of K)) hK (projectiveLinePower K B hK I) g p =
              y}.Finite :=
  exists_coordinateProjection_finite_fibres_of_contraction_step
    (fun I g hg => exists_subsetProjection_ne_of_not_forall_finite K B hK I hZ z hz_sep hz_lft g
      hg)
    w

end AlgebraicGeometry.Space

end
