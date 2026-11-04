module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingGeneratorOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparationLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms

/-!
# Closed subspaces of finite presentation avoiding a quasi-compact set of points

Let `P` be a quasi-compact and quasi-separated algebraic space over a scheme `S` and `C ⊆ P` a
closed subspace. A closed subspace of finite presentation containing `C` can be chosen to miss
any prescribed quasi-compact set of points of `|P|` which `C` misses, and at the same time to
contain, on a quasi-compact étale chart, a prescribed finite type sheaf of ideals contained in the
ideal of `C`.

This is the point-set consequence of the ideal-sheaf form of Stacks 0829 compatible with a chart,
`AlgebraicGeometry.Space.exists_isFinitePresentation_le_chartKer`: a point off `C` lies on an
affine étale chart to which `C` does not base change at all
(`AlgebraicGeometry.Space.mem_idealUnitLocus_of_notMem_range_pointsMap_ι`), the unit ideal of
that chart is then a finite type sheaf of ideals contained in the ideal of `C`, and a closed
subspace of finite presentation containing `C` whose ideal on that chart is the unit ideal misses
the whole image of the chart. Quasi-compactness of the prescribed set lets finitely many such
closed subspaces do, and their intersection is again of finite presentation.

## Main results

* `AlgebraicGeometry.Space.exists_isFinitePresentation_disjoint_of_notMem`: one point.
* `AlgebraicGeometry.Space.exists_isFinitePresentation_disjoint_le_chartKer`: a quasi-compact set
  of points and a chart condition at once.

## References

* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] pointTopology

/-- A closed subspace whose ideal on a chart is the unit ideal misses the image of the chart. -/
theorem notMem_range_of_chartKer_eq_top (P : AlgebraicSpaces B S hS)
    (T : ClosedSubspaces B S hS P.1) {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ P.1)
    (hT : chartKer B S hS P T φ = ⊤) (w : points B S hS (yoneda.obj U)) :
    pointsMap B S hS (yoneda.obj U) φ w ∉ Set.range (pointsMap B S hS T.1.toFunctor T.1.ι) := by
  intro hw
  have hmem : w ∈ pointsMap B S hS (yoneda.obj U) φ ⁻¹'
      Set.range (pointsMap B S hS T.1.toFunctor T.1.ι) := hw
  rw [preimage_range_pointsMap_eq_range_pointsMap_snd B S hS T.2.2.rep φ] at hmem
  obtain ⟨t, -⟩ := hmem
  have hempty : IsEmpty ((BigFppfOver.toScheme B S hS).obj (T.2.2.rep.pullback φ)) :=
    (Scheme.Hom.ker_eq_top_iff_isEmpty _).1 hT
  exact hempty.elim (pointsToScheme B S hS (T.2.2.rep.pullback φ) t)

/-- **A point off a closed subspace is avoided by a closed subspace of finite presentation
containing it, on a whole open neighbourhood.** -/
theorem exists_isFinitePresentation_disjoint_of_notMem (P : AlgebraicSpaces B S hS)
    (hPqc : IsQuasiCompactSpace B S hS P.1) (hPqs : IsAbsolutelyQuasiSeparated B S hS hZ P.1)
    (C : ClosedSubspaces B S hS P.1) {k : points B S hS P.1}
    (hk : k ∉ Set.range (pointsMap B S hS C.1.toFunctor C.1.ι)) :
    ∃ (N : Set (points B S hS P.1)) (T : ClosedSubspaces B S hS P.1), IsOpen N ∧ k ∈ N ∧
      IsFinitePresentation B S hS T.1.ι ∧ C.1 ≤ T.1 ∧
      Disjoint N (Set.range (pointsMap B S hS T.1.toFunctor T.1.ι)) := by
  obtain ⟨U, hUaff, hUtop, hkU⟩ := exists_affine_chart_obj_eq_top_of_mem_idealUnitLocus B S hS P _
    (mem_idealUnitLocus_of_notMem_range_pointsMap_ι B S hS P C hk)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) := hUaff
  have hoff : ∀ p : points B S hS (yoneda.obj U.1.left), pointsMap B S hS _ U.1.hom p ∉
      Set.range (pointsMap B S hS C.1.toFunctor C.1.ι) := fun p =>
    notMem_range_pointsMap_ι_of_definingIdealSheaf_obj_eq_top B S hS P C _ rfl U hUaff hUtop
      ⟨p, rfl⟩
  have hCtop : chartKer B S hS P C U.1.hom = ⊤ :=
    (Scheme.Hom.ker_eq_top_iff_isEmpty _).2
      (isEmpty_pullback_of_forall_notMem_range B S hS P C U.1.hom hoff)
  obtain ⟨T, hTfp, hCT, hTtop⟩ := exists_isFinitePresentation_le_chartKer B S hS hZ P hPqc hPqs C
    U.1.hom U.2 ⊤ Stacks.FiniteTypeIdealSheaf.isFiniteType_top (le_of_eq hCtop.symm)
  refine ⟨Set.range (pointsMap B S hS (yoneda.obj U.1.left) U.1.hom), T,
    isOpen_range_pointsMap_of_isEtale B S hS U.1.hom (isAlgebraicSpace_yoneda B S hS _) P.2
      (isEtale_of_presheaf_etale B S hS U.2), hkU, hTfp, hCT, ?_⟩
  rw [Set.disjoint_left]
  rintro _ ⟨w, rfl⟩
  exact notMem_range_of_chartKer_eq_top B S hS P T U.1.hom (top_le_iff.1 hTtop) w

/-- The intersection of two closed subspaces of finite presentation is a closed subspace of
finite presentation. -/
theorem exists_inf_closedSubspaces (P : AlgebraicSpaces B S hS)
    (T₁ T₂ : ClosedSubspaces B S hS P.1) (h₁ : IsFinitePresentation B S hS T₁.1.ι)
    (h₂ : IsFinitePresentation B S hS T₂.1.ι) :
    ∃ T : ClosedSubspaces B S hS P.1, T.1 = T₁.1 ⊓ T₂.1 ∧ IsFinitePresentation B S hS T.1.ι :=
  ⟨⟨T₁.1 ⊓ T₂.1, inf_isClosedSubspace B S hS P.1 P.2 T₁ T₂⟩, rfl,
    isFinitePresentation_inf B S hS P.2 T₁.1 T₂.1 T₁.2 T₂.2
      (inf_isClosedSubspace B S hS P.1 P.2 T₁ T₂) h₁ h₂⟩

/-- **A closed subspace of finite presentation containing `C` can be chosen to miss a
quasi-compact set of points which `C` misses, and to satisfy a chart condition.** -/
theorem exists_isFinitePresentation_disjoint_le_chartKer (P : AlgebraicSpaces B S hS)
    (hPqc : IsQuasiCompactSpace B S hS P.1) (hPqs : IsAbsolutelyQuasiSeparated B S hS hZ P.1)
    (C : ClosedSubspaces B S hS P.1) (K : Set (points B S hS P.1)) (hK : IsCompact K)
    (hKC : Disjoint K (Set.range (pointsMap B S hS C.1.toFunctor C.1.ι)))
    {m : ℕ} {U : Fin m → BigFppfOver B S hS}
    [∀ i, CompactSpace ((BigFppfOver.toScheme B S hS).obj (U i))]
    (φ : ∀ i, yoneda.obj (U i) ⟶ P.1)
    (hφ : ∀ i, MorphismProperty.presheaf (MorphismProperty.inverseImage @Etale
      (BigFppfOver.toScheme B S hS)) (φ i))
    (J₀ : ∀ i, ((BigFppfOver.toScheme B S hS).obj (U i)).IdealSheafData)
    (hJ₀ : ∀ i, (J₀ i).IsFiniteType) (hJ₀C : ∀ i, J₀ i ≤ chartKer B S hS P C (φ i)) :
    ∃ T : ClosedSubspaces B S hS P.1, IsFinitePresentation B S hS T.1.ι ∧ C.1 ≤ T.1 ∧
      Disjoint K (Set.range (pointsMap B S hS T.1.toFunctor T.1.ι)) ∧
      ∀ i, J₀ i ≤ chartKer B S hS P T (φ i) := by
  classical
  -- For each point of `K`, an open neighbourhood and a closed subspace missing it.
  have hloc : ∀ k ∈ K, ∃ (N : Set (points B S hS P.1)) (T : ClosedSubspaces B S hS P.1),
      IsOpen N ∧ k ∈ N ∧ IsFinitePresentation B S hS T.1.ι ∧ C.1 ≤ T.1 ∧
      Disjoint N (Set.range (pointsMap B S hS T.1.toFunctor T.1.ι)) := fun k hk =>
    exists_isFinitePresentation_disjoint_of_notMem B S hS hZ P hPqc hPqs C
      (Set.disjoint_left.1 hKC hk)
  have : Nonempty (ClosedSubspaces B S hS P.1) := ⟨C⟩
  choose! N T hNo hkN hTfp hCT hNT using hloc
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover N fun k hk => (hNo k hk).mem_nhds (hkN k hk)
  -- The chart conditions, and one closed subspace of finite presentation containing `C`.
  obtain ⟨V, ψ, hVaff, -, hψe⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS P.1 P.2).1 hPqc
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hVaff
  obtain ⟨T₀, hT₀fp, hCT₀, -⟩ := exists_isFinitePresentation_le_chartKer B S hS hZ P hPqc hPqs C
    ψ ((isEtale_iff_presheaf_of_yoneda B S hS ψ).1 hψe) ⊥
    Stacks.FiniteTypeIdealSheaf.isFiniteType_bot bot_le
  have hchart : ∀ i, ∃ T : ClosedSubspaces B S hS P.1, IsFinitePresentation B S hS T.1.ι ∧
      C.1 ≤ T.1 ∧ J₀ i ≤ chartKer B S hS P T (φ i) := fun i =>
    exists_isFinitePresentation_le_chartKer B S hS hZ P hPqc hPqs C (φ i) (hφ i) (J₀ i) (hJ₀ i)
      (hJ₀C i)
  choose T' hT'fp hCT' hJT' using hchart
  -- The intersection of the finitely many closed subspaces.
  have key : ∀ s : Finset (ClosedSubspaces B S hS P.1),
      (∀ T ∈ s, IsFinitePresentation B S hS T.1.ι ∧ C.1 ≤ T.1) →
      ∃ T'' : ClosedSubspaces B S hS P.1, IsFinitePresentation B S hS T''.1.ι ∧ C.1 ≤ T''.1 ∧
        ∀ T ∈ s, T''.1 ≤ T.1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨T₀, hT₀fp, hCT₀, by simp⟩
    | insert a s ha ih =>
      intro hs
      obtain ⟨T'', hfp, hC'', hle⟩ := ih fun T hT => hs T (Finset.mem_insert_of_mem hT)
      obtain ⟨haf, haC⟩ := hs a (Finset.mem_insert_self a s)
      obtain ⟨T₃, h₃eq, h₃fp⟩ := exists_inf_closedSubspaces B S hS P T'' a hfp haf
      refine ⟨T₃, h₃fp, by rw [h₃eq]; exact le_inf hC'' haC, fun T hT => ?_⟩
      rw [h₃eq]
      rcases Finset.mem_insert.1 hT with rfl | hT
      · exact inf_le_right
      · exact inf_le_left.trans (hle T hT)
  obtain ⟨T'', hT''fp, hCT'', hT''s⟩ := key (t.image T ∪ Finset.univ.image T') (by
    intro T' hT'
    rcases Finset.mem_union.1 hT' with h | h
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h
      exact ⟨hTfp k (htK k hk), hCT k (htK k hk)⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      exact ⟨hT'fp i, hCT' i⟩)
  refine ⟨T'', hT''fp, hCT'', ?_, fun i => ?_⟩
  · rw [Set.disjoint_left]
    intro x hxK hxT
    obtain ⟨k, hkt, hxk⟩ := Set.mem_iUnion₂.1 (hcov hxK)
    exact Set.disjoint_left.1 (hNT k (htK k hkt)) hxk
      (range_pointsMap_ι_le B S hS
        (hT''s _ (Finset.mem_union_left _ (Finset.mem_image_of_mem T hkt))) hxT)
  · refine le_trans (hJT' i) ((le_chartKer_iff B S hS P T'' (φ i) _).2 ?_)
    exact le_trans (fun j x hx => hT''s (T' i) (Finset.mem_union_right _
      (Finset.mem_image_of_mem T' (Finset.mem_univ i))) _ hx)
      ((le_chartKer_iff B S hS P (T' i) (φ i) _).1 le_rfl)

end AlgebraicGeometry.Space

end
