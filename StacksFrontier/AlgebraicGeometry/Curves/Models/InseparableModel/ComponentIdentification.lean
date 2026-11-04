module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.Model
public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.ComponentRange
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricComponents
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.Immersions

/-!
# A regular model with an inseparable component: the irreducible components of the special fibre

The special fibre `X_k` of `Stacks.Models.InseparableModel.situation` has exactly two irreducible
components, and their reduced closed subschemes of `X` are the images of the closed immersions
`jC₁ : ℙ¹_k ⟶ X` and `jE : ℙ¹_κ ⟶ X`.

## Main results

* `Stacks.Models.InseparableModel.specialFiber_components`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Stacks.Models.InseparableModel

/-! ### Two irreducible closed sets covering the range of an embedding -/

/-- If the range of `f` is the union of closed sets `P` and `Q`, the image of an irreducible set
lies in `P` or in `Q`. -/
private theorem image_subset_or_of_range_eq_union {A Y : Type*}
    [TopologicalSpace A] [TopologicalSpace Y] {f : A → Y} (hf : Continuous f) {P Q : Set Y}
    (hPc : IsClosed P) (hQc : IsClosed Q) (hr : Set.range f = P ∪ Q) {T : Set A}
    (hT : IsIrreducible T) : f '' T ⊆ P ∨ f '' T ⊆ Q :=
  isPreirreducible_iff_isClosed_union_isClosed.mp (hT.image f hf.continuousOn).2 P Q hPc hQc
    (hr ▸ Set.image_subset_range f T)

/-- Let `f : A → Y` be an embedding into a quasi-sober space whose range is the union of two
irreducible closed sets `P` and `Q`, neither contained in the other. Then `f⁻¹ P` is an
irreducible component of `A`: it is irreducible because `P` lies in the range, and an irreducible
set containing it has irreducible image inside `P ∪ Q`, hence inside `P`, since inside `Q` would
force `P ⊆ Q`. -/
private theorem preimage_mem_irreducibleComponents_of_range_eq_union {A Y : Type*}
    [TopologicalSpace A] [TopologicalSpace Y] [QuasiSober Y] {f : A → Y}
    (hf : Topology.IsEmbedding f) {P Q : Set Y} (hP : IsIrreducible P) (hPc : IsClosed P)
    (hQc : IsClosed Q) (hr : Set.range f = P ∪ Q) (hPQ : ¬ P ⊆ Q) :
    f ⁻¹' P ∈ irreducibleComponents A := by
  have hPr : P ⊆ Set.range f := hr ▸ Set.subset_union_left
  refine ⟨isIrreducible_preimage_of_isEmbedding hf hP hPc hPr, fun T hT hPT => ?_⟩
  rcases image_subset_or_of_range_eq_union hf.continuous hPc hQc hr hT with h | h
  · exact Set.image_subset_iff.mp h
  · refine absurd ?_ hPQ
    rw [← Set.image_preimage_eq_of_subset hPr]
    exact (Set.image_mono hPT).trans h

/-- In the situation of `preimage_mem_irreducibleComponents_of_range_eq_union`, every
irreducible component of `A` is `f⁻¹ P` or `f⁻¹ Q`: its image lies in `P` or in `Q`, so it lies
in the irreducible set `f⁻¹ P` or `f⁻¹ Q`, and is then equal to it by maximality. -/
private theorem eq_or_eq_of_range_eq_union {A Y : Type*}
    [TopologicalSpace A] [TopologicalSpace Y] [QuasiSober Y] {f : A → Y}
    (hf : Topology.IsEmbedding f) {P Q : Set Y} (hP : IsIrreducible P) (hPc : IsClosed P)
    (hQ : IsIrreducible Q) (hQc : IsClosed Q) (hr : Set.range f = P ∪ Q) {Z : Set A}
    (hZ : Z ∈ irreducibleComponents A) : Z = f ⁻¹' P ∨ Z = f ⁻¹' Q := by
  rcases image_subset_or_of_range_eq_union hf.continuous hPc hQc hr hZ.1 with h | h
  · refine Or.inl (Set.Subset.antisymm (Set.image_subset_iff.mp h) ?_)
    exact hZ.2 (isIrreducible_preimage_of_isEmbedding hf hP hPc
      (hr ▸ Set.subset_union_left)) (Set.image_subset_iff.mp h)
  · refine Or.inr (Set.Subset.antisymm (Set.image_subset_iff.mp h) ?_)
    exact hZ.2 (isIrreducible_preimage_of_isEmbedding hf hQ hQc
      (hr ▸ Set.subset_union_right)) (Set.image_subset_iff.mp h)

/-! ### The special fibre as a subset of the model -/

/-- Every point of `Spec k` maps to the closed point of `Spec R`. -/
private theorem Spec_algebraMap_Rk_apply (p : Spec (.of k)) :
    (Spec.map (CommRingCat.ofHom (algebraMap R k))).base p = IsLocalRing.closedPoint R := by
  obtain rfl : p = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  have : IsLocalHom (algebraMap R k) := algebraMap_Rk_surjective.isLocalHom
  exact Spec_closedPoint (f := CommRingCat.ofHom (algebraMap R k))

/-- The image of the special fibre in `X` is the fibre of `X ⟶ Spec R` over the closed point. -/
private theorem range_specialFiberι :
    Set.range situation.specialFiberι.base = X_to_R.base ⁻¹' {IsLocalRing.closedPoint R} := by
  have hrange : Set.range (Spec.map (CommRingCat.ofHom (algebraMap R k))).base =
      {IsLocalRing.closedPoint R} := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨IsLocalRing.closedPoint k,
      Spec_algebraMap_Rk_apply _⟩, ?_⟩
    rintro x ⟨p, rfl⟩
    exact Spec_algebraMap_Rk_apply p
  rw [← hrange]
  exact Scheme.Pullback.range_fst X_to_R (Spec.map (CommRingCat.ofHom (algebraMap R k)))

/-- **The image of the special fibre is the union of the two lines.** -/
private theorem range_specialFiberι_eq_union :
    Set.range situation.specialFiberι.base = Set.range jC₁.base ∪ Set.range jE.base := by
  rw [range_specialFiberι]
  ext x
  refine ⟨fun hx => mem_range_jC₁_or_mem_range_jE x hx, ?_⟩
  rintro (⟨y, rfl⟩ | ⟨y, rfl⟩)
  · show (jC₁ ≫ X_to_R).base y = _
    rw [jC₁_comp_X_to_R, Scheme.Hom.comp_apply]
    exact Spec_algebraMap_Rk_apply _
  · show (jE ≫ X_to_R).base y = _
    rw [jE_comp_X_to_R, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact Spec_algebraMap_Rk_apply _

/-- The range of a closed immersion from an irreducible scheme is irreducible and closed. -/
private theorem isIrreducible_range {Y Z : Scheme} [IrreducibleSpace Y] (j : Y ⟶ Z)
    [IsClosedImmersion j] : IsIrreducible (Set.range j.base) ∧ IsClosed (Set.range j.base) := by
  refine ⟨?_, j.isClosedEmbedding.isClosed_range⟩
  rw [← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ Y).image _ j.continuous.continuousOn

/-- The component ideal of the special-fibre component `ι⁻¹(range j)` of a regular model is the
kernel of `j`, for a closed immersion `j` of a reduced scheme into the model whose range lies in
the special fibre: both are the reduced ideal of the closed set `range j`. -/
private theorem specialFiberComponentIdeal_eq_ker (S : RegularProperModelSituation.{0})
    {Y : Scheme.{0}} [IsReduced Y] (j : Y ⟶ S.X) [IsClosedImmersion j]
    (hj : Set.range j.base ⊆ Set.range S.specialFiberι.base)
    (Z : irreducibleComponents S.specialFiber)
    (hZ : (Z : Set S.specialFiber) = S.specialFiberι.base ⁻¹' Set.range j.base) :
    S.specialFiberComponentIdeal Z = j.ker := by
  have hclosed := j.isClosedEmbedding.isClosed_range
  have hC : TopologicalSpace.Closeds.closure
      (S.specialFiberι.base '' (Z : Set S.specialFiber)) = j.ker.support := by
    apply TopologicalSpace.Closeds.ext
    rw [TopologicalSpace.Closeds.coe_closure, hZ, Set.image_preimage_eq_of_subset hj,
      Scheme.Hom.support_ker]
  rw [ker_eq_vanishingIdeal_of_reduced_closed_immersion j, ← hC]

/-- **The two components of the special fibre.** -/
theorem specialFiber_components :
    ∃ ZC ZE : irreducibleComponents situation.specialFiber, ZC ≠ ZE ∧ (∀ Z, Z = ZC ∨ Z = ZE) ∧
      situation.specialFiberComponentIdeal ZC = jC₁.ker ∧
      situation.specialFiberComponentIdeal ZE = jE.ker := by
  have hemb := situation.specialFiberι.isClosedEmbedding.isEmbedding
  obtain ⟨hCi, hCc⟩ := isIrreducible_range jC₁
  obtain ⟨hEi, hEc⟩ := isIrreducible_range jE
  have hr := range_specialFiberι_eq_union
  have hCE : ¬ Set.range jC₁.base ⊆ Set.range jE.base := fun h => by
    obtain ⟨x, hx, hx'⟩ := exists_mem_range_jC₁_notMem_range_jE
    exact hx' (h hx)
  have hEC : ¬ Set.range jE.base ⊆ Set.range jC₁.base := fun h => by
    obtain ⟨x, hx, hx'⟩ := exists_mem_range_jE_notMem_range_jC₁
    exact hx' (h hx)
  have hr' : Set.range situation.specialFiberι.base =
      Set.range jE.base ∪ Set.range jC₁.base := hr.trans (Set.union_comm _ _)
  let ZC : irreducibleComponents situation.specialFiber :=
    ⟨_, preimage_mem_irreducibleComponents_of_range_eq_union hemb hCi hCc hEc hr hCE⟩
  let ZE : irreducibleComponents situation.specialFiber :=
    ⟨_, preimage_mem_irreducibleComponents_of_range_eq_union hemb hEi hEc hCc hr' hEC⟩
  refine ⟨ZC, ZE, fun h => hCE ?_, fun Z => ?_, ?_, ?_⟩
  · exact Set.preimage_subset_preimage_iff (hr ▸ Set.subset_union_left) |>.mp
      (congrArg Subtype.val h).le
  · rcases eq_or_eq_of_range_eq_union hemb hCi hCc hEi hEc hr Z.2 with h | h
    · exact .inl (Subtype.ext h)
    · exact .inr (Subtype.ext h)
  · exact @specialFiberComponentIdeal_eq_ker situation _ _ jC₁ isClosedImmersion_jC₁
      (hr ▸ Set.subset_union_left) ZC rfl
  · exact @specialFiberComponentIdeal_eq_ker situation _ _ jE isClosedImmersion_jE
      (hr ▸ Set.subset_union_right) ZE rfl

end Stacks.Models.InseparableModel
