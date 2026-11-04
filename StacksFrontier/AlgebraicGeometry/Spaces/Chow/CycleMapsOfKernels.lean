module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceLocallyFiniteSums

/-!
# Cycle maps given by a kernel, and the reduction of a comparison to one subspace

In the situation of Stacks 0EDT let `X/B` and `T/B` be good. Many homomorphisms
`Φ : Z_a(X) → Z_b(T)` of the chapter are defined one integral closed subspace at a time: a
`b`-cycle `φ(W)` on `T` is attached to each integral closed subspace `W ⊆ X`, and
`Φ(∑ n_W [W]) = ∑ n_W φ(W)`. This is how the refined Gysin homomorphism of Stacks 0ER1 is
defined, and it is preserved by composition and by pushforward along a closed immersion. The
sum is meaningful because `φ(W)` lies over `W` along a map `π : |T| → |X|` of point sets, so
only finitely many `W` meet a given point.

Stacks 0EQ8 observes that two such maps which agree up to rational equivalence on every `[W]`
need not agree up to rational equivalence on an infinite cycle. They do when the rational
equivalence between `φ(W)` and `ψ(W)` lies over `W`: the witnesses then form a locally finite
family by `AlgebraicGeometry.Space.isRationallyEquivalentToZero_finsum_max`. This is the reduction
of the proof of Stacks 0ERC to the case `α = [W]`, "the general case will then follow from the
observation in Remark 0EQ8 (and the specific shape of our rational equivalence produced below)",
and the main result below states it for the two composites of refined Gysin maps of that lemma.

## Main definitions

* `AlgebraicGeometry.Space.IsCycleMapOfKernel`: `Φ` is given by the kernel `φ`, which lies
  over the subspaces of `X` along `π`.

## Main results

* `AlgebraicGeometry.Space.isCycleMapOfKernel_gysinCycleMap`: the refined Gysin map of Stacks
  0ER1 is given by its component cycles.
* `AlgebraicGeometry.Space.IsCycleMapOfKernel.comp` and
  `AlgebraicGeometry.Space.IsCycleMapOfKernel.closedPushforward`: composition, and pushforward
  along a closed immersion.
* `AlgebraicGeometry.Space.isCycleFamilySumWithin_sub_of_isCycleMapOfKernel` and
  `AlgebraicGeometry.Space.isRationallyEquivalentToZero_sub_of_isCycleMapOfKernel`: two maps
  given by kernels whose difference on each `W` is a sum of members of a class of cycles closed
  under negation over `W` differ by such a sum on every cycle; for principal divisors, they
  agree up to rational equivalence.
* `AlgebraicGeometry.Space.isCycleFamilySumWithin_closedPushforward_gysin_gysin_sub` and
  `AlgebraicGeometry.Space.isRationallyEquivalentToZero_closedPushforward_gysin_gysin_sub`:
  the case `α = [W]` of Stacks 0ERC suffices, for any two pairs of refined Gysin maps and any
  closed immersion comparing their targets over `X`.

## References

* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ERC](https://stacks.math.columbia.edu/tag/0ERC)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X T : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (sT : T ⟶ D.space)

/-- Only finitely many integral closed subspaces with a nonzero coefficient in a cycle contain a
given point: a neighbourhood of the point meets only finitely many of their point sets. -/
theorem finite_setOf_ne_zero_mem_subspacePointSet {a : ℤ} (β : CycleGroup D sX a)
    (x : points D.site D.base D.base_mem X) :
    {W : IntegralClosedSubspace D.site D.base D.base_mem X |
      β.1 W ≠ 0 ∧ x ∈ subspacePointSet D.site D.base D.base_mem X W.subspace}.Finite := by
  obtain ⟨N, hN, hNfin⟩ := β.2.1 x
  refine hNfin.subset fun W hW => ⟨x, ?_, mem_of_mem_nhds hN⟩
  simpa [hW.1] using hW.2

/-- A homomorphism `Φ : Z_a(X) → Z_b(T)` is *the cycle map of the kernel* `φ`, which attaches a
`b`-cycle on `T` to every integral closed subspace of `X`, when `Φ(α) = ∑ α(W) φ(W)`
coefficientwise, and the kernel *lies over* the subspaces of `X` along `π : |T| → |X|`: an
integral closed subspace of `T` occurring in `φ(W)` maps into `|W|`. -/
structure IsCycleMapOfKernel
    (π : points D.site D.base D.base_mem T → points D.site D.base D.base_mem X) {a b : ℤ}
    (Φ : CycleGroup D sX a →+ CycleGroup D sT b)
    (φ : IntegralClosedSubspace D.site D.base D.base_mem X → CycleGroup D sT b) : Prop where
  /-- The coefficients of `Φ(α)` are `∑ α(W) φ(W)`. -/
  apply : ∀ (α : CycleGroup D sX a) (Z : IntegralClosedSubspace D.site D.base D.base_mem T),
    (Φ α).1 Z = ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X, α.1 W * (φ W).1 Z
  /-- The kernel lies over the subspaces of `X`. -/
  support : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem T), (φ W).1 Z ≠ 0 →
      subspacePointSet D.site D.base D.base_mem T Z.subspace ⊆
        π ⁻¹' subspacePointSet D.site D.base D.base_mem X W.subspace

variable {D sX sT}

/-- Every integral closed subspace of `T` contains a point of `|T|`, its generic point. -/
private theorem exists_mem_subspacePointSet
    (Z : IntegralClosedSubspace D.site D.base D.base_mem T) :
    ∃ z, z ∈ subspacePointSet D.site D.base D.base_mem T Z.subspace :=
  ⟨_, Z.genericPoint D.site D.base D.base_mem, rfl⟩

/-- The sum defining a cycle map of a kernel is finite at every integral closed subspace `Z` of
`T`: a contributing `W` occurs in `α` and contains the image of the generic point of `Z`. -/
theorem IsCycleMapOfKernel.finite_support
    {π : points D.site D.base D.base_mem T → points D.site D.base D.base_mem X} {a b : ℤ}
    {Φ : CycleGroup D sX a →+ CycleGroup D sT b}
    {φ : IntegralClosedSubspace D.site D.base D.base_mem X → CycleGroup D sT b}
    (h : IsCycleMapOfKernel D sX sT π Φ φ) (α : CycleGroup D sX a)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem T) :
    (Function.support fun W : IntegralClosedSubspace D.site D.base D.base_mem X =>
      α.1 W * (φ W).1 Z).Finite := by
  obtain ⟨z, hz⟩ := exists_mem_subspacePointSet Z
  refine (finite_setOf_ne_zero_mem_subspacePointSet D sX α (π z)).subset fun W hW => ?_
  have hprod : α.1 W * (φ W).1 Z ≠ 0 := Function.mem_support.1 hW
  exact ⟨left_ne_zero_of_mul hprod, h.support W Z (right_ne_zero_of_mul hprod) hz⟩

/-- A nonzero coefficient of the cycle `Φ(α)` lies over a subspace occurring in `α`. -/
theorem IsCycleMapOfKernel.exists_of_ne_zero
    {π : points D.site D.base D.base_mem T → points D.site D.base D.base_mem X} {a b : ℤ}
    {Φ : CycleGroup D sX a →+ CycleGroup D sT b}
    {φ : IntegralClosedSubspace D.site D.base D.base_mem X → CycleGroup D sT b}
    (h : IsCycleMapOfKernel D sX sT π Φ φ) (α : CycleGroup D sX a)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem T) (hZ : (Φ α).1 Z ≠ 0) :
    ∃ W, α.1 W ≠ 0 ∧ (φ W).1 Z ≠ 0 := by
  by_contra hall
  refine hZ ?_
  rw [h.apply]
  refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
  rcases not_and_or.1 (not_exists.1 hall W) with hW | hW
  · rw [not_not.1 hW, zero_mul]
  · rw [not_not.1 hW, mul_zero]

variable (D) in
/-- **Stacks 0ER1(2).** The refined Gysin map is the cycle map of its component cycles, which lie
over the subspaces of `X` along the inclusion `i : E → X`. -/
theorem isCycleMapOfKernel_gysinCycleMap (p : X ⟶ D.space)
    (E : ClosedSubspaces D.site D.base D.base_mem X) (hE : D.IsGood (E.1.ι ≫ p)) (k : ℤ)
    (rule : GysinComponentRule D p E k) :
    IsCycleMapOfKernel D p (E.1.ι ≫ p) (pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι)
      (gysinCycleMap D p E hE k rule) (gysinComponentCycle D p E hE k rule) where
  apply α Z := gysinCycleMap_apply D p E hE k rule α Z
  support W Z hZ := subspacePointSet_subset_of_gysinComponentCycle_ne_zero D p E hE k rule W Z hZ

/-- **Composition.** If `Φ₁ : Z_a(X) → Z_b(T₁)` is the cycle map of `φ₁` over `π₁` and
`Φ₂ : Z_b(T₁) → Z_c(T₂)` is the cycle map of `φ₂` over `π₂`, then `Φ₂ ∘ Φ₁` is the cycle map of
`W ↦ Φ₂(φ₁(W))` over `π₁ ∘ π₂`.

The double sum `∑_V ∑_W α(W) φ₁(W)(V) φ₂(V)(Z)` may be summed in either order: a contributing
pair has `W` occurring in `α` and containing the image of the generic point `z` of `Z`, and `V`
occurring in `φ₁(W)` and containing the image of `z` in `T₁`, and there are finitely many such
pairs. -/
theorem IsCycleMapOfKernel.comp {T₁ T₂ : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {s₁ : T₁ ⟶ D.space} {s₂ : T₂ ⟶ D.space}
    {π₁ : points D.site D.base D.base_mem T₁ → points D.site D.base D.base_mem X}
    {π₂ : points D.site D.base D.base_mem T₂ → points D.site D.base D.base_mem T₁} {a b c : ℤ}
    {Φ₁ : CycleGroup D sX a →+ CycleGroup D s₁ b}
    {φ₁ : IntegralClosedSubspace D.site D.base D.base_mem X → CycleGroup D s₁ b}
    {Φ₂ : CycleGroup D s₁ b →+ CycleGroup D s₂ c}
    {φ₂ : IntegralClosedSubspace D.site D.base D.base_mem T₁ → CycleGroup D s₂ c}
    (h₁ : IsCycleMapOfKernel D sX s₁ π₁ Φ₁ φ₁) (h₂ : IsCycleMapOfKernel D s₁ s₂ π₂ Φ₂ φ₂) :
    IsCycleMapOfKernel D sX s₂ (π₁ ∘ π₂) (Φ₂.comp Φ₁) fun W => Φ₂ (φ₁ W) where
  apply α Z := by
    obtain ⟨z, hz⟩ := exists_mem_subspacePointSet Z
    have hfin : {WV : IntegralClosedSubspace D.site D.base D.base_mem X ×
        IntegralClosedSubspace D.site D.base D.base_mem T₁ |
          α.1 WV.1 * (φ₁ WV.1).1 WV.2 * (φ₂ WV.2).1 Z ≠ 0}.Finite := by
      refine ((finite_setOf_ne_zero_mem_subspacePointSet D sX α (π₁ (π₂ z))).biUnion
        fun W _ => (Set.finite_singleton W).prod
          (finite_setOf_ne_zero_mem_subspacePointSet D s₁ (φ₁ W) (π₂ z))).subset ?_
      rintro ⟨W, V⟩ hWV
      have hWV' : α.1 W * (φ₁ W).1 V * (φ₂ V).1 Z ≠ 0 := hWV
      have h3 : (φ₂ V).1 Z ≠ 0 := right_ne_zero_of_mul hWV'
      have h12 : α.1 W * (φ₁ W).1 V ≠ 0 := left_ne_zero_of_mul hWV'
      have hV : π₂ z ∈ subspacePointSet D.site D.base D.base_mem T₁ V.subspace :=
        h₂.support V Z h3 hz
      have hW : π₁ (π₂ z) ∈ subspacePointSet D.site D.base D.base_mem X W.subspace :=
        h₁.support W V (right_ne_zero_of_mul h12) hV
      exact Set.mem_biUnion (x := W) ⟨left_ne_zero_of_mul h12, hW⟩
        ⟨rfl, right_ne_zero_of_mul h12, hV⟩
    change (Φ₂ (Φ₁ α)).1 Z = _
    rw [h₂.apply]
    simp_rw [h₁.apply, finsum_mul]
    rw [finsum_comm_of_finite (fun W V => α.1 W * (φ₁ W).1 V * (φ₂ V).1 Z) hfin]
    refine finsum_congr fun W => ?_
    rw [h₂.apply, mul_finsum]
    exact finsum_congr fun V => mul_assoc _ _ _
  support W Z hZ := by
    obtain ⟨V, hV, hV'⟩ := h₂.exists_of_ne_zero (φ₁ W) Z hZ
    exact fun y hy => h₁.support W V hV (h₂.support V Z hV' hy)

/-- **Pushforward along a closed immersion.** If `Φ : Z_a(X) → Z_b(T)` is the cycle map of `φ`
over `π`, and `i : T → T'` is a closed immersion over the base with `π' ∘ |i| = π`, then the
composite of `Φ` with the pushforward along `i` is the cycle map of `W ↦ i_* φ(W)` over `π'`. -/
theorem IsCycleMapOfKernel.closedPushforward
    {T' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sT' : T' ⟶ D.space}
    (hT' : IsAlgebraicSpace D.site D.base D.base_mem T')
    (hT : IsAlgebraicSpace D.site D.base D.base_mem T)
    (hT'dec : IsDecentSpace D.site D.base D.base_mem T') {i : T ⟶ T'}
    (hi : IsClosedImmersion D.site D.base D.base_mem i)
    (hsT' : IsLocallyOfFiniteType D.site D.base D.base_mem sT') (hic : i ≫ sT' = sT)
    {π : points D.site D.base D.base_mem T → points D.site D.base D.base_mem X}
    {π' : points D.site D.base D.base_mem T' → points D.site D.base D.base_mem X}
    (hπ : π' ∘ pointsMap D.site D.base D.base_mem T i = π) {a b : ℤ}
    {Φ : CycleGroup D sX a →+ CycleGroup D sT b}
    {φ : IntegralClosedSubspace D.site D.base D.base_mem X → CycleGroup D sT b}
    (h : IsCycleMapOfKernel D sX sT π Φ φ) :
    IsCycleMapOfKernel D sX sT' π'
      ((cycleGroupClosedPushforward D hT' hT hT'dec hi sT' hsT' sT hic b).comp Φ)
      fun W => cycleGroupClosedPushforward D hT' hT hT'dec hi sT' hsT' sT hic b (φ W) where
  apply α Z' := by
    change cycleClosedPushforward D hT' hT hT'dec hi (Φ α).1 Z' =
      ∑ᶠ W, α.1 W * cycleClosedPushforward D hT' hT hT'dec hi (φ W).1 Z'
    by_cases hex : ∃ Z, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hT' hT
        hT'dec hi Z = Z'
    · obtain ⟨Z, rfl⟩ := hex
      rw [cycleClosedPushforward_apply_pushforward, h.apply]
      refine finsum_congr fun W => ?_
      rw [cycleClosedPushforward_apply_pushforward]
    · have hne : ∀ Z, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hT' hT
          hT'dec hi Z ≠ Z' := fun Z hZ => hex ⟨Z, hZ⟩
      rw [cycleClosedPushforward_apply_of_forall_ne D hT' hT hT'dec hi _ Z' hne]
      refine (finsum_eq_zero_of_forall_eq_zero fun W => ?_).symm
      rw [cycleClosedPushforward_apply_of_forall_ne D hT' hT hT'dec hi _ Z' hne, mul_zero]
  support W Z' hZ' := by
    change cycleClosedPushforward D hT' hT hT'dec hi (φ W).1 Z' ≠ 0 at hZ'
    by_cases hex : ∃ Z, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hT' hT
        hT'dec hi Z = Z'
    · obtain ⟨Z, rfl⟩ := hex
      rw [cycleClosedPushforward_apply_pushforward] at hZ'
      rw [IntegralClosedSubspace.subspacePointSet_pushforward]
      rintro _ ⟨y, hy, rfl⟩
      have hπy := h.support W Z hZ' hy
      rw [Set.mem_preimage, ← hπ] at hπy
      exact hπy
    · exact absurd (cycleClosedPushforward_apply_of_forall_ne D hT' hT hT'dec hi _ Z'
        fun Z hZ => hex ⟨Z, hZ⟩) hZ'

variable (sT) in
/-- **The reduction of Stacks 0EQ8, for any class of summands.** Let `P W` be a set of cycles on
each integral closed subspace `W ⊆ T`, closed under negation, and let `Φ, Ψ : Z_a(X) → Z_b(T)` be
the cycle maps of kernels `φ`, `ψ` lying over the subspaces of `X` along a continuous
`π : |T| → |X|`. If for every integral closed subspace `W ⊆ X` the difference `φ(W) - ψ(W)` is a
locally finite sum of pushforwards of members of `P` within `π⁻¹|W|`, then so is `Φ(α) - Ψ(α)`
for every `a`-cycle `α`, within `π⁻¹` of the union of the subspaces occurring in `α`.

The cycle `Φ(α) - Ψ(α)` is coefficientwise `∑ α(W) (φ(W) - ψ(W))`, and the sets `π⁻¹|W|` for
the `W` occurring in `α` form a locally finite family, so
`AlgebraicGeometry.Space.isCycleFamilySumWithin_finsum` applies. -/
theorem isCycleFamilySumWithin_sub_of_isCycleMapOfKernel (hT : D.IsGood sT) {b : ℤ}
    {P : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem T,
      Set (CycleGroup D (W.subspace.ι ≫ sT) b)}
    (hP : ∀ {W c}, c ∈ P W → -c ∈ P W)
    {π : points D.site D.base D.base_mem T → points D.site D.base D.base_mem X}
    (hπ : Continuous π) {a : ℤ} {Φ Ψ : CycleGroup D sX a →+ CycleGroup D sT b}
    {φ ψ : IntegralClosedSubspace D.site D.base D.base_mem X → CycleGroup D sT b}
    (hΦ : IsCycleMapOfKernel D sX sT π Φ φ) (hΨ : IsCycleMapOfKernel D sX sT π Ψ ψ)
    (h : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      IsCycleFamilySumWithin.{u, v} D sT hT b P (φ W - ψ W)
        (π ⁻¹' subspacePointSet D.site D.base D.base_mem X W.subspace))
    (α : CycleGroup D sX a) :
    IsCycleFamilySumWithin.{u, max (u + 1) v} D sT hT b P (Φ α - Ψ α)
      (⋃ W : IntegralClosedSubspace D.site D.base D.base_mem X,
        if α.1 W = 0 then ∅ else π ⁻¹' subspacePointSet D.site D.base D.base_mem X W.subspace) := by
  classical
  have hloc : LocallyFinite fun W : IntegralClosedSubspace D.site D.base D.base_mem X =>
      if α.1 W = 0 then (∅ : Set (points D.site D.base D.base_mem T))
        else π ⁻¹' subspacePointSet D.site D.base D.base_mem X W.subspace := by
    have h0 := α.2.1.preimage_continuous hπ
    refine h0.subset fun W => ?_
    split_ifs with hW <;> simp
  refine (isCycleFamilySumWithin_finsum D sT hT b _ hloc
    (fun W => α.1 W • (φ W - ψ W)) (fun W => ?_) fun Z => ?_)
  · split_ifs with hW
    · rw [hW, zero_smul]
      exact isCycleFamilySumWithin_zero D sT hT b ∅
    · exact (h W).zsmul hP (α.1 W)
  · change (Φ α).1 Z - (Ψ α).1 Z = _
    rw [hΦ.apply, hΨ.apply, ← finsum_sub_distrib (hΦ.finite_support α Z)
      (hΨ.finite_support α Z)]
    refine finsum_congr fun W => ?_
    change _ = α.1 W • ((φ W).1 Z - (ψ W).1 Z)
    rw [smul_eq_mul, mul_sub]

variable (sT) in
/-- **The reduction of Stacks 0EQ8.** Let `Φ, Ψ : Z_a(X) → Z_b(T)` be the cycle maps of kernels
`φ`, `ψ` lying over the subspaces of `X` along a continuous `π : |T| → |X|`. If for every
integral closed subspace `W ⊆ X` the difference `φ(W) - ψ(W)` is rationally equivalent to zero
within `π⁻¹|W|`, then `Φ(α) - Ψ(α)` is rationally equivalent to zero for every `a`-cycle `α`,
within `π⁻¹` of the union of the subspaces occurring in `α`: the case of the principal divisors
of `AlgebraicGeometry.Space.isCycleFamilySumWithin_sub_of_isCycleMapOfKernel`. -/
theorem isRationallyEquivalentToZeroWithin_sub_of_isCycleMapOfKernel (hT : D.IsGood sT)
    {π : points D.site D.base D.base_mem T → points D.site D.base D.base_mem X}
    (hπ : Continuous π) {a b : ℤ} {Φ Ψ : CycleGroup D sX a →+ CycleGroup D sT b}
    {φ ψ : IntegralClosedSubspace D.site D.base D.base_mem X → CycleGroup D sT b}
    (hΦ : IsCycleMapOfKernel D sX sT π Φ φ) (hΨ : IsCycleMapOfKernel D sX sT π Ψ ψ)
    (h : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      IsRationallyEquivalentToZeroWithin.{v} D sT hT b (φ W - ψ W)
        (π ⁻¹' subspacePointSet D.site D.base D.base_mem X W.subspace))
    (α : CycleGroup D sX a) :
    IsRationallyEquivalentToZeroWithin.{max (u + 1) v} D sT hT b (Φ α - Ψ α)
      (⋃ W : IntegralClosedSubspace D.site D.base D.base_mem X,
        if α.1 W = 0 then ∅ else π ⁻¹' subspacePointSet D.site D.base D.base_mem X W.subspace) :=
  (isCycleFamilySumWithin_sub_of_isCycleMapOfKernel sT hT neg_mem_principalDivisors hπ hΦ hΨ
    (fun W => (h W).isCycleFamilySumWithin) α).isRationallyEquivalentToZeroWithin

variable (sT) in
/-- **The reduction of Stacks 0EQ8**, forgetting where the witnesses lie: two cycle maps of
kernels whose differences on the subspaces of `X` are rationally equivalent to zero over those
subspaces agree up to rational equivalence. -/
theorem isRationallyEquivalentToZero_sub_of_isCycleMapOfKernel (hT : D.IsGood sT)
    {π : points D.site D.base D.base_mem T → points D.site D.base D.base_mem X}
    (hπ : Continuous π) {a b : ℤ} {Φ Ψ : CycleGroup D sX a →+ CycleGroup D sT b}
    {φ ψ : IntegralClosedSubspace D.site D.base D.base_mem X → CycleGroup D sT b}
    (hΦ : IsCycleMapOfKernel D sX sT π Φ φ) (hΨ : IsCycleMapOfKernel D sX sT π Ψ ψ)
    (h : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      IsRationallyEquivalentToZeroWithin.{v} D sT hT b (φ W - ψ W)
        (π ⁻¹' subspacePointSet D.site D.base D.base_mem X W.subspace))
    (α : CycleGroup D sX a) :
    IsRationallyEquivalentToZero.{max (u + 1) v} D sT hT b (Φ α - Ψ α) :=
  (isRationallyEquivalentToZeroWithin_sub_of_isCycleMapOfKernel sT hT hπ hΦ hΨ h
    α).isRationallyEquivalentToZero

/-! ### Two composites of refined Gysin maps -/

section GysinGysin

variable (D) (p : X ⟶ D.space) (E E' : ClosedSubspaces D.site D.base D.base_mem X)
    (hE : D.IsGood (E.1.ι ≫ p)) (hE' : D.IsGood (E'.1.ι ≫ p)) (k : ℤ)
    (rule : GysinComponentRule D p E (k + 1)) (rule' : GysinComponentRule D p E' (k + 1))
    (F : ClosedSubspaces D.site D.base D.base_mem E.1.toFunctor)
    (F' : ClosedSubspaces D.site D.base D.base_mem E'.1.toFunctor)
    (hF : D.IsGood (F.1.ι ≫ E.1.ι ≫ p)) (hF' : D.IsGood (F'.1.ι ≫ E'.1.ι ≫ p))
    (ruleF : GysinComponentRule D (E.1.ι ≫ p) F k)
    (ruleF' : GysinComponentRule D (E'.1.ι ≫ p) F' k)
    {e : F.1.toFunctor ⟶ F'.1.toFunctor} (he : IsClosedImmersion D.site D.base D.base_mem e)
    (hecomp : e ≫ F'.1.ι ≫ E'.1.ι = F.1.ι ≫ E.1.ι)

include hecomp in
/-- The comparison `e` is a morphism over the base. -/
theorem comp_structure_of_comp_eq : e ≫ F'.1.ι ≫ E'.1.ι ≫ p = F.1.ι ≫ E.1.ι ≫ p := by
  rw [← Category.assoc F'.1.ι, ← Category.assoc, hecomp, Category.assoc]

/-- The pushforward along the comparison `e : F → F'` of `k`-cycles, `F` and `F'` being viewed
over the base through `X`. -/
abbrev comparisonPushforward :
    CycleGroup D (F.1.ι ≫ E.1.ι ≫ p) k →+ CycleGroup D (F'.1.ι ≫ E'.1.ι ≫ p) k :=
  cycleGroupClosedPushforward D hF'.1 hF.1 (D.isDecentSpace_of_isGood _ hF') he
    (F'.1.ι ≫ E'.1.ι ≫ p) hF'.2.2 (F.1.ι ≫ E.1.ι ≫ p)
    (comp_structure_of_comp_eq D p E E' F F' hecomp) k

/-- **The reduction of Stacks 0ERC to `α = [W]`, for any class of summands.** Let `E, E' ⊆ X`
be closed subspaces with refined Gysin maps `Z_{k+2}(X) → Z_{k+1}(E)` and
`Z_{k+2}(X) → Z_{k+1}(E')` of Stacks 0ER1, let `F ⊆ E` and `F' ⊆ E'` be closed subspaces with
refined Gysin maps `Z_{k+1}(E) → Z_k(F)` and `Z_{k+1}(E') → Z_k(F')`, and let `e : F → F'` be a
closed immersion over `X`. Let `P V` be a set of cycles on each integral closed subspace
`V ⊆ F'`, closed under negation. Suppose that for every integral closed subspace `W ⊆ X` of
δ-dimension `k + 2` the two images of `[W]` in `Z_k(F')`, namely `e_*` of the first composite and
the second composite applied to `[W]`, differ by a locally finite sum of pushforwards of members
of `P` within the inverse image of `|W|`. Then so do the two images of every `(k+2)`-cycle `α` on
`X`, within the inverse image of the union of the subspaces occurring in `α`.

In the proof of Stacks 0ERC, `F = F' = E ∩ E'`, the summands are principal divisors, and the
hypothesis is the comparison of the two composites on `[W]` by the key formula, whose witnesses
lie in `W ∩ E ∩ E'`. -/
theorem isCycleFamilySumWithin_closedPushforward_gysin_gysin_sub
    {P : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem F'.1.toFunctor,
      Set (CycleGroup D (V.subspace.ι ≫ F'.1.ι ≫ E'.1.ι ≫ p) k)}
    (hP : ∀ {V c}, c ∈ P V → -c ∈ P V)
    (h : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D p W = k + 1 + 1),
      IsCycleFamilySumWithin.{u, v} D (F'.1.ι ≫ E'.1.ι ≫ p) hF' k P
        (comparisonPushforward D p E E' k F F' hF hF' he hecomp
            (gysinCycleMap D (E.1.ι ≫ p) F hF k ruleF
              (gysinCycleMap D p E hE (k + 1) rule (integralCycle D p (k + 1 + 1) W hW))) -
          gysinCycleMap D (E'.1.ι ≫ p) F' hF' k ruleF'
            (gysinCycleMap D p E' hE' (k + 1) rule' (integralCycle D p (k + 1 + 1) W hW)))
        ((pointsMap D.site D.base D.base_mem E'.1.toFunctor E'.1.ι ∘
          pointsMap D.site D.base D.base_mem F'.1.toFunctor F'.1.ι) ⁻¹'
            subspacePointSet D.site D.base D.base_mem X W.subspace))
    (α : CycleGroup D p (k + 1 + 1)) :
    IsCycleFamilySumWithin.{u, max (u + 1) v} D (F'.1.ι ≫ E'.1.ι ≫ p) hF' k P
      (comparisonPushforward D p E E' k F F' hF hF' he hecomp
          (gysinCycleMap D (E.1.ι ≫ p) F hF k ruleF (gysinCycleMap D p E hE (k + 1) rule α)) -
        gysinCycleMap D (E'.1.ι ≫ p) F' hF' k ruleF' (gysinCycleMap D p E' hE' (k + 1) rule' α))
      (⋃ W : IntegralClosedSubspace D.site D.base D.base_mem X,
        if α.1 W = 0 then ∅ else
          (pointsMap D.site D.base D.base_mem E'.1.toFunctor E'.1.ι ∘
            pointsMap D.site D.base D.base_mem F'.1.toFunctor F'.1.ι) ⁻¹'
              subspacePointSet D.site D.base D.base_mem X W.subspace) := by
  have hπ : (pointsMap D.site D.base D.base_mem E'.1.toFunctor E'.1.ι ∘
      pointsMap D.site D.base D.base_mem F'.1.toFunctor F'.1.ι) ∘
        pointsMap D.site D.base D.base_mem F.1.toFunctor e =
      pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι ∘
        pointsMap D.site D.base D.base_mem F.1.toFunctor F.1.ι := by
    have h1 := congrArg (pointsMap D.site D.base D.base_mem F.1.toFunctor) hecomp
    simp only [pointsMap_comp] at h1
    exact h1
  have hΦ := ((isCycleMapOfKernel_gysinCycleMap D p E hE (k + 1) rule).comp
    (isCycleMapOfKernel_gysinCycleMap D (E.1.ι ≫ p) F hF k ruleF)).closedPushforward hF'.1 hF.1
      (D.isDecentSpace_of_isGood _ hF') he hF'.2.2
      (comp_structure_of_comp_eq D p E E' F F' hecomp) hπ
  have hΨ := (isCycleMapOfKernel_gysinCycleMap D p E' hE' (k + 1) rule').comp
    (isCycleMapOfKernel_gysinCycleMap D (E'.1.ι ≫ p) F' hF' k ruleF')
  refine isCycleFamilySumWithin_sub_of_isCycleMapOfKernel _ hF' hP
    ((continuous_pointsMap D.site D.base D.base_mem E'.1.ι).comp
      (continuous_pointsMap D.site D.base D.base_mem F'.1.ι)) hΦ hΨ (fun W => ?_) α
  by_cases hW : deltaDimension D p W = k + 1 + 1
  · have h1 := h W hW
    rw [gysinCycleMap_integralCycle D p E hE (k + 1) rule hW,
      gysinCycleMap_integralCycle D p E' hE' (k + 1) rule' hW] at h1
    exact h1
  · rw [gysinComponentCycle_of_deltaDimension_ne D p E hE (k + 1) rule hW,
      gysinComponentCycle_of_deltaDimension_ne D p E' hE' (k + 1) rule' hW]
    simp only [map_zero, sub_zero]
    exact isCycleFamilySumWithin_zero D _ hF' k _

/-- **The reduction of Stacks 0ERC to `α = [W]`.** In the situation of
`AlgebraicGeometry.Space.isCycleFamilySumWithin_closedPushforward_gysin_gysin_sub`, if for every
integral closed subspace `W ⊆ X` of δ-dimension `k + 2` the two images of `[W]` in `Z_k(F')`
differ by a cycle rationally equivalent to zero within the inverse image of `|W|`, then the two
images of every `(k+2)`-cycle on `X` differ by a cycle rationally equivalent to zero. -/
theorem isRationallyEquivalentToZero_closedPushforward_gysin_gysin_sub
    (h : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D p W = k + 1 + 1),
      IsRationallyEquivalentToZeroWithin.{v} D (F'.1.ι ≫ E'.1.ι ≫ p) hF' k
        (comparisonPushforward D p E E' k F F' hF hF' he hecomp
            (gysinCycleMap D (E.1.ι ≫ p) F hF k ruleF
              (gysinCycleMap D p E hE (k + 1) rule (integralCycle D p (k + 1 + 1) W hW))) -
          gysinCycleMap D (E'.1.ι ≫ p) F' hF' k ruleF'
            (gysinCycleMap D p E' hE' (k + 1) rule' (integralCycle D p (k + 1 + 1) W hW)))
        ((pointsMap D.site D.base D.base_mem E'.1.toFunctor E'.1.ι ∘
          pointsMap D.site D.base D.base_mem F'.1.toFunctor F'.1.ι) ⁻¹'
            subspacePointSet D.site D.base D.base_mem X W.subspace))
    (α : CycleGroup D p (k + 1 + 1)) :
    IsRationallyEquivalentToZero.{max (u + 1) v} D (F'.1.ι ≫ E'.1.ι ≫ p) hF' k
      (comparisonPushforward D p E E' k F F' hF hF' he hecomp
          (gysinCycleMap D (E.1.ι ≫ p) F hF k ruleF (gysinCycleMap D p E hE (k + 1) rule α)) -
        gysinCycleMap D (E'.1.ι ≫ p) F' hF' k ruleF' (gysinCycleMap D p E' hE' (k + 1) rule' α)) :=
  (isCycleFamilySumWithin_closedPushforward_gysin_gysin_sub D p E E' hE hE' k rule rule' F F' hF
    hF' ruleF ruleF' he hecomp neg_mem_principalDivisors
    (fun W hW => (h W hW).isCycleFamilySumWithin) α).isRationallyEquivalentToZeroWithin
    |>.isRationallyEquivalentToZero

end GysinGysin

end AlgebraicGeometry.Space

end
