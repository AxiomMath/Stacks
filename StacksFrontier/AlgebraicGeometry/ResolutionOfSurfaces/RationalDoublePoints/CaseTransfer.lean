module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.CaseTwoInvariant
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.EmbeddingDimensionThree

/-!
# Case I, case II and the case II invariants along local homomorphisms

The properties of a local ring used in the case analysis of Section 54.12 —
`AlgebraicGeometry.IsGoodCoordinate`, `AlgebraicGeometry.IsCaseOne`,
`AlgebraicGeometry.IsCaseTwo`, `AlgebraicGeometry.HasDoubleLineRelation` and
`AlgebraicGeometry.HasDoubleLineRelationUnit` — are transported along a local homomorphism
`φ : A → A'` which induces a surjection on residue fields and maps `𝔪_A` onto `𝔪_{A'}`, such as the
map from a Noetherian local ring to its completion. The case dichotomy
(`AlgebraicGeometry.isCaseOne_or_isCaseTwo`) is the dichotomy of the source in this language.

## References

* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
-/

@[expose] public section

open IsLocalRing

namespace AlgebraicGeometry

/-- **Case II of Section 54.12, in its normal form.** There are generators `x₁, x₂, x₃` of the
maximal ideal with `x₃² = Σ bₚᵩᵣ xₚxᵩxᵣ`. -/
def IsCaseTwo (B : Type*) [CommRing B] [IsLocalRing B] : Prop :=
  ∃ (w : Fin 3 → B) (b : Fin 3 → Fin 3 → Fin 3 → B), Ideal.span (Set.range w) = maximalIdeal B ∧
    w 2 * w 2 = ∑ p, ∑ q, ∑ r, b p q r * (w p * w q * w r)

/-- **The dichotomy of Section 54.12**: given the dimension formula
`dim_κ 𝔪ⁿ/𝔪ⁿ⁺¹ = 2n + 1` for `n = 1, 2`, a Noetherian local ring is in case I or in case II. -/
theorem isCaseOne_or_isCaseTwo {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (h1 : Module.finrank (ResidueField A) (gradedPiece A 1) = 3)
    (h2 : Module.finrank (ResidueField A) (gradedPiece A 2) = 5) :
    IsCaseOne A ∨ IsCaseTwo A := by
  rcases exists_sq_eq_cubicExpansion_or_not_isScalarSqLinear h1 h2 with
    ⟨x, b, hspan, hsq⟩ | ⟨x, a, b, hspan, hupper, hunit, hrel, hcase⟩
  · exact Or.inr ⟨x, b, hspan, hsq⟩
  · refine Or.inl ⟨x, a, hspan, hupper, hunit, ?_, hcase⟩
    rw [hrel, ← hspan, span_pow_three_eq_span_triples]
    exact Ideal.sum_mem _ fun p _ => Ideal.sum_mem _ fun q _ => Ideal.sum_mem _ fun r _ =>
      Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨(p, q, r), rfl⟩)

/-- **The dichotomy of Section 54.12 for a rational double point**: the ring of a Situation 0BGC
is in case I or in case II. The dimension formula `dim_κ 𝔪ⁿ/𝔪ⁿ⁺¹ = 2n + 1` it needs is
`AlgebraicGeometry.RationalDoublePointSituation.finrank_gradedPiece_eq_two_mul_add_one`. -/
theorem RationalDoublePointSituation.isCaseOne_or_isCaseTwo
    (S : RationalDoublePointSituation) : IsCaseOne S.A ∨ IsCaseTwo S.A :=
  AlgebraicGeometry.isCaseOne_or_isCaseTwo (S.finrank_gradedPiece_eq_two_mul_add_one 1)
    (S.finrank_gradedPiece_eq_two_mul_add_one 2)

variable {A A' : Type*} [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']
  (φ : A →+* A') [IsLocalHom φ]

/-- The isomorphism of residue fields induced by a local homomorphism which is surjective on
residue fields. -/
theorem exists_residueField_ringEquiv_of_isLocalHom
    (hsurj : Function.Surjective ((Ideal.Quotient.mk (maximalIdeal A')).comp φ)) :
    ∃ ι : ResidueField A ≃+* ResidueField A', ∀ r, ι (residue A r) = residue A' (φ r) := by
  refine ⟨RingEquiv.ofBijective (ResidueField.map φ) ⟨(ResidueField.map φ).injective,
    fun β => ?_⟩, ResidueField.map_residue φ⟩
  obtain ⟨r, hr⟩ := hsurj β
  exact ⟨residue A r, by rw [ResidueField.map_residue]; exact hr⟩

/-- A local homomorphism mapping `𝔪_A` onto `𝔪_{A'}` sends generators of `𝔪_A` to generators of
`𝔪_{A'}`. -/
theorem span_range_comp_eq (hmap : Ideal.map φ (maximalIdeal A) = maximalIdeal A')
    {w : Fin 3 → A} (hspan : Ideal.span (Set.range w) = maximalIdeal A) :
    Ideal.span (Set.range (φ ∘ w)) = maximalIdeal A' := by
  rw [Set.range_comp, ← Ideal.map_span, hspan, hmap]

/-- A local homomorphism sends units to units. -/
theorem map_notMem_maximalIdeal {r : A} (hr : r ∉ maximalIdeal A) : φ r ∉ maximalIdeal A' :=
  notMem_maximalIdeal.mpr ((notMem_maximalIdeal.mp hr).map φ)

/-- A local homomorphism mapping `𝔪_A` onto `𝔪_{A'}` sends `𝔪_Aⁿ` into `𝔪_{A'}ⁿ`. -/
theorem map_mem_maximalIdeal_pow (hmap : Ideal.map φ (maximalIdeal A) = maximalIdeal A')
    {n : ℕ} {r : A} (hr : r ∈ maximalIdeal A ^ n) : φ r ∈ maximalIdeal A' ^ n := by
  rw [← hmap, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hr

/-- The unit, upper-triangularity and `𝔪³` conditions of case I are transported along a local
homomorphism mapping `𝔪_A` onto `𝔪_{A'}`. -/
private theorem map_upper_unit_rel (hmap : Ideal.map φ (maximalIdeal A) = maximalIdeal A')
    {w : Fin 3 → A} {a : Fin 3 → Fin 3 → A} (hupper : ∀ p q, q < p → a p q = 0)
    (hunit : ∃ p q, p ≤ q ∧ a p q ∉ maximalIdeal A)
    (hrel : ∑ p, ∑ q, a p q * (w p * w q) ∈ maximalIdeal A ^ 3) :
    (∀ p q, q < p → φ (a p q) = 0) ∧ (∃ p q, p ≤ q ∧ φ (a p q) ∉ maximalIdeal A') ∧
      ∑ p, ∑ q, φ (a p q) * ((φ ∘ w) p * (φ ∘ w) q) ∈ maximalIdeal A' ^ 3 := by
  refine ⟨fun p q hpq => by simp [hupper p q hpq], ?_, ?_⟩
  · obtain ⟨p, q, hpq, hne⟩ := hunit
    exact ⟨p, q, hpq, map_notMem_maximalIdeal φ hne⟩
  · simpa [map_sum, map_mul] using map_mem_maximalIdeal_pow φ hmap hrel

/-- A good coordinate is transported along a local homomorphism surjective on residue fields and
mapping `𝔪_A` onto `𝔪_{A'}`. -/
theorem IsGoodCoordinate.map
    (hsurj : Function.Surjective ((Ideal.Quotient.mk (maximalIdeal A')).comp φ))
    (hmap : Ideal.map φ (maximalIdeal A) = maximalIdeal A') {g : A} (h : IsGoodCoordinate A g) :
    IsGoodCoordinate A' (φ g) := by
  obtain ⟨ι, hι⟩ := exists_residueField_ringEquiv_of_isLocalHom φ hsurj
  obtain ⟨w, a, hw0, hspan, hupper, hunit, hrel, hgood⟩ := h
  have key := map_upper_unit_rel φ hmap hupper hunit hrel
  refine ⟨φ ∘ w, fun p q => φ (a p q), by simp [hw0], span_range_comp_eq φ hmap hspan,
    key.1, key.2.1, key.2.2, ?_⟩
  simp only [IsGoodCoordinateForm, ← hι]
  exact fun h' => hgood
    ((isScalarSqLinear_map_iff (restrictFirstVar fun p q => residue A (a p q)) ι).mp h')

/-- Case I is transported along a local homomorphism surjective on residue fields and mapping
`𝔪_A` onto `𝔪_{A'}`. -/
theorem IsCaseOne.map
    (hsurj : Function.Surjective ((Ideal.Quotient.mk (maximalIdeal A')).comp φ))
    (hmap : Ideal.map φ (maximalIdeal A) = maximalIdeal A') (h : IsCaseOne A) :
    IsCaseOne A' := by
  obtain ⟨ι, hι⟩ := exists_residueField_ringEquiv_of_isLocalHom φ hsurj
  obtain ⟨w, a, hspan, hupper, hunit, hrel, hcase⟩ := h
  have key := map_upper_unit_rel φ hmap hupper hunit hrel
  refine ⟨φ ∘ w, fun p q => φ (a p q), span_range_comp_eq φ hmap hspan,
    key.1, key.2.1, key.2.2, ?_⟩
  simp only [← hι]
  rwa [isScalarSqLinear_map_iff]

/-- Case II is transported along a local homomorphism mapping `𝔪_A` onto `𝔪_{A'}`. -/
theorem IsCaseTwo.map (hmap : Ideal.map φ (maximalIdeal A) = maximalIdeal A')
    (h : IsCaseTwo A) : IsCaseTwo A' := by
  obtain ⟨w, b, hspan, hsq⟩ := h
  refine ⟨φ ∘ w, fun p q r => φ (b p q r), span_range_comp_eq φ hmap hspan, ?_⟩
  simpa [map_sum, map_mul] using congrArg φ hsq

/-- The case II invariant is transported along a local homomorphism mapping `𝔪_A` onto
`𝔪_{A'}`. -/
theorem HasDoubleLineRelation.map (hmap : Ideal.map φ (maximalIdeal A) = maximalIdeal A')
    {w : Fin 3 → A} (h : HasDoubleLineRelation A w) : HasDoubleLineRelation A' (φ ∘ w) := by
  obtain ⟨hspan, F, hF, hsq⟩ := h
  refine ⟨span_range_comp_eq φ hmap hspan, φ F, map_mem_maximalIdeal_pow φ hmap hF, ?_⟩
  simpa using congrArg φ hsq

/-- The case II invariant with a nondegenerate `w₂²`-coefficient is transported along a local
homomorphism mapping `𝔪_A` onto `𝔪_{A'}`. -/
theorem HasDoubleLineRelationUnit.map (hmap : Ideal.map φ (maximalIdeal A) = maximalIdeal A')
    {w : Fin 3 → A} (h : HasDoubleLineRelationUnit A w) :
    HasDoubleLineRelationUnit A' (φ ∘ w) := by
  obtain ⟨hspan, F, f, hf, hFf, hsq⟩ := h
  refine ⟨span_range_comp_eq φ hmap hspan, φ F, φ f, hf.map φ, ?_, by simpa using congrArg φ hsq⟩
  have h1 := Ideal.mem_map_of_mem φ hFf
  rw [Ideal.map_mul, Ideal.map_span, hmap, Set.image_pair] at h1
  simpa using h1

end AlgebraicGeometry

end
