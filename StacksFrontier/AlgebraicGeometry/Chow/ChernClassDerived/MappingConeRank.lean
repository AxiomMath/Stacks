module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.CommonRankRefinement
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.MappingConeComplex

/-!
# The alternating rank class is additive on a mapping cone

Let `Y` be locally of finite type over the base of chapter 42 of the Stacks Project and let
`α : 𝓔₁^• ⟶ 𝓔₂^•` be a map of locally bounded complexes of finite locally free `𝒪_Y`-modules.
Then

  `r(𝓔₂^•) = r(𝓔₁^•) + r(C(α)^•)`

for the alternating rank class `r` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DerivedChernClasses`. This is the
degree-zero case of the additivity `P_p(𝓔₂^•) = P_p(𝓔₁^•) + P_p(C(α)^•)` of [Stacks, Tag 0F9F],
and it is what makes the power sums and the Chern character additive, since `P_0` is the rank.

## Main results

* `Stacks.Chow.finsum_negOnePow_coneRank` — the arithmetic identity behind it: the alternating
  sum of the cone's rank function `n ↦ ρ(n + 1) + σ(n)` is `-∑_n (-1)^n ρ(n) + ∑_n (-1)^n σ(n)`.
* `Stacks.Chow.complexRankClass_mappingCone` — **the degree-zero case of [Stacks, Tag 0F9F]**:
  the alternating rank class of `𝓔₂^•` is that of `𝓔₁^•` plus that of the cone.

## Implementation notes

The arithmetic is read off `Stacks.Chow.coneRank_apply`: the degree-`n` term of the cone is
`𝓔₁^{n + 1} ⊕ 𝓔₂^n`, so the sum splits into a shifted copy of the alternating sum of `ρ` and the
alternating sum of `σ`. Reindexing the shifted copy by `n ↦ n + 1` costs a sign, by
`Int.negOnePow_succ`, and that sign is the `-` in the statement. Splitting a `finsum` needs both
halves to have finite support, which they do because `ρ` and `σ` are finitely supported.

The geometry is one application of `Stacks.Chow.eq_of_res_eq_of_constantRanks`: the identity is an
identity of classes glued over rank loci, so it is read on the common refinement of the two
decompositions, where all three complexes have constant ranks and each class is an integer
multiple of `1` by `Stacks.Chow.res_complexRankClass_of_constant_rank`. The ranks of the cone
there are `Stacks.Chow.coneRank` of the other two, by
`Stacks.Chow.isFiniteLocallyFreeOfRank_pullbackComplex_mappingCone_X`.

## References

* [Stacks Project, Tag 0F9F](https://stacks.math.columbia.edu/tag/0F9F)
* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The alternating sum of the cone's rank function -/

/-- **The alternating sum of the cone's rank function.** If `𝓔₁^•` has the constant ranks `ρ` and
`𝓔₂^•` the constant ranks `σ`, then the cone has the ranks `n ↦ ρ(n + 1) + σ(n)` and its
alternating sum is `-∑_n (-1)^n ρ(n) + ∑_n (-1)^n σ(n)`: the sum splits in two, and reindexing the
`ρ`-half by `n ↦ n + 1` flips the sign of `(-1)^n`. -/
theorem finsum_negOnePow_coneRank (ρ σ : ℤ →₀ ℕ) :
    (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (coneRank ρ σ n : ℤ)) =
      -(∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (ρ n : ℤ)) + ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (σ n : ℤ) := by
  classical
  have hfin (τ : ℤ →₀ ℕ) (k : ℤ) :
      (Function.support fun n : ℤ ↦ (n.negOnePow : ℤ) * (τ (n + k) : ℤ)).Finite :=
    (τ.hasFiniteSupport.preimage (add_left_injective k).injOn).subset fun n hn h0 ↦
      hn (by simp [h0])
  have hA := hfin ρ 1
  have hB := by simpa only [add_zero] using hfin σ 0
  have hshift : (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (ρ (n + 1) : ℤ)) =
      -∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (ρ n : ℤ) := by
    rw [← finsum_comp_equiv (Equiv.addRight (1 : ℤ))
      (f := fun m : ℤ ↦ (m.negOnePow : ℤ) * (ρ m : ℤ)), ← finsum_neg_distrib]
    refine finsum_congr fun n ↦ ?_
    simp only [Equiv.coe_addRight, Int.negOnePow_succ, Units.val_neg, neg_mul, neg_neg]
  have hsplit : (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (coneRank ρ σ n : ℤ)) =
      (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (ρ (n + 1) : ℤ)) +
        ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (σ n : ℤ) := by
    rw [← finsum_add_distrib hA hB]
    refine finsum_congr fun n ↦ ?_
    rw [coneRank_apply]
    push_cast
    ring
  rw [hsplit, hshift]

/-! ### Additivity of the alternating rank class on a cone -/

/-- **The alternating rank class is additive on a mapping cone**, the degree-zero case of
[Stacks, Tag 0F9F]: for `α : 𝓔₁^• ⟶ 𝓔₂^•` a map of locally bounded complexes of finite locally
free `𝒪_Y`-modules, `r(𝓔₂^•) = r(𝓔₁^•) + r(C(α)^•)`.

Both sides are glued over rank loci, so the identity is read on the common refinement of the two
decompositions (`Stacks.Chow.eq_of_res_eq_of_constantRanks`). There all three complexes have
constant ranks — `ρ`, `σ` and `Stacks.Chow.coneRank ρ σ` — so each class is an integer multiple
of `1`, and the identity of integers is `Stacks.Chow.finsum_negOnePow_coneRank`. -/
theorem complexRankClass_mappingCone (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] {P₁ P₂ : CochainComplex Y.Modules ℤ} (α : P₁ ⟶ P₂)
    (h₁ : IsLocallyBoundedFiniteLocallyFree P₁) (h₂ : IsLocallyBoundedFiniteLocallyFree P₂) :
    complexRankClass C sY h₂ =
      complexRankClass C sY h₁ +
        complexRankClass C sY (isLocallyBoundedFiniteLocallyFree_mappingCone α h₁ h₂) := by
  refine eq_of_res_eq_of_constantRanks C sY h₁ h₂ fun Z g _ ρ σ hρg hσg ↦ ?_
  rcases isEmpty_or_nonempty Z with _ | _
  · exact (TotalChowClass.subsingleton_of_isEmpty _).elim _ _
  · have harith : (∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (ρ n : ℤ)) +
        ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (coneRank ρ σ n : ℤ) =
          ∑ᶠ n : ℤ, (n.negOnePow : ℤ) * (σ n : ℤ) := by
      rw [finsum_negOnePow_coneRank]
      ring
    rw [map_add, res_complexRankClass_of_constant_rank C sY h₂ g rfl σ hσg,
      res_complexRankClass_of_constant_rank C sY h₁ g rfl ρ hρg,
      res_complexRankClass_of_constant_rank C sY
        (isLocallyBoundedFiniteLocallyFree_mappingCone α h₁ h₂) g rfl (coneRank ρ σ)
        (isFiniteLocallyFreeOfRank_pullbackComplex_mappingCone_X g α ρ σ hρg hσg),
      ← add_zsmul, harith]

end Stacks.Chow

end
