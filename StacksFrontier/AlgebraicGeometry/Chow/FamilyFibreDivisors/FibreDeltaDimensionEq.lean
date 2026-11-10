module

public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.FibreDeltaDimension

/-!
# The delta-dimension of a nonempty fibre of an integral family over the projective line

Let `W ⊆ X ×_S 𝐏¹_S` be an integral closed subscheme contained in neither of the two
distinguished sections. If the zero fibre of `W` is nonempty, its delta-dimension is exactly one
less than that of `W`; likewise for the infinity fibre. So an integral `W` dominating `𝐏¹` has
relative dimension `k + 1` exactly when its (nonempty) zero fibre has delta-dimension `k`.

The bound `dim_δ (fibre) ≤ dim_δ W - 1` is `Stacks.Chow.schemeDeltaDimension_zeroFiber_le`. The
equality is the same argument read for every component: the zero divisor of `W` is an effective
Cartier divisor on `W` (Tag 02S4 part (1)), each of its irreducible components has delta-dimension
`dim_δ W - 1` (Tag 02RK), so as soon as there is a component the divisor has exactly that
delta-dimension, and the fibre has the same delta-dimension as the divisor.

## Main results

* `Stacks.Chow.schemeDeltaDimension_zeroFiber_eq_add_neg_one`,
  `Stacks.Chow.schemeDeltaDimension_infinityFiber_eq_add_neg_one`: the equality for a nonempty
  fibre.
* `Stacks.Chow.schemeDeltaDimension_zeroFiber_eq`,
  `Stacks.Chow.schemeDeltaDimension_infinityFiber_eq`: a family of relative dimension `k + 1`
  with a nonempty fibre has a fibre of delta-dimension `k`.
* `Stacks.Chow.relativeDimension_genericPoints_eq_of_schemeDeltaDimension_zeroFiber_eq`,
  `Stacks.Chow.relativeDimension_genericPoints_eq_of_schemeDeltaDimension_infinityFiber_eq`:
  conversely, a fibre of delta-dimension `k` forces the family to have relative dimension
  `k + 1`.

## References

* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 02RK](https://stacks.math.columbia.edu/tag/02RK)
* [Stacks Project, Tag 0B1M](https://stacks.math.columbia.edu/tag/0B1M)
* [Stacks Project, Tag 0B1U](https://stacks.math.columbia.edu/tag/0B1U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (W : (projectiveLineProduct f).IdealSheafData)

/-- **An effective Cartier divisor with a component drops the delta-dimension by exactly one.**
Every irreducible component of an effective Cartier divisor on an integral scheme has
delta-dimension one less than the scheme (Tag 02RK), and the delta-dimension of the divisor is the
supremum over its components. -/
theorem schemeDeltaDimension_isEffectiveCartierDivisor_eq {Y : Scheme.{u}} (p : Y ⟶ C.S)
    [LocallyOfFiniteType p] [IsIntegral Y] (D : Y.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hne : Nonempty (irreducibleComponents D.subscheme)) :
    schemeDeltaDimension C (D.subschemeι ≫ p) = schemeDeltaDimension C p + (-1 : ℤ) := by
  rw [schemeDeltaDimension_eq_iSup]
  simp_rw [deltaDimension_irreducibleComponent_isEffectiveCartierDivisor C p D hD]
  exact ciSup_const

/-- A closed subscheme whose delta-dimension is not `⊥` has an irreducible component. -/
private theorem nonempty_irreducibleComponents_of_schemeDeltaDimension_ne_bot {Y : Scheme.{u}}
    (p : Y ⟶ C.S) [LocallyOfFiniteType p] (h : schemeDeltaDimension C p ≠ ⊥) :
    Nonempty (irreducibleComponents Y) := by
  by_contra hcon
  rw [not_nonempty_iff] at hcon
  exact h (by rw [schemeDeltaDimension_eq_iSup]; exact iSup_of_empty _)

/-- A scheme with a point has delta-dimension different from `⊥`. -/
private theorem schemeDeltaDimension_ne_bot_of_nonempty {Y : Scheme.{u}} (p : Y ⟶ C.S)
    [LocallyOfFiniteType p] (y : Y) : schemeDeltaDimension C p ≠ ⊥ := by
  obtain ⟨Z, hZ, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({y} : Set Y) isIrreducible_singleton
  rw [schemeDeltaDimension_eq_iSup]
  exact ne_bot_of_le_ne_bot (by exact_mod_cast (WithBot.coe_ne_bot (a := _)))
    (le_iSup _ (⟨Z, hZ⟩ : irreducibleComponents Y))

/-- **The delta-dimension of a nonempty zero fibre.** For an integral `W` not contained in the
image of the zero section and meeting it, the zero fibre of `W` has delta-dimension exactly one
less than `W`. -/
theorem schemeDeltaDimension_zeroFiber_eq_add_neg_one [IsIntegral W.subscheme]
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection f))
    (hne : Nonempty (irreducibleComponents (zeroDivisor f W).subscheme)) :
    schemeDeltaDimension C ((zeroFiber f W).subschemeι ≫ f) =
      schemeDeltaDimension C (familyBase f W) + (-1 : ℤ) :=
  (schemeDeltaDimension_zeroFiber_eq_zeroDivisor C f W).trans
    (schemeDeltaDimension_isEffectiveCartierDivisor_eq C (familyBase f W) (zeroDivisor f W)
      (zeroDivisor_isEffectiveCartierDivisor f W h₀) hne)

/-- **The delta-dimension of a nonempty infinity fibre.** The infinity-section twin of
`Stacks.Chow.schemeDeltaDimension_zeroFiber_eq_add_neg_one`. -/
theorem schemeDeltaDimension_infinityFiber_eq_add_neg_one [IsIntegral W.subscheme]
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f))
    (hne : Nonempty (irreducibleComponents (infinityDivisor f W).subscheme)) :
    schemeDeltaDimension C ((infinityFiber f W).subschemeι ≫ f) =
      schemeDeltaDimension C (familyBase f W) + (-1 : ℤ) :=
  (schemeDeltaDimension_infinityFiber_eq_infinityDivisor C f W).trans
    (schemeDeltaDimension_isEffectiveCartierDivisor_eq C (familyBase f W) (infinityDivisor f W)
      (infinityDivisor_isEffectiveCartierDivisor f W hInf) hne)

/-- **A family of relative dimension `k + 1` with a nonempty zero fibre has a zero fibre of
delta-dimension `k`.** -/
theorem schemeDeltaDimension_zeroFiber_eq [IsIntegral W.subscheme] {k : ℤ}
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase f W) ξ.1 = k + 1)
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection f))
    (hne : Nonempty (zeroFiber f W).subscheme) :
    schemeDeltaDimension C ((zeroFiber f W).subschemeι ≫ f) = (k : EInt) := by
  have hne' : Nonempty (irreducibleComponents (zeroDivisor f W).subscheme) := by
    refine nonempty_irreducibleComponents_of_schemeDeltaDimension_ne_bot C
      ((zeroDivisor f W).subschemeι ≫ familyBase f W) ?_
    rw [← schemeDeltaDimension_zeroFiber_eq_zeroDivisor C f W]
    exact schemeDeltaDimension_ne_bot_of_nonempty C _ hne.some
  rw [schemeDeltaDimension_zeroFiber_eq_add_neg_one C f W h₀ hne',
    schemeDeltaDimension_familyBase C f W hDim, coe_add_neg_one]

/-- **A family of relative dimension `k + 1` with a nonempty infinity fibre has an infinity fibre
of delta-dimension `k`.** -/
theorem schemeDeltaDimension_infinityFiber_eq [IsIntegral W.subscheme] {k : ℤ}
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase f W) ξ.1 = k + 1)
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f))
    (hne : Nonempty (infinityFiber f W).subscheme) :
    schemeDeltaDimension C ((infinityFiber f W).subschemeι ≫ f) = (k : EInt) := by
  have hne' : Nonempty (irreducibleComponents (infinityDivisor f W).subscheme) := by
    refine nonempty_irreducibleComponents_of_schemeDeltaDimension_ne_bot C
      ((infinityDivisor f W).subschemeι ≫ familyBase f W) ?_
    rw [← schemeDeltaDimension_infinityFiber_eq_infinityDivisor C f W]
    exact schemeDeltaDimension_ne_bot_of_nonempty C _ hne.some
  rw [schemeDeltaDimension_infinityFiber_eq_add_neg_one C f W hInf hne',
    schemeDeltaDimension_familyBase C f W hDim, coe_add_neg_one]

/-- The relative dimension of the generic point of an integral `W` from its delta-dimension. -/
private theorem relativeDimension_genericPoints_eq_of_schemeDeltaDimension_familyBase
    [IsIntegral W.subscheme] {k : ℤ}
    (h : schemeDeltaDimension C (familyBase f W) + (-1 : ℤ) = (k : EInt)) :
    ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase f W) ξ.1 = k + 1 := by
  rintro ⟨x, hx⟩
  rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
  subst hx
  rw [schemeDeltaDimension_eq_genericPoint C (familyBase f W), ← coe_add_coe_eq_coe_add] at h
  have h2 := WithBotTop.coe_injective h
  change relativeDimension C.dimensionFunction (familyBase f W) (genericPoint W.subscheme) = k + 1
  omega

/-- **A zero fibre of delta-dimension `k` forces relative dimension `k + 1`.** For an integral
`W` not contained in the image of the zero section, if the zero fibre of `W` has delta-dimension
`k` then the generic point of `W` has relative dimension `k + 1` over the base. -/
theorem relativeDimension_genericPoints_eq_of_schemeDeltaDimension_zeroFiber_eq
    [IsIntegral W.subscheme] {k : ℤ}
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection f))
    (hk : schemeDeltaDimension C ((zeroFiber f W).subschemeι ≫ f) = (k : EInt)) :
    ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase f W) ξ.1 = k + 1 := by
  have hne : Nonempty (irreducibleComponents (zeroDivisor f W).subscheme) := by
    refine nonempty_irreducibleComponents_of_schemeDeltaDimension_ne_bot C
      ((zeroDivisor f W).subschemeι ≫ familyBase f W) ?_
    rw [← schemeDeltaDimension_zeroFiber_eq_zeroDivisor C f W, hk]
    exact_mod_cast WithBot.coe_ne_bot
  refine relativeDimension_genericPoints_eq_of_schemeDeltaDimension_familyBase C f W ?_
  rw [← schemeDeltaDimension_zeroFiber_eq_add_neg_one C f W h₀ hne, hk]

/-- **An infinity fibre of delta-dimension `k` forces relative dimension `k + 1`.** The
infinity-section twin of
`Stacks.Chow.relativeDimension_genericPoints_eq_of_schemeDeltaDimension_zeroFiber_eq`. -/
theorem relativeDimension_genericPoints_eq_of_schemeDeltaDimension_infinityFiber_eq
    [IsIntegral W.subscheme] {k : ℤ}
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f))
    (hk : schemeDeltaDimension C ((infinityFiber f W).subschemeι ≫ f) = (k : EInt)) :
    ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase f W) ξ.1 = k + 1 := by
  have hne : Nonempty (irreducibleComponents (infinityDivisor f W).subscheme) := by
    refine nonempty_irreducibleComponents_of_schemeDeltaDimension_ne_bot C
      ((infinityDivisor f W).subschemeι ≫ familyBase f W) ?_
    rw [← schemeDeltaDimension_infinityFiber_eq_infinityDivisor C f W, hk]
    exact_mod_cast WithBot.coe_ne_bot
  refine relativeDimension_genericPoints_eq_of_schemeDeltaDimension_familyBase C f W ?_
  rw [← schemeDeltaDimension_infinityFiber_eq_add_neg_one C f W hInf hne, hk]

end Stacks.Chow

end
