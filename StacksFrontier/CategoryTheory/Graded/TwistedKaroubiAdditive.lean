module

public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiTate
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiSummands
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# Additivity of the twisted Karoubi envelope

Let `C` be a category graded over a ring `R` with a graded monoidal structure, and let `L` be a
formal direct factor of the degree-zero category with `K(L) ≅ T(-1)`, where
`K : (X, p) ↦ (X, p, 0)` and `T(n) = (𝟙, 𝟙, n)`. Then every triple `(Z, q, n)` is isomorphic to a
triple of any larger twist `n + d`, namely `(Z, q, n + d) ⊗ K(L^{⊗ d})`. Hence, if any two triples
with the same twist have a direct sum, any two triples have a direct sum, and the twisted Karoubi
envelope has finite direct sums.

This is the reduction in the proof of Stacks 0FGF: for `n < m`,
`(Z, q, n) ≅ (Z, q, m) ⊗ (X, c₂, 0)^{⊗ (m - n)} = (Z × X^{m-n}, q ⊗ c₂ ⊗ ⋯ ⊗ c₂, m)` with
`(X, c₂, 0) ≅ 𝟏(-1)` the Lefschetz motive, which reduces direct sums to the case of equal twists.

## Main definitions

* `CategoryTheory.GradedCategory.TwistedKaroubi.raiseTwistIso`:
  `N ≅ (Z, q, n + d) ⊗ K(L^{⊗ d})` for `N = (Z, q, n)`.

## Main results

* `CategoryTheory.GradedCategory.TwistedKaroubi.hasBinaryBiproducts_of_twist_eq`: direct sums of
  triples with equal twists give all binary direct sums.
* `CategoryTheory.GradedCategory.TwistedKaroubi.hasFiniteBiproducts_of_twist_eq`: and then finite
  direct sums.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Category Idempotents Limits

namespace CategoryTheory.GradedCategory.TwistedKaroubi

universe w v u

variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [GradedCategory R C]
  [MonoidalCategory C] [IsGradedMonoidal R C]

omit [IsGradedMonoidal R C] in
/-- The triple `(𝟙, 0, 0)` with zero idempotent is a zero object. -/
theorem isZero_unitZero :
    IsZero (⟨𝟙_ C, 0, Submodule.zero_mem _, zero_comp, 0⟩ : TwistedKaroubi R C) :=
  isZero_of_p_eq_zero _ rfl

omit [IsGradedMonoidal R C] in
/-- The twisted Karoubi envelope of a graded monoidal category has a zero object. -/
theorem hasZeroObject : HasZeroObject (TwistedKaroubi R C) :=
  ⟨⟨_, isZero_unitZero⟩⟩

variable (L : Karoubi (DegreeZero R C)) (eL : (untwisted R C).obj L ≅ tateTriple R C (-1))

/-- **Raising the twist.** If `K(L) ≅ T(-1)`, then `N = (Z, q, n)` is isomorphic to
`(Z, q, n + d) ⊗ K(L^{⊗ d})`, a triple of twist `n + d`. -/
noncomputable def raiseTwistIso (N : TwistedKaroubi R C) (d : ℕ) :
    N ≅ { N with twist := N.twist + d } ⊗ (untwisted R C).obj (tensorPow L d) :=
  (twistCongrIso N (by ring : N.twist = N.twist + d + -1 * (d : ℤ))) ≪≫
    (tensorUnitTwistIso { N with twist := N.twist + d } (-1 * (d : ℤ))).symm ≪≫
      whiskerLeftIso _ ((tensorPowTateTripleIso (-1) d).symm ≪≫ (tensorPowIso eL d).symm ≪≫
        (tensorPowMapIso (untwisted R C) L d).symm)

/-- The triple `(Z, q, n + d) ⊗ K(L^{⊗ d})` has twist `n + d`. -/
theorem twist_raiseTwist (N : TwistedKaroubi R C) (d : ℕ) :
    ({ N with twist := N.twist + d } ⊗ (untwisted R C).obj (tensorPow L d)).twist =
      N.twist + d := by
  simp

include eL in
/-- **Direct sums of triples with equal twists give all binary direct sums**, when
`K(L) ≅ T(-1)`. -/
theorem hasBinaryBiproducts_of_twist_eq
    (h : ∀ M N : TwistedKaroubi R C, M.twist = N.twist → HasBinaryBiproduct M N) :
    HasBinaryBiproducts (TwistedKaroubi R C) := by
  refine ⟨fun M N ↦ ?_⟩
  rcases le_total M.twist N.twist with hMN | hNM
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, N.twist = M.twist + d := ⟨(N.twist - M.twist).toNat, by omega⟩
    have := h _ N ((twist_raiseTwist L M d).trans hd.symm)
    exact hasBinaryBiproduct_of_iso (raiseTwistIso L eL M d).symm (Iso.refl N)
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, M.twist = N.twist + d := ⟨(M.twist - N.twist).toNat, by omega⟩
    have := h M _ (hd.trans (twist_raiseTwist L N d).symm)
    exact hasBinaryBiproduct_of_iso (Iso.refl M) (raiseTwistIso L eL N d).symm

include eL in
/-- **The twisted Karoubi envelope has finite direct sums** if any two triples with the same
twist have a direct sum and `K(L) ≅ T(-1)`. -/
theorem hasFiniteBiproducts_of_twist_eq
    (h : ∀ M N : TwistedKaroubi R C, M.twist = N.twist → HasBinaryBiproduct M N) :
    HasFiniteBiproducts (TwistedKaroubi R C) := by
  have := hasBinaryBiproducts_of_twist_eq L eL h
  have : HasZeroObject (TwistedKaroubi R C) := hasZeroObject
  have : HasFiniteProducts (TwistedKaroubi R C) := hasFiniteProducts_of_has_binary_and_terminal
  exact HasFiniteBiproducts.of_hasFiniteProducts

end CategoryTheory.GradedCategory.TwistedKaroubi
