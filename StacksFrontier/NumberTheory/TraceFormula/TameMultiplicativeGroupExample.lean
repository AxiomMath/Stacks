module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.ConstantAction
public import StacksFrontier.NumberTheory.TraceFormula.CommutativeExampleInverse

/-!
# The case `a = 1` of the commutative example occurs for `π₁ᵗ(𝐆_{m,𝔽_p}, η̄)`

[Stacks, Tag 03VQ] considers extensions `1 → G = Ẑ^{(q)} → Γ → Ẑ → 1`, `F ↦ 1`, with
`F x F⁻¹ = u x`, having an abstract trace formula ([Stacks, Tag 03VO]) with integer `q`, and
states that the special case `a = qu = 1` occurs with `Γ = π₁ᵗ(𝐆_{m,𝔽_p}, η̄)`,
`#S_1 = q - 1` and `#S_2 = ((q² - 1) - (q - 1))/2`.

For a finite field `k` with `q` elements, `tameFundamentalGroupEquiv` identifies
`Γ = Ẑ^{(q)} ⋊ Ẑ` with `F x F⁻¹ = q⁻¹ x` (so `u = q⁻¹`, `qu = 1`) with the tame fundamental group
`π₁ᵗ(𝐆_{m,k}, η̄)`, the automorphism group of the fibre functor at the geometric generic point on
the finite étale covers of `𝐆_{m,k}` tamely ramified at `0` and `∞`. Under it, the degree
`Γ → Ẑ` is the action on constants: an element of degree `d` acts on every point of every tame
cover, on the constants in `𝔽_{q^n}`, as the geometric Frobenius to the power `d mod n`; its
kernel `G = Ẑ^{(q)}` is the geometric part. The extension `Γ` has the abstract trace formula of
`commutativeExample_hasAbstractTraceFormula_inverse`, with integer `q`, `#S_1 = q - 1` and
`#S_2 = ((q² - 1) - (q - 1))/2`. For `k = 𝔽_p` this is the source's statement, `q = p`.

## Implementation notes

The abstract trace formula `Stacks.TraceFormula.AbstractTraceFormula Γ` quantifies over finite
coefficient rings and modules in the universe of `Γ`. It is stated for `Γ = Ẑ^{(p)} ⋊ Ẑ`, which is
identified with `π₁ᵗ(𝐆_{m,𝔽_p}, η̄)` by the isomorphism of topological groups in the statement;
the latter, an automorphism group of a functor on a large category, lives one universe up.

## Main results

* `AlgebraicGeometry.TameMultiplicativeGroup.tameFundamentalGroup_hasAbstractTraceFormula`: any
  finite field.
* `AlgebraicGeometry.TameMultiplicativeGroup.tameFundamentalGroup_zmod_hasAbstractTraceFormula`:
  **[Stacks, Tag 03VQ]**, `𝐆_{m,𝔽_p}`.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.TraceFormula

universe u

namespace AlgebraicGeometry.TameMultiplicativeGroup

attribute [local instance] compactSpace_gamma totallyDisconnectedSpace_gamma

/-- **The case `a = 1` occurs for the tame fundamental group of `𝐆_m` over a finite field.** For
`k` finite with `q` elements, there is an isomorphism of topological groups
`e : Ẑ^{(q)} ⋊ Ẑ ≃ₜ* π₁ᵗ(𝐆_{m,k}, η̄)`, where `F x F⁻¹ = q⁻¹ x`, under which an element of degree
`d` acts on the constants `𝔽_{q^n}` of the points of every tame cover as the geometric Frobenius to
the power `d mod n`; and this extension has an abstract trace formula with integer `q`, `qu = 1`,
`S_d` the orbits of exact size `d` of multiplication by `q` on `ℤ/(q^d - 1)`, `#S_1 = q - 1` and
`#S_2 = ((q² - 1) - (q - 1))/2`. -/
theorem tameFundamentalGroup_hasAbstractTraceFormula (k : Type u) [Field k] [Fintype k] {q : ℕ}
    (hq : Fintype.card k = q) :
    ∃ e : Gamma (inverseCharacter q) ≃ₜ* tameFundamentalGroup k,
      (∀ (γ : Gamma (inverseCharacter q)) (Y : TameCover k) (y : (tameFiberFunctor k).obj Y)
        (c : Γ(Y.obj.left, ⊤)) (n : ℕ) (hn : n ≠ 0), fiberRingHom y c ∈ frobField k n →
          fiberRingHom (autApply (e γ) Y y) c ^ (q ^ (restrictedMod 1 n hn
            (Nat.coprime_one_right n) (Multiplicative.toAdd (degree _ γ))).val) =
            fiberRingHom y c) ∧
      ∃ T : AbstractTraceFormula (Gamma (inverseCharacter q)) (degree _) (continuous_degree _)
          (degree_surjective _),
        T.q = q ∧
          (∀ x : RestrictedProfiniteIntegers q,
            frobenius (inverseCharacter q) * incl _ (Multiplicative.ofAdd x) *
                (frobenius (inverseCharacter q))⁻¹ =
              incl _ (Multiplicative.ofAdd ((qInv q : RestrictedProfiniteIntegers q) * x))) ∧
          (q : RestrictedProfiniteIntegers q) * (qInv q : RestrictedProfiniteIntegers q) = 1 ∧
          (∀ d, T.S d = Necklace.Orbits q d) ∧
          Fintype.card (T.S 1) = q - 1 ∧ Fintype.card (T.S 2) = ((q ^ 2 - 1) - (q - 1)) / 2 := by
  subst hq
  have : Fact (2 ≤ Fintype.card k) := ⟨Fintype.one_lt_card⟩
  exact ⟨tameFundamentalGroupEquiv k, fun γ Y y c n hn hc ↦
    fiberRingHom_fiberAct_pow_card γ Y y c hn hc,
    commutativeExample_hasAbstractTraceFormula_inverse (Fintype.card k)⟩

/-- **Stacks Project, Tag 03VQ: the special case `a = 1` occurs with
`Γ = π₁ᵗ(𝐆_{m,𝔽_p}, η̄)`, `#S_1 = q - 1` and `#S_2 = ((q² - 1) - (q - 1))/2`.** For `p` prime there
is an isomorphism of topological groups `e : Ẑ^{(p)} ⋊ Ẑ ≃ₜ* π₁ᵗ(𝐆_{m,𝔽_p}, η̄)`, with
`F x F⁻¹ = u x`, `u = p⁻¹`, compatible with the degrees (an element of degree `d` acts on the
constants `𝔽_{p^n}` of the points of every tame cover as the geometric Frobenius to the power
`d mod n`, so the kernel `Ẑ^{(p)}` is the geometric part); and this extension has an abstract trace
formula with integer `q = p`, `qu = a = 1`, `#S_1 = q - 1` and `#S_2 = ((q² - 1) - (q - 1))/2`. -/
@[stacks 03VQ "the special case a = 1 does occur with Γ = π₁ᵗ(𝐆_{m,𝔽_p}, η̄), #S₁ = q - 1 and \
#S₂ = ((q² - 1) - (q - 1))/2"]
theorem tameFundamentalGroup_zmod_hasAbstractTraceFormula (p : ℕ) [Fact p.Prime] :
    ∃ e : Gamma (inverseCharacter p) ≃ₜ* tameFundamentalGroup (ZMod p),
      (∀ (γ : Gamma (inverseCharacter p)) (Y : TameCover (ZMod p))
        (y : (tameFiberFunctor (ZMod p)).obj Y) (c : Γ(Y.obj.left, ⊤)) (n : ℕ) (hn : n ≠ 0),
          fiberRingHom y c ∈ frobField (ZMod p) n →
          fiberRingHom (autApply (e γ) Y y) c ^ (p ^ (restrictedMod 1 n hn
            (Nat.coprime_one_right n) (Multiplicative.toAdd (degree _ γ))).val) =
            fiberRingHom y c) ∧
      ∃ T : AbstractTraceFormula (Gamma (inverseCharacter p)) (degree _) (continuous_degree _)
          (degree_surjective _),
        T.q = p ∧
          (∀ x : RestrictedProfiniteIntegers p,
            frobenius (inverseCharacter p) * incl _ (Multiplicative.ofAdd x) *
                (frobenius (inverseCharacter p))⁻¹ =
              incl _ (Multiplicative.ofAdd ((qInv p : RestrictedProfiniteIntegers p) * x))) ∧
          (p : RestrictedProfiniteIntegers p) * (qInv p : RestrictedProfiniteIntegers p) = 1 ∧
          (∀ d, T.S d = Necklace.Orbits p d) ∧
          Fintype.card (T.S 1) = p - 1 ∧ Fintype.card (T.S 2) = ((p ^ 2 - 1) - (p - 1)) / 2 :=
  tameFundamentalGroup_hasAbstractTraceFormula (ZMod p) (ZMod.card p)

end AlgebraicGeometry.TameMultiplicativeGroup

end
