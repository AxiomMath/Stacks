module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.DegreewiseSymbol
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveFormalNeighborhoodSupplement

/-!
# A degreewise symbol system from any presentation of the graded pieces

`AlgebraicGeometry.SemistableReduction.DegreewiseSymbol` asks for the graded pieces
`Iₙ / Iₙ₊₁` of a multiplicative filtration to be presented as the binary forms of degree `n`.
That is more than a geometric computation delivers: the graded pieces of the
projection-kernel filtration of [Stacks, Tag 0C2K] come out as the global sections of a twist
on the projective line, and the identification of those with the binary forms is available only
after a choice. This file removes the choice from the interface. A family of `k`-vector spaces
`Wₙ` of dimension `n + 1`, each presenting `Iₙ / Iₙ₊₁` by a `scalar`-semilinear map, is already
a degreewise symbol system: both `Wₙ` and the degree-`n` forms are `k`-spaces of dimension
`n + 1`, so some `k`-linear isomorphism between them exists
(`LinearEquiv.ofFinrankEq`), and composing with it turns the presentation into a symbol.

Nothing is lost by the choice, because `DegreewiseSymbol` relates the symbols in different
degrees to one another in no way at all; see the module docstring of
`StacksFrontier/AlgebraicGeometry/SemistableReduction/DegreewiseSymbol.lean`. The dimension is the
only thing about the degree-`n` forms that its consumers use.

## What this reduces Stacks 0C2K to

Through `AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData.ofDegreewiseSymbol`
the four conclusions of [Stacks, Tag 0C2K] for an exceptional curve of the first kind follow
from a degreewise symbol system on the projection-kernel filtration whose associated graded ring
is generated in degree one. With the constructor below, producing that system needs exactly:

* the `k`-vector spaces `Wₙ`, which are `Γ(X, 𝒪_X(-D ^ n)|_D)` — of dimension `n + 1` by
  `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.finrank_restrictedNegativeTwistSections`;
* the semilinear presentations `σₙ`, which are
  `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.exists_addMonoidHom_smul_formalNeighborhoodProjection_graded` read backwards — that result
  gives the additive bijection, its kernel, and the semilinearity `σₙ (c a) = scalar c · σₙ a`,
  the last on an affine cover, since the map comes from the `𝒪_X`-linear short exact sequence of
  [Stacks, Tag 0C4T] while the scalars act by multiplication inside `Γ(Eₙ₊₁, 𝒪)`;
* degree-one generation `Iₙ₊₁ ⊆ I₁ Iₙ + Iₙ₊₂` of the associated graded ring.

The first two are proved; the third is not.

## Main definitions

* `AlgebraicGeometry.SemistableReduction.DegreewiseSymbol.ofGradedPresentation` — the symbol
  system built from semilinear presentations of the graded pieces by `k`-vector spaces of the
  right dimension.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open MvPolynomial

universe u

namespace AlgebraicGeometry.SemistableReduction

namespace DegreewiseSymbol

variable {A : Type u} [CommRing A] {k : Type u} [Field k]

/-! ### The binary forms of degree `n` as a space of dimension `n + 1` -/

/-- The binary forms of degree `n` are finite dimensional over `k`: they have the monomial basis
`MvPolynomial.homogeneousBinaryBasis`. -/
public theorem finiteDimensional_homogeneousSubmodule (k : Type u) [Field k] (n : ℕ) :
    FiniteDimensional k (homogeneousSubmodule (Fin 2) k n) :=
  Module.Finite.of_basis (homogeneousBinaryBasis k n)

/-- **The binary forms of degree `n` have dimension `n + 1`.** -/
public theorem finrank_homogeneousSubmodule (k : Type u) [Field k] (n : ℕ) :
    Module.finrank k (homogeneousSubmodule (Fin 2) k n) = n + 1 := by
  rw [Module.finrank_eq_card_basis (homogeneousBinaryBasis k n), Fintype.card_fin]

/-- A `k`-vector space of dimension `n + 1` is `k`-linearly isomorphic to the binary forms of
degree `n`. The isomorphism is a choice, and nothing below depends on which one is made. -/
public theorem nonempty_linearEquiv_homogeneousSubmodule {W : Type u} [AddCommGroup W]
    [Module k W] {n : ℕ} (hW : Module.finrank k W = n + 1) :
    Nonempty (W ≃ₗ[k] homogeneousSubmodule (Fin 2) k n) :=
  have : FiniteDimensional k W := .of_finrank_pos (by rw [hW]; omega)
  have := finiteDimensional_homogeneousSubmodule k n
  ⟨LinearEquiv.ofFinrankEq _ _ (by rw [hW, finrank_homogeneousSubmodule])⟩

/-! ### The constructor -/

/-- **A degreewise symbol system from semilinear presentations of the graded pieces.**

The data is a multiplicative filtration `I` by ideals, a residue homomorphism `scalar` onto `k`
with kernel `I₁`, and for every `n` a `k`-vector space `W n` of dimension `n + 1` together with
a map `σ n : A ⟶ W n` which, on `I n`, is additive, semilinear over `scalar`, vanishes exactly
on `I (n + 1)` and is onto `W n`. That is a presentation of `Iₙ / Iₙ₊₁` as a `k`-space of
dimension `n + 1`, one degree at a time.

The symbol is `σ n` followed by some `k`-linear isomorphism `W n ≅ (k[T₀, T₁])ₙ`, which exists
by `AlgebraicGeometry.SemistableReduction.DegreewiseSymbol`
`.nonempty_linearEquiv_homogeneousSubmodule`. Which isomorphism is chosen is immaterial: the
structure imposes no relation between different degrees, and the hypothesis its consumers add —
degree-one generation of the associated graded ring — is a statement about the filtration
alone. -/
public def ofGradedPresentation (ideal : ℕ → Ideal A) (scalar : A →+* k) (W : ℕ → Type u)
    [∀ n, AddCommGroup (W n)] [∀ n, Module k (W n)] (σ : ∀ n, A → W n)
    (finrank_W : ∀ n, Module.finrank k (W n) = n + 1)
    (ideal_zero : ideal 0 = ⊤) (ideal_succ_le : ∀ n, ideal (n + 1) ≤ ideal n)
    (mul_le : ∀ m n, ideal m * ideal n ≤ ideal (m + n))
    (ker_scalar : RingHom.ker scalar = ideal 1)
    (surjective_scalar : Function.Surjective scalar)
    (σ_add : ∀ (n : ℕ) {a b : A}, a ∈ ideal n → b ∈ ideal n → σ n (a + b) = σ n a + σ n b)
    (σ_smul : ∀ (n : ℕ) (c : A) {a : A}, a ∈ ideal n → σ n (c * a) = scalar c • σ n a)
    (σ_eq_zero_iff : ∀ (n : ℕ) {a : A}, a ∈ ideal n → (σ n a = 0 ↔ a ∈ ideal (n + 1)))
    (σ_surjective : ∀ (n : ℕ) (v : W n), ∃ a ∈ ideal n, σ n a = v) :
    DegreewiseSymbol A k :=
  let ε : ∀ n, W n ≃ₗ[k] homogeneousSubmodule (Fin 2) k n := fun n =>
    (nonempty_linearEquiv_homogeneousSubmodule (finrank_W n)).some
  { ideal := ideal
    scalar := scalar
    symbol := fun n a => (ε n (σ n a) : MvPolynomial (Fin 2) k)
    ideal_zero := ideal_zero
    ideal_succ_le := ideal_succ_le
    mul_le := mul_le
    ker_scalar := ker_scalar
    surjective_scalar := surjective_scalar
    symbol_mem := fun n {a} _ => (ε n (σ n a)).2
    symbol_add := fun n {a b} ha hb => by
      rw [σ_add n ha hb, (ε n).map_add, Submodule.coe_add]
    symbol_smul := fun n c {a} ha => by
      rw [σ_smul n c ha, (ε n).map_smul, Submodule.coe_smul]
    symbol_eq_zero_iff := fun n {a} ha => by
      rw [Submodule.coe_eq_zero, LinearEquiv.map_eq_zero_iff]
      exact σ_eq_zero_iff n ha
    surjective_symbol := fun n v hv => by
      obtain ⟨a, ha, hav⟩ := σ_surjective n ((ε n).symm ⟨v, hv⟩)
      exact ⟨a, ha, by rw [hav, LinearEquiv.apply_symm_apply]⟩ }

/-- The filtration of the degreewise symbol system built from a graded presentation is the
filtration it was given. -/
@[simp]
public theorem ofGradedPresentation_ideal (ideal : ℕ → Ideal A) (scalar : A →+* k)
    (W : ℕ → Type u) [∀ n, AddCommGroup (W n)] [∀ n, Module k (W n)] (σ : ∀ n, A → W n)
    (finrank_W : ∀ n, Module.finrank k (W n) = n + 1)
    (ideal_zero : ideal 0 = ⊤) (ideal_succ_le : ∀ n, ideal (n + 1) ≤ ideal n)
    (mul_le : ∀ m n, ideal m * ideal n ≤ ideal (m + n))
    (ker_scalar : RingHom.ker scalar = ideal 1)
    (surjective_scalar : Function.Surjective scalar)
    (σ_add : ∀ (n : ℕ) {a b : A}, a ∈ ideal n → b ∈ ideal n → σ n (a + b) = σ n a + σ n b)
    (σ_smul : ∀ (n : ℕ) (c : A) {a : A}, a ∈ ideal n → σ n (c * a) = scalar c • σ n a)
    (σ_eq_zero_iff : ∀ (n : ℕ) {a : A}, a ∈ ideal n → (σ n a = 0 ↔ a ∈ ideal (n + 1)))
    (σ_surjective : ∀ (n : ℕ) (v : W n), ∃ a ∈ ideal n, σ n a = v) :
    (ofGradedPresentation ideal scalar W σ finrank_W ideal_zero ideal_succ_le mul_le ker_scalar
      surjective_scalar σ_add σ_smul σ_eq_zero_iff σ_surjective).ideal = ideal :=
  rfl

end DegreewiseSymbol

end AlgebraicGeometry.SemistableReduction

end
