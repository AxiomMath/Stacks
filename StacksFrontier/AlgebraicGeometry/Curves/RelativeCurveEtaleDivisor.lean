module

public import StacksFrontier.RingTheory.Etale.SeparatingDivisor
public import StacksFrontier.RingTheory.Smooth.LocallyStandardSmoothDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# An étale divisor on an affine chart of a family of smooth curves

Let `g : U ⟶ W` be smooth of relative dimension one and affine, `W` integral and locally
noetherian over a field `k` of characteristic `p`. Around the image of any point `u` of `U` there
is a nonempty affine open `W₀ ⊆ W` such that, with `A = Γ(W, W₀)` and `B = Γ(U, g⁻¹ W₀)`, the
étale divisor of `Polynomial.exists_etale_divisor_of_locally_isStandardSmooth` exists: `a ≠ 0` in
`A`, `t ∈ B` and `h ∈ A[X]` monic of positive degree, with every element of `B` times a power of
`a` integral over `A[X]` through `t`, and `B_a ⧸ (h(t))` finite étale over `A_a`.

The hypotheses of the algebraic statement are read off the chart: `A` is a noetherian domain of
characteristic `p` (it is a nonzero `k`-algebra), `A ⟶ B` is of finite type and locally standard
smooth of relative dimension one (`AlgebraicGeometry.HasRingHomProperty.appLE`); `B` is flat over
the domain `A` and nonzero (it contains `u`), so its generic fibre is nonzero, and has dimension
one (`Algebra.ringKrullDim_eq_of_locally_isStandardSmoothOfRelativeDimension`).

This is the divisor along which the Gysin map of `R² g_!` is taken in the reduction of the weight
bound of Weil II ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `AlgebraicGeometry.exists_etale_divisor_of_smoothOfRelativeDimension_one`.
-/

public section

open CategoryTheory Polynomial

universe u

namespace AlgebraicGeometry

/-- **An étale divisor on an affine chart of a family of smooth curves.** -/
theorem exists_etale_divisor_of_smoothOfRelativeDimension_one {U W : Scheme.{u}} (g : U ⟶ W)
    [SmoothOfRelativeDimension 1 g] [IsAffineHom g] [LocallyOfFiniteType g]
    [IsLocallyNoetherian W] [IsIntegral W] (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (fW : W ⟶ Spec (.of k)) (u : U) :
    ∃ W₀ : W.affineOpens, g.base u ∈ W₀.1 ∧
      letI : Algebra Γ(W, W₀) Γ(U, g ⁻¹ᵁ W₀) := (g.appLE W₀ (g ⁻¹ᵁ W₀) le_rfl).hom.toAlgebra
      ∃ (a : Γ(W, W₀)) (t : Γ(U, g ⁻¹ᵁ W₀)) (h : Γ(W, W₀)[X]), a ≠ 0 ∧ h.Monic ∧
        0 < h.natDegree ∧
        (∀ x : Γ(U, g ⁻¹ᵁ W₀), ∃ n : ℕ,
          (aeval t : Γ(W, W₀)[X] →ₐ[Γ(W, W₀)] Γ(U, g ⁻¹ᵁ W₀)).toRingHom.IsIntegralElem
            (a ^ n • x)) ∧
        ∀ (A' B' : Type u) [CommRing A'] [CommRing B'] [Algebra Γ(W, W₀) A']
          [Algebra Γ(U, g ⁻¹ᵁ W₀) B'] [Algebra A' B'] [Algebra Γ(W, W₀) B']
          [IsScalarTower Γ(W, W₀) A' B'] [IsScalarTower Γ(W, W₀) Γ(U, g ⁻¹ᵁ W₀) B']
          [IsLocalization.Away a A'] [IsLocalization (Algebra.algebraMapSubmonoid
            Γ(U, g ⁻¹ᵁ W₀) (Submonoid.powers a)) B'],
          Algebra.Etale A' (B' ⧸ Ideal.span {algebraMap Γ(U, g ⁻¹ᵁ W₀) B' (aeval t h)}) ∧
          Module.Finite A' (B' ⧸ Ideal.span {algebraMap Γ(U, g ⁻¹ᵁ W₀) B' (aeval t h)}) := by
  obtain ⟨W₀, hW₀, hmem, -⟩ := exists_isAffineOpen_mem_and_subset
    (show g.base u ∈ (⊤ : W.Opens) from trivial)
  refine ⟨⟨W₀, hW₀⟩, hmem, ?_⟩
  let : Algebra Γ(W, W₀) Γ(U, g ⁻¹ᵁ W₀) := (g.appLE W₀ (g ⁻¹ᵁ W₀) le_rfl).hom.toAlgebra
  have : Nonempty W₀ := ⟨⟨_, hmem⟩⟩
  have : Nonempty (g ⁻¹ᵁ W₀) := ⟨⟨u, hmem⟩⟩
  have : IsNoetherianRing Γ(W, W₀) := IsLocallyNoetherian.component_noetherian ⟨W₀, hW₀⟩
  -- the characteristic
  let φ : k →+* Γ(W, W₀) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ fW.appLE ⊤ W₀ (by simp)).hom
  have : CharP Γ(W, W₀) p := charP_of_injective_ringHom φ.injective p
  -- smoothness and finite type of the chart
  have hsm : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap Γ(W, W₀) Γ(U, g ⁻¹ᵁ W₀)) :=
    HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension 1) g inferInstance ⟨W₀, hW₀⟩
      ⟨g ⁻¹ᵁ W₀, hW₀.preimage g⟩ le_rfl
  have : Algebra.FiniteType Γ(W, W₀) Γ(U, g ⁻¹ᵁ W₀) :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) g inferInstance ⟨W₀, hW₀⟩
      ⟨g ⁻¹ᵁ W₀, hW₀.preimage g⟩ le_rfl
  have : Algebra.Smooth Γ(W, W₀) Γ(U, g ⁻¹ᵁ W₀) :=
    Algebra.smooth_of_locally_isStandardSmoothOfRelativeDimension hsm
  -- the generic fibre is nonzero and of dimension one
  let A := Γ(W, W₀)
  let B := Γ(U, g ⁻¹ᵁ W₀)
  let K := FractionRing A
  let BK := Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
  have hle : Algebra.algebraMapSubmonoid B (nonZeroDivisors A) ≤ nonZeroDivisors B := by
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_nonZeroDivisors_iff_right]
    intro b hb
    refine Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B) hs ?_
    change s • b = s • (0 : B)
    rwa [smul_zero, Algebra.smul_def, mul_comm]
  have : Nontrivial BK := (IsLocalization.injective BK hle).nontrivial
  have : Algebra.IsPushout A B K BK :=
    Algebra.isPushout_of_isLocalization (R := A) (S := nonZeroDivisors A) (A := K) (T := B)
      (B := BK)
  have hsmK : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap K BK) :=
    RingHom.locally_isStableUnderBaseChange RingHom.isStandardSmoothOfRelativeDimension_respectsIso
      (RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange 1) A B K BK hsm
  exact Polynomial.exists_etale_divisor_of_locally_isStandardSmooth A B p hsm
    (by exact_mod_cast Algebra.ringKrullDim_eq_of_locally_isStandardSmoothOfRelativeDimension hsmK)

end AlgebraicGeometry
