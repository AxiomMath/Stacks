module

public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerTwist

/-!
# Cohomology of the quotients `F/IⁿF` from that of the graded pieces

Let `F` be an `𝒪_X`-module and `I ⊆ 𝒪_X` a sheaf of ideals.  The quotients `F/IⁿF` sit in short
exact sequences `0 → IⁿF/Iⁿ⁺¹F → F/Iⁿ⁺¹F → F/IⁿF → 0` with `F/I⁰F = 0`.  By the long exact
cohomology sequence and induction on `n`:

1. if `Hᵖ(IⁿF/Iⁿ⁺¹F) = 0` for all `n` and `p > 0`, then `Hᵖ(F/IⁿF) = 0` for all `n` and `p > 0`;
2. if `H¹(IⁿF/Iⁿ⁺¹F) = 0`, then `H⁰(F/Iⁿ⁺¹F) ⟶ H⁰(F/IⁿF)` is surjective.

These are the two numbered conclusions in the proof of Stacks 0D39, there for `𝔪ⁿℱ ⊗ ℒ^{⊗ d}`.
The formal part is stated for any additive functor on an abelian category with enough
injectives and any tower of short exact sequences.

## Main results

* `Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_tower`: (1), abstractly.
* `Stacks.Cohomology.RightDerivedDelta.epi_rightDerived_zero_map_g`: (2), abstractly.
* `AlgebraicGeometry.Space.idealPowTowerShortComplex`: the tower of `F/IⁿF`, and its exactness.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.RightDerivedDelta

universe v u v' u'

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
  {𝒟 : Type u'} [Category.{v'} 𝒟] [Abelian 𝒟] (Q : 𝒜 ⥤ 𝒟) [Q.Additive]

/-- **Vanishing along a tower of short exact sequences.**  Let `0 → Gₙ → Tₙ₊₁ → Tₙ → 0` be
short exact with `T₀ = 0`.  If every `RᵖQ Gₙ` vanishes for `p > 0`, so does every `RᵖQ Tₙ`. -/
theorem isZero_rightDerived_tower (sc : ℕ → ShortComplex 𝒜) (hsc : ∀ n, (sc n).ShortExact)
    (e : ∀ n, (sc (n + 1)).X₃ ≅ (sc n).X₂) (h0 : IsZero (sc 0).X₃)
    (h1 : ∀ n p, 0 < p → IsZero ((Q.rightDerived p).obj (sc n).X₁)) :
    ∀ n p, 0 < p → IsZero ((Q.rightDerived p).obj (sc n).X₃) := by
  intro n
  induction n with
  | zero =>
    intro p hp
    have := h0.injective
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt hp
    exact Q.isZero_rightDerived_obj_injective_succ (0 + q) _
  | succ n ih =>
    exact fun p hp => (isZero_rightDerived_X₂ (hsc n) Q p (h1 n p hp) (ih p hp)).of_iso
      ((Q.rightDerived p).mapIso (e n))

/-- **Surjectivity in degree zero.**  For a short exact sequence `0 → X₁ → X₂ → X₃ → 0` with
`R¹Q X₁ = 0`, the map `R⁰Q X₂ ⟶ R⁰Q X₃` is an epimorphism. -/
theorem epi_rightDerived_zero_map_g {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h : IsZero ((Q.rightDerived 1).obj S.X₁)) : Epi ((Q.rightDerived 0).map S.g) := by
  obtain ⟨δ, -, hex⟩ := exists_delta_exact_composableArrows₅ hS Q
  exact ((hex 0).exact 1).epi_f (h.eq_of_tgt _ _)

end Stacks.Cohomology.RightDerivedDelta

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (I : IdealSheaves B S hS X.1 X.2) (M : Modules.{u, u} B S hS X.1 X.2)

/-- **The tower `0 → IⁿM/Iⁿ⁺¹M → M/Iⁿ⁺¹M → M/IⁿM → 0`**, as the third-isomorphism short
complex of `Iⁿ⁺¹M ⊆ IⁿM ⊆ M`. -/
abbrev idealPowTowerShortComplex (n : ℕ) : ShortComplex (Modules.{u, u} B S hS X.1 X.2) :=
  Stacks.Abelian.cokernelCompShortComplex
    (Stacks.SheafOfModules.Submodule.homOfLE (idealPowSubmodule_succ_le I n M))
    (idealPowSubmodule I n M).ι

/-- The sequence `0 → IⁿM/Iⁿ⁺¹M → M/Iⁿ⁺¹M → M/IⁿM → 0` is short exact. -/
theorem idealPowTowerShortComplex_shortExact (n : ℕ) :
    (idealPowTowerShortComplex I M n).ShortExact :=
  Stacks.Abelian.cokernelCompShortComplex_shortExact _ _

/-- The left term of the tower is the graded piece. -/
theorem idealPowTowerShortComplex_X₁ (n : ℕ) :
    (idealPowTowerShortComplex I M n).X₁ = idealPowGradedPiece I M n :=
  rfl

/-- The right term of the `n + 1`-st stage is the middle term of the `n`-th. -/
def idealPowTowerShortComplexX₃Iso (n : ℕ) :
    (idealPowTowerShortComplex I M (n + 1)).X₃ ≅ (idealPowTowerShortComplex I M n).X₂ :=
  (cokernelIsoOfEq (Stacks.SheafOfModules.Submodule.homOfLE_comp_ι
    (idealPowSubmodule_succ_le I n M))).symm

/-- `M/I⁰M = 0`. -/
theorem isZero_idealPowTowerShortComplex_zero_X₃ : IsZero (idealPowTowerShortComplex I M 0).X₃ := by
  have : Epi (idealPowSubmodule I 0 M).ι := by
    refine ⟨fun {Z} g h hgh => ?_⟩
    rw [← Category.id_comp g, ← idealPowZeroSection_ι I M, Category.assoc, hgh,
      ← Category.assoc, idealPowZeroSection_ι, Category.id_comp]
  exact isZero_cokernel_of_epi _

end AlgebraicGeometry.Space

end
