module

public import StacksFrontier.RingTheory.Rig.LiftingUniformity
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupExtension
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.FibreDimensionBound
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0GAQ at the source's precision

`Rig.exists_algHom_lift` is Stacks 0GAQ, unconditionally and at the source's precision
`I^{n-(d+1)c}` under the source's bound `n ≥ max(q₀ + (d+1)c, 2(d+1)c + 1)`, with `d` and `q₀`
the integers of Local Cohomology, Section 0GA6, for `Gr_I(C)`.

The earlier registrations `Rig.exists_algHom_lift_of_dualSituation` and its primed form carry the
blowup cohomology as a family of `DualSituation`s and the duality input of Tag 0GAC as
hypotheses, and reach only the level `n - (2+D)c`. Here:

* the blowup cohomology is the blowup's own (`blowupDualSituationOfFiberLE`, at the fibre-dimension
  bound `d` and the threshold `qS`);
* the duality input of Tag 0GAC is not needed: the obstruction is killed by the corrected
  Tag 0GAD `Stacks.LocalCohomology.UniformityIII.exists_extension_of_split`, which follows the
  source's `d = 0` argument for every `d` and reaches the level `m - (d+1)c`;
* `d` is the maximal fibre dimension of the blowup
  (`Stacks.LocalCohomology.UniformityIII.fibreDim`), finite for `C` Noetherian.

## Main results

* `Rig.extendsAtLevel_of_fiber_le`: Tag 0GAD's extension property on the blowup, at offset
  `(d+1)c`.
* `Rig.exists_algHom_lift_of_fiber_le`: Stacks 0GAQ at any fibre-dimension bound `d` and any `q₀`
  with the defining property of `q(S)`.
* `Rig.exists_algHom_lift`: **Stacks 0GAQ**.

## References

* [Stacks Project, Tag 0GAQ](https://stacks.math.columbia.edu/tag/0GAQ)
* [Stacks Project, Tag 0GAD](https://stacks.math.columbia.edu/tag/0GAD)
* [Stacks Project, Tag 0GA6](https://stacks.math.columbia.edu/tag/0GA6)
-/

@[expose] public noncomputable section

open CategoryTheory RestrictedPowerSeries Stacks.LocalCohomology.UniformityIII
open scoped TensorProduct

namespace Rig

universe u v

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

attribute [local instance] HasDerivedCategory.standard

/-- **Tag 0GAD's extension property on the blowup of `Spec C` in `IC`**, at every level `m`
with offset `(d + 1)c`, for `d` a bound on the fibre dimensions of the blowup and `q₀` with the
defining property of `q(S)`. This is `exists_extension_of_split`. -/
theorem extendsAtLevel_of_fiber_le {C : Type u} [CommRing C] [IsNoetherianRing C]
    (JC : Ideal C) {d : ℕ}
    (hfib : ∀ s, topologicalKrullDim ((Stacks.Blowup.toSpec JC).fiber s) ≤ (d : WithBot ℕ∞))
    (q₀ : ℕ) (hq₀ : IsBaseThreshold JC q₀) (c r m : ℕ) (hm : q₀ + (d + 1) * c ≤ m) :
    ExtendsAtLevel JC m (m - (d + 1) * c) c r (Nat.sub_le m ((d + 1) * c)) := by
  intro M D hD φ
  have hcm : c ≤ m := by nlinarith
  obtain ⟨Λ, hΛ⟩ := exists_extension_of_split JC hfib q₀ hq₀ hcm D hD φ
    (f := m - (d + 1) * c) (by omega) (by omega)
  exact ⟨Λ, hΛ⟩

/-- **Stacks 0GAQ at a fibre-dimension bound.** For `d` a bound on the dimensions of the fibres of
the blowup of `Spec C` in `IC` and `q₀` with the defining property of `q(S)` for `IC`, and
`n ≥ q₀ + (d+1)c` with `n > 2(d+1)c`, every `A`-algebra map `ψₙ : B → C/IⁿC` agrees modulo
`I^{n-(d+1)c}` with the reduction of an `A`-algebra map `φ : B → C`. -/
public theorem exists_algHom_lift_of_fiber_le
    {I : Ideal A} (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) (c : ℕ)
    (hExt : ∀ a ∈ I ^ c, ∀ (N : ModuleCat.{max u v} B.carrier)
      (ξ : DerivedCategory.Ext
        (DerivedCategory.Q.obj (completedNaiveCotangentComplex B P).cochainComplex)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
      (algebraMap A B.carrier a) • ξ = 0)
    {C : Type u} [CommRing C] [IsNoetherianRing C] [Algebra A C]
    [IsAdicComplete (I.map (algebraMap A C)) C] {d : ℕ}
    (hfib : ∀ s, topologicalKrullDim
      ((Stacks.Blowup.toSpec (I.map (algebraMap A C))).fiber s) ≤ (d : WithBot ℕ∞))
    (q₀ : ℕ) (hq₀ : IsBaseThreshold (I.map (algebraMap A C)) q₀)
    (n : ℕ) (hn₁ : q₀ + (d + 1) * c ≤ n) (hn₂ : 2 * ((d + 1) * c) < n)
    (ψn : B.carrier →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n) :
    ∃ φ : B.carrier →ₐ[A] C,
      (Ideal.Quotient.factorₐ A
        (Ideal.pow_le_pow_right (Nat.sub_le n ((d + 1) * c)))).comp ψn =
      (Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (n - (d + 1) * c))).comp φ :=
  exists_algHom_lift_of_extension B P c hExt ((d + 1) * c) n hn₂
    (fun m hm => extendsAtLevel_of_fiber_le _ hfib q₀ hq₀ c P.variableCount m (by omega)) ψn

/-- **Stacks Project, Tag 0GAQ.** Let `c ≥ 0`, let `I` be an ideal of a Noetherian ring `A`, let
`B` be in the category of Stacks 0AL4 for `(A, I)`, with a completed polynomial presentation `P`,
such that `I ^ c` annihilates `Ext¹_B(NL^∧_{B/A}, N)` for every `B`-module `N`, and let `C` be a
Noetherian `I`-adically complete `A`-algebra. Denote `d = d(Gr_I(C))` and `q₀ = q(Gr_I(C))` the
integers of Local Cohomology, Section 0GA6. Then for `n ≥ max(q₀ + (d + 1)c, 2(d + 1)c + 1)`
every `A`-algebra map `ψₙ : B → C/IⁿC` agrees modulo `I^{n-(d+1)c}` with the reduction of an
`A`-algebra map `φ : B → C`.

The two integers are the defining quantities of Section 0GA6, computed on the blowup `X` of
`Spec(C)` in `IC`: `d` is the maximal dimension of the fibres of `X ⟶ Spec(C)`
(`Stacks.LocalCohomology.UniformityIII.fibreDim`, a maximum by
`Stacks.LocalCohomology.UniformityIII.topologicalKrullDim_fiber_le_fibreDim` and
`Stacks.LocalCohomology.UniformityIII.fibreDim_le`), and `q₀` is the least integer past which
the twists `𝒪_Y(q)` of the exceptional divisor have no higher cohomology and global sections
`I^q C/I^{q+1} C` (`Stacks.LocalCohomology.UniformityIII.qS`), which is the source's `q(S)`
because `Hⁱ(Y, 𝒪_Y(q))` vanishes for `i > d` anyway (Stacks 02V7;
`Stacks.LocalCohomology.UniformityIII.qS_isLeast_isBaseThresholdUpTo_fibreDim`).

**The proof.** The obstruction relation of Stacks 0GAP makes the obstruction complex
`[(C/IᵐC) ⊗ J → (C/IᵐC)ʳ]` of a lift a two-term complex whose differential splits multiplication
by `I^c`; the obstruction then dies at level `m - (d+1)c` by the corrected Tag 0GAD
(`Stacks.LocalCohomology.UniformityIII.exists_extension_of_split`), and the iteration of the
source (`Rig.exists_algHom_lift_of_extension`) passes to the limit in the complete ring `C`. The
source's own argument for Tag 0GAD reaches only `m - (2+d)c` for `d > 0`; the argument used is the
one the source gives for `d = 0` (a local lift and the vanishing of a global obstruction), carried
out for every `d`, which reaches the source's level. -/
@[stacks 0GAQ "with d = d(Gr_I(C)) and q₀ = q(Gr_I(C)) the defining quantities of Section 0GA6 \
computed on the blowup of Spec(C) in IC (maximal fibre dimension and the threshold qS), and \
NL^∧_{B/A} computed from a completed polynomial presentation P of B"]
public theorem exists_algHom_lift
    {I : Ideal A} (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) (c : ℕ)
    (hExt : ∀ a ∈ I ^ c, ∀ (N : ModuleCat.{max u v} B.carrier)
      (ξ : DerivedCategory.Ext
        (DerivedCategory.Q.obj (completedNaiveCotangentComplex B P).cochainComplex)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
      (algebraMap A B.carrier a) • ξ = 0)
    {C : Type u} [CommRing C] [IsNoetherianRing C] [Algebra A C]
    [IsAdicComplete (I.map (algebraMap A C)) C]
    (n : ℕ)
    (hn : max (qS (I.map (algebraMap A C)) +
        (fibreDim (I.map (algebraMap A C)) + 1) * c)
      (2 * ((fibreDim (I.map (algebraMap A C)) + 1) * c) + 1) ≤ n)
    (ψn : B.carrier →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n) :
    ∃ φ : B.carrier →ₐ[A] C,
      (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right
        (Nat.sub_le n ((fibreDim (I.map (algebraMap A C)) + 1) * c)))).comp ψn =
      (Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^
        (n - (fibreDim (I.map (algebraMap A C)) + 1) * c))).comp φ :=
  exists_algHom_lift_of_fiber_le B P c hExt
    (topologicalKrullDim_fiber_le_fibreDim (I.map (algebraMap A C)))
    _ (isBaseThreshold_qS _) n (le_of_max_le_left hn) (by have := le_of_max_le_right hn; omega) ψn

end Rig

end
