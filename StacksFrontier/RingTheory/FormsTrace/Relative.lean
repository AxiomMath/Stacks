module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.TraceMapPositive.AbsoluteFormsComparison
public import StacksFrontier.RingTheory.FormsTrace.Defs

/-!
# Trace maps on relative differential forms

Let `Λ → A → B` be ring maps with `A → B` finite projective, and let
`Θ^p : Ω^p_{B/ℤ} → Ω^p_{A/ℤ}` be a family of maps on absolute forms which is linear over the
forms of `A` (`Stacks.FormsTrace.IsWedgeLinear`). Property (3) of Stacks, Proposition 0FLC says
that `Θ` induces maps `Θ_Λ^p : Ω^p_{B/Λ} → Ω^p_{A/Λ}` on the forms relative to `Λ`, forming a
map of relative de Rham complexes.

The descended maps are `KaehlerDifferential.relativeTrace`, with defining property
`KaehlerDifferential.relativeTrace_absoluteToRelative`, uniqueness
`KaehlerDifferential.eq_relativeTrace`, linearity over the relative forms of `A`
(`KaehlerDifferential.relativeTrace_wedgeMul`) and compatibility with the relative de Rham
differentials (`KaehlerDifferential.relativeTrace_deRhamDifferential`). Existence and uniqueness of
the descended family are stated together, and the relative maps satisfy property (1) of Lemma 0FLB.

## Main results

* `Stacks.FormsTrace.IsWedgeLinear.existsUnique_relative`: **there is exactly one family
  `Θ_Λ` with `Θ_Λ ∘ (Ω_{B/ℤ} → Ω_{B/Λ}) = (Ω_{A/ℤ} → Ω_{A/Λ}) ∘ Θ`**.
* `Stacks.FormsTrace.IsFormsTrace.relativeTrace_smul_mapExteriorPower`: **property (1) for the
  relative maps**, `Θ_Λ(b · ρ^*ω) = Trace_{B/A}(b) · ω` for a relative form `ω` of `A`.

## References

* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
-/

@[expose] public noncomputable section

open KaehlerDifferential

universe u

namespace Stacks.FormsTrace

variable {Λ A B : Type u} [CommRing Λ] [CommRing A] [CommRing B] [Algebra Λ A] [Algebra Λ B]
  [Algebra A B] [IsScalarTower Λ A B]

variable (Λ) in
/-- **Stacks 0FLC (3), existence and uniqueness of the descended maps, on rings.** A family
`Θ^p : Ω^p_{B/ℤ} → Ω^p_{A/ℤ}` which is linear over the forms of `A` induces exactly one family
`Θ_Λ^p : Ω^p_{B/Λ} → Ω^p_{A/Λ}` of `A`-linear maps compatible with the surjections
`Ω^p_{·/ℤ} → Ω^p_{·/Λ}`. It is `KaehlerDifferential.relativeTrace Λ Θ hW`. -/
theorem IsWedgeLinear.existsUnique_relative
    {Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]} (hW : IsWedgeLinear A B Θ) :
    ∃! ΘΛ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄Λ] →ₗ[A] ⋀[A]^p Ω[A⁄Λ],
      ∀ (p : ℕ) (x : ⋀[B]^p Ω[B⁄ℤ]),
        ΘΛ p (absoluteToRelative Λ B p x) = absoluteToRelative Λ A p (Θ p x) :=
  ⟨relativeTrace Λ Θ hW, relativeTrace_absoluteToRelative Λ Θ hW,
    fun ΘΛ hΘΛ => funext fun p => eq_relativeTrace Λ Θ hW p (ΘΛ p) (hΘΛ p)⟩

variable [Module.Finite A B] [Module.Projective A B]

variable (Λ) in
/-- **Stacks 0FLB (1) for the relative maps of 0FLC (3).** If `Θ` is compatible with the trace
(`Θ(b · f^*ω) = Trace_{B/A}(b) · ω`) and linear over the forms of `A`, the induced maps on
relative forms satisfy `Θ_Λ(b · ρ^*ω) = Trace_{B/A}(b) · ω` for `b ∈ B` and `ω ∈ Ω^p_{A/Λ}`,
where `ρ^* = KaehlerDifferential.mapExteriorPower Λ A B p` is the pull-back of relative forms. -/
theorem IsFormsTrace.relativeTrace_smul_mapExteriorPower
    {Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]} (hT : IsFormsTrace A B Θ)
    (hW : IsWedgeLinear A B Θ) (p : ℕ) (b : B) (ω : ⋀[A]^p Ω[A⁄Λ]) :
    relativeTrace Λ Θ hW p (b • mapExteriorPower Λ A B p ω) = trace A B b • ω := by
  obtain ⟨ω', rfl⟩ := absoluteToRelative_surjective Λ A p ω
  rw [← absoluteToRelative_formsMap, ← map_smul, relativeTrace_absoluteToRelative]
  exact (congrArg (absoluteToRelative Λ A p) (hT p b ω')).trans (map_smul _ _ _)

end Stacks.FormsTrace

end
