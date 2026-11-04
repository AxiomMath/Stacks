module

public import Mathlib.RingTheory.Etale.Basic
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.Completion

/-!
# The completed naive cotangent complex of a formally étale algebra

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `A → B` a formally étale algebra of finite
type.  The naive cotangent complex of a finite presentation `α : A[x₁, …, xₙ] ↠ B` is then not
merely acyclic: its differential `J / J² → ⨁ᵢ B dxᵢ` is *bijective*, injectivity being the
vanishing of `H¹(L_{B/A})` and surjectivity the vanishing of `Ω_{B/A}`.  Because a bijective
differential stays bijective after base change, Stacks 0GAF carries this to the completed naive
cotangent complex `NL^∧_{B^/A}` of the `I`-adic completion of `B`, which is therefore acyclic as
well.

This is the first step of the proof of Stacks 0GCK: the horizontal maps `A → A'` and `B → B'` of
a localization diagram are étale, so the completed naive cotangent complexes of the relative
completions `(A')^` and `(B')^` vanish.

## Main results

* `Rig.bijective_presentationDifferential` — the differential of `NL(α)` is bijective for a
  formally étale algebra.
* `Rig.bijective_completedDifferential` — the differential of `NL^∧_{B^/A}` is bijective.
* `Rig.hneg_completedComplex_eq_bot` and `Rig.subsingleton_hzero_completedComplex` —
  `H⁻¹(NL^∧_{B^/A}) = 0` and `H⁰(NL^∧_{B^/A}) = 0`.

## Implementation notes

Bijectivity rather than acyclicity is the statement proved, for two reasons: it is what the
hypotheses actually give, and it is the form that survives the two transports used here.  Base
change of an acyclic two-term complex need not be acyclic without flatness, whereas base change
of a bijective map is bijective; and the comparison of Stacks 0GAF is an isomorphism of
complexes, which transports bijectivity of the differential with no homological algebra at all.

## References

* [Stacks Project, Tag 0GAF](https://stacks.math.columbia.edu/tag/0GAF)
* [Stacks Project, Tag 0GCK](https://stacks.math.columbia.edu/tag/0GCK)
* [Stacks Project, Tag 00UQ](https://stacks.math.columbia.edu/tag/00UQ)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Rig

universe u v

section Presentation

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
  [Algebra.FormallyEtale A B] {n : ℕ} (G : Algebra.Generators A B (Fin n))

/-- For a formally étale algebra the differential `J / J² → ⨁ᵢ B dxᵢ` of the naive cotangent
complex of a finite presentation is bijective: it is injective because `H¹(L_{B/A}) = 0` and
surjective because `Ω_{B/A} = 0`. -/
public theorem bijective_presentationDifferential :
    Function.Bijective (presentationDifferential G) := by
  let : Algebra.FormallySmooth A G.toExtension.Ring :=
    Algebra.instFormallySmoothMvPolynomial (Fin n)
  have hinj : Function.Injective G.toExtension.cotangentComplex :=
    (Algebra.Extension.cotangentComplex_injective_iff G.toExtension).mpr
      Algebra.FormallyEtale.subsingleton_h1Cotangent
  have hsurj : Function.Surjective G.toExtension.cotangentComplex := fun y =>
    (Algebra.Extension.exact_cotangentComplex_toKaehler y).mp (Subsingleton.elim _ _)
  have hd : (presentationDifferential G : G.toExtension.Cotangent →ₗ[B] (Fin n → B)) =
      G.cotangentSpaceBasis.equivFun.toLinearMap ∘ₗ G.toExtension.cotangentComplex := rfl
  rw [hd, LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact G.cotangentSpaceBasis.equivFun.bijective.comp ⟨hinj, hsurj⟩

end Presentation

section Completed

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  {B : Type v} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
  [Algebra.FormallyEtale A B] {n : ℕ} (G : Algebra.Generators A B (Fin n))

/-- Base change of the differential of the naive cotangent complex of a formally étale algebra
is bijective, being the base change of a linear equivalence. -/
public theorem bijective_baseChange_presentationDifferential :
    Function.Bijective
      (baseChangedTwoTerm (adicCompletionObj I (B := B)).carrier
        (presentationDifferential G)).d :=
  (LinearEquiv.baseChange B (adicCompletionObj I (B := B)).carrier _ _
    (LinearEquiv.ofBijective _ (bijective_presentationDifferential G))).bijective

/-- **The completed naive cotangent complex of a formally étale algebra of finite type is
acyclic**, in the strong form that the differential of `NL^∧_{B^/A}` is bijective.  The
comparison of Stacks 0GAF identifies that differential with the base change along `B → B^` of
the differential of `NL(α)`, which is bijective by
`Rig.bijective_presentationDifferential`. -/
public theorem bijective_completedDifferential :
    Function.Bijective (completedComplex I G).twoTerm.d := by
  obtain ⟨hf₁, hf₀, hcomm⟩ := bijective_completionComparison I G
  have hbc := bijective_baseChange_presentationDifferential I G
  have hstep : ∀ a, (completedComplex I G).twoTerm.d ((completionComparison I G).f₁ a) =
      (completionComparison I G).f₀
        ((baseChangedTwoTerm (adicCompletionObj I (B := B)).carrier
          (presentationDifferential G)).d a) :=
    fun a => LinearMap.congr_fun hcomm a
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · obtain ⟨a, rfl⟩ := hf₁.2 x
    obtain ⟨b, rfl⟩ := hf₁.2 y
    rw [hstep, hstep] at hxy
    exact congrArg _ (hbc.1 (hf₀.1 hxy))
  · obtain ⟨w, hw⟩ := hf₀.2 z
    obtain ⟨a, ha⟩ := hbc.2 w
    exact ⟨(completionComparison I G).f₁ a, by rw [hstep, ha, hw]⟩

/-- `H⁻¹(NL^∧_{B^/A}) = 0` for a formally étale algebra of finite type. -/
public theorem hneg_completedComplex_eq_bot : (completedComplex I G).Hneg = ⊥ :=
  LinearMap.ker_eq_bot.mpr (bijective_completedDifferential I G).1

/-- `H⁰(NL^∧_{B^/A}) = 0` for a formally étale algebra of finite type. -/
public theorem subsingleton_hzero_completedComplex :
    Subsingleton (completedComplex I G).Hzero :=
  Submodule.Quotient.subsingleton_iff.mpr
    (LinearMap.range_eq_top.mpr (bijective_completedDifferential I G).2)

end Completed

end Rig

end
