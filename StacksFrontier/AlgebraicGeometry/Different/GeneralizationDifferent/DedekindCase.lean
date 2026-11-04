module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.DedekindDifferent.NormalTrace
public import StacksFrontier.AlgebraicGeometry.Different.DedekindDifferent.OneMemComplementaryModule
public import StacksFrontier.AlgebraicGeometry.Different.GeneralizationDifferent.Basic

/-!
# The generalized different when the Dedekind different is defined

Let `A → B` be a map for which the Dedekind different is defined, let `X = Spec(A)` and
`Y = Spec(B)`.  Then `f : Y → X` satisfies the first condition of the generalization of the
different: `A → B_𝔮` is flat at every associated prime `𝔮` of `B` and at every prime lying over
an associated prime of `A`.  The trace element of the generic fibre comes from a section of the
relative dualizing module `ω_{B/A} = Hom_A(B, A)` exactly when `1` lies in the complementary
module `L_{B/A}` — for instance when `A` is normal — and that section is then the image `c(1)`
of `1` under the trace-pairing identification `c : L_{B/A} ≃ ω_{B/A}`.  In this case the
Dedekind different is an ideal of `B` and agrees with the generalized different.

## Main results

* `Stacks.Discriminant.fractionBaseChangeFlat_of_dedekindDifferentSetup` and
  `Stacks.Discriminant.flatAtPrimesOverAssociatedPrimes_of_dedekindDifferentSetup`: the first
  condition of the generalization holds.
* `Stacks.Discriminant.exists_dual_trace_iff_one_mem_complementaryModule`: the trace element
  extends exactly when `1` lies in the complementary module.
* `Stacks.Discriminant.one_mem_complementaryModule_of_isNormalRing`: it does when `A` is
  normal.
* `Stacks.Discriminant.eq_complementaryModuleEquivDualizingModule_one`: the extension is
  `c(1)`, and in particular unique.

## Implementation notes

The relative dualizing module of the finite map `A → B` is `Module.Dual A B`, and the base
change map (49.2.3.1) to the generic fibre carries `φ` to the `Q(A)`-linear functional whose
value at the image of `b ∈ B` is the image of `φ(b)`.  Its injectivity, which the source gets
from the associated points of `ω_{V/X}` mapping to associated primes of `A`, is here
injectivity of `A → Q(A)`.  So "the trace element `τ_{V/X}` comes from a section of
`ω_{Y/X}`" is the condition that some `φ : Hom_A(B, A)` have
`φ(b) ↦ Trace_{L/K}(b)` for every `b ∈ B`, which is the form used below.

The first condition of the generalization is the geometric statement that the flat locus
contains `Ass(𝒪_Y)` and `f⁻¹(Ass(𝒪_X))`; on affines that is condition (4) of Tag 0BWL,
`Stacks.Discriminant.FlatAtPrimesOverAssociatedPrimes`, and the source's own proof is the
implication from condition (2) of that tag, which the étale generic fibre supplies.

The whole of Tag 0BWN, including the equality `𝔇_f = (𝔇_{B/A})~` of coherent ideal sheaves on
`Y`, is `Stacks.Discriminant.generalizedDifferent_spec_eq_tilde_dedekindDifferent`; the results
here are its algebraic ingredients.

## References

* [Stacks Project, Tag 0BWN](https://stacks.math.columbia.edu/tag/0BWN)
* [Stacks Project, Tag 0BWL](https://stacks.math.columbia.edu/tag/0BWL)
* [Stacks Project, Tag 0BWM](https://stacks.math.columbia.edu/tag/0BWM)
* [Stacks Project, Tag 0BW1](https://stacks.math.columbia.edu/tag/0BW1)
* [Stacks Project, Tag 0BW2](https://stacks.math.columbia.edu/tag/0BW2)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.Discriminant

universe u v

attribute [local instance] algebraDualModule

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-! ### The first condition of the generalization -/

/-- When the Dedekind different of `A → B` is defined, nonzerodivisors of `A` stay
nonzerodivisors in `B` and the generic fibre is flat over the total quotient ring: this is
condition (2) of Tag 0BWL. -/
theorem fractionBaseChangeFlat_of_dedekindDifferentSetup (setup : DedekindDifferentSetup A B) :
    FractionBaseChangeFlat A B := by
  refine ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := Submonoid.mem_map.mp hy
    exact setup.maps_nonZeroDivisors a ha
  · let : Algebra (FractionRing A) (B ⊗[A] FractionRing A) := Algebra.TensorProduct.rightAlgebra
    have : Algebra.Etale (FractionRing A) (B ⊗[A] FractionRing A) := setup.etaleGenericFiber
    exact (Module.Flat.equiv_iff
      (Algebra.TensorProduct.commRight A (FractionRing A) B).toLinearEquiv).mpr
      (Algebra.Smooth.flat _ _)

/-- **[Stacks, Tag 0BWN], condition (1).** When the Dedekind different of `A → B` is defined,
`Spec(B) → Spec(A)` satisfies the first condition of the generalization of the different: `A` is
flat at every associated prime of `B` and at every prime of `B` lying over an associated prime
of `A`. -/
theorem flatAtPrimesOverAssociatedPrimes_of_dedekindDifferentSetup
    (setup : DedekindDifferentSetup A B) : FlatAtPrimesOverAssociatedPrimes A B :=
  flatAtPrimesOverAssociatedPrimes_of_fractionBaseChangeFlat A B
    (fractionBaseChangeFlat_of_dedekindDifferentSetup setup)

/-! ### The second condition of the generalization -/

/-- **[Stacks, Tag 0BWN], condition (2).** The trace element of the generic fibre comes from a
section of the relative dualizing module `ω_{B/A} = Hom_A(B, A)` exactly when `1` lies in the
complementary module `L_{B/A}`. -/
theorem exists_dual_trace_iff_one_mem_complementaryModule (setup : DedekindDifferentSetup A B) :
    letI : Algebra (FractionRing A) (B ⊗[A] FractionRing A) :=
      Algebra.TensorProduct.rightAlgebra
    (∃ φ : Module.Dual A B, ∀ b : B,
        algebraMap A (FractionRing A) (φ b) =
          setup.trace (algebraMap B (B ⊗[A] FractionRing A) b)) ↔
      (1 : B ⊗[A] FractionRing A) ∈ setup.complementaryModule := by
  constructor
  · rintro ⟨φ, hφ⟩
    exact (one_mem_complementaryModule_iff setup).mpr fun b => ⟨φ b, hφ b⟩
  · intro h1
    exact ⟨complementaryModuleEquivDualizingModule setup ⟨1, h1⟩,
      complementaryModuleEquivDualizingModule_one_mem_apply setup h1⟩

/-- **[Stacks, Tag 0BWN], the normal case.** If `A` is a normal ring then `1` lies in the
complementary module, so the generalization applies. -/
theorem one_mem_complementaryModule_of_isNormalRing (setup : DedekindDifferentSetup A B)
    (hA : IsNormalRing A) : (1 : B ⊗[A] FractionRing A) ∈ setup.complementaryModule := by
  rw [DedekindDifferentSetup.mem_complementaryModule]
  intro b
  simpa only [mul_one] using trace_algebraMap_mem_range_of_isNormalRing setup hA b

/-- **[Stacks, Tag 0BWN], uniqueness of the extension.** A section of the relative dualizing
module `ω_{B/A} = Hom_A(B, A)` inducing the trace element of the generic fibre is the image of
`1` under the trace-pairing identification of the complementary module with `ω_{B/A}`. -/
theorem eq_complementaryModuleEquivDualizingModule_one (setup : DedekindDifferentSetup A B)
    (h1 : (1 : B ⊗[A] FractionRing A) ∈ setup.complementaryModule) (φ : Module.Dual A B)
    (hφ : letI : Algebra (FractionRing A) (B ⊗[A] FractionRing A) :=
        Algebra.TensorProduct.rightAlgebra
      ∀ b : B, algebraMap A (FractionRing A) (φ b) =
        setup.trace (algebraMap B (B ⊗[A] FractionRing A) b)) :
    φ = complementaryModuleEquivDualizingModule setup ⟨1, h1⟩ := by
  refine LinearMap.ext fun b => IsFractionRing.injective A (FractionRing A) ?_
  exact (hφ b).trans
    (complementaryModuleEquivDualizingModule_one_mem_apply setup h1 b).symm

end Stacks.Discriminant

end
