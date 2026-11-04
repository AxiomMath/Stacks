module

public import StacksFrontier.RingTheory.FormsTrace.ChartTrace
public import StacksFrontier.RingTheory.FormsTrace.FramedBaseChange
public import StacksFrontier.RingTheory.FormsTrace.FramedIndependence

/-!
# The trace maps on forms of a framed algebra

Let `B` be an `A`-algebra with a frame `f` (`Stacks.FormsTrace.ChartFrame`): a basis of `B` over
`A` with first vector `1`, together with a syntomic-good element `g` of the universal ring whose
image under the classifying map of the basis is a unit. The trace maps of the universal chart
ring of `f` (`Stacks.FormsTrace.exists_isFormsTrace_universalChart`) descend to maps
`Θ^p_{B/A} : Ω^p_B → Ω^p_A` (`Stacks.FormsTrace.ChartFrame.framedTrace`). This file fixes the
choice of the trace maps on the chart, and records that the result is independent of the frame
and compatible with base change.

## Main definitions

* `Stacks.FormsTrace.ChartFrame.trace`: the trace maps on the forms of a framed algebra.

## Main results

* `Stacks.FormsTrace.ChartFrame.isFormsTrace_trace`, `isWedgeLinear_trace`, `commutesWithD_trace`:
  property (1) of Lemma 0FLB, property (2) of Proposition 0FLC, and the compatibility with `d`.
* `Stacks.FormsTrace.ChartFrame.trace_eq`: independence of the frame.
* `Stacks.FormsTrace.ChartFrame.trace_baseChange`: compatibility with base change.
* `Stacks.FormsTrace.ChartFrame.trace_formsMap_of_isPushout`: compatibility with base change for
  arbitrary frames on the two sides, of possibly different ranks.
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.FiniteFreeAlgebra

universe u

namespace Stacks.FormsTrace

namespace ChartFrame

variable {d : ℕ} [NeZero d] {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The chosen trace maps on the forms of the universal chart ring of a frame. -/
def chartTrace (f : ChartFrame d A B) :
    ∀ p : ℕ, ⋀[f.ChartAlgebra]^p Ω[f.ChartAlgebra⁄ℤ] →ₗ[f.Chart] ⋀[f.Chart]^p Ω[f.Chart⁄ℤ] :=
  (exists_isFormsTrace_universalChart A f.good).choose

/-- The chosen trace maps on the chart have property (1) of Lemma 0FLB. -/
theorem isFormsTrace_chartTrace (f : ChartFrame d A B) :
    IsFormsTrace f.Chart f.ChartAlgebra f.chartTrace :=
  (exists_isFormsTrace_universalChart A f.good).choose_spec.1

/-- The chosen trace maps on the chart commute with `d`. -/
theorem commutesWithD_chartTrace (f : ChartFrame d A B) :
    CommutesWithD f.Chart f.ChartAlgebra f.chartTrace :=
  (exists_isFormsTrace_universalChart A f.good).choose_spec.2.2

/-- **The trace maps on the forms of a framed algebra** `Θ^p_{B/A} : Ω^p_B → Ω^p_A`. -/
def trace (f : ChartFrame d A B) : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ] :=
  f.framedTrace f.chartTrace f.isFormsTrace_chartTrace

/-- **Property (1) of Stacks, Lemma 0FLB** for the trace maps of a framed algebra. -/
theorem isFormsTrace_trace [Module.Finite A B] [Module.Projective A B] (f : ChartFrame d A B) :
    IsFormsTrace A B f.trace :=
  f.isFormsTrace_framedTrace f.isFormsTrace_chartTrace

/-- **Property (2) of Stacks, Proposition 0FLC** for the trace maps of a framed algebra. -/
theorem isWedgeLinear_trace (f : ChartFrame d A B) : IsWedgeLinear A B f.trace :=
  f.isWedgeLinear_framedTrace f.isFormsTrace_chartTrace

/-- **The trace maps of a framed algebra commute with the de Rham differentials.** -/
theorem commutesWithD_trace (f : ChartFrame d A B) : CommutesWithD A B f.trace :=
  f.commutesWithD_framedTrace f.isFormsTrace_chartTrace f.commutesWithD_chartTrace

/-- **Independence of the frame**: two frames of the same rank give the same trace maps. -/
theorem trace_eq (f₁ f₂ : ChartFrame d A B) : f₁.trace = f₂.trace :=
  f₁.framedTrace_eq f₂ f₁.isFormsTrace_chartTrace f₂.isFormsTrace_chartTrace
    (exists_isFormsTrace_comparisonChart A f₂.g f₁.good).choose_spec.1

/-- **Compatibility with base change** of the trace maps of a framed algebra. -/
theorem trace_baseChange (A' B' : Type u) [CommRing A'] [CommRing B'] [Algebra A A']
    [Algebra A' B'] [Algebra B B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B']
    [Algebra.IsPushout A B A' B'] (f : ChartFrame d A B) (p : ℕ) (x : ⋀[B]^p Ω[B⁄ℤ]) :
    (f.baseChange A' B').trace p (formsMap B B' p x) = formsMap A A' p (f.trace p x) :=
  f.framedTrace_baseChange A' B' f.isFormsTrace_chartTrace
    (f.baseChange A' B').isFormsTrace_chartTrace p x

/-- Two bases of a module over a nontrivial commutative ring, indexed by `Fin d₁` and `Fin d₂`,
have `d₁ = d₂`. -/
theorem rank_eq_of_basis {M : Type*} [AddCommGroup M] [Module A M] [Nontrivial A] {d₁ d₂ : ℕ}
    (e₁ : Module.Basis (Fin d₁) A M) (e₂ : Module.Basis (Fin d₂) A M) : d₁ = d₂ :=
  Fin.equiv_iff_eq.mp ⟨e₁.indexEquiv e₂⟩

/-- **Compatibility with base change, for arbitrary frames**: if `(A, B) → (A', B')` is a pushout
and `f`, `f'` are frames of `B/A` and `B'/A'` (of possibly different ranks), then
`Θ_{B'/A'}(g^*x) = f^*Θ_{B/A}(x)`. -/
theorem trace_formsMap_of_isPushout {d' : ℕ} [NeZero d'] (A' B' : Type u) [CommRing A']
    [CommRing B'] [Algebra A A'] [Algebra A' B'] [Algebra B B'] [Algebra A B']
    [IsScalarTower A A' B'] [IsScalarTower A B B'] [Algebra.IsPushout A B A' B']
    (f : ChartFrame d A B) (f' : ChartFrame d' A' B') (p : ℕ) (x : ⋀[B]^p Ω[B⁄ℤ]) :
    f'.trace p (formsMap B B' p x) = formsMap A A' p (f.trace p x) := by
  rcases subsingleton_or_nontrivial A' with hA' | hA'
  · have : Subsingleton (⋀[A']^p Ω[A'⁄ℤ]) := Module.subsingleton A' _
    exact Subsingleton.elim _ _
  · obtain rfl : d = d' := rank_eq_of_basis (baseChangeBasis A' B' f) f'.basis
    rw [trace_eq f' (f.baseChange A' B'), trace_baseChange]

end ChartFrame

end Stacks.FormsTrace

end
