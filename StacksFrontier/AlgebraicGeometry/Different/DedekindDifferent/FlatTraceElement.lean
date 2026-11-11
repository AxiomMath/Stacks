module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.DedekindDifferent.DifferentIdeal
public import StacksFrontier.AlgebraicGeometry.Different.DedekindDifferent.FlatCase
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.DedekindComparison
public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceElementUnique
public import StacksFrontier.RingTheory.TraceElement.FiniteFlat
public import StacksFrontier.RingTheory.TraceElement.Independence

/-!
# The trace element and the Dedekind different of a flat finite algebra

Let `A → B` be flat with Dedekind different defined. The relative dualizing module `ω_{B/A}` is
`Stacks.Discriminant.dualizingModule F` for any finite-open factorization `F` of `A → B`, and the
trace element `τ_{B/A} ∈ ω_{B/A}` of Tag 0BT6 is the element satisfying
`Stacks.Discriminant.IsTraceElement`. This file proves Tag 0BW3: the canonical isomorphism
`L_{B/A} → ω_{B/A}` of Tag 0BW2 sends `1` to `τ_{B/A}`, and
`𝔇_{B/A} = {b ∈ B | b ω_{B/A} ⊆ B τ_{B/A}}`.

## Main results

* `Stacks.Discriminant.complementaryModuleEquivDualizingModule_one_eq_traceElement`: Tag 0BW3 (1).
* `Stacks.Discriminant.mem_dedekindDifferentIdeal_iff_smul_mem_span_traceElement` and
  `Stacks.Discriminant.dedekindDifferent_eq_image_setOf_smul_mem_span_traceElement`: Tag 0BW3 (2).

## Implementation notes

The canonical isomorphism `L_{B/A} → ω_{B/A}` of Tag 0BW2 is
`Stacks.Discriminant.complementaryModuleEquivDualizingModule`, with target `Hom_A(B, A)`; Stacks
identifies that with `ω_{B/A}` because `A → B` is finite. Here that identification is the
composite of `Stacks.Discriminant.selfFactorizationDualEquiv` (the dualizing module of the
factorization of `A → B` through itself is `Hom_A(B, A)`) with the canonical comparison
`Stacks.Discriminant.dualizingModuleEquiv` (Tag 0BT1) to the dualizing module of an arbitrary
factorization `F`, so both parts are stated in `dualizingModule F` for every `F`. The
computation behind part (1), that the trace element `Trace_{B/A} ⊗ 1` of Tag 0BT8 is the image
of `1`, is `Stacks.Discriminant.selfFactorizationDualEquiv_finiteFlatTraceElement`.

The trace element is unique (Tag 0BT7), so it is named by its property: the statements hold for
every `τ` with `IsTraceElement F τ`, at the test universes of
`Stacks.Discriminant.isTraceElement_unique`. One exists by Tag 0BT8
(`Stacks.Discriminant.isTraceElement_finiteFlatTraceElement`) transported along Tag 0BT6
(`Stacks.Discriminant.isTraceElement_congr`).

The Noetherian and finiteness instances used to form `IsTraceElement` are those supplied by the
setup: `A` is Noetherian, `B` is finite over `A`, hence Noetherian and quasi-finite.

## References

* [Stacks Project, Tag 0BW3](https://stacks.math.columbia.edu/tag/0BW3)
* [Stacks Project, Tag 0BW2](https://stacks.math.columbia.edu/tag/0BW2)
* [Stacks Project, Tag 0BT6](https://stacks.math.columbia.edu/tag/0BT6)
* [Stacks Project, Tag 0BT7](https://stacks.math.columbia.edu/tag/0BT7)
* [Stacks Project, Tag 0BT8](https://stacks.math.columbia.edu/tag/0BT8)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v w

namespace Stacks.Discriminant

attribute [local instance] algebraDualModule

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-! ### Tag 0BW3 -/

section TraceElement

variable (setup : DedekindDifferentSetup A B) [Module.Flat A B]

/-- **Stacks Project, Tag 0BW3, part (1).** If the Dedekind different of a flat algebra `A → B`
is defined, the canonical isomorphism `L_{B/A} → ω_{B/A}` (Tag 0BW2, followed by the canonical
identification `Hom_A(B, A) ≅ ω_{B/A}` for a finite-open factorization `F`) sends `1` to the trace
element `τ_{B/A}` of Tag 0BT6. -/
@[stacks 0BW3 "part (1)"]
theorem complementaryModuleEquivDualizingModule_one_eq_traceElement :
    letI : IsNoetherianRing A := setup.isNoetherianRing
    letI : Module.Finite A B := setup.finite
    letI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
    ∀ (F : FiniteOpenFactorization.{u, v, w} A B) (τ : dualizingModule F),
      IsTraceElement.{u, v, w, u, max u v, max u v} F τ →
        dualizingModuleEquiv (selfFactorization A B) F
            (selfFactorizationDualEquiv.symm
              (complementaryModuleEquivDualizingModule setup
                ⟨1, one_mem_complementaryModule_of_flat setup⟩)) = τ := by
  let : IsNoetherianRing A := setup.isNoetherianRing
  let : Module.Finite A B := setup.finite
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  intro F τ hτ
  have h : selfFactorizationDualEquiv (finiteFlatTraceElement A B) =
      complementaryModuleEquivDualizingModule setup
        ⟨1, one_mem_complementaryModule_of_flat setup⟩ :=
    selfFactorizationDualEquiv_finiteFlatTraceElement setup
  rw [← h, LinearEquiv.symm_apply_apply]
  exact isTraceElement_unique F
    ((isTraceElement_congr (selfFactorization A B) F _).mp
      (isTraceElement_finiteFlatTraceElement A B)) hτ

/-- **Stacks Project, Tag 0BW3, part (2), membership form.** If the Dedekind different of a flat
algebra `A → B` is defined, an element `b ∈ B` lies in the Dedekind different exactly when
`b ω_{B/A} ⊆ B τ_{B/A}`. -/
@[stacks 0BW3 "part (2), membership form"]
theorem mem_dedekindDifferentIdeal_iff_smul_mem_span_traceElement :
    letI : IsNoetherianRing A := setup.isNoetherianRing
    letI : Module.Finite A B := setup.finite
    letI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
    ∀ (F : FiniteOpenFactorization.{u, v, w} A B) (τ : dualizingModule F),
      IsTraceElement.{u, v, w, u, max u v, max u v} F τ → ∀ b : B,
        b ∈ dedekindDifferentIdeal setup ↔
          ∀ x : dualizingModule F, b • x ∈ Submodule.span B {τ} := by
  let : IsNoetherianRing A := setup.isNoetherianRing
  let : Module.Finite A B := setup.finite
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  intro F τ hτ b
  let Φ : Module.Dual A B ≃ₗ[B] dualizingModule F :=
    selfFactorizationDualEquiv.symm.trans (dualizingModuleEquiv (selfFactorization A B) F)
  have hΦ : Φ (complementaryModuleEquivDualizingModule setup
      ⟨1, one_mem_complementaryModule_of_flat setup⟩) = τ :=
    complementaryModuleEquivDualizingModule_one_eq_traceElement setup F τ hτ
  change algebraMap B (B ⊗[A] FractionRing A) b ∈ setup.dedekindDifferent ↔ _
  rw [mem_dedekindDifferent_iff_smul_dual_le_trace setup b]
  simp only [Submodule.mem_span_singleton]
  constructor
  · rintro h x
    obtain ⟨a, ha⟩ := h (Φ.symm x)
    exact ⟨a, by rw [← hΦ, ← map_smul, ha, map_smul, LinearEquiv.apply_symm_apply]⟩
  · rintro h g
    obtain ⟨a, ha⟩ := h (Φ g)
    refine ⟨a, Φ.injective ?_⟩
    rw [map_smul, map_smul, hΦ]
    exact ha

/-- **Stacks Project, Tag 0BW3, part (2).** If the Dedekind different of a flat algebra `A → B`
is defined, then `𝔇_{B/A} = {b ∈ B | b ω_{B/A} ⊆ B τ_{B/A}}`, as a subset of the generic fibre
`L = B ⊗_A Q(A)` in which the Dedekind different is defined. -/
@[stacks 0BW3 "part (2)"]
theorem dedekindDifferent_eq_image_setOf_smul_mem_span_traceElement :
    letI : IsNoetherianRing A := setup.isNoetherianRing
    letI : Module.Finite A B := setup.finite
    letI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
    ∀ (F : FiniteOpenFactorization.{u, v, w} A B) (τ : dualizingModule F),
      IsTraceElement.{u, v, w, u, max u v, max u v} F τ →
        (setup.dedekindDifferent : Set (B ⊗[A] FractionRing A)) =
          algebraMap B (B ⊗[A] FractionRing A) ''
            {b | ∀ x : dualizingModule F, b • x ∈ Submodule.span B {τ}} := by
  let : IsNoetherianRing A := setup.isNoetherianRing
  let : Module.Finite A B := setup.finite
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  intro F τ hτ
  have hset : (dedekindDifferentIdeal setup : Set B) =
      {b | ∀ x : dualizingModule F, b • x ∈ Submodule.span B {τ}} :=
    Set.ext (mem_dedekindDifferentIdeal_iff_smul_mem_span_traceElement setup F τ hτ)
  rw [dedekindDifferent_eq_map_ideal setup (one_mem_complementaryModule_of_flat setup),
    Submodule.map_coe]
  change (algebraMap B (B ⊗[A] FractionRing A)) '' (dedekindDifferentIdeal setup : Set B) = _
  rw [hset]

end TraceElement

end Stacks.Discriminant

end
