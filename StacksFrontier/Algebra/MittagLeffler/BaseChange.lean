module

public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.MittagLeffler.TensorProductPi

/-!
# Base change of flat, Mittag-Leffler and projective modules

Let `R → S` be a ring map and `M` an `R`-module. Each of the following properties of `M` passes
to the `S`-module `S ⊗_R M`: being flat, being Mittag-Leffler, being a direct sum of countably
generated modules, and being projective.

Flatness and projectivity are Mathlib instances. For the Mittag-Leffler condition we use the
criterion 059M: `M` is Mittag-Leffler if and only if `M ⊗_R ∏ Q_α → ∏ M ⊗_R Q_α` is injective
for every family of modules `Q_α`. For a family of `S`-modules the map for `S ⊗_R M` over `S` is
identified with the map for `M` over `R` by `(S ⊗_R M) ⊗_S Q ≅ M ⊗_R Q`. A decomposition of `M`
as an internal direct sum base changes to one of `S ⊗_R M` (`DirectSum.IsInternal.baseChange`),
and a submodule spanned by a countable set base changes to one spanned by a countable set.

## Implementation notes

As in 059M, 05A5 and 058W, the Mittag-Leffler condition is spelled out inline as condition (1)
of 059E, and "`M` is a direct sum of countably generated modules" as a set of submodules of `M`
which is independent, has supremum `⊤`, and whose members are each spanned by a countable set.
The base change is written `S ⊗[R] M`, Mathlib's order. The module and `S` share the universe
`v`, and `R` is `v`-small, so that condition 059E (1) quantifies over all finitely presented
modules on both sides.

## References

* [Stacks Project, Tag 05A3](https://stacks.math.columbia.edu/tag/05A3)
-/

@[expose] public section

open TensorProduct

universe u v

namespace Module

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
  {M : Type v} [AddCommGroup M] [Module R M]

/-- The Mittag-Leffler condition, in the form 059E (1), passes from `M` to `S ⊗_R M`. -/
theorem mittagLeffler_baseChange [Small.{v} R]
    (hM : ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
          [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) :
    ∀ (P : Type v) [AddCommGroup P] [Module S P] [Module.FinitePresentation S P]
      (f : P →ₗ[S] S ⊗[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module S Q)
        (_ : Module.FinitePresentation S Q) (g : P →ₗ[S] Q), ∀ (N : Type v) [AddCommGroup N]
          [Module S N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
  rw [mittagLeffler_iff_piRightHom_injective] at hM ⊢
  intro A Q _ _
  let _ : ∀ α, Module R (Q α) := fun α ↦ Module.compHom (Q α) (algebraMap R S)
  have : ∀ α, IsScalarTower R S (Q α) := fun α ↦
    ⟨fun r s q ↦ by change (r • s) • q = algebraMap R S r • s • q; rw [Algebra.smul_def, mul_smul]⟩
  let φ (N : Type v) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :
      (S ⊗[R] M) ⊗[S] N ≃ₗ[R] M ⊗[R] N :=
    ((TensorProduct.comm S _ N).restrictScalars R) ≪≫ₗ
      ((AlgebraTensorModule.cancelBaseChange R S S N M).restrictScalars R) ≪≫ₗ
        TensorProduct.comm R N M
  have key (x : (S ⊗[R] M) ⊗[S] (∀ α, Q α)) (α : A) :
      φ (Q α) (piRightHom S S (S ⊗[R] M) Q x α) = piRightHom R R M Q (φ (∀ α, Q α) x) α := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul y q =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul s m => simp [φ]
      | add y₁ y₂ h₁ h₂ => simp only [add_tmul, map_add, Pi.add_apply, h₁, h₂]
    | add x₁ x₂ h₁ h₂ => simp only [map_add, Pi.add_apply, h₁, h₂]
  intro x y hxy
  refine (φ (∀ α, Q α)).injective (hM A Q (funext fun α ↦ ?_))
  rw [← key, ← key, hxy]

/-- Base change along a ring map `R → S` preserves flatness, the Mittag-Leffler condition, being
a direct sum of countably generated modules, and projectivity. -/
@[stacks 05A3 "Mittag-Leffler is spelled out inline as condition (1) of 059E and \"direct sum of
countably generated modules\" as an independent set of countably spanned submodules with supremum
`⊤`, as in 059M, 05A5 and 058W. The source's `M ⊗_R S` is written `S ⊗[R] M`."]
theorem baseChange_flat_and_mittagLeffler_and_exists_sSupIndep_countable_span_and_projective
    [Small.{v} R] :
    (Module.Flat R M → Module.Flat S (S ⊗[R] M)) ∧
    ((∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
          [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) →
      ∀ (P : Type v) [AddCommGroup P] [Module S P] [Module.FinitePresentation S P]
      (f : P →ₗ[S] S ⊗[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module S Q)
        (_ : Module.FinitePresentation S Q) (g : P →ₗ[S] Q), ∀ (N : Type v) [AddCommGroup N]
          [Module S N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) ∧
    ((∃ 𝒮 : Set (Submodule R M), sSupIndep 𝒮 ∧ sSup 𝒮 = ⊤ ∧
        ∀ N ∈ 𝒮, ∃ t : Set M, t.Countable ∧ Submodule.span R t = N) →
      ∃ 𝒮 : Set (Submodule S (S ⊗[R] M)), sSupIndep 𝒮 ∧ sSup 𝒮 = ⊤ ∧
        ∀ N ∈ 𝒮, ∃ t : Set (S ⊗[R] M), t.Countable ∧ Submodule.span S t = N) ∧
    (Module.Projective R M → Module.Projective S (S ⊗[R] M)) := by
  refine ⟨fun _ ↦ inferInstance, mittagLeffler_baseChange S, ?_, fun _ ↦ inferInstance⟩
  classical
  rintro ⟨𝒮, hind, hsup, hcount⟩
  have hint : DirectSum.IsInternal fun N : 𝒮 ↦ (N : Submodule R M) := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top, ← sSup_eq_iSup']
    exact ⟨(sSupIndep_iff 𝒮).mp hind, hsup⟩
  obtain ⟨hind', hsup'⟩ :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp
      (DirectSum.IsInternal.baseChange (S := S) _ hint)
  refine ⟨Set.range fun N : 𝒮 ↦ (N : Submodule R M).baseChange S, hind'.sSupIndep_range,
    by rw [sSup_range, hsup'], ?_⟩
  rintro _ ⟨⟨N, hN⟩, rfl⟩
  obtain ⟨t, ht, rfl⟩ := hcount N hN
  exact ⟨TensorProduct.mk R S M 1 '' t, ht.image _, (Submodule.baseChange_span (A := S) t).symm⟩

end Module
