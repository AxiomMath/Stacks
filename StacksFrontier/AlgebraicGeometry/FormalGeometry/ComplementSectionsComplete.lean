module

public import StacksFrontier.RingTheory.AdicCompletion.TateModule.FiniteComplete
public import StacksFrontier.RingTheory.AdicCompletion.TateModule.ShortExactComplete
public import StacksFrontier.RingTheory.AdicCompletion.TateModule.Vanishing
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.Comparison

/-!
# Completeness of sections away from `V(𝔞)` and vanishing of a Tate module

Let `A` be a Noetherian ring which is `f`-adically complete, let `𝔞` be a finitely generated ideal,
let `M` be a finite `A`-module and let `U = Spec(A) ∖ V(𝔞)`. These are the two hypotheses of
Stacks 0EII on the local cohomology of `M`, each turned into a statement about `U`:

* if `H¹_𝔞(M)` is annihilated by a power of `f`, then `Γ(U, M̃)` is `f`-adically complete;
* if `H²_𝔞(M)` is annihilated by a power of `f`, then the `f`-adic Tate module of `H¹(U, M̃)`
  vanishes.

The degree-zero formal-functions sequence
`0 ⟶ Γ(U, M̃)^∧ ⟶ lim H⁰(U, M̃/fⁿM̃) ⟶ T_f(H¹(U, M̃)) ⟶ 0` of Stacks 0BLD, in which these are
the first and third terms, is not formalized in this library.

## Main results

* `Stacks.Algebraization.smul_top_eq_bot_of_pow_smul_eq_zero` — the annihilation hypothesis of
  Stacks 0EII rewritten as `(f)ᶜ • ⊤ = ⊥`.
* `Stacks.Algebraization.isAdicComplete_complementGlobalSections` — the sections of `M̃` on
  `U = Spec(A) ∖ V(𝔞)` are `f`-adically complete.
* `Stacks.Algebraization.isZero_adicTateModule_homology_complement` — the `f`-adic Tate module of
  `H¹(U, M̃)` vanishes.

## References

* [Stacks Project, Tag 0EII](https://stacks.math.columbia.edu/tag/0EII)
* [Stacks Project, Tag 0BLD](https://stacks.math.columbia.edu/tag/0BLD)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- A module annihilated by `f ^ c` is annihilated by the `c`-th power of the ideal `(f)`. -/
theorem smul_top_eq_bot_of_pow_smul_eq_zero {A : Type u} [CommRing A] {Q : Type*}
    [AddCommGroup Q] [Module A Q] (f : A) (c : ℕ) (h : ∀ x : Q, f ^ c • x = 0) :
    (Ideal.span {f}) ^ c • (⊤ : Submodule A Q) = ⊥ := by
  rw [Ideal.span_singleton_pow, eq_bot_iff, Submodule.smul_le]
  intro a ha x _
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp ha
  rw [mul_smul, smul_comm, h x, smul_zero]
  exact Submodule.zero_mem _

/-- **The sections away from `V(𝔞)` of the sheaf associated to a finite module are complete.**
Let `A` be a Noetherian ring which is `f`-adically complete, let `𝔞` be a finitely generated ideal
and let `M` be a finite `A`-module whose first local cohomology module `H¹_𝔞(M)` is annihilated by
`f ^ c`. Then the `A`-module `Γ(U, M̃)` of sections on `U = Spec(A) ∖ V(𝔞)` is `f`-adically
complete. -/
theorem isAdicComplete_complementGlobalSections
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG) (f : A)
    (M : ModuleCat.{u} A) [Module.Finite A M] [IsAdicComplete (Ideal.span {f}) A]
    (c : ℕ) (h1 : ∀ x : localCohomologyModule A I hI M 1, f ^ c • x = 0) :
    IsAdicComplete (Ideal.span {f})
      (complementGlobalSections A I (complementTilde A I M)) := by
  obtain ⟨D⟩ := nonempty_localizationTriangleData.{u, u} A I hI
  set F := complementTilde A I M
  set r := restrictionToComplement D M F (Iso.refl _)
  set b := localizationBoundary D M F (Iso.refl _)
  have hexact : Function.Exact r b :=
    exact_restrictionToComplement_localizationBoundary D M F (Iso.refl _)
  have hsurj : Function.Surjective b := localizationBoundary_surjective D M F (Iso.refl _)
  set K := LinearMap.ker r
  set r' := K.liftQ r le_rfl
  have hr'inj : Function.Injective r' :=
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
  have : Module.Finite A (M ⧸ K) := Module.Finite.of_surjective K.mkQ K.mkQ_surjective
  have : IsAdicComplete (Ideal.span {f}) (M ⧸ K) :=
    AdicCompletion.isAdicComplete_of_finite_of_isNoetherianRing _ _
  have hexact' : Function.Exact r' b := fun y ↦ by
    rw [hexact y]
    refine ⟨fun ⟨x, hx⟩ ↦ ⟨K.mkQ x, hx⟩, fun ⟨x, hx⟩ ↦ ?_⟩
    obtain ⟨x₀, rfl⟩ := K.mkQ_surjective x
    exact ⟨x₀, hx⟩
  exact AdicCompletion.isAdicComplete_of_shortExact_of_pow_smul_top_eq_bot _ hr'inj hexact'
    hsurj (smul_top_eq_bot_of_pow_smul_eq_zero f c h1)

/-- **The Tate module of the first cohomology of the complement vanishes.** If the second local
cohomology module `H²_𝔞(M)` is annihilated by `f ^ c`, then the `f`-adic Tate module of
`H¹(U, M̃)`, the first cohomology of derived sections on `U = Spec(A) ∖ V(𝔞)`, is a zero object. -/
theorem isZero_adicTateModule_homology_complement
    {A : Type u} [CommRing A] {I : Ideal A} {hI : I.FG}
    (D : LocalizationTriangleData.{u, u} A I hI) (M : ModuleCat.{u} A) (f : A) (c : ℕ)
    (h2 : ∀ x : localCohomologyModule A I hI M 2, f ^ c • x = 0) :
    Limits.IsZero (CompletionSequences.adicTateModule A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).obj (D.complement.obj M)) f) := by
  refine Stacks.TateModule.isZero_adicTateModule_of_pow_smul_eq_zero A _ f c fun x ↦ ?_
  set e := homologyComplementIsoLocalCohomologyModule D M 1 le_rfl with he
  have hinj : Function.Injective e.hom.hom :=
    fun _ _ h ↦ (ModuleCat.mono_iff_injective e.hom).1 inferInstance h
  refine hinj ?_
  rw [map_smul, _root_.map_zero]
  exact h2 (e.hom x)

end Stacks.Algebraization

end
