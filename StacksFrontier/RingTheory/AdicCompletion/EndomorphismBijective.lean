module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.FiniteType
public import StacksFrontier.RingTheory.AdicCompletion.LinearOverCompletion

/-!
# Maps out of an adic completion that are surjective modulo the ideal

Let `I` be a finitely generated ideal of a commutative ring `A` and let `M` be a finite
`A`-module. An `A`-linear endomorphism `g` of the `I`-adic completion `M^∧` whose image together
with `I • M^∧` is all of `M^∧` is bijective. Modulo `I^k` it is a surjective endomorphism of the
finite module `M^∧ / I^k M^∧ = M / I^k M`, hence injective by the Orzech property of commutative
rings; injectivity then follows because `M^∧` is `I`-adically separated, and surjectivity because
it is `I`-adically complete.

Consequently a linear map from `M^∧` to a module that is abstractly isomorphic to `M^∧`, and that
is surjective modulo `I`, is an isomorphism.

## Main results

* `AdicCompletion.bijective_of_range_sup_smul_eq_top`: the endomorphism statement.
* `AdicCompletion.bijective_of_linearEquiv_of_range_sup_smul_eq_top`: the statement for a map to
  a module isomorphic to `M^∧`.
-/

@[expose] public section

namespace AdicCompletion

variable {A : Type*} [CommRing A] {I : Ideal A}
variable {M : Type*} [AddCommGroup M] [Module A M]

/-- If `R ⊔ I • ⊤ = ⊤`, then `R ⊔ I ^ k • ⊤ = ⊤` for every `k`. -/
theorem sup_pow_smul_top_eq_top {N : Type*} [AddCommGroup N] [Module A N] {R : Submodule A N}
    (h : R ⊔ I • (⊤ : Submodule A N) = ⊤) (k : ℕ) : R ⊔ I ^ k • (⊤ : Submodule A N) = ⊤ := by
  induction k with
  | zero => simp
  | succ k ih =>
    refine eq_top_iff.2 ?_
    calc (⊤ : Submodule A N) = R ⊔ I • (R ⊔ I ^ k • ⊤) := by rw [ih, h]
      _ ≤ R ⊔ I ^ (k + 1) • ⊤ := by
        rw [Submodule.smul_sup, pow_succ', Submodule.mul_smul]
        exact sup_le le_sup_left (sup_le (Submodule.smul_le_right.trans le_sup_left) le_sup_right)

variable [Module.Finite A M]

/-- The quotient `M^∧ / I ^ k M^∧` is a finite module, being `M / I ^ k M`. -/
theorem finite_quotient_pow_smul_top (hI : I.FG) (k : ℕ) :
    Module.Finite A (AdicCompletion I M ⧸ (I ^ k • ⊤ : Submodule A (AdicCompletion I M))) := by
  have e := (Submodule.quotEquivOfEq _ _ (pow_smul_top_eq_ker_eval (M := M) hI)).trans
    ((eval I M k).quotKerEquivOfSurjective (eval_surjective I M k))
  exact Module.Finite.equiv e.symm

/-- An endomorphism of `M^∧` that is surjective modulo `I` is injective modulo every power
of `I`. -/
theorem mem_pow_smul_top_of_map_mem (hI : I.FG) (g : AdicCompletion I M →ₗ[A] AdicCompletion I M)
    (hg : LinearMap.range g ⊔ I • (⊤ : Submodule A (AdicCompletion I M)) = ⊤) (k : ℕ)
    {x : AdicCompletion I M} (hx : g x ∈ (I ^ k • ⊤ : Submodule A (AdicCompletion I M))) :
    x ∈ (I ^ k • ⊤ : Submodule A (AdicCompletion I M)) := by
  set N : Submodule A (AdicCompletion I M) := I ^ k • ⊤ with hN
  have hgN : N ≤ N.comap g := fun y hy => map_mem_pow_smul_top g I k hy
  let gbar := N.mapQ N g hgN
  have hsurj : Function.Surjective gbar := by
    intro y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective N y
    have hz : z ∈ LinearMap.range g ⊔ N := by
      rw [hN, sup_pow_smul_top_eq_top hg k]; trivial
    obtain ⟨_, ⟨w, rfl⟩, n, hn, hwn⟩ := Submodule.mem_sup.1 hz
    refine ⟨Submodule.Quotient.mk w, ?_⟩
    rw [Submodule.mapQ_apply, ← hwn, Submodule.Quotient.mk_add,
      (Submodule.Quotient.mk_eq_zero N).2 hn, add_zero]
  have := finite_quotient_pow_smul_top (M := M) hI k
  have hinj := OrzechProperty.injective_of_surjective_endomorphism gbar hsurj
  have h0 : gbar (Submodule.Quotient.mk x) = 0 := by
    rw [Submodule.mapQ_apply]
    exact (Submodule.Quotient.mk_eq_zero N).2 hx
  exact (Submodule.Quotient.mk_eq_zero N).1 (hinj (h0.trans (_root_.map_zero gbar).symm))

/-- **An endomorphism of an adic completion that is surjective modulo the ideal is bijective.**
Let `I` be a finitely generated ideal and `M` a finite module. If the image of an endomorphism
`g` of `M^∧`, together with `I • M^∧`, is all of `M^∧`, then `g` is bijective. -/
theorem bijective_of_range_sup_smul_eq_top (hI : I.FG)
    (g : AdicCompletion I M →ₗ[A] AdicCompletion I M)
    (hg : LinearMap.range g ⊔ I • (⊤ : Submodule A (AdicCompletion I M)) = ⊤) :
    Function.Bijective g := by
  have hc := isAdicComplete (M := M) hI
  refine ⟨(injective_iff_map_eq_zero g).2 fun x hx => ?_, fun z => ?_⟩
  · refine IsHausdorff.haus' (I := I) x fun k => ?_
    rw [SModEq.zero]
    refine mem_pow_smul_top_of_map_mem hI g hg k ?_
    rw [hx]
    exact Submodule.zero_mem _
  · have hz (k : ℕ) : ∃ w, z - g w ∈ (I ^ k • ⊤ : Submodule A (AdicCompletion I M)) := by
      have : z ∈ LinearMap.range g ⊔ (I ^ k • ⊤ : Submodule A (AdicCompletion I M)) := by
        rw [sup_pow_smul_top_eq_top hg k]; trivial
      obtain ⟨_, ⟨w, rfl⟩, n, hn, hwn⟩ := Submodule.mem_sup.1 this
      exact ⟨w, by rw [← hwn, add_sub_cancel_left]; exact hn⟩
    choose f hf using hz
    have hcauchy : ∀ {m n : ℕ}, m ≤ n →
        f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule A (AdicCompletion I M))] := by
      intro m n hmn
      rw [SModEq.sub_mem]
      refine mem_pow_smul_top_of_map_mem hI g hg m ?_
      have hn : z - g (f n) ∈ (I ^ m • ⊤ : Submodule A (AdicCompletion I M)) :=
        Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn) (hf n)
      have := Submodule.sub_mem _ hn (hf m)
      rwa [sub_sub_sub_cancel_left, ← map_sub] at this
    obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec hcauchy
    refine ⟨L, (sub_eq_zero.1 (IsHausdorff.haus' (I := I) (z - g L) fun k => ?_)).symm⟩
    rw [SModEq.zero]
    have h1 := map_mem_pow_smul_top g I k ((SModEq.sub_mem).1 (hL k))
    rw [map_sub] at h1
    have := Submodule.add_mem _ (hf k) h1
    rwa [sub_add_sub_cancel] at this

/-- **A map from an adic completion to an isomorphic module, surjective modulo the ideal, is
bijective.** Let `I` be a finitely generated ideal and `M` a finite module. If `N` is isomorphic
to `M^∧` and the image of a linear map `c : M^∧ → N`, together with `I • N`, is all of `N`, then
`c` is bijective. -/
theorem bijective_of_linearEquiv_of_range_sup_smul_eq_top (hI : I.FG)
    {N : Type*} [AddCommGroup N] [Module A N] (ψ : AdicCompletion I M ≃ₗ[A] N)
    (c : AdicCompletion I M →ₗ[A] N)
    (hc : LinearMap.range c ⊔ I • (⊤ : Submodule A N) = ⊤) :
    Function.Bijective c := by
  let g : AdicCompletion I M →ₗ[A] AdicCompletion I M := ψ.symm.toLinearMap ∘ₗ c
  have hg : LinearMap.range g ⊔ I • (⊤ : Submodule A (AdicCompletion I M)) = ⊤ := by
    have h := congrArg (Submodule.map ψ.symm.toLinearMap) hc
    rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top, LinearEquiv.range,
      ← LinearMap.range_comp] at h
    exact h
  have hb := bijective_of_range_sup_smul_eq_top hI g hg
  have : (c : AdicCompletion I M → N) = ψ ∘ g := by
    funext x
    simp [g]
  rw [this]
  exact ψ.bijective.comp hb

end AdicCompletion
