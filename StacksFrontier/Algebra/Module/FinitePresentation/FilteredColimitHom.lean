module

public import Mathlib.Algebra.Module.FinitePresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Homomorphisms out of a finitely presented module into a filtered colimit

Let `N` be a system of `R`-modules indexed by a directed preorder `J`, with transition maps `t`,
and let `P` carry compatible maps `ι j : N j →ₗ[R] P` exhibiting `P` as the colimit of the
system: every element of `P` comes from some stage (`hsurj`), and an element of a stage that
dies in `P` already dies at a later stage (`hzero`). Then homomorphisms out of a finitely
presented module are the colimit of the homomorphisms into the stages.

The two statements below are the injectivity and the surjectivity of the comparison map
`colim_j Hom_R(M, N j) → Hom_R(M, P)`, phrased elementwise so that no colimit of modules has to
be constructed. Injectivity needs only that `M` be finitely generated; surjectivity is where
finite presentation enters, the relations of a presentation of `M` being what has to be
annihilated at a later stage.

## Main results

* `Module.Finite.exists_le_comp_eq_of_comp_eq`: two homomorphisms into a stage that agree in the
  colimit already agree at a later stage.
* `Module.FinitePresentation.exists_lift`: every homomorphism into the colimit factors through
  some stage.

## Implementation notes

The system is given by bare data — a family of modules, a transition map for each `≤`, and the
directed-system identity `htrans` — rather than by a functor out of a category, because the
consumers index by a preorder and because this makes both statements usable without a
`HasColimit` instance. A cocone that is an honest filtered colimit satisfies `hsurj` and
`hzero`, those being the elementwise description of a filtered colimit of modules.
-/

@[expose] public section

universe u v w w'

namespace Module

variable {R : Type u} [Ring R] {J : Type v} [Preorder J] [IsDirected J (· ≤ ·)]
  {N : J → Type w} [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]
  {t : ∀ ⦃i j : J⦄, i ≤ j → N i →ₗ[R] N j}
  {P : Type w'} [AddCommGroup P] [Module R P] {ι : ∀ j, N j →ₗ[R] P}
  {M : Type*} [AddCommGroup M] [Module R M]

/-- **Injectivity of `colim_j Hom_R(M, N j) → Hom_R(M, P)` for `M` finitely generated.** Two
homomorphisms from a finitely generated module into one stage of the system which become equal
in the colimit are already equal at some later stage.

Only the `hzero` half of the colimit hypothesis is used: each of the finitely many generators of
`M` gives an element of `N j` dying in `P`, hence dying at a later stage, and a single stage
above all of those serves for all of them at once. -/
theorem Finite.exists_le_comp_eq_of_comp_eq [Module.Finite R M]
    (htrans : ∀ ⦃i j k : J⦄ (h : i ≤ j) (h' : j ≤ k) (x : N i), t h' (t h x) = t (h.trans h') x)
    (hzero : ∀ (j : J) (y : N j), ι j y = 0 → ∃ (k : J) (h : j ≤ k), t h y = 0)
    {j : J} (ψ₁ ψ₂ : M →ₗ[R] N j) (h : (ι j).comp ψ₁ = (ι j).comp ψ₂) :
    ∃ (k : J) (hjk : j ≤ k), (t hjk).comp ψ₁ = (t hjk).comp ψ₂ := by
  classical
  have : Nonempty J := ⟨j⟩
  obtain ⟨s, hs⟩ := Module.finite_def.mp ‹Module.Finite R M›
  have hz : ∀ x : M, ι j (ψ₁ x - ψ₂ x) = 0 := fun x => by
    have hx := LinearMap.congr_fun h x
    simp only [LinearMap.comp_apply] at hx
    simp [hx]
  choose k hjk hk0 using fun x : M => hzero j (ψ₁ x - ψ₂ x) (hz x)
  obtain ⟨K, hK⟩ := Finset.exists_le (insert j (s.image k))
  have hjK : j ≤ K := hK j (Finset.mem_insert_self _ _)
  refine ⟨K, hjK, LinearMap.ext_on hs fun x hx => ?_⟩
  have hkK : k x ≤ K := hK _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx))
  have hsub : t hjK (ψ₁ x - ψ₂ x) = 0 := by
    rw [← htrans (hjk x) hkK, hk0 x, map_zero]
  simpa [sub_eq_zero] using hsub

/-- **Surjectivity of `colim_j Hom_R(M, N j) → Hom_R(M, P)` for `M` finitely presented.** Every
homomorphism from a finitely presented module into the colimit factors through some stage.

The argument is the standard one. Choose a presentation `R^m → R^n → M → 0`. The images of the
`n` basis vectors lift to a common stage `j₀`, giving a map `R^n → N j₀` that agrees with the
given one after `ι j₀`. That map need not kill the relations, but each of the `m` relations is
sent to an element dying in `P`, hence dying at a later stage; a stage above all of them kills
every relation, so the map descends to `M`. -/
@[ega "IV 8.5.2.1" "partial"]
theorem FinitePresentation.exists_lift [Module.FinitePresentation R M]
    (htrans : ∀ ⦃i j k : J⦄ (h : i ≤ j) (h' : j ≤ k) (x : N i), t h' (t h x) = t (h.trans h') x)
    (hcompat : ∀ ⦃i j : J⦄ (h : i ≤ j) (x : N i), ι j (t h x) = ι i x)
    (hsurj : ∀ x : P, ∃ (j : J) (y : N j), ι j y = x)
    (hzero : ∀ (j : J) (y : N j), ι j y = 0 → ∃ (k : J) (h : j ≤ k), t h y = 0)
    (φ : M →ₗ[R] P) :
    ∃ (j : J) (ψ : M →ₗ[R] N j), (ι j).comp ψ = φ := by
  classical
  have : Nonempty J := by obtain ⟨j, -, -⟩ := hsurj 0; exact ⟨j⟩
  obtain ⟨n, m, f, g, hf, hfg⟩ := Module.FinitePresentation.exists_fin' R M
  set bn := Pi.basisFun R (Fin n) with hbn
  set bm := Pi.basisFun R (Fin m) with hbm
  -- lift the images of the `n` generators, then move them to a common stage `j₀`
  choose a y hy using fun i : Fin n => hsurj (φ (f (bn i)))
  obtain ⟨j₀, hj₀⟩ := Finset.exists_le (Finset.univ.image a)
  have haj : ∀ i : Fin n, a i ≤ j₀ := fun i =>
    hj₀ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  set ψ₀ : (Fin n → R) →ₗ[R] N j₀ := bn.constr ℕ (fun i => t (haj i) (y i)) with hψ₀
  have hψ₀b : ∀ i : Fin n, ψ₀ (bn i) = t (haj i) (y i) := by
    intro i; simp [hψ₀]
  have key : (ι j₀).comp ψ₀ = φ.comp f := by
    refine bn.ext fun i => ?_
    simp only [LinearMap.comp_apply, hψ₀b, hcompat, hy]
  -- each relation dies in `P`, hence at a later stage; collect those stages
  have hrel : ∀ l : Fin m, ι j₀ (ψ₀ (g (bm l))) = 0 := by
    intro l
    have := LinearMap.congr_fun key (g (bm l))
    simp only [LinearMap.comp_apply] at this
    rw [this, hfg.apply_apply_eq_zero, map_zero]
  choose c hc hc0 using fun l : Fin m => hzero j₀ (ψ₀ (g (bm l))) (hrel l)
  obtain ⟨K, hK⟩ := Finset.exists_le (insert j₀ (Finset.univ.image c))
  have hjK : j₀ ≤ K := hK j₀ (Finset.mem_insert_self _ _)
  have hcK : ∀ l : Fin m, c l ≤ K := fun l =>
    hK _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ l)))
  -- at stage `K` the map kills every relation, hence all of `ker f`
  set ψK : (Fin n → R) →ₗ[R] N K := (t hjK).comp ψ₀ with hψK
  have hzeroRel : ψK.comp g = 0 := by
    refine bm.ext fun l => ?_
    simp only [LinearMap.comp_apply, hψK, LinearMap.zero_apply]
    rw [← htrans (hc l) (hcK l), hc0 l, map_zero]
  have hker : LinearMap.ker f ≤ LinearMap.ker ψK := by
    intro x hx
    obtain ⟨z, rfl⟩ := (hfg x).mp (LinearMap.mem_ker.mp hx)
    have := LinearMap.congr_fun hzeroRel z
    simpa using this
  -- descend along the surjection `f`
  refine ⟨K, (Submodule.liftQ _ ψK hker).comp
    (LinearMap.quotKerEquivOfSurjective f hf).symm.toLinearMap, ?_⟩
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, rfl⟩ := hf x
  have hsymm : (LinearMap.quotKerEquivOfSurjective f hf).symm (f z) = Submodule.Quotient.mk z := by
    rw [LinearEquiv.symm_apply_eq]
    simp [LinearMap.quotKerEquivOfSurjective]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hsymm, Submodule.liftQ_apply, hψK]
  rw [hcompat]
  have := LinearMap.congr_fun key z
  simpa using this

end Module
