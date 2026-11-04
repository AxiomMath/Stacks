module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Finite free algebras and their fibres

## Main definitions

* `Algebra.TensorProduct.algHomOfLiesOver`: a ring map `C → C'` lying over `B → B'`, as a map of
  `B`-algebras.

## Main results

* `Matrix.eq_zero_of_forall_exists_mem_ker_map`: **Nakayama for the kernel of a matrix.**
  If over a local ring `B` every vector over the residue field lifts to the kernel of a matrix
  `N`, then `N = 0`.
* `exists_notMem_mul_eq_zero_of_free`: if `S` is free over `A` and some `σ ∉ p S` kills the image
  of `a`, then some `s ∉ p` kills `a`.
* `Algebra.TensorProduct.bijective_lift_of_coordinates`: if a ring map `ρ : C → C'` from a
  `B`-algebra to a `B'`-algebra, over a ring map `ψ : B → B'`, reads in compatible coordinates
  `B^r ≅ C` and `B'^r ≅ C'` as `v ↦ ψ ∘ v`, then the induced map `B' ⊗_B C → C'` is bijective.
* `Algebra.Etale.of_free_of_forall_residueField`: **a finite free algebra all of whose fibres
  are formally unramified is étale.**

## References

* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
* [Stacks Project, Tag 02GU](https://stacks.math.columbia.edu/tag/02GU)
-/

@[expose] public section

open scoped TensorProduct

universe u v

/-- **Nakayama for the kernel of a matrix.** Let `B` be a local ring and `π : B → K` a ring map to
a field whose kernel is the maximal ideal. If every vector over `K` is the image under `π` of a
vector in the kernel of `N`, then `N` vanishes. -/
theorem Matrix.eq_zero_of_forall_exists_mem_ker_map {B K : Type*} [CommRing B] [IsLocalRing B]
    [Field K] (π : B →+* K) (hπ : ∀ b, π b = 0 → b ∈ IsLocalRing.maximalIdeal B) {m n : ℕ}
    (N : Matrix (Fin m) (Fin n) B)
    (h : ∀ w : Fin n → K, ∃ v ∈ LinearMap.ker N.mulVecLin, π ∘ v = w) : N = 0 := by
  classical
  set K' := LinearMap.ker N.mulVecLin
  have hsmul : ∀ w : Fin n → B, (∀ i, w i ∈ IsLocalRing.maximalIdeal B) →
      w ∈ (IsLocalRing.maximalIdeal B) • (⊤ : Submodule B (Fin n → B)) := by
    intro w hw
    rw [pi_eq_sum_univ w]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem_smul (hw i) Submodule.mem_top
  have hle : (⊤ : Submodule B (Fin n → B)) ≤ K' ⊔ (IsLocalRing.maximalIdeal B) • ⊤ := by
    intro x _
    obtain ⟨v, hv, hvx⟩ := h (π ∘ x)
    have hdiff : x - v ∈ (IsLocalRing.maximalIdeal B) • (⊤ : Submodule B (Fin n → B)) := by
      refine hsmul _ fun i => hπ _ ?_
      rw [Pi.sub_apply, map_sub, sub_eq_zero]
      exact (congrFun hvx i).symm
    have := Submodule.add_mem_sup hv hdiff
    rwa [add_sub_cancel] at this
  have htop : (⊤ : Submodule B (Fin n → B)) ≤ K' :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top)
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) hle
  ext i j
  have hj : Pi.single j 1 ∈ K' := htop Submodule.mem_top
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at hj
  simpa using congrFun hj i

/-- **An element killed after a free base change is killed before it, away from the prime.** Let
`φ : A → S` make `S` a free `A`-module and let `p` be a prime of `A`. If some `σ ∈ S` outside
`p S` kills `φ a`, then some `s ∈ A` outside `p` kills `a`. -/
theorem exists_notMem_mul_eq_zero_of_free {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [Module.Free A S] (p : Ideal A) (a : A) (σ : S) (hσ : σ ∉ p.map (algebraMap A S))
    (h : σ * algebraMap A S a = 0) : ∃ s : A, s ∉ p ∧ s * a = 0 := by
  classical
  by_contra hne
  have hcon : ∀ s : A, s * a = 0 → s ∈ p := fun s hs => by_contra fun hsp => hne ⟨s, hsp, hs⟩
  let b := Module.Free.chooseBasis A S
  have hcoord : ∀ i, b.repr σ i ∈ p := fun i => by
    refine hcon _ ?_
    have h1 : a • σ = 0 := by rw [Algebra.smul_def, mul_comm, h]
    have h2 := congrArg (fun x => b.repr x i) h1
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
      Pi.zero_apply] at h2
    rwa [mul_comm] at h2
  apply hσ
  rw [← b.linearCombination_repr σ, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hcoord i))

namespace Algebra.TensorProduct

variable {B B' C C' : Type*} [CommRing B] [CommRing B'] [CommRing C] [CommRing C']
  [Algebra B C] [Algebra B B'] [Algebra B' C'] (ρ : C →+* C') {r : ℕ}

/-- The ring map `ρ : C → C'` lying over `B → B'`, as a map of `B`-algebras when `C'` is made a
`B`-algebra through `B'`. -/
noncomputable def algHomOfLiesOver
    (hρ : ∀ b : B, ρ (algebraMap B C b) = algebraMap B' C' (algebraMap B B' b)) :
    letI : Algebra B C' := ((algebraMap B' C').comp (algebraMap B B')).toAlgebra
    C →ₐ[B] C' :=
  letI : Algebra B C' := ((algebraMap B' C').comp (algebraMap B B')).toAlgebra
  { ρ with commutes' := hρ }

/-- **The base-change map is bijective when it is so in coordinates.** Let `ρ : C → C'` be a ring
map over `B → B'` from a `B`-algebra to a `B'`-algebra, and let `θ : B^r ≅ C` and
`θ' : B'^r ≅ C'` be linear identifications with `ρ (θ v) = θ' (algebraMap B B' ∘ v)`. Then the
map `B' ⊗_B C → C'`, `b' ⊗ c ↦ b' · ρ c`, is bijective. -/
theorem bijective_lift_of_coordinates
    (hρ : ∀ b : B, ρ (algebraMap B C b) = algebraMap B' C' (algebraMap B B' b))
    (θ : (Fin r → B) ≃ₗ[B] C) (θ' : (Fin r → B') ≃ₗ[B'] C')
    (hθ : ∀ v, ρ (θ v) = θ' (algebraMap B B' ∘ v)) :
    letI : Algebra B C' := ((algebraMap B' C').comp (algebraMap B B')).toAlgebra
    letI : IsScalarTower B B' C' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    Function.Bijective (Algebra.TensorProduct.lift (Algebra.ofId B' C')
      (algHomOfLiesOver ρ hρ) fun _ _ => Commute.all _ _) := by
  let : Algebra B C' := ((algebraMap B' C').comp (algebraMap B B')).toAlgebra
  let : IsScalarTower B B' C' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  set μ := Algebra.TensorProduct.lift (Algebra.ofId B' C') (algHomOfLiesOver ρ hρ)
    fun _ _ => Commute.all _ _
  let e : B' ⊗[B] (Fin r → B) ≃ₗ[B'] (Fin r → B') :=
    TensorProduct.piScalarRight B B' B' (Fin r)
  let t : B' ⊗[B] (Fin r → B) ≃ₗ[B'] B' ⊗[B] C := LinearEquiv.baseChange B B' _ _ θ
  have key : ∀ x, μ (t x) = θ' (e x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v =>
      simp only [t, e, μ, LinearEquiv.baseChange_tmul, Algebra.TensorProduct.lift_tmul]
      show algebraMap B' C' c * ρ (θ v) = _
      rw [hθ v, ← Algebra.smul_def, ← map_smul]
      congr 1
      funext i
      simp [Algebra.smul_def, mul_comm]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hμ : (μ : B' ⊗[B] C → C') = θ' ∘ e ∘ t.symm :=
    funext fun x => by rw [Function.comp_apply, Function.comp_apply, ← key,
      LinearEquiv.apply_symm_apply]
  rw [hμ]
  exact θ'.bijective.comp (e.bijective.comp t.symm.bijective)

end Algebra.TensorProduct

namespace Algebra.Etale

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **A finite free algebra with formally unramified fibres is étale.** If `C` is a finite free
`B`-algebra such that for every prime `q` of `B` the fibre `κ(q) ⊗_B C` is formally unramified
over `κ(q)`, then `C` is étale over `B`. -/
theorem of_free_of_forall_residueField {B : Type u} {C : Type v} [CommRing B] [CommRing C]
    [Algebra B C] [Module.Finite B C] [Module.Free B C]
    (hfib : ∀ (q : Ideal B) [q.IsPrime],
      Algebra.FormallyUnramified q.ResidueField (q.ResidueField ⊗[B] C)) :
    Algebra.Etale B C := by
  have hmod : Module.FinitePresentation B C := Module.finitePresentation_of_projective B C
  have halg : Algebra.FinitePresentation B C := Algebra.FinitePresentation.of_finitePresentation B C
  have hΩ : Module.Finite B Ω[C⁄B] := Module.Finite.trans C _
  have hsupp : Module.support B Ω[C⁄B] = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun q hq => ?_
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hq
    have hfibΩ : Subsingleton Ω[(q.asIdeal.ResidueField ⊗[B] C)⁄q.asIdeal.ResidueField] :=
      (Algebra.formallyUnramified_iff _ _).mp (hfib q.asIdeal)
    have hres : Subsingleton (q.asIdeal.ResidueField ⊗[B] Ω[C⁄B]) :=
      (KaehlerDifferential.tensorKaehlerEquivBase B q.asIdeal.ResidueField C
        (q.asIdeal.ResidueField ⊗[B] C)).toEquiv.subsingleton
    exact not_nontrivial_iff_subsingleton.mpr hres hq
  have hsub : Subsingleton Ω[C⁄B] := Module.support_eq_empty_iff.mp hsupp
  have hunr : Algebra.FormallyUnramified B C := (Algebra.formallyUnramified_iff _ _).mpr hsub
  exact Algebra.Etale.of_formallyUnramified_of_flat

end Algebra.Etale

end
