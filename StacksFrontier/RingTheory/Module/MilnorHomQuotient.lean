module

public import Mathlib
public import StacksFrontier.RingTheory.Flat.ShortExact
public import StacksFrontier.RingTheory.Module.BaseChangeQuotientHom

/-!
# Reduction of homomorphisms modulo an ideal, and Milnor patching of homomorphisms

Let `R` be a commutative ring, let `M` and `N` be `R`-modules with `M` finite projective, and let
`𝔞`, `𝔟` be ideals of `R`. Reducing an `R`-linear map `h : M →ₗ[R] N` modulo `𝔞` means forming
`LinearMap.baseChange (R ⧸ 𝔞) h`. This file identifies the kernel of reduction, shows that
vanishing modulo both `𝔞` and `𝔟` forces vanishing modulo `𝔞 ⊓ 𝔟` when `N` is flat, and glues a
compatible pair of reductions into a single `R`-linear map. These are the module-theoretic
ingredients of Milnor patching for homomorphisms.

## Main results

* `Stacks.MilnorHom.mem_smul_top_hom_pi_iff`: an `R`-linear map out of `Fin r → R` lies in
  `𝔞 • (⊤ : Submodule R ((Fin r → R) →ₗ[R] N))` exactly when it sends each standard basis vector
  into `𝔞 • (⊤ : Submodule R N)`.
* `Stacks.MilnorHom.mem_smul_top_hom_iff`: for `M` finite projective, `h : M →ₗ[R] N` lies in
  `𝔞 • (⊤ : Submodule R (M →ₗ[R] N))` exactly when its image lies in `𝔞 • (⊤ : Submodule R N)`;
  combined with `Stacks.BaseChangeQuotient.baseChange_quotient_eq_zero_iff` this says that the
  kernel of reduction modulo `𝔞` on `Hom_R(M, N)` is `𝔞 • Hom_R(M, N)`.
* `Stacks.MilnorHom.baseChange_eq_zero_of_baseChange_eq_zero_pair`: if `N` is flat and `h` reduces
  to zero modulo `𝔞` and modulo `𝔟`, then `h` base changes to zero along any `R`-algebra whose
  structure map kills `𝔞 ⊓ 𝔟`.
* `Stacks.MilnorHom.exists_baseChange_eq_pair`: a pair of homomorphisms over `R ⧸ 𝔞` and `R ⧸ 𝔟`
  that is realized by `R`-linear maps agreeing over `R ⧸ (𝔞 ⊔ 𝔟)` is realized by a single
  `R`-linear map.
* `Stacks.MilnorHom.moduleCat_extendScalars_map_hom` and
  `Stacks.MilnorHom.moduleCat_extendScalars_map_eq_zero_iff`: the dictionary identifying the action
  of `ModuleCat.extendScalars` on morphisms with `LinearMap.baseChange`.
-/

@[expose] public section

universe u

namespace Stacks.MilnorHom

open scoped TensorProduct

section Modules

variable {R : Type u} [CommRing R] {M N : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- If an `R`-linear map `h : M →ₗ[R] N` lies in `𝔞 • (⊤ : Submodule R (M →ₗ[R] N))`, then every
value of `h` lies in `𝔞 • (⊤ : Submodule R N)`. -/
theorem apply_mem_smul_top_of_mem_smul_top (𝔞 : Ideal R) {h : M →ₗ[R] N}
    (hh : h ∈ 𝔞 • (⊤ : Submodule R (M →ₗ[R] N))) (m : M) :
    h m ∈ 𝔞 • (⊤ : Submodule R N) := by
  refine Submodule.smul_induction_on hh (fun x hx g _ => ?_) fun g₁ g₂ k₁ k₂ => ?_
  · rw [LinearMap.smul_apply]
    exact Submodule.smul_mem_smul hx Submodule.mem_top
  · rw [LinearMap.add_apply]
    exact Submodule.add_mem _ k₁ k₂

/-- Scaling a fixed element of `𝔞 • (⊤ : Submodule R N)` by a linear functional produces an
element of `𝔞 • (⊤ : Submodule R (P →ₗ[R] N))`. -/
theorem smulRight_mem_smul_top {P : Type u} [AddCommGroup P] [Module R P] (𝔞 : Ideal R)
    (g : P →ₗ[R] R) {n : N} (hn : n ∈ 𝔞 • (⊤ : Submodule R N)) :
    g.smulRight n ∈ 𝔞 • (⊤ : Submodule R (P →ₗ[R] N)) := by
  refine Submodule.smul_induction_on hn (fun x hx n' _ => ?_) fun n₁ n₂ k₁ k₂ => ?_
  · have hx' : g.smulRight (x • n') = x • g.smulRight n' := by
      refine LinearMap.ext fun p => ?_
      rw [LinearMap.smulRight_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
        smul_comm]
    rw [hx']
    exact Submodule.smul_mem_smul hx Submodule.mem_top
  · have hadd : g.smulRight (n₁ + n₂) = g.smulRight n₁ + g.smulRight n₂ := by
      refine LinearMap.ext fun p => ?_
      rw [LinearMap.smulRight_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
        LinearMap.smulRight_apply, smul_add]
    rw [hadd]
    exact Submodule.add_mem _ k₁ k₂

/-- An `R`-linear map `h : (Fin r → R) →ₗ[R] N` lies in `𝔞 • ⊤` exactly when each value
`h (Pi.single i 1)` lies in `𝔞 • (⊤ : Submodule R N)`. -/
theorem mem_smul_top_hom_pi_iff (𝔞 : Ideal R) (r : ℕ) (h : (Fin r → R) →ₗ[R] N) :
    h ∈ 𝔞 • (⊤ : Submodule R ((Fin r → R) →ₗ[R] N)) ↔
      ∀ i, h (Pi.single i 1) ∈ 𝔞 • (⊤ : Submodule R N) := by
  refine ⟨fun hh i => apply_mem_smul_top_of_mem_smul_top 𝔞 hh _, fun hi => ?_⟩
  have hbasis : ∀ x : Fin r → R, ∑ i : Fin r, x i • (Pi.single i 1 : Fin r → R) = x := by
    intro x
    simpa only [Pi.basisFun_repr, Pi.basisFun_apply] using (Pi.basisFun R (Fin r)).sum_repr x
  have hsum : h = ∑ i : Fin r, (LinearMap.proj i).smulRight (h (Pi.single i 1)) := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.sum_apply]
    conv_lhs => rw [← hbasis x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, LinearMap.smulRight_apply, LinearMap.proj_apply]
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => smulRight_mem_smul_top 𝔞 _ (hi i)

/-- The kernel of reduction modulo `𝔞` on homomorphisms out of a finite projective module: an
`R`-linear map `h : M →ₗ[R] N` lies in `𝔞 • (⊤ : Submodule R (M →ₗ[R] N))` if and only if its
image lies in `𝔞 • (⊤ : Submodule R N)`. -/
theorem mem_smul_top_hom_iff (𝔞 : Ideal R) [Module.Finite R M] [Module.Projective R M]
    (h : M →ₗ[R] N) :
    h ∈ 𝔞 • (⊤ : Submodule R (M →ₗ[R] N)) ↔ ∀ m : M, h m ∈ 𝔞 • (⊤ : Submodule R N) := by
  refine ⟨fun hh m => apply_mem_smul_top_of_mem_smul_top 𝔞 hh m, fun hmem => ?_⟩
  obtain ⟨r, π, σ, -, -, hπσ⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have hfree : h ∘ₗ π ∈ 𝔞 • (⊤ : Submodule R ((Fin r → R) →ₗ[R] N)) :=
    (mem_smul_top_hom_pi_iff 𝔞 r (h ∘ₗ π)).mpr fun i => hmem (π (Pi.single i 1))
  have hcomp : ∀ g ∈ 𝔞 • (⊤ : Submodule R ((Fin r → R) →ₗ[R] N)),
      g ∘ₗ σ ∈ 𝔞 • (⊤ : Submodule R (M →ₗ[R] N)) := by
    intro g hg
    refine Submodule.smul_induction_on hg (fun x hx g' _ => ?_) fun g₁ g₂ k₁ k₂ => ?_
    · rw [LinearMap.smul_comp]
      exact Submodule.smul_mem_smul hx Submodule.mem_top
    · rw [LinearMap.add_comp]
      exact Submodule.add_mem _ k₁ k₂
  rw [← LinearMap.comp_id h, ← hπσ, ← LinearMap.comp_assoc]
  exact hcomp _ hfree

/-- If `N` is flat and `h : M →ₗ[R] N` reduces to zero both modulo `𝔞` and modulo `𝔟`, then `h`
base changes to zero along every `R`-algebra `S` whose structure map kills `𝔞 ⊓ 𝔟`. -/
theorem baseChange_eq_zero_of_baseChange_eq_zero_pair {S : Type u} [CommRing S] [Algebra R S]
    (𝔞 𝔟 : Ideal R) (hker : ∀ x ∈ 𝔞 ⊓ 𝔟, (algebraMap R S) x = 0)
    [Module.Flat R N] (h : M →ₗ[R] N)
    (h𝔞 : LinearMap.baseChange (R ⧸ 𝔞) h = 0)
    (h𝔟 : LinearMap.baseChange (R ⧸ 𝔟) h = 0) :
    LinearMap.baseChange S h = 0 := by
  refine Stacks.BaseChangeQuotient.baseChange_eq_zero_of_image_mem_smul (𝔞 ⊓ 𝔟) hker h fun m => ?_
  rw [← ideal_smul_top_inf R 𝔞 𝔟 N]
  exact Submodule.mem_inf.mpr
    ⟨(Stacks.BaseChangeQuotient.baseChange_quotient_eq_zero_iff 𝔞 h).mp h𝔞 m,
      (Stacks.BaseChangeQuotient.baseChange_quotient_eq_zero_iff 𝔟 h).mp h𝔟 m⟩

/-- Gluing a compatible pair of reductions: if `h₁` realizes `a` over `R ⧸ 𝔞`, if `h₂` realizes
`b` over `R ⧸ 𝔟`, and if `h₁` and `h₂` have the same reduction over `R ⧸ (𝔞 ⊔ 𝔟)`, then a single
`R`-linear map realizes both `a` and `b`. -/
theorem exists_baseChange_eq_pair (𝔞 𝔟 : Ideal R) [Module.Finite R M] [Module.Projective R M]
    (a : (R ⧸ 𝔞) ⊗[R] M →ₗ[R ⧸ 𝔞] (R ⧸ 𝔞) ⊗[R] N)
    (b : (R ⧸ 𝔟) ⊗[R] M →ₗ[R ⧸ 𝔟] (R ⧸ 𝔟) ⊗[R] N)
    (h₁ h₂ : M →ₗ[R] N)
    (ha : LinearMap.baseChange (R ⧸ 𝔞) h₁ = a)
    (hb : LinearMap.baseChange (R ⧸ 𝔟) h₂ = b)
    (hcompat : LinearMap.baseChange (R ⧸ (𝔞 ⊔ 𝔟)) h₁ = LinearMap.baseChange (R ⧸ (𝔞 ⊔ 𝔟)) h₂) :
    ∃ h : M →ₗ[R] N, LinearMap.baseChange (R ⧸ 𝔞) h = a ∧ LinearMap.baseChange (R ⧸ 𝔟) h = b := by
  have hzero : LinearMap.baseChange (R ⧸ (𝔞 ⊔ 𝔟)) (h₁ - h₂) = 0 := by
    rw [LinearMap.baseChange_sub, hcompat, sub_self]
  have hmem : h₁ - h₂ ∈ (𝔞 ⊔ 𝔟) • (⊤ : Submodule R (M →ₗ[R] N)) :=
    (mem_smul_top_hom_iff (𝔞 ⊔ 𝔟) (h₁ - h₂)).mpr
      ((Stacks.BaseChangeQuotient.baseChange_quotient_eq_zero_iff (𝔞 ⊔ 𝔟) (h₁ - h₂)).mp hzero)
  rw [Submodule.sup_smul] at hmem
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hmem
  have hu0 : LinearMap.baseChange (R ⧸ 𝔞) u = 0 :=
    (Stacks.BaseChangeQuotient.baseChange_quotient_eq_zero_iff 𝔞 u).mpr fun m =>
      apply_mem_smul_top_of_mem_smul_top 𝔞 hu m
  have hv0 : LinearMap.baseChange (R ⧸ 𝔟) v = 0 :=
    (Stacks.BaseChangeQuotient.baseChange_quotient_eq_zero_iff 𝔟 v).mpr fun m =>
      apply_mem_smul_top_of_mem_smul_top 𝔟 hv m
  have hveq : h₁ - u = h₂ + v := by
    rw [← sub_eq_zero, show h₁ - u - (h₂ + v) = h₁ - h₂ - (u + v) by abel, ← huv, sub_self]
  refine ⟨h₁ - u, ?_, ?_⟩
  · rw [LinearMap.baseChange_sub, hu0, sub_zero, ha]
  · rw [hveq, LinearMap.baseChange_add, hb, hv0, add_zero]

end Modules

section ModuleCatBridge

open CategoryTheory

/-- The action of `ModuleCat.extendScalars` on a morphism is `LinearMap.baseChange` for the algebra
structure induced by the ring map. -/
theorem moduleCat_extendScalars_map_hom {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {L L' : ModuleCat.{u} R} (h : L ⟶ L') :
    letI : Algebra R S := φ.hom.toAlgebra
    ((ModuleCat.extendScalars φ.hom).map h).hom = LinearMap.baseChange S h.hom :=
  rfl

/-- A morphism of `ModuleCat` becomes zero after extension of scalars exactly when its base change
is the zero linear map. -/
theorem moduleCat_extendScalars_map_eq_zero_iff {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {L L' : ModuleCat.{u} R} (h : L ⟶ L') :
    letI : Algebra R S := φ.hom.toAlgebra
    (ModuleCat.extendScalars φ.hom).map h = 0 ↔ LinearMap.baseChange S h.hom = 0 := by
  let : Algebra R S := φ.hom.toAlgebra
  exact ⟨fun hzero => ModuleCat.hom_ext_iff.mp hzero, fun hzero => ModuleCat.hom_ext hzero⟩

end ModuleCatBridge

end Stacks.MilnorHom

end
