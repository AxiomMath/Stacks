module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Moving a factorization through a two-term differential

For a two-term complex `d : M → L` with `L` free, say that a scalar `a` *factors through* `d`
when `a • id_M = h ∘ d` for some linear `h : L → M`.  Condition (3) of Stacks 0GAJ reads
rig-smoothness as such a factorization of a power of the ideal of definition through the
differential of the completed naive cotangent complex.  This file collects the four ways in
which the proof of Stacks 0GCK moves such factorizations around.

* Along a map of two-term complexes whose left-hand term has bijective differential, a
  factorization through the middle complex gives one through the right-hand complex
  (`Rig.exists_factor_right_of_bijective_left`).  In the transitivity sequence of Stacks 0ALM
  for `A → B → C` with `NL^∧_{B/A}` acyclic this passes from `NL^∧_{C/A}` to `NL^∧_{C/B}`.
* Along a map of two-term complexes whose right-hand term has bijective differential and whose
  left-hand map is injective in degree `-1`, a factorization through the middle complex gives
  one through the left-hand complex (`Rig.exists_factor_left_of_bijective_right`).  This passes
  from `NL^∧_{C/A}` to `NL^∧_{B/A} ⊗_B C` when `NL^∧_{C/B}` is acyclic and Stacks 0AQJ applies.
* A factorization after a faithfully flat base change descends, when the source of the
  differential is finitely presented (`Rig.exists_factor_of_faithfullyFlat`).
* Over a finite product of rings, factorizations after base change to each factor glue
  (`Rig.exists_factor_of_finite_family`).

## Implementation notes

The two base-change statements rest on one computation,
`Rig.one_tmul_mkQ_smul_id_eq_zero`: writing `Φ : Hom(L, M) → End(M)` for precomposition with
`d`, a factorization after a flat base change `R → T` kills `1 ⊗ [a • id]` in
`T ⊗_R coker Φ`.  This uses that `Hom` out of a finitely presented module commutes with flat
base change (`Module.FinitePresentation.isBaseChange_map`).  Faithful flatness then kills
`[a • id]` itself, and over a product of rings so does its vanishing after each factor.

## References

* [Stacks Project, Tag 0GCK](https://stacks.math.columbia.edu/tag/0GCK)
* [Stacks Project, Tag 0GAJ](https://stacks.math.columbia.edu/tag/0GAJ)
* [Stacks Project, Tag 0ALM](https://stacks.math.columbia.edu/tag/0ALM)
-/

@[expose] public section

open TensorProduct

namespace Rig

section Rows

variable {R : Type*} [CommRing R]
  {M₁ M₂ M₃ L₁ L₂ L₃ : Type*}
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup M₃] [Module R M₃]
  [AddCommGroup L₁] [Module R L₁] [AddCommGroup L₂] [Module R L₂]
  [AddCommGroup L₃] [Module R L₃] [Module.Projective R L₃]
  (d₁ : M₁ →ₗ[R] L₁) (d₂ : M₂ →ₗ[R] L₂) (d₃ : M₃ →ₗ[R] L₃)
  (ι : M₁ →ₗ[R] M₂) (π : M₂ →ₗ[R] M₃) (incl : L₁ →ₗ[R] L₂) (proj : L₂ →ₗ[R] L₃)

/-- **A factorization through the middle of a row of two-term complexes passes to the right
when the left-hand differential is bijective.**  Given the commutative diagram

```
L₁ --incl--> L₂ --proj--> L₃
↑ d₁         ↑ d₂         ↑ d₃
M₁ ---ι----> M₂ ----π---> M₃
```

with `π ∘ ι = 0`, `π` surjective, the top row exact in the middle with `proj` surjective onto
the projective `L₃`, and `d₁` bijective: if `a • id = h₂ ∘ d₂` then `a • id = h₃ ∘ d₃` for
`h₃ = π ∘ h₂ ∘ σ`, where `σ` is a section of `proj`. -/
public theorem exists_factor_right_of_bijective_left
    (hd₁ : Function.Bijective d₁)
    (hsq₁ : ∀ x, d₂ (ι x) = incl (d₁ x)) (hsq₂ : ∀ x, d₃ (π x) = proj (d₂ x))
    (hπι : ∀ x, π (ι x) = 0) (hπ : Function.Surjective π)
    (hrow : Function.Exact incl proj) (hproj : Function.Surjective proj)
    (a : R) (h : ∃ h₂ : L₂ →ₗ[R] M₂, h₂ ∘ₗ d₂ = a • LinearMap.id) :
    ∃ h₃ : L₃ →ₗ[R] M₃, h₃ ∘ₗ d₃ = a • LinearMap.id := by
  obtain ⟨h₂, hh₂⟩ := h
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property proj LinearMap.id hproj
  let e₁ := LinearEquiv.ofBijective d₁ hd₁
  refine ⟨π ∘ₗ h₂ ∘ₗ σ, LinearMap.ext fun m₃ => ?_⟩
  obtain ⟨m, rfl⟩ := hπ m₃
  have hσm : proj (σ (proj (d₂ m))) = proj (d₂ m) := by
    rw [← LinearMap.comp_apply proj σ, hσ, LinearMap.id_apply]
  obtain ⟨u, hu⟩ := (hrow (σ (proj (d₂ m)) - d₂ m)).mp (by rw [map_sub, hσm, sub_self])
  have hlift : σ (proj (d₂ m)) = d₂ (m + ι (e₁.symm u)) := by
    rw [map_add, hsq₁, show d₁ (e₁.symm u) = u from e₁.apply_symm_apply u, hu]
    abel
  have hh : h₂ (d₂ (m + ι (e₁.symm u))) = a • (m + ι (e₁.symm u)) := by
    rw [← LinearMap.comp_apply h₂ d₂, hh₂, LinearMap.smul_apply, LinearMap.id_apply]
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
  rw [hsq₂, hlift, hh, map_smul, map_add, hπι, add_zero]

/-- **A factorization through the middle of a row of two-term complexes passes to the left
when the right-hand differential is bijective and `ι` is injective.**  In the diagram of
`Rig.exists_factor_right_of_bijective_left`, assume instead that the bottom row is exact in the
middle with `π` surjective, that `ι` is injective and that `d₃` is bijective.  If
`a • id = h₂ ∘ d₂` then `a • id = h₁ ∘ d₁`: the map `h₂ ∘ incl`, corrected by a lift `τ` of
`d₃⁻¹` through `π`, lands in the image of `ι`. -/
public theorem exists_factor_left_of_bijective_right
    (hd₃ : Function.Bijective d₃) (hι : Function.Injective ι)
    (hsq₁ : ∀ x, d₂ (ι x) = incl (d₁ x))
    (hrow : Function.Exact ι π) (hπ : Function.Surjective π)
    (a : R) (h : ∃ h₂ : L₂ →ₗ[R] M₂, h₂ ∘ₗ d₂ = a • LinearMap.id) :
    ∃ h₁ : L₁ →ₗ[R] M₁, h₁ ∘ₗ d₁ = a • LinearMap.id := by
  obtain ⟨h₂, hh₂⟩ := h
  let e₃ := LinearEquiv.ofBijective d₃ hd₃
  obtain ⟨τ, hτ⟩ := Module.projective_lifting_property π e₃.symm.toLinearMap hπ
  let g : L₁ →ₗ[R] M₂ := h₂ ∘ₗ incl - τ ∘ₗ d₃ ∘ₗ π ∘ₗ h₂ ∘ₗ incl
  have hg : ∀ x, g x ∈ LinearMap.range ι := fun x => (hrow (g x)).mp (by
    have hτy : π (τ (d₃ (π (h₂ (incl x))))) = π (h₂ (incl x)) := by
      rw [← LinearMap.comp_apply π τ, hτ]
      exact e₃.symm_apply_apply _
    simp only [g, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hτy, sub_self])
  let eι := LinearEquiv.ofInjective ι hι
  refine ⟨eι.symm.toLinearMap ∘ₗ g.codRestrict (LinearMap.range ι) hg,
    LinearMap.ext fun m₁ => hι ?_⟩
  have hι' : ∀ z : LinearMap.range ι, ι (eι.symm z) = z := fun z =>
    congrArg Subtype.val (eι.apply_symm_apply z)
  have hπι : π (ι m₁) = 0 := (hrow (ι m₁)).mpr ⟨m₁, rfl⟩
  have hh : h₂ (incl (d₁ m₁)) = a • ι m₁ := by
    rw [← hsq₁, ← LinearMap.comp_apply h₂ d₂, hh₂, LinearMap.smul_apply, LinearMap.id_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply,
    LinearMap.id_apply, map_smul]
  rw [hι', LinearMap.codRestrict_apply]
  simp only [g, LinearMap.sub_apply, LinearMap.comp_apply, hh, map_smul, hπι, smul_zero,
    map_zero, sub_zero]

end Rows

section BaseChange

variable {S : Type*} [CommRing S] {T : Type*} [CommRing T] [Algebra S T]
  {M : Type*} [AddCommGroup M] [Module S M] {n : ℕ} (d : M →ₗ[S] (Fin n → S))

/-- A scalar factors through `d` once the class of `a • id` in `coker Φ` vanishes. -/
private theorem exists_factor_of_mkQ_eq_zero (a : S)
    (h : (LinearMap.range (LinearMap.lcomp S M d)).mkQ (a • LinearMap.id) = 0) :
    ∃ h' : (Fin n → S) →ₗ[S] M, h' ∘ₗ d = a • LinearMap.id := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  exact h

/-- **A factorization after a flat base change kills the obstruction class after that base
change.**  Write `Φ : Hom(⨁_{i<n} S, M) → End(M)` for precomposition with `d`; a scalar `a`
factors through `d` exactly when the class of `a • id` in `coker Φ` vanishes.  If `M` is
finitely presented, `T` is flat over `S` and `algebraMap a` factors through the base change
`T ⊗_S M → ⨁_{i<n} T` of `d`, then `1 ⊗ [a • id] = 0` in `T ⊗_S coker Φ`. -/
public theorem one_tmul_mkQ_smul_id_eq_zero [Module.Flat S T] [Module.FinitePresentation S M]
    (a : S)
    (h : ∃ hT : (Fin n → T) →ₗ[T] T ⊗[S] M,
      hT ∘ₗ ((((Algebra.linearMap S T).compLeft (Fin n)) ∘ₗ d).liftBaseChange T) =
        (algebraMap S T a) • LinearMap.id) :
    (1 : T) ⊗ₜ[S] (LinearMap.range (LinearMap.lcomp S M d)).mkQ (a • LinearMap.id) = 0 := by
  classical
  obtain ⟨hT, hhT⟩ := h
  have bE := Module.FinitePresentation.isBaseChange_map S (Fin n → S) M T
  have bM := Module.FinitePresentation.isBaseChange_map S M M T
  let ψ := (TensorProduct.piScalarRight S T T (Fin n)).toLinearMap
  have hψ : ψ ∘ₗ d.baseChange T =
      (((Algebra.linearMap S T).compLeft (Fin n)) ∘ₗ d).liftBaseChange T := by
    refine TensorProduct.AlgebraTensorModule.curry_injective ?_
    refine LinearMap.ext fun c => LinearMap.ext fun m => ?_
    funext j
    simp [ψ, TensorProduct.piScalarRightHom_tmul, Algebra.smul_def, mul_comm]
  have key : ∀ z, bM.equiv ((LinearMap.lcomp S M d).lTensor T z) =
      (bE.equiv z) ∘ₗ d.baseChange T := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul t g =>
      rw [LinearMap.lTensor_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul,
        LinearMap.smul_comp, LinearMap.baseChangeHom_apply, LinearMap.baseChangeHom_apply,
        LinearMap.lcomp_apply', LinearMap.baseChange_comp]
    | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, LinearMap.add_comp]
  have hy : (LinearMap.lcomp S M d).lTensor T (bE.equiv.symm (hT ∘ₗ ψ)) =
      (1 : T) ⊗ₜ[S] (a • LinearMap.id) := by
    apply bM.equiv.injective
    rw [key, bE.equiv.apply_symm_apply, IsBaseChange.equiv_tmul, one_smul,
      LinearMap.comp_assoc, hψ, hhT, LinearMap.baseChangeHom_apply,
      LinearMap.baseChange_smul, LinearMap.baseChange_id]
    exact LinearMap.ext fun z => algebraMap_smul T a z
  calc (1 : T) ⊗ₜ[S] (LinearMap.range (LinearMap.lcomp S M d)).mkQ (a • LinearMap.id)
      = ((LinearMap.range (LinearMap.lcomp S M d)).mkQ.lTensor T)
          ((1 : T) ⊗ₜ[S] (a • LinearMap.id)) := rfl
    _ = (((LinearMap.range (LinearMap.lcomp S M d)).mkQ ∘ₗ
          LinearMap.lcomp S M d).lTensor T) (bE.equiv.symm (hT ∘ₗ ψ)) := by
        rw [← hy, LinearMap.lTensor_comp_apply]
    _ = 0 := by rw [LinearMap.range_mkQ_comp, LinearMap.lTensor_zero, LinearMap.zero_apply]

/-- **Factorizations descend along faithfully flat base change.**  If `M` is finitely
presented and `T` is faithfully flat over `S`, a scalar of `S` whose image in `T` factors
through the base change of `d : M → ⨁_{i<n} S` already factors through `d`. -/
public theorem exists_factor_of_faithfullyFlat [Module.FaithfullyFlat S T]
    [Module.FinitePresentation S M] (a : S)
    (h : ∃ hT : (Fin n → T) →ₗ[T] T ⊗[S] M,
      hT ∘ₗ ((((Algebra.linearMap S T).compLeft (Fin n)) ∘ₗ d).liftBaseChange T) =
        (algebraMap S T a) • LinearMap.id) :
    ∃ h' : (Fin n → S) →ₗ[S] M, h' ∘ₗ d = a • LinearMap.id := by
  have hz := one_tmul_mkQ_smul_id_eq_zero (T := T) d a h
  rw [Module.FaithfullyFlat.one_tmul_eq_zero_iff] at hz
  exact exists_factor_of_mkQ_eq_zero d a hz

end BaseChange

section Family

variable {S : Type*} [CommRing S] {ι : Type*} [Fintype ι] {A : ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, Algebra S (A i)]
  {M : Type*} [AddCommGroup M] [Module S M] {n : ℕ} (d : M →ₗ[S] (Fin n → S))

/-- **Factorizations after base change to a finite family that splits the base ring glue.**
Let `A i` be flat `S`-algebras and `β i : A i → S` be `S`-linear maps with `∑ i, β i 1 = 1`; for
a finite product `S = ∏ Aᵢ` these are the inclusions of the factors, and `β i 1` are the
idempotents splitting `S`.  If `M` is finitely presented and, for every `i`, the image of `a` in
`A i` factors through the base change of `d` to `A i`, then `a` factors through `d`: the class
of `a • id` in `coker Φ` is killed by each `β i 1`, by `Rig.one_tmul_mkQ_smul_id_eq_zero`, and
hence by their sum. -/
public theorem exists_factor_of_finite_family [∀ i, Module.Flat S (A i)]
    [Module.FinitePresentation S M] (β : ∀ i, A i →ₗ[S] S) (hβ : ∑ i, β i 1 = 1) (a : S)
    (h : ∀ i, ∃ hT : (Fin n → A i) →ₗ[A i] A i ⊗[S] M,
      hT ∘ₗ ((((Algebra.linearMap S (A i)).compLeft (Fin n)) ∘ₗ d).liftBaseChange (A i)) =
        (algebraMap S (A i) a) • LinearMap.id) :
    ∃ h' : (Fin n → S) →ₗ[S] M, h' ∘ₗ d = a • LinearMap.id := by
  set q := (LinearMap.range (LinearMap.lcomp S M d)).mkQ (a • LinearMap.id)
  have he : ∀ i, β i 1 • q = 0 := by
    intro i
    have hq : (1 : A i) ⊗ₜ[S] q = 0 := one_tmul_mkQ_smul_id_eq_zero (T := A i) d a (h i)
    have := congrArg (fun z => TensorProduct.lid S _ (LinearMap.rTensor _ (β i) z)) hq
    simpa using this
  have hq0 : q = 0 := by
    calc q = (∑ i, β i 1) • q := by rw [hβ, one_smul]
      _ = ∑ i, β i 1 • q := Finset.sum_smul
      _ = 0 := Finset.sum_eq_zero fun i _ => he i
  exact exists_factor_of_mkQ_eq_zero d a hq0

end Family

end Rig

end
