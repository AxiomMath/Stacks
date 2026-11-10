module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksFrontier.RingTheory.AdicCompletion.InverseLimitShift
public import StacksFrontier.RingTheory.AdicCompletion.InverseLimitTensor
public import StacksFrontier.RingTheory.AdicCompletion.ShiftedLevelCompletion

/-!
# A base change of a tower of shifted quotients, and its completed limit

`bijective_invLimitTensorMap` of
`StacksFrontier/RingTheory/AdicCompletion/InverseLimitTensor.lean` identifies the base change of a
limit with the limit of the base changes **for a module free of finite rank**, and the module
documentation there records that neither half of the hypothesis is removable: for `N` free on an
infinite basis the comparison map is not surjective, the support of a compatible family being
allowed to grow with the level.

**This file replaces that statement by one that needs no hypothesis on the module at all**, at the
cost of completing the left-hand side.  If the tower `(M_e)` is the tower of shifted quotients of
its own limit `M`, that is if the transition maps are surjective with
`ker (M_{e+1} ⟶ M_e) = I^{N+e} M_{e+1}`, then for **every** `A`-module `N`

`(N ⊗_A M)^∧ ≅ lim_e (N ⊗_A M_e)`,

because base change along `N` carries a tower of shifted quotients to another one: it is right
exact, so `N ⊗ M_e = (N ⊗ M) / I^{N+e} (N ⊗ M)`, and
`Crystalline.completionLevelEquiv` then applies.

The hypotheses are stated on the *reductions* `r_e : X ⟶ P_e` rather than on the transition maps
of the tower — surjective with `ker (r_e) = I^{N+e} X` — because that is the form in which they are
available: for a quasi-coherent crystal over the system of
[Stacks, Proposition 60.21.1, Tag 07JN] it is
`...SmallSite.mem_pow_smul_top_iff_wholeSpaceSectionsVal_eq_zero`.  The passage from the tower
relation `ker (M_{e+1} ⟶ M_e) = I^{N+e} M_{e+1}` to that form is
`Crystalline.ker_limitLevelProj`, which is `Crystalline.ker_proj_shift`.

## Main definitions

* `Crystalline.tensorLevelProj` — the level-`e` projection `N ⊗_A X ⟶ N ⊗_A P_e` of a base
  change.
* `Crystalline.tensorCompletionLevel` — the level-`e` readout `(N ⊗_A X)^∧ ⟶ N ⊗_A P_e`.
* `Crystalline.tensorCompletionLevelEquiv` — **the completed interchange**
  `(N ⊗_A X)^∧ ≅ lim_e (N ⊗_A P_e)`.
* `Crystalline.limitLevelProj` — the reduction to the level `e` of a module identified with the
  limit of a tower, which is the `r_e` of the tower presentation.

## Main results

* `Crystalline.range_lTensor_subtype_smul_top` — the image of `N ⊗ (J X)` in `N ⊗ X` is
  `J (N ⊗ X)`.
* `Crystalline.ker_lTensor_of_ker_eq_smul_top` — **right exactness in the form used here**: a
  surjection with kernel `J X` base changes to a surjection with kernel `J (N ⊗ X)`.
* `Crystalline.ker_tensorLevelProj` — the kernel of the level projection of the base change is
  `I^{N+e}`, which is the hypothesis `Crystalline.completionLevelEquiv` runs on.
* `Crystalline.ker_limitLevelProj` — the same for a module presented as the limit of the tower,
  from the tower relation.
* `Crystalline.pow_smul_top_eq_bot_of_ker_proj` — the projection relation forces the annihilation
  `I^{N+e} P_e = 0`, so item (07JB) needs no separate input.
* `Crystalline.tensorCompletionLevel_of`, `...._transition` and `...._injective` — the properties
  of the readout, inherited from
  `StacksFrontier/RingTheory/AdicCompletion/ShiftedLevelCompletion.lean`.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 09B8](https://stacks.math.columbia.edu/tag/09B8)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Crystalline

/-- A surjection carries `J • ⊤` onto `J • ⊤`. -/
private theorem map_smul_top_of_surjective {A : Type*} [CommRing A] {M M' : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] (J : Ideal A) (f : M →ₗ[A] M')
    (hf : Function.Surjective f) :
    Submodule.map f (J • (⊤ : Submodule A M)) = J • (⊤ : Submodule A M') := by
  rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hf]

/-! ### Right exactness of a base change, read on the `J`-filtration -/

section RightExact

variable {A : Type u} [CommRing A] (Nmod : Type v) [AddCommGroup Nmod] [Module A Nmod]
  {X : Type w} [AddCommGroup X] [Module A X]

/-- **The image of `N ⊗ (J X)` in `N ⊗ X` is `J (N ⊗ X)`.** -/
theorem range_lTensor_subtype_smul_top (J : Ideal A) :
    LinearMap.range (LinearMap.lTensor Nmod (J • (⊤ : Submodule A X)).subtype) =
      J • (⊤ : Submodule A (Nmod ⊗[A] X)) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨w, rfl⟩
    induction w using TensorProduct.inductionOn with
    | tmul q z =>
        rw [LinearMap.lTensor_tmul]
        refine Submodule.smul_induction_on
          (p := fun x ↦ q ⊗ₜ[A] x ∈ J • (⊤ : Submodule A (Nmod ⊗[A] X))) z.2
          (fun a ha x _ ↦ ?_) (fun x y hx hy ↦ ?_)
        · rw [TensorProduct.tmul_smul]
          exact Submodule.smul_mem_smul ha Submodule.mem_top
        · rw [TensorProduct.tmul_add]
          exact Submodule.add_mem _ hx hy
    | add w w' hw hw' =>
        rw [map_add]
        exact Submodule.add_mem _ hw hw'
  · rw [Submodule.smul_le]
    intro a ha w hw
    clear hw
    induction w using TensorProduct.inductionOn with
    | tmul q x =>
        refine ⟨q ⊗ₜ[A] ⟨a • x, Submodule.smul_mem_smul ha Submodule.mem_top⟩, ?_⟩
        rw [LinearMap.lTensor_tmul]
        change q ⊗ₜ[A] (a • x) = a • (q ⊗ₜ[A] x)
        rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    | add w w' hw hw' =>
        rw [smul_add]
        exact Submodule.add_mem _ hw hw'

/-- **Right exactness, read on the `J`-filtration**: a surjection with kernel `J X` base changes
to a surjection with kernel `J (N ⊗ X)`.  This is what makes a base change of a tower of shifted
quotients another tower of shifted quotients. -/
theorem ker_lTensor_of_ker_eq_smul_top {Y : Type w} [AddCommGroup Y] [Module A Y]
    (q : X →ₗ[A] Y) (hq : Function.Surjective q) (J : Ideal A)
    (hkerq : LinearMap.ker q = J • (⊤ : Submodule A X)) :
    LinearMap.ker (LinearMap.lTensor Nmod q) = J • (⊤ : Submodule A (Nmod ⊗[A] X)) := by
  have hex : Function.Exact
      (Submodule.subtype (J • (⊤ : Submodule A X))) q := by
    rw [LinearMap.exact_iff, hkerq]
    exact (Submodule.range_subtype _).symm
  have hlt := _root_.lTensor_exact Nmod hex hq
  rw [LinearMap.exact_iff] at hlt
  rw [hlt, range_lTensor_subtype_smul_top Nmod J]

end RightExact

/-! ### The base change of a tower of shifted quotients -/

noncomputable section Tower

variable {A : Type u} [CommRing A] {I : Ideal A} (Nmod : Type v) [AddCommGroup Nmod]
  [Module A Nmod] (X : Type w) [AddCommGroup X] [Module A X]
  (P : ℕ → Type w) [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
  (s : ∀ n, P (n + 1) →ₗ[A] P n) (N : ℕ) (r : ∀ n, X →ₗ[A] P n)

/-- **The level-`n` projection of a base change `N ⊗_A X`**, the base change of the reduction
`X ⟶ Pₙ`. -/
def tensorLevelProj (n : ℕ) : Nmod ⊗[A] X →ₗ[A] Nmod ⊗[A] P n :=
  LinearMap.lTensor Nmod (r n)

/-- The level-`n` projection sends `q ⊗ₜ x` to `q ⊗ₜ rₙ x`. -/
@[simp] theorem tensorLevelProj_tmul (n : ℕ) (q : Nmod) (x : X) :
    tensorLevelProj Nmod X P r n (q ⊗ₜ[A] x) = q ⊗ₜ[A] r n x :=
  rfl

variable (hsurj : ∀ n, Function.Surjective (r n))
  (hker : ∀ n, LinearMap.ker (r n) = I ^ (N + n) • (⊤ : Submodule A X))
  (hcomp : ∀ n, s n ∘ₗ r (n + 1) = r n)

include hcomp in
/-- The level projections of a base change are compatible with the tower. -/
theorem lTensor_comp_tensorLevelProj (n : ℕ) :
    LinearMap.lTensor Nmod (s n) ∘ₗ tensorLevelProj Nmod X P r (n + 1) =
      tensorLevelProj Nmod X P r n := by
  rw [tensorLevelProj, tensorLevelProj, ← LinearMap.lTensor_comp, hcomp n]

include hsurj in
/-- The level projections of a base change are surjective. -/
theorem tensorLevelProj_surjective (n : ℕ) :
    Function.Surjective (tensorLevelProj Nmod X P r n) :=
  LinearMap.lTensor_surjective Nmod (hsurj n)

include hsurj hker in
/-- **The kernel of the level projection of a base change is `I^{N+n}`.**  This is right
exactness, `Crystalline.ker_lTensor_of_ker_eq_smul_top`: a base change of a tower of shifted
quotients is another tower of shifted quotients, for **every** module and with no finiteness. -/
theorem ker_tensorLevelProj (n : ℕ) :
    LinearMap.ker (tensorLevelProj Nmod X P r n) =
      I ^ (N + n) • (⊤ : Submodule A (Nmod ⊗[A] X)) :=
  ker_lTensor_of_ker_eq_smul_top Nmod (r n) (hsurj n) _ (hker n)

/-! ### The completed interchange -/

include hsurj hker in
/-- **The level-`n` readout of the completion of a base change.** -/
def tensorCompletionLevel (n : ℕ) :
    AdicCompletion I (Nmod ⊗[A] X) →ₗ[A] Nmod ⊗[A] P n :=
  completionLevel I (Nmod ⊗[A] X) (fun n ↦ Nmod ⊗[A] P n) N
    (tensorLevelProj Nmod X P r) (ker_tensorLevelProj Nmod X P N r hsurj hker) n

include hsurj hker in
/-- On the image of `N ⊗_A X` in its completion, the level-`n` readout is the level-`n`
projection. -/
@[simp] theorem tensorCompletionLevel_of (n : ℕ) (z : Nmod ⊗[A] X) :
    tensorCompletionLevel Nmod X P N r hsurj hker n (AdicCompletion.of I (Nmod ⊗[A] X) z) =
      tensorLevelProj Nmod X P r n z :=
  rfl

include hsurj hker hcomp in
/-- The readouts of the completion of a base change are compatible with the tower. -/
theorem tensorCompletionLevel_transition (n : ℕ) (w : AdicCompletion I (Nmod ⊗[A] X)) :
    LinearMap.lTensor Nmod (s n)
        (tensorCompletionLevel Nmod X P N r hsurj hker (n + 1) w) =
      tensorCompletionLevel Nmod X P N r hsurj hker n w :=
  completionLevel_transition I (Nmod ⊗[A] X) (fun n ↦ Nmod ⊗[A] P n)
    (fun n ↦ LinearMap.lTensor Nmod (s n)) N (tensorLevelProj Nmod X P r)
    (ker_tensorLevelProj Nmod X P N r hsurj hker)
    (lTensor_comp_tensorLevelProj Nmod X P s r hcomp) n w

include hsurj hker in
/-- **The readouts of the completion of a base change separate its points.**  This is what lets
the clauses of a comparison datum on `X` be checked one level at a time. -/
theorem tensorCompletionLevel_injective {w w' : AdicCompletion I (Nmod ⊗[A] X)}
    (h : ∀ n, tensorCompletionLevel Nmod X P N r hsurj hker n w =
      tensorCompletionLevel Nmod X P N r hsurj hker n w') :
    w = w' :=
  completionLevel_injective I (Nmod ⊗[A] X) (fun n ↦ Nmod ⊗[A] P n) N
    (tensorLevelProj Nmod X P r) (ker_tensorLevelProj Nmod X P N r hsurj hker)
    (tensorLevelProj_surjective Nmod X P r hsurj) h

include hsurj hker hcomp in
/-- **The completed interchange `(N ⊗_A X)^∧ ≅ lim_n (N ⊗_A Pₙ)`**, for every `A`-module `N` and
with no finiteness anywhere.  This is what replaces `bijective_invLimitTensorMap`, whose
hypothesis — a finite basis of `N` — is not satisfied by the module of differentials of
[Stacks, Lemma 60.17.3, Tag 07JG] when the presentation has infinitely many variables. -/
def tensorCompletionLevelEquiv :
    AdicCompletion I (Nmod ⊗[A] X) ≃ₗ[A] ↥(invLimitTensor Nmod P s) :=
  completionLevelEquiv I (Nmod ⊗[A] X) (fun n ↦ Nmod ⊗[A] P n)
    (fun n ↦ LinearMap.lTensor Nmod (s n)) N (tensorLevelProj Nmod X P r)
    (ker_tensorLevelProj Nmod X P N r hsurj hker)
    (tensorLevelProj_surjective Nmod X P r hsurj)
    (lTensor_comp_tensorLevelProj Nmod X P s r hcomp)

include hsurj hker hcomp in
/-- The `n`-th component of the image of `w` under `tensorCompletionLevelEquiv` is the level-`n`
readout of `w`. -/
@[simp] theorem tensorCompletionLevelEquiv_val (w : AdicCompletion I (Nmod ⊗[A] X)) (n : ℕ) :
    (tensorCompletionLevelEquiv Nmod X P s N r hsurj hker hcomp w).val n =
      tensorCompletionLevel Nmod X P N r hsurj hker n w :=
  rfl

end Tower

/-! ### The reduction maps of a tower identified with the limit of its levels -/

noncomputable section OfLimit

variable {A : Type u} [CommRing A] {I : Ideal A} {M₀ : Type w} [AddCommGroup M₀] [Module A M₀]
  (lev : ℕ → Type w) [∀ n, AddCommGroup (lev n)] [∀ n, Module A (lev n)]
  (trans : ∀ n, lev (n + 1) →ₗ[A] lev n)
  (eqv : M₀ ≃ₗ[A] ↥(invLimit lev trans)) (N : ℕ)
  (hsurj : ∀ n, Function.Surjective (trans n))

/-- **The reduction of a module identified with the limit of a tower to the level `n`.** -/
def limitLevelProj (n : ℕ) : M₀ →ₗ[A] lev n :=
  (invLimit.proj lev trans n).comp (eqv : M₀ →ₗ[A] ↥(invLimit lev trans))

/-- The reduction of `m` to the level `n` is the `n`-th component of the image of `m` in the
limit. -/
@[simp] theorem limitLevelProj_apply (n : ℕ) (m : M₀) :
    limitLevelProj lev trans eqv n m = invLimit.proj lev trans n (eqv m) :=
  rfl

/-- The reductions to the levels are compatible with the tower. -/
theorem trans_comp_limitLevelProj (n : ℕ) :
    trans n ∘ₗ limitLevelProj lev trans eqv (n + 1) = limitLevelProj lev trans eqv n :=
  LinearMap.ext fun m ↦ invLimit.proj_comp_transition lev trans n (eqv m)

include hsurj in
/-- The reductions to the levels are surjective, which is Mittag-Leffler. -/
theorem limitLevelProj_surjective (n : ℕ) :
    Function.Surjective (limitLevelProj lev trans eqv n) := by
  intro y
  obtain ⟨x, hx⟩ := invLimit.proj_surjective lev trans hsurj n y
  refine ⟨eqv.symm x, ?_⟩
  change invLimit.proj lev trans n (eqv (eqv.symm x)) = y
  rw [LinearEquiv.apply_symm_apply, hx]

variable (hker : ∀ n, LinearMap.ker (trans n) = I ^ (N + n) • (⊤ : Submodule A (lev (n + 1))))
  (hI : I.FG)

include hsurj hker hI in
/-- **The kernel of the reduction to the level `n` is `I^{N+n}`**, which is
`Crystalline.ker_proj_shift` read across the identification of `M` with the limit.  This is the
bridge from the *tower* relation `ker (M_{n+1} ⟶ M_n) = I^{N+n} M_{n+1}` to the *projection*
relation that the completed interchange runs on. -/
theorem ker_limitLevelProj (n : ℕ) :
    LinearMap.ker (limitLevelProj lev trans eqv n) =
      I ^ (N + n) • (⊤ : Submodule A M₀) := by
  rw [limitLevelProj, LinearMap.ker_comp, ker_proj_shift trans N hsurj hker hI n,
    ← map_smul_top_of_surjective _ (eqv : M₀ →ₗ[A] ↥(invLimit lev trans)) eqv.surjective,
    Submodule.comap_map_eq_of_injective eqv.injective]

end OfLimit

/-! ### The annihilation that the projection relation forces -/

section Annihilation

variable {A : Type u} [CommRing A] {I : Ideal A} {X : Type w} [AddCommGroup X] [Module A X]
  (P : ℕ → Type w) [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)] (N : ℕ)
  (r : ∀ n, X →ₗ[A] P n) (hsurj : ∀ n, Function.Surjective (r n))
  (hker : ∀ n, LinearMap.ker (r n) = I ^ (N + n) • (⊤ : Submodule A X))

include hsurj hker in
/-- **`I^{N+n}` annihilates `Pₙ`**, which is forced by `Pₙ = X / I^{N+n} X` and needs no separate
input.  This is how item (07JB) of [Stacks, Lemma 60.17.3, Tag 07JG] follows from the crystal
tower relation. -/
theorem pow_smul_top_eq_bot_of_ker_proj (n : ℕ) :
    I ^ (N + n) • (⊤ : Submodule A (P n)) = ⊥ := by
  rw [← map_smul_top_of_surjective _ (r n) (hsurj n), ← hker n, eq_bot_iff]
  rintro x ⟨y, hy, rfl⟩
  simpa using hy

end Annihilation

end Crystalline

end
