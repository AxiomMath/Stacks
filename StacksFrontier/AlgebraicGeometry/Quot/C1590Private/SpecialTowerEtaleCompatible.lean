module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SpecialTowerInterfaces
public import StacksFrontier.RingTheory.C1590Private.EtaleTensorPi

/-!
# Étale base change commutes with the limit of a special tower

This is piece (B) of the special-tower route to the effectivity hypothesis of Stacks 0D5A:
`AlgebraicGeometry.C1590Private.SpecialTowerEtaleCompatible`, stated in
`StacksFrontier/AlgebraicGeometry/Quot/C1590Private/SpecialTowerInterfaces.lean`.

Let `⋯ → R₁ → R₀` be a tower with surjective transition maps, special in the sense of
`AlgebraicGeometry.C1590Private.IsSpecialTower`: the kernel of `Rₙ₊₁ → Rₙ` is killed by the
preimage of a maximal ideal `𝔪ₙ` of `R₀`, the `𝔪ₙ` pairwise distinct. Write `L = lim Rₙ`,
`𝔫ₙ ⊂ L` for the preimage of `𝔪ₙ`, `I = Ker(L → R₀)` and `Vₙ = Ker(Rₙ₊₁ → Rₙ)`, an
`L/𝔫ₙ`-vector space. The proof:

1. By the Chinese remainder theorem there are `eₙ ∈ 𝔫₀ ⋯ 𝔫ₙ₋₁` with `1 - eₙ ∈ 𝔫ₙ`
   (`AlgebraicGeometry.C1590Private.exists_towerIdempotents`). Then `x ↦ (eₙ xₙ₊₁)ₙ` is an
   isomorphism `I ≅ ∏ₙ Vₙ` (`AlgebraicGeometry.C1590Private.bijective_kernelComponent`).
2. For `C` étale over `L`, `C ⊗ ∏ₙ Vₙ = ∏ₙ C ⊗ Vₙ`
   (`Stacks.C1590Private.bijective_piRightHom_of_etale`), so `C ⊗ I = ∏ₙ C ⊗ Vₙ`.
3. With `C` flat, `C ⊗ Vₙ ⊂ C ⊗ Rₙ₊₁` is the kernel of `C ⊗ Rₙ₊₁ → C ⊗ Rₙ`, and the `n`-th
   component of `C ⊗ I` is read off in `C ⊗ Rₙ₊₁` as `eₙ` times the image. A compatible sequence
   in the `C ⊗ Rₙ` then differs from its lift at level `0` by a sum `∑ₙ tₙ ∈ ∏ₙ C ⊗ Vₙ` which is
   finite in each component, and this sum is its unique preimage
   (`AlgebraicGeometry.C1590Private.existsUnique_tmul_one_eq`).

The square-zero hypothesis of `AlgebraicGeometry.C1590Private.SpecialTowerEtaleCompatible` and
the Noetherian hypothesis in `AlgebraicGeometry.C1590Private.IsSpecialTower` are not used.

## Main results

* `AlgebraicGeometry.C1590Private.isEtaleCompatibleTower_of_isSpecialTower`: a special tower
  with surjective transition maps is étale-compatible.
* `AlgebraicGeometry.C1590Private.specialTowerEtaleCompatible`: (B).

## References

* [Stacks Project, Tag 0G2S](https://stacks.math.columbia.edu/tag/0G2S)
* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
-/

@[expose] public noncomputable section

open TensorProduct Deformation.Artin.SquareZeroTower

universe u

namespace AlgebraicGeometry.C1590Private

section Limit

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n)

/-- With surjective transition maps, every projection `lim Rₙ → Rₙ` is surjective. -/
theorem towerLimitProj_surjective (hf : ∀ n, Function.Surjective (f n)) (n : ℕ) :
    Function.Surjective (towerLimitProj f n) := by
  induction n generalizing R with
  | zero =>
    intro x
    choose σ hσ using hf
    exact ⟨⟨fun k => Nat.rec (motive := fun k => R k) x (fun k y => σ k y) k,
      fun k => hσ k _⟩, rfl⟩
  | succ n ih =>
    intro x
    obtain ⟨y, hy⟩ := ih (R := fun k => R (k + 1)) (fun k => f (k + 1)) (fun k => hf (k + 1)) x
    refine ⟨⟨fun k => Nat.rec (motive := fun k => R k) (f 0 (y.1 0)) (fun k _ => y.1 k) k,
      fun k => ?_⟩, hy⟩
    cases k with
    | zero => rfl
    | succ k => exact y.2 k

/-- The projections of the limit lie over `R₀`. -/
theorem toBase_towerLimitProj (l : limit f) (n : ℕ) :
    toBase f n (towerLimitProj f n l) = towerLimitProj f 0 l :=
  limit_le_sameBase f l.2 n

end Limit

section Kernel

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] {f : ∀ n, R (n + 1) →+* R n}
  [∀ n, Algebra (limit f) (R n)] (hπ : ∀ n, algebraMap (limit f) (R n) = towerLimitProj f n)
include hπ

/-- `lim Rₙ` acts on `Rₙ` through the projection. -/
theorem smul_eq_towerLimitProj_mul (l : limit f) {n : ℕ} (x : R n) :
    l • x = towerLimitProj f n l * x := by
  rw [Algebra.smul_def, hπ]

/-- The transition map `Rₙ₊₁ → Rₙ`, as a map of `lim Rₙ`-modules. -/
def transitionLinearMap (n : ℕ) : R (n + 1) →ₗ[limit f] R n where
  toFun := f n
  map_add' := map_add (f n)
  map_smul' l x := by
    rw [RingHom.id_apply, smul_eq_towerLimitProj_mul hπ, smul_eq_towerLimitProj_mul hπ, map_mul]
    congr 1
    exact l.2 n

/-- `AlgebraicGeometry.C1590Private.transitionLinearMap` is `f n` on elements. -/
@[simp] theorem transitionLinearMap_apply (n : ℕ) (x : R (n + 1)) :
    transitionLinearMap hπ n x = f n x := rfl

variable (e : ℕ → limit f)
  (he : ∀ n (x : R n), toBase f n x = 0 → towerLimitProj f n (e n) * x = 0)

/-- The `n`-th component `Ker(lim Rₙ → R₀) → Ker(Rₙ₊₁ → Rₙ)`, `x ↦ eₙ xₙ₊₁`. -/
def kernelComponent (n : ℕ) :
    RingHom.ker (towerLimitProj f 0) →ₗ[limit f] LinearMap.ker (transitionLinearMap hπ n) :=
  LinearMap.codRestrict _
    (e n • (Algebra.linearMap (limit f) (R (n + 1)) ∘ₗ
      (RingHom.ker (towerLimitProj f 0)).subtype)) fun x => by
    rw [LinearMap.mem_ker, LinearMap.smul_apply, map_smul, smul_eq_towerLimitProj_mul hπ]
    refine he n _ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      Algebra.linearMap_apply, transitionLinearMap_apply, hπ]
    rw [show f n (towerLimitProj f (n + 1) x) = towerLimitProj f n x from x.1.2 n,
      toBase_towerLimitProj]
    exact x.2

/-- The value of `AlgebraicGeometry.C1590Private.kernelComponent`. -/
theorem coe_kernelComponent (n : ℕ) (x : RingHom.ker (towerLimitProj f 0)) :
    (kernelComponent hπ e he n x : R (n + 1)) =
      towerLimitProj f (n + 1) (e n) * towerLimitProj f (n + 1) x := by
  simp [kernelComponent, smul_eq_towerLimitProj_mul hπ, hπ]

/-- **`Ker(lim Rₙ → R₀) = ∏ₙ Ker(Rₙ₊₁ → Rₙ)`**, through the components
`AlgebraicGeometry.C1590Private.kernelComponent`, when `1 - eₙ` kills `Ker(Rₙ₊₁ → Rₙ)` and
`eₙ (1 - eₙ)` kills `Ker(Rₙ₊₁ → R₀)`. -/
theorem bijective_kernelComponent (hf : ∀ n, Function.Surjective (f n))
    (hV : ∀ n, ∀ z ∈ RingHom.ker (f n), towerLimitProj f (n + 1) (1 - e n) * z = 0)
    (he' : ∀ n (x : R (n + 1)), toBase f (n + 1) x = 0 →
      towerLimitProj f (n + 1) (e n * (1 - e n)) * x = 0) :
    Function.Bijective (LinearMap.pi (kernelComponent hπ e he)) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx => ?_, fun v => ?_⟩
  · have h : ∀ n, towerLimitProj f n x = 0 := by
      intro n
      induction n with
      | zero => exact x.2
      | succ n ih =>
        have hz : towerLimitProj f (n + 1) x ∈ RingHom.ker (f n) := by
          rw [RingHom.mem_ker]
          exact (x.1.2 n).trans ih
        have h1 := hV n _ hz
        have h2 := congrArg Subtype.val (congrFun hx n)
        rw [LinearMap.pi_apply, coe_kernelComponent] at h2
        simp only [Pi.zero_apply, Submodule.coe_zero] at h2
        simp only [map_sub, map_one] at h1
        linear_combination h1 + h2
    exact Subtype.ext (Subtype.ext (funext h))
  · choose σ hσ using hf
    let u : ∀ n, R n := fun n => Nat.rec (motive := fun n => R n) 0
      (fun n y => σ n y - towerLimitProj f (n + 1) (e n) * σ n y + (v n : R (n + 1))) n
    have hu1 : ∀ n, toBase f n (u n) = 0 → f n (u (n + 1)) = u n := by
      intro n hn
      change f n (σ n (u n) - towerLimitProj f (n + 1) (e n) * σ n (u n) + (v n : R (n + 1))) =
        u n
      have hv : f n (v n : R (n + 1)) = 0 := (v n).2
      rw [map_add, map_sub, map_mul, hσ, hv, show f n (towerLimitProj f (n + 1) (e n)) =
        towerLimitProj f n (e n) from (e n).2 n, he n _ hn, sub_zero, add_zero]
    have hu0 : ∀ n, toBase f n (u n) = 0 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [toBase_succ, hu1 n ih, ih]
    let x : RingHom.ker (towerLimitProj f 0) := ⟨⟨u, fun n => hu1 n (hu0 n)⟩, rfl⟩
    refine ⟨x, funext fun n => Subtype.ext ?_⟩
    rw [LinearMap.pi_apply, coe_kernelComponent]
    have hw : toBase f (n + 1) (σ n (u n)) = 0 := by rw [toBase_succ, hσ, hu0]
    have h1 := he' n _ hw
    have h2 := hV n _ (v n).2
    simp only [map_sub, map_one, map_mul] at h1 h2
    change towerLimitProj f (n + 1) (e n) *
      (σ n (u n) - towerLimitProj f (n + 1) (e n) * σ n (u n) + (v n : R (n + 1))) = v n
    linear_combination h1 - h2

end Kernel

section Tensor

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] {f : ∀ n, R (n + 1) →+* R n}
  [∀ n, Algebra (limit f) (R n)] (hπ : ∀ n, algebraMap (limit f) (R n) = towerLimitProj f n)
  (e : ℕ → limit f)
  (he : ∀ n (x : R n), toBase f n x = 0 → towerLimitProj f n (e n) * x = 0)
  (C : Type*) [AddCommGroup C] [Module (limit f) C]
include hπ

/-- `C ⊗ Ker(lim Rₙ → R₀) → ∏ₙ C ⊗ Ker(Rₙ₊₁ → Rₙ)`. -/
def kernelTensorPi : C ⊗[limit f] RingHom.ker (towerLimitProj f 0) →ₗ[limit f]
    ∀ n, C ⊗[limit f] LinearMap.ker (transitionLinearMap hπ n) :=
  piRightHom (limit f) (limit f) C _ ∘ₗ (LinearMap.pi (kernelComponent hπ e he)).lTensor C

/-- The components of `AlgebraicGeometry.C1590Private.kernelTensorPi`. -/
theorem kernelTensorPi_apply (t : C ⊗[limit f] RingHom.ker (towerLimitProj f 0)) (n : ℕ) :
    kernelTensorPi hπ e he C t n = (kernelComponent hπ e he n).lTensor C t := by
  induction t using TensorProduct.inductionOn with
  | tmul c x => rfl
  | add x y hx hy => rw [map_add, Pi.add_apply, hx, hy, map_add]

/-- The `n`-th component of `t ∈ C ⊗ Ker(lim Rₙ → R₀)`, read in `C ⊗ Rₙ₊₁`, is `eₙ` times the
image of `t`. -/
theorem lTensor_subtype_kernelTensorPi (t : C ⊗[limit f] RingHom.ker (towerLimitProj f 0))
    (n : ℕ) :
    (LinearMap.ker (transitionLinearMap hπ n)).subtype.lTensor C (kernelTensorPi hπ e he C t n) =
      e n • (Algebra.linearMap (limit f) (R (n + 1))).lTensor C
        ((RingHom.ker (towerLimitProj f 0)).subtype.lTensor C t) := by
  rw [kernelTensorPi_apply]
  induction t using TensorProduct.inductionOn with
  | tmul c x => simp [kernelComponent, TensorProduct.tmul_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, smul_add]

/-- `eₙ` acts as the identity on `C ⊗ Ker(Rₙ₊₁ → Rₙ)`. -/
theorem smul_tensor_kernel_eq_self
    (hV : ∀ n, ∀ z ∈ RingHom.ker (f n), towerLimitProj f (n + 1) (1 - e n) * z = 0) (n : ℕ)
    (w : C ⊗[limit f] LinearMap.ker (transitionLinearMap hπ n)) : e n • w = w := by
  have h : (1 - e n) • w = 0 := by
    induction w using TensorProduct.inductionOn with
    | tmul c v =>
      have hv : (1 - e n) • v = 0 := by
        refine Subtype.ext ?_
        rw [Submodule.coe_smul, smul_eq_towerLimitProj_mul hπ]
        exact hV n v.1 v.2
      rw [← TensorProduct.tmul_smul, hv, TensorProduct.tmul_zero]
    | add x y hx hy => rw [smul_add, hx, hy, add_zero]
  rwa [sub_smul, one_smul, sub_eq_zero, eq_comm] at h

/-- `C ⊗ lim Rₙ → C ⊗ Rₙ₊₁ → C ⊗ Rₙ` is `C ⊗ lim Rₙ → C ⊗ Rₙ`. -/
theorem lTensor_transition_comp (n : ℕ) (y : C ⊗[limit f] limit f) :
    (transitionLinearMap hπ n).lTensor C ((Algebra.linearMap (limit f) (R (n + 1))).lTensor C y) =
      (Algebra.linearMap (limit f) (R n)).lTensor C y := by
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
  congr 2
  refine LinearMap.ext fun l => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply, hπ,
    transitionLinearMap_apply]
  exact l.2 n

/-- An element of `C ⊗ lim Rₙ` dying in `C ⊗ Rₙ` dies in every `C ⊗ Rₖ`, `k ≤ n`. -/
theorem lTensor_algebraMap_eq_zero_of_le {y : C ⊗[limit f] limit f} {n : ℕ}
    (hy : (Algebra.linearMap (limit f) (R n)).lTensor C y = 0) {k : ℕ} (hk : k ≤ n) :
    (Algebra.linearMap (limit f) (R k)).lTensor C y = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction j with
  | zero => exact hy
  | succ j ih =>
    refine ih ?_ (Nat.le_add_right k j)
    rw [← lTensor_transition_comp hπ C (k + j)]
    exact (congrArg ((transitionLinearMap hπ (k + j)).lTensor C) hy).trans (map_zero _)

/-- The structure map `lim Rₙ → Rₙ` is surjective when the transition maps are. -/
private theorem algebraLinearMap_surjective (hf : ∀ n, Function.Surjective (f n)) (n : ℕ) :
    Function.Surjective (Algebra.linearMap (limit f) (R n)) := fun x => by
  obtain ⟨l, hl⟩ := towerLimitProj_surjective f hf n x
  exact ⟨l, by simp [hπ, hl]⟩

/-- `C ⊗ Ker(lim Rₙ → R₀) → C ⊗ lim Rₙ → C ⊗ R₀` is exact. -/
theorem exact_lTensor_base (hf : ∀ n, Function.Surjective (f n)) :
    Function.Exact ((RingHom.ker (towerLimitProj f 0)).subtype.lTensor C)
      ((Algebra.linearMap (limit f) (R 0)).lTensor C) := by
  refine lTensor_exact C (fun y => ?_) (algebraLinearMap_surjective hπ hf 0)
  simp only [Algebra.linearMap_apply, hπ, Set.mem_range, Submodule.coe_subtype]
  exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, by rintro ⟨x, rfl⟩; exact x.2⟩

/-- `C ⊗ Ker(Rₙ₊₁ → Rₙ) → C ⊗ Rₙ₊₁ → C ⊗ Rₙ` is exact. -/
theorem exact_lTensor_transition (hf : ∀ n, Function.Surjective (f n)) (n : ℕ) :
    Function.Exact ((LinearMap.ker (transitionLinearMap hπ n)).subtype.lTensor C)
      ((transitionLinearMap hπ n).lTensor C) :=
  lTensor_exact C (LinearMap.exact_subtype_ker_map _) (hf n)

/-- An element of `C ⊗ Ker(lim Rₙ → R₀)` whose components below `m` vanish dies in `C ⊗ Rₘ`. -/
theorem lTensor_algebraMap_eq_zero_of_components (hf : ∀ n, Function.Surjective (f n))
    (hV : ∀ n, ∀ z ∈ RingHom.ker (f n), towerLimitProj f (n + 1) (1 - e n) * z = 0)
    (U : C ⊗[limit f] RingHom.ker (towerLimitProj f 0)) (m : ℕ)
    (hU : ∀ i < m, kernelTensorPi hπ e he C U i = 0) :
    (Algebra.linearMap (limit f) (R m)).lTensor C
      ((RingHom.ker (towerLimitProj f 0)).subtype.lTensor C U) = 0 := by
  induction m with
  | zero => exact (exact_lTensor_base hπ C hf).apply_apply_eq_zero U
  | succ m ih =>
    set y := (Algebra.linearMap (limit f) (R (m + 1))).lTensor C
      ((RingHom.ker (towerLimitProj f 0)).subtype.lTensor C U)
    have hy : (transitionLinearMap hπ m).lTensor C y = 0 := by
      rw [lTensor_transition_comp]
      exact ih fun i hi => hU i (hi.trans m.lt_succ_self)
    obtain ⟨w, hw⟩ := ((exact_lTensor_transition hπ C hf m) y).mp hy
    have h1 := lTensor_subtype_kernelTensorPi hπ e he C U m
    rw [hU m m.lt_succ_self, map_zero] at h1
    rw [← hw, ← smul_tensor_kernel_eq_self hπ e C hV m w, map_smul, hw]
    exact h1.symm

variable [Module.Flat (limit f) C]

/-- For `C` flat, the `n`-th component of `t` vanishes once the image of `t` dies in
`C ⊗ Rₙ₊₁`. -/
private theorem kernelTensorPi_apply_eq_zero (t : C ⊗[limit f] RingHom.ker (towerLimitProj f 0))
    (n : ℕ) (ht : (Algebra.linearMap (limit f) (R (n + 1))).lTensor C
      ((RingHom.ker (towerLimitProj f 0)).subtype.lTensor C t) = 0) :
    kernelTensorPi hπ e he C t n = 0 := by
  apply Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
  rw [lTensor_subtype_kernelTensorPi, ht, smul_zero, map_zero]

/-- For `C` flat with `C ⊗ Ker(lim Rₙ → R₀) = ∏ₙ C ⊗ Ker(Rₙ₊₁ → Rₙ)`, an element of `C ⊗ lim Rₙ`
dying in every `C ⊗ Rₙ` is zero. -/
theorem eq_zero_of_forall_lTensor_algebraMap (hf : ∀ n, Function.Surjective (f n))
    (hΨ : Function.Bijective (kernelTensorPi hπ e he C)) (y : C ⊗[limit f] limit f)
    (hy : ∀ n, (Algebra.linearMap (limit f) (R n)).lTensor C y = 0) : y = 0 := by
  obtain ⟨t, rfl⟩ := ((exact_lTensor_base hπ C hf) y).mp (hy 0)
  suffices kernelTensorPi hπ e he C t = 0 by
    rw [hΨ.1 (this.trans (map_zero _).symm), map_zero]
  exact funext fun n => kernelTensorPi_apply_eq_zero hπ e he C t n (hy _)

/-- **The limit of the levels.** If the transition maps are surjective and
`C ⊗ Ker(lim Rₙ → R₀) = ∏ₙ C ⊗ Ker(Rₙ₊₁ → Rₙ)` through the components `x ↦ eₙ xₙ₊₁`, then every
compatible sequence of elements of `C ⊗ Rₙ` comes from exactly one element of `C`. -/
theorem existsUnique_tmul_one_eq (hf : ∀ n, Function.Surjective (f n))
    (hV : ∀ n, ∀ z ∈ RingHom.ker (f n), towerLimitProj f (n + 1) (1 - e n) * z = 0)
    (hΨ : Function.Bijective (kernelTensorPi hπ e he C)) (s : ∀ n, C ⊗[limit f] R n)
    (hs : ∀ n, (transitionLinearMap hπ n).lTensor C (s (n + 1)) = s n) :
    ∃! c : C, ∀ n, c ⊗ₜ[limit f] (1 : R n) = s n := by
  have hρ : ∀ n, Function.Surjective ((Algebra.linearMap (limit f) (R n)).lTensor C) :=
    fun n => LinearMap.lTensor_surjective C (algebraLinearMap_surjective hπ hf n)
  have h1 : ∀ (c : C) (n : ℕ), c ⊗ₜ[limit f] (1 : R n) =
      (Algebra.linearMap (limit f) (R n)).lTensor C (c ⊗ₜ[limit f] (1 : limit f)) :=
    fun c n => by simp
  refine existsUnique_of_exists_of_unique ?_ fun c c' hc hc' => ?_
  · choose x hx using fun n => hρ n (s n)
    have hd : ∀ n, (Algebra.linearMap (limit f) (R n)).lTensor C (x (n + 1) - x n) = 0 :=
      fun n => by rw [map_sub, ← lTensor_transition_comp hπ C n, hx, hx, hs, sub_self]
    choose t ht using fun n =>
      ((exact_lTensor_base hπ C hf) _).mp (lTensor_algebraMap_eq_zero_of_le hπ C (hd n)
        (Nat.zero_le n))
    have hti : ∀ n, ∀ i < n, kernelTensorPi hπ e he C (t n) i = 0 := by
      intro n i hi
      refine kernelTensorPi_apply_eq_zero hπ e he C _ i ?_
      rw [ht]
      exact lTensor_algebraMap_eq_zero_of_le hπ C (hd n) hi
    obtain ⟨T, hT⟩ := hΨ.2 fun i =>
      ∑ k ∈ Finset.range (i + 1), kernelTensorPi hπ e he C (t k) i
    refine ⟨TensorProduct.rid (limit f) C
      (x 0 + (RingHom.ker (towerLimitProj f 0)).subtype.lTensor C T), fun m => ?_⟩
    rw [h1, ← TensorProduct.rid_symm_apply, LinearEquiv.symm_apply_apply]
    have hxm : x m = x 0 + (RingHom.ker (towerLimitProj f 0)).subtype.lTensor C
        (∑ k ∈ Finset.range m, t k) := by
      rw [map_sum]
      simp_rw [ht]
      rw [Finset.sum_range_sub x m]
      abel
    have hsplit : x 0 + (RingHom.ker (towerLimitProj f 0)).subtype.lTensor C T =
        x m + (RingHom.ker (towerLimitProj f 0)).subtype.lTensor C
          (T - ∑ k ∈ Finset.range m, t k) := by
      rw [hxm, map_sub]
      abel
    rw [hsplit, map_add, hx,
      lTensor_algebraMap_eq_zero_of_components hπ e he C hf hV _ m fun i hi => ?_, add_zero]
    rw [map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, hT, sub_eq_zero]
    exact Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun k hk hk' =>
      hti k i (by simp only [Finset.mem_range] at hk hk'; omega)
  · have h0 := eq_zero_of_forall_lTensor_algebraMap hπ e he C hf hΨ
      ((c - c') ⊗ₜ[limit f] (1 : limit f)) fun n => by
        rw [TensorProduct.sub_tmul, map_sub, ← h1, ← h1, hc, hc', sub_self]
    have h0' := congrArg (TensorProduct.rid (limit f) C) h0
    rw [TensorProduct.rid_tmul, one_smul, map_zero, sub_eq_zero] at h0'
    exact h0'

end Tensor

section Special

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n)

/-- **The idempotents of a special tower.** For the pairwise distinct maximal ideals `𝔫ₙ` of
`lim Rₙ` over the points of a special tower there are `eₙ ∈ 𝔫₀ ⋯ 𝔫ₙ₋₁` with `1 - eₙ ∈ 𝔫ₙ`
(Chinese remainder theorem). Then `eₙ` kills `Ker(Rₙ → R₀)`, `eₙ (1 - eₙ)` kills
`Ker(Rₙ₊₁ → R₀)`, and `1 - eₙ` kills `Ker(Rₙ₊₁ → Rₙ)`. -/
theorem exists_towerIdempotents (hf : ∀ n, Function.Surjective (f n)) {𝔪 : ℕ → Ideal (R 0)}
    (h𝔪 : ∀ n, (𝔪 n).IsMaximal) (hne : Pairwise fun n m => 𝔪 n ≠ 𝔪 m)
    (hker : ∀ n (r : R (n + 1)), toBase f (n + 1) r ∈ 𝔪 n → ∀ z ∈ RingHom.ker (f n), r * z = 0) :
    ∃ (𝔫 : ℕ → Ideal (limit f)) (e : ℕ → limit f), (∀ n, (𝔫 n).IsMaximal) ∧
      (∀ n, ∀ l ∈ 𝔫 n, ∀ z ∈ RingHom.ker (f n), towerLimitProj f (n + 1) l * z = 0) ∧
      (∀ n (x : R n), toBase f n x = 0 → towerLimitProj f n (e n) * x = 0) ∧
      (∀ n, 1 - e n ∈ 𝔫 n) ∧
      (∀ n (x : R (n + 1)), toBase f (n + 1) x = 0 →
        towerLimitProj f (n + 1) (e n * (1 - e n)) * x = 0) := by
  let 𝔫 : ℕ → Ideal (limit f) := fun n => (𝔪 n).comap (towerLimitProj f 0)
  have h𝔫max : ∀ n, (𝔫 n).IsMaximal := fun n =>
    Ideal.comap_isMaximal_of_surjective _ (towerLimitProj_surjective f hf 0)
  have h𝔫ker : ∀ n, ∀ l ∈ 𝔫 n, ∀ z ∈ RingHom.ker (f n),
      towerLimitProj f (n + 1) l * z = 0 := fun n l hl z hz =>
    hker n _ (by rw [toBase_towerLimitProj]; exact hl) z hz
  have hJ : ∀ n, ∀ l ∈ ∏ j ∈ Finset.range n, 𝔫 j, ∀ x : R n, toBase f n x = 0 →
      towerLimitProj f n l * x = 0 := by
    intro n
    induction n with
    | zero =>
      intro l _ x hx
      rw [show x = 0 from hx, mul_zero]
    | succ n ih =>
      intro l hl x hx
      rw [Finset.prod_range_succ] at hl
      refine Submodule.mul_induction_on (C := fun r => towerLimitProj f (n + 1) r * x = 0) hl
        (fun a ha b hb => ?_) fun a b h1 h2 => ?_
      · have hz : towerLimitProj f (n + 1) a * x ∈ RingHom.ker (f n) := by
          rw [RingHom.mem_ker, map_mul,
            show f n (towerLimitProj f (n + 1) a) = towerLimitProj f n a from a.2 n]
          exact ih a ha _ hx
        rw [map_mul, mul_comm (towerLimitProj f (n + 1) a), mul_assoc]
        exact h𝔫ker n b hb _ hz
      · rw [map_add, add_mul, h1, h2, add_zero]
  have hcop : ∀ n, (∏ j ∈ Finset.range n, 𝔫 j) ⊔ 𝔫 n = ⊤ := by
    intro n
    by_contra hne'
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne'
    have h1 : 𝔫 n = M :=
      (h𝔫max n).eq_of_le hM.ne_top ((le_sup_right : 𝔫 n ≤ _ ⊔ 𝔫 n).trans hle)
    have h2 : ∏ j ∈ Finset.range n, 𝔫 j ≤ 𝔫 n := by
      rw [h1]
      exact (le_sup_left : ∏ j ∈ Finset.range n, 𝔫 j ≤ _ ⊔ 𝔫 n).trans hle
    obtain ⟨j, hj, hjn⟩ := ((h𝔫max n).isPrime.prod_le).mp h2
    have h3 : 𝔫 j = 𝔫 n := (h𝔫max j).eq_of_le (h𝔫max n).ne_top hjn
    exact hne (Finset.mem_range.mp hj).ne
      (Ideal.comap_injective_of_surjective _ (towerLimitProj_surjective f hf 0) h3)
  have hone : ∀ n, (1 : limit f) ∈ (∏ j ∈ Finset.range n, 𝔫 j) ⊔ 𝔫 n := fun n => by
    rw [hcop n]
    exact Submodule.mem_top
  choose a ha b hb hab using fun n => Submodule.mem_sup.mp (hone n)
  have hb' : ∀ n, 1 - a n ∈ 𝔫 n := fun n => by
    rw [← hab n, add_sub_cancel_left]
    exact hb n
  refine ⟨𝔫, a, h𝔫max, h𝔫ker, fun n => hJ n (a n) (ha n), hb', fun n x hx => hJ (n + 1) _ ?_ x hx⟩
  rw [Finset.prod_range_succ]
  exact Ideal.mul_mem_mul (ha n) (hb' n)

/-- `C ⊗ towerTransitionAlgHom` is `C ⊗ transitionLinearMap`. -/
theorem map_towerTransitionAlgHom_eq_lTensor (n : ℕ) (C : Type*) [CommRing C]
    [Algebra (limit f) C] :
    letI := fun m => (towerLimitProj f m).toAlgebra
    ∀ x : C ⊗[limit f] R (n + 1),
      Algebra.TensorProduct.map (AlgHom.id (limit f) C) (towerTransitionAlgHom f n) x =
        (transitionLinearMap (fun _ => rfl) n).lTensor C x := by
  let := fun m => (towerLimitProj f m).toAlgebra
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul c r => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **(B) for one tower.** Étale base change commutes with the limit of a special tower. -/
theorem isEtaleCompatibleTower_of_isSpecialTower (hf : ∀ n, Function.Surjective (f n))
    (hs : IsSpecialTower f) : IsEtaleCompatibleTower f := by
  obtain ⟨-, 𝔪, h𝔪, hne, hker⟩ := hs
  obtain ⟨𝔫, e, h𝔫max, h𝔫ker, he, he1, he'⟩ := exists_towerIdempotents f hf h𝔪 hne hker
  let : ∀ m, Algebra (limit f) (R m) := fun m => (towerLimitProj f m).toAlgebra
  unfold IsEtaleCompatibleTower
  intro C _ _ _ s hs
  have hπ : ∀ n, algebraMap (limit f) (R n) = towerLimitProj f n := fun n => rfl
  have := h𝔫max
  have hV : ∀ n, ∀ z ∈ RingHom.ker (f n), towerLimitProj f (n + 1) (1 - e n) * z = 0 :=
    fun n => h𝔫ker n _ (he1 n)
  have hQ := Stacks.C1590Private.bijective_piRightHom_of_etale
    (V := fun n => LinearMap.ker (transitionLinearMap hπ n)) 𝔫
    (fun n l hl v => Subtype.ext ((smul_eq_towerLimitProj_mul hπ l v.1).trans
      (h𝔫ker n l hl v.1 v.2))) C
  have hΦ := bijective_kernelComponent hπ e he hf hV he'
  have hΨ : Function.Bijective (kernelTensorPi hπ e he C) :=
    hQ.comp (((LinearEquiv.ofBijective _ hΦ).lTensor C).bijective)
  refine existsUnique_tmul_one_eq hπ e he C hf hV hΨ s fun n => ?_
  rw [← hs n, map_towerTransitionAlgHom_eq_lTensor]

end Special

/-- **(B).** The limit of a special tower of square-zero thickenings commutes with étale base
change. The square-zero hypothesis is not used. -/
theorem specialTowerEtaleCompatible : SpecialTowerEtaleCompatible.{u} :=
  fun _ _ f hf _ hs => isEtaleCompatibleTower_of_isSpecialTower f hf hs

end AlgebraicGeometry.C1590Private
