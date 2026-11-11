module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Projective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Examples.Algebra.LocallyFreeNotFpqcLocal
public import StacksFrontier.Examples.Algebra.RankOneSumNotLocallyFree.BaseChange
public import StacksFrontier.Examples.Algebra.RankOneSumNotLocallyFree.EulerCharMod2
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# A countable direct sum of invertible modules which is not locally free

Let `torus ℕ = ℚ[u_k, v_k : k ∈ ℕ]/(u_k² + v_k² - 1)` be the coordinate ring of a countable
product of circles over `ℚ`, and let `L_k = pointIdeal k = (u_k - 1, v_k)` be the ideal of the
rational point `(1, 0)` in the `k`-th factor. Each `L_k` is invertible, so `M = ⨁ k, L_k` is a
projective module and a countable direct sum of finite locally free modules of rank one. We show
that `M` is not locally free.

Suppose that the basic opens `D(f_i)` cover `Spec (torus ℕ)` and that every `M_{f_i}` is free.
Some `g = f_i` does not vanish at the point `P = ((1, 0), (1, 0), …)`, and `g` only involves the
coordinates below some `n`. Choose a basis of `M_g`; it is infinite, and `n + 1` of its vectors
lie in the localization of a finite piece `⨁_{k < n + r} L_k`, which therefore contains a free
direct summand of rank `n + 1`. Base change along the map `ψ : (torus ℕ)_g → torus (Fin r)`
which evaluates the coordinates outside `[n, n + r)` at `(1, 0)` and keeps the others: `ψ(g)` is
the nonzero rational number `g(P)`, the `L_k` with `k < n` become free of rank one, and the
`L_{n + t}` become the ideals `I_t` of the point in `torus (Fin r)`. Hence
`B^n × Q ≃ B^{n + 1} × P'` for `B = torus (Fin r)`, `Q = I_0 × ⋯ × I_{r - 1}` and a finite `P'`.

This is impossible. For the mod-two Euler characteristic `φ` of finite `B`-modules, the Euler
class `∑_k φ (⋀^k Q)` vanishes as soon as `Q` is stably of the form `B × P'`, while the Koszul
identity computes it as `φ (B ⧸ (I_0 + ⋯ + I_{r - 1})) = φ (ℚ) = 1`.

Combined with the faithfully flat trivialization of countable sums of invertible modules, this
gives a module which is not locally free but becomes free after a faithfully flat base change.

## Main results

* `Stacks.Examples.CircleTorus.not_nonempty_linearEquiv_idealPi`: there is no isomorphism
  `B^n × (I_0 × ⋯ × I_{r - 1}) ≃ B^{n + 1} × P'` with `P'` finite.
* `Stacks.Examples.CircleTorus.not_isLocallyFree_pointSum`: `⨁ k, pointIdeal k` is not locally
  free.
* `exists_countable_projective_directSum_isFiniteLocallyFreeOfRank_one_not_isLocallyFree`
  (Stacks 05WL): a countable ring with a projective, not locally free, countable direct sum of
  finite locally free modules of rank one.
* `Stacks.Examples.CircleTorus.exists_ring_faithfullyFlat_free_baseChange_not_isLocallyFree`
  (Stacks 05VF): a countable direct sum of rank one locally free modules which is not locally
  free and becomes free after a faithfully flat base change.

## Implementation notes

The source realizes the ring as a colimit of tensor products of coordinate rings of affine
curves and detects the failure of local freeness through Chern classes on products of curves.
Here the ring is the explicit product of circles over `ℚ` and the obstruction is the mod-two
Euler characteristic (the constant term modulo two of the Hilbert polynomial of a good
filtration), which is additive on short exact sequences and equals `1` on the residue field of a
rational point.

## References

* [Stacks Project, Tag 05WL](https://stacks.math.columbia.edu/tag/05WL)
* [Stacks Project, Tag 05VF](https://stacks.math.columbia.edu/tag/05VF)
-/

@[expose] public section

open scoped TensorProduct DirectSum

namespace Stacks.Examples.CircleTorus

/-! ### The Euler class of a product of ideals of points -/

/-- The ideal of the point in the `i`-th coordinate of `torus (Fin r)` for `i < r`, and the unit
ideal for `i ≥ r`. -/
noncomputable def pointIdeals (r i : ℕ) : Ideal (torus (Fin r)) :=
  if h : i < r then pointIdeal ⟨i, h⟩ else ⊤

/-- For `i < r`, `pointIdeals r i` is the ideal of the point in the `i`-th coordinate. -/
theorem pointIdeals_of_lt {r i : ℕ} (h : i < r) : pointIdeals r i = pointIdeal ⟨i, h⟩ :=
  dite_eq_left h

/-- Each `pointIdeals r i` is an invertible module. -/
instance invertible_pointIdeals (r i : ℕ) :
    Module.Invertible (torus (Fin r)) (pointIdeals r i) := by
  by_cases h : i < r
  · rw [pointIdeals_of_lt h]
    infer_instance
  · rw [pointIdeals, dite_eq_right h]
    exact Module.Invertible.congr
      (Submodule.topEquiv : (⊤ : Ideal (torus (Fin r))) ≃ₗ[torus (Fin r)] torus (Fin r)).symm

/-- `I 0 ⊔ ⋯ ⊔ I (j - 1) ≤ X` if and only if `I i ≤ X` for all `i < j`. -/
theorem partialSup_le_iff {B : Type*} [CommRing B] (I : ℕ → Ideal B) (X : Ideal B) :
    ∀ j, ModTwoInvariant.partialSup I j ≤ X ↔ ∀ i < j, I i ≤ X
  | 0 => ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => bot_le⟩
  | j + 1 => by
    change ModTwoInvariant.partialSup I j ⊔ I j ≤ X ↔ _
    rw [sup_le_iff, partialSup_le_iff I X j]
    constructor
    · rintro ⟨h₁, h₂⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h₁ i hi
      · exact h₂
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h j (Nat.lt_succ_self j)⟩

/-- For `j ≤ r`, `I_0 + ⋯ + I_{j - 1}` is the supremum of the ideals of the point in the
coordinates below `j`. -/
theorem partialSup_pointIdeals (r j : ℕ) (hj : j ≤ r) :
    ModTwoInvariant.partialSup (pointIdeals r) j =
      ⨆ j' ∈ {j' : Fin r | (j' : ℕ) < j}, pointIdeal j' := by
  apply le_antisymm
  · refine (partialSup_le_iff _ _ j).mpr fun i hi => ?_
    have hir : i < r := lt_of_lt_of_le hi hj
    rw [pointIdeals_of_lt hir]
    exact le_iSup₂ (f := fun (j' : Fin r) (_ : j' ∈ {j' : Fin r | (j' : ℕ) < j}) =>
      pointIdeal j') ⟨i, hir⟩ hi
  · refine iSup₂_le fun j' hj' => ?_
    have h := (partialSup_le_iff (pointIdeals r) _ j).mp le_rfl (j' : ℕ) hj'
    rwa [pointIdeals_of_lt j'.2] at h

/-- The multiplication maps `I_j ⊗ (B ⧸ (I_0 + ⋯ + I_{j - 1})) → B ⧸ (I_0 + ⋯ + I_{j - 1})` are
injective for `j < r`. -/
theorem injective_mulMap_pointIdeals (r j : ℕ) (hj : j < r) :
    Function.Injective (ModTwoInvariant.mulMap (pointIdeals r) j) := by
  have hS : (⟨j, hj⟩ : Fin r) ∉ {j' : Fin r | (j' : ℕ) < j} := fun h => lt_irrefl j h
  have key := injective_pointIdeal_tensor_quotient {j' : Fin r | (j' : ℕ) < j} hS
  have hmul : ModTwoInvariant.mulMap (pointIdeals r) j =
      (TensorProduct.lid (torus (Fin r))
          (torus (Fin r) ⧸ ModTwoInvariant.partialSup (pointIdeals r) j)).toLinearMap ∘ₗ
        (pointIdeals r j).subtype.rTensor
          (torus (Fin r) ⧸ ModTwoInvariant.partialSup (pointIdeals r) j) :=
    TensorProduct.ext' fun x y => by
      simp only [ModTwoInvariant.mulMap, TensorProduct.lift.tmul, LinearMap.comp_apply,
        Submodule.subtype_apply, LinearMap.lsmul_apply, LinearMap.rTensor_tmul,
        LinearEquiv.coe_coe, TensorProduct.lid_tmul]
  rw [hmul, partialSup_pointIdeals r j hj.le, pointIdeals_of_lt hj]
  exact key

/-- **The Euler class contradiction.** Let `φ` be a mod-two invariant of `torus (Fin r)`-modules
with `φ (B ⧸ (I_0 + ⋯ + I_{r - 1})) = 1`. Then there is no isomorphism
`B^n × (I_0 × ⋯ × I_{r - 1}) ≃ B^{n + 1} × P'` with `P'` finite. -/
theorem not_nonempty_linearEquiv_idealPi_of_eq_one {r : ℕ} (φ : ModTwoInvariant (torus (Fin r)))
    (hφ : φ.toFun (torus (Fin r) ⧸ ModTwoInvariant.partialSup (pointIdeals r) r) = 1) (n : ℕ)
    (P' : Type) [AddCommGroup P'] [Module (torus (Fin r)) P'] [Module.Finite (torus (Fin r)) P'] :
    ¬ Nonempty (((Fin n → torus (Fin r)) × ModTwoInvariant.idealPi (pointIdeals r) r)
      ≃ₗ[torus (Fin r)] ((Fin (n + 1) → torus (Fin r)) × P')) := by
  rintro ⟨e⟩
  obtain ⟨N₀, hN₀⟩ := exists_subsingleton_exteriorPower (torus (Fin r)) P'
  have h₁ := φ.sum_eulerSeq_eq_zero n (N₀ + r) (ModTwoInvariant.idealPi (pointIdeals r) r) P'
    (fun k hk => hN₀ k (le_trans (Nat.le_add_right N₀ r) hk)) e
  have hK := ModTwoInvariant.sum_exteriorPower_idealPi_tensor (pointIdeals r) φ r
    (fun j hj => injective_mulMap_pointIdeals r j hj) r le_rfl (torus (Fin r))
  have h₂ : ∑ k ∈ Finset.range (r + 1),
      φ.toFun (⋀[torus (Fin r)]^k (ModTwoInvariant.idealPi (pointIdeals r) r)) = 1 := by
    rw [← hφ, ← φ.congr' (TensorProduct.lid (torus (Fin r))
      (torus (Fin r) ⧸ ModTwoInvariant.partialSup (pointIdeals r) r)), ← hK]
    exact Finset.sum_congr rfl fun k _ => φ.congr' (TensorProduct.rid (torus (Fin r)) _).symm
  have h₃ : ∑ k ∈ Finset.range (N₀ + r + 1),
        φ.toFun (⋀[torus (Fin r)]^k (ModTwoInvariant.idealPi (pointIdeals r) r)) =
      ∑ k ∈ Finset.range (r + 1),
        φ.toFun (⋀[torus (Fin r)]^k (ModTwoInvariant.idealPi (pointIdeals r) r)) := by
    refine (Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun k _ hk => ?_).symm
    have hrk : r < k := by
      rw [Finset.mem_range] at hk
      omega
    have := ModTwoInvariant.subsingleton_exteriorPower_idealPi (pointIdeals r) r k hrk
    exact φ.eq_zero_of_subsingleton _
  rw [h₃, h₂] at h₁
  exact one_ne_zero h₁

/-- **No stable isomorphism `B^n × (I_0 × ⋯ × I_{r - 1}) ≃ B^{n + 1} × P'`** over
`B = torus (Fin r)`, where `I_t` is the ideal of the point `(1, 0)` in the `t`-th circle and `P'`
is finite. -/
theorem not_nonempty_linearEquiv_idealPi (r n : ℕ) (P' : Type) [AddCommGroup P']
    [Module (torus (Fin r)) P'] [Module.Finite (torus (Fin r)) P'] :
    ¬ Nonempty (((Fin n → torus (Fin r)) × ModTwoInvariant.idealPi (pointIdeals r) r)
      ≃ₗ[torus (Fin r)] ((Fin (n + 1) → torus (Fin r)) × P')) :=
  not_nonempty_linearEquiv_idealPi_of_eq_one (eulerCharModTwo r) (eulerCharModTwo_point r) n P'

/-! ### The reduction to the Euler class -/

/-- A free summand of rank `n + 1` of the base change of `∏_{k < n + r} L_k` to a localization
`A`, transported further to `B = torus (Fin r)` along a map keeping the coordinates in
`[n, n + r)` and evaluating those below `n`, contradicts `not_nonempty_linearEquiv_idealPi`. -/
theorem false_of_linearEquiv_window (n r : ℕ) {A : Type} [CommRing A] [Algebra (torus ℕ) A]
    [Algebra (torus ℕ) (torus (Fin r))] [Algebra A (torus (Fin r))]
    [IsScalarTower (torus ℕ) A (torus (Fin r))]
    (hu₁ : ∀ k, k < n → algebraMap (torus ℕ) (torus (Fin r)) (u k) = 1)
    (hv₁ : ∀ k, k < n → algebraMap (torus ℕ) (torus (Fin r)) (v k) = 0)
    (hu₂ : ∀ t : Fin r, algebraMap (torus ℕ) (torus (Fin r)) (u (n + (t : ℕ))) = u t)
    (hv₂ : ∀ t : Fin r, algebraMap (torus ℕ) (torus (Fin r)) (v (n + (t : ℕ))) = v t)
    (P : Submodule A (A ⊗[torus ℕ] pointPi (n + r))) [Module.Finite A P]
    (eP : (A ⊗[torus ℕ] pointPi (n + r)) ≃ₗ[A] (Fin (n + 1) → A) × P) : False := by
  let e₁ : (torus (Fin r) ⊗[torus ℕ] pointPi (n + r)) ≃ₗ[torus (Fin r)]
      (Fin (n + 1) → torus (Fin r)) × (torus (Fin r) ⊗[A] P) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (torus ℕ) A (torus (Fin r))
        (torus (Fin r)) (pointPi (n + r))).symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (torus (Fin r)) (torus (Fin r)))
        eP ≪≫ₗ
      TensorProduct.prodRight A (torus (Fin r)) (torus (Fin r)) (Fin (n + 1) → A) P ≪≫ₗ
      LinearEquiv.prodCongr
        (TensorProduct.piScalarRight A (torus (Fin r)) (torus (Fin r)) (Fin (n + 1)))
        (LinearEquiv.refl _ _)
  let f₁ := TensorProduct.piRight (torus ℕ) (torus (Fin r)) (torus (Fin r))
    (fun i : Fin (n + r) => pointFam (i : ℕ))
  let f₂ := (LinearEquiv.piCongrLeft (torus (Fin r))
    (fun i : Fin (n + r) => torus (Fin r) ⊗[torus ℕ] pointFam (i : ℕ)) finSumFinEquiv).symm
  let f₃ := LinearEquiv.sumPiEquivProdPi (torus (Fin r)) (Fin n) (Fin r)
    (fun s => torus (Fin r) ⊗[torus ℕ] pointFam ((finSumFinEquiv s : Fin (n + r)) : ℕ))
  let f₄ : ((s : Fin n) →
        torus (Fin r) ⊗[torus ℕ] pointFam ((finSumFinEquiv (Sum.inl s) : Fin (n + r)) : ℕ))
      ≃ₗ[torus (Fin r)] (Fin n → torus (Fin r)) :=
    LinearEquiv.piCongrRight fun s => tensorPointEquivSelf _ (hu₁ _ s.2) (hv₁ _ s.2)
  let f₅ : ((t : Fin r) →
        torus (Fin r) ⊗[torus ℕ] pointFam ((finSumFinEquiv (Sum.inr t) : Fin (n + r)) : ℕ))
      ≃ₗ[torus (Fin r)] ModTwoInvariant.idealPi (pointIdeals r) r :=
    LinearEquiv.piCongrRight fun t => tensorPointEquiv (hu₂ t) (hv₂ t) ≪≫ₗ
      LinearEquiv.ofEq _ _ (pointIdeals_of_lt t.2).symm
  let e₂ : (torus (Fin r) ⊗[torus ℕ] pointPi (n + r)) ≃ₗ[torus (Fin r)]
      (Fin n → torus (Fin r)) × ModTwoInvariant.idealPi (pointIdeals r) r :=
    f₁ ≪≫ₗ f₂ ≪≫ₗ f₃ ≪≫ₗ f₄.prodCongr f₅
  exact not_nonempty_linearEquiv_idealPi r n (torus (Fin r) ⊗[A] P) ⟨e₂.symm ≪≫ₗ e₁⟩

/-- If the composite `A ⊗ ⨁ k, L_k → A ⊗ ∏_{k < N} L_k → A ⊗ ⨁ k, L_k` is the identity, then
`L_N ⊗ B = 0` for every `A`-algebra `B`; this is impossible when `u_N ↦ 1` and `v_N ↦ 0` in a
nonzero `B`. -/
theorem false_of_comp_eq_id {A B : Type} [CommRing A] [CommRing B] [Nontrivial B]
    [Algebra (torus ℕ) A] [Algebra (torus ℕ) B] [Algebra A B] [IsScalarTower (torus ℕ) A B]
    (N : ℕ)
    (hid : ((extend (torus ℕ) pointFam N).baseChange A).comp
      ((truncate (torus ℕ) pointFam N).baseChange A) = LinearMap.id)
    (hu : algebraMap (torus ℕ) B (u N) = 1) (hv : algebraMap (torus ℕ) B (v N) = 0) : False := by
  have hz : (1 : A) ⊗ₜ[torus ℕ]
      DirectSum.lof (torus ℕ) ℕ pointFam N ⟨v N, v_mem_pointIdeal N⟩ = 0 := by
    have h := LinearMap.congr_fun hid
      ((1 : A) ⊗ₜ[torus ℕ] DirectSum.lof (torus ℕ) ℕ pointFam N ⟨v N, v_mem_pointIdeal N⟩)
    rw [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.baseChange_tmul,
      LinearMap.baseChange_tmul, truncate_lof_of_le (torus ℕ) pointFam N N le_rfl, map_zero,
      TensorProduct.tmul_zero] at h
    exact h.symm
  let θ : A ⊗[torus ℕ] pointSum →ₗ[torus ℕ] B ⊗[torus ℕ] pointFam N :=
    TensorProduct.map (IsScalarTower.toAlgHom (torus ℕ) A B).toLinearMap
      (DirectSum.component (torus ℕ) ℕ pointFam N)
  have h₁ : θ ((1 : A) ⊗ₜ[torus ℕ]
      DirectSum.lof (torus ℕ) ℕ pointFam N ⟨v N, v_mem_pointIdeal N⟩) =
      (1 : B) ⊗ₜ[torus ℕ] (⟨v N, v_mem_pointIdeal N⟩ : pointFam N) := by
    simp only [θ, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one,
      DirectSum.component.lof_self]
  rw [hz, map_zero] at h₁
  have hinj := (Module.Invertible.bijective_of_surjective
    (surjective_tensorPointGen (B := B) hu hv)).injective
  have h₂ : tensorPointGen (B := B) N 1 = tensorPointGen (B := B) N 0 := by
    rw [map_zero, tensorPointGen, LinearMap.toSpanSingleton_apply_one]
    exact h₁.symm
  exact one_ne_zero (hinj h₂)

/-- A localization `(torus ℕ)_g` with `g(P) ≠ 0` over which `⨁ k, L_k` has a finite basis does
not exist. -/
theorem false_of_finite_basis (n : ℕ) (g : torus ℕ) (hg : IsUnit (windowMap n 0 g)) {κ : Type}
    [Finite κ]
    (b : Module.Basis κ (Localization.Away g) (Localization.Away g ⊗[torus ℕ] pointSum)) :
    False := by
  classical
  have := Fintype.ofFinite κ
  choose N' hN' using fun j =>
    exists_baseChange_extend_truncate (torus ℕ) pointFam (Localization.Away g) (b j)
  obtain ⟨N, hN, hnN⟩ : ∃ N, Finset.univ.sup N' ≤ N ∧ n ≤ N :=
    ⟨Finset.univ.sup N' + n, Nat.le_add_right _ _, Nat.le_add_left _ _⟩
  have hid : ((extend (torus ℕ) pointFam N).baseChange (Localization.Away g)).comp
      ((truncate (torus ℕ) pointFam N).baseChange (Localization.Away g)) = LinearMap.id :=
    b.ext fun j => by
      rw [LinearMap.comp_apply, LinearMap.id_apply]
      exact hN' j N ((Finset.le_sup (Finset.mem_univ j)).trans hN)
  let : Algebra (torus ℕ) (torus (Fin 0)) := (windowMap n 0).toRingHom.toAlgebra
  let : Algebra (Localization.Away g) (torus (Fin 0)) :=
    (IsLocalization.Away.lift (S := Localization.Away g) g
      (g := algebraMap (torus ℕ) (torus (Fin 0))) hg).toAlgebra
  have : IsScalarTower (torus ℕ) (Localization.Away g) (torus (Fin 0)) :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.Away.lift_comp (S := Localization.Away g) g
      (g := algebraMap (torus ℕ) (torus (Fin 0))) hg).symm
  have := nontrivial_torus (Fin 0)
  exact false_of_comp_eq_id (A := Localization.Away g) (B := torus (Fin 0)) N hid
    (windowMap_u_of_notMem n 0 N fun h => absurd h.2 (by omega))
    (windowMap_v_of_notMem n 0 N fun h => absurd h.2 (by omega))

/-- The reduction step: a free summand of rank `n + 1` of the base change of `∏_{k < n + r} L_k`
to `(torus ℕ)_g`, where `windowMap n r g` is a unit, does not exist. -/
theorem false_of_window (n r : ℕ) (g : torus ℕ) (hg : IsUnit (windowMap n r g))
    (P : Submodule (Localization.Away g) (Localization.Away g ⊗[torus ℕ] pointPi (n + r)))
    [Module.Finite (Localization.Away g) P]
    (eP : (Localization.Away g ⊗[torus ℕ] pointPi (n + r)) ≃ₗ[Localization.Away g]
      (Fin (n + 1) → Localization.Away g) × P) : False := by
  let : Algebra (torus ℕ) (torus (Fin r)) := (windowMap n r).toRingHom.toAlgebra
  let : Algebra (Localization.Away g) (torus (Fin r)) :=
    (IsLocalization.Away.lift (S := Localization.Away g) g
      (g := algebraMap (torus ℕ) (torus (Fin r))) hg).toAlgebra
  have : IsScalarTower (torus ℕ) (Localization.Away g) (torus (Fin r)) :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.Away.lift_comp (S := Localization.Away g) g
      (g := algebraMap (torus ℕ) (torus (Fin r))) hg).symm
  exact false_of_linearEquiv_window n r
    (fun k hk => windowMap_u_of_notMem n r k fun h => absurd h.1 (by omega))
    (fun k hk => windowMap_v_of_notMem n r k fun h => absurd h.1 (by omega))
    (fun t => windowMap_u_add n r t) (fun t => windowMap_v_add n r t) P eP

/-- **The direct sum of the ideals of the points is not locally free.** -/
theorem not_isLocallyFree_pointSum : ¬ Module.IsLocallyFree (torus ℕ) pointSum := by
  rintro ⟨ι, f, hspan, hfree⟩
  obtain ⟨i, hi⟩ : ∃ i, evalAll ℕ (f i) ≠ 0 := by
    by_contra h
    push Not at h
    have hle : Ideal.span (Set.range f) ≤ RingHom.ker (evalAll ℕ) :=
      Ideal.span_le.mpr (by
        rintro _ ⟨j, rfl⟩
        exact RingHom.mem_ker.mpr (h j))
    rw [hspan] at hle
    have h₁ : evalAll ℕ 1 = 0 := RingHom.mem_ker.mp (hle Submodule.mem_top)
    rw [map_one] at h₁
    exact one_ne_zero h₁
  obtain ⟨n, hn⟩ := exists_windowMap_eq (f i)
  have hunit : ∀ r, IsUnit (windowMap n r (f i)) := fun r => by
    rw [hn n r le_rfl]
    exact (Ne.isUnit hi).map (Algebra.ofId ℚ (torus (Fin r)))
  have : Module.Free (Localization.Away (f i))
      (LocalizedModule (Submonoid.powers (f i)) pointSum) := hfree i
  have hbase := (IsLocalizedModule.isBaseChange (Submonoid.powers (f i))
    (Localization.Away (f i)) (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) pointSum)).equiv
  have : Module.Free (Localization.Away (f i)) (Localization.Away (f i) ⊗[torus ℕ] pointSum) :=
    Module.Free.of_equiv hbase.symm
  obtain ⟨e, he⟩ : ∃ e : Fin (n + 1) → Module.Free.ChooseBasisIndex (Localization.Away (f i))
      (Localization.Away (f i) ⊗[torus ℕ] pointSum), Function.Injective e := by
    by_cases hκ : Finite (Module.Free.ChooseBasisIndex (Localization.Away (f i))
      (Localization.Away (f i) ⊗[torus ℕ] pointSum))
    · have := hκ
      exact (false_of_finite_basis n (f i) (hunit 0) (Module.Free.chooseBasis _ _)).elim
    · have := not_finite_iff_infinite.mp hκ
      exact ⟨fun j => Infinite.natEmbedding _ j,
        (Infinite.natEmbedding _).injective.comp Fin.val_injective⟩
  obtain ⟨N₀, hN₀⟩ := exists_linearEquiv_pi_prod (torus ℕ) pointFam
    (Module.Free.chooseBasis (Localization.Away (f i))
      (Localization.Away (f i) ⊗[torus ℕ] pointSum)) e he
  obtain ⟨P, hP, ⟨eP⟩⟩ := hN₀ (n + N₀) (Nat.le_add_left N₀ n)
  have := hP
  exact false_of_window n N₀ (f i) (hunit N₀) P eP

/-- **Stacks 05WL.** There is a countable ring `R` and a projective `R`-module which is a direct
sum of countably many finite locally free modules of rank one but is not locally free. The ring
is the coordinate ring of a countable product of circles over `ℚ`, and the summands are the ideals
of a rational point in the factors. -/
@[stacks 05WL "a countable ring with a countable direct sum of invertible (finite locally free \
rank one) modules that is projective but not locally free"]
theorem exists_countable_projective_directSum_isFiniteLocallyFreeOfRank_one_not_isLocallyFree :
    ∃ (R : Type) (_ : CommRing R), Countable R ∧ ∃ L : ℕ → ModuleCat.{0} R,
      (∀ n, Module.IsFiniteLocallyFreeOfRank R (L n) 1) ∧
        Module.Projective R (DirectSum ℕ fun n => L n) ∧
          ¬ Module.IsLocallyFree R (DirectSum ℕ fun n => L n) :=
  ⟨torus ℕ, inferInstance, inferInstance,
    fun n => ModuleCat.of (torus ℕ) (pointFam n),
    fun n => isFiniteLocallyFreeOfRank_pointIdeal n,
    Module.Projective.directSum_iff.mpr fun n =>
      (inferInstance : Module.Projective (torus ℕ) (pointFam n)),
    not_isLocallyFree_pointSum⟩

/-- **Stacks 05VF.** Being locally free does not descend along faithfully flat ring maps. The
direct sum `⨁ k, pointIdeal k` over the coordinate ring of a countable product of circles over `ℚ`
is a countable direct sum of rank one locally free modules which is projective and not locally
free (Stacks 05WL), and it becomes free over a faithfully flat algebra. -/
@[stacks 05VF "being locally free does not descend along faithfully flat ring maps: a projective \
countable direct sum of rank one locally free modules which is not locally free becomes free \
after a faithfully flat base change"]
theorem exists_ring_faithfullyFlat_free_baseChange_not_isLocallyFree :
    ∃ (R : Type) (_ : CommRing R) (L : ℕ → Type) (_ : ∀ n, AddCommGroup (L n))
      (_ : ∀ n, Module R (L n)),
      (∀ n, Module.IsFiniteLocallyFreeOfRank R (L n) 1) ∧ ¬ Module.IsLocallyFree R (⨁ n, L n) ∧
        ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S), Module.Projective R (⨁ n, L n) ∧
          Module.FaithfullyFlat R S ∧ Module.Free S (S ⊗[R] (⨁ n, L n)) := by
  obtain ⟨S, hS, hAlg, hproj, hff, hfree⟩ :=
    Stacks.Examples.exists_faithfullyFlat_free_baseChange_directSum.{0} (R := torus ℕ) pointFam
      fun n => isFiniteLocallyFreeOfRank_pointIdeal n
  exact ⟨torus ℕ, inferInstance, pointFam, inferInstance, inferInstance,
    fun n => isFiniteLocallyFreeOfRank_pointIdeal n, not_isLocallyFree_pointSum,
    S, hS, hAlg, hproj, hff, hfree⟩

end Stacks.Examples.CircleTorus
