module

public import StacksFrontier.AlgebraicGeometry.Crystalline.StratifiedDescent
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorStratificationLevel
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPairEquivalence07JH

/-!
# The Taylor stratification of a pair

The proof of [Stacks, Proposition 60.17.4, Tag 07JH] builds the crystal of a pair `(M, ∇)` from
the Taylor series `m ⊗ 1 ↦ ∑_K θ_K(m) ⊗ ξ^{[K]}`, where `∇ m = ∑_i θ_i(m) d x_i` and
`θ_K = ∏_i θ_i^{k_i}`, and checks that it is a stratification: well defined (Taylor's formula),
unital and a cocycle.  This module does that over an abstract descent system
(`Crystalline.StratifiedDescent.System`) given the ring-level data of Taylor's formula on it.

## Main definitions

* `Crystalline.StratifiedDescent.TaylorData` — the monomials `ξ^{[K]}` and `v^{[K]} u^{[L]}` of
  the levels, their behaviour under the diagonal, the faces and the levels, and Taylor's formula
  for the ring `D`.
* `Crystalline.StratifiedDescent.pairStr`, `Crystalline.StratifiedDescent.pairStratification` —
  the Taylor stratification of a pair.

## Main results

* `Crystalline.StratifiedDescent.isUnital_pairStr`, `isCocycle_pairStr`,
  `isLevelCompatible_pairStr` — the three axioms of a stratification.
* `Crystalline.StratifiedDescent.pairStr_map` — morphisms of pairs commute with the Taylor
  stratifications.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped TensorProduct

universe u v₁ u₁ v uI

namespace Crystalline.StratifiedDescent

open Finset.HasAntidiagonal

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] {O : 𝒜ᵒᵖ ⥤ CommRingCat.{u}} {D : Type u} [CommRing D]

/-- **The data of Taylor's formula on a descent system**: the divided power monomials
`ξ^{[K]} ∈ O(T(1)_e)` and `v^{[K]} u^{[L]} ∈ O(T(2)_e)`, how they multiply, what the diagonal, the
three faces and the level maps do to them, the composite operators `δ_K` of `D` with Taylor's
formula `p₁(d) = ∑_K p₀(δ_K d) ξ^{[K]}` at every level, and the vanishing of `p^n` at each level.
Every field is a property of the rings `O(T(n)_e)` and of `D` alone. -/
structure TaylorData (S : System 𝒜 O D) (ι : Type uI) [DecidableEq ι] where
  /-- The monomials `ξ^{[K]}` of `O(T(1)_e)`. -/
  xi : ∀ e, (ι →₀ ℕ) → O.obj (op (S.T1 e))
  /-- The monomials `v^{[K]} u^{[L]}` of `O(T(2)_e)`. -/
  eta : ∀ e, (ι →₀ ℕ) × (ι →₀ ℕ) → O.obj (op (S.T2 e))
  /-- They multiply as divided power monomials. -/
  xi_mul : ∀ e A B, xi e A * xi e B =
    (((A + B).prod fun i n ↦ n.choose (A i) : ℕ) : O.obj (op (S.T1 e))) * xi e (A + B)
  /-- The diagonal kills every `ξ^{[K]}` with `K ≠ 0`. -/
  xi_diag : ∀ e K, (O.map (S.diag e).op).hom (xi e K) = if K = 0 then 1 else 0
  /-- The face `p₀₁` sends `ξ^{[L]}` to `u^{[L]}`. -/
  xi_face01 : ∀ e L, (O.map (S.face01 e).op).hom (xi e L) = eta e (0, L)
  /-- The face `p₁₂` sends `ξ^{[K]}` to `v^{[K]}`. -/
  xi_face12 : ∀ e K, (O.map (S.face12 e).op).hom (xi e K) = eta e (K, 0)
  /-- The face `p₀₂` sends `ξ^{[N]}` to `(u + v)^{[N]}`. -/
  xi_face02 : ∀ e N, (O.map (S.face02 e).op).hom (xi e N) = ∑ x ∈ antidiagonal N, eta e x
  /-- `v^{[K]} u^{[L]}` is the product of `v^{[K]}` and `u^{[L]}`. -/
  eta_mul : ∀ e K L, eta e (K, 0) * eta e (0, L) = eta e (K, L)
  /-- The level maps send `ξ^{[K]}` to `ξ^{[K]}`. -/
  xi_lev : ∀ e K, (O.map (S.lev1 e).op).hom (xi (e + 1) K) = xi e K
  /-- The composite operators `δ_K` of `D`. -/
  delta : (ι →₀ ℕ) → D →+ D
  /-- Taylor's formula in `O(T(1)_e)`: `p₁(d) = ∑_K p₀(δ_K d) ξ^{[K]}`, a finite sum. -/
  taylor : ∀ e (d : D), ∃ t : Finset (ι →₀ ℕ),
    (∀ A ∉ t, S.ptRing (S.v e 0) (delta A d) * xi e A = 0) ∧
      S.ptRing (S.v e 1) d = ∑ A ∈ t, S.ptRing (S.v e 0) (delta A d) * xi e A
  /-- The prime. -/
  p : ℕ
  /-- A power of `p` vanishing at each level. -/
  nil : ℕ → ℕ
  /-- It vanishes in `O(T(1)_e)`. -/
  nil_one : ∀ e, ((p : O.obj (op (S.T1 e)))) ^ nil e = 0
  /-- It vanishes in `O(T(2)_e)`. -/
  nil_two : ∀ e, ((p : O.obj (op (S.T2 e)))) ^ nil e = 0

/-! ### The Taylor stratification of a pair -/

section Push

variable {M : Type*} [AddCommGroup M] [Module D M] {B B' : Type u} [CommRing B] [CommRing B']

/-- The base change of `Crystalline.TaylorStratification` is the change of ring `twistMap`. -/
theorem push_eq_twistMap (q₀ : D →+* B) (σ : B →+* B') (r : D →+* B') (h : σ.comp q₀ = r)
    (z : TwistedScalars q₀ ⊗[D] M) :
    TaylorStratification.push σ r h z = twistMap σ h z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul b m => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Push

/-- An element of `p^n M` is `p^n` times an element of `M`. -/
theorem exists_eq_pow_smul_of_mem_pPowSmul {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N]
    [Module R N] {p n : ℕ} {x : N} (hx : x ∈ pPowSmul p R N n) :
    ∃ y : N, x = ((p : R) ^ n) • y := by
  rw [pPowSmul, DividedPowers.pAdicIdeal, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul] at hx
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  exact ⟨y, rfl⟩

/-- Two functions vanishing off finite sets vanish off a common finite set. -/
private theorem exists_finset_eq_zero_of_two {α X Y : Type*} [Zero X] [Zero Y]
    {f : α → X} {g : α → Y}
    (hf : ∃ s : Finset α, ∀ a ∉ s, f a = 0) (hg : ∃ s : Finset α, ∀ a ∉ s, g a = 0) :
    ∃ s : Finset α, (∀ a ∉ s, f a = 0) ∧ ∀ a ∉ s, g a = 0 := by
  classical
  obtain ⟨s, hs⟩ := hf
  obtain ⟨s', hs'⟩ := hg
  exact ⟨s ∪ s', fun a ha ↦ hs a (mt (Finset.mem_union_left _) ha),
    fun a ha ↦ hs' a (mt (Finset.mem_union_right _) ha)⟩

section Pair

variable {S : System 𝒜 O D} {ι : Type uI} [DecidableEq ι] (T : TaylorData S ι)
  {Omega : Type v} [AddCommGroup Omega] [Module D Omega] {dx : ι → Omega} {dd : D → Omega}
  {coord : ι → (Omega →ₗ[D] D)} (P : Pair.{u, v, uI, u} T.p D Omega dx dd)
  (hc : IsCoordinateDual dx coord)

/-- The terms of the Taylor map of a pair at a level vanish off a finite set. -/
theorem exists_finset_term_eq_zero (e : ℕ) (m : P.carrier) :
    ∃ s : Finset (ι →₀ ℕ), ∀ K ∉ s,
      TaylorStratification.term (S.ptRing (S.v e 0)) (T.xi e) (P.taylorThetaPowHom hc) m K = 0 := by
  refine ⟨(P.finite_taylorThetaPow_notMem hc (T.nil e) m).toFinset, fun K hK ↦ ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hK
  obtain ⟨y, hy⟩ := exists_eq_pow_smul_of_mem_pPowSmul hK
  refine TaylorStratification.term_eq_zero_of_smul (d := (T.p : D) ^ T.nil e) ?_ hy
  rw [map_pow, map_natCast]
  exact T.nil_one e

variable {P hc} in
/-- The terms of the Taylor map have finite support. -/
theorem finite_support_term (e : ℕ) (m : P.carrier) :
    (Function.support (TaylorStratification.term (S.ptRing (S.v e 0)) (T.xi e)
      (P.taylorThetaPowHom hc) m)).Finite := by
  obtain ⟨s, hs⟩ := exists_finset_term_eq_zero T P hc e m
  exact s.finite_toSet.subset fun K hK ↦ by
    by_contra h
    exact hK (hs K h)

variable (hfamD : IsThetaMonomialFamily D (fun i ↦ T.delta (Finsupp.single i 1))
    (fun K ↦ T.delta K))
  (hdelta : ∀ i f, coord i (dd f) = -T.delta (Finsupp.single i 1) f)

/-- **The Taylor stratification of a pair at the level `e`**:
`m ↦ ∑_K ξ^{[K]} ⊗ θ_K(m)`, semilinear for the second vertex. -/
noncomputable def pairStr (e : ℕ) :
    P.carrier →ₛₗ[S.ptRing (S.v e 1)] TwistedScalars (S.ptRing (S.v e 0)) ⊗[D] P.carrier where
  toFun m := TaylorStratification.taylorMap (S.ptRing (S.v e 0)) (T.xi e)
    (P.taylorThetaPowHom hc) m
  map_add' m n := TaylorStratification.taylorMap_add (finite_support_term T e m)
    (finite_support_term T e n)
  map_smul' d m := by
    obtain ⟨s, hs⟩ := exists_finset_term_eq_zero T P hc e m
    obtain ⟨t, ht, htay⟩ := T.taylor e d
    exact TaylorStratification.taylorMap_smul
      (fun A B ↦ (A + B).prod fun i n ↦ n.choose (A i)) T.delta (S.ptRing (S.v e 1))
      (T.xi_mul e) (fun K f m ↦ P.taylorThetaPow_smul hc hfamD hdelta K f m) d m s t hs ht htay

/-- The Taylor stratification of a pair sends `m` to its Taylor map `∑_K ξ^{[K]} ⊗ θ_K(m)`. -/
theorem pairStr_apply (e : ℕ) (m : P.carrier) :
    pairStr T P hc hfamD hdelta e m = TaylorStratification.taylorMap (S.ptRing (S.v e 0))
      (T.xi e) (P.taylorThetaPowHom hc) m := rfl

/-- The pullback of the Taylor stratification along a map into `T(1)_e` is the sum of the
pulled-back monomials. -/
theorem twistMap_pairStr {B : Type u} [CommRing B] (e : ℕ) (σ : O.obj (op (S.T1 e)) →+* B)
    (r : D →+* B) (h : σ.comp (S.ptRing (S.v e 0)) = r) (m : P.carrier) (s : Finset (ι →₀ ℕ))
    (hs : ∀ K ∉ s, TaylorStratification.term (S.ptRing (S.v e 0)) (T.xi e)
      (P.taylorThetaPowHom hc) m K = 0) :
    twistMap σ h (pairStr T P hc hfamD hdelta e m) =
      ∑ K ∈ s, TwistedScalars.mk r (σ (T.xi e K)) ⊗ₜ[D] P.taylorThetaPow hc K m := by
  rw [← push_eq_twistMap, pairStr_apply, TaylorStratification.push_taylorMap _ _ _ _ s hs]
  rfl

/-- **The unit axiom of the Taylor stratification.** -/
theorem isUnital_pairStr : S.IsUnital (pairStr T P hc hfamD hdelta) := by
  classical
  rw [S.isUnital_iff]
  intro e m
  obtain ⟨s, hs⟩ := exists_finset_term_eq_zero T P hc e m
  rw [S.pullStrat_apply, twistMap_pairStr T P hc hfamD hdelta e _ _ _ m (insert 0 s)
    (fun K hK ↦ hs K fun h' ↦ hK (Finset.mem_insert_of_mem h')),
    Finset.sum_eq_single_of_mem 0 (Finset.mem_insert_self _ _)]
  · rw [T.xi_diag, if_pos rfl, (P.isThetaMonomialFamily_taylorThetaPow hc).apply_zero]
    rfl
  · intro K _ hK0
    rw [T.xi_diag, if_neg hK0]
    exact TensorProduct.zero_tmul _ _

/-- The composite Taylor operators of a pair are `p^n`-divisible off a finite set. -/
theorem exists_finset_nsmul (n : ℕ) (m : P.carrier) :
    ∃ s : Finset (ι →₀ ℕ), ∀ K ∉ s, ∃ z, P.taylorThetaPowHom hc K m = (T.p ^ n : ℕ) • z := by
  refine ⟨(P.finite_taylorThetaPow_notMem hc n m).toFinset, fun K hK ↦ ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hK
  obtain ⟨y, hy⟩ := exists_eq_pow_smul_of_mem_pPowSmul hK
  refine ⟨y, ?_⟩
  rw [P.taylorThetaPowHom_apply, hy, ← Nat.cast_smul_eq_nsmul D, Nat.cast_pow]

/-- **The cocycle axiom of the Taylor stratification.** -/
theorem isCocycle_pairStr : S.IsCocycle (pairStr T P hc hfamD hdelta) := by
  rw [S.isCocycle_iff]
  intro e
  refine baseChange_ext fun m ↦ ?_
  rw [LinearMap.comp_apply, S.comparison_one_tmul, S.comparison_one_tmul, S.pullStrat_apply,
    S.pullStrat_apply, ← push_eq_twistMap, ← push_eq_twistMap, pairStr_apply]
  refine TaylorStratification.cocycle (O.map (S.face01 e).op).hom (O.map (S.face12 e).op).hom
    (O.map (S.face02 e).op).hom (S.ptRing (S.w e 0)) (S.ptRing (S.w e 1))
    (S.map_comp_ptRing (S.face01_v_zero e)) (S.map_comp_ptRing (S.face12_v_zero e))
    (S.map_comp_ptRing (S.face02_v_zero e)) (T.eta e)
    (T.xi_face01 e) (T.xi_face12 e) (T.xi_face02 e) (T.eta_mul e) ?_ (T.nil_one e)
    (T.nil_two e) (exists_finset_nsmul T P hc (T.nil e))
    (S.pullStrat (pairStr T P hc hfamD hdelta) (S.face01 e) _ _
      (S.map_comp_ptRing (S.face01_v_zero e)) (S.map_comp_ptRing (S.face01_v_one e))) ?_ m
  · intro K L m
    show P.taylorThetaPow hc L (P.taylorThetaPow hc K m) = P.taylorThetaPow hc (K + L) m
    rw [(P.isThetaMonomialFamily_taylorThetaPow hc).add]
    rfl
  · intro m
    rw [S.pullStrat_apply, ← push_eq_twistMap]
    rfl

/-- **The level axiom of the Taylor stratification.** -/
theorem isLevelCompatible_pairStr : S.IsLevelCompatible (pairStr T P hc hfamD hdelta) := by
  classical
  rw [S.isLevelCompatible_iff]
  intro e
  refine LinearMap.ext fun m ↦ ?_
  obtain ⟨s, hs, hs'⟩ := exists_finset_eq_zero_of_two (exists_finset_term_eq_zero T P hc e m)
    (exists_finset_term_eq_zero T P hc (e + 1) m)
  rw [S.pullStrat_apply, twistMap_pairStr T P hc hfamD hdelta (e + 1) _ _ _ m s hs', pairStr_apply,
    TaylorStratification.taylorMap_eq_sum s hs]
  refine Finset.sum_congr rfl fun K _ ↦ ?_
  rw [T.xi_lev]
  rfl

/-- **The Taylor stratification of a pair.** -/
noncomputable def pairStratification : Stratification S P.carrier where
  str := pairStr T P hc hfamD hdelta
  isUnital := isUnital_pairStr T P hc hfamD hdelta
  isCocycle := isCocycle_pairStr T P hc hfamD hdelta
  isLevelCompatible := isLevelCompatible_pairStr T P hc hfamD hdelta

omit hfamD hdelta in
/-- **A morphism of pairs commutes with the Taylor stratifications.** -/
theorem pairStr_map (hfamD : IsThetaMonomialFamily D (fun i ↦ T.delta (Finsupp.single i 1))
      (fun K ↦ T.delta K))
    (hdelta : ∀ i f, coord i (dd f) = -T.delta (Finsupp.single i 1) f)
    {Q : Pair.{u, v, uI, u} T.p D Omega dx dd} (φ : P ⟶ Q) (e : ℕ) (m : P.carrier) :
    pairStr T Q hc hfamD hdelta e (φ.toLinearMap m) =
      LinearMap.lTensor _ φ.toLinearMap (pairStr T P hc hfamD hdelta e m) := by
  classical
  obtain ⟨s, hs, hs'⟩ := exists_finset_eq_zero_of_two (exists_finset_term_eq_zero T P hc e m)
    (exists_finset_term_eq_zero T Q hc e (φ.toLinearMap m))
  rw [pairStr_apply, pairStr_apply, TaylorStratification.taylorMap_eq_sum s hs',
    TaylorStratification.taylorMap_eq_sum s hs, map_sum]
  refine Finset.sum_congr rfl fun K _ ↦ ?_
  rw [TaylorStratification.term, TaylorStratification.term, LinearMap.lTensor_tmul,
    P.taylorThetaPowHom_apply, Q.taylorThetaPowHom_apply, φ.taylorThetaPow_apply hc]

end Pair

end Crystalline.StratifiedDescent

end
