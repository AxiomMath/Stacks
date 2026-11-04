module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicTowerLimit
public import StacksFrontier.LinearAlgebra.BlockTrace

/-!
# Traces and ranks on the limit of a tower looking free

Let `H : ℕᵒᵖ ⥤ ModuleCat ℤ_p` be a tower of finite modules looking free
(`Stacks.EtaleCohomology.TowerLimit`), `M = lim H(n)` (finite free over `ℤ_p`) and `φ` an
endomorphism of `M`. The level `H(n)` is `M/pⁿ⁺¹M ≅ (ℤ/pⁿ⁺¹)^r`, `r` the rank of `M`, and:

* the trace over `ℤ/pⁿ⁺¹` of the map induced by `φ` on `H(n)`, read through any additive
  equivalence with a `ℤ/pⁿ⁺¹`-module, is the reduction of the trace of `φ`
  (`Stacks.EtaleCohomology.TowerLimit.trace_toZModLinearMap_eq_toZModPow_trace`);
* `#H(0) = p^r` (`Stacks.EtaleCohomology.TowerLimit.natCard_obj_zero`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v

namespace Stacks.EtaleCohomology.TowerLimit

variable {p : ℕ} [Fact p.Prime] {F : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[p]} [HasLimit F]
  (hkill : ∀ n (x : F.obj (op n)), (p : ℤ_[p]) ^ (n + 1) • x = 0)
  (hsurj : ∀ n, Function.Surjective (tr F (Nat.le_succ n)))
  (hker : ∀ n (x : F.obj (op (n + 1))), tr F (Nat.le_succ n) x = 0 →
    ∃ y, x = (p : ℤ_[p]) ^ (n + 1) • y)
  (htors : ∀ n k (x : F.obj (op (n + k + 1))), (p : ℤ_[p]) ^ (k + 1) • x = 0 →
    ∃ y, x = (p : ℤ_[p]) ^ (n + 1) • y)
  (hfin : ∀ n, Finite (F.obj (op n)))

/-- The reduction `M → (ι → ℤ/pⁿ⁺¹)` of the coordinates in a basis. -/
def basisReduction {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] {ι : Type*}
    (b : Module.Basis ι ℤ_[p] M) (n : ℕ) : M →+ (ι → ZMod (p ^ (n + 1))) where
  toFun x i := PadicInt.toZModPow (n + 1) (b.repr x i)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

/-- The reduction of coordinates in a finite basis is surjective. -/
theorem surjective_basisReduction {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] {ι : Type*}
    [Finite ι] (b : Module.Basis ι ℤ_[p] M) (n : ℕ) : Function.Surjective (basisReduction b n) := by
  intro v
  choose w hw using fun i => ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) (n + 1)) (v i)
  refine ⟨b.repr.symm (Finsupp.equivFunOnFinite.symm w), funext fun i => ?_⟩
  simp [basisReduction, hw]

/-- The kernel of the reduction of coordinates `M → (ι → ℤ/pⁿ⁺¹)` is `pⁿ⁺¹ M`. -/
theorem basisReduction_eq_zero_iff {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] {ι : Type*}
    (b : Module.Basis ι ℤ_[p] M) (n : ℕ) (x : M) :
    basisReduction b n x = 0 ↔ ∃ y, x = (p : ℤ_[p]) ^ (n + 1) • y := by
  constructor
  · intro h
    have hi : ∀ i, ∃ c, b.repr x i = (p : ℤ_[p]) ^ (n + 1) * c := fun i => by
      have h0 : PadicInt.toZModPow (n + 1) (b.repr x i) = 0 := congrFun h i
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at h0
      obtain ⟨c, hc⟩ := h0
      exact ⟨c, by rw [← hc, mul_comm]⟩
    choose c hc using hi
    refine ⟨b.repr.symm (Finsupp.ofSupportFinite c ?_), b.repr.injective (Finsupp.ext fun i => ?_)⟩
    · refine (b.repr x).finite_support.subset fun i hi => ?_
      rw [Function.mem_support, hc]
      exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)) hi
    · rw [map_smul, LinearEquiv.apply_symm_apply, Finsupp.smul_apply, Finsupp.ofSupportFinite_coe,
        hc, smul_eq_mul]
  · rintro ⟨y, rfl⟩
    ext i
    simp only [basisReduction, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul, Finsupp.smul_apply,
      smul_eq_mul, map_mul, map_pow, map_natCast, Pi.zero_apply]
    rw [← Nat.cast_pow, ZMod.natCast_self, zero_mul]

include hkill hsurj hker htors hfin in
/-- **The level `H(n)` is `(ℤ/pⁿ⁺¹)^r` through a basis of the limit**: an additive equivalence
`H(n) ≃ (ι → ℤ/pⁿ⁺¹)` carrying the projection `M → H(n)` to the reduction of coordinates. -/
theorem exists_levelAddEquiv (n : ℕ) {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℤ_[p] ↑(limit F)) :
    ∃ e : F.obj (op n) ≃+ (ι → ZMod (p ^ (n + 1))),
      ∀ x, e ((limit.π F (op n)).hom x) = basisReduction b n x := by
  let πn := (limit.π F (op n)).hom.toAddMonoidHom
  have hπ : Function.Surjective πn := fun y => surjective_π hsurj hfin n y
  have hk : πn.ker = (basisReduction b n).ker := by
    ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, basisReduction_eq_zero_iff]
    constructor
    · exact exists_eq_smul_of_π_eq_zero hkill hsurj hker htors n x
    · rintro ⟨y, rfl⟩
      show (limit.π F (op n)).hom ((p : ℤ_[p]) ^ (n + 1) • y) = 0
      rw [map_smul, hkill]
  refine ⟨(QuotientAddGroup.quotientKerEquivOfSurjective πn hπ).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq hk).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective _ (surjective_basisReduction b n))),
    fun x => ?_⟩
  have h1 : (QuotientAddGroup.quotientKerEquivOfSurjective πn hπ).symm (πn x) =
      (x : ↑(limit F) ⧸ πn.ker) :=
    (AddEquiv.symm_apply_eq _).2 rfl
  show (QuotientAddGroup.quotientKerEquivOfSurjective _ (surjective_basisReduction b n))
    ((QuotientAddGroup.quotientAddEquivOfEq hk)
      ((QuotientAddGroup.quotientKerEquivOfSurjective πn hπ).symm (πn x))) = _
  rw [h1]
  rfl

include hkill hsurj hker htors hfin in
/-- **The trace on a level is the reduction of the trace on the limit.** If `σ` is an additive
endomorphism of an abelian group `A` which, through an additive equivalence `θ : A ≃ H(n)`, is the
map induced by `φ`, then the trace of `σ` over `ℤ/pⁿ⁺¹` (for any `ℤ/pⁿ⁺¹`-module structure on `A`)
is the reduction of the trace of `φ`. -/
theorem trace_toZModLinearMap_eq_toZModPow_trace (φ : limit F ⟶ limit F) (n : ℕ)
    {A : Type*} [AddCommGroup A] [Module (ZMod (p ^ (n + 1))) A] (θ : A ≃+ F.obj (op n))
    (σ : A →+ A)
    (hσ : ∀ x : ↑(limit F), θ (σ (θ.symm ((limit.π F (op n)).hom x))) =
      (limit.π F (op n)).hom (φ.hom x)) :
    LinearMap.trace (ZMod (p ^ (n + 1))) A (σ.toZModLinearMap (p ^ (n + 1))) =
      PadicInt.toZModPow (n + 1) (LinearMap.trace ℤ_[p] _ φ.hom) := by
  have := finite hkill hsurj hker htors hfin
  have := free hkill hsurj hker htors hfin
  let b := Module.Free.chooseBasis ℤ_[p] ↑(limit F)
  obtain ⟨e, he⟩ := exists_levelAddEquiv hkill hsurj hker htors hfin n b
  let A' := (LinearMap.toMatrix b b φ.hom).map (PadicInt.toZModPow (p := p) (n + 1))
  let T := Matrix.toLin' A'
  have hT : ∀ x : ↑(limit F), T (basisReduction b n x) = basisReduction b n (φ.hom x) := by
    intro x
    funext i
    show (A'.mulVec (basisReduction b n x)) i = PadicInt.toZModPow (n + 1) (b.repr (φ.hom x) i)
    rw [← LinearMap.toMatrix_mulVec_repr b b φ.hom x, RingHom.map_mulVec]
    rfl
  have key := AddMonoidHom.trace_toZModLinearMap_eq_of_addEquiv (n := p ^ (n + 1))
    (e.symm.trans θ.symm) T.toAddMonoidHom σ (fun v => by
      obtain ⟨x, rfl⟩ := surjective_basisReduction b n v
      show θ.symm (e.symm (T (basisReduction b n x))) = σ (θ.symm (e.symm (basisReduction b n x)))
      rw [hT, ← he, ← he, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply,
        ← hσ, AddEquiv.symm_apply_apply])
  rw [← key]
  have hlin : T.toAddMonoidHom.toZModLinearMap (p ^ (n + 1)) = T := by
    ext v; rfl
  rw [hlin, LinearMap.trace_eq_matrix_trace (ZMod (p ^ (n + 1))) (Pi.basisFun _ _),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin',
    LinearMap.trace_eq_matrix_trace ℤ_[p] b, AddMonoidHom.map_trace]

include hkill hsurj hker htors hfin in
/-- **`#H(0) = p^r`**, `r` the rank of the limit. -/
theorem natCard_obj_zero : Nat.card (F.obj (op 0)) = p ^ Module.finrank ℤ_[p] ↑(limit F) := by
  have := finite hkill hsurj hker htors hfin
  have := free hkill hsurj hker htors hfin
  let b := Module.Free.chooseBasis ℤ_[p] ↑(limit F)
  obtain ⟨e, -⟩ := exists_levelAddEquiv hkill hsurj hker htors hfin 0 b
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, pow_one,
    Module.finrank_eq_card_chooseBasisIndex, Nat.card_eq_fintype_card]

end Stacks.EtaleCohomology.TowerLimit

end
