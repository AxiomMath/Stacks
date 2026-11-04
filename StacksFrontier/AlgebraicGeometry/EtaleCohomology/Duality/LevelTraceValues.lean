module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.WayOutPairing
public import StacksFrontier.Algebra.Module.Injective.ZModPrimePower

/-!
# Changing the group of values of a trace

Let `t : Ext^N(O, D) → A` be a trace and `ι : A → A'` an injective additive map. If every additive
map `Ext^j(F, D) → A'` factors through `ι`, then duality at `F` for `ι ∘ t` is duality at `F` for
`t`: the pairings differ by the bijection `Hom(Ext^j(F, D), A) → Hom(Ext^j(F, D), A')`.

The example is `ι : ℤ/p ↪ ℤ/pᵐ`, `x ↦ p^{m-1} x`
(`Stacks.EtaleCohomology.LevelChange.zmodPowEmbedding`): every map from a group killed by `p` to
`ℤ/pᵐ` lands in the `p`-torsion `p^{m-1} ℤ/pᵐ`, the image of `ι`. So Poincaré duality with `ℤ/ℓ`
coefficients, whose traces take values in `ℤ/ℓ`, is also duality for the traces valued in `ℤ/ℓᵐ`.

## Main results

* `CategoryTheory.Abelian.Ext.isDualityPerfect_comp_iff_of_injective`.
* `Stacks.EtaleCohomology.LevelChange.zmodPowEmbedding`, `injective_zmodPowEmbedding`,
  `exists_comp_zmodPowEmbedding_eq`.
-/

@[expose] public noncomputable section

universe w v u

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {A A' : Type*} [AddCommGroup A] [AddCommGroup A']

/-- **Duality does not see an injective change of the group of values**, as long as every map
out of the dual `Ext` groups factors through it. -/
theorem isDualityPerfect_comp_iff_of_injective {O D : C} {N : ℕ} (t : Ext.{w} O D N →+ A)
    (ι : A →+ A') (hι : Function.Injective ι) (F : C)
    (hfac : ∀ (j : ℕ) (φ : Ext.{w} F D j →+ A'), ∃ ψ : Ext.{w} F D j →+ A, ι.comp ψ = φ) :
    IsDualityPerfect O D N (ι.comp t) F ↔ IsDualityPerfect O D N t F := by
  refine forall_congr' fun i => forall_congr' fun j => forall_congr' fun h => ?_
  let post : (Ext.{w} F D j →+ A) → (Ext.{w} F D j →+ A') := fun φ => ι.comp φ
  have hpost : Function.Bijective post :=
    ⟨fun φ ψ hφψ => AddMonoidHom.ext fun y => hι (DFunLike.congr_fun hφψ y),
      fun φ => hfac j φ⟩
  have hcomp : ⇑(dualityPairing O D N (ι.comp t) F h) = post ∘ dualityPairing O D N t F h := by
    funext x
    ext y
    rfl
  rw [hcomp]
  exact Function.Bijective.of_comp_iff' hpost _

end CategoryTheory.Abelian.Ext

namespace Stacks.EtaleCohomology.LevelChange

variable (p m : ℕ) [Fact p.Prime] [NeZero m]

/-- **`ℤ/p ↪ ℤ/pᵐ`, `x ↦ p^{m-1} x`.** -/
def zmodPowEmbedding : ZMod p →+ ZMod (p ^ m) :=
  ZMod.lift p ⟨(AddMonoidHom.mulLeft ((p : ZMod (p ^ m)) ^ (m - 1))).comp
      (Int.castAddHom (ZMod (p ^ m))), by
    change (p : ZMod (p ^ m)) ^ (m - 1) * ((p : ℤ) : ZMod (p ^ m)) = 0
    rw [Int.cast_natCast, ← pow_succ, Nat.sub_add_cancel (NeZero.one_le), ← Nat.cast_pow,
      ZMod.natCast_self]⟩

omit [Fact p.Prime] in
/-- The embedding `ℤ/p ↪ ℤ/pᵐ` sends the class of `k : ℕ` to the class of `p^{m-1} k`. -/
theorem zmodPowEmbedding_natCast (k : ℕ) :
    zmodPowEmbedding p m (k : ZMod p) = ((p ^ (m - 1) * k : ℕ) : ZMod (p ^ m)) := by
  rw [← Int.cast_natCast (R := ZMod p), zmodPowEmbedding, ZMod.lift_coe]
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft,
    Int.coe_castAddHom, Int.cast_natCast, Nat.cast_mul, Nat.cast_pow]

/-- The map `ℤ/p → ℤ/pᵐ`, `x ↦ p^{m-1} x`, is injective. -/
theorem injective_zmodPowEmbedding : Function.Injective (zmodPowEmbedding p m) := by
  have hp : p.Prime := Fact.out
  have hm : p ^ m = p ^ (m - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel (NeZero.one_le)]
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ZMod p) = x := ⟨x.val, ZMod.natCast_zmod_val x⟩
  rw [zmodPowEmbedding_natCast, CharP.cast_eq_zero_iff (ZMod (p ^ m)) (p ^ m), hm] at hx
  exact (CharP.cast_eq_zero_iff (ZMod p) p k).2
    (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) hx)

/-- **Every map from a group killed by `p` to `ℤ/pᵐ` factors through `ℤ/p ↪ ℤ/pᵐ`.** -/
theorem exists_comp_zmodPowEmbedding_eq {V : Type*} [AddCommGroup V]
    (hV : ∀ v : V, p • v = 0) (φ : V →+ ZMod (p ^ m)) :
    ∃ ψ : V →+ ZMod p, (zmodPowEmbedding p m).comp ψ = φ := by
  have hmem : ∀ v, ∃ x : ZMod p, zmodPowEmbedding p m x = φ v := by
    intro v
    have h0 : (p : ZMod (p ^ m)) ^ (m - (m - 1)) * φ v = 0 := by
      rw [Nat.sub_sub_self (NeZero.one_le), pow_one, ← nsmul_eq_mul, ← map_nsmul, hV, map_zero]
    obtain ⟨s, hs⟩ := Stacks.ZModPrimePower.exists_eq_pow_mul_of_pow_mul_eq_zero
      (Nat.sub_le m 1) h0
    refine ⟨(s.val : ZMod p), ?_⟩
    rw [zmodPowEmbedding_natCast, hs, Nat.cast_mul, Nat.cast_pow, ZMod.natCast_zmod_val]
  choose ψ hψ using hmem
  refine ⟨AddMonoidHom.mk' ψ fun v w => injective_zmodPowEmbedding p m ?_, AddMonoidHom.ext hψ⟩
  rw [map_add, hψ, hψ, hψ, map_add]

end Stacks.EtaleCohomology.LevelChange

end
