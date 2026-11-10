module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveExtWeilPairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CyclicCoverSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.WayOutPairing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Poincaré duality for `ℤ/ℓ` on a smooth proper curve, in all degrees

Let `X` be a smooth proper curve over an algebraically closed field `k`, `ℓ` a prime invertible in
`k`, and `t : H²(X, ℤ/ℓ) → ℤ/ℓ` an isomorphism (a trace map). Then the Yoneda pairing

`Ext^i(ℤ/ℓ, ℤ/ℓ) × Ext^{2-i}(ℤ/ℓ, ℤ/ℓ) → Ext²(ℤ/ℓ, ℤ/ℓ) → ℤ/ℓ`

is perfect for `i = 0, 1, 2`: in the language of `CategoryTheory.Abelian.Ext.IsDualityPerfect`,
duality holds at the constant sheaf. In degree `1` this is the nondegeneracy of the cup product on
`H¹` (`Stacks.EtaleCohomology.ExtensionTorsor.bijective_bilinearComp_flip`), transposed by a
dimension count; in degrees `0` and `2` it is `End(ℤ/ℓ_X) = ℤ/ℓ` and `#H²(X, ℤ/ℓ) = ℓ`.

This is the base case of Poincaré duality in dimension `d` by induction on the dimension, and,
with `CategoryTheory.Abelian.Ext.isDualityPerfect_of_resolution` and
`CategoryTheory.Abelian.Ext.isDualityPerfect_obj_iff`, the input for locally constant
coefficients on curves.

## Main results

* `Stacks.EtaleCohomology.ExtensionTorsor.natCard_addMonoidHom_zmod`: `#Hom(V, ℤ/ℓ) = #V`.
* `Stacks.EtaleCohomology.ExtensionTorsor.isDualityPerfect_unitSheaf`: duality at `ℤ/ℓ_X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.ExtensionTorsor

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **`#Hom(V, ℤ/ℓ) = #V`** for a finite `ℤ/ℓ`-vector space `V`. -/
theorem natCard_addMonoidHom_zmod {ℓ : ℕ} [Fact ℓ.Prime] (V : Type*) [AddCommGroup V]
    [Module (ZMod ℓ) V] [Finite V] : Nat.card (V →+ ZMod ℓ) = Nat.card V := by
  have hp : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hp.ne_zero⟩
  have : Module.Finite (ZMod ℓ) V := Module.Finite.of_finite
  rw [Nat.card_congr (AddMonoidHom.toZModLinearMapEquiv ℓ).toEquiv]
  change Nat.card (Module.Dual (ZMod ℓ) V) = Nat.card V
  rw [Module.natCard_eq_pow_finrank (K := ZMod ℓ) (V := Module.Dual (ZMod ℓ) V),
    Module.natCard_eq_pow_finrank (K := ZMod ℓ) (V := V), Subspace.dual_finrank_eq]

/-- A type with `ℓ` elements, `ℓ` prime, is finite. -/
private theorem finite_of_natCard_eq_prime {ℓ : ℕ} [Fact ℓ.Prime] {α : Type*}
    (h : Nat.card α = ℓ) : Finite α :=
  Nat.finite_of_card_ne_zero (by rw [h]; exact (Fact.out : ℓ.Prime).ne_zero)

/-- A bilinear pairing `A × B → ℤ/ℓ` with `#B ≤ #A` whose left kernel is trivial is perfect. -/
private theorem bijective_of_eq_zero_of_natCard_le {ℓ : ℕ} [Fact ℓ.Prime] {A B : Type*}
    [AddCommGroup A] [AddCommGroup B] [Module (ZMod ℓ) B] [Finite B] (φ : A →+ (B →+ ZMod ℓ))
    (hcard : Nat.card B ≤ Nat.card A) (h : ∀ x, φ x = 0 → x = 0) : Function.Bijective φ := by
  have := FunLike.finite (B →+ ZMod ℓ)
  refine Function.Injective.bijective_of_nat_card_le ?_ (by rwa [natCard_addMonoidHom_zmod])
  exact (injective_iff_map_eq_zero φ).2 h

/-- On a connected scheme, every element of `Ext⁰(ℤ/ℓ_X, ℤ/ℓ_X)` is a scalar multiple of the
identity. -/
theorem exists_eq_smul_mk₀_id_unitSheaf {X : Scheme.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
    [ConnectedSpace X] (x : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 0) :
    ∃ c : ZMod ℓ, x = c • Ext.mk₀ (𝟙 (unitSheaf (X := X) ℓ)) := by
  have hp : ℓ.Prime := Fact.out
  have hcard := natCard_end_unitSheaf (X := X) ℓ
  have : Finite (unitSheaf (X := X) ℓ ⟶ unitSheaf ℓ) := finite_of_natCard_eq_prime hcard
  have hid : 𝟙 (unitSheaf (X := X) ℓ) ≠ 0 := by
    intro hz
    have : Subsingleton (unitSheaf (X := X) ℓ ⟶ unitSheaf ℓ) := ⟨fun g g' => by
      rw [← Category.comp_id g, ← Category.comp_id g', hz, comp_zero, comp_zero]⟩
    exact hp.one_lt.ne (Nat.card_unique.symm.trans hcard)
  have hinj : Function.Injective (fun c : ZMod ℓ => c • 𝟙 (unitSheaf (X := X) ℓ)) := by
    intro c c' hcc
    by_contra hne
    apply hid
    have h1 : (c - c') • 𝟙 (unitSheaf (X := X) ℓ) = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.2 hcc
    simpa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hne)] using
      congrArg (fun g => (c - c')⁻¹ • g) h1
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective (unitSheaf (X := X) ℓ) (unitSheaf (X := X) ℓ)).2 x
  obtain ⟨c, rfl⟩ := (hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_zmod])).2 g
  exact ⟨c, Ext.mk₀_smul c (𝟙 (unitSheaf (X := X) ℓ))⟩

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsProper f] {ℓ : ℕ} [Fact ℓ.Prime]

include f in
/-- For a smooth proper curve `X` over an algebraically closed field `k` and a prime `ℓ`
invertible in `k`, `Ext²(ℤ/ℓ_X, ℤ/ℓ_X)` has exactly `ℓ` elements. -/
theorem natCard_ext_two_unitSheaf (hℓ : IsUnit (ℓ : k)) :
    Nat.card (Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 2) = ℓ :=
  Stacks.Kummer.natCard_ext_two_constantModuleSheaf_of_smoothProperCurve f hℓ
    (fun L hL => Stacks.Picard.exists_nsmul_eq_of_picardDegree_eq_zero f _ hℓ L hL)

include f in
/-- For a smooth proper curve `X` over an algebraically closed field `k` and a prime `ℓ`
invertible in `k`, `Ext¹(ℤ/ℓ_X, ℤ/ℓ_X)` is finite. -/
theorem finite_ext_one_unitSheaf' (hℓ : IsUnit (ℓ : k)) :
    Finite (Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 1) := by
  have key : ∀ N : ℕ, N = ℓ ^ 1 → Finite (Ext (unitSheaf (X := X) N) (unitSheaf N) 1) := by
    rintro N rfl
    exact Stacks.Picard.finite_ext_one_unitSheaf f hℓ 1
  exact key ℓ (pow_one ℓ).symm

include f in
/-- For a smooth proper curve `X` over an algebraically closed field `k`, a prime `ℓ` invertible in
`k` and an additive bijection `t : H²(X, ℤ/ℓ) → ℤ/ℓ`, the pairing `(x, y) ↦ t (x ∘ y)` on
`Ext¹(ℤ/ℓ, ℤ/ℓ) × Ext¹(ℤ/ℓ, ℤ/ℓ)` is perfect. -/
theorem bijective_dualityPairing_unitSheaf_one_one (hℓ : IsUnit (ℓ : k))
    (t : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 2 →+ ZMod ℓ) (htb : Function.Bijective t) :
    Function.Bijective (Ext.dualityPairing (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 2 t
      (unitSheaf ℓ) (show 1 + 1 = 2 from rfl)) := by
  have := finite_ext_one_unitSheaf' f hℓ
  refine bijective_of_eq_zero_of_natCard_le _ le_rfl fun x hx => ?_
  by_contra hne
  obtain ⟨δ, hδ⟩ : ∃ δ : Module.Dual (ZMod ℓ) (Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 1),
      δ x ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hne ((Module.forall_dual_apply_eq_zero_iff (ZMod ℓ) x).1 hall)
  let te := AddEquiv.ofBijective t htb
  let χ : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 1 →+
      Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 2 := te.symm.toAddMonoidHom.comp δ.toAddMonoidHom
  obtain ⟨a, ha⟩ := (bijective_bilinearComp_flip f hℓ).2 χ
  have h1 : x.comp a (by norm_num : 1 + 1 = 2) = χ x := DFunLike.congr_fun ha x
  have hxa := DFunLike.congr_fun hx a
  rw [Ext.dualityPairing_apply, AddMonoidHom.zero_apply, h1] at hxa
  exact hδ (by simpa [χ, te] using hxa)

include f in
/-- **Poincaré duality for `ℤ/ℓ` on a smooth proper curve**, in all degrees: for any additive
injection `t : H²(X, ℤ/ℓ) → ℤ/ℓ` (an isomorphism, by counting), the pairing
`(x, y) ↦ t (x ∘ y)` on `Ext^i(ℤ/ℓ, ℤ/ℓ) × Ext^{2-i}(ℤ/ℓ, ℤ/ℓ)` is perfect. -/
@[sga "4½ Arcata 6.1" "special case", sga "4½ Arcata 6.3.1" "special case"]
theorem isDualityPerfect_unitSheaf (hℓ : IsUnit (ℓ : k))
    (t : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 2 →+ ZMod ℓ) (ht : Function.Injective t) :
    Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 2 t (unitSheaf ℓ) := by
  have hp : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hp.ne_zero⟩
  have : IsIntegral X := IsCurve.toIsVariety.toIsIntegral (k := k) (f := f)
  have h2 := natCard_ext_two_unitSheaf f hℓ
  have : Finite (Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 2) := finite_of_natCard_eq_prime h2
  have h0 : Nat.card (Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 0) = ℓ :=
    (Nat.card_congr (Ext.homEquiv₀ (X := unitSheaf (X := X) ℓ) (Y := unitSheaf ℓ))).trans
      (natCard_end_unitSheaf (X := X) ℓ)
  have : Finite (Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) 0) := finite_of_natCard_eq_prime h0
  have htb : Function.Bijective t := ht.bijective_of_nat_card_le (by rw [h2, Nat.card_zmod])
  intro i j h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :
      (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 1) ∨ (i = 2 ∧ j = 0) := by omega
  · -- degree `(0, 2)`
    refine bijective_of_eq_zero_of_natCard_le _ (h2.trans_le h0.ge) fun x hx => ?_
    -- every class of degree zero is a scalar
    obtain ⟨c, rfl⟩ := exists_eq_smul_mk₀_id_unitSheaf x
    obtain ⟨y, hy⟩ := htb.2 1
    have := DFunLike.congr_fun hx y
    rw [Ext.dualityPairing_apply, AddMonoidHom.zero_apply, Ext.smul_comp, Ext.mk₀_id_comp,
      ← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, map_nsmul, hy, nsmul_eq_mul, mul_one,
      ZMod.natCast_zmod_val] at this
    rw [this, zero_smul]
  · -- degree `(1, 1)`
    exact bijective_dualityPairing_unitSheaf_one_one f hℓ t htb
  · -- degree `(2, 0)`
    refine bijective_of_eq_zero_of_natCard_le _ (h0.trans_le h2.ge) fun x hx => ?_
    have := DFunLike.congr_fun hx (Ext.mk₀ (𝟙 (unitSheaf (X := X) ℓ)))
    rw [Ext.dualityPairing_apply, AddMonoidHom.zero_apply, Ext.comp_mk₀_id] at this
    exact ht (this.trans (map_zero t).symm)

end Stacks.EtaleCohomology.ExtensionTorsor
