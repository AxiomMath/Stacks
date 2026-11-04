module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CupProductRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveCupProductLevel

/-!
# A criterion for restriction of `H^*(-, ℤ/ℓ)` to be bijective

Let `i : Z_s ⟶ W` and `h : Z_t ⟶ W` be morphisms of schemes and `ℓ` a prime, and write
`Hᵠ(-) = Ext^q(ℤ/ℓ, ℤ/ℓ)` for étale cohomology with coefficients `ℤ/ℓ`. Suppose restriction along
`i` is bijective in every degree. Then restriction along `h` is bijective in every degree as soon
as

* `Z_s` and `Z_t` are nonempty and connected (degree `0`);
* `Hᵠ(Z_s)` and `Hᵠ(Z_t)` vanish for `q ≥ 3`;
* `H²(Z_s)` and `H²(Z_t)` have `ℓ` elements and some class of `H²(W)` restricts to a nonzero
  class on `Z_t`;
* `H¹(Z_s)` and `H¹(Z_t)` are finite of the same order, and the cup product is nondegenerate on
  `H¹(Z_s)`: for every nonzero `b` there is an `x` with `x ∪ b ≠ 0`.

This is the cohomological core of the specialization argument for a smooth proper family of curves
over a strictly henselian base: `i` is the inclusion of the closed geometric fibre (proper base
change), `h` that of another geometric fibre.

In degree one restriction along `h` is injective because a nonzero class `b` of `H¹(W)` has a
partner `x` with `x ∪ b ≠ 0` (nondegeneracy on `Z_s`, transported along `i`), restriction along
`h` is injective in degree two, and restriction is multiplicative; it is then bijective by
counting.

## Main results

* `Stacks.EtaleCohomology.CurveFamily.bijective_constantExtRestriction_of_curves`.
* `Stacks.EtaleCohomology.CurveFamily.bijective_constantExtRestriction_of_points`: the analogue
  when `H^q(Z_s)` and `H^q(Z_t)` vanish for `q ≥ 1`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.CurveFamily

/-- **An additive map between groups of prime order which is nonzero somewhere is bijective.** -/
theorem bijective_of_natCard_eq_prime {ℓ : ℕ} (hℓ : ℓ.Prime) {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] (hA : Nat.card A = ℓ) (hB : Nat.card B = ℓ) (f : A →+ B) {a : A}
    (ha : f a ≠ 0) : Function.Bijective f := by
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; exact hℓ.ne_zero)
  have : Finite B := Nat.finite_of_card_ne_zero (by rw [hB]; exact hℓ.ne_zero)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    -- the kernel is a subgroup of a group of prime order not containing `a`
    have hcard := AddSubgroup.card_addSubgroup_dvd_card f.ker
    rw [hA] at hcard
    rcases (Nat.dvd_prime hℓ).1 hcard with h1 | hℓ'
    · exact (AddSubgroup.eq_bot_of_card_eq _ h1).le hx
    · have htop : f.ker = ⊤ := AddSubgroup.eq_top_of_card_eq _ (hℓ'.trans hA.symm)
      exact absurd (htop ▸ AddSubgroup.mem_top a : a ∈ f.ker) ha
  exact hinj.bijective_of_nat_card_le (hB.trans hA.symm).le

variable (ℓ : ℕ) [Fact ℓ.Prime] {W Zs Zt : Scheme.{u}} (i : Zs ⟶ W) (h : Zt ⟶ W)

/-- `Hᵠ(X, ℤ/ℓ) = Ext^q(ℤ/ℓ_X, ℤ/ℓ_X)`. -/
abbrev H (X : Scheme.{u}) (q : ℕ) : Type (u + 1) :=
  Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod ℓ) X.smallEtaleTopology)
    (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod ℓ) X.smallEtaleTopology) q

omit [Fact ℓ.Prime] in
/-- Restriction maps the unit class of `H⁰` to the unit class. -/
theorem constantExtRestriction_mk₀_id {X Y : Scheme.{u}} (g : Y ⟶ X) :
    constantExtRestriction (ZMod ℓ) g 0 (Ext.mk₀ (𝟙 _)) = Ext.mk₀ (𝟙 _) := by
  rw [constantExtRestriction_apply, Ext.mapExactFunctor_mk₀, CategoryTheory.Functor.map_id,
    Ext.mk₀_comp_mk₀,
    Category.comp_id, Ext.mk₀_comp_mk₀, Iso.hom_inv_id]

/-- The unit class of `H⁰(X, ℤ/ℓ)` is nonzero on a connected, hence nonempty, scheme. -/
theorem mk₀_id_ne_zero (X : Scheme.{u}) [ConnectedSpace X] :
    (Ext.mk₀ (𝟙 _) : H ℓ X 0) ≠ 0 := by
  intro h0
  have hcard := Stacks.EtaleCohomology.LevelChange.natCard_ext_zero_unitSheaf (Y := X) ℓ
  have hid : (𝟙 (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod ℓ)
      X.smallEtaleTopology)) = 0 := by
    apply (Ext.mk₀_bijective _ _).1
    rw [h0, Ext.mk₀_zero]
  have hsub : Subsingleton (H ℓ X 0) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ _).2 a
    obtain ⟨b, rfl⟩ := (Ext.mk₀_bijective _ _).2 b
    rw [← Category.comp_id a, ← Category.comp_id b, hid, comp_zero, comp_zero]
  have : Nat.card (H ℓ X 0) = 1 := Nat.card_unique
  rw [this] at hcard
  exact (Fact.out : ℓ.Prime).one_lt.ne hcard

/-- **Degree zero**: restriction to a connected scheme is bijective on `H⁰(-, ℤ/ℓ)` as soon as the
source `H⁰` has `ℓ` elements. -/
theorem bijective_constantExtRestriction_zero [ConnectedSpace Zt] (hW : Nat.card (H ℓ W 0) = ℓ) :
    Function.Bijective (constantExtRestriction (ZMod ℓ) h 0) := by
  refine bijective_of_natCard_eq_prime (Fact.out : ℓ.Prime) hW
    (Stacks.EtaleCohomology.LevelChange.natCard_ext_zero_unitSheaf ℓ) _ (a := Ext.mk₀ (𝟙 _)) ?_
  rw [constantExtRestriction_mk₀_id]
  exact mk₀_id_ne_zero ℓ Zt

variable {ℓ i h}

/-- Restriction is bijective in a degree where both `H` groups are trivial and `H(W)` is
too. -/
private theorem bijective_restriction_of_subsingleton {q : ℕ}
    (hi : Function.Bijective (constantExtRestriction (ZMod ℓ) i q))
    [Subsingleton (H ℓ Zs q)] [Subsingleton (H ℓ Zt q)] :
    Function.Bijective (constantExtRestriction (ZMod ℓ) h q) := by
  have : Subsingleton (H ℓ W q) := (Equiv.ofBijective _ hi).subsingleton
  exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

/-- If restriction along `i` is bijective in degree `0` and `Zs` is connected, `H⁰(W)` has `ℓ`
elements. -/
private theorem natCard_H_zero_of_bijective [ConnectedSpace Zs]
    (hi : Function.Bijective (constantExtRestriction (ZMod ℓ) i 0)) :
    Nat.card (H ℓ W 0) = ℓ :=
  (Nat.card_congr (Equiv.ofBijective _ hi)).trans
    (Stacks.EtaleCohomology.LevelChange.natCard_ext_zero_unitSheaf (Y := Zs) ℓ)

/-- **The criterion, for curves.** -/
theorem bijective_constantExtRestriction_of_curves
    [ConnectedSpace Zs] [ConnectedSpace Zt]
    (hi : ∀ q, Function.Bijective (constantExtRestriction (ZMod ℓ) i q))
    (hs3 : ∀ q, 3 ≤ q → Subsingleton (H ℓ Zs q)) (ht3 : ∀ q, 3 ≤ q → Subsingleton (H ℓ Zt q))
    (hs2 : Nat.card (H ℓ Zs 2) = ℓ) (ht2 : Nat.card (H ℓ Zt 2) = ℓ)
    (hc : ∃ c : H ℓ W 2, constantExtRestriction (ZMod ℓ) h 2 c ≠ 0)
    [Finite (H ℓ Zs 1)] (h1 : Nat.card (H ℓ Zs 1) = Nat.card (H ℓ Zt 1))
    (hpair : ∀ b : H ℓ Zs 1, b ≠ 0 → ∃ x : H ℓ Zs 1, x.comp b (by norm_num : 1 + 1 = 2) ≠ 0)
    (q : ℕ) : Function.Bijective (constantExtRestriction (ZMod ℓ) h q) := by
  have hℓ : ℓ.Prime := Fact.out
  have hW2 : Nat.card (H ℓ W 2) = ℓ := (Nat.card_congr (Equiv.ofBijective _ (hi 2))).trans hs2
  -- degree two
  have hb2 : Function.Bijective (constantExtRestriction (ZMod ℓ) h 2) := by
    obtain ⟨c, hc⟩ := hc
    exact bijective_of_natCard_eq_prime hℓ hW2 ht2 _ hc
  match q with
  | 0 => exact bijective_constantExtRestriction_zero ℓ h (natCard_H_zero_of_bijective (hi 0))
  | 2 => exact hb2
  | 1 =>
    -- injectivity through the cup product
    have hinj : Function.Injective (constantExtRestriction (ZMod ℓ) h 1) := by
      rw [injective_iff_map_eq_zero]
      intro b hb
      by_contra hne
      have hib : constantExtRestriction (ZMod ℓ) i 1 b ≠ 0 := by
        rw [Ne, ← map_zero (constantExtRestriction (ZMod ℓ) i 1)]
        exact fun h' => hne ((hi 1).1 h')
      obtain ⟨x', hx'⟩ := hpair _ hib
      obtain ⟨x, rfl⟩ := (hi 1).2 x'
      rw [← constantExtRestriction_comp] at hx'
      have hxb : x.comp b (by norm_num : 1 + 1 = 2) ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hx'
        exact hx' rfl
      have := (map_ne_zero_iff _ hb2.1).2 hxb
      rw [constantExtRestriction_comp, hb, Ext.comp_zero] at this
      exact this rfl
    have : Finite (H ℓ W 1) := Finite.of_equiv _ (Equiv.ofBijective _ (hi 1)).symm
    have : Finite (H ℓ Zt 1) := Nat.finite_of_card_ne_zero (by
      rw [← h1]
      exact Nat.card_pos.ne')
    have hcard : Nat.card (H ℓ Zt 1) ≤ Nat.card (H ℓ W 1) := by
      rw [← h1, Nat.card_congr (Equiv.ofBijective _ (hi 1))]
    exact hinj.bijective_of_nat_card_le hcard
  | q + 3 =>
    have := hs3 (q + 3) (by omega)
    have := ht3 (q + 3) (by omega)
    exact bijective_restriction_of_subsingleton (hi (q + 3))

/-- **The criterion, for points**: when `Hᵠ(Z_s)` and `Hᵠ(Z_t)` vanish in positive degrees. -/
theorem bijective_constantExtRestriction_of_points
    [ConnectedSpace Zs] [ConnectedSpace Zt]
    (hi : ∀ q, Function.Bijective (constantExtRestriction (ZMod ℓ) i q))
    (hs : ∀ q, 0 < q → Subsingleton (H ℓ Zs q)) (ht : ∀ q, 0 < q → Subsingleton (H ℓ Zt q))
    (q : ℕ) : Function.Bijective (constantExtRestriction (ZMod ℓ) h q) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact bijective_constantExtRestriction_zero ℓ h (natCard_H_zero_of_bijective (hi 0))
  · have := hs q hq
    have := ht q hq
    exact bijective_restriction_of_subsingleton (hi q)

end Stacks.EtaleCohomology.CurveFamily

end
