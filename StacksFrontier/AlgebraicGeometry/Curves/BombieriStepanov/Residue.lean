module

public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.Local
public import StacksFrontier.AlgebraicGeometry.FieldToResidue

/-!
# Residues at the places of a curve

Let `X` be an integral scheme over a field `k`. Its function field is a `k`-algebra through the
structure morphism. At a point `x` whose local ring is a discrete valuation ring, the residue map
`𝒪_{X,x} → κ(x)` reads the valuation `ord_x` as follows.

* If `k → κ(x)` is onto, the place is residue-rational in the sense of
  `Stacks.BombieriStepanov.IsResidueRational`. Two functions of the same order differ, up to a
  constant multiple, by a function of larger order.
* If every element of `κ(x)` satisfies `c ^ Q = c`, then `y ≡ y ^ Q` modulo the maximal ideal for
  every `y` regular at `x`. This applies when `κ(x)` is finite of order dividing a power of `Q`.

## Main definitions

* `Stacks.BombieriStepanov.functionFieldAlgebra`: the `k`-algebra structure of `R(X)`.

## Main results

* `Stacks.BombieriStepanov.algebraMap_functionFieldAlgebra`: the constants of `R(X)` are the images
  of the constants of every local ring.
* `Stacks.BombieriStepanov.isResidueRational_schemeVal`
* `Stacks.BombieriStepanov.one_le_schemeVal_sub_pow`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace Stacks.BombieriStepanov

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k))

/-- The `k`-algebra structure of the function field given by the structure morphism. -/
abbrev functionFieldAlgebra : Algebra k X.functionField :=
  (fieldToStalk p (genericPoint X)).hom.toAlgebra

/-- The constants of `R(X)` are the images of the constants of the local ring at any point. -/
theorem algebraMap_functionFieldAlgebra (x : X) (c : k) :
    @algebraMap k X.functionField _ _ (functionFieldAlgebra p) c =
      algebraMap (X.presheaf.stalk x) X.functionField ((fieldToStalk p x).hom c) := by
  rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
  change (fieldToStalk p (genericPoint X)).hom c =
    ((fieldToStalk p x) ≫ X.presheaf.stalkSpecializes _).hom c
  have h : X.presheaf.germ ⊤ x trivial ≫
      X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) =
      X.presheaf.germ ⊤ (genericPoint X) trivial :=
    X.presheaf.germ_stalkSpecializes _ _
  rw [fieldToStalk, fieldToStalk, Category.assoc, Category.assoc, h]

variable [IsLocallyNoetherian X] {x : X} (hx : coheight x = 1)
  [IsDiscreteValuationRing (X.presheaf.stalk x)]

include hx in
/-- **A place with residue field `k` is residue-rational.** If `k → κ(x)` is onto, two nonzero
functions of the same order at `x` differ by a unit `u`. A constant `c` has the same residue as
`u`, so `f - c g = (u - c) g` has larger order. -/
theorem isResidueRational_schemeVal
    (hsurj : Function.Surjective fun c : k =>
      IsLocalRing.residue (X.presheaf.stalk x) ((fieldToStalk p x).hom c)) :
    letI := functionFieldAlgebra p
    IsResidueRational (k := k) (schemeVal x) := by
  let := functionFieldAlgebra p
  intro f g hf hg hfg
  rw [schemeVal_apply x hf, schemeVal_apply x hg] at hfg
  obtain ⟨u, hu⟩ := exists_unit_mul_eq_of_ord_eq hx hf hg (WithTop.coe_injective hfg)
  obtain ⟨c, hc⟩ := hsurj (IsLocalRing.residue _ (u : X.presheaf.stalk x))
  have hc' : IsLocalRing.residue (X.presheaf.stalk x) ((fieldToStalk p x).hom c) =
      IsLocalRing.residue _ (u : X.presheaf.stalk x) := hc
  refine ⟨c, ?_⟩
  set d : X.presheaf.stalk x := (u : X.presheaf.stalk x) - (fieldToStalk p x).hom c with hd
  have hdm : d ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [← IsLocalRing.residue_eq_zero_iff, hd, map_sub, hc', sub_self]
  have heq : f - algebraMap k X.functionField c * g =
      algebraMap (X.presheaf.stalk x) X.functionField d * g := by
    rw [← hu, algebraMap_functionFieldAlgebra p x c, hd, map_sub]
    ring
  rw [heq, schemeVal_apply x hf]
  rcases eq_or_ne d 0 with hd0 | hd0
  · rw [hd0, map_zero, zero_mul, AddValuation.map_zero]
    exact WithTop.coe_lt_top _
  have hd0' : algebraMap (X.presheaf.stalk x) X.functionField d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hd0
  rw [schemeVal_apply x (mul_ne_zero hd0' hg), Scheme.ord_mul hd0' hg]
  have h1 := one_le_ord_algebraMap hx hd0 hdm
  have h2 := WithTop.coe_injective hfg
  exact WithTop.coe_lt_coe.2 (by omega)

include hx in
/-- **The Frobenius congruence at a place.** If every element of the residue field satisfies
`c ^ Q = c`, then `y ≡ y ^ Q` modulo the maximal ideal for every `y` regular at `x`. -/
theorem one_le_schemeVal_sub_pow (Q : ℕ)
    (hQ : ∀ c : IsLocalRing.ResidueField (X.presheaf.stalk x), c ^ Q = c) {y : X.functionField}
    (hy : 0 ≤ schemeVal x y) : ((1 : ℤ) : WithTop ℤ) ≤ schemeVal x (y - y ^ Q) := by
  have hQ0 : Q ≠ 0 := by
    intro h0
    have := hQ 0
    rw [h0, pow_zero] at this
    exact one_ne_zero this
  have hord : 0 ≤ X.ord y x := by
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    · rw [schemeVal_apply x hy0] at hy
      exact_mod_cast hy
  obtain ⟨a, rfl⟩ := exists_algebraMap_eq_of_ord_nonneg hx hord
  rw [← map_pow, ← map_sub]
  rcases eq_or_ne (a - a ^ Q) 0 with h0 | h0
  · rw [h0, map_zero, AddValuation.map_zero]
    exact le_top
  have h0' : algebraMap (X.presheaf.stalk x) X.functionField (a - a ^ Q) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 h0
  rw [schemeVal_apply x h0']
  refine WithTop.coe_le_coe.2 (one_le_ord_algebraMap hx h0 ?_)
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, hQ, sub_self]

end Stacks.BombieriStepanov

end
