module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.DerivationAlong

/-!
# Cardinality bounds for the constructions of the chart gluing

The gluing of infinitesimal lifts through a formally étale chart takes place among the algebras
of a fixed class `P`. When `P` is the class of algebras of cardinality at most an infinite
cardinal `κ`, membership in `P` of every construction used is a cardinality bound, recorded here:
tensor products, trivial square-zero extensions, subtypes and modules of differentials of
`κ`-small objects are `κ`-small.

## Main results

* `Stacks.ChartGlue.mk_tensorProduct_le`
* `Stacks.ChartGlue.mk_trivExt_le`
* `Stacks.ChartGlue.mk_kaehler_le`
-/

@[expose] public section

open Cardinal TensorProduct

universe u v w

namespace Stacks.ChartGlue

variable {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)

/-- A product of two `κ`-small types is `κ`-small. -/
private theorem mk_prod_le_of_le (hκ : ℵ₀ ≤ κ) {α β : Type u} (hα : #α ≤ κ)
    (hβ : #β ≤ κ) : #(α × β) ≤ κ := by
  rw [mk_prod, lift_id, lift_id]
  exact mul_le_of_le hκ hα hβ

include hκ in
/-- A tensor product of two `κ`-small modules is `κ`-small. -/
theorem mk_tensorProduct_le {R : Type u} [CommSemiring R] {M N : Type u} [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] (hM : #M ≤ κ) (hN : #N ≤ κ) :
    #(M ⊗[R] N) ≤ κ := by
  have hsurj : Function.Surjective
      (AddCon.mk' (addConGen (TensorProduct.Eqv R M N)) : FreeAddMonoid (M × N) → M ⊗[R] N) :=
    AddCon.mk'_surjective
  refine (mk_le_of_surjective hsurj).trans ?_
  have hlist : #(FreeAddMonoid (M × N)) = #(List (M × N)) :=
    Cardinal.mk_congr FreeAddMonoid.toList
  rw [hlist]
  refine (mk_list_le_max _).trans (max_le hκ ?_)
  exact mk_prod_le_of_le hκ hM hN

include hκ in
/-- A trivial square-zero extension of a `κ`-small ring by a `κ`-small module is `κ`-small. -/
theorem mk_trivExt_le {C : Type u} [CommRing C] {N : Type u} [AddCommGroup N] [Module C N]
    (hC : #C ≤ κ) (hN : #N ≤ κ) : #(TrivExt C N) ≤ κ := by
  exact mk_prod_le_of_le hκ hC hN

include hκ in
/-- The module of differentials of a `κ`-small algebra is `κ`-small. -/
theorem mk_kaehler_le {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    (hS : #S ≤ κ) : #(Ω[S⁄R]) ≤ κ := by
  have hsurj := (KaehlerDifferential.ideal R S).toCotangent_surjective
  refine (mk_le_of_surjective hsurj).trans ?_
  exact (mk_subtype_le _).trans (mk_tensorProduct_le hκ hS hS)

end Stacks.ChartGlue

end
