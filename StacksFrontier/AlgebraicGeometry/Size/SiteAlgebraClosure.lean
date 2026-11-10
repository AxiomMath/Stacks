module

public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.Pullback
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale

/-!
# Closure of the algebras of a big site under symmetric algebras and square-zero extensions

A big site with cutoff `κ` admits the affine scheme `Spec B` exactly when its size is below `κ`.
For a spectrum the size is `max ℵ₀ #B` (`AlgebraicGeometry.Scheme.size_Spec`), so at an
uncountable cutoff the condition is just `#B < κ`. This file records that equivalence and
cardinality bounds for the module `Hom_A(N, D)` with `N` finitely generated, for symmetric
algebras, and for the trivial square-zero extension `C[ε] = C ⊕ C`.

## Main results

* `AlgebraicGeometry.schemeSizeBelow_spec_iff` — `Spec B` is below the cutoff iff `#B` is.
* `Cardinal.mk_linearMap_lt_of_fg` — `#Hom_A(N, D) < κ` for `N` finitely generated and
  `#D < κ`.
* `Cardinal.mk_symmetricAlgebra_le` — `#Sym_C(W) ≤ max (max #C #W) ℵ₀`.
* `Cardinal.mk_trivSqZeroExt_lt` — `C ⊕ V` with `#C, #V < κ` is below `κ`.
* `AlgebraicGeometry.schemeSizeBelow_spec_symmetricAlgebra`,
  `AlgebraicGeometry.schemeSizeBelow_spec_trivSqZeroExt` — the corresponding algebras of the
  site.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open Cardinal

universe u

namespace Cardinal

/-- **The module of linear maps out of a finitely generated module is small.** For `N` a
finitely generated `A`-module and `#D < κ` with `κ` uncountable, `#Hom_A(N, D) < κ`. -/
public theorem mk_linearMap_lt_of_fg {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) {A : Type u} [CommRing A]
    {N : Type u} [AddCommGroup N] [Module A N] [Module.Finite A N]
    {D : Type u} [AddCommGroup D] [Module A D] (hD : #D < κ) : #(N →ₗ[A] D) < κ := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := N)
  have hinj : Function.Injective fun f : N →ₗ[A] D => fun i => f (s i) :=
    fun _ _ h => LinearMap.ext_on_range hs (congrFun h)
  refine (mk_le_of_injective hinj).trans_lt ?_
  rw [show #(Fin n → D) = #D ^ n by simp]
  rcases lt_or_ge #D ℵ₀ with h | h
  · exact (power_lt_aleph0 h natCast_lt_aleph0).trans hκ
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using one_lt_aleph0.trans hκ
    · exact (power_nat_le h).trans_lt hD

/-- **The symmetric algebra is no larger than its generators.** `#Sym_C(W) ≤ max (max #C #W) ℵ₀`. -/
public theorem mk_symmetricAlgebra_le (C : Type u) [CommRing C] (W : Type u) [AddCommGroup W]
    [Module C W] : #(SymmetricAlgebra C W) ≤ max (max #C #W) ℵ₀ := by
  have hsurj : Function.Surjective
      (MvPolynomial.aeval (R := C) fun w : W => SymmetricAlgebra.ι C W w) := by
    intro a
    induction a using SymmetricAlgebra.induction with
    | algebraMap r => exact ⟨MvPolynomial.C r, by simp⟩
    | ι x => exact ⟨MvPolynomial.X x, by simp⟩
    | mul a b ha hb =>
      obtain ⟨p, rfl⟩ := ha
      obtain ⟨q, rfl⟩ := hb
      exact ⟨p * q, map_mul _ _ _⟩
    | add a b ha hb =>
      obtain ⟨p, rfl⟩ := ha
      obtain ⟨q, rfl⟩ := hb
      exact ⟨p + q, map_add _ _ _⟩
  exact (mk_le_of_surjective hsurj).trans MvPolynomial.cardinalMk_le_max

/-- **The trivial square-zero extension of small objects is small**: for `κ` uncountable and
`#C, #V < κ`, `#(C ⊕ V) < κ`. -/
public theorem mk_trivSqZeroExt_lt {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) {C : Type u} {V : Type u}
    (hC : #C < κ) (hV : #V < κ) : #(TrivSqZeroExt C V) < κ := by
  change #(C × V) < κ
  rw [mk_prod, lift_id, lift_id]
  exact (mul_le_max _ _).trans_lt (max_lt (max_lt hC hV) hκ)

end Cardinal

namespace AlgebraicGeometry

/-- **An affine scheme is below an uncountable cutoff exactly when its ring is**: the size of
`Spec B` is `max ℵ₀ #B`. -/
public theorem schemeSizeBelow_spec_iff {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (B : Type u)
    [CommRing B] : schemeSizeBelow κ (Spec (CommRingCat.of B)) ↔ #B < κ := by
  change (Spec (CommRingCat.of B)).size < κ ↔ _
  rw [Scheme.size_Spec]
  exact ⟨(le_max_right _ _).trans_lt, max_lt hκ⟩

/-- **The symmetric algebra of a small module over an algebra of the site is an algebra of the
site.** -/
public theorem schemeSizeBelow_spec_symmetricAlgebra {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (C : Type u) [CommRing C] (W : Type u) [AddCommGroup W] [Module C W]
    (hC : schemeSizeBelow κ (Spec (CommRingCat.of C))) (hW : #W < κ) :
    schemeSizeBelow κ (Spec (CommRingCat.of (SymmetricAlgebra C W))) :=
  (schemeSizeBelow_spec_iff hκ _).2 ((mk_symmetricAlgebra_le C W).trans_lt
    (max_lt (max_lt ((schemeSizeBelow_spec_iff hκ C).1 hC) hW) hκ))

/-- **The trivial square-zero extension of an algebra of the site by a small module is an algebra
of the site**; in particular so is the ring of dual numbers `C[ε] = TrivSqZeroExt C C`. -/
public theorem schemeSizeBelow_spec_trivSqZeroExt {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (C : Type u) [CommRing C] (V : Type u) [AddCommGroup V] [Module C V] [Module Cᵐᵒᵖ V]
    [IsCentralScalar C V] (hC : schemeSizeBelow κ (Spec (CommRingCat.of C))) (hV : #V < κ) :
    schemeSizeBelow κ (Spec (CommRingCat.of (TrivSqZeroExt C V))) :=
  (schemeSizeBelow_spec_iff hκ _).2
    (mk_trivSqZeroExt_lt hκ ((schemeSizeBelow_spec_iff hκ C).1 hC) hV)

end AlgebraicGeometry

end
