module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal

/-!
# Finitely many effective Cartier divisors are simultaneously principal

An effective Cartier divisor is cut out by a nonzerodivisor on some affine open neighbourhood of
any point, which is `Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor`.
This file makes that simultaneous in two ways at once: for *finitely many* divisors, and *inside a
prescribed affine open*. Both are needed to read a local structure off several ideal sheaves at
one point, as Stacks tag 0ESU does with the Fitting ideals of a module after its blowup — there
the bound past which the Fitting ideals are the unit ideal is found on one affine open, and the
local equations must then be found on a smaller one.

## Main results

* `Stacks.Divisors.isRegular_restrict_of_le`: a nonzerodivisor restricts to a nonzerodivisor along
  an inclusion of affine opens.
* `Stacks.Divisors.exists_affineOpen_le_forall_ideal_eq_span`: **finitely many effective Cartier
  divisors are cut out by nonzerodivisors on a common affine open neighbourhood of any point,
  inside any prescribed affine open neighbourhood of it.**

## Implementation notes

Shrinking an affine open preserves the two things that matter. The ideal cut out on the smaller
affine open is the image of the one cut out on the larger, which is
`AlgebraicGeometry.Scheme.IdealSheafData.map_ideal`, so a principal ideal stays principal with the
restricted generator. And the restriction map between affine opens is *flat*, because it is the
map on sections of the identity, which is an open immersion; multiplication by a nonzerodivisor
stays injective after a flat base change, so the restricted generator is still a nonzerodivisor.
Flatness is what makes an arbitrary affine open inside the intersection usable, with no need for
the shrinking to go through standard opens.

## References

* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 0ESU](https://stacks.math.columbia.edu/tag/0ESU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-- **A nonzerodivisor restricts to a nonzerodivisor between affine opens.** The restriction map
`Γ(X, W) → Γ(X, A)` of an inclusion `A ≤ W` of affine opens is the map on sections of the
identity of `X`, which is an open immersion and so flat; multiplication by a nonzerodivisor stays
injective after a flat base change. -/
theorem isRegular_restrict_of_le {A W : X.affineOpens} (hAW : A ≤ W) {b : Γ(X, W.1)}
    (hb : IsRegular b) :
    IsRegular ((X.presheaf.map (homOfLE (show A.1 ≤ W.1 from hAW)).op).hom b) := by
  let : Algebra Γ(X, W.1) Γ(X, A.1) :=
    (X.presheaf.map (homOfLE (show A.1 ≤ W.1 from hAW)).op).hom.toAlgebra
  have he : A.1 ≤ (𝟙 X) ⁻¹ᵁ W.1 := show A.1 ≤ W.1 from hAW
  have heq : (Scheme.Hom.appLE (𝟙 X) W.1 A.1 he).hom =
      (X.presheaf.map (homOfLE (show A.1 ≤ W.1 from hAW)).op).hom := rfl
  have hflat : Module.Flat Γ(X, W.1) Γ(X, A.1) := by
    rw [← RingHom.flat_algebraMap_iff, RingHom.algebraMap_toAlgebra, ← heq]
    exact AlgebraicGeometry.Flat.flat_appLE (𝟙 X) W.2 A.2 he
  have hsmul : IsSMulRegular Γ(X, A.1) b := Module.Flat.isSMulRegular_of_isRegular hb
  have hleft : IsLeftRegular
      ((X.presheaf.map (homOfLE (show A.1 ≤ W.1 from hAW)).op).hom b) := by
    intro p r hpr
    refine hsmul ?_
    simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hpr
  exact ⟨hleft, fun p r hpr => hleft (by simpa [mul_comm] using hpr)⟩

/-- A generator of an effective Cartier divisor's ideal that is a nonzerodivisor restricts to one
along an inclusion of affine opens. -/
private theorem regular_and_ideal_eq_span_restrict (C : X.IdealSheafData) {A W : X.affineOpens}
    (hAW : A ≤ W) {b : Γ(X, W.1)} (h : IsRegular b ∧ C.ideal W = Ideal.span {b}) :
    IsRegular ((X.presheaf.map (homOfLE (show A.1 ≤ W.1 from hAW)).op).hom b) ∧
      C.ideal A = Ideal.span {(X.presheaf.map (homOfLE (show A.1 ≤ W.1 from hAW)).op).hom b} := by
  refine ⟨isRegular_restrict_of_le hAW h.1, ?_⟩
  rw [← Scheme.IdealSheafData.map_ideal C hAW, h.2, Ideal.map_span, Set.image_singleton]
  rfl

/-- **Finitely many effective Cartier divisors are simultaneously principal on nonzerodivisors,
inside a prescribed affine open.** Each is cut out by a nonzerodivisor on some affine open
neighbourhood of the point; an affine open neighbourhood inside the intersection of those and of
the prescribed open keeps every one of them principal, with the restricted generators, which stay
nonzerodivisors by `Stacks.Divisors.isRegular_restrict_of_le`. -/
theorem exists_affineOpen_le_forall_ideal_eq_span {ι : Type*} (s : Finset ι)
    (C : ι → X.IdealSheafData) (hC : ∀ i ∈ s, IsEffectiveCartierDivisor (C i))
    (W : X.affineOpens) (x : X) (hxW : x ∈ (W.1 : Set X)) :
    ∃ U : X.affineOpens, x ∈ (U.1 : Set X) ∧ U ≤ W ∧
      ∃ f : ι → Γ(X, U.1), ∀ i ∈ s, IsRegular (f i) ∧ (C i).ideal U = Ideal.span {f i} := by
  classical
  induction s using Finset.cons_induction with
  | empty => exact ⟨W, hxW, le_rfl, 0, by simp⟩
  | cons i t hit ih =>
      obtain ⟨W', hxW', hW'W, g, hg⟩ := ih fun j hj => hC j (Finset.mem_cons_of_mem hj)
      obtain ⟨V, hV, hxV, b, hbreg, hb⟩ :=
        exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor (C i)
          (hC i (Finset.mem_cons_self ..)) x
      obtain ⟨-, ⟨A, hA, rfl⟩, hxA, hsub⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open
          (show x ∈ (W'.1 : Set X) ∩ (V : Set X) from ⟨hxW', hxV⟩)
          ((W'.1 : X.Opens).isOpen.inter V.isOpen)
      have hAW' : (⟨A, hA⟩ : X.affineOpens) ≤ W' := fun z hz => (hsub hz).1
      have hAV : (⟨A, hA⟩ : X.affineOpens) ≤ (⟨V, hV⟩ : X.affineOpens) := fun z hz => (hsub hz).2
      refine ⟨⟨A, hA⟩, hxA, hAW'.trans hW'W, Function.update
        (fun j => (X.presheaf.map (homOfLE hAW').op).hom (g j)) i
        ((X.presheaf.map (homOfLE hAV).op).hom b), fun j hj => ?_⟩
      rcases Finset.mem_cons.mp hj with rfl | hjt
      · rw [Function.update_self]
        exact regular_and_ideal_eq_span_restrict _ hAV ⟨hbreg, hb⟩
      · have hji : j ≠ i := fun h => hit (h ▸ hjt)
        rw [Function.update_of_ne hji]
        exact regular_and_ideal_eq_span_restrict _ hAW' (hg j hjt)

end Stacks.Divisors

end
