module

public import StacksFrontier.Algebra.Homology.CupProductBoundaryDelta

/-!
# The lift of a cocycle is never unique, and the cochain over its differential moves with it

`Stacks.CupProduct.liftCycles_homologyπ_eq_of_lift` says that the cohomology *class* of a
cochain `x₁` lying over `d(x₂)` does not depend on the lift `x₂` of a cocycle `x₃`, nor on the
choice of `x₁` over it.  That statement would be uninteresting if the data it quantifies over
were rigid: if `x₂` determined `x₁`, there would be nothing for the class to be independent
*of*.  This file shows the data is genuinely free.

Given one lift `x₂` of `x₃` along `S.g` and an arbitrary cochain `u` of `S.X₁` in the same
degree, `x₂ + u ≫ S.f` is another lift of the same `x₃` — because `S.f ≫ S.g = 0` — and
`x₁ + u ≫ d` lies over its differential.  So the pairs `(lift, cochain over its differential)`
form an orbit under translation by the cochains of `S.X₁`, and two members of that orbit differ,
at the level of cochains, by `u ≫ d`, which is nonzero as soon as `u` is not a cocycle.

The two classes nevertheless agree, by `Stacks.CupProduct.liftCycles_homologyπ_eq_of_lift`.
Taken together: the class-level conclusion of that theorem is exactly the sharp one, and the
cochain-level statement it might be mistaken for is false.

Neither lemma uses short exactness; they are identities in the short complex `S` alone.

## Main results

* `Stacks.CupProduct.comp_g_f_of_add_comp_f_f`: translating a lift by a cochain of `S.X₁` gives
  another lift of the same cocycle.
* `Stacks.CupProduct.comp_f_f_of_add_comp_d`: the cochain over the differential translates by
  `u ≫ d` along with it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

universe v₁ u₁

namespace Stacks.CupProduct

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] (S : ShortComplex (CochainComplex C ℤ))

/-- **Translating a lift by a cochain of `S.X₁` gives another lift of the same cocycle.**  If
`x₂` lifts `x₃` along `S.g`, then so does `x₂ + u ≫ S.f` for every cochain `u` of `S.X₁` in the
same degree, because `S.f ≫ S.g = 0`.  A lift of a cocycle is therefore never unique unless the
cochains of `S.X₁` in that degree vanish. -/
theorem comp_g_f_of_add_comp_f_f (n : ℤ) {P : C} {x₃ : P ⟶ S.X₃.X n} (x₂ : P ⟶ S.X₂.X n)
    (hx₂ : x₂ ≫ S.g.f n = x₃) (u : P ⟶ S.X₁.X n) :
    (x₂ + u ≫ S.f.f n) ≫ S.g.f n = x₃ := by
  rw [Preadditive.add_comp, hx₂, Category.assoc, ← HomologicalComplex.comp_f, S.zero]
  simp

/-- **The cochain over the differential translates with the lift.**  If `x₁` lies over `d(x₂)`
along `S.f`, then `x₁ + u ≫ d` lies over `d(x₂ + u ≫ S.f)`, by the commutation of `S.f` with the
differentials.  So the cochain `x₁` is determined by the lift only up to `u ≫ d`; it is the
cohomology class that is well defined, which is
`Stacks.CupProduct.liftCycles_homologyπ_eq_of_lift`. -/
theorem comp_f_f_of_add_comp_d (n : ℤ) {P : C} (x₂ : P ⟶ S.X₂.X n) (x₁ : P ⟶ S.X₁.X (n + 1))
    (hx₁ : x₁ ≫ S.f.f (n + 1) = x₂ ≫ S.X₂.d n (n + 1)) (u : P ⟶ S.X₁.X n) :
    (x₁ + u ≫ S.X₁.d n (n + 1)) ≫ S.f.f (n + 1) =
      (x₂ + u ≫ S.f.f n) ≫ S.X₂.d n (n + 1) := by
  rw [Preadditive.add_comp, Preadditive.add_comp, hx₁, Category.assoc, Category.assoc,
    S.f.comm n (n + 1)]

end Stacks.CupProduct

end
