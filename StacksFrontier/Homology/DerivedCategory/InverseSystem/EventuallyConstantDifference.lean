module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.Basic
public import StacksCore.Tactic.StacksAttribute

/-! # The Milnor difference of an eventually constant tower is a split epimorphism

Let `D` be a preadditive category and let `X : ℕ → D` be a tower with transition maps
`f n : X (n + 1) ⟶ X n`. The *Milnor difference* of the tower is the endomorphism

`d = Pi.lift (fun n ↦ π n - π (n + 1) ≫ f n)`

of the product `∏ X`, whose cokernel is the first derived inverse limit `R¹lim X` and whose kernel
is `lim X`. This file proves that `d` is a **split epimorphism**, hence that `R¹lim X` vanishes, as
soon as the transition maps are isomorphisms from some index on.

No condition is imposed on the finitely many transition maps below that index; in contrast,
`DerivedCategory.isDerivedLimit_of_limit_cone_of_epi` asks that *every* transition map be an
epimorphism. A tower arising as `n ↦ H^j(U, τ_{≥ -n}K)` in Stacks 0BKZ has invertible
transitions for `-j ≤ n`, and nothing is known about the remaining ones.

The proof is an induction on the index past which the transitions are invertible, and it is
carried out in a form that mentions no products at all: for an arbitrary object `P` and an
arbitrary family `p n : P ⟶ X n`, the system of equations `g n - g (n + 1) ≫ f n = p n` has a
solution `g`. When every transition is invertible, `g` is built upwards from `g 0 = 0` by
`g (n + 1) = (g n - p n) ≫ (f n)⁻¹`. The inductive step replaces the tower by its shift, which
pushes the index down by one, and recovers the missing bottom value from `g 0 = p 0 + g 1 ≫ f 0`
-- the one direction of the recursion that needs no inverse.

## Main results

* `Stacks.InverseSystem.exists_difference_section`: the solution of the difference equations, with
  no products involved.
* `Stacks.InverseSystem.isSplitEpi_milnorDifference`: the Milnor difference of an eventually
  constant tower is a split epimorphism.
* `Stacks.InverseSystem.isZero_cokernel_milnorDifference`: its cokernel, the first derived inverse
  limit of the tower, is zero.
* `Stacks.InverseSystem.isSplitEpi_milnorDifference_functor`,
  `Stacks.InverseSystem.isZero_cokernel_milnorDifference_functor`: the same for a tower presented
  as a functor out of `ℕᵒᵖ`.

## References

* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
* [Stacks Project, Tag 0BKX](https://stacks.math.columbia.edu/tag/0BKX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.InverseSystem

universe v u

variable {D : Type u} [Category.{v} D] [Preadditive D]

/-- **The difference equations of an eventually constant tower are solvable.** Given a tower
`X` with transition maps `f`, invertible from index `N` on, and an arbitrary family of maps
`p n : P ⟶ X n`, there is a family `g n : P ⟶ X n` with `g n - g (n + 1) ≫ f n = p n` for every
`n`. Nothing is assumed of the transition maps below `N`. -/
theorem exists_difference_section (X : ℕ → D) (f : ∀ n, X (n + 1) ⟶ X n) {P : D}
    (p : ∀ n, P ⟶ X n) (N : ℕ) (hf : ∀ n, N ≤ n → IsIso (f n)) :
    ∃ g : ∀ n, P ⟶ X n, ∀ n, g n - g (n + 1) ≫ f n = p n := by
  induction N generalizing X with
  | zero =>
    have (n : ℕ) : IsIso (f n) := hf n (Nat.zero_le n)
    refine ⟨Nat.rec 0 fun n g => (g - p n) ≫ inv (f n), fun n => ?_⟩
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, sub_sub_cancel]
  | succ N ih =>
    obtain ⟨g, hg⟩ := ih (fun n => X (n + 1)) (fun n => f (n + 1)) (fun n => p (n + 1))
      (fun n hn => hf (n + 1) (by omega))
    refine ⟨Nat.rec (p 0 + g 0 ≫ f 0) fun n _ => g n, fun n => ?_⟩
    cases n with
    | zero => simp
    | succ n => exact hg n

variable (X : ℕ → D) (f : ∀ n, X (n + 1) ⟶ X n) [HasProduct X]

/-- The Milnor difference of a tower: the endomorphism `π n - π (n + 1) ≫ f n` of the product of
the terms, whose kernel is the inverse limit of the tower and whose cokernel is its first derived
inverse limit. -/
def milnorDifference : (∏ᶜ X) ⟶ ∏ᶜ X :=
  Pi.lift fun n => Pi.π X n - Pi.π X (n + 1) ≫ f n

/-- The `n`-th component of the Milnor difference is `π n - π (n + 1) ≫ f n`. -/
@[simp]
lemma milnorDifference_π (n : ℕ) :
    milnorDifference X f ≫ Pi.π X n = Pi.π X n - Pi.π X (n + 1) ≫ f n := by
  simp [milnorDifference]

/-- **The Milnor difference of an eventually constant tower splits.** If the transition maps of the
tower are isomorphisms from index `N` on, then its Milnor difference is a split epimorphism. -/
theorem isSplitEpi_milnorDifference (N : ℕ) (hf : ∀ n, N ≤ n → IsIso (f n)) :
    IsSplitEpi (milnorDifference X f) := by
  obtain ⟨g, hg⟩ := exists_difference_section X f (fun n => Pi.π X n) N hf
  refine IsSplitEpi.mk ⟨Pi.lift g, ?_⟩
  refine Pi.hom_ext _ _ fun n => ?_
  rw [Category.assoc, milnorDifference_π, Category.id_comp, Preadditive.comp_sub,
    ← Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π]
  exact hg n

/-- **The first derived inverse limit of an eventually constant tower vanishes.** -/
theorem isZero_cokernel_milnorDifference (N : ℕ) (hf : ∀ n, N ≤ n → IsIso (f n))
    [HasCokernel (milnorDifference X f)] : IsZero (cokernel (milnorDifference X f)) :=
  have := isSplitEpi_milnorDifference X f N hf
  isZero_cokernel_of_epi (milnorDifference X f)

variable (F : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ => F.obj ⟨n⟩]

/-- **The Milnor difference of an eventually constant tower splits**, for a tower presented as a
functor out of `ℕᵒᵖ`. -/
theorem isSplitEpi_milnorDifference_functor (N : ℕ)
    (hF : ∀ n, N ≤ n → IsIso (F.map (homOfLE (Nat.le_succ n)).op)) :
    IsSplitEpi (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => F.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ => F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op) :=
  isSplitEpi_milnorDifference (fun n : ℕ => F.obj ⟨n⟩)
    (fun n => F.map (homOfLE (Nat.le_succ n)).op) N hF

/-- **The first derived inverse limit of an eventually constant tower vanishes**, for a tower
presented as a functor out of `ℕᵒᵖ`. -/
theorem isZero_cokernel_milnorDifference_functor (N : ℕ)
    (hF : ∀ n, N ≤ n → IsIso (F.map (homOfLE (Nat.le_succ n)).op))
    [HasCokernel (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => F.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ => F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op)] :
    IsZero (cokernel (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => F.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ => F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op)) :=
  have := isSplitEpi_milnorDifference_functor F N hF
  isZero_cokernel_of_epi _

end Stacks.InverseSystem

end
