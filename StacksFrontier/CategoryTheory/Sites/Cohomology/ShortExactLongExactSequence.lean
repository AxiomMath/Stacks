module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The long exact cohomology sequence of a short exact sequence of abelian sheaves

Let `(C, J)` be a site and let `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` be a short exact sequence of sheaves of
abelian groups on it. This file records the long exact sequence of its cohomology groups
`CategoryTheory.Sheaf.H`, in every degree:

`0 → H⁰(F₁) → H⁰(F₂) → H⁰(F₃) → H¹(F₁) → H¹(F₂) → H¹(F₃) → H²(F₁) → ⋯`

## Main definitions and results

* `Stacks.Cohomology.GlobalLongExactSequence.boundary`: the connecting homomorphism
  `Hⁿ(F₃) → Hⁿ⁺¹(F₁)`, composition with the extension class of the sequence.
* `Stacks.Cohomology.GlobalLongExactSequence.exact_map_map`,
  `Stacks.Cohomology.GlobalLongExactSequence.exact_map_boundary` and
  `Stacks.Cohomology.GlobalLongExactSequence.exact_boundary_map`: exactness at the three kinds
  of term.
* `Stacks.Cohomology.GlobalLongExactSequence.injective_map_zero`: the sequence starts with a
  zero, that is, the first map is injective in degree zero.

## References

* [Stacks Project, Tag 0DNM](https://stacks.math.columbia.edu/tag/0DNM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe w' w v u

namespace Stacks.Cohomology.GlobalLongExactSequence

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/-- **The connecting homomorphism of the long exact cohomology sequence.** For a short exact
sequence of sheaves of abelian groups, composition with its extension class raises the degree
by one and lands in the cohomology of the subsheaf. -/
def boundary {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact) (n : ℕ) :
    Sheaf.H.{w'} S.X₃ n →+ Sheaf.H.{w'} S.X₁ (n + 1) :=
  hS.extClass.postcomp
    ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))) rfl

/-- **Exactness at the middle term**: `Hⁿ(F₁) → Hⁿ(F₂) → Hⁿ(F₃)` is exact. -/
theorem exact_map_map {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)
    (n : ℕ) :
    Function.Exact (Sheaf.H.map.{w'} S.f n) (Sheaf.H.map.{w'} S.g n) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp (Ext.covariant_sequence_exact₂' _ hS n)

/-- **Exactness at the quotient term**: `Hⁿ(F₂) → Hⁿ(F₃) → Hⁿ⁺¹(F₁)` is exact, the second map
being the connecting homomorphism. -/
theorem exact_map_boundary {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)
    (n : ℕ) :
    Function.Exact (Sheaf.H.map.{w'} S.g n) (boundary hS n) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Ext.covariant_sequence_exact₃' _ hS n (n + 1) rfl)

/-- **Exactness at the subsheaf term**: `Hⁿ(F₃) → Hⁿ⁺¹(F₁) → Hⁿ⁺¹(F₂)` is exact, the first map
being the connecting homomorphism. -/
theorem exact_boundary_map {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)
    (n : ℕ) :
    Function.Exact (boundary hS n) (Sheaf.H.map.{w'} S.f (n + 1)) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Ext.covariant_sequence_exact₁' _ hS n (n + 1) rfl)

/-- **The long exact sequence begins with a zero.** A monomorphism of sheaves of abelian groups
is injective on degree-zero cohomology. -/
@[sga "4½ Arcata 1.6.5" "partial"]
theorem injective_map_zero {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G) [Mono f] :
    Function.Injective (Sheaf.H.map.{w'} f 0) := by
  intro x y h
  apply (Ext.addEquiv₀ (C := Sheaf J AddCommGrpCat.{w})).injective
  apply (cancel_mono f).1
  rw [← Sheaf.H.addEquiv₀_map f x, ← Sheaf.H.addEquiv₀_map f y, h]

end Stacks.Cohomology.GlobalLongExactSequence

end
