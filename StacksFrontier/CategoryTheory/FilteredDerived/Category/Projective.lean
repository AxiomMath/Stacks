module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import StacksCore.CategoryTheory.Filtration.GradedPieces
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Homology

/-!
# Filtered projective objects

Let `C` be an abelian category. A finite filtered object of `C` is filtered projective when
each of its graded pieces is a projective object of `C`. For modules there is a stronger
notion: a finite filtered module is filtered finite projective when each graded piece is
finitely generated as well as projective. The underlying module of such an object is then
itself finite and projective, obtained by splitting off one graded piece at a time along the
finite filtration.

## Main definitions

* `CategoryTheory.FilteredDerived.IsFilteredProjective`: every graded piece of a finite
  filtered object is projective.
* `CategoryTheory.FilteredDerived.IsFilteredFiniteProjective`: every graded piece of a finite
  filtered module is finite and projective.

## Main results

* `CategoryTheory.FilteredDerived.IsFilteredFiniteProjective.isFilteredProjective`: filtered
  finite projectivity implies filtered projectivity.
* `CategoryTheory.FilteredDerived.IsFilteredFiniteProjective.finite_projective_forget`: the
  underlying module of a filtered finite projective module is finite projective.

## Implementation notes

A finite filtered object is represented by `CategoryTheory.FiniteFilteredObject`, and its
`p`-th graded piece is the value of `CategoryTheory.FilteredObject.gr p` on the underlying
filtered object. Both predicates are abbreviations, so that the API for
`CategoryTheory.Projective` and for `Module.Finite` applies to them directly. The module
category is taken in universe `max u v` over a ring in universe `u`, as the equivalence
between categorical projectivity and `Module.Projective` requires.

## References

* [Stacks Project, Tag 03TA](https://stacks.math.columbia.edu/tag/03TA)
* [Stacks Project, Section 03TJ](https://stacks.math.columbia.edu/tag/03TJ)
* [Stacks Project, Tag 03TL](https://stacks.math.columbia.edu/tag/03TL)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v u

namespace CategoryTheory.FilteredDerived

/-- A finite filtered object is **filtered projective** if all its graded pieces are
projective. -/
@[stacks 03TA "filtered_projective"]
abbrev IsFilteredProjective {C : Type u} [Category.{v} C] [Abelian C]
    (I : FiniteFilteredObject C) : Prop :=
  ∀ p : ℤ, Projective ((FilteredObject.gr (C := C) p).obj I.obj)

/-- A finite filtered module is **filtered finite projective** if each graded piece is finite
and projective. -/
abbrev IsFilteredFiniteProjective {R : Type u} [Ring R]
    (P : FiniteFilteredObject (ModuleCat.{max u v} R)) : Prop :=
  ∀ p : ℤ, Module.Finite R ((FiniteFilteredObject.grP
      (𝒜 := ModuleCat.{max u v} R) p).obj P) ∧
    Projective ((FiniteFilteredObject.grP p).obj P)

variable {R : Type u} [Ring R] {P : FiniteFilteredObject (ModuleCat.{max u v} R)}

/-- Filtered finite projectivity implies filtered projectivity. -/
theorem IsFilteredFiniteProjective.isFilteredProjective
    (hP : IsFilteredFiniteProjective P) : IsFilteredProjective P :=
  fun p => (hP p).2

/-- The underlying module of a filtered finite projective module is finite projective.
Descending induction along the finite filtration splits off one graded piece at a time. -/
@[sga "4½ Rapport 4.2" "more general"]
theorem IsFilteredFiniteProjective.finite_projective_forget
    (hP : IsFilteredFiniteProjective P) :
    Module.Finite R ((FiniteFilteredObject.forget (𝒜 := ModuleCat.{max u v} R)).obj P) ∧
      Module.Projective R
        ((FiniteFilteredObject.forget (𝒜 := ModuleCat.{max u v} R)).obj P) := by
  obtain ⟨a, ha⟩ := P.property.exists_isIso_ι
  obtain ⟨b, hb⟩ := P.property.exists_isZero_obj
  have hstep (p : ℤ) :
      Module.Finite R (P.obj.filtration.obj (op (p + 1))) ∧
        Projective (P.obj.filtration.obj (op (p + 1))) →
      Module.Finite R (P.obj.filtration.obj (op p)) ∧
        Projective (P.obj.filtration.obj (op p)) := by
    rintro ⟨hfin, hproj⟩
    let S := FilteredObject.stepShortComplex (FilteredObject.succHom p) P.obj
    have : Module.Finite R S.X₁ := hfin
    have : Projective S.X₁ := hproj
    have : Module.Finite R S.X₃ := (hP p).1
    have : Projective S.X₃ := (hP p).2
    let e := (FilteredObject.stepShortComplex_shortExact
      (FilteredObject.succHom p) P.obj).splittingOfProjective.isoBinaryBiproduct
    have : Module.Finite R ((S.X₁ ⊞ S.X₃) : ModuleCat R) :=
      Module.Finite.equiv (ModuleCat.biprodIsoProd S.X₁ S.X₃).symm.toLinearEquiv
    exact ⟨Module.Finite.equiv e.symm.toLinearEquiv,
      Projective.of_iso e.symm inferInstance⟩
  have hbase : Module.Finite R (P.obj.filtration.obj (op (max a b))) ∧
      Projective (P.obj.filtration.obj (op (max a b))) := by
    have h := P.obj.filtration.isZero_obj_of_le (le_max_right a b) hb
    have := ModuleCat.subsingleton_of_isZero h
    exact ⟨inferInstance, h.projective⟩
  have hall : ∀ p ≤ max a b, Module.Finite R (P.obj.filtration.obj (op p)) ∧
      Projective (P.obj.filtration.obj (op p)) :=
    Int.leInductionDown hbase fun p _ h ↦ hstep (p - 1) (by rwa [sub_add_cancel])
  obtain ⟨_, hproj⟩ := hall a (le_max_left a b)
  have : Projective (FiniteFilteredObject.forget.obj P) :=
    Projective.of_iso (asIso (P.obj.filtration.ι.app (op a))) hproj
  exact ⟨Module.Finite.equiv (asIso (P.obj.filtration.ι.app (op a))).toLinearEquiv,
    inferInstance⟩

end CategoryTheory.FilteredDerived

end
