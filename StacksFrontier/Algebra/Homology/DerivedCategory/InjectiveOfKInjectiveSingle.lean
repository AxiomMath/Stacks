module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension

/-!
# An object whose single complex is K-injective is injective

Let `C` be an abelian category and `E` an object of `C`. If the complex `E[0]`, that is `E`
placed in degree `0`, is K-injective, then `E` is an injective object. This is the converse of
`CochainComplex.isKInjective_single_obj_of_injective`.

## Main results

* `CochainComplex.injective_of_isKInjective_single`: an object whose single complex in degree
  `0` is K-injective is injective.

## Implementation notes

For K-injective `E[0]`, `Ext¹(Y, E)` is the type of cohomology classes of degree `1` of the
Hom complex from `Y[0]` to `E[0]`
(`CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective`). A cochain of degree `1`
between two complexes concentrated in degree `0` is zero, since each of its components starts
or ends at a zero object. So `Ext¹(-, E)` vanishes, and `E` is injective by
`CategoryTheory.injective_iff_subsingleton_ext_one`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A cochain of degree `1` between two complexes concentrated in degree `0` is zero. -/
private lemma subsingleton_cochain_single_one (Y E : C) :
    Subsingleton (HomComplex.Cochain ((singleFunctor C 0).obj Y)
      ((singleFunctor C 0).obj E) 1) := by
  refine ⟨fun z₁ z₂ => HomComplex.Cochain.ext _ _ fun p q hpq => ?_⟩
  by_cases hp : p = 0
  · have hq : q ≠ 0 := by omega
    exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 E q hq).eq_of_tgt _ _
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 Y p hp).eq_of_src _ _

/-- **An object whose single complex is K-injective is injective.** If `E` placed in degree `0`
is a K-injective complex, then `E` is an injective object. -/
theorem injective_of_isKInjective_single (E : C)
    [((singleFunctor C 0).obj E).IsKInjective] : Injective E := by
  let := HasExt.standard C
  rw [injective_iff_subsingleton_ext_one.{max u v}]
  intro Y
  have := subsingleton_cochain_single_one Y E
  have : Subsingleton (HomComplex.CohomologyClass ((singleFunctor C 0).obj Y)
      ((singleFunctor C 0).obj E) 1) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨y, rfl⟩ := y.mk_surjective
    rw [show x = y from HomComplex.Cocycle.ext (Subsingleton.elim _ _)]
  exact (HomComplex.CohomologyClass.equivOfIsKInjective.{max u v}
    (K := (singleFunctor C 0).obj Y) (L := (singleFunctor C 0).obj E) (n := 1)).symm.subsingleton

end CochainComplex
