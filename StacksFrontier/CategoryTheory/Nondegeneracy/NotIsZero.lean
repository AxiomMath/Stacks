module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum

/-!
# Primitives for proving that an object is not a zero object

A statement about an object `X` of a category with zero objects says nothing when `X` is a zero
object: there is exactly one morphism out of it and into it, so every equation between such
morphisms holds. Certifying that a construction over `X` is not of this kind therefore needs a
`¬ IsZero` input at the bottom of the argument, and the two shapes that input takes for sheaves
of modules and for their derived categories are collected here.

The reflection step — a zero object pulled back along a fully faithful functor — is not restated
here: Mathlib's `CategoryTheory.Limits.IsZero.of_full_of_faithful_of_isZero` and the repository's
`AlgebraicGeometry.isZero_of_isZero_map`
(`StacksFrontier/AlgebraicGeometry/UnboundedDerivedDirectImage/UniformBound.lean`) already cover it.

## Main results

* `Stacks.Nondegeneracy.not_isZero_of_section_ne_zero`: a sheaf of modules with one nonzero
  local section is not a zero object. `Stacks.Nondegeneracy.not_isZero_of_nontrivial` is the
  form reading a `Nontrivial` instance on a module of sections instead, and
  `Stacks.Nondegeneracy.not_isZero_unit_of_one_ne_zero` specialises both to the unit module, for
  which the section is `1`.
* `Stacks.Nondegeneracy.not_isZero_Q_obj_of_not_isZero_homology`: a cochain complex with
  nonvanishing homology in one degree has a nonzero image in the derived category. This is the
  complex-level counterpart of `DerivedCategory.isZero_iff_forall_isZero_homology`
  (`StacksFrontier/Homology/DerivedCategory/IsZero.lean`), which speaks about an abstract object of
  the derived category and so cannot be applied to a complex without this bridge.
* `Stacks.Nondegeneracy.not_isZero_singleFunctor_obj`: a nonzero object of an abelian category
  remains nonzero in the derived category when placed in a single degree.
-/

@[expose] public section

open CategoryTheory Limits

namespace Stacks.Nondegeneracy

universe w v u

/-! ### Sheaves of modules -/

section SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **A sheaf of modules with a nonzero local section is not a zero object.**  This is the
bottom of every non-degeneracy argument about sheaves of modules: it turns an arithmetic fact
about one module of sections into a statement about the object.  It is the contrapositive of
`Stacks.subsingleton_of_isZero`. -/
theorem not_isZero_of_section_ne_zero {M : SheafOfModules.{w} R} {X : Cᵒᵖ}
    (m : M.val.obj X) (hm : m ≠ 0) : ¬ IsZero M :=
  fun h => hm ((Stacks.subsingleton_of_isZero h X).elim m 0)

/-- **A sheaf of modules whose sections over some object form a nontrivial module is not a zero
object.**  The instance-driven form of `Stacks.Nondegeneracy.not_isZero_of_section_ne_zero`. -/
theorem not_isZero_of_nontrivial (M : SheafOfModules.{w} R) (X : Cᵒᵖ)
    [Nontrivial (M.val.obj X)] : ¬ IsZero M :=
  fun h => (not_subsingleton _) (Stacks.subsingleton_of_isZero h X)

/-- **The unit sheaf of modules is not a zero object as soon as one of its rings of sections is
nontrivial.**  The sections of `SheafOfModules.unit R` over `X` are `R.val.obj X` acting on
itself, so `1 ≠ 0` there is exactly a nonzero section. -/
theorem not_isZero_unit_of_one_ne_zero (R : Sheaf J RingCat.{w}) (X : Cᵒᵖ)
    (h : (1 : R.val.obj X) ≠ 0) : ¬ IsZero (SheafOfModules.unit R) :=
  not_isZero_of_section_ne_zero (M := SheafOfModules.unit R) (X := X) (1 : R.val.obj X) h

/-- **The unit sheaf of modules is not a zero object as soon as one of its rings of sections is
nontrivial**, read off a `Nontrivial` instance. -/
theorem not_isZero_unit_of_nontrivial (R : Sheaf J RingCat.{w}) (X : Cᵒᵖ)
    [Nontrivial (R.val.obj X)] : ¬ IsZero (SheafOfModules.unit R) :=
  not_isZero_unit_of_one_ne_zero R X one_ne_zero

end SheafOfModules

/-! ### Derived categories -/

section Derived

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- **A cochain complex with nonvanishing homology in one degree is nonzero in the derived
category.**  This is the acyclicity criterion in the direction a non-degeneracy certificate
needs: the homology functor on the derived category factors the homology functor on complexes,
so a complex whose image is a zero object has vanishing homology everywhere. -/
theorem not_isZero_Q_obj_of_not_isZero_homology {K : CochainComplex A ℤ} (n : ℤ)
    (h : ¬ IsZero ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n).obj K)) :
    ¬ IsZero (DerivedCategory.Q.obj K) :=
  fun hz => h (((DerivedCategory.homologyFunctorFactors A n).app K).isZero_iff.mp
    ((DerivedCategory.homologyFunctor A n).map_isZero hz))

/-- **A nonzero object of an abelian category stays nonzero in the derived category, placed in
any degree.**  `DerivedCategory.singleFunctor A n` is fully faithful, so a zero object upstairs
would reflect back to `M`. -/
theorem not_isZero_singleFunctor_obj (n : ℤ) {M : A} (h : ¬ IsZero M) :
    ¬ IsZero ((DerivedCategory.singleFunctor A n).obj M) :=
  fun hz => h (IsZero.of_full_of_faithful_of_isZero (DerivedCategory.singleFunctor A n) M hz)

end Derived

end Stacks.Nondegeneracy
