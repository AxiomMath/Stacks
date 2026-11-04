module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Parasitic
public import StacksFrontier.AlgebraicGeometry.DeRham.DiffOpComplex
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex
public import StacksFrontier.AlgebraicGeometry.Nondegeneracy.StructureSheafNotIsZero

/-!
# The de Rham complex of a nonempty scheme is not a zero complex

The comparison data of the relative Künneth and de Rham constructions are bare morphism types,
inhabited by the zero morphism, so a statement that one of them exists certifies nothing on its
own. What it has to be tested against is a nonzero object: a statement asserting `¬ IsZero` of
`Ω^p_{X/S}`, of a term of the de Rham complex, or of an object of the derived categories these
maps live between.

This file supplies the bottom of that chain at `p = 0`, where `Ω^0_{X/S} ≅ 𝒪_X`, from
`AlgebraicGeometry.Scheme.not_isZero_unit`.

## Main results

* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.not_isZero_of_section_ne_zero` and
  `...not_isZero_of_not_isZero_module`: an object of the category of finite-order differential
  operators is a zero object exactly when its underlying module is, which the category's `IsZero`
  API did not record in this direction.
* `AlgebraicGeometry.Scheme.Hom.not_isZero_relativeDifferentialForms_zero`: `Ω^0_{X/S}` is not a
  zero `𝒪_X`-module when `X` is nonempty.
* `AlgebraicGeometry.Scheme.Hom.not_isZero_deRhamDiffOpTerm_zero` and
  `...not_isZero_deRhamDiffOpComplex_X_zero`: the degree-zero term of the relative de Rham
  complex, in the category of finite-order differential operators, is not a zero object.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry

namespace FiniteOrderDifferentialOperatorCategory

variable {X S : Scheme.{u}} {a : X ⟶ S}

/-- Any two local sections of a zero object of the category of finite-order differential
operators are equal. -/
private theorem eq_of_isZero {F : FiniteOrderDifferentialOperatorCategory a} (h : IsZero F)
    {U : (X.Opens)ᵒᵖ} (x y : F.module.val.obj U) : x = y := by
  have he : (𝟙 F : F ⟶ F) = 0 := (IsZero.iff_id_eq_zero F).mp h
  exact (congrArg (fun f : F ⟶ F => f.1 U x) he).trans (congrArg (fun f : F ⟶ F => f.1 U y) he).symm

/-- **An object of the category of finite-order differential operators with a nonzero local
section is not a zero object.**  A morphism of that category is an additive map on local
sections, so the identity is the zero morphism only if every local section vanishes. -/
theorem not_isZero_of_section_ne_zero {F : FiniteOrderDifferentialOperatorCategory a}
    {U : (X.Opens)ᵒᵖ} (m : F.module.val.obj U) (hm : m ≠ 0) : ¬ IsZero F := by
  intro h
  exact hm (eq_of_isZero h m 0)

/-- **An object of the category of finite-order differential operators whose underlying module
is not a zero module is not a zero object.**  The converse direction, from a zero object to a
zero module, is not needed here and is not stated. -/
theorem not_isZero_of_not_isZero_module {F : FiniteOrderDifferentialOperatorCategory a}
    (h : ¬ IsZero F.module) : ¬ IsZero F := by
  intro hF
  refine h ((Stacks.Adequate.isZero_iff_forall_subsingleton F.module).mpr (fun U => ?_))
  exact ⟨fun x y => eq_of_isZero hF x y⟩

end FiniteOrderDifferentialOperatorCategory

namespace Scheme.Hom

variable {X S : Scheme.{u}} (a : X ⟶ S)

/-- **`Ω^0_{X/S}` is not a zero `𝒪_X`-module when `X` is nonempty.**  The degree-zero piece of
the exterior algebra is `𝒪_X`, by `relativeDifferentialFormsZeroIso`, and the structure sheaf of
a nonempty scheme is not zero. -/
theorem not_isZero_relativeDifferentialForms_zero [Nonempty X] :
    ¬ IsZero (relativeDifferentialForms a 0) :=
  fun h => Scheme.not_isZero_unit X
    (((relativeDifferentialFormsZeroIso a).isZero_iff).mp h)

/-- **The degree-zero term of the relative de Rham complex is not a zero object** of the category
of finite-order differential operators on `X/S`, for a nonempty `X`. -/
theorem not_isZero_deRhamDiffOpTerm_zero [Nonempty X] :
    ¬ IsZero (deRhamDiffOpTerm a 0) :=
  FiniteOrderDifferentialOperatorCategory.not_isZero_of_not_isZero_module
    (not_isZero_relativeDifferentialForms_zero a)

/-- **The relative de Rham complex is not a zero complex**: its term in degree `0` is nonzero,
for a nonempty `X`.  This is the `¬ IsZero` anchor that the relative Künneth comparison of
[Stacks, Tag 0G4B] and the de Rham Künneth map of Section 36.25 are tested against; the
`ℤ`-indexed extension `deRhamDiffOpCochainComplex` has the same term in degree `0`, by
`deRhamDiffOpCochainComplexXIso`. -/
theorem not_isZero_deRhamDiffOpComplex_X_zero [Nonempty X] :
    ¬ IsZero ((deRhamDiffOpComplex a).X 0) :=
  not_isZero_deRhamDiffOpTerm_zero a

end Scheme.Hom

end AlgebraicGeometry
