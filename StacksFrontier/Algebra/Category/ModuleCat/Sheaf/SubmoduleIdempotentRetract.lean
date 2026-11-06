module

public import Mathlib.CategoryTheory.Retract
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleFactorThru

/-!
# A submodule on which a global scalar acts as the identity is a retract

Let `R` be a sheaf of rings with commutative rings of sections, `M` a sheaf of `R`-modules and
`N` a submodule of `M`. A compatible family `f` of local sections of `R` acts on `M` by
multiplication, naturally in `M` (`Stacks.SheafOfModules.globalSectionToEnd`). Suppose that

* multiplication by `f` carries every local section of `M` into `N`, and
* multiplication by `f` is the identity on every local section of `N`.

Then `N` is a **retract** of `M`: the inclusion is the section and the corestriction of
multiplication by `f` is the retraction. If moreover `f` vanishes, the retraction is zero and `N`
is a zero object.

This is the mechanism by which the determinant of a sheaf of modules is recognised as a retract
of the exterior algebra on a trivialising open: the rank idempotent of Stacks 0FJ9 is the family
`f`, the degreewise exterior annihilator is `N`, and the two hypotheses above are the two halves
of the idempotent's defining property. Above the top rank the idempotent vanishes and the
corresponding annihilator is zero, which is what makes the coproduct over the degrees finite.

## Main definitions

* `Stacks.SheafOfModules.smulRetraction`: multiplication by `f`, corestricted to `N`.
* `Stacks.SheafOfModules.retractOfSmul`: **the retract.**

## Main results

* `Stacks.SheafOfModules.smulRetraction_ι`: the corestriction composed with the inclusion of `N`
  is multiplication by `f`.
* `Stacks.SheafOfModules.isZero_toSheafOfModules_of_smul_eq_self`: a submodule on which a
  *vanishing* family acts as the identity is a zero object.

## Implementation notes

The corestriction is `SheafOfModules.Submodule.factorThru`, which is `LinearMap.codRestrict`
applied objectwise; nothing here needs a presheaf-level construction. The retract equation is an
equality of morphisms into a submodule, so it is checked on local sections and then on
representatives with `Subtype.ext`.

Commutativity of the rings of sections is assumed in the form `∀ U, IsMulCommutative
(R.obj.obj U)`, as `Stacks.SheafOfModules.globalSectionToEnd` does; it is what makes
multiplication by a section a morphism of sheaves of modules rather than only of sheaves of
abelian groups.

## References

* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
* [Stacks Project, Section 0FJ9](https://stacks.math.columbia.edu/tag/0FJ9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [∀ U, IsMulCommutative (R.obj.obj U)] {M : _root_.SheafOfModules.{w} R} (N : M.Submodule)
  (f : (R.obj ⋙ forget RingCat).sections)

open scoped IsMulCommutative

/-- **Multiplication by `f`, corestricted to a submodule it maps into.** -/
noncomputable def smulRetraction
    (hmem : ∀ (X : Cᵒᵖ) (x : M.val.obj X), f.val X • x ∈ N.obj X) :
    M ⟶ N.toSheafOfModules :=
  N.factorThru ((globalSectionToEnd.{v, u, w, w} R f).asHom.app M) hmem

/-- The corestriction of multiplication by `f` has the same values as multiplication by `f`. -/
@[simp] theorem smulRetraction_val_app_val
    (hmem : ∀ (X : Cᵒᵖ) (x : M.val.obj X), f.val X • x ∈ N.obj X) (X : Cᵒᵖ)
    (x : M.val.obj X) :
    (((smulRetraction R N f hmem).val.app X) x).val = f.val X • x :=
  rfl

/-- The corestriction of multiplication by `f`, composed with the inclusion of `N`, is
multiplication by `f`. -/
@[reassoc (attr := simp)]
theorem smulRetraction_ι (hmem : ∀ (X : Cᵒᵖ) (x : M.val.obj X), f.val X • x ∈ N.obj X) :
    smulRetraction R N f hmem ≫ N.ι = (globalSectionToEnd.{v, u, w, w} R f).asHom.app M :=
  N.factorThru_ι _ hmem

/-- **A submodule into which multiplication by `f` maps and on which it is the identity is a
retract of the ambient sheaf of modules.** The inclusion is the section and the corestriction of
multiplication by `f` is the retraction. -/
noncomputable def retractOfSmul
    (hmem : ∀ (X : Cᵒᵖ) (x : M.val.obj X), f.val X • x ∈ N.obj X)
    (hself : ∀ (X : Cᵒᵖ) (y : N.obj X), f.val X • (y : M.val.obj X) = (y : M.val.obj X)) :
    Retract N.toSheafOfModules M where
  i := N.ι
  r := smulRetraction R N f hmem
  retract := by
    refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun X => ?_)
    ext y
    exact Subtype.ext (hself X y)

omit [∀ U, IsMulCommutative (R.obj.obj U)] in
/-- **A submodule on which a vanishing family acts as the identity is a zero object**: every one
of its local sections is its own multiple by zero. -/
theorem isZero_toSheafOfModules_of_smul_eq_self
    (hself : ∀ (X : Cᵒᵖ) (y : N.obj X), f.val X • (y : M.val.obj X) = (y : M.val.obj X))
    (hf : ∀ X : Cᵒᵖ, f.val X = 0) : IsZero N.toSheafOfModules := by
  rw [IsZero.iff_id_eq_zero]
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun X => ?_)
  ext y
  refine Subtype.ext ?_
  have h := hself X y
  rw [hf X, zero_smul] at h
  exact h.symm

end Stacks.SheafOfModules

end
