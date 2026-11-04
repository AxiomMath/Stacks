module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.SplitFamilyComplexExactness

/-!
# The sheaf-level Čech complex of a split family is exact in positive degrees

`Stacks.CechSite.exactAt_cechComplex_of_section` says that the Čech complex of a family one of
whose members admits a section is exact in every positive degree, for a presheaf with values in
an abelian category.  This file transports that statement to the *sheaf-level* Čech complex
`Stacks.CechSite.SheafLevel.complexFunctor`, whose coefficients are sheaves of modules.

## Main results

* `Stacks.CechSite.exactAt_cechComplex_of_section_of_abelian`: the Čech complex of a split
  family is exact in positive degrees, with the abelian structure of the coefficient category
  supplied as data rather than as an instance.
* `Stacks.CechSite.SheafLevel.abelian_toPreadditive`: the additive structure underlying
  `CategoryTheory.SheafOfModules.instAbelian` is
  `CategoryTheory.SheafOfModules.instPreadditive`.
* `Stacks.CechSite.SheafLevel.exactAt_complexFunctor_of_section`: the sheaf-level Čech complex
  of a split family is exact in every positive degree.

## Implementation notes

The content is already in `Stacks.CechSite.exactAt_cechComplex_of_section`, and
`Stacks.CechSite.SheafLevel.complexFunctor_obj_eq` already identifies the sheaf-level complex
with the Čech complex of the Čech diagram.  The one obstacle is which
`CategoryTheory.Preadditive` instance each side carries.
`Stacks.CechSite.SheafLevel.complexFunctor` is built with
`CategoryTheory.SheafOfModules.instPreadditive`, whereas
`Stacks.CechSite.exactAt_cechComplex_of_section` is stated under `[Abelian A]` and so carries
`CategoryTheory.Abelian.toPreadditive`.  The two are equal by `rfl` — the abelian structure of
sheaves of modules is transferred along the sheafification adjunction from that very additive
structure — but *applying* the theorem to the complex makes Lean unify the two complexes field
by field, with the instances unfolded inside each field, and that exceeds the per-declaration
elaboration budget.

The fix is to separate the two costs into two declarations.
`exactAt_cechComplex_of_section_of_abelian` takes the `CategoryTheory.Abelian` structure as an
*explicit argument* together with an equation identifying its additive part with the ambient
`CategoryTheory.Preadditive` instance; substituting that equation puts the goal in the shape the
original theorem proves, with no unification of complexes to perform.  The equation itself is
`abelian_toPreadditive`, a one-line `rfl` whose cost is a projection of a structure instance and
is paid in its own declaration.  `exactAt_complexFunctor_of_section` then composes the two, and
elaborates in a few seconds.

**What is not here: the general covering family.**  A covering family admits no section, so
nothing below applies to it directly.  The passage from here to a covering family is the
base-change-and-locality step: evaluate the complex over an object `W` mapping to a member
`U_i`, identify the result with the Čech complex of the base-changed family `{U_k ×_X W → W}`,
whose member at `i` does admit a section — the diagonal `W ⟶ U_i ×_X W` — and conclude by the
locality criterion `Stacks.SheafOfModules.ComplexLocality.exactAt_of_coversTop`.

## References

* [Stacks Project, Tag 03AT](https://stacks.math.columbia.edu/tag/03AT)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u v' u'

namespace Stacks.CechSite

variable {C : Type u} [Category.{v} C]

namespace SheafLevel

section Instance

variable {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The additive structure underlying the abelian structure of sheaves of modules is the
canonical one.**  `CategoryTheory.SheafOfModules.instAbelian` is transferred along the
sheafification adjunction from `CategoryTheory.SheafOfModules.instPreadditive`, so its additive
part is that instance on the nose. -/
theorem abelian_toPreadditive :
    (SheafOfModules.instAbelian (R := R)).toPreadditive = SheafOfModules.instPreadditive R :=
  rfl

end Instance

end SheafLevel

variable {X : C} (E : PreZeroHypercover.{w} X)
  [HasFiniteProducts C] [HasFiniteProducts (Over X)]

omit [HasFiniteProducts C] in
/-- **The Čech complex of a split family is exact in positive degrees**, with the abelian
structure of the coefficient category supplied as data.

This is `Stacks.CechSite.exactAt_cechComplex_of_section` with the `CategoryTheory.Abelian`
structure given as an explicit argument `ab` and the ambient
`CategoryTheory.Preadditive` instance — the one the complex in the conclusion is built with —
left free, the two being tied together by the hypothesis `hab`.  Supplying `hab` from a separate
declaration is what lets the statement be applied to a complex whose additive structure is
spelled differently from `CategoryTheory.Abelian.toPreadditive`; see the implementation notes of
this file. -/
theorem exactAt_cechComplex_of_section_of_abelian
    {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [pre : Preadditive A]
    (ab : Abelian A) (hab : ab.toPreadditive = pre)
    (P : Cᵒᵖ ⥤ A) {i₀ : E.I₀} (s : X ⟶ E.X i₀) (hs : s ≫ E.f i₀ = 𝟙 X) (n : ℕ) (hn : 0 < n) :
    (cechComplex E P).ExactAt n := by
  subst hab
  let := ab
  exact exactAt_cechComplex_of_section E P s hs n hn

namespace SheafLevel

variable {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [HasBinaryProducts C]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasProducts.{w} (SheafOfModules.{w} R)]
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [HasFiniteProducts C] [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The sheaf-level Čech complex of a split family is exact in positive degrees.**

A *section* of the `i₀`-th member of the family is `s : X ⟶ E.X i₀` with `s ≫ E.f i₀ = 𝟙 X`.
A general covering family has no such section, so this is not yet the statement that the
sheaf-level Čech complex of a covering is a resolution; see the implementation notes of this
file. -/
theorem exactAt_complexFunctor_of_section (F : SheafOfModules.{w} R) {i₀ : E.I₀}
    (s : X ⟶ E.X i₀) (hs : s ≫ E.f i₀ = 𝟙 X) (n : ℕ) (hn : 0 < n) :
    ((complexFunctor R E).obj F).ExactAt n :=
  exactAt_cechComplex_of_section_of_abelian E (SheafOfModules.instAbelian R)
    (abelian_toPreadditive R) (diagramObj R F) s hs n hn

end SheafLevel

end Stacks.CechSite

end
