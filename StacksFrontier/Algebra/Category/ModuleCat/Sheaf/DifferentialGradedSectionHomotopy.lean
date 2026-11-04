module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionModule
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomotopyCategory

/-!
# Sections of a sheaf of differential graded modules descend to the homotopy categories

Let `(A, d)` be a sheaf of differential graded algebras on a site and let `U` be an object of
the site. Taking sections over `U` is a functor from right differential graded `A`-modules to
right differential graded modules over the section algebra `A(U)`; this file shows that it
carries homotopies to homotopies, hence homotopic morphisms to homotopic homomorphisms, and
therefore descends to a functor `K(A) ⥤ K(A(U))` of homotopy categories.

A homotopy at the level of sheaves is a family of morphisms `M^n ⟶ N^{n-1}` compatible with the
right action of `A` and with commutator `f - g` against the differentials. Reading it on
sections summand by summand produces exactly a homotopy of the ambient, single-type notion: a
right `A(U)`-linear map of the total sections lowering the grading by one.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.Homotopy.sectionsAdd`: the map on total sections
  underlying a homotopy.
* `SheafOfModules.DifferentialGradedModule.Homotopy.sections`: **a homotopy of morphisms of
  sheaves of differential graded modules, read on sections over `U`.**
* `SheafOfModules.DifferentialGradedModule.sectionHomotopyFunctor`: **the functor
  `K(A) ⥤ K(A(U))` of homotopy categories induced by taking sections over `U`.**

## Main results

* `SheafOfModules.DifferentialGradedModule.Homotopic.sections`: taking sections carries
  homotopic morphisms to homotopic homomorphisms.
* `SheafOfModules.DifferentialGradedModule.sectionHomotopyFunctorIso` and
  `SheafOfModules.DifferentialGradedModule.sectionHomotopyFunctor_map_quotient_map`: the functor
  on homotopy categories is the descent of the section functor.

## Implementation notes

The degree bookkeeping is the whole content of the two nontrivial fields. Compatibility of a
sheaf-level homotopy with the right action is an `HEq` between homogeneous sections of the
propositionally — but not definitionally — equal degrees `(n + m) - 1` and `(n - 1) + m`;
`SheafOfModules.of_heq` turns it into an equality of summands of the direct sum of sections. The
homotopy equation carries an `eqToHom` identifying `(n + 1) - 1` with `n`, absorbed by
`SheafOfModules.DifferentialGradedModule.of_eqToHom_val_app`, and reads the differential of `N`
from degree `n - 1` to degree `n`, which `sectionD_of'` supplies from the differential of the
sections at its own target degree.

Evaluation of a morphism of sheaves of modules at a fixed local section is additive, and
`evalSectionHom` packages it so that the difference and the sum appearing in the homotopy
equation can be distributed over it by `map_sub` and `map_add`.

## References

* [Stacks Project, Tag 0FS0](https://stacks.math.columbia.edu/tag/0FS0)
* [Stacks Project, Tag 09JN](https://stacks.math.columbia.edu/tag/09JN)
-/

@[expose] public noncomputable section

open CategoryTheory DirectSum

universe t a v u

namespace SheafOfModules

namespace DifferentialGradedModule

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra sectionRModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R}

/-! ### Index bookkeeping -/

/-- Evaluation of a morphism of sheaves of modules at a fixed local section, as an additive map
in the morphism. The additivity of the hom groups of sheaves of modules is pointwise on local
sections. -/
def evalSectionHom {P Q : SheafOfModules.{a} R} (U : Cᵒᵖ) (z : P.val.obj U) :
    (P ⟶ Q) →+ Q.val.obj U :=
  AddMonoidHom.mk' (fun φ ↦ φ.val.app U z) fun _ _ ↦ rfl

/-- Evaluating a morphism at a fixed local section through `evalSectionHom` is applying the
morphism to that section. -/
@[simp] theorem evalSectionHom_apply {P Q : SheafOfModules.{a} R} (U : Cᵒᵖ) (z : P.val.obj U)
    (φ : P ⟶ Q) : evalSectionHom U z φ = φ.val.app U z := rfl

/-- The differential of the sections, read on a summand at an arbitrary target degree: the
degree-`j` form of `SheafOfModules.DifferentialGradedModule.sectionD_of` for `i + 1 = j`. -/
theorem sectionD_of' (M : DifferentialGradedModule.{t, a, a} A) (U : Cᵒᵖ) {i j : ℤ}
    (hij : i + 1 = j) (x : M.sectionsPiece U i) :
    M.sectionD U (DirectSum.of (M.sectionsPiece U) i x) =
      DirectSum.of (M.sectionsPiece U) j ((M.complex.d i j).val.app U x) := by
  subst hij
  exact M.sectionD_of U i x

/-- Transport of a homogeneous piece along an equality of degrees is absorbed by the structure
map of the direct sum of sections. -/
theorem of_eqToHom_val_app (N : DifferentialGradedModule.{t, a, a} A) (U : Cᵒᵖ) {i j : ℤ}
    (e : i = j) (x : N.sectionsPiece U i) :
    DirectSum.of (N.sectionsPiece U) j
        ((eqToHom (congrArg N.complex.X e)).val.app U x) =
      DirectSum.of (N.sectionsPiece U) i x := by
  subst e
  rfl

/-! ### A homotopy on sections -/

namespace Homotopy

variable {M N : DifferentialGradedModule.{t, a, a} A} {f g : M ⟶ N}

/-- The map on sections of the degree-`n` piece given by the degree-`n` component of a
homotopy, landing in the sections of the degree-`n - 1` piece. -/
def sectionsApp (h : Homotopy f g) (U : Cᵒᵖ) (n : ℤ) :
    M.sectionsPiece U n →+ N.sectionsPiece U (n - 1) :=
  AddMonoidHom.mk' (fun x ↦ (h.app n).val.app U x) fun x y ↦ map_add _ x y

/-- The degree-`n` map on sections of a homotopy applies the degree-`n` component of the
homotopy to the section. -/
@[simp] theorem sectionsApp_apply (h : Homotopy f g) (U : Cᵒᵖ) (n : ℤ)
    (x : M.sectionsPiece U n) : h.sectionsApp U n x = (h.app n).val.app U x := rfl

/-- **The map on total sections underlying a homotopy**: on the degree-`n` summand it is the
degree-`n` component of the homotopy, landing in the degree-`n - 1` summand. -/
def sectionsAdd (h : Homotopy f g) (U : Cᵒᵖ) : M.totalSections U →+ N.totalSections U :=
  DirectSum.toAddMonoid fun n ↦
    (DirectSum.of (N.sectionsPiece U) (n - 1)).comp (h.sectionsApp U n)

/-- On the degree-`n` summand, the map on total sections underlying a homotopy is the degree-`n`
map on sections, landing in the degree-`n - 1` summand. -/
@[simp] theorem sectionsAdd_of (h : Homotopy f g) (U : Cᵒᵖ) (n : ℤ)
    (x : M.sectionsPiece U n) :
    h.sectionsAdd U (DirectSum.of (M.sectionsPiece U) n x) =
      DirectSum.of (N.sectionsPiece U) (n - 1) (h.sectionsApp U n x) :=
  DirectSum.toAddMonoid_of
    (fun n ↦ (DirectSum.of (N.sectionsPiece U) (n - 1)).comp (h.sectionsApp U n)) n x

/-- The map on total sections underlying a homotopy is compatible with the right action of the
section algebra: this is the action compatibility of the homotopy, read summand by summand, the
degrees `(n + i) - 1` and `(n - 1) + i` being identified by `SheafOfModules.of_heq`. -/
theorem sectionsAdd_act (h : Homotopy f g) (U : Cᵒᵖ) (x : M.totalSections U)
    (s : A.toGradedAlgebra.totalSections U) :
    h.sectionsAdd U (M.act U x s) = N.act U (h.sectionsAdd U x) s := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply]
  | add x y hx hy => simp only [map_add, AddMonoidHom.add_apply, hx, hy]
  | of n p =>
      induction s using DirectSum.induction_on with
      | zero => simp only [map_zero]
      | add s s' hs hs' => simp only [map_add, hs, hs']
      | of i q =>
          simp only [act_of, actOn_of, sectionsAdd_of, sectionsApp_apply]
          exact of_heq (show n + i - 1 = n - 1 + i by omega) (h.map_mul n i U p q)

/-- The homotopy equation of a sheaf-level homotopy, evaluated at a local section: the two
composites are read on sections by `SheafOfModules.comp_val_app_apply`, and the difference and
the sum are distributed over evaluation at the section. -/
theorem comm_val_app (h : Homotopy f g) (U : Cᵒᵖ) (n : ℤ) (p : M.sectionsPiece U n) :
    (f.toHomologicalComplex.f n).val.app U p - (g.toHomologicalComplex.f n).val.app U p =
      (N.complex.d (n - 1) n).val.app U ((h.app n).val.app U p) +
        (eqToHom (congrArg N.complex.X (show n + 1 - 1 = n by omega))).val.app U
          ((h.app (n + 1)).val.app U ((M.complex.d n (n + 1)).val.app U p)) := by
  have e := congrArg (evalSectionHom (Q := N.complex.X n) U p) (h.comm n)
  rw [map_sub, map_add] at e
  exact e

/-- **A homotopy between morphisms of sheaves of differential graded modules, read on sections
over `U`.** Its underlying map is the component of the homotopy on each summand, it lowers the
grading by one because that component does, and its homotopy equation is the homotopy equation
of the sheaf-level homotopy evaluated on sections. -/
def sections (h : Homotopy f g) (U : Cᵒᵖ) :
    _root_.DifferentialGradedModule.Homotopy (sectionMap f U) (sectionMap g U) where
  toLinearMap :=
    { toFun := h.sectionsAdd U
      map_add' := map_add _
      map_smul' := fun s x ↦ h.sectionsAdd_act U x s.unop }
  map_grading := by
    rintro n x ⟨p, rfl⟩
    change h.sectionsAdd U (DirectSum.of (M.sectionsPiece U) n p) ∈
      Stacks.ExternalGrading.intSummand (N.sectionsPiece U) (n - 1)
    rw [sectionsAdd_of]
    exact Stacks.ExternalGrading.of_mem_intSummand _ (n - 1) _
  homotopy_eq := by
    intro x
    change sectionMapAdd f U x - sectionMapAdd g U x =
      N.sectionD U (h.sectionsAdd U x) + h.sectionsAdd U (M.sectionD U x)
    induction x using DirectSum.induction_on with
    | zero => simp only [map_zero, sub_zero, add_zero]
    | add x y hx hy =>
        simp only [map_add]
        rw [add_sub_add_comm, hx, hy]
        abel
    | of n p =>
        rw [sectionMapAdd_of, sectionMapAdd_of, sectionsAdd_of,
          N.sectionD_of' U (show n - 1 + 1 = n by omega), M.sectionD_of U n p, sectionsAdd_of,
          ← N.of_eqToHom_val_app U (show n + 1 - 1 = n by omega), ← map_sub, ← map_add]
        exact congrArg (DirectSum.of (N.sectionsPiece U) n) (h.comm_val_app U n p)

end Homotopy

/-- **Taking sections over `U` carries homotopic morphisms to homotopic homomorphisms.** -/
theorem Homotopic.sections {M N : DifferentialGradedModule.{t, a, a} A} {f g : M ⟶ N}
    (h : Homotopic f g) (U : Cᵒᵖ) :
    _root_.DifferentialGradedModule.Homotopic (sectionMap f U) (sectionMap g U) :=
  ⟨h.some.sections U⟩

/-! ### The functor on homotopy categories -/

/-- **The functor `K(A) ⥤ K(A(U))` induced by taking sections over `U`**: the section functor
followed by the homotopy quotient descends through the homotopy quotient of the sheaf side,
because taking sections preserves homotopies. -/
def sectionHomotopyFunctor (A : DifferentialGradedAlgebra.{t, a} R) (U : Cᵒᵖ) :
    HomotopyCategory.{t, a, a} A ⥤
      _root_.DifferentialGradedModule.HomotopyCategory (A.sectionAlgebra U) :=
  CategoryTheory.Quotient.lift
    (fun {M N : DifferentialGradedModule.{t, a, a} A} (f g : M ⟶ N) ↦ Homotopic f g)
    (sectionModuleFunctor A U ⋙
      _root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U))
    (fun _ _ _ _ hh ↦ CategoryTheory.Quotient.sound _ (Homotopic.sections hh U))

/-- The functor on homotopy categories is the descent of the section functor: composing it with
the homotopy quotient gives back the section functor followed by the homotopy quotient. -/
def sectionHomotopyFunctorIso (A : DifferentialGradedAlgebra.{t, a} R) (U : Cᵒᵖ) :
    HomotopyCategory.quotient.{t, a, a} A ⋙ sectionHomotopyFunctor A U ≅
      sectionModuleFunctor A U ⋙
        _root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U) :=
  CategoryTheory.Quotient.lift.isLift _ _ _

/-- The functor on homotopy categories sends the homotopy class of a morphism of sheaves of
differential graded modules to the homotopy class of its map on sections. -/
theorem sectionHomotopyFunctor_map_quotient_map {M N : DifferentialGradedModule.{t, a, a} A}
    (U : Cᵒᵖ) (f : M ⟶ N) :
    (sectionHomotopyFunctor A U).map ((HomotopyCategory.quotient A).map f) =
      (_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).map
        (sectionMap f U) :=
  rfl

end DifferentialGradedModule

end SheafOfModules

end
