module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeIdentity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetRightAdjoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategoryTriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedHomKInjective

/-!
# Cohomology as morphisms out of the regular differential graded module

Let `R` be a sheaf of rings on a site admitting sheafification and let `A` be a sheaf of
differential graded `R`-algebras, regarded as a right differential graded module over itself.
A morphism from that regular module into a right differential graded `A`-module `M` is right
multiplication by a closed global section of `M` in degree zero, and every such section arises
in this way from exactly one morphism. Consequently, for a quasi-isomorphism `N ⟶ I` into a
right differential graded module `I` which is local for the quasi-isomorphisms, every morphism
`A ⟶ N` of `D(A, d)` is the class of a closed global section of `I` in degree zero, and two
such sections have the same class exactly when the morphisms they define are homotopic. On a
ringed site and for `N` the shift `M[n]` of the homotopy category this reads
`H^n(C, M) = Hom_{D(A, d)}(A, M[n])`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.ClosedSections`: the closed global sections of a
  right differential graded module in a given degree.
* `SheafOfModules.DifferentialGradedModule.evalOne`: the global section in degree zero obtained
  by evaluating a morphism out of the regular module at the unit of the algebra.
* `SheafOfModules.DifferentialGradedModule.ofSection`: right multiplication by a closed global
  section in degree zero, as a morphism out of the regular module.
* `SheafOfModules.DifferentialGradedModule.derivedClassOfClosedSection`: the morphism of
  `D(A, d)` from the regular module attached to a closed global section in degree zero of a
  module receiving a quasi-isomorphism.
* `SheafOfModules.DifferentialGradedModule.derivedClassOfClosedSectionOfKInjective`: the same
  for a graded injective and K-injective such module, where locality is not assumed.

## Main results

* `SheafOfModules.DifferentialGradedModule.homRegularEquivClosedSections`: evaluation at the
  unit is a bijection from the morphisms out of the regular module onto the closed global
  sections in degree zero.
* `SheafOfModules.DifferentialGradedModule.exists_closedSection_derivedClass_eq` and
  `...exists_closedSection_derivedClass_eq_shift`: every morphism `A ⟶ N`, respectively
  `A ⟶ M[n]`, of `D(A, d)` is the class of a closed global section in degree zero of the
  resolution.
* `SheafOfModules.DifferentialGradedModule.derivedClassOfClosedSection_eq_iff`: two closed
  global sections have the same class exactly when they are homotopic.
* `SheafOfModules.DifferentialGradedModule.`
  `derivedClassOfClosedSection_surjective_and_eq_iff_of_isKInjective`: both directions at once,
  for a graded injective and K-injective resolution of the shift `M[n]` and with no locality
  hypothesis.

## References

* [Stacks Project, Tag 0FTX](https://stacks.math.columbia.edu/tag/0FTX)
* [Stacks Project, Tag 0FT8](https://stacks.math.columbia.edu/tag/0FT8)
* [Stacks Project, Tag 0FS8](https://stacks.math.columbia.edu/tag/0FS8)
* [Stacks Project, Tag 0FSX](https://stacks.math.columbia.edu/tag/0FSX)
-/

@[expose] public section

open CategoryTheory

namespace SheafOfModules

namespace DifferentialGradedModule

universe t a v u

section Regular

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R}

private theorem castHom_trans (X : ℤ → SheafOfModules.{a} R) {i j k : ℤ} (h : i = j)
    (h' : j = k) (U : Cᵒᵖ) (x : (X i).val.obj U) :
    castHom X h' U (castHom X h U x) = castHom X (h.trans h') U x := by
  subst h; subst h'; rfl

private theorem castHom_eq_of_heq (X : ℤ → SheafOfModules.{a} R) {i j k : ℤ} (hi : i = k)
    (hj : j = k) (U : Cᵒᵖ) {x : (X i).val.obj U} {y : (X j).val.obj U} (h : HEq x y) :
    castHom X hi U x = castHom X hj U y := by
  cases hi; cases hj; exact eq_of_heq h

private theorem homSections_f_castHom {K L : CochainComplex (SheafOfModules.{a} R) ℤ}
    (f : K ⟶ L) {i j : ℤ} (h : i = j) (U : Cᵒᵖ) (x : (K.X i).val.obj U) :
    castHom L.X h U (homSections (f.f i) U x) = homSections (f.f j) U (castHom K.X h U x) := by
  subst h; rfl

/-- The unit of a sheaf of differential graded algebras, as a global section in degree zero of
the regular right differential graded module. -/
def regularOne (A : DifferentialGradedAlgebra.{t, a} R) :
    ((regularModule A).complex.X 0).sections := A.one

/-- On each object, the unit section of the regular module is the unit of the algebra. -/
@[simp] theorem regularOne_eval (A : DifferentialGradedAlgebra.{t, a} R) (U : Cᵒᵖ) :
    (regularOne A).eval U = A.one.eval U := rfl

/-- The unit is a closed global section of the regular module. -/
theorem regularOne_closed (A : DifferentialGradedAlgebra.{t, a} R) (U : Cᵒᵖ) :
    ((regularModule A).complex.d 0 (0 + 1)).val.app U ((regularOne A).eval U) = 0 := by
  change ((regularModule A).complex.d 0 1).val.app U ((regularOne A).eval U) = 0
  exact A.one_closed U

/-- The closed global sections of a right differential graded module in degree `n`: the global
sections of its degree-`n` piece which the differential kills. -/
def ClosedSections (M : DifferentialGradedModule.{t, a, a} A) (n : ℤ) : Type _ :=
  { z : (M.complex.X n).sections //
    ∀ U : Cᵒᵖ, (M.complex.d n (n + 1)).val.app U (z.eval U) = 0 }

/-- Evaluation at the unit of the algebra: the global section in degree zero that a morphism
out of the regular right differential graded module takes the unit to. -/
def evalOne {M : DifferentialGradedModule.{t, a, a} A} (f : regularModule A ⟶ M) :
    (M.complex.X 0).sections :=
  PresheafOfModules.sectionsMk
    (fun U => homSections (f.toHomologicalComplex.f 0) U ((regularOne A).eval U))
    (fun {U V} g => by
      rw [homSections_naturality (f.toHomologicalComplex.f 0) g ((regularOne A).eval U)]
      exact congrArg _ (PresheafOfModules.sections_property (regularOne A) g))

/-- On each object, `evalOne f` is the value of `f` in degree zero at the unit. -/
theorem evalOne_eval {M : DifferentialGradedModule.{t, a, a} A} (f : regularModule A ⟶ M)
    (U : Cᵒᵖ) :
    (evalOne f).eval U = (f.toHomologicalComplex.f 0).val.app U ((regularOne A).eval U) := rfl

/-- Evaluation at the unit, as a closed global section in degree zero. -/
def evalOneClosed {M : DifferentialGradedModule.{t, a, a} A} (f : regularModule A ⟶ M) :
    ClosedSections M 0 :=
  ⟨evalOne f, fun U => by
    rw [evalOne_eval, ← homSections_apply, ← homSections_apply, ← homSections_comp,
      homSections_congr (f.toHomologicalComplex.comm 0 (0 + 1)) U, homSections_comp,
      homSections_apply ((regularModule A).complex.d 0 (0 + 1)) U ((regularOne A).eval U),
      regularOne_closed]
    simp⟩

/-- Right multiplication by a global section of `M` in degree `k`, as a morphism from the
degree-`n` piece of the algebra to the degree-`k + n` piece of `M`. -/
noncomputable def actionSheafHom {M : DifferentialGradedModule.{t, a, a} A} {k : ℤ}
    (z : (M.complex.X k).sections) (n : ℤ) : A.complex.X n ⟶ M.complex.X (k + n) :=
  ⟨{ app := fun U => ModuleCat.ofHom
      { toFun := fun y => (M.mul k n).app U (z.eval U) y
        map_add' := fun y y' => by simp
        map_smul' := fun r y => (M.mul k n).map_smul_right U r (z.eval U) y }
     naturality := fun {U V} g => by
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro y
       simp only [ModuleCat.comp_apply, ModuleCat.restrictScalars.map_apply]
       change (M.mul k n).app V (z.eval V) ((A.complex.X n).val.map g y)
         = (M.complex.X (k + n)).val.map g ((M.mul k n).app U (z.eval U) y)
       rw [(M.mul k n).naturality g (z.eval U) y,
         PresheafOfModules.sections_property z g] }⟩

/-- On sections, `actionSheafHom z n` is right multiplication by `z` through the action of `M`. -/
theorem homSections_actionSheafHom {M : DifferentialGradedModule.{t, a, a} A} {k : ℤ}
    (z : (M.complex.X k).sections) (n : ℤ) (U : Cᵒᵖ) (y : (A.complex.X n).val.obj U) :
    homSections (actionSheafHom z n) U y = (M.mul k n).app U (z.eval U) y := rfl

/-- Right multiplication by a global section of `M` in degree zero, as a morphism from the
degree-`n` piece of the algebra to the degree-`n` piece of `M`. -/
noncomputable def actionHom {M : DifferentialGradedModule.{t, a, a} A}
    (z : (M.complex.X 0).sections) (n : ℤ) : A.complex.X n ⟶ M.complex.X n :=
  actionSheafHom z n ≫ degCastHom M.complex.X (zero_add n)

/-- On sections, `actionHom z n` is right multiplication by `z`, followed by the identification of
degree `0 + n` with degree `n`. -/
theorem homSections_actionHom {M : DifferentialGradedModule.{t, a, a} A}
    (z : (M.complex.X 0).sections) (n : ℤ) (U : Cᵒᵖ) (y : (A.complex.X n).val.obj U) :
    homSections (actionHom z n) U y
      = castHom M.complex.X (zero_add n) U ((M.mul 0 n).app U (z.eval U) y) := by
  rw [actionHom, homSections_comp, homSections_degCastHom, homSections_actionSheafHom]

/-- Right multiplication by a closed global section in degree zero, as a morphism of complexes
from the algebra to `M`. -/
noncomputable def ofSectionComplexHom {M : DifferentialGradedModule.{t, a, a} A}
    (z : (M.complex.X 0).sections)
    (hz : ∀ U : Cᵒᵖ, (M.complex.d 0 (0 + 1)).val.app U (z.eval U) = 0) :
    A.complex ⟶ M.complex where
  f n := actionHom z n
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine homSections_ext fun U y => ?_
    rw [homSections_comp, homSections_actionHom, homSections_d_succ_castHom,
      leibniz' M 0 i U (z.eval U) y, homSections_apply, hz U]
    simp only [map_zero, AddMonoidHom.zero_apply, Int.negOnePow_zero, Units.val_one,
      one_smul, zero_add, castHom_trans]
    rw [homSections_comp, homSections_actionHom]

/-- The degree-`n` component of `ofSectionComplexHom z hz` is `actionHom z n`. -/
theorem ofSectionComplexHom_f {M : DifferentialGradedModule.{t, a, a} A}
    (z : (M.complex.X 0).sections)
    (hz : ∀ U : Cᵒᵖ, (M.complex.d 0 (0 + 1)).val.app U (z.eval U) = 0) (n : ℤ) :
    (ofSectionComplexHom z hz).f n = actionHom z n := rfl

/-- Right multiplication by a global section in degree zero commutes with the action of the
algebra. -/
theorem actionHom_mul {M : DifferentialGradedModule.{t, a, a} A}
    (z : (M.complex.X 0).sections) (n i : ℤ) (U : Cᵒᵖ)
    (x : (A.complex.X n).val.obj U) (y : (A.complex.X i).val.obj U) :
    homSections (actionHom z (n + i)) U ((A.mul n i).app U x y)
      = (M.mul n i).app U (homSections (actionHom z n) U x) y := by
  rw [homSections_actionHom, homSections_actionHom, mul_castHom_left]
  exact (castHom_eq_of_heq M.complex.X _ _ U (M.mul_assoc 0 n i U (z.eval U) x y)).symm

/-- The morphism of right differential graded modules out of the regular module determined by a
closed global section in degree zero: right multiplication by that section. -/
noncomputable def ofSection {M : DifferentialGradedModule.{t, a, a} A}
    (z : (M.complex.X 0).sections)
    (hz : ∀ U : Cᵒᵖ, (M.complex.d 0 (0 + 1)).val.app U (z.eval U) = 0) :
    regularModule A ⟶ M where
  toHomologicalComplex := ofSectionComplexHom z hz
  map_mul n i U x y := actionHom_mul z n i U x y

/-- The degree-`n` component of `ofSection z hz` is `actionHom z n`. -/
theorem ofSection_toHomologicalComplex_f {M : DifferentialGradedModule.{t, a, a} A}
    (z : (M.complex.X 0).sections)
    (hz : ∀ U : Cᵒᵖ, (M.complex.d 0 (0 + 1)).val.app U (z.eval U) = 0) (n : ℤ) :
    (ofSection z hz).toHomologicalComplex.f n = actionHom z n := rfl

/-- Right multiplication by a closed global section takes the unit to that section. -/
theorem evalOne_ofSection {M : DifferentialGradedModule.{t, a, a} A}
    (z : (M.complex.X 0).sections)
    (hz : ∀ U : Cᵒᵖ, (M.complex.d 0 (0 + 1)).val.app U (z.eval U) = 0) :
    evalOne (ofSection z hz) = z := by
  refine PresheafOfModules.sections_ext _ _ fun U => ?_
  refine (homSections_actionHom z 0 U (A.one.eval U)).trans ?_
  exact castHom_eq_of_heq M.complex.X (zero_add 0) rfl U (M.mul_one 0 U (z.eval U))

/-- A morphism out of the regular module is right multiplication by its value at the unit. -/
theorem ofSection_evalOne {M : DifferentialGradedModule.{t, a, a} A}
    (f : regularModule A ⟶ M) :
    ofSection (evalOne f) (evalOneClosed f).2 = f := by
  refine Hom.ext fun n => homSections_ext fun U y => ?_
  refine (homSections_actionHom (evalOne f) n U y).trans ?_
  have hone : castHom (regularModule A).complex.X (zero_add n) U
      (((regularModule A).mul 0 n).app U ((regularOne A).eval U) y) = y :=
    castHom_eq_of_heq _ (zero_add n) rfl U (A.one_mul n U y)
  have key : (M.mul 0 n).app U ((evalOne f).eval U) y
      = homSections (f.toHomologicalComplex.f (0 + n)) U
        (((regularModule A).mul 0 n).app U ((regularOne A).eval U) y) :=
    (f.map_mul 0 n U ((regularOne A).eval U) y).symm
  rw [key, homSections_f_castHom f.toHomologicalComplex (zero_add n) U, hone]

/-- **Evaluation at the unit.** Morphisms from the regular right differential graded module into
a right differential graded module `M` are the closed global sections of `M` in degree zero. -/
noncomputable def homRegularEquivClosedSections (M : DifferentialGradedModule.{t, a, a} A) :
    (regularModule A ⟶ M) ≃ ClosedSections M 0 where
  toFun := evalOneClosed
  invFun z := ofSection z.1 z.2
  left_inv f := ofSection_evalOne f
  right_inv z := Subtype.ext (evalOne_ofSection z.1 z.2)

/-- The inverse of `homRegularEquivClosedSections M` sends a closed global section to right
multiplication by it. -/
@[simp] theorem homRegularEquivClosedSections_symm_apply
    {M : DifferentialGradedModule.{t, a, a} A} (z : ClosedSections M 0) :
    (homRegularEquivClosedSections M).symm z = ofSection z.1 z.2 := rfl

end Regular

/-! ### Morphisms out of the regular module in the derived category -/

section Derived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{a}] [J.WEqualsLocallyBijective AddCommGrpCat.{a}]
  {A : DifferentialGradedAlgebra.{t, a} R}

/-- The morphism of `D(A, d)` from the regular right differential graded module attached to a
closed global section in degree zero of a module `I` receiving a quasi-isomorphism from `N`:
multiply the unit by that section and localize. -/
noncomputable def derivedClassOfClosedSection {N I : DifferentialGradedModule.{t, a, a} A}
    (hI : (quasiIsomorphisms.{t, a, a} A).isLocal ((HomotopyCategory.quotient A).obj I))
    {b : N ⟶ I} (hb : QuasiIso b.toHomologicalComplex) (z : ClosedSections I 0) :
    ((toDerivedCategory.{t, a, a} A).obj
        ((HomotopyCategory.quotient A).obj (regularModule A)) ⟶
      (toDerivedCategory.{t, a, a} A).obj ((HomotopyCategory.quotient A).obj N)) :=
  (derivedHomEquivHomotopyHom (M := regularModule A) hI hb).symm
    ((HomotopyCategory.quotient A).map ((homRegularEquivClosedSections I).symm z))

/-- Every morphism from the regular right differential graded module into `N` in `D(A, d)` is the
class of a closed global section in degree zero of a module `I`, local for the
quasi-isomorphisms, receiving a quasi-isomorphism from `N`. -/
theorem exists_closedSection_derivedClass_eq {N I : DifferentialGradedModule.{t, a, a} A}
    (hI : (quasiIsomorphisms.{t, a, a} A).isLocal ((HomotopyCategory.quotient A).obj I))
    {b : N ⟶ I} (hb : QuasiIso b.toHomologicalComplex)
    (ξ : (toDerivedCategory.{t, a, a} A).obj
        ((HomotopyCategory.quotient A).obj (regularModule A)) ⟶
      (toDerivedCategory.{t, a, a} A).obj ((HomotopyCategory.quotient A).obj N)) :
    ∃ z : ClosedSections I 0, derivedClassOfClosedSection hI hb z = ξ := by
  obtain ⟨g, hg⟩ := (HomotopyCategory.quotient A).map_surjective (X := regularModule A) (Y := I)
    (derivedHomEquivHomotopyHom (M := regularModule A) hI hb ξ)
  refine ⟨homRegularEquivClosedSections I g, ?_⟩
  rw [derivedClassOfClosedSection, Equiv.symm_apply_eq, Equiv.symm_apply_apply, hg]

/-- Two closed global sections in degree zero of a module `I`, local for the
quasi-isomorphisms, have the same class in `D(A, d)` exactly when right multiplication by them is
homotopic. -/
theorem derivedClassOfClosedSection_eq_iff {N I : DifferentialGradedModule.{t, a, a} A}
    (hI : (quasiIsomorphisms.{t, a, a} A).isLocal ((HomotopyCategory.quotient A).obj I))
    {b : N ⟶ I} (hb : QuasiIso b.toHomologicalComplex) (z z' : ClosedSections I 0) :
    derivedClassOfClosedSection hI hb z = derivedClassOfClosedSection hI hb z' ↔
      Homotopic (ofSection z.1 z.2) (ofSection z'.1 z'.2) := by
  rw [derivedClassOfClosedSection, derivedClassOfClosedSection, Equiv.apply_eq_iff_eq]
  exact HomotopyCategory.quotient_map_eq_iff _ _

end Derived

/-! ### The shifted form on a ringed site -/

section Shift

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {B : DifferentialGradedAlgebra.{u, a} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}

/-- The shift `M[n]` of a right differential graded module, read off the translation functors
of the homotopy category. -/
noncomputable abbrev shiftedModule
    (B : DifferentialGradedAlgebra.{u, a} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (M : DifferentialGradedModule.{u, a, a} B) (n : ℤ) :
    DifferentialGradedModule.{u, a, a} B :=
  (((HomotopyCategory.quotient B).obj M)⟦n⟧).as

/-- The image of `shiftedModule B M n` in the homotopy category is the shift by `n` of the image of
`M`. -/
theorem quotient_obj_shiftedModule
    (B : DifferentialGradedAlgebra.{u, a} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (M : DifferentialGradedModule.{u, a, a} B) (n : ℤ) :
    (HomotopyCategory.quotient B).obj (shiftedModule B M n) =
      ((HomotopyCategory.quotient B).obj M)⟦n⟧ := rfl

variable [HasSheafify X.J AddCommGrpCat.{a}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{a}]

/-- The shifted form of `exists_closedSection_derivedClass_eq`: every morphism `A ⟶ M[n]` of
`D(A, d)` is the class of a closed global section in degree zero of a module `I`, local for the
quasi-isomorphisms, receiving a quasi-isomorphism from `M[n]`. -/
theorem exists_closedSection_derivedClass_eq_shift
    {M I : DifferentialGradedModule.{u, a, a} B} {n : ℤ}
    (hI : (quasiIsomorphisms.{u, a, a} B).isLocal ((HomotopyCategory.quotient B).obj I))
    {b : shiftedModule B M n ⟶ I} (hb : QuasiIso b.toHomologicalComplex)
    (ξ : (toDerivedCategory.{u, a, a} B).obj
        ((HomotopyCategory.quotient B).obj (regularModule B)) ⟶
      (toDerivedCategory.{u, a, a} B).obj (((HomotopyCategory.quotient B).obj M)⟦n⟧)) :
    ∃ z : ClosedSections I 0, derivedClassOfClosedSection hI hb z = ξ :=
  exists_closedSection_derivedClass_eq hI hb ξ

end Shift

/-! ### Graded injective K-injective resolutions -/

section KInjective

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {B : DifferentialGradedAlgebra.{u, a} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  [HasSheafify X.J AddCommGrpCat.{a}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{a}]

/-- The morphism of `D(A, d)` from the regular right differential graded module attached to a
closed global section in degree zero of a graded injective and K-injective module `I` receiving
a quasi-isomorphism from `N`. -/
noncomputable def derivedClassOfClosedSectionOfKInjective
    {N I : DifferentialGradedModule.{u, a, a} B} (hI : IsKInjective I) (hI' : GradedInjective I)
    {b : N ⟶ I} (hb : QuasiIso b.toHomologicalComplex) (z : ClosedSections I 0) :
    ((toDerivedCategory.{u, a, a} B).obj
        ((HomotopyCategory.quotient B).obj (regularModule B)) ⟶
      (toDerivedCategory.{u, a, a} B).obj ((HomotopyCategory.quotient B).obj N)) :=
  derivedClassOfClosedSection (isLocal_quotient_obj_of_isKInjective hI hI') hb z

/-- Let `(C, O)` be a ringed site, `A` a sheaf of differential graded `O`-algebras, `M` a right
differential graded `A`-module and `n` an integer. Let `I` be a graded injective and K-injective
right differential graded `A`-module receiving a quasi-isomorphism from the shift `M[n]`. Then
the closed global sections of `I` in degree zero modulo homotopy are the morphisms `A ⟶ M[n]` of
`D(A, d)`: every such morphism is the class of a closed global section, and two closed global
sections have the same class exactly when right multiplication by them is homotopic. -/
theorem derivedClassOfClosedSection_surjective_and_eq_iff_of_isKInjective
    {M I : DifferentialGradedModule.{u, a, a} B} {n : ℤ}
    (hI : IsKInjective I) (hI' : GradedInjective I)
    {b : shiftedModule B M n ⟶ I} (hb : QuasiIso b.toHomologicalComplex) :
    (∀ ξ : (toDerivedCategory.{u, a, a} B).obj
          ((HomotopyCategory.quotient B).obj (regularModule B)) ⟶
        (toDerivedCategory.{u, a, a} B).obj (((HomotopyCategory.quotient B).obj M)⟦n⟧),
        ∃ z : ClosedSections I 0,
          derivedClassOfClosedSectionOfKInjective hI hI' hb z = ξ) ∧
      ∀ z z' : ClosedSections I 0,
        derivedClassOfClosedSectionOfKInjective hI hI' hb z =
            derivedClassOfClosedSectionOfKInjective hI hI' hb z' ↔
          Homotopic (ofSection z.1 z.2) (ofSection z'.1 z'.2) :=
  ⟨fun ξ => exists_closedSection_derivedClass_eq_shift
      (isLocal_quotient_obj_of_isKInjective hI hI') hb ξ,
    derivedClassOfClosedSection_eq_iff (isLocal_quotient_obj_of_isKInjective hI hI') hb⟩

end KInjective

end DifferentialGradedModule

end SheafOfModules

end
