module

public import Mathlib.CategoryTheory.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopy

/-!
# The homotopy category of differential graded modules

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded
`R`-algebras. The homotopy category `K(A)` has the right differential graded `A`-modules as
objects and the homotopy classes of their morphisms as arrows.

Being homotopic is an equivalence relation stable under composition on either side, that is, a
congruence on the category of right differential graded modules, and the homotopy category is
the categorical quotient by it. Because the relation is already a congruence, the composition
closure that the quotient takes adds nothing, so the arrows of the quotient *are* the homotopy
classes.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.HomotopyCategory` is the homotopy category of right
  differential graded modules over a sheaf of differential graded algebras.
* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient` is the functor sending a
  morphism of right differential graded modules to its homotopy class.

## Main results

* `SheafOfModules.DifferentialGradedModule.homotopic_congruence`: homotopy is an equivalence
  relation compatible with composition.
* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient_map_eq_iff`: two morphisms
  have the same homotopy class exactly when they are homotopic.

## Implementation notes

The three parts of the equivalence relation are built from the zero homotopy, the negative of a
homotopy and the sum of two homotopies. Their action compatibility is an equality of
homogeneous sections in the propositionally — but not definitionally — equal degrees
`(n + m) - 1` and `(n - 1) + m`, so each needs the corresponding transport of `0`, of a
negation and of a sum across an equality of degrees; these are the private `gradedHEqZero`,
`gradedHEqNeg` and `gradedHEqAdd`.

`HomotopyCategory` is an `abbrev` so that the category structure, the morphism type and the
whole `CategoryTheory.Quotient` API are available on it without re-exporting them. The category
instance and the fullness of the quotient functor are nonetheless declared, since they are
found by typeclass search only through the congruence instance.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of
a ringed site, and the universes of the site, the ring, the algebra pieces and the module
pieces are independent, matching `SheafOfModules.DifferentialGradedAlgebra` and
`SheafOfModules.DifferentialGradedModule`; a ringed site `X` is the case `R := X.ringSheaf`.

## References

* [Stacks Project, Tag 0FS1](https://stacks.math.columbia.edu/tag/0FS1)
-/

@[expose] public section

open CategoryTheory

universe t a m v u

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

section Helpers

private theorem heqMap {V W : ℤ → Type*} {i j : ℤ} (hij : i = j)
    (f : ∀ k, V k → W k) {x : V i} {y : V j} (h : x ≍ y) :
    f i x ≍ f j y := by
  cases hij
  exact heq_of_eq (congrArg (f i) (eq_of_heq h))

private theorem gradedHEqZero {V : ℤ → Type*} [∀ i, AddCommMonoid (V i)]
    {i j : ℤ} (hij : i = j) :
    (0 : V i) ≍ (0 : V j) := by
  cases hij
  rfl

private theorem gradedHEqAdd {V : ℤ → Type*} [∀ i, AddCommGroup (V i)]
    {i j : ℤ} (hij : i = j) {x x' : V i} {y y' : V j}
    (h : x ≍ y) (h' : x' ≍ y') : x + x' ≍ y + y' := by
  cases hij
  exact heq_of_eq (congrArg₂ (· + ·) (eq_of_heq h) (eq_of_heq h'))

end Helpers

variable {A : DifferentialGradedAlgebra.{t, a} R}

/-- The zero homotopy from a morphism of right differential graded modules to itself. -/
private def homotopyRefl {M N : DifferentialGradedModule.{t, a, m} A} (f : M ⟶ N) :
    Homotopy f f where
  app _ := 0
  map_mul n i U x b := by
    change HEq (0 : (N.complex.X (n + i - 1)).val.obj U)
      ((N.mul (n - 1) i).app U (0 : (N.complex.X (n - 1)).val.obj U) b)
    simpa using (gradedHEqZero (V := fun q => (N.complex.X q).val.obj U)
      (show n + i - 1 = (n - 1) + i by omega))
  comm n := by simp

/-- The negative of a homotopy, a homotopy in the other direction. -/
private def homotopySymm {M N : DifferentialGradedModule.{t, a, m} A} {f g : M ⟶ N}
    (h : Homotopy f g) : Homotopy g f where
  app n := -h.app n
  map_mul n i U x b := by
    change HEq (-((h.app (n + i)).val.app U ((M.mul n i).app U x b))) _
    have hneg : ConcreteCategory.hom ((-h.app n).val.app U) =
        -ConcreteCategory.hom ((h.app n).val.app U) := by
      have hval : (-h.app n).val = -(h.app n).val :=
        CategoryTheory.Functor.map_neg (SheafOfModules.forget R)
      have hcomp : ConcreteCategory.hom (-(h.app n).val.app U) =
          -ConcreteCategory.hom ((h.app n).val.app U) := ModuleCat.hom_neg _
      exact (congrArg (fun φ => ConcreteCategory.hom (φ.app U)) hval).trans hcomp
    rw [hneg]
    simpa [map_neg] using
      (heqMap (V := fun q => (N.complex.X q).val.obj U) (show n + i - 1 = (n - 1) + i by omega)
        (fun _ => Neg.neg) (h.map_mul n i U x b))
  comm n := by
    rw [show g.toHomologicalComplex.f n - f.toHomologicalComplex.f n =
      -(f.toHomologicalComplex.f n - g.toHomologicalComplex.f n) by abel, h.comm]
    simp
    abel

/-- The sum of two consecutive homotopies. -/
private def homotopyTrans {M N : DifferentialGradedModule.{t, a, m} A} {f g k : M ⟶ N}
    (h : Homotopy f g) (h' : Homotopy g k) : Homotopy f k where
  app n := h.app n + h'.app n
  map_mul n i U x b := by
    simpa using
      (gradedHEqAdd (V := fun q => (N.complex.X q).val.obj U)
        (show n + i - 1 = (n - 1) + i by omega)
        (h.map_mul n i U x b) (h'.map_mul n i U x b))
  comm n := by
    rw [show f.toHomologicalComplex.f n - k.toHomologicalComplex.f n =
      (f.toHomologicalComplex.f n - g.toHomologicalComplex.f n) +
      (g.toHomologicalComplex.f n - k.toHomologicalComplex.f n) by abel,
      h.comm, h'.comm]
    simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
    abel

/-- The homotopy category of right differential graded modules over a sheaf of differential
graded algebras: the quotient of the category of right differential graded modules by the
homotopy relation. -/
@[stacks 0FS1 "the homotopy category"]
abbrev HomotopyCategory (A : DifferentialGradedAlgebra.{t, a} R) : Type _ :=
  CategoryTheory.Quotient
    (fun {M N : DifferentialGradedModule.{t, a, m} A} (f g : M ⟶ N) => Homotopic f g)

/-- Being homotopic is an equivalence relation compatible with composition on either side. -/
@[stacks 0FS1 "homotopy classes form a congruence"]
theorem homotopic_congruence (A : DifferentialGradedAlgebra.{t, a} R) :
    CategoryTheory.Congruence
      (fun {M N : DifferentialGradedModule.{t, a, m} A} (f g : M ⟶ N) => Homotopic f g) :=
  { equivalence :=
      { refl := fun f => ⟨homotopyRefl f⟩
        symm := fun ⟨h⟩ => ⟨homotopySymm h⟩
        trans := fun ⟨h⟩ ⟨h'⟩ => ⟨homotopyTrans h h'⟩ }
    comp_left := by
      intro K L M e g h ⟨H⟩
      exact ⟨{
        app n := e.toHomologicalComplex.f n ≫ H.app n
        map_mul n i U x b :=
          HEq.trans
            (heq_of_eq (congrArg (fun z => (H.app (n + i)).val.app U z)
              (e.map_mul n i U x b)))
            (H.map_mul n i U ((e.toHomologicalComplex.f n).val.app U x) b)
        comm n := by
          simp only [comp_f]
          rw [← Preadditive.comp_sub, H.comm, Preadditive.comp_add]
          simp only [Category.assoc]
          congr 1
          rw [← Category.assoc, e.toHomologicalComplex.comm n (n + 1)]
          simp only [Category.assoc]
      }⟩
    comp_right := by
      intro K L M f g h ⟨H⟩
      exact ⟨{
        app n := H.app n ≫ h.toHomologicalComplex.f (n - 1)
        map_mul n i U x b :=
          HEq.trans
            (heqMap (show n + i - 1 = (n - 1) + i by omega)
              (fun q z => (h.toHomologicalComplex.f q).val.app U z)
              (H.map_mul n i U x b))
            (heq_of_eq (h.map_mul (n - 1) i U ((H.app n).val.app U x) b))
        comm n := by
          simp only [comp_f]
          rw [← Preadditive.sub_comp, H.comm]
          simp only [Preadditive.add_comp, Category.assoc]
          rw [h.toHomologicalComplex.comm (n - 1) n]
          simp
      }⟩ }

attribute [instance] homotopic_congruence

/-- The homotopy category of right differential graded modules is a category, with morphisms the
homotopy classes of morphisms of differential graded modules. -/
instance (A : DifferentialGradedAlgebra.{t, a} R) :
    Category (HomotopyCategory.{t, a, m} A) :=
  CategoryTheory.Quotient.category (r :=
    (fun {M N : DifferentialGradedModule.{t, a, m} A} (f g : M ⟶ N) => Homotopic f g))

namespace HomotopyCategory

/-- The canonical functor from right differential graded modules to their homotopy category. -/
@[implicit_reducible]
def quotient (A : DifferentialGradedAlgebra.{t, a} R) :
    DifferentialGradedModule.{t, a, m} A ⥤ HomotopyCategory.{t, a, m} A :=
  CategoryTheory.Quotient.functor _

/-- The quotient functor to the homotopy category is full. -/
instance quotient_full (A : DifferentialGradedAlgebra.{t, a} R) :
    (quotient.{t, a, m} A).Full :=
  CategoryTheory.Quotient.full_functor _

/-- Two morphisms of right differential graded modules determine the same arrow of the homotopy
category exactly when they are homotopic. -/
theorem quotient_map_eq_iff {M N : DifferentialGradedModule.{t, a, m} A} (f g : M ⟶ N) :
    (quotient A).map f = (quotient A).map g ↔ Homotopic f g :=
  CategoryTheory.Quotient.functor_map_eq_iff _ f g

end HomotopyCategory

end DifferentialGradedModule

end SheafOfModules
