module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ConstantBaseRing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.DifferentialGraded.AlgebraCategory
public import StacksFrontier.Algebra.Homology.FunctorToComplexOfFunctors
public import StacksCore.Tactic.StacksAttribute

/-!
# An inverse system of differential graded algebras as a sheaf of them

Let `C` be a category viewed as a site with the chaotic topology and let `𝒪` be the constant
sheaf of rings with value a commutative ring `Λ`. A sheaf of differential graded
`𝒪`-algebras on this site is the same thing as an inverse system of differential graded
`Λ`-algebras, that is, a functor `Cᵒᵖ ⥤ DifferentialGradedAlgebra Λ`. This file turns that
identification into a construction: it builds the sheaf of differential graded algebras from
the system.

## Main definitions

* `Stacks.ChaoticSite.systemComplex`: the cochain complex of sheaves of modules underlying the
  system, degree by degree the graded pieces of the stages.
* `Stacks.ChaoticSite.gradedMul`: multiplication of homogeneous elements of a differential
  graded algebra as a biadditive map of the graded pieces, and
  `Stacks.ChaoticSite.systemMul`, `Stacks.ChaoticSite.systemOne` the induced multiplication and
  unit of the sheaf.
* `Stacks.ChaoticSite.systemAlgebra`: **the sheaf of differential graded algebras attached to
  the system.**

## Implementation notes

The differential of the complex is not definitionally the graded differential of the stage,
because `CochainComplex.of` guards it by a decidable equality of degrees that does not reduce
for a variable degree; `systemComplex_d_val_app` is the rewrite that evaluates it.
-/
@[expose] public noncomputable section

open CategoryTheory Opposite DifferentialGradedModule Stacks.PresheafOfModules

universe u u₁ v₁

namespace Stacks.ChaoticSite

variable {C : Type u₁} [Category.{v₁} C] {Λ : Type u} [CommRing Λ]
  (A : Cᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} Λ)

/-- The sheaf of rings underlying the constant sheaf of commutative rings is the constant
sheaf of rings. -/
theorem toRingCat_constCommRingSheaf (Λ : Type u) [CommRing Λ] :
    Stacks.SheafOfModules.Tensor.ringSheaf (constCommRingSheaf (C := C) Λ)
      = constRingSheaf (C := C) Λ := by
  show (⟨(Functor.const Cᵒᵖ).obj (CommRingCat.of Λ) ⋙ forget₂ CommRingCat.{u} RingCat.{u},
      _⟩ : Sheaf (⊥ : GrothendieckTopology C) RingCat.{u}) = ⟨constRing (C := C) Λ, _⟩
  congr 1

/-- The cochain complex of sheaves of modules underlying an inverse system of differential
graded algebras. -/
def systemComplex : CochainComplex (SheafOfModules.{u} (constRingSheaf (C := C) Λ)) ℤ :=
  ((ofFunctorSheaf Λ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (HomologicalComplex.ofFunctorToComplex
      (A ⋙ DifferentialGradedAlgebra.toCochainComplexFunctor))

/-- The degree `p` term of `systemComplex A` evaluated at `U` is the degree `p` piece of the
grading of `A.obj U`. -/
theorem systemComplex_X_val_obj (p : ℤ) (U : Cᵒᵖ) :
    ((systemComplex A).X p).val.obj U = ModuleCat.of Λ ((A.obj U).grading p) := rfl

/-- The differential of `systemComplex A` evaluated at `U` is the graded differential of
`A.obj U`. -/
theorem systemComplex_d_val_app (p : ℤ) (U : Cᵒᵖ) :
    ((systemComplex A).d p (p + 1)).val.app U =
      ModuleCat.ofHom ((regularModule (A.obj U)).gradedDifferential p) :=
  toCochainComplex_d (regularModule (A.obj U)) p

/-- Multiplication of homogeneous elements of a differential graded algebra, as a biadditive
map of the graded pieces. -/
def gradedMul (B : DifferentialGradedAlgebra.{u, u} Λ) (p q : ℤ) :
    B.grading p →+ B.grading q →+ B.grading (p + q) :=
  AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => ⟨(x : B.A) * (y : B.A), SetLike.mul_mem_graded x.2 y.2⟩)
      (fun y z => Subtype.ext (by simpa using mul_add (x : B.A) (y : B.A) (z : B.A))))
    (fun x z => by
      refine AddMonoidHom.ext fun y => Subtype.ext ?_
      simpa using add_mul (x : B.A) (z : B.A) (y : B.A))

/-- The underlying element of `gradedMul B p q x y` is the product of `x` and `y` in `B.A`. -/
@[simp]
theorem gradedMul_coe (B : DifferentialGradedAlgebra.{u, u} Λ) (p q : ℤ)
    (x : B.grading p) (y : B.grading q) :
    ((gradedMul B p q x y : B.grading (p + q)) : B.A) = (x : B.A) * (y : B.A) := rfl

/-- Multiplication of the sheaf of differential graded algebras attached to an inverse system:
over each object of the site it is the multiplication of the stage. -/
def systemMul (p q : ℤ) :
    SheafOfModules.BilinearMap ((systemComplex A).X p) ((systemComplex A).X q)
      ((systemComplex A).X (p + q)) where
  app U := gradedMul (A.obj U) p q
  map_smul_left U r x y :=
    Subtype.ext (smul_mul_assoc (show Λ from r) (Subtype.val x) (Subtype.val y))
  map_smul_right U r x y :=
    Subtype.ext (mul_smul_comm (show Λ from r) (Subtype.val x) (Subtype.val y))
  naturality {U V} f x y := Subtype.ext (map_mul (A.map f).toAlgebraHom _ _)

/-- The component of `systemMul A p q` at `U` is `gradedMul (A.obj U) p q`. -/
@[simp]
theorem systemMul_app (p q : ℤ) (U : Cᵒᵖ) :
    (systemMul A p q).app U = gradedMul (A.obj U) p q := rfl

/-- The unit of the sheaf of differential graded algebras attached to an inverse system. -/
def systemOne : ((systemComplex A).X 0).sections :=
  _root_.PresheafOfModules.sectionsMk (fun U => ⟨1, SetLike.one_mem_graded _⟩)
    (fun U V f => Subtype.ext (map_one (A.map f).toAlgebraHom))

/-- Transport along an equality of degrees does not change the underlying value. -/
theorem gradedCast_val {d₁ d₂ : ℤ} (h : d₁ = d₂) (U : Cᵒᵖ)
    (z : ((systemComplex A).X d₁).val.obj U) :
    Subtype.val (SheafOfModules.gradedCast
        (fun q => (((systemComplex A).X q).val.obj U : Type u)) h z) = Subtype.val z := by
  subst h
  rfl

/-- Two homogeneous elements of equal degree with the same underlying value are
heterogeneously equal. -/
theorem heq_grading {B : DifferentialGradedAlgebra.{u, u} Λ} {d₁ d₂ : ℤ} (h : d₁ = d₂)
    {x : B.grading d₁} {y : B.grading d₂} (hxy : (x : B.A) = (y : B.A)) : x ≍ y := by
  subst h
  exact heq_of_eq (Subtype.ext hxy)

/-- **An inverse system of differential graded `Λ`-algebras, realized as a sheaf of differential
graded algebras over the constant sheaf of rings on the chaotic site.** -/
def systemAlgebra :
    SheafOfModules.DifferentialGradedAlgebra.{u, u} (constRingSheaf (C := C) Λ) where
  complex := systemComplex A
  mul _ _ := systemMul A _ _
  one := systemOne A
  mul_assoc p q r U x y z := heq_grading (add_assoc p q r) (mul_assoc _ _ _)
  one_mul p U x := heq_grading (zero_add p) (one_mul _)
  mul_one p U x := heq_grading (add_zero p) (mul_one _)
  leibniz n i U x y := by
    have hd : ∀ (p : ℤ) (z : ((systemComplex A).X p).val.obj U),
        Subtype.val (((systemComplex A).d p (p + 1)).val.app U z)
          = (A.obj U).d (Subtype.val z) := by
      intro p z
      rw [systemComplex_d_val_app]
      rfl
    have hmul : ∀ (p q : ℤ) (a : ((systemComplex A).X p).val.obj U)
        (b : ((systemComplex A).X q).val.obj U),
        Subtype.val ((systemMul A p q).app U a b)
          = Subtype.val a * Subtype.val b := fun _ _ _ _ => rfl
    have hadd : ∀ (d : ℤ) (a b : ((systemComplex A).X d).val.obj U),
        Subtype.val (a + b) = Subtype.val a + Subtype.val b := fun _ _ _ => rfl
    have hsmul : ∀ (d m : ℤ) (a : ((systemComplex A).X d).val.obj U),
        Subtype.val (m • a) = m • Subtype.val a := fun _ _ _ => rfl
    refine Subtype.ext ?_
    simp only [hd, hmul, hadd, hsmul, gradedCast_val]
    exact (A.obj U).leibniz n i (Subtype.val x) (Subtype.val y) x.2 y.2

end Stacks.ChaoticSite

end
