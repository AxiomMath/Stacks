module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedForgetLimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopy
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeLimits

/-!
# Homotopies into a product of differential graded modules

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded
`R`-algebras. Two morphisms of right differential graded `A`-modules into a product which
become homotopic after every projection are homotopic.

This is the step that makes the homotopy category inherit products from the category of right
differential graded modules, and it is used both for the existence of products in the homotopy
category and for the stability of K-injectivity under products.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.homotopyIntoProduct` assembles a homotopy into a
  product out of a family of homotopies into its factors.

## Implementation notes

The components of a homotopy are morphisms of sheaves of modules, so the family of homotopies
can be glued by the universal property of the product *in each homogeneous degree*. That the
product of right differential graded modules is a product degreewise is
`productDegreeLimit`: forgetting the differential commutes with limits because it is a right
adjoint, and taking a homogeneous component of a graded module commutes with limits because
limits of sheaves of modules are degreewise and sectionwise.

The homotopy equation of the assembled homotopy is then checked degreewise by the same
universal property, and its compatibility with the action of `A` is checked on sections, one
factor at a time, using `CategoryTheory.Limits.Concrete.isLimit_ext` to separate the factors.
The two sides of that compatibility live in the propositionally — but not definitionally —
equal degrees `(n + i) - 1` and `(n - 1) + i`, so it is stated with `HEq` and proved through
`cast`; `sheaf_eqToHom_app_cast` identifies the action on sections of an `eqToHom` between
sheaves of modules with the corresponding `cast`.

The index type lies in the universe of the module sections, which is where the category of
right differential graded modules has its products.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of
a ringed site, and the universes of the site, the ring and the algebra pieces are independent;
a ringed site `X` is the case `R := X.ringSheaf`.

## References

* [Stacks Project, Tag 0FS2](https://stacks.math.columbia.edu/tag/0FS2)
* [Stacks Project, Tag 0FSV](https://stacks.math.columbia.edu/tag/0FSV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- A product of right differential graded modules is a product in each homogeneous degree. -/
noncomputable def productDegreeLimit {A : DifferentialGradedAlgebra.{t, a} R} {ι : Type m}
    (N : ι → DifferentialGradedModule.{t, a, m} A)
    (P : DifferentialGradedModule.{t, a, m} A) (π : ∀ i, P ⟶ N i)
    (hP : IsLimit (Fan.mk P π)) (n : ℤ) :
    IsLimit ((GradedModule.pieceFunctor A.toGradedAlgebra n).mapCone
      ((forgetToGradedModule A).mapCone (Fan.mk P π))) := by
  letI : PreservesLimitsOfShape (Discrete ι) (forgetToGradedModule.{t, a, m} A) :=
    inferInstance
  letI : PreservesLimitsOfShape (Discrete ι)
      (GradedModule.pieceFunctor.{t, a, m} A.toGradedAlgebra n) :=
    (GradedModule.pieceFunctor_preservesLimitsOfSize.{t, a, m}
      (A := A.toGradedAlgebra) n).preservesLimitsOfShape
  exact isLimitOfPreserves _ (isLimitOfPreserves _ hP)

/-- An `eqToHom` between sheaves of modules acts on sections as the corresponding transport. -/
theorem sheaf_eqToHom_app_cast {F G : SheafOfModules.{m} R}
    (e : F = G) (U : Cᵒᵖ) (x : (F.val.obj U).carrier) :
    ((eqToHom e).val.app U) x =
      cast (congrArg (fun H : SheafOfModules.{m} R => (H.val.obj U).carrier) e) x := by
  cases e
  rfl

/-- Two morphisms into a product of right differential graded modules which become homotopic
after every projection are homotopic. -/
noncomputable def homotopyIntoProduct {A : DifferentialGradedAlgebra.{t, a} R} {ι : Type m}
    {M : DifferentialGradedModule.{t, a, m} A}
    (N : ι → DifferentialGradedModule.{t, a, m} A)
    (P : DifferentialGradedModule.{t, a, m} A) (π : ∀ i, P ⟶ N i)
    (hP : IsLimit (Fan.mk P π)) {f g : M ⟶ P}
    (h : ∀ i, Homotopic (f ≫ π i) (g ≫ π i)) : Homotopy f g := by
  let hChosen : ∀ i, Homotopy (f ≫ π i) (g ≫ π i) := fun i => Classical.choice (h i)
  let H : ∀ n : ℤ, M.complex.X n ⟶ P.complex.X (n - 1) := fun n =>
    (productDegreeLimit N P π hP (n - 1)).lift
      { pt := M.complex.X n
        π := { app := fun i => (hChosen i.as).app n
               naturality := by
                 rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl⟩⟩
                 simp } }
  have hfac (n : ℤ) (i : ι) :
      H n ≫ (π i).toHomologicalComplex.f (n - 1) = (hChosen i).app n :=
    (productDegreeLimit N P π hP (n - 1)).fac _ ⟨i⟩
  refine ⟨H, ?_, ?_⟩
  · intro n i U x b
    let k : ℤ := n + i - 1
    let l : ℤ := (n - 1) + i
    have e : k = l := by dsimp [k, l]; omega
    let eP : ((P.complex.X l).val.obj U).carrier = ((P.complex.X k).val.obj U).carrier :=
      congrArg (fun q => ((P.complex.X q).val.obj U).carrier) e.symm
    let eN (j : ι) :
        (((N j).complex.X k).val.obj U).carrier = (((N j).complex.X l).val.obj U).carrier :=
      congrArg (fun q => (((N j).complex.X q).val.obj U).carrier) e
    let hs := isLimitOfPreserves (SheafOfModules.evaluation R U)
      (productDegreeLimit N P π hP k)
    have hEq :
        ((H (n + i)).val.app U ((M.mul n i).app U x b)) =
          cast eP ((P.mul (n - 1) i).app U ((H n).val.app U x) b) := by
      refine Concrete.isLimit_ext _ hs _ _ ?_
      intro j
      change ((π j.as).toHomologicalComplex.f k).val.app U
          ((H (n + i)).val.app U ((M.mul n i).app U x b)) =
        ((π j.as).toHomologicalComplex.f k).val.app U
          (cast eP ((P.mul (n - 1) i).app U ((H n).val.app U x) b))
      have hfacApp (q : ℤ) (z : (M.complex.X q).val.obj U) :
          ((π j.as).toHomologicalComplex.f (q - 1)).val.app U ((H q).val.app U z) =
            ((hChosen j.as).app q).val.app U z := by
        have hh := congrArg (fun φ : M.complex.X q ⟶ (N j.as).complex.X (q - 1) =>
          φ.val.app U z) (hfac q j.as)
        simpa only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
          ConcreteCategory.comp_apply] using hh
      have hcastMul :
          cast (eN j.as) (((hChosen j.as).app (n + i)).val.app U ((M.mul n i).app U x b)) =
            ((N j.as).mul (n - 1) i).app U (((hChosen j.as).app n).val.app U x) b :=
        cast_eq_iff_heq.mpr ((hChosen j.as).map_mul n i U x b)
      calc
        ((π j.as).toHomologicalComplex.f k).val.app U
            ((H (n + i)).val.app U ((M.mul n i).app U x b)) =
            ((hChosen j.as).app (n + i)).val.app U ((M.mul n i).app U x b) := by
              simpa [k] using hfacApp (n + i) ((M.mul n i).app U x b)
        _ = cast (eN j.as).symm (((N j.as).mul (n - 1) i).app U
              (((hChosen j.as).app n).val.app U x) b) := by
              simpa using congrArg (cast (eN j.as).symm) hcastMul
        _ = cast (eN j.as).symm (((π j.as).toHomologicalComplex.f l).val.app U
              ((P.mul (n - 1) i).app U ((H n).val.app U x) b)) := by
              congr 1
              rw [(π j.as).map_mul (n - 1) i U ((H n).val.app U x) b, hfacApp n x]
        _ = ((π j.as).toHomologicalComplex.f k).val.app U
              (cast eP ((P.mul (n - 1) i).app U ((H n).val.app U x) b)) := by
              have hnat := congrArg (fun φ : P.complex.X l ⟶ (N j.as).complex.X k =>
                φ.val.app U ((P.mul (n - 1) i).app U ((H n).val.app U x) b))
                (eqToHom_naturality (π j.as).toHomologicalComplex.f e.symm)
              simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
                ConcreteCategory.comp_apply] at hnat
              rw [sheaf_eqToHom_app_cast (congrArg (fun q => (N j.as).complex.X q) e.symm) U,
                sheaf_eqToHom_app_cast (congrArg (fun q => P.complex.X q) e.symm) U] at hnat
              simpa [eP, eN] using hnat
    apply heq_of_cast_eq eP.symm
    simpa using congrArg (cast eP.symm) hEq
  · intro n
    apply (productDegreeLimit N P π hP n).hom_ext
    intro j
    change (f.toHomologicalComplex.f n - g.toHomologicalComplex.f n) ≫
        (π j.as).toHomologicalComplex.f n =
      (H n ≫ P.complex.d (n - 1) n +
        M.complex.d n (n + 1) ≫ H (n + 1) ≫
          eqToHom (congrArg P.complex.X (show (n + 1) - 1 = n by omega))) ≫
        (π j.as).toHomologicalComplex.f n
    calc
      (f.toHomologicalComplex.f n - g.toHomologicalComplex.f n) ≫
          (π j.as).toHomologicalComplex.f n =
          (hChosen j.as).app n ≫ (N j.as).complex.d (n - 1) n +
            M.complex.d n (n + 1) ≫ (hChosen j.as).app (n + 1) ≫
              eqToHom (congrArg ((N j.as).complex.X)
                (show (n + 1) - 1 = n by omega)) := by
        rw [Preadditive.sub_comp]
        simpa only [comp_f, Category.assoc] using (hChosen j.as).comm n
      _ = (H n ≫ P.complex.d (n - 1) n +
            M.complex.d n (n + 1) ≫ H (n + 1) ≫
              eqToHom (congrArg P.complex.X (show (n + 1) - 1 = n by omega))) ≫
            (π j.as).toHomologicalComplex.f n := by
        rw [Preadditive.add_comp]
        apply congrArg₂ (· + ·)
        · rw [← hfac n j.as, Category.assoc, (π j.as).toHomologicalComplex.comm (n - 1) n,
            Category.assoc]
        · rw [← hfac (n + 1) j.as]
          simp only [Category.assoc]
          rw [eqToHom_naturality (π j.as).toHomologicalComplex.f (show (n + 1) - 1 = n by omega)]

end DifferentialGradedModule

end SheafOfModules
