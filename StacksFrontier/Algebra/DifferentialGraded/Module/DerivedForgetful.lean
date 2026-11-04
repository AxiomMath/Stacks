module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategory

/-! # The underlying complex of a differential graded module, read in derived categories

Let `(A, d)` be a differential graded algebra over a commutative ring `R`. A homomorphism of
right differential graded `A`-modules that is homotopic to another has the same image in the
derived category of cochain complexes of `R`-modules, and a quasi-isomorphism becomes invertible
there. So the underlying-complex functor
`DifferentialGradedModule.forgetToCochainComplex`, followed by the localization
`DerivedCategory.Q`, descends first to the homotopy category `K(A, d)` and then to the derived
category `D(A, d)`, giving the forgetful functor `D(A, d) ⥤ D(ModuleCat R)`. It is compatible
with taking cohomology: the cohomology of the image of a module is the cohomology of its
underlying complex.

## Main definitions

* `DifferentialGradedModule.forgetHomotopyToDerivedCategory`: the underlying-complex functor on
  the homotopy category, `K(A, d) ⥤ D(ModuleCat R)`.
* `DifferentialGradedModule.derivedForget`: the forgetful functor `D(A, d) ⥤ D(ModuleCat R)`.

## Main results

* `DifferentialGradedModule.Q_map_toCochainMap_eq_of_homotopy`: homotopic homomorphisms have the
  same image in `D(ModuleCat R)`.
* `DifferentialGradedModule.quasiIsomorphisms_isInvertedBy_forgetHomotopyToDerivedCategory`: the
  quasi-isomorphisms of `K(A, d)` are inverted by the underlying-complex functor.
* `DifferentialGradedModule.derivedForgetFactorization` and
  `DifferentialGradedModule.forgetHomotopyToDerivedCategoryIso`: the two descents commute with
  the localization and quotient functors up to canonical isomorphism.
* `DifferentialGradedModule.derivedForgetHomologyIso`: compatibility with cohomology.
* `DifferentialGradedModule.isIso_iff_isIso_derivedForget_map` and
  `DifferentialGradedModule.derivedForget_reflectsIsomorphisms`: a morphism of `D(A, d)` is
  invertible exactly when its underlying morphism of `D(ModuleCat R)` is, so the forgetful
  functor reflects isomorphisms.

## Implementation notes

The underlying complexes are taken over the base ring `R` rather than over `ℤ`. The derived
category `D(A, d)` is the localization `DifferentialGradedModule.derivedCategory'`; the
construction uses no triangulated structure.

The differential graded algebra and its modules are taken at a single universe, so the
underlying complexes are complexes of `ModuleCat.{u} R`; the universe of the morphisms of the
chosen derived category of those is free.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
* [Stacks Project, Tag 09KX](https://stacks.math.columbia.edu/tag/09KX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- Homotopic homomorphisms of differential graded modules have the same image in the derived
category of cochain complexes. -/
theorem Q_map_toCochainMap_eq_of_homotopy {M N : DifferentialGradedModule.{u, u, u} A}
    {f g : M ⟶ N} (h : Homotopy f g) :
    DerivedCategory.Q.map ((forgetToCochainComplex A).map f) =
      DerivedCategory.Q.map ((forgetToCochainComplex A).map g) := by
  have hq : (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map
        ((forgetToCochainComplex A).map f) =
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map
        ((forgetToCochainComplex A).map g) :=
    HomotopyCategory.eq_of_homotopy _ _ (underlyingHomotopy A h)
  have h₁ := DerivedCategory.quotientCompQhIso_hom_naturality ((forgetToCochainComplex A).map f)
  have h₂ := DerivedCategory.quotientCompQhIso_hom_naturality ((forgetToCochainComplex A).map g)
  rw [hq] at h₁
  rw [h₁] at h₂
  exact (cancel_epi ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app _)).mp h₂

/-- The underlying complex of a differential graded module, read in the derived category of
cochain complexes of `R`-modules, as a functor on the homotopy category `K(A, d)`. -/
def forgetHomotopyToDerivedCategory :
    HomotopyCategory.{u, u, u} A ⥤ DerivedCategory (ModuleCat.{u} R) :=
  CategoryTheory.Quotient.lift (homotopyRel A) (forgetToCochainComplex A ⋙ DerivedCategory.Q)
    (fun _ _ _ _ h => Q_map_toCochainMap_eq_of_homotopy A h.some)

/-- Reading a differential graded module in `D(ModuleCat R)` through the homotopy category gives
its underlying complex. -/
def forgetHomotopyToDerivedCategoryIso :
    toHomotopyCategory.{u, u, u} A ⋙ forgetHomotopyToDerivedCategory A ≅
      forgetToCochainComplex A ⋙ DerivedCategory.Q :=
  CategoryTheory.Quotient.lift.isLift _ _ _

/-- The quasi-isomorphisms of `K(A, d)` are inverted by the underlying-complex functor into
`D(ModuleCat R)`. -/
theorem quasiIsomorphisms_isInvertedBy_forgetHomotopyToDerivedCategory :
    (quasiIsomorphisms' A).IsInvertedBy (forgetHomotopyToDerivedCategory A) := by
  rintro ⟨M⟩ ⟨N⟩ f hf
  induction f using Quot.inductionOn with
  | h g =>
    have : QuasiIso ((forgetToCochainComplex A).map g) := hf g rfl
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map ((forgetToCochainComplex A).map g)))

/-- The forgetful functor `D(A, d) ⥤ D(ModuleCat R)`: the underlying complex of a differential
graded module, descended through the localization at the quasi-isomorphisms. -/
def derivedForget : derivedCategory' A ⥤ DerivedCategory (ModuleCat.{u} R) :=
  Localization.lift (forgetHomotopyToDerivedCategory A)
    (quasiIsomorphisms_isInvertedBy_forgetHomotopyToDerivedCategory A) (quasiIsomorphisms' A).Q

/-- The forgetful functor on derived categories, precomposed with the localization functor
`K(A, d) ⥤ D(A, d)`, is the underlying-complex functor on `K(A, d)`. -/
def derivedForgetFactorization :
    (quasiIsomorphisms' A).Q ⋙ derivedForget A ≅ forgetHomotopyToDerivedCategory A :=
  Localization.fac _ (quasiIsomorphisms_isInvertedBy_forgetHomotopyToDerivedCategory A) _

/-- The forgetful functor `D(A, d) ⥤ D(ModuleCat R)` is compatible with taking cohomology: the
degree-`n` cohomology of the image of a differential graded module is the degree-`n` cohomology
of its underlying complex. -/
def derivedForgetHomologyIso (n : ℤ) :
    toHomotopyCategory.{u, u, u} A ⋙ (quasiIsomorphisms' A).Q ⋙ derivedForget A ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} R) n ≅
      forgetToCochainComplex A ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n :=
  Functor.isoWhiskerLeft (toHomotopyCategory.{u, u, u} A)
      (Functor.isoWhiskerRight (derivedForgetFactorization A)
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n)) ≪≫
    Functor.isoWhiskerRight (forgetHomotopyToDerivedCategoryIso A)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n) ≪≫
    Functor.isoWhiskerLeft (forgetToCochainComplex A)
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n)

/-- A morphism of `D(A, d)` is invertible exactly when the morphism it induces on underlying
complexes in `D(ModuleCat R)` is invertible. -/
theorem isIso_iff_isIso_derivedForget_map {X Y : derivedCategory' A} (φ : X ⟶ Y) :
    IsIso φ ↔ IsIso ((derivedForget A).map φ) := by
  refine ⟨fun _ => inferInstance, fun h => ?_⟩
  have := Localization.essSurj (quasiIsomorphisms' A).Q (quasiIsomorphisms' A)
  set eX := (quasiIsomorphisms' A).Q.objObjPreimageIso X with hEX
  set eY := (quasiIsomorphisms' A).Q.objObjPreimageIso Y with hEY
  obtain ⟨α, hα⟩ := Localization.exists_leftFraction (quasiIsomorphisms' A).Q
    (quasiIsomorphisms' A) (eX.hom ≫ φ ≫ eY.inv)
  have hfac : (eX.hom ≫ φ ≫ eY.inv) ≫ (quasiIsomorphisms' A).Q.map α.s =
      (quasiIsomorphisms' A).Q.map α.f := by
    rw [hα]
    exact MorphismProperty.LeftFraction.map_comp_map_s α _ _
  have hs : IsIso ((quasiIsomorphisms' A).Q.map α.s) :=
    Localization.inverts (quasiIsomorphisms' A).Q (quasiIsomorphisms' A) _ α.hs
  have hUf : IsIso ((derivedForget A).map ((quasiIsomorphisms' A).Q.map α.f)) := by
    rw [← hfac]
    simp only [Functor.map_comp]
    infer_instance
  have hf : quasiIsomorphisms' A α.f := by
    intro g hg
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
    refine (NatIso.isIso_map_iff (forgetHomotopyToDerivedCategoryIso A) g).mp ?_
    show IsIso ((forgetHomotopyToDerivedCategory A).map
      ((toHomotopyCategory.{u, u, u} A).map g))
    rw [hg]
    exact (NatIso.isIso_map_iff (derivedForgetFactorization A) α.f).mp hUf
  have hfiso : IsIso ((quasiIsomorphisms' A).Q.map α.f) :=
    Localization.inverts (quasiIsomorphisms' A).Q (quasiIsomorphisms' A) _ hf
  have hmid : IsIso (eX.hom ≫ φ ≫ eY.inv) := by
    have : IsIso ((eX.hom ≫ φ ≫ eY.inv) ≫ (quasiIsomorphisms' A).Q.map α.s) := by
      rwa [hfac]
    exact IsIso.of_isIso_comp_right _ ((quasiIsomorphisms' A).Q.map α.s)
  have hφ : φ = eX.inv ≫ (eX.hom ≫ φ ≫ eY.inv) ≫ eY.hom := by simp
  rw [hφ]
  infer_instance

/-- The forgetful functor `D(A, d) ⥤ D(ModuleCat R)` reflects isomorphisms. -/
instance derivedForget_reflectsIsomorphisms : (derivedForget A).ReflectsIsomorphisms where
  reflects φ _ := (isIso_iff_isIso_derivedForget_map A φ).mpr inferInstance

end DifferentialGradedModule

end
