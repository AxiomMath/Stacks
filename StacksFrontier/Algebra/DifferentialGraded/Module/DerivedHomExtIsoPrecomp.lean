module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomExtIso
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomPrecomposition
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomPrecompositionCohomology
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomPrecompositionShift
public import StacksCore.Tactic.StacksAttribute

/-! # Tag 0CS5: the identification of derived Hom cohomology with Ext is natural in the bimodule

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R`. For a
differential graded `(A, B)`-bimodule `N`, Tag 0CS5 identifies

`H^n(RHom(N, -)) = Ext^n_{D(B,d)}(N, -) = Hom_{D(B,d)}(N, (-)[n])`

and asserts that the identification is natural in the target — which is
`DifferentialGradedModule.extLinearEquiv_naturality` — *and* contravariantly functorial in the
bimodule with respect to the operation of Tag 0BYV. This file proves the second assertion, which
is the remaining clause of Tag 0CS5.

## Main definitions

* `DifferentialGraded.Bimodule.extFunctorPrecomp`: precomposition with a homomorphism of
  bimodules on `Ext^n_{D(B,d)}(-, -)`, as a transformation of the functors
  `DifferentialGradedModule.extFunctor`.

## Main results

* `DifferentialGraded.Bimodule.extLinearEquiv_derivedPrecomp`: **Stacks 0CS5**, the clause that
  the identification is compatible with Tag 0BYV. A cohomology class of derived Hom out of `N`,
  pulled back along `f : M ⟶ N`, is the corresponding `Ext`-class precomposed with the image of
  `f` in `D(B, d)`.
* `DifferentialGraded.Bimodule.extIso_derivedPrecomp`: the same as a square of natural
  transformations on `D(B, d)`.

## Implementation notes

*Why the universal property does the work.* The two identifications being compared are
`DifferentialGradedModule.extIso`, which is not constructed but obtained from the universal
property of a right derived functor, so the only way to compare transformations out of it is
`CategoryTheory.Functor.rightDerived_ext`: two transformations out of
`H^n(RHom(N, -))` agree as soon as they agree after restriction along the localization and
composition with the comparison map. Doing that, and using
`DifferentialGradedModule.extIso_fac` on both sides, replaces the square on `D(B, d)` by a square
on `K(B, d)` between the *comparison maps* `DifferentialGradedModule.extComparisonUnit`, which are
explicit. This is
`DifferentialGraded.Bimodule.extComparisonUnit_precompToDerivedNatTrans`.

*What the square on `K(B, d)` needs.* The comparison map is a composite of three pieces
(`DifferentialGradedModule.extComparisonUnit_app`), so the square splits into three:

* the piece built from Tag 09LC and Tag 0FQR, which needs those two results to be natural in the
  bimodule — `DifferentialGraded.Bimodule.homCohomologyZeroNatIso_precompHomotopyNatTrans` and
  `DifferentialGraded.Bimodule.homHomotopyCategoryFunctorShiftIso_precompHomotopyNatTrans`,
  proved in the two files of the same name prefix;
* the localization map on morphism modules, where the square is the functoriality of the
  localization functor;
* the transport of the shift across the localization, where the square is the naturality of
  precomposition on the co-Yoneda functors of `D(B, d)`.

*Why two of the isomorphisms have their components read off by `rfl` rather than by `simp`.* The
isomorphisms `DifferentialGradedModule.homShiftCohomologyUliftIso` and
`DifferentialGradedModule.extFunctorRestrictedIso` are isomorphisms of functors into
`ModuleCat.{u + 1} R` out of a category whose morphisms are in `Type u`, so the hom-universe of
the functor category is a `max` in which the section universe occurs only inside that `max`; a
rewrite then leaves it as a metavariable, and `CategoryTheory.Iso.trans_hom` does not fire on
their bodies, on a goal that prints correctly. Their components are therefore recorded here as
`rfl` lemmas — `DifferentialGraded.Bimodule.homShiftCohomologyUliftIso_hom_app` and
`DifferentialGraded.Bimodule.extFunctorRestrictedIso_inv_app` — and used in place of unfolding.
`DifferentialGradedModule.homShiftCohomologyIso`, whose target is in the single universe `u`, does
not have the problem.

*Why `DifferentialGraded.Bimodule.precompShiftCohomologyNatTrans` exists.* Same family of issue,
one level down: the functor being derived has two spellings that agree only at default
transparency, so the composite of precomposition with the comparison map is not type-correct at
`implicit` transparency unless precomposition is given at the spelling the comparison map uses.
Naming it once is the fix; see its own docstring.

## References

* [Stacks Project, Tag 0CS5](https://stacks.math.columbia.edu/tag/0CS5); the functoriality in the
  bimodule is [Tag 0BYV](https://stacks.math.columbia.edu/tag/0BYV), the derived Hom functor is
  [Tag 09LI](https://stacks.math.columbia.edu/tag/09LI), and the two underived naturality inputs
  are [Tag 09LC](https://stacks.math.columbia.edu/tag/09LC) and
  [Tag 0FQR](https://stacks.math.columbia.edu/tag/0FQR).
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R} {M N : Bimodule A B}

/-! ### Precomposition on `Ext` -/

/-- Precomposition with a homomorphism of differential graded `(A, B)`-bimodules, on the
`R`-linear co-Yoneda functors of the derived category `D(B, d)`. -/
def coyonedaPrecompDerivedCategory (f : M ⟶ N) :
    (linearCoyoneda R (derivedCategory' B)).obj
        (Opposite.op ((quasiIsomorphisms' B).Q.obj
          ((toHomotopyCategory B).obj N.rightModule))) ⟶
      (linearCoyoneda R (derivedCategory' B)).obj
        (Opposite.op ((quasiIsomorphisms' B).Q.obj
          ((toHomotopyCategory B).obj M.rightModule))) :=
  (linearCoyoneda R (derivedCategory' B)).map
    ((quasiIsomorphisms' B).Q.map ((toHomotopyCategory B).map f.rightHom)).op

/-- **Precomposition on `Ext`.** A homomorphism `f : M ⟶ N` of differential graded
`(A, B)`-bimodules induces `Ext^n_{D(B,d)}(N, -) ⟹ Ext^n_{D(B,d)}(M, -)`, by composing with the
image of `f` in `D(B, d)`. -/
def extFunctorPrecomp (f : M ⟶ N) (n : ℤ) :
    extFunctor B N.rightModule n ⟶ extFunctor B M.rightModule n :=
  Functor.whiskerLeft (CategoryTheory.shiftFunctor (derivedCategory' B) n)
    (coyonedaPrecompDerivedCategory f)

/-- Precomposition on the functor whose right derived functor is degree-`n` cohomology of derived
Hom, spelled at `DifferentialGradedModule.homShiftCohomologyFunctor`.

The spelling matters: that functor is equal to internal hom read in `D(A, d)` followed by
degree-`n` cohomology only by unfolding at default transparency, so a composite written with
`CategoryTheory.Functor.whiskerRight (precompToDerivedNatTrans f) _` in place of this is not
type-correct at `implicit` transparency and no rewrite fires in it. -/
def precompShiftCohomologyNatTrans (f : M ⟶ N) (n : ℤ) :
    homShiftCohomologyFunctor A B N.rightModule N.leftAction n ⟶
      homShiftCohomologyFunctor A B M.rightModule M.leftAction n :=
  Functor.whiskerRight (precompToDerivedNatTrans f) (extCohomologyFunctor A n)

/-- The component of `DifferentialGraded.Bimodule.precompShiftCohomologyNatTrans`. -/
theorem precompShiftCohomologyNatTrans_app (f : M ⟶ N) (n : ℤ) (X : HomotopyCategory B) :
    (precompShiftCohomologyNatTrans f n).app X =
      (extCohomologyFunctor A n).map
        ((quasiIsomorphisms' A).Q.map ((precompHomotopyNatTrans f).app X)) :=
  rfl

/-! ### The components of the two universe-mixing isomorphisms -/

/-- The component of `DifferentialGradedModule.homShiftCohomologyUliftIso` is the universe lift of
the component of `DifferentialGradedModule.homShiftCohomologyIso`. -/
theorem homShiftCohomologyUliftIso_hom_app (L : Bimodule A B) (n : ℤ) (X : HomotopyCategory B) :
    (homShiftCohomologyUliftIso A B L.rightModule L.leftAction n).hom.app X =
      (ModuleCat.uliftFunctor.{u + 1, u} R).map
        ((homShiftCohomologyIso A B L.rightModule L.leftAction n).hom.app X) :=
  rfl

/-- The component of `DifferentialGradedModule.extFunctorRestrictedIso` is the co-Yoneda functor
applied to the comparison of the localization with the shift. -/
theorem extFunctorRestrictedIso_inv_app (L : Bimodule A B) (n : ℤ) (X : HomotopyCategory B) :
    (extFunctorRestrictedIso B L.rightModule n).inv.app X =
      ((linearCoyoneda R (derivedCategory' B)).obj
          (Opposite.op ((quasiIsomorphisms' B).Q.obj
            ((toHomotopyCategory B).obj L.rightModule)))).map
        (((quasiIsomorphisms' B).Q.commShiftIso n).hom.app X) :=
  rfl

/-- Degree-`n` cohomology on `D(A, d)` with values in the universe of the morphism modules of a
derived category is the shift followed by degree-zero cohomology, lifted. -/
theorem extCohomologyFunctor_map (n : ℤ) {X Y : derivedCategory' A} (g : X ⟶ Y) :
    (extCohomologyFunctor A n).map g =
      (ModuleCat.uliftFunctor.{u + 1, u} R).map
        ((degreeZeroCohomologyOnLocalization' A).map
          ((CategoryTheory.shiftFunctor (derivedCategory' A) n).map g)) :=
  rfl

/-! ### The square on the homotopy category -/

/-- A functor carries a commuting square to a commuting square. -/
private theorem map_comp_eq_map_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {W X Y Z : C} {f : W ⟶ X} {g : X ⟶ Z} {f' : W ⟶ Y} {g' : Y ⟶ Z} (h : f ≫ g = f' ≫ g') :
    F.map f ≫ F.map g = F.map f' ≫ F.map g' := by
  rw [← F.map_comp, ← F.map_comp, h]

/-- **Tags 09LC and 0FQR are natural in the bimodule, as they enter Tag 0CS5.** The identification
of degree-`n` cohomology of ordinary internal hom with the `n`-shifted morphism module of
`K(B, d)` carries precomposition by a homomorphism of differential graded bimodules to
precomposition on morphism modules.

The four squares composed here are the naturality of
`CategoryTheory.Functor.commShiftIso` of the localization, the naturality of
`DifferentialGradedModule.degreeZeroCohomologyOnLocalizationIso'`, Tag 0FQR in the bimodule and
Tag 09LC in the bimodule. -/
theorem homShiftCohomologyIso_precompHomotopyNatTrans (f : M ⟶ N) (n : ℤ)
    (X : HomotopyCategory B) :
    (degreeZeroCohomologyOnLocalization' A).map
          ((CategoryTheory.shiftFunctor (derivedCategory' A) n).map
            ((quasiIsomorphisms' A).Q.map ((precompHomotopyNatTrans f).app X))) ≫
        (homShiftCohomologyIso A B M.rightModule M.leftAction n).hom.app X =
      (homShiftCohomologyIso A B N.rightModule N.leftAction n).hom.app X ≫
        (coyonedaPrecompHomotopyCategory f).app
          ((CategoryTheory.shiftFunctor (HomotopyCategory B) n).obj X) := by
  have c1 : (degreeZeroCohomologyOnLocalization' A).map
        ((CategoryTheory.shiftFunctor (derivedCategory' A) n).map
          ((quasiIsomorphisms' A).Q.map ((precompHomotopyNatTrans f).app X))) ≫
      (degreeZeroCohomologyOnLocalization' A).map
        (((quasiIsomorphisms' A).Q.commShiftIso n).inv.app
          ((homHomotopyCategoryFunctor A B M.rightModule M.leftAction).obj X)) =
      (degreeZeroCohomologyOnLocalization' A).map
        (((quasiIsomorphisms' A).Q.commShiftIso n).inv.app
          ((homHomotopyCategoryFunctor A B N.rightModule N.leftAction).obj X)) ≫
      (degreeZeroCohomologyOnLocalization' A).map
        ((quasiIsomorphisms' A).Q.map
          ((CategoryTheory.shiftFunctor (HomotopyCategory A) n).map
            ((precompHomotopyNatTrans f).app X))) := by
    exact map_comp_eq_map_comp _ (((quasiIsomorphisms' A).Q.commShiftIso n).inv.naturality
      ((precompHomotopyNatTrans f).app X))
  have c2 : (degreeZeroCohomologyOnLocalization' A).map
        ((quasiIsomorphisms' A).Q.map
          ((CategoryTheory.shiftFunctor (HomotopyCategory A) n).map
            ((precompHomotopyNatTrans f).app X))) ≫
      (degreeZeroCohomologyOnLocalizationIso' A).hom.app
        ((CategoryTheory.shiftFunctor (HomotopyCategory A) n).obj
          ((homHomotopyCategoryFunctor A B M.rightModule M.leftAction).obj X)) =
      (degreeZeroCohomologyOnLocalizationIso' A).hom.app
        ((CategoryTheory.shiftFunctor (HomotopyCategory A) n).obj
          ((homHomotopyCategoryFunctor A B N.rightModule N.leftAction).obj X)) ≫
      (degreeZeroCohomologyOnHomotopy' A).map
        ((CategoryTheory.shiftFunctor (HomotopyCategory A) n).map
          ((precompHomotopyNatTrans f).app X)) :=
    (degreeZeroCohomologyOnLocalizationIso' A).hom.naturality
      ((CategoryTheory.shiftFunctor (HomotopyCategory A) n).map
        ((precompHomotopyNatTrans f).app X))
  have h0FQR := NatTrans.congr_app
    (homHomotopyCategoryFunctorShiftIso_precompHomotopyNatTrans f n) X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h0FQR
  have c3 : (degreeZeroCohomologyOnHomotopy' A).map
        ((CategoryTheory.shiftFunctor (HomotopyCategory A) n).map
          ((precompHomotopyNatTrans f).app X)) ≫
      (degreeZeroCohomologyOnHomotopy' A).map
        ((homHomotopyCategoryFunctorShiftIso A B M.rightModule M.leftAction n).hom.app X) =
      (degreeZeroCohomologyOnHomotopy' A).map
        ((homHomotopyCategoryFunctorShiftIso A B N.rightModule N.leftAction n).hom.app X) ≫
      (degreeZeroCohomologyOnHomotopy' A).map
        ((precompHomotopyNatTrans f).app
          ((CategoryTheory.shiftFunctor (HomotopyCategory B) n).obj X)) := by
    exact map_comp_eq_map_comp _ h0FQR
  have c4 := NatTrans.congr_app (homCohomologyZeroNatIso_precompHomotopyNatTrans f)
    ((CategoryTheory.shiftFunctor (HomotopyCategory B) n).obj X)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at c4
  simp only [homShiftCohomologyIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc]
  rw [← Category.assoc, c1, Category.assoc,
    ← Category.assoc ((degreeZeroCohomologyOnLocalization' A).map
      ((quasiIsomorphisms' A).Q.map
        ((CategoryTheory.shiftFunctor (HomotopyCategory A) n).map
          ((precompHomotopyNatTrans f).app X)))), c2, Category.assoc,
    ← Category.assoc ((degreeZeroCohomologyOnHomotopy' A).map
      ((CategoryTheory.shiftFunctor (HomotopyCategory A) n).map
        ((precompHomotopyNatTrans f).app X))), c3, Category.assoc, c4]

/-- The localization map on morphism modules carries precomposition on `K(B, d)` to precomposition
on `D(B, d)`: this is the functoriality of the localization functor. -/
theorem coyonedaLocalizationMap_coyonedaPrecomp (f : M ⟶ N) (Y : HomotopyCategory B) :
    (ModuleCat.uliftFunctor.{u + 1, u} R).map ((coyonedaPrecompHomotopyCategory f).app Y) ≫
        (coyonedaLocalizationMap B M.rightModule).app Y =
      (coyonedaLocalizationMap B N.rightModule).app Y ≫
        (coyonedaPrecompDerivedCategory f).app ((quasiIsomorphisms' B).Q.obj Y) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun g => ?_)
  exact (quasiIsomorphisms' B).Q.map_comp ((toHomotopyCategory B).map f.rightHom) g.down

/-- Precomposition on `Ext` is compatible with the transport of the shift across the
localization. -/
theorem extFunctorRestrictedIso_extFunctorPrecomp (f : M ⟶ N) (n : ℤ) (X : HomotopyCategory B) :
    (coyonedaPrecompDerivedCategory f).app
          ((quasiIsomorphisms' B).Q.obj
            ((CategoryTheory.shiftFunctor (HomotopyCategory B) n).obj X)) ≫
        (extFunctorRestrictedIso B M.rightModule n).inv.app X =
      (extFunctorRestrictedIso B N.rightModule n).inv.app X ≫
        (extFunctorPrecomp f n).app ((quasiIsomorphisms' B).Q.obj X) := by
  rw [extFunctorRestrictedIso_inv_app M, extFunctorRestrictedIso_inv_app N, extFunctorPrecomp,
    Functor.whiskerLeft_app]
  exact ((coyonedaPrecompDerivedCategory f).naturality
    (((quasiIsomorphisms' B).Q.commShiftIso n).hom.app X)).symm

/-- **The comparison map of Tag 0CS5 is natural in the bimodule.** On `K(B, d)`, the comparison
from degree-`n` cohomology of ordinary internal hom to `Ext^n_{D(B,d)}` carries precomposition
with a homomorphism of differential graded bimodules to precomposition on `Ext`. -/
theorem extComparisonUnit_precompToDerivedNatTrans (f : M ⟶ N) (n : ℤ) :
    precompShiftCohomologyNatTrans f n ≫ extComparisonUnit A B M.rightModule M.leftAction n =
      extComparisonUnit A B N.rightModule N.leftAction n ≫
        Functor.whiskerLeft (quasiIsomorphisms' B).Q (extFunctorPrecomp f n) := by
  ext X : 2
  have ha : (precompShiftCohomologyNatTrans f n).app X ≫
        (homShiftCohomologyUliftIso A B M.rightModule M.leftAction n).hom.app X =
      (homShiftCohomologyUliftIso A B N.rightModule N.leftAction n).hom.app X ≫
      (ModuleCat.uliftFunctor.{u + 1, u} R).map ((coyonedaPrecompHomotopyCategory f).app
        ((CategoryTheory.shiftFunctor (HomotopyCategory B) n).obj X)) := by
    rw [homShiftCohomologyUliftIso_hom_app, homShiftCohomologyUliftIso_hom_app]
    exact map_comp_eq_map_comp (ModuleCat.uliftFunctor.{u + 1, u} R)
      (homShiftCohomologyIso_precompHomotopyNatTrans f n X)
  have hb := coyonedaLocalizationMap_coyonedaPrecomp f
    ((CategoryTheory.shiftFunctor (HomotopyCategory B) n).obj X)
  have hc := extFunctorRestrictedIso_extFunctorPrecomp f n X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, extComparisonUnit_app, Category.assoc]
  rw [← Category.assoc, ha, Category.assoc,
    ← Category.assoc ((ModuleCat.uliftFunctor.{u + 1, u} R).map
      ((coyonedaPrecompHomotopyCategory f).app
        ((CategoryTheory.shiftFunctor (HomotopyCategory B) n).obj X))), hb, Category.assoc, hc]

/-! ### The square on the derived category -/

/-- The component of the comparison map of Tag 09LI followed by degree-`n` cohomology. -/
theorem extCohomologyComparisonUnit_app (L : Bimodule A B)
    (D : DerivedHomData A B L.rightModule L.leftAction) (n : ℤ) (X : HomotopyCategory B) :
    (extCohomologyComparisonUnit A B L.rightModule L.leftAction D n).app X =
      (extCohomologyFunctor A n).map (D.comparison.app X) :=
  Category.comp_id _

/-- The comparison map from degree-`n` cohomology of ordinary internal hom to degree-`n`
cohomology of derived Hom is natural in the bimodule. -/
theorem extCohomologyComparisonUnit_derivedPrecomp
    (DN : DerivedHomData A B N.rightModule N.leftAction)
    (DM : DerivedHomData A B M.rightModule M.leftAction) (f : M ⟶ N) (n : ℤ) :
    extCohomologyComparisonUnit A B N.rightModule N.leftAction DN n ≫
        Functor.whiskerLeft (quasiIsomorphisms' B).Q
          (Functor.whiskerRight (derivedPrecomp DN DM f) (extCohomologyFunctor A n)) =
      precompShiftCohomologyNatTrans f n ≫
        extCohomologyComparisonUnit A B M.rightModule M.leftAction DM n := by
  ext X : 2
  have h := NatTrans.congr_app (derivedPrecomp_comparison DN DM f) X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    extCohomologyComparisonUnit_app]
  exact map_comp_eq_map_comp _ h

/-- **Stacks 0CS5, the compatibility with Tag 0BYV, as a square of functors.** The identification
of degree-`n` cohomology of derived Hom with `Ext^n_{D(B,d)}` carries the transformation of
derived Hom functors induced by a homomorphism `f : M ⟶ N` of differential graded
`(A, B)`-bimodules to precomposition with the image of `f` in `D(B, d)`. -/
theorem extIso_derivedPrecomp (DN : DerivedHomData A B N.rightModule N.leftAction)
    (DM : DerivedHomData A B M.rightModule M.leftAction) (f : M ⟶ N) (n : ℤ) :
    Functor.whiskerRight (derivedPrecomp DN DM f) (extCohomologyFunctor A n) ≫
        (extIso A B M.rightModule M.leftAction DM n).hom =
      (extIso A B N.rightModule N.leftAction DN n).hom ≫ extFunctorPrecomp f n := by
  have := isRightDerivedFunctor_extCohomologyComparisonUnit A B N.rightModule N.leftAction DN n
  refine Functor.rightDerived_ext (DN.functor ⋙ extCohomologyFunctor A n)
    (extCohomologyComparisonUnit A B N.rightModule N.leftAction DN n) (quasiIsomorphisms' B)
    (extFunctor B M.rightModule n) _ _ ?_
  rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp, ← Category.assoc, ← Category.assoc,
    extCohomologyComparisonUnit_derivedPrecomp, Category.assoc,
    extIso_fac A B M.rightModule M.leftAction DM n,
    extIso_fac A B N.rightModule N.leftAction DN n,
    extComparisonUnit_precompToDerivedNatTrans]

/-! ### Tag 0CS5, clause (iii) -/

-- NO `extCohomologyFunctor_map_up` HERE. It stated exactly the `private theorem` of the same
-- name at `StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomExtIso.lean`:239, which this
-- module imports -- same binders, same statement, same `rfl` proof. This copy had no use in
-- this file, so it was dead as well as duplicated and nothing needed repointing.

/-- `Ext^n_{D(B,d)}(N, -) ⟹ Ext^n_{D(B,d)}(M, -)` acts by precomposition with the image of `f`. -/
private theorem extFunctorPrecomp_app_apply (f : M ⟶ N) (n : ℤ) (P : derivedCategory' B)
    (y : (quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj N.rightModule) ⟶ P⟦n⟧) :
    (extFunctorPrecomp f n).app P y =
      (quasiIsomorphisms' B).Q.map ((toHomotopyCategory B).map f.rightHom) ≫ y :=
  rfl

/-- **Stacks 0CS5, the clause asserting compatibility with Tag 0BYV.** For a homomorphism
`f : M ⟶ N` of differential graded `(A, B)`-bimodules, the identification of Tag 0CS5 carries the
pullback along `f` of a degree-`n` cohomology class of derived Hom out of `N` — the transformation
of Tag 0BYV, `DifferentialGraded.Bimodule.derivedPrecomp` — to the `Ext`-class of `N` composed
with the image of `f` in `D(B, d)`.

Together with `DifferentialGradedModule.extIso` and
`DifferentialGradedModule.extLinearEquiv_naturality` this completes Tag 0CS5. -/
@[stacks 0CS5 "the identification is natural in the bimodule, with respect to Tag 0BYV"]
theorem extLinearEquiv_derivedPrecomp (DN : DerivedHomData A B N.rightModule N.leftAction)
    (DM : DerivedHomData A B M.rightModule M.leftAction) (f : M ⟶ N) (n : ℤ)
    (P : derivedCategory' B)
    (x : (degreeZeroCohomologyOnLocalization' A).obj ((DN.functor.obj P)⟦n⟧)) :
    extLinearEquiv A B M.rightModule M.leftAction DM n P
        ((degreeZeroCohomologyOnLocalization' A).map
          (((derivedPrecomp DN DM f).app P)⟦n⟧') x) =
      (quasiIsomorphisms' B).Q.map ((toHomotopyCategory B).map f.rightHom) ≫
        extLinearEquiv A B N.rightModule N.leftAction DN n P x := by
  have h := NatTrans.congr_app (extIso_derivedPrecomp DN DM f n) P
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at h
  exact ConcreteCategory.congr_hom h (ULift.up x)

end DifferentialGraded.Bimodule

end
