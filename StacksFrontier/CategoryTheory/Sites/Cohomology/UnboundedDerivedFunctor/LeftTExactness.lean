module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
import StacksCore.Tactic.StacksAttribute

/-! # Left t-exactness of an unbounded right derived functor

Let `A` and `B` be abelian categories, `A` Grothendieck abelian with enough injectives, and let
`F : A ⥤ B` be an additive functor. The unbounded right derived functor `RF : D(A) ⥤ D(B)`
carries `D^{≥ n}(A)` into `D^{≥ n}(B)`: a derived object with no cohomology below degree `n` has
derived image with no cohomology below degree `n`.

The argument is the one the source gives for a single object, run on a complex. An object of
`D^{≥ n}(A)` is represented by a cochain complex whose cohomology vanishes below `n`, hence by
Tag 013K by an injective resolution whose terms vanish below `n` outright. A complex of
injectives that vanishes below some degree is K-injective, and the unit of `RF` is invertible at
a K-injective complex, so `RF` of the object is the image of that resolution under `F` applied
degreewise. An additive functor sends a zero object to a zero object, so that image again
vanishes below `n`, and a complex that vanishes below `n` has no cohomology below `n`.

Left exactness of `F` is not needed, only additivity, exactly as for the vanishing of `R ⁱ F` in
negative degrees.

## Main results

* `Stacks.DerivedFunctor.isGE_totalRightDerived_obj`: the unbounded right derived functor of an
  additive functor is left t-exact.
* `Stacks.DerivedFunctor.isZero_homology_totalRightDerived_obj`: the same, read as vanishing of
  the cohomology objects below the bound.

## Implementation notes

The statement is about the unbounded right derived functor
`(F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh`,
whose existence is automatic over a Grothendieck abelian source by
`Stacks.Cohomology.Localization.hasRightDerivedFunctorOfGrothendieck`; the bounded-below variants
in `StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective` are about
`CategoryTheory.Functor.rightDerivedFunctorPlus` on `D⁺` instead, and the unbounded statement
there (Tag 07K7) additionally assumes finite cohomological dimension, which is not available for
a general additive `F`.

`EnoughInjectives A` is what supplies the resolution of Tag 013K;
`IsGrothendieckAbelian A`, with its own universe, is what makes the derived functor exist and its
unit invertible on K-injective complexes.

## References

* [Stacks Project, Tag 013K](https://stacks.math.columbia.edu/tag/013K)
* [Stacks Project, Tag 013R](https://stacks.math.columbia.edu/tag/013R)
* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedFunctor

universe v u vB uB wG wD wE

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{wG} A]
  [EnoughInjectives A] [HasDerivedCategory.{wD} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wE} B]

/-- The functor on the homotopy category whose total right derived functor is the unbounded right
derived functor of `F`. -/
abbrev homotopyMap (F : A ⥤ B) [F.Additive] :
    HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory B :=
  F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The unbounded right derived functor of an additive functor between abelian categories, the
source being Grothendieck abelian. -/
@[sga "4½ Etat_0 4.2.3" "(a), right-derived case"]
abbrev totalRightDerived (F : A ⥤ B) [F.Additive] :
    DerivedCategory A ⥤ DerivedCategory B :=
  (homotopyMap F).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))

omit [IsGrothendieckAbelian.{wG} A] [EnoughInjectives A] [HasDerivedCategory.{wD} A]
  [HasDerivedCategory.{wE} B] in
/-- Applying an additive functor degreewise to a cochain complex that vanishes below `n` gives a
cochain complex that vanishes below `n`. -/
lemma isStrictlyGE_mapHomologicalComplex (F : A ⥤ B) [F.Additive]
    (X : CochainComplex A ℤ) (n : ℤ) [X.IsStrictlyGE n] :
    CochainComplex.IsStrictlyGE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) n := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact F.map_isZero (X.isZero_of_isStrictlyGE n i hi)

omit [EnoughInjectives A] in
/-- The unbounded right derived functor of `F` at a K-injective complex is `F` applied
degreewise, up to the canonical isomorphism. -/
lemma isIso_totalRightDerivedUnit_app_of_isKInjective (F : A ⥤ B) [F.Additive]
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    IsIso (((homotopyMap F).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))).app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) :=
  Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective (homotopyMap F)
    (totalRightDerived F)
    ((homotopyMap F).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) I

/-- **Left t-exactness.** The unbounded right derived functor of an additive functor carries an
object with no cohomology below degree `n` to one with no cohomology below degree `n`. -/
theorem isGE_totalRightDerived_obj (F : A ⥤ B) [F.Additive]
    (L : DerivedCategory A) (n : ℤ) [L.IsGE n] :
    ((totalRightDerived F).obj L).IsGE n := by
  classical
  -- Represent `L` by a cochain complex, and that complex by an injective resolution which
  -- vanishes below `n`.
  set X : CochainComplex A ℤ := DerivedCategory.Q.objPreimage L with hXdef
  have eX : DerivedCategory.Q.obj X ≅ L := DerivedCategory.Q.objObjPreimageIso L
  have hXGE : X.IsGE n := by
    rw [← DerivedCategory.isGE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isGE_of_iso eX.symm n
  obtain ⟨R, -, hRGE⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE n X
  have hinj : ∀ i, Injective (R.cocomplex.X i) := R.injective
  have hKI : R.cocomplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective R.cocomplex n
  have hqi : QuasiIso R.ι := R.quasiIso
  -- `L` is the image of the resolution in the derived category.
  have eL : L ≅ DerivedCategory.Q.obj R.cocomplex :=
    eX.symm ≪≫ asIso (DerivedCategory.Q.map R.ι)
  -- The unit of the derived functor is invertible there, so `RF L` is `F` applied degreewise.
  have hunit := isIso_totalRightDerivedUnit_app_of_isKInjective F R.cocomplex
  have eQ : DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj R.cocomplex) ≅
        DerivedCategory.Q.obj R.cocomplex :=
    (DerivedCategory.quotientCompQhIso A).app R.cocomplex
  have eRF : (totalRightDerived F).obj L ≅
      (homotopyMap F).obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj R.cocomplex) :=
    (totalRightDerived F).mapIso (eL ≪≫ eQ.symm) ≪≫
      (@asIso _ _ _ _ _ hunit).symm
  -- That complex vanishes below `n`, hence has no cohomology below `n`.
  have hmap : CochainComplex.IsStrictlyGE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cocomplex) n :=
    isStrictlyGE_mapHomologicalComplex F R.cocomplex n
  have eTarget : (homotopyMap F).obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj R.cocomplex) ≅
        DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cocomplex) :=
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app
      R.cocomplex) ≪≫
      (DerivedCategory.quotientCompQhIso B).app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cocomplex)
  have : (DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cocomplex)).IsGE n := by
    have : CochainComplex.IsGE
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cocomplex) n := inferInstance
    rw [DerivedCategory.isGE_Q_obj_iff]
    infer_instance
  exact DerivedCategory.TStructure.t.isGE_of_iso (eRF ≪≫ eTarget).symm n

/-- **Left t-exactness, in terms of cohomology objects.** The unbounded right derived functor of
an additive functor has vanishing cohomology below any bound of its argument. -/
theorem isZero_homology_totalRightDerived_obj (F : A ⥤ B) [F.Additive]
    (L : DerivedCategory A) (n : ℤ) [L.IsGE n] (q : ℤ) (hq : q < n) :
    IsZero ((DerivedCategory.homologyFunctor B q).obj ((totalRightDerived F).obj L)) :=
  have := isGE_totalRightDerived_obj F L n
  DerivedCategory.isZero_of_isGE _ n q hq

end Stacks.DerivedFunctor

end
