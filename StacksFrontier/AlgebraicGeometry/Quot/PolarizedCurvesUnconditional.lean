module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStack
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurves
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackUnconditional
public import StacksFrontier.CategoryTheory.TwoFibreProductOverFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleBaseChange

/-!
# The stack of polarized curves (Stacks 0D5C)

Stacks 0D5C considers the 2-fibre product
`PolarizedCurves = 𝒞urves ×_{𝒮paces'_{fp, flat, proper}} 𝒫olarized`
and asserts that it parametrizes polarized curves, i.e. families of curves endowed with a
relatively ample invertible sheaf, that its projection to `𝒫olarized` makes it an open and closed
substack (by Stacks 0D5B), and that its projection to `𝒞urves` is algebraic, smooth and
surjective. This file proves the first two assertions.

The 2-fibre product square `AlgebraicGeometry.polarizedCurvesFiberedCategory` is stated on the
hypothesis that the category of polarized families is fibred in groupoids over the big fppf site
of `Spec(ℤ)` (the second assertion of Stacks 0D3Z). That hypothesis is proved here: polarized
families are fibred in groupoids over the big fppf site
(`AlgebraicGeometry.polarizedProjection_isFiberedInGroupoids_unconditional`), and reading a scheme
of the site over the terminal scheme `Spec(ℤ)` is the inverse of the equivalence
`Over.equivalenceOfIsTerminal`, along which Stacks 003S transfers
(`CategoryTheory.Functor.IsFiberedInGroupoids.sliceAtTerminal`).

## Main definitions

* `AlgebraicGeometry.isPolarizedCurve`: a polarized family whose underlying family of algebraic
  spaces has relative dimension at most one.
* `AlgebraicGeometry.PolarizedFamily.toCurveFamily`: the family of curves underlying a polarized
  curve.
* `AlgebraicGeometry.polarizedCurvesEquivalence`: **Stacks 0D5C**, the 2-fibre product is
  equivalent, through its first projection, to the category of polarized curves.

## Main results

* `AlgebraicGeometry.polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids`: the
  category of polarized families is fibred in groupoids over the big fppf site of `Spec(ℤ)`.
* `AlgebraicGeometry.polarizedCurvesToPolarized_isOpenImmersion_and_isClosedImmersion`:
  **Stacks 0D5C**, `PolarizedCurves` is an open and closed substack of `𝒫olarized`.
* `AlgebraicGeometry.polarizedCurvesUnconditional` (the object of Stacks Section 0DPY) and
  `AlgebraicGeometry.isRepresentableByAlgebraicSpaces_polarizedCurvesToPolarizedUnconditional`,
  `AlgebraicGeometry.isOpenImmersion_polarizedCurvesToPolarizedUnconditional`,
  `AlgebraicGeometry.isClosedImmersion_polarizedCurvesToPolarizedUnconditional`
  (**Stacks 0DPZ**): the 2-fibre product and its projection to `𝒫olarized`, an open and closed
  immersion, with Stacks 0D3Z supplied.

## Implementation notes

The first projection `PolarizedCurves ⟶ 𝒫olarized` is fully faithful because it is the base
change of the fully faithful inclusion `𝒞urves ⟶ 𝒮paces'_{fp, flat, proper}` of Stacks 0D50
(`CategoryTheory.TwoFibreProductOver.full_fst`), and its essential image is the polarized curves:
an object of the 2-fibre product is a polarized family identified, by a strongly cartesian
isomorphism, with a family of curves, so the bound on the relative dimension passes to it
(Stacks 04NS part (1)); conversely a polarized curve, its family of curves and the identity of
their common family of algebraic spaces form an object of the 2-fibre product lying over it on
the nose. The category of polarized families has its morphisms in `Type u` while the 2-fibre
product has them in `Type (u + 1)` (see `AlgebraicGeometry.PolarizedFamilyUp`), so the
equivalence crosses that change of morphism universe.

## References

* [Stacks Project, Tag 0D5C](https://stacks.math.columbia.edu/tag/0D5C)
* [Stacks Project, Tag 0D5B](https://stacks.math.columbia.edu/tag/0D5B)
* [Stacks Project, Tag 0D3Z](https://stacks.math.columbia.edu/tag/0D3Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u})

/-- Reading a scheme of the big fppf site over the terminal scheme is the inverse of the
equivalence between a category and its slice at a terminal object. -/
theorem schemeOverIntegers_eq_equivalenceOfIsTerminal_inverse :
    schemeOverIntegers B = (Over.equivalenceOfIsTerminal
      (isTerminal_obj_specULiftZ B B.contains_integerBase)).inverse := by
  have hobj : ∀ X, (schemeOverIntegers B).obj X = (Over.equivalenceOfIsTerminal
      (isTerminal_obj_specULiftZ B B.contains_integerBase)).inverse.obj X := fun X =>
    congrArg Over.mk ((isTerminal_obj_specULiftZ B B.contains_integerBase).hom_ext _ _)
  refine CategoryTheory.Functor.ext hobj (fun X Y f => ?_)
  refine Over.OverMorphism.ext ?_
  simp only [Over.comp_left, Over.eqToHom_left]
  rfl

/-- **Stacks 0D3Z over the big fppf site of `Spec(ℤ)`.** The category of polarized families is
fibred in groupoids over the big fppf site of the terminal scheme. -/
theorem polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids :
    (polarizedProjection B ⋙ schemeOverIntegers B).IsFiberedInGroupoids := by
  rw [schemeOverIntegers_eq_equivalenceOfIsTerminal_inverse]
  exact polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal _

/-! ### Polarized curves -/

/-- A polarized family is a *polarized curve* when its underlying family of algebraic spaces has
relative dimension at most one, i.e. when it is a family of curves (Stacks 0D4Z). -/
def isPolarizedCurve : ObjectProperty (PolarizedFamily B) := fun P =>
  Space.HasRelativeDimensionLE 1 B integerBase B.contains_integerBase
    (yoneda.map P.structureMapOverIntegers)

variable {B} in
/-- The family of curves underlying a polarized curve. -/
@[simps]
def PolarizedFamily.toCurveFamily (hZ : B.Contains integerBase) (P : PolarizedFamily B)
    (hP : isPolarizedCurve B P) : CurveFamily B hZ where
  base := (schemeOverIntegers B).obj P.base
  total := ⟨yoneda.obj ((schemeOverIntegers B).obj P.totalObj),
    isAlgebraicSpace_yoneda B integerBase hZ _⟩
  toBase := ObjectProperty.homMk (yoneda.map P.structureMapOverIntegers)
  flat := P.isProperFlat_yoneda_structureMapOverIntegers.2.1
  proper := P.isProperFlat_yoneda_structureMapOverIntegers.2.2
  finitePresentation := P.isProperFlat_yoneda_structureMapOverIntegers.1
  relativeDimensionLE := hP

variable (hZ : B.Contains integerBase)

/-- The family of curves underlying a polarized curve has, as its underlying family of
algebraic spaces, the family underlying the polarized family. -/
theorem curvesToCartesianProperFlat_obj_toCurveFamily (P : PolarizedFamily B)
    (hP : isPolarizedCurve B P) :
    (curvesToCartesianProperFlat B hZ).obj (P.toCurveFamily hZ hP) =
      (forgetPolarization B).obj P :=
  rfl

/-- An object of the 2-fibre product is a polarized curve: its polarized family is identified by
a strongly cartesian isomorphism with the family of algebraic spaces underlying a family of
curves, and the bound on the relative dimension passes along it (Stacks 04NS part (1)). -/
theorem isPolarizedCurve_fst_obj (W : (polarizedCurvesFiberedCategory B hZ
      (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).val.obj) :
    isPolarizedCurve B (ULiftHom.objDown.{u + 1, u + 1} W.x) :=
  (isCurveSpace_of_isStronglyCartesian B integerBase hZ _ _ W.iso.hom.property
    ⟨(curvesToCartesianProperFlat B hZ).obj W.y |>.obj.property,
      W.y.relativeDimensionLE⟩).2

/-- The first projection of the 2-fibre product, landing in the polarized curves. -/
def polarizedCurvesToIsPolarizedCurve :
    (polarizedCurvesFiberedCategory B hZ
      (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).val.obj ⥤
      (isPolarizedCurve B).FullSubcategory :=
  (isPolarizedCurve B).lift
    (CatFiberedInGroupoids.homFunctor
        (polarizedCurvesToPolarized B hZ
          (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)) ⋙
      (ULiftHom.down : PolarizedFamilyUp B ⥤ PolarizedFamily B))
    (isPolarizedCurve_fst_obj B hZ)

/-- The first projection of the 2-fibre product, followed by the inclusion of the polarized
curves, is the projection to `𝒫olarized`. -/
theorem polarizedCurvesToIsPolarizedCurve_comp_ι :
    polarizedCurvesToIsPolarizedCurve B hZ ⋙ (isPolarizedCurve B).ι =
      CatFiberedInGroupoids.homFunctor
          (polarizedCurvesToPolarized B hZ
            (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)) ⋙
        (ULiftHom.down : PolarizedFamilyUp B ⥤ PolarizedFamily B) :=
  rfl

/-- The projection of the 2-fibre product to `𝒫olarized` is faithful. -/
instance faithful_homFunctor_polarizedCurvesToPolarized :
    (CatFiberedInGroupoids.homFunctor (polarizedCurvesToPolarized B hZ
      (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B))).Faithful :=
  have := curvesToCartesianProperFlat_faithful B hZ
  TwoFibreProductOver.faithful_fst_of_faithful (G := curvesToCartesianProperFlat B hZ)

/-- The projection of the 2-fibre product to `𝒫olarized` is full. -/
instance full_homFunctor_polarizedCurvesToPolarized :
    (CatFiberedInGroupoids.homFunctor (polarizedCurvesToPolarized B hZ
      (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B))).Full :=
  have := curvesToCartesianProperFlat_faithful B hZ
  have := curvesToCartesianProperFlat_full B hZ
  TwoFibreProductOver.full_fst (G := curvesToCartesianProperFlat B hZ) rfl rfl

/-- The first projection of the 2-fibre product into the polarized curves is fully faithful. -/
def polarizedCurvesToIsPolarizedCurveFullyFaithful :
    (polarizedCurvesToIsPolarizedCurve B hZ).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := (isPolarizedCurve B).ι)
    ((Functor.FullyFaithful.ofFullyFaithful (CatFiberedInGroupoids.homFunctor
      (polarizedCurvesToPolarized B hZ
        (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)))).comp
      (ULiftHom.equiv.{u, u + 1, u + 1} (C := PolarizedFamily B)).fullyFaithfulInverse)

/-- The first projection of the 2-fibre product into the polarized curves is faithful. -/
instance : (polarizedCurvesToIsPolarizedCurve B hZ).Faithful :=
  (polarizedCurvesToIsPolarizedCurveFullyFaithful B hZ).faithful

/-- The first projection of the 2-fibre product into the polarized curves is full. -/
instance : (polarizedCurvesToIsPolarizedCurve B hZ).Full :=
  (polarizedCurvesToIsPolarizedCurveFullyFaithful B hZ).full

/-- The object of the 2-fibre product attached to a polarized curve: the polarized family, its
family of curves, and the identity of their common family of algebraic spaces. -/
def polarizedCurveToPolarizedCurves (P : (isPolarizedCurve B).FullSubcategory) :
    (polarizedCurvesFiberedCategory B hZ
      (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).val.obj where
  base := (schemeOverIntegers B).obj P.obj.base
  x := ULiftHom.objUp.{u + 1, u + 1} P.obj
  y := P.obj.toCurveFamily hZ P.property
  hx := rfl
  hy := rfl
  iso := Iso.refl _
  vertical := IsHomLift.id rfl

/-- Every polarized curve is the first projection of an object of the 2-fibre product. -/
instance : (polarizedCurvesToIsPolarizedCurve B hZ).EssSurj where
  mem_essImage P := ⟨polarizedCurveToPolarizedCurves B hZ P, ⟨Iso.refl _⟩⟩

/-- The first projection of the 2-fibre product into the polarized curves is an equivalence. -/
instance : (polarizedCurvesToIsPolarizedCurve B hZ).IsEquivalence where

/-- **Stacks 0D5C: the 2-fibre product parametrizes polarized curves.** The 2-fibre product
`PolarizedCurves = 𝒞urves ×_{𝒮paces'_{fp, flat, proper}} 𝒫olarized` is equivalent, through its
first projection, to the category of polarized families of relative dimension at most one, i.e.
of families of curves endowed with a relatively ample invertible module. -/
def polarizedCurvesEquivalence :
    (polarizedCurvesFiberedCategory B hZ
      (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).val.obj ≌
      (isPolarizedCurve B).FullSubcategory :=
  (polarizedCurvesToIsPolarizedCurve B hZ).asEquivalence

/-- **Stacks 0D5C: PolarizedCurves is an open and closed substack of `𝒫olarized`.** The
projection `PolarizedCurves ⟶ 𝒫olarized` is representable by algebraic spaces, an open immersion
and a closed immersion. -/
theorem polarizedCurvesToPolarized_isOpenImmersion_and_isClosedImmersion :
    Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (polarizedCurvesToPolarized B hZ
          (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).hom ∧
      Stack.IsOpenImmersion B integerBase hZ (polarizedCurvesToPolarized B hZ
        (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)) ∧
      Stack.IsClosedImmersion B integerBase hZ (polarizedCurvesToPolarized B hZ
        (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)) :=
  ⟨isRepresentableByAlgebraicSpaces_polarizedCurvesToPolarized B hZ _,
    isOpenImmersion_polarizedCurvesToPolarized B hZ _,
    isClosedImmersion_polarizedCurvesToPolarized B hZ _⟩

/-! ### PolarizedCurves (Stacks Section 0DPY) and Stacks 0DPZ with Stacks 0D3Z supplied -/

/-- *PolarizedCurves*, the 2-fibre product
`𝒞urves ×_{𝒮paces'_{fp, flat, proper}} 𝒫olarized` of
`AlgebraicGeometry.polarizedCurvesFiberedCategory` (as in Stacks Section 0DPY), with Stacks 0D3Z
supplied. -/
abbrev polarizedCurvesUnconditional :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  polarizedCurvesFiberedCategory B hZ
    (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)

/-- The projection `PolarizedCurves ⟶ 𝒫olarized` of
`AlgebraicGeometry.polarizedCurvesToPolarized`, with Stacks 0D3Z supplied. -/
abbrev polarizedCurvesToPolarizedUnconditional :
    polarizedCurvesUnconditional B hZ ⟶
      polarizedFiberedCategory B hZ
        (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B) :=
  polarizedCurvesToPolarized B hZ
    (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)

/-- The projection `PolarizedCurves ⟶ 𝒫olarized` is representable by algebraic spaces. -/
@[stacks 0DPZ "representability by algebraic spaces"]
theorem isRepresentableByAlgebraicSpaces_polarizedCurvesToPolarizedUnconditional :
    Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
      (polarizedCurvesToPolarizedUnconditional B hZ).hom :=
  isRepresentableByAlgebraicSpaces_polarizedCurvesToPolarized B hZ
    (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)

/-- The projection `PolarizedCurves ⟶ 𝒫olarized` is an open immersion. -/
@[stacks 0DPZ "open immersion"]
theorem isOpenImmersion_polarizedCurvesToPolarizedUnconditional :
    Stack.IsOpenImmersion B integerBase hZ (polarizedCurvesToPolarizedUnconditional B hZ) :=
  isOpenImmersion_polarizedCurvesToPolarized B hZ
    (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)

/-- The projection `PolarizedCurves ⟶ 𝒫olarized` is a closed immersion. -/
@[stacks 0DPZ "closed immersion"]
theorem isClosedImmersion_polarizedCurvesToPolarizedUnconditional :
    Stack.IsClosedImmersion B integerBase hZ (polarizedCurvesToPolarizedUnconditional B hZ) :=
  isClosedImmersion_polarizedCurvesToPolarized B hZ
    (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)

end AlgebraicGeometry
