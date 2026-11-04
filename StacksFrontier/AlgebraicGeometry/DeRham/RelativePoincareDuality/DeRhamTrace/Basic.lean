module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamPoincareTraceCriterion
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.RelativeHodgePairing
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.SmoothOfRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RelativeEmbeddingDimensionForms

/-!
# The objects of relative Poincaré duality for de Rham cohomology

In the situation of [Stacks, Tag 0G8G] (`f : X ⟶ S` proper smooth over a quasi-compact
quasi-separated base, fibres nonempty and equidimensional of dimension `n`) this file names the
objects of [Stacks, Tag 0G8K]: `Rf_*(Ω^•_{X/S}[2n])`, its cohomology sheaf `R^{2n}f_*Ω^•_{X/S}`,
multiplication by a global function on `Ω^p_{X/S}`, and the inclusion
`Rf_*Ω^n_{X/S}[n] ⟶ Rf_*(Ω^•_{X/S}[2n])` of the top piece of the de Rham complex.

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Stacks.StandardDerivedModel
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.DerivedTensor.RingedSite (DerivedModules derivedTensorProductFunctor
  canonicalDerivedTensorProduct)
open Stacks.DeRhamDirectImage (inverseImageBase inverseImageBaseProjection)

universe u

namespace AlgebraicGeometry.RelativeDualitySituation

variable (D : RelativeDualitySituation.{u})

/-- `Rf_*(Ω^•_{X/S}[2n])` in `D(𝒪_S)`. -/
abbrev deRhamDirectImageTop :=
  (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f)).obj
    ((shiftFunctor (DerivedModules.{u + 1, u} (inverseImageBase D.f).sheaf) (2 * D.n : ℤ)).obj
      (Scheme.deRhamDerived D.f))

/-- `R^{2n} f_* Ω^•_{X/S}`. -/
abbrev deRhamTopCohomology : D.S.Modules :=
  (DerivedCategory.homologyFunctor D.S.Modules (2 * D.n : ℤ)).obj D.f.deRhamDirectImage

/-- The relative de Rham complex `Ω^•_{X/S}`, as a complex of `f⁻¹𝒪_S`-modules. -/
abbrev deRhamCx :=
  SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras D.f)
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))

/-- Multiplication by a global function on `Ω^p_{X/S}`, as a map of `f⁻¹𝒪_S`-modules. -/
def formsSMul (g : Γ(D.X, ⊤)) (p : ℕ) : D.deRhamCx.X p ⟶ D.deRhamCx.X p :=
  (RingedSpaceModuleAdjunction.modulePushforward
      (Stacks.DeRhamDirectImage.toInverseImageBase D.f)).map
    (Stacks.Cohomology.InvertibleDerived.smulHom (X := D.X.toRingedSpace) g
      (Scheme.Hom.relativeDifferentialForms D.f (p : ℤ)))

/-- `Ω^n_{X/S}` as an `f⁻¹𝒪_S`-module. -/
abbrev topForms : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
    ((TopCat.Sheaf.pullback CommRingCat.{u} D.f.base).obj D.S.sheaf)) :=
  (RingedSpaceModuleAdjunction.modulePushforward
      (Stacks.DeRhamDirectImage.toInverseImageBase D.f)).obj
    (Scheme.Hom.relativeDifferentialForms D.f D.n)

/-- `Ω^{n+1}_{X/S} = 0`, so the top differential of `Ω^•_{X/S}` vanishes. -/
theorem isZero_deRhamCx_X_succ : IsZero (D.deRhamCx.X (D.n + 1)) :=
  (SheafOfModules.restrictScalars _).map_isZero
    (Scheme.Hom.isZero_relativeDifferentialForms_of_smoothOfRelativeDimension D.f D.n (D.n + 1)
      (by omega))

/-- The inclusion `Ω^n_{X/S}[-n] ⟶ Ω^•_{X/S}` of the top-degree piece, as a map of complexes of
`f⁻¹𝒪_S`-modules. -/
def topFormsToDeRham :
    (HomologicalComplex.single _ (ComplexShape.up ℤ) (D.n : ℤ)).obj D.topForms ⟶
      D.deRhamCx.extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.mkHomFromSingle
    (D.deRhamCx.extendXIso ComplexShape.embeddingUpNat (i := D.n) (by simp)).inv
    (fun k hk => by
      obtain rfl : (D.n : ℤ) + 1 = k := hk
      exact ((D.isZero_deRhamCx_X_succ).of_iso
        (D.deRhamCx.extendXIso ComplexShape.embeddingUpNat (i := D.n + 1) (by simp))).eq_of_tgt _ _)

/-- `Rf_*(Ω^n[n])`, along `f`, is `Rf_*(Ω^n[-n][2n])` along `(X, f⁻¹𝒪_S) ⟶ (S, 𝒪_S)`. -/
def topPieceIso : (Stacks.Duality.derivedPushforward D.f).obj
    ((D.f.formsInDegreeZero D.n)⟦(D.n : ℤ)⟧) ≅
      (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f)).obj
        ((shiftFunctor (DerivedModules.{u + 1, u} (inverseImageBase D.f).sheaf) (2 * D.n : ℤ)).obj
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) (D.n : ℤ)).obj D.topForms))) :=
  letI := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift
    D.f.toLRSHom.toShHom
  letI := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift
    (inverseImageBaseProjection D.f)
  ((derivedPushforward D.f.toLRSHom.toShHom).commShiftIso (D.n : ℤ)).app _ ≪≫
    (shiftFunctor _ (D.n : ℤ)).mapIso (D.f.formsDirectImageIso D.n) ≪≫
    (((derivedPushforward (inverseImageBaseProjection D.f)).commShiftIso (D.n : ℤ)).app _).symm ≪≫
    (derivedPushforward (inverseImageBaseProjection D.f)).mapIso
      (((DerivedCategory.singleFunctors _).shiftIso (D.n : ℤ) (-(D.n : ℤ)) 0 (by omega)).app _ ≪≫
        (((DerivedCategory.singleFunctors _).shiftIso (2 * D.n : ℤ) (-(D.n : ℤ)) (D.n : ℤ)
          (by omega)).app _).symm ≪≫
        (shiftFunctor _ (2 * D.n : ℤ)).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ (D.n : ℤ)).app D.topForms))

/-- (A5) the inclusion of the top piece `Rf_*Ω^n[n] ⟶ Rf_*(Ω^•[2n])`. -/
def topInclusion : (Stacks.Duality.derivedPushforward D.f).obj
    ((D.f.formsInDegreeZero D.n)⟦(D.n : ℤ)⟧) ⟶ D.deRhamDirectImageTop :=
  D.topPieceIso.hom ≫ (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f)).map
    ((shiftFunctor (DerivedModules.{u + 1, u} (inverseImageBase D.f).sheaf) (2 * D.n : ℤ)).map
      (DerivedCategory.Q.map D.topFormsToDeRham))


end AlgebraicGeometry.RelativeDualitySituation

end
