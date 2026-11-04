module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoefficientRestrictionDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamCohomologyDirectImage
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BraidingNatIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleLeftComplex
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothDeRhamProjectionFormula
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedTarget
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ExactPushforwardHomology
import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage

/-!
# The direct image of the graded target of Section 0FMK is the first page

Let `f : X ⟶ Y` be a quasi-compact, quasi-separated and smooth morphism of schemes over a base
`g : Y ⟶ S`. Section 0FMK identifies the `k`-th graded piece of the filtration of `Ω^•_{X/S}`
with `f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`, read over `(f ∘ g)^{-1}𝒪_S`
(`Stacks.DeRhamSmooth.gradedTargetComplex`). The proof of [Stacks, Tag 0FMM] then computes the
higher direct images of that complex by the projection formula of [Stacks, Tag 0FML]:

`R^{k+q}f_*(f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}) = H^q(Ω^k_{Y/S} ⊗^𝐋_{𝒪_Y} Rf_*Ω^•_{X/Y})`.

This file carries that computation out.

## Main results

* `Stacks.DeRhamSmooth.higherDirectImageCoefficientRestrictionIso`: the higher direct images of
  a complex of `f^{-1}𝒪_Y`-modules read over `(f ∘ g)^{-1}𝒪_S` are those taken over
  `f^{-1}𝒪_Y`, read over `g^{-1}𝒪_S`.

## References

* [Stacks Project, Tag 0FMM](https://stacks.math.columbia.edu/tag/0FMM)
* [Stacks Project, Tag 0FML](https://stacks.math.columbia.edu/tag/0FML)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.FilteredComplex (higherDirectImage)

universe u

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf
attribute [local instance] Stacks.DeRhamDirectImage.abelian_modules

namespace Stacks.DeRhamSmooth

open Stacks.DeRhamDirectImage

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The higher direct images of a complex of `f^{-1}𝒪_Y`-modules, read over
`(f ∘ g)^{-1}𝒪_S`, are those over `f^{-1}𝒪_Y` read over `g^{-1}𝒪_S`**:

`R^n(f, (f ∘ g)^{-1}𝒪_S)_*(C|) ≅ (R^n(f, f^{-1}𝒪_Y)_*C)|`.

The derived restriction of scalars is computed degreewise
(`Stacks.DeRhamSmooth.derivedCoefficientRestrictionQIso`), derived direct image is compatible
with composition (`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso`),
the two composites to `(Y, g^{-1}𝒪_S)` agree
(`Stacks.DeRhamSmooth.coefficientRingChange_comp_relativeBase`), and the restriction of scalars
along `g^{-1}𝒪_S ⟶ 𝒪_Y` is exact, so it commutes with taking cohomology sheaves
(`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardHomologyFunctorObjIso`). -/
def higherDirectImageCoefficientRestrictionIso
    (C : CochainComplex (Modules (inverseImageBase f)) ℤ) (n : ℤ) :
    higherDirectImage (derivedRelativePushforward f g)
        (((coefficientRestriction f g).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) n ≅
      (pushforward (toInverseImageBase g)).obj
        ((DerivedCategory.homologyFunctor (Modules Y.toRingedSpace) n).obj
          ((derivedPushforward (inverseImageBaseProjection f)).obj
            (DerivedCategory.Q.obj C))) :=
  (DerivedCategory.homologyFunctor _ n).mapIso
      ((derivedPushforward (relativeBase f g)).mapIso
          (derivedCoefficientRestrictionQIso f g C).symm ≪≫
        (derivedPushforwardCompIso (coefficientRingChange f g) (relativeBase f g)).app _ ≪≫
        eqToIso (congrArg (fun φ => (derivedPushforward.{u} φ).obj (DerivedCategory.Q.obj C))
          (coefficientRingChange_comp_relativeBase f g)) ≪≫
        ((derivedPushforwardCompIso (inverseImageBaseProjection f)
          (toInverseImageBase g)).app _).symm) ≪≫
    letI : PreservesFiniteLimits (modulePushforward (toInverseImageBase g)) :=
      inferInstanceAs (PreservesFiniteLimits (pushforward (toInverseImageBase g)))
    letI : PreservesFiniteColimits (modulePushforward (toInverseImageBase g)) :=
      inferInstanceAs (PreservesFiniteColimits (pushforward (toInverseImageBase g)))
    derivedPushforwardHomologyFunctorObjIso (toInverseImageBase g) n _

/-- **`f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}` is the total tensor complex of `Ω^•_{X/Y}` with
`f^*Ω^k_{Y/S}` placed in degree zero**: the total complex of a tensor product with a complex
concentrated in degree zero (`HomologicalComplex.singleLeftIsoMapBifunctor`), followed by the
Koszul symmetry of total tensor complexes
(`Stacks.SheafOfModules.Tensor.tensorComplexFlipIso`). This is the form in which conclusion (4) of
[Stacks, Tag 0FML] is stated
(`Stacks.DeRhamDirectImage.deRhamOrdinaryProjectionFormulaIso`). -/
def gradedTargetTensorIsoTensorComplex (k : ℕ) :
    gradedTargetTensor f g k ≅
      ((Stacks.SheafOfModules.Tensor.tensorComplex (inverseImageBase f).sheaf).obj
          (deRhamCochainComplex f)).obj
        ((CochainComplex.singleFunctor (Modules (inverseImageBase f)) 0).obj
          ((modulePullback (inverseImageBaseProjection f)).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)))) :=
  HomologicalComplex.singleLeftIsoMapBifunctor
      (Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf)
      (pulledBackTargetForms f g k) (deRhamCochainComplex f) ≪≫
    Stacks.SheafOfModules.Tensor.tensorComplexFlipIso (inverseImageBase f).sheaf _ _

/-- **The higher direct images of `f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}` are the first page
of the spectral sequence of [Stacks, Tag 0FMM]**: for `f : X ⟶ Y` quasi-compact,
quasi-separated and smooth over `g : Y ⟶ S`,

`R^{k+q}f_*(f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}) ≅ H^q(Ω^k_{Y/S} ⊗^𝐋_{𝒪_Y} Rf_*Ω^•_{X/Y})`,

read over `g^{-1}𝒪_S`. This is the computation in the proof of Tag 0FMM: the change of
coefficients (`Stacks.DeRhamSmooth.higherDirectImageCoefficientRestrictionIso`), the shift
`[-k]`, the identification of the tensored complex with a total tensor complex
(`Stacks.DeRhamSmooth.gradedTargetTensorIsoTensorComplex`), conclusion (4) of
[Stacks, Tag 0FML] at the relative de Rham complex and the quasi-coherent `Ω^k_{Y/S}`
(`Stacks.DeRhamDirectImage.deRhamOrdinaryProjectionFormulaIso`), the commutativity constraint
of the derived tensor product, and the comparison of the bounded below and the unbounded derived
direct image of `Ω^•_{X/Y}`. -/
def higherDirectImageGradedTargetIso [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    (k : ℕ) (q : ℤ) :
    higherDirectImage (derivedRelativePushforward f g) (gradedTargetComplex f g k)
        ((k : ℤ) + q) ≅
      deRhamFirstPage f g (k : ℤ) q :=
  letI : (derivedPushforward (inverseImageBaseProjection f)).CommShift ℤ :=
    (derivedAdjunction (inverseImageBaseProjection f)).rightAdjointCommShift ℤ
  higherDirectImageCoefficientRestrictionIso f g _ _ ≪≫
    (pushforward (toInverseImageBase g)).mapIso
      ((DerivedCategory.homologyFunctor (Modules Y.toRingedSpace) ((k : ℤ) + q)).mapIso
          ((derivedPushforward (inverseImageBaseProjection f)).mapIso
              ((DerivedCategory.Q.commShiftIso (-(k : ℤ))).app (gradedTargetTensor f g k)) ≪≫
            ((derivedPushforward (inverseImageBaseProjection f)).commShiftIso
              (-(k : ℤ))).app _) ≪≫
        ((DerivedCategory.homologyFunctor (Modules Y.toRingedSpace) 0).shiftIso
          (-(k : ℤ)) ((k : ℤ) + q) q (by omega)).app _ ≪≫
        (DerivedCategory.homologyFunctor (Modules Y.toRingedSpace) q).mapIso
          ((derivedPushforward (inverseImageBaseProjection f)).mapIso
              (DerivedCategory.Q.mapIso (gradedTargetTensorIsoTensorComplex f g k)) ≪≫
            (deRhamOrdinaryProjectionFormulaIso f
              (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))
              (AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentialForms g k)).symm ≪≫
            ((Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso
                (Stacks.RingedSpace.toRingedSite Y.toRingedSpace)
                (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
                  Y.toRingedSpace.sheaf)).app _).app _ ≪≫
            ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
                Y.toRingedSpace.sheaf).obj _).mapIso
              (AlgebraicGeometry.DeRhamCohomologyDirectImage.derivedDeRhamDirectImageUnboundedIso
                f).symm))

end Stacks.DeRhamSmooth

end
