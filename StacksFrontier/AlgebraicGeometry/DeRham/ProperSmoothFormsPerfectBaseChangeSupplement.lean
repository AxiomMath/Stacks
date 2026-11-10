module

public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsPerfectBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFiniteType
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsOperator
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsLocallyFree
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatUntensoredBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
import StacksCore.Tactic.StacksAttribute

/-!
# Further results on `ProperSmoothFormsPerfectBaseChange`

Results about the objects of the module
`StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsPerfectBaseChange` that need imports
beyond those of that module.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction StrictlyPerfect
open Stacks.Cohomology.ProperSupportPerfection (derivedPushforwardOX)

universe v u₁ u

namespace AlgebraicGeometry.ProperSmoothDeRham

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] abelianDerivedTensorModules

/-! ### The perfectness half of Stacks 0FM0 for the differential forms -/

section Perfect

open Stacks.Cohomology.PerfectPushforward

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **[Stacks, Tag 0FM0], the perfectness of `Rf_*Ω^p_{X/S}`, over a Noetherian base.** Let
`f : X ⟶ S` be a proper smooth morphism of schemes with `S` Noetherian. Then `Rf_*Ω^p_{X/S}` is
a perfect object of `D(𝒪_S)`.

This is [Stacks, Tag 0B6F] at the perfect object `Ω^p_{X/S}` in degree zero; a smooth morphism
is flat, so the morphism is flat and proper as that tag asks. The new content is perfectness of
`Ω^p_{X/S}`, which is
`AlgebraicGeometry.ProperSmoothDeRham.isPerfect_single_relativeDifferentialForms`; everything
else is what [Stacks, Tag 0B6F] already carries, reproduced here unchanged.

Cf. Stacks Tag 0FM0; not registered because it carries the hypotheses `hcoh` and `htor`, the
stand-ins `PushforwardCoherenceResidue` and `PushforwardTorDimensionResidue` of Stacks Tags 0DJQ
and 08EV. -/
public theorem isPerfect_derivedPushforward_relativeDifferentialForms
    [Smooth f] [IsProper f] [IsNoetherian S]
    (D : RingedSpace.CertifiedDerivedSheafTensoring
      (RingedSpace.inverseImage S.toRingedSpace f.base))
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct (schemeSite X).O)
    [(Stacks.SheafOfModules.Tensor.sheafTensor (schemeSite X).O).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor (schemeSite X).O).obj M).Additive]
    [∀ K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules (schemeSite X).O) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor (schemeSite X).O) (ComplexShape.up ℤ)]
    (hcoh : PushforwardCoherenceResidue f (derivedPushforwardOX f))
    (htor : PushforwardTorDimensionResidue f D (derivedPushforwardOX f))
    (p : ℕ)
    (htorForms : D.HasFiniteTorDimension ((Scheme.Hom.derivedScalarRestriction f).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj
        (Scheme.Hom.relativeDifferentialForms f (p : ℤ))))) :
    RingedSpace.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforwardOX f).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (Scheme.Hom.relativeDifferentialForms f (p : ℤ)))) :=
  isPerfect_derivedPushforward_of_flatProper f D T hcoh htor _
    { isPerfect := isPerfect_single_relativeDifferentialForms f p
      hasFiniteTorDimension := htorForms }

end Perfect

/-! ### The base-change half of Stacks 0FM0 for the differential forms -/

section BaseChange

open AlgebraicGeometry.ProperFlatBaseChange
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

/-- **[Stacks, Tag 0FM0], the base-change half for `Rf_*Ω^p_{X/S}`, in the tensor form of
[Stacks, Tag 0B91].** Let `f : X ⟶ S` be a smooth morphism of finite presentation. For
every cartesian base-change square the canonical map

`Lg^*Rf_*(E ⊗^L_{𝒪_X} Ω^p_{X/S}) ⟶ Rf'_*(L(g')^*E ⊗^L_{𝒪_{X'}} (g')^*Ω^p_{X/S})`

of `AlgebraicGeometry.tensorFlatBaseChangeMap` is an isomorphism, for every `E` for which the two
derived tensor products have quasi-coherent cohomology (`hK`, `hK'`) — in particular for the
`E = 𝒪_X` this tag is about. Properness is not needed for this half.

This is `AlgebraicGeometry.ProperFlatBaseChange.isIso_tensorFlatBaseChangeMap_module_of_isPullback`
at the module `Ω^p_{X/S}`, whose flatness over `S` is
`AlgebraicGeometry.ProperSmoothDeRham.isFlatOver_relativeDifferentialForms`, read off
[Stacks, Tag 02G1] through the exterior-power result of this file.

Cf. Stacks Tag 0FM0; not registered because it carries the hypotheses `hK` and `hK'`. -/
public theorem isIso_tensorFlatBaseChangeMap_relativeDifferentialForms
    {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (hsq : IsPullback g' f' f g)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (hf : FinitePresentation f) [Smooth f] (p : ℕ)
    (E : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj
      (((derivedTensorProductFunctor X.sheaf).obj E).obj
        (DerivedCategory.Q.obj (singleDegreeComplex
          (Scheme.Hom.relativeDifferentialForms f (p : ℤ)))))).IsQuasicoherent)
    (hK' : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj
      (((derivedTensorProductFunctor X'.sheaf).obj
          ((derivedPullback g'.toLRSHom.toShHom).obj E)).obj
        (DerivedCategory.Q.obj
          ((pullbackComplex g'.toLRSHom.toShHom).obj (singleDegreeComplex
            (Scheme.Hom.relativeDifferentialForms f (p : ℤ))))))).IsQuasicoherent) :
    IsIso (tensorFlatBaseChangeMap f g f' g' sq E
      (singleDegreeComplex (Scheme.Hom.relativeDifferentialForms f (p : ℤ)))) :=
  isIso_tensorFlatBaseChangeMap_module_of_isPullback f g f' g' hsq sq hf _
    (isFlatOver_relativeDifferentialForms f p) E hK hK'

end BaseChange

end AlgebraicGeometry.ProperSmoothDeRham

end
