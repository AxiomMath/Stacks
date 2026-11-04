module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiPullbackExact
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartsHaveEnoughObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedFunctorAmplitudeUnbounded
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.AcyclicObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.KInjectiveSectionsComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HypercohomologyOverAcyclicOpens

/-!
# Cohomology sheaves of `ε_*` of a K-injective complex with quasi-coherent cohomology

Let `X = yoneda.obj U` be the algebraic space represented by an object `U` of the big fppf site
over `S`, with underlying scheme `X_0`, and let `ε : (X_étale, 𝒪_X) ⟶ (X_{0,Zar}, 𝒪_{X_0})` be
`AlgebraicGeometry.Space.representedZariskiRingedToposHomRepresentedZariskiRingedToposHom`.
For a K-injective complex `I` of `𝒪_X`-modules whose cohomology sheaves are quasi-coherent, the
comparison

`H^q(ε_* I) ⟶ ε_* H^q(I)`

of the left exact functor `ε_*` is an isomorphism.  This is the computation of the cohomology
sheaves of `Rε_*` in the proof of Stacks 071Q: over an affine open `V ⊆ X_0` the étale chart
`V ⟶ X` is affine, so by Stacks 0BKZ, with the vanishing of the higher cohomology of
quasi-coherent modules on affine charts as input, `H^q(V, I) = Γ(V, H^q(I))`; and affine opens
cover `X_0`.

## Main results

* `isIso_evaluation_homologyComparison_forget_of_isAffineChart_representedZariskiDirectImage`:
  Stacks 0BKZ on the small étale site of an algebraic space, read on sections of a K-injective
  complex.
* `isIso_homologyComparison_representedZariskiModulePushforward_representedZariskiDirectImage`:
  the comparison `H^q(ε_* I) ⟶ ε_* H^q(I)` is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.HypercohomologyEdge

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] enoughInjectives_modules_ringUniverse
  isGrothendieckAbelian_modules_ringUniverse

section Chart

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}

/-- **Stacks 0BKZ on the small étale site of an algebraic space, read on sections.**  For a
K-injective complex `I` of `𝒪_X`-modules with quasi-coherent cohomology sheaves and an affine
étale chart `W`, the comparison `H^q(Γ(W, I)) ⟶ Γ(W, H^q(I))` is bijective, in the form of the
comparison of the forgetful functor to presheaves of modules on sections over `W`. -/
theorem isIso_evaluation_homologyComparison_forget_of_isAffineChart_representedZariskiDirectImage
    (I : CochainComplex (Modules.{u, u} B S hS X hX) ℤ) (hI : I.IsKInjective)
    (hqc : ∀ q : ℤ, (I.homology q).IsQuasicoherentOnSite)
    (W : SmallEtale B S hS X) (hW : IsAffineChart B S hS X W) (q : ℤ) :
    IsIso ((PresheafOfModules.evaluation
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)).obj
          (op W)).map
      (HomologyComparison.homologyComparison
        (SheafOfModules.forget.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)))
        I q)) := by
  have := smallEtaleRingedSite_hasSheafify B S hS X hX
  refine
    isIso_evaluation_map_homologyComparison_forget_kInjectiveSectionsComparison.{u + 1, u, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)) W q I hI ?_
  refine isIso_hypercohomologyEdge_app_of_acyclic_cover.{u + 1, u, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)) W
    (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))
    (IsAffineChart B S hS X) (hasEnoughObjects_isAffineChart B S hS X)
    (fun V hV p hp m => ?_) hW q
  refine isZero_rightDerived_evaluation_of_isAffineChart B S hS X hX _ ?_ V hV p hp
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((DerivedCategory.homologyFunctorFactorsh _ m).app _ ≪≫
      (HomotopyCategory.homologyFunctorFactors _ (ComplexShape.up ℤ) m).app I).symm (hqc m)

end Chart

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The étale chart `V ⟶ X` attached to an affine open `V` of the scheme `X_0` underlying `U` is
an affine chart. -/
theorem isAffineChart_representedOpensToSmallEtale_obj_representedZariskiDirectImage
    {V : (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Opens}
    (hV : IsAffineOpen V) :
    IsAffineChart B S hS (yoneda.obj U)
      ((representedSchemeOpensToSmallEtaleRepresentedZariskiRingedToposHom B S hS U).obj V) :=
  hV

/-- The pushforward `ε_*` of `𝒪_X`-modules along `ε` is an additive functor. -/
instance additive_representedZariskiModulePushforward_representedZariskiDirectImage :
    (representedZariskiModulePushforwardRepresentedZariskiPullbackExact B S hS U).Additive :=
  RingedToposHom.pushforwardModules_additive
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U)

/-- The pushforward `ε_*` of `𝒪_X`-modules along `ε` preserves finite limits. -/
instance preservesFiniteLimits_representedZariskiModulePushforward_representedZariskiDirectImage :
    PreservesFiniteLimits
      (representedZariskiModulePushforwardRepresentedZariskiPullbackExact B S hS U) :=
  RingedToposHom.pushforwardModules_preservesFiniteLimits
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U)

/-- **The cohomology sheaves of `ε_*` of a K-injective complex with quasi-coherent cohomology.**
For a K-injective complex `I` of `𝒪_X`-modules whose cohomology sheaves are quasi-coherent, the
comparison `H^q(ε_* I) ⟶ ε_* H^q(I)` of the left exact functor `ε_*` is an isomorphism. -/
theorem isIso_homologyComparison_representedZariskiModulePushforward_representedZariskiDirectImage
    (I : CochainComplex (Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)) ℤ) (hI : I.IsKInjective)
    (hqc : ∀ q : ℤ, (I.homology q).IsQuasicoherentOnSite) (q : ℤ) :
    IsIso (HomologyComparison.homologyComparison
      (representedZariskiModulePushforwardRepresentedZariskiPullbackExact B S hS U) I q) :=
  isIso_homologyComparison_of_isIso_evaluation_kInjectiveSectionsComparison
    (representedZariskiModulePushforwardRepresentedZariskiPullbackExact B S hS U) I q
    (Stacks.Cohomology.AcyclicOpen.hasEnoughObjects_of_isBasis
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U).isBasis_affineOpens)
    (fun V _ => (representedSchemeOpensToSmallEtaleRepresentedZariskiRingedToposHom B S hS U).obj V)
    (fun V _ =>
      representedZariskiPushforwardEvaluationIsoRepresentedZariskiPullbackExact B S hS U V)
    (fun _ hV =>
      isIso_evaluation_homologyComparison_forget_of_isAffineChart_representedZariskiDirectImage
        I hI hqc _ (isAffineChart_representedOpensToSmallEtale_obj_representedZariskiDirectImage
          B S hS U hV) q)

end AlgebraicGeometry.Space
