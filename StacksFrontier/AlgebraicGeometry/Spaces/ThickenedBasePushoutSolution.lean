module

public import StacksFrontier.AlgebraicGeometry.Spaces.ThickenedBaseIdealInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickenedBasePushoutQcqs
public import StacksFrontier.Deformation.ToposThickening.KernelPushoutSolution

/-!
# Solutions over a thickened base and a change of ideal module

Let `f : X ⟶ D` be a morphism of algebraic spaces with `X` quasi-compact and quasi-separated,
`i : D ⟶ D'` a closed immersion, and `P` a square-zero extension problem (91.13.0.1) of the small
étale ringed topoi over `f` whose thickened base is `i⁻¹𝒪_{D'}`, with prescribed ideal module `ℱ`.
For `φ : ℱ ⟶ 𝒢` with `DQ_X(ℱ) ⟶ DQ_X(𝒢)` an isomorphism, [Stacks Project, Tag 0D3Q] says that
pushout along `φ` is an equivalence from the solutions for `ℱ` to the solutions for `𝒢`. The body
of the proof of [Stacks Project, Tag 0D3X] uses its essential surjectivity: a solution `𝒪''` for
`𝒢` is the pushout of a solution `𝒪'` for `ℱ`, which in particular maps to `𝒪''` over the change
of ideal module along `φ`. This file proves that form directly from [Stacks Project, Tag 0D3P],
as the source's proof of 0D3Q does.

## Main results

* `AlgebraicGeometry.Space.exists_kernelChangeHom_of_isIso_coherator_map_of_qcqs`.

## References

* [Stacks Project, Tag 0D3Q](https://stacks.math.columbia.edu/tag/0D3Q)
* [Stacks Project, Tag 0D3P](https://stacks.math.columbia.edu/tag/0D3P)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation Deformation.AlgebraExtension
open Deformation.ToposThickening

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian
attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X D D' : AlgebraicSpaces B S hS}

/-- Every solution over the changed ideal module receives a solution of `P`, once
post-composition with `φ` is injective on the maps out of the base ideal. -/
theorem exists_kernelChangeHom_of_injective
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXc : IsQuasiCompactSpace B S hS X.1) (hXs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (f : X ⟶ D) (i : D ⟶ D')
    (P : RingedToposExtensionProblem (smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedTopos B S hS D))
    (hPf : P.f = smallEtaleRingedToposHom B S hS f)
    (eBase : P.baseExtension ≅
      (smallEtaleInverseImageRing B S hS i).obj (smallEtaleRingedTopos B S hS D').O)
    (heBase : eBase.hom ≫ (smallEtaleRingedToposHom B S hS i).fSharpInverseImage =
      P.baseReduction)
    {N : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (structureSheaf B S hS X.1 X.2))}
    (φ : P.G ⟶ N)
    (hDQ : letI := quasicoherentDerivedInclusion_isLeftAdjoint_of_qcqs B S hS hZ X.1 X.2 hXc hXs
      IsIso ((qcohDerivedProp B S hS X).ι.rightAdjoint.map
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).map φ)))
    (hinj : ∀ d₁ d₂ : P.I ⟶ (SheafOfModules.restrictScalars ((sheafCompose
        (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
          P.f.fSharpInverseImage)).obj P.G,
      d₁ ≫ (SheafOfModules.restrictScalars ((sheafCompose (SmallEtale.topology B S hS X.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map P.f.fSharpInverseImage)).map φ =
        d₂ ≫ (SheafOfModules.restrictScalars ((sheafCompose (SmallEtale.topology B S hS X.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map P.f.fSharpInverseImage)).map φ →
        d₁ = d₂)
    (R : (RingedToposExtensionProblem.changeKernel P φ).CompatibleFirstOrderThickening) :
    ∃ P' : P.CompatibleFirstOrderThickening,
      Nonempty (RingedToposExtensionProblem.KernelChangeHom.{u, u + 1, u, u, u + 1, u} (S := P) φ
        P' R) := by
  cases P with
  | mk Pf baseExt red hred hsq I G incl c hzero huniv =>
  subst hPf
  let a₁ := inverseImageBaseMap B S hS (f ≫ i)
  let hF := isPushoutFunctor_sitePushoutFunctor (smallEtaleModelTopology B S hS X.1)
    (modelEquiv B S hS X) a₁ φ
  have : (sitePushoutFunctor (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X) a₁
      φ).IsEquivalence :=
    isEquivalence_of_isPushoutFunctor_of_isIso_coherator_map_of_qcqs B S hS (f ≫ i) hZ hXc hXs
      φ hF hDQ
  have := isLocallySurjective_inverseImage_map B S hS f red hred
  have : (SmallEtale.topology B S hS X.1).HasSheafCompose (forget CommRingCat.{u}) :=
    inferInstance
  exact RingedToposExtensionProblem.exists_kernelChangeHom_of_isPushoutFunctor.{u, u + 1, u, u,
      u + 1, u}
    (A := inverseImageBase B S hS (f ≫ i)) (a := a₁) (N := N)
    (F := sitePushoutFunctor (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X) a₁ φ)
    (X := smallEtaleRingedTopos B S hS X) (B := smallEtaleRingedTopos B S hS D)
    ⟨smallEtaleRingedToposHom B S hS f, baseExt, red, hred, hsq, I, G, incl, c, hzero, huniv⟩
    (thickenedBaseIso B S hS f i eBase) (thickenedBaseIso_hom_comp B S hS f i eBase red heBase)
    φ hF hinj R

/-- **Every solution over the changed ideal module receives a solution of `P`** (the essential
surjectivity of [Stacks Project, Tag 0D3Q], in the form used by [Stacks Project, Tag 0D3X]). Let
`f : X ⟶ D` be a morphism of algebraic spaces with `X` quasi-compact and quasi-separated,
`i : D ⟶ D'` a closed immersion, and `P` a square-zero extension problem of the small étale
ringed topoi over `f` whose thickened base is `i⁻¹𝒪_{D'}` with reduction `i♯`. Let `φ : ℱ ⟶ 𝒢`
be a morphism of `𝒪_X`-modules from the prescribed module of `P` with `DQ_X(ℱ) ⟶ DQ_X(𝒢)` an
isomorphism. Then every solution `𝒪''` of the problem with ideal module `𝒢` receives a morphism
over the change of ideal module along `φ` from a solution `𝒪'` of `P`. -/
theorem exists_kernelChangeHom_of_isIso_coherator_map_of_qcqs
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXc : IsQuasiCompactSpace B S hS X.1) (hXs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (f : X ⟶ D) (i : D ⟶ D') (hi : IsClosedImmersion B S hS i.hom)
    (P : RingedToposExtensionProblem (smallEtaleRingedTopos B S hS X)
      (smallEtaleRingedTopos B S hS D))
    (hPf : P.f = smallEtaleRingedToposHom B S hS f)
    (eBase : P.baseExtension ≅
      (smallEtaleInverseImageRing B S hS i).obj (smallEtaleRingedTopos B S hS D').O)
    (heBase : eBase.hom ≫ (smallEtaleRingedToposHom B S hS i).fSharpInverseImage =
      P.baseReduction)
    {N : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (structureSheaf B S hS X.1 X.2))}
    (φ : P.G ⟶ N)
    (hDQ : letI := quasicoherentDerivedInclusion_isLeftAdjoint_of_qcqs B S hS hZ X.1 X.2 hXc hXs
      IsIso ((qcohDerivedProp B S hS X).ι.rightAdjoint.map
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).map φ)))
    (R : (RingedToposExtensionProblem.changeKernel P φ).CompatibleFirstOrderThickening) :
    ∃ P' : P.CompatibleFirstOrderThickening,
      Nonempty (RingedToposExtensionProblem.KernelChangeHom.{u, u + 1, u, u, u + 1, u} (S := P) φ
        P' R) :=
  exists_kernelChangeHom_of_injective B S hS hZ hXc hXs f i P hPf eBase heBase φ hDQ
    (fun d₁ d₂ h => baseIdeal_comp_injective_of_isIso_coherator_map B S hS f i hZ hXc hXs hi P hPf
      eBase heBase φ hDQ d₁ d₂ h) R

end AlgebraicGeometry.Space

end
