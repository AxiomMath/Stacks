module

public import StacksFrontier.AlgebraicGeometry.Spaces.ThickenedBaseIdealInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickenedBasePushoutQcqs
import StacksCore.Tactic.StacksAttribute

/-!
# Pushout of solutions over a thickened base is an equivalence

Let `f : X ⟶ D` be a morphism of algebraic spaces with `X` quasi-compact and quasi-separated, and
let `D ⊂ D'` be a first order thickening, with inclusion `i`. Consider the square-zero extension
problem (91.13.0.1) of [Stacks Project, Tag 08UF] of the small étale ringed topoi over `f`, whose
thickened base is `i⁻¹𝒪_{D'}` with reduction `i♯`, and whose prescribed ideal module is `ℱ`. For
`φ : ℱ ⟶ 𝒢` let `FT` be pushout along `φ`, from the solutions for `ℱ` to the solutions for `𝒢`
(characterised by the universal property of the pushout). [Stacks Project, Tag 0D3Q] says that
`FT` is an equivalence when `DQ_X(ℱ) ⟶ DQ_X(𝒢)` is an isomorphism.

The source's proof: a solution is in particular an extension `0 ⟶ ℱ ⟶ 𝒪' ⟶ 𝒪_X ⟶ 0` of
`f⁻¹𝒪_{D'}`-algebras, and the solutions are the full subcategory of those on which the map
`c_{𝒪'} : f⁻¹𝒥 ⟶ ℱ` they induce is the prescribed `c`; [Stacks Project, Tag 0D3P], applied to
`X ⟶ D'`, gives an equivalence `F` of extensions with `c_{F(𝒪')} = φ ∘ c_{𝒪'}`, which carries one
subcategory onto the other. The last step uses that post-composition with `φ` is injective on
maps `f⁻¹𝒥 ⟶ ℱ`, which the source leaves tacit: those are maps out of the quasi-coherent
`(f ≫ i)^*𝓘`, `𝓘` the ideal of `D` in `D'`, and `DQ_X(φ)` is an isomorphism.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_of_isKernelPushoutFunctor_of_isIso_coherator_map_of_qcqs`:
  [Stacks Project, Tag 0D3Q].

## References

* [Stacks Project, Tag 0D3Q](https://stacks.math.columbia.edu/tag/0D3Q)
* [Stacks Project, Tag 0D3P](https://stacks.math.columbia.edu/tag/0D3P)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation.ToposThickening

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian
attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X D D' : AlgebraicSpaces B S hS}

/-- **[Stacks Project, Tag 0D3Q].** Let `f : X ⟶ D` be a morphism of algebraic spaces with `X`
quasi-compact and quasi-separated, and `i : D ⟶ D'` a closed immersion (for instance a first order
thickening). Let `P` be a square-zero extension problem (91.13.0.1) of the small étale ringed
topoi over `f` whose thickened base is `i⁻¹𝒪_{D'}`, its reduction being `i♯`, with prescribed
ideal module `ℱ`. Let `φ : ℱ ⟶ 𝒢` be a morphism of `𝒪_X`-modules with `DQ_X(ℱ) ⟶ DQ_X(𝒢)` an
isomorphism, `DQ_X` the right adjoint of `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` of [Stacks Project, Tag 0CR4],
and let `FT` be pushout along `φ` from the solutions of `P` to those of the problem with ideal
module `𝒢` (characterised by the universal property of the pushout). Then `FT` is an equivalence
of categories.

The source asks `D ⊂ D'` to be a first order thickening; the argument only uses that `i` is a
closed immersion, the square-zero condition being part of the problem `P`. -/
@[stacks 0D3Q]
theorem isEquivalence_of_isKernelPushoutFunctor_of_isIso_coherator_map_of_qcqs
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
    {FT : P.CompatibleFirstOrderThickening ⥤
      (RingedToposExtensionProblem.changeKernel P φ).CompatibleFirstOrderThickening}
    (hFT : RingedToposExtensionProblem.IsKernelPushoutFunctor.{u, u + 1, u, u, u + 1, u}
      (S := P) φ FT)
    (hDQ : letI := quasicoherentDerivedInclusion_isLeftAdjoint_of_qcqs B S hS hZ X.1 X.2 hXc hXs
      IsIso ((qcohDerivedProp B S hS X).ι.rightAdjoint.map
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).map φ))) :
    FT.IsEquivalence :=
  isEquivalence_of_isKernelPushoutFunctor_of_injective B S hS f i hZ hXc hXs P hPf eBase heBase φ
    hFT hDQ fun d₁ d₂ h =>
      baseIdeal_comp_injective_of_isIso_coherator_map B S hS f i hZ hXc hXs hi P hPf eBase heBase φ
        hDQ d₁ d₂ h

end AlgebraicGeometry.Space

end
