module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialModuleSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialQuasicoherentDerivedUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfPretopology

/-!
# The spectral sequence of a quasi-coherent module along an fppf hypercovering

Let `S` be a scheme, `X` an algebraic space over `S`, `U` a simplicial algebraic space over `S`
and `a : U → X` an augmentation which is an fppf hypercovering of `X` (Section 0DH4). For a
quasi-coherent `𝒪_X`-module `𝓕` with pullbacks `𝓕_p = a_p^*𝓕` to `U_{p, étale}`, there is a
canonical spectral sequence

`E_1^{p,q} = H^q_ét(U_p, 𝓕_p) ⇒ H^{p+q}_ét(X, 𝓕)`

(Stacks 0DHH). It is the spectral sequence of Stacks 0D7E for `a^*𝓕` on the small étale site of
`U`, whose abutment `H^{p+q}_ét(U, a^*𝓕)` is `H^{p+q}_ét(X, 𝓕)` because `𝓕 ⟶ Ra_*(a^*𝓕)` is an
isomorphism for quasi-coherent `𝓕` (Stacks 0DHE), so that
`RΓ(X_étale, 𝓕) = RΓ(U_étale, a^*𝓕)` (Stacks 0DHG).

## Main results

* `moduleSpectralSequence_abutsTo_of_isFppfHypercovering`: **Stacks 0DHH**, the convergence of
  `moduleSpectralSequence`, whose first page is `moduleSpectralSequencePageOneIso`.
* `isHypercoveringAugmentation_pretopology_of_isFppfHypercovering`: an fppf hypercovering in the
  sense of Section 0DH4 is a hypercovering, in the sense of Stacks 09X8, for the chosen fppf
  coverings of a big fppf site of algebraic spaces.

## References

* [Stacks Project, Tag 0DH4](https://stacks.math.columbia.edu/tag/0DH4)
* [Stacks Project, Tag 0DHE](https://stacks.math.columbia.edu/tag/0DHE)
* [Stacks Project, Tag 0DHG](https://stacks.math.columbia.edu/tag/0DHG)
* [Stacks Project, Tag 0DHH](https://stacks.math.columbia.edu/tag/0DHH)
* [Stacks Project, Tag 0D7E](https://stacks.math.columbia.edu/tag/0D7E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.CategoryTheory.Hypercovering

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S)

/-- **A flat, locally finitely presented, surjective morphism is a chosen fppf covering**: the
one-member family `{f : Y → X}` is an fppf covering (Stacks 03Y8), and its index set is no larger
than that of the covering `{id_X}`, which the chosen coverings contain. -/
theorem singleton_mem_pretopology {X Y : T.Spaces} {f : Y ⟶ X}
    (hf : Space.fppfSurjective T.schemeSite S T.scheme_mem f) :
    Presieve.singleton f ∈ T.pretopologyBigFppfPretopology X := by
  refine ⟨PreZeroHypercover.singleton.{u + 2} f, (PreZeroHypercover.presieve₀_singleton f).symm,
    ?_, ?_⟩
  · refine ⟨X.2, fun _ ↦ Y.2, fun _ ↦ hf.1, fun _ ↦ hf.2.1, ?_⟩
    exact Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨PUnit.unit, hf.2.2 x⟩
  · exact (T.coverings_isSite.1 (𝟙 X)).2

/-- **An fppf hypercovering is a hypercovering for the chosen fppf coverings.** An augmented
simplicial algebraic space `a : U → X` whose augmentation `U₀ → X`, canonical morphism
`U₁ → U₀ ×_X U₀` and higher matching morphisms are flat, locally of finite presentation and
surjective (Section 0DH4) is a hypercovering of `X` in `(Spaces/S)_fppf` in the sense of
Stacks 09X8. -/
theorem isHypercoveringAugmentation_pretopology_of_isFppfHypercovering
    {A : SimplicialObject.Augmented T.Spaces} (hA : Space.IsFppfHypercovering A) :
    IsHypercoveringAugmentation T.pretopologyBigFppfPretopology A.left A.hom :=
  ⟨T.singleton_mem_pretopology hA.map_zero, T.singleton_mem_pretopology hA.map_one,
    fun n hn ↦ T.singleton_mem_pretopology (hA.matching n hn)⟩

end AlgebraicGeometry.BigFppfSpaceSite


namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S}

/-- **Stacks 0DHH.** Let `S` be a scheme, `X` an algebraic space over `S`, `U` a simplicial
algebraic space over `S` and `a : U → X` an augmentation which is an fppf hypercovering of `X`.
Let `𝓕` be a quasi-coherent `𝒪_X`-module and `𝓕_p = a_p^*𝓕` its pullback to `U_{p, étale}`. Then
the spectral sequence `moduleSpectralSequence`, with first page
`E_1^{p,q} = H^q_ét(U_p, 𝓕_p)` (`moduleSpectralSequencePageOneIso`), converges to
`H^{p+q}_ét(X, 𝓕)`. The algebraic spaces are those of a big fppf site `T` of algebraic spaces
over `S` (Stacks 0DBV). -/
@[stacks 0DHH "the spectral sequence converges to `H^{p+q}_ét(X, 𝓕)`"]
theorem moduleSpectralSequence_abutsTo_of_isFppfHypercovering
    {A : SimplicialObject.Augmented T.Spaces} (hA : IsFppfHypercovering A)
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem A.right).O))
    [F.IsQuasicoherentOnSite] :
    CategoryTheory.SpectralSequence.AbutsTo ((moduleSpectralSequence A.hom).obj F)
      (fun n => if 0 ≤ n then
        ((spacesEtaleRingedTopos T.schemeSite S T.scheme_mem
            A.right).moduleGlobalSections.rightDerived n.toNat).obj F
        else AddCommGrpCat.of PUnit.{u + 2}) :=
  have h := T.isHypercoveringAugmentation_pretopology_of_isFppfHypercovering hA
  moduleSpectralSequence_abutsTo_of_isIso_unit A.hom F
    (isIso_augmentationRingedToposHom_unit_app h F)
    (isZero_rightDerived_augmentationRingedToposHom_pushforwardModules_pullbackModules h F)

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
