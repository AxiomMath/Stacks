module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ImpliedProperties.RegularSpaceAlterationLocalDomain
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationGenericStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactDiagonalQuasiAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints

/-!
# A normal local domain with a proper surjection from a regular space has normal completion

Let `(A, 𝔪)` be a Noetherian local normal domain and let `g : X ⟶ Spec A` be a proper surjective
morphism from a regular algebraic space. Then the `𝔪`-adic completion of `A` is a normal ring.

This is part (3) of [Stacks, Tag 0BHU] with the alteration replaced by a proper surjection, so
`X` need not be integral.

## Main results

* `AlgebraicGeometry.Space.isNormalRing_adicCompletion_tensor_globalFunctions_of_isProper`: the
  completed base change `Aˆ ⊗_A Γ(X, 𝒪_X)` is a normal ring, `Γ(X, 𝒪_X)` is a finite `A`-module
  and `A ⟶ Γ(X, 𝒪_X)` is injective.
* `AlgebraicGeometry.Space.isNormalRing_adicCompletion_of_isProper_of_isSurjective_of_isRegular`:
  the completion of `A` is a normal ring.

## References

* [Stacks Project, Tag 0BHU](https://stacks.math.columbia.edu/tag/0BHU)
* [Stacks Project, Tag 0BGH](https://stacks.math.columbia.edu/tag/0BGH)
* [Stacks Project, Tag 0BHQ](https://stacks.math.columbia.edu/tag/0BHQ)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

/-- **The completed global functions of a proper surjection from a regular space.** For `A` a
Noetherian local ring which is reduced and `g : X ⟶ Spec A` proper and surjective with `X`
regular, `C = Γ(X, 𝒪_X)` is a finite `A`-module, `A ⟶ C` is injective and `Aˆ ⊗_A C` is a
normal ring. -/
theorem isNormalRing_adicCompletion_tensor_globalFunctions_of_isProper
    (A : Type u) [CommRing A] [_root_.IsReduced A] [IsNoetherianRing A] [IsLocalRing A]
    (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (g : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hprop : IsProper B (Spec (.of A)) hA g) (hsurj : IsSurjective B (Spec (.of A)) hA g)
    (hreg : HasEtaleLocalProperty B (Spec (.of A)) hA X (fun T : Scheme.{u} => IsRegular T)) :
    Module.Finite A (globalFunctions B (Spec (.of A)) hA X) ∧
      Function.Injective (algebraMap A (globalFunctions B (Spec (.of A)) hA X)) ∧
      IsNormalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A]
        globalFunctions B (Spec (.of A)) hA X) := by
  classical
  let Xs : AlgebraicSpaces B (Spec (.of A)) hA := ⟨X, hX⟩
  have hred : HasEtaleLocalProperty B (Spec (.of A)) hA X
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T) :=
    hasEtaleLocalProperty_isReduced_of_isNormal B (Spec (.of A)) hA X
      (isNormal_of_isRegular B (Spec (.of A)) hA X hreg)
  have hfin : Module.Finite A (globalFunctions B (Spec (.of A)) hA X) :=
    module_finite_globalFunctions_of_isProper B A hA Xs g hprop hred
  have hinj : Function.Injective (algebraMap A (globalFunctions B (Spec (.of A)) hA X)) :=
    injective_algebraMap_globalFunctions_of_isProper B A hA Xs g hprop hsurj
  refine ⟨hfin, hinj, ?_⟩
  let Ac := AdicCompletion (IsLocalRing.maximalIdeal A) A
  have hAc : B.Contains (Spec (.of Ac)) := B.contains_spec_adicCompletion hA _
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  let Ys : AlgebraicSpaces B (Spec (.of A)) hA :=
    ⟨completionSpace A B hA hAc g, isAlgebraicSpace_completionSpace A B hA hAc g hX⟩
  have hX' : IsPullback (completionProjection A B hA hAc g)
      (pullback.snd g (completionBaseMap A B hA hAc)) g
      (yoneda.map (siteTerminalHom B (Spec (.of A)) hA (specAlgebraObj A Ac B hA hAc))) :=
    IsPullback.of_hasPullback g (completionBaseMap A B hA hAc)
  have hqc : IsQuasiCompactSpace B (Spec (.of A)) hA X :=
    isQuasiCompactSpace_of_isProper_baseObject A B hA X hX g hprop
  have hterm : IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hA)))) :=
    IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal
  have hsep : IsAbsolutelySeparated B (Spec (.of A)) hA hZ X :=
    (isAbsolutelySeparated_iff_isSeparatedOver B (Spec (.of A)) hA hZ inferInstance hX).mpr
      ((isSeparatedOver_iff_isSeparated_of_isTerminal B (Spec (.of A)) hA hterm g).mpr hprop.1)
  have hdec : IsDecentSpace B (Spec (.of A)) hA X :=
    isDecentSpace_of_isAbsolutelyQuasiSeparated B (Spec (.of A)) hA X hX
      (isQuasiSeparatedOver_of_isSeparatedOver B (⊤_ Scheme.{u}) hZ _ hsep)
  have hYreg : HasEtaleLocalProperty B (Spec (.of A)) hA (completionSpace A B hA hAc g)
      (fun T : Scheme.{u} => IsRegular T) :=
    (hasEtaleLocalProperty_isRegular_completionSpace_iff_of_isProper A B hA hAc g hX
      hdec hprop).mp hreg
  have hYnorm := isNormal_of_isRegular B (Spec (.of A)) hA _ hYreg
  have hYnoeth : HasEtaleLocalProperty B (Spec (.of A)) hA (completionSpace A B hA hAc g)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) := by
    obtain ⟨U, φ, hs, he, hr⟩ := hYreg
    exact ⟨U, φ, hs, he, isLocallyNoetherian_of_isRegular hr⟩
  obtain ⟨e⟩ := nonempty_ringEquiv_globalFunctions_baseChange A Ac hAc (X := Xs) (X' := Ys) g hX'
    hZ hqc hsep
  have hTnoeth : IsNoetherianRing (Ac ⊗[A] globalFunctions B (Spec (.of A)) hA X) :=
    IsNoetherianRing.of_finite Ac _
  have hGnoeth : IsNoetherianRing (globalFunctions B (Spec (.of A)) hA Ys.obj) :=
    isNoetherianRing_of_ringEquiv _ e.symm
  exact IsNormalRing.congr e (isNormalRing_globalFunctions_of_isPullback A Ac hAc (X := Xs)
    (X' := Ys) g hX' hZ hqc hsep hYnorm hYnoeth hGnoeth)

/-- **A Noetherian local normal domain with a proper surjection from a regular algebraic space
has normal completion.** Let `A` be a Noetherian local normal domain and `g : X ⟶ Spec A` a
proper surjective morphism with `X` regular. Then the `𝔪`-adic completion of `A` is a normal
ring. -/
theorem isNormalRing_adicCompletion_of_isProper_of_isSurjective_of_isRegular
    (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    [IsLocalRing A]
    (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (g : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hprop : IsProper B (Spec (.of A)) hA g) (hsurj : IsSurjective B (Spec (.of A)) hA g)
    (hreg : HasEtaleLocalProperty B (Spec (.of A)) hA X (fun T : Scheme.{u} => IsRegular T)) :
    IsNormalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  obtain ⟨hfin, hinj, hCD⟩ :=
    isNormalRing_adicCompletion_tensor_globalFunctions_of_isProper A B hA X hX g hprop hsurj
      hreg
  have h := isNormalRing_adicCompletion_of_finite_injective A A
    (globalFunctions B (Spec (.of A)) hA X) hinj (IsNormalRing.of_isIntegrallyClosed A)
    (IsNormalRing.congr (ofTensorProductAlgEquiv (IsLocalRing.maximalIdeal A)
      (globalFunctions B (Spec (.of A)) hA X)).toRingEquiv hCD)
  have hid : (IsLocalRing.maximalIdeal A).map (algebraMap A A) =
      IsLocalRing.maximalIdeal A := by simp
  rwa [hid] at h

end AlgebraicGeometry.Space

end
