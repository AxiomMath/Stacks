module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ProperDirectImageCompletionMap
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.AuxiliaryIdealClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.BaseIdealSheafPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetImage

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# The algebraization step of Grothendieck's existence theorem for algebraic spaces

In Situation 08B7, let `(𝓕_n)` be a coherent `𝓘`-adic system on `X` with support proper over
`A`, and let `π : X' ⟶ X` be a representable proper morphism which is an isomorphism over the
complement of a closed subspace `Z` with ideal `𝒦`.  If the pullback `(π^*𝓕_n)` is the
completion of a coherent `𝒪_{X'}`-module `𝓕'` with support proper over `A`, and if completion is an
equivalence on every closed subspace of `X` cut out by a power of `𝒦`, then `(𝓕_n)` lies in the
essential image of the completion functor
(`AlgebraicGeometry.Space.C1573.essImage_completionFunctorProperOver_of_pullback_algebraization`).

This is the last paragraph of the proof of Stacks 08BE: Stacks 08BD produces a map
`(𝓕_n) ⟶ (π_*𝓕')^∧` with kernel and cokernel killed by a power of `𝒦`, and Stacks 08BC concludes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573 _root_.CategoryTheory.C1573
variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}

/-- The direct image along a proper morphism of a module with support proper over `A` has
support proper over `A`. -/
theorem C1573.hasProperSupport_modulePushforward_of_isProper
    {X X' : AlgebraicSpaces B (Spec (.of A)) hA}
    (π : X' ⟶ X) (_hπ : yoneda.relativelyRepresentable π.hom)
    (hπp : IsProper B (Spec (.of A)) hA π.hom)
    (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom)
    (hf' : IsLocallyOfFiniteType B (Spec (.of A)) hA (π ≫ f).hom)
    (F : Modules.{u, u} B (Spec (.of A)) hA X'.1 X'.2)
    (hP : IsCoherent B (Spec (.of A)) hA X.1 X.2 ((modulePushforward B (Spec (.of A)) hA π).obj F))
    (hF : HasProperSupport B (Spec (.of A)) hA X'.2 (schemeSpace (baseObject A B hA)).2 (π ≫ f).hom
      hf' ((SheafOfModules.toSheaf _).obj F)) :
    HasProperSupport B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf
      ((SheafOfModules.toSheaf _).obj ((modulePushforward B (Spec (.of A)) hA π).obj F)) := by
  let := hP
  let := isFiniteTypeOnSite_of_isCoherentOnSite B (Spec (.of A)) hA X
    ((modulePushforward B (Spec (.of A)) hA π).obj F)
  have hcl := isClosed_supportOfSheaf_of_isFiniteTypeOnSite B (Spec (.of A)) hA X.1 X.2
    ((modulePushforward B (Spec (.of A)) hA π).obj F)
  obtain ⟨hFcl, hFp⟩ := hF
  have himg := isProperOver_image_of_universallyClosed B (Spec (.of A)) hA X'.2 X.2
    (schemeSpace (baseObject A B hA)).2 π.hom f.hom hπp.2.2 hf' hf _ hFcl hFp
  have hsub := supportOfSheaf_modulePushforward_subset_image B (Spec (.of A)) hA π F
    (isClosed_of_universallyClosed B (Spec (.of A)) hA X.2 π.hom hπp.2.2) hFcl
  exact ⟨hcl, isProperOver_of_subset B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2
    f.hom hf _ _ hcl _ hsub himg⟩

/-- The pullback along a proper morphism of a coherent module with support proper over `A` has
support proper over `A`: its support is the inverse image of the support (Stacks 07TZ), and the
inverse image of a closed subset proper over the base under a proper morphism is proper over the
base (Stacks 0CZG). -/
theorem C1573.hasProperSupport_modulePullback_of_isProper
    {X X' : AlgebraicSpaces B (Spec (.of A)) hA}
    (π : X' ⟶ X) (hπp : IsProper B (Spec (.of A)) hA π.hom)
    (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom)
    (hf' : IsLocallyOfFiniteType B (Spec (.of A)) hA (π ≫ f).hom)
    (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (hFc : IsCoherent B (Spec (.of A)) hA X.1 X.2 F)
    (hF : HasProperSupport B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf
      ((SheafOfModules.toSheaf _).obj F)) :
    HasProperSupport B (Spec (.of A)) hA X'.2 (schemeSpace (baseObject A B hA)).2 (π ≫ f).hom hf'
      ((SheafOfModules.toSheaf _).obj ((modulePullback B (Spec (.of A)) hA π).obj F)) := by
  let := hFc
  have hft := isFiniteTypeOnSite_of_isCoherentOnSite B (Spec (.of A)) hA X F
  obtain ⟨hcl, hp⟩ := hF
  have hpre := isProperOver_preimage_of_isProper B (Spec (.of A)) hA X'.2 X.2
    (schemeSpace (baseObject A B hA)).2 π.hom f.hom hπp hf' hf _ hcl hp
  have heq := supportOfSheaf_modulePullback_eq B (Spec (.of A)) hA π F
    hFc.toIsQuasicoherentOnSite hft
  unfold HasProperSupport
  rw [heq]
  exact ⟨_, hpre⟩

/-- **The algebraization step of Stacks 08BE.**  In Situation 08B7, let `π : X' ⟶ X` be a
representable proper morphism from a Noetherian algebraic space which is an isomorphism over the
complement of a closed subspace `Z`, and suppose completion is an equivalence on the closed
subspaces of `X` cut out by the positive powers of the ideal `𝒦` of `Z`.  If the pullback of a
coherent `I`-adic system `(𝓕_n)` with support proper over `A` is the completion of a coherent
`𝒪_{X'}`-module with support proper over `A`, then `(𝓕_n)` is in the essential image of the
completion functor. -/
theorem C1573.essImage_completionFunctorProperOver_of_pullback_algebraization [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A] (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsFiniteType B (Spec (.of A)) hA f.hom)
    (hsep : IsSeparated B (Spec (.of A)) hA f.hom) (Z : ClosedSubspaces B (Spec (.of A)) hA X.1)
    (h1 : ∀ e : ℕ, 0 < e → ∃ (W : AlgebraicSpaces B (Spec (.of A)) hA) (i : W ⟶ X)
      (hi : IsClosedImmersion B (Spec (.of A)) hA i.hom),
      SheafOfModules.kerIdeal (structureSharp B (Spec (.of A)) hA i) =
        idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (definingIdealSheaf B (Spec (.of A)) hA X Z)
          e (SheafOfModules.unit _) ∧
      letI := fact_isLocallyNoetherian_of_baseObject W (i ≫ f)
        (isLocallyOfFiniteType_closedImmersion_comp i hi f hf.1)
      (completionFunctorProperOver B (Spec (.of A)) hA W.1 (schemeSpace (baseObject A B hA)).1
        W.2 (schemeSpace (baseObject A B hA)).2 (i ≫ f).hom
        (isLocallyOfFiniteType_closedImmersion_comp i hi f hf.1) (baseIdealSubmodule W.1 W.2 I)
        (isQuasicoherentOnSite_baseIdealSubmodule (X := W.1) (hX := W.2) I)).IsEquivalence)
    (E : CoherentAdicSystemsProperOver B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2
      f.hom hf.1 (baseIdealSubmodule X.1 X.2 I))
    {X' : AlgebraicSpaces B (Spec (.of A)) hA}
    (hX' : IsNoetherian B (Spec (.of A)) hA B.contains_terminal X'.1) (π : X' ⟶ X)
    (hπ : yoneda.relativelyRepresentable π.hom) (hπp : IsProper B (Spec (.of A)) hA π.hom)
    (hiso : IsIso ((openComplement B (Spec (.of A)) hA Z.1).fromPreimage π.hom))
    (hπf : IsLocallyOfFiniteType B (Spec (.of A)) hA (π ≫ f).hom)
    (F : Modules.{u, u} B (Spec (.of A)) hA X'.1 X'.2)
    (hF : IsCoherent B (Spec (.of A)) hA X'.1 X'.2 F)
    (hFsupp : HasProperSupport B (Spec (.of A)) hA X'.2 (schemeSpace (baseObject A B hA)).2
      (π ≫ f).hom hπf ((SheafOfModules.toSheaf _).obj F))
    (β : E.obj.obj ⋙ modulePullback B (Spec (.of A)) hA π ≅
      adicQuotientSystem B (Spec (.of A)) hA X'.1 X'.2 (baseIdealSubmodule X'.1 X'.2 I) F) :
    letI := fact_isLocallyNoetherian_of_baseObject X f hf.1
    (completionFunctorProperOver B (Spec (.of A)) hA X.1 (schemeSpace (baseObject A B hA)).1 X.2
      (schemeSpace (baseObject A B hA)).2 f.hom hf.1 (baseIdealSubmodule X.1 X.2 I)
      (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).essImage E := by
  let := fact_isLocallyNoetherian_of_baseObject X f hf.1
  have hXN := isNoetherian_of_isFiniteType_baseObject X f hf hsep
  have β' : E.obj.obj ⋙ modulePullback B (Spec (.of A)) hA π ≅
      adicQuotientSystem B (Spec (.of A)) hA X'.1 X'.2
        (inverseImageIdeal B (Spec (.of A)) hA π hπ (baseIdealSubmodule X.1 X.2 I)) F :=
    (inverseImageIdeal_baseIdealSheaf π hπ I).symm ▸ β
  obtain ⟨hP, α, hα⟩ := exists_hom_completion_modulePushforward_annihilated B (Spec (.of A)) hA
    B.contains_terminal hX' hXN π hπ hπp (baseIdealSubmodule X.1 X.2 I)
    (definingIdealSheaf B (Spec (.of A)) hA X Z)
    (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I) Z rfl hiso E.obj F hF β'
  let H : CoherentModulesProperOver B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2
      f.hom hf.1 :=
    ⟨⟨(modulePushforward B (Spec (.of A)) hA π).obj F, hP⟩,
      hasProperSupport_modulePushforward_of_isProper π hπ hπp f hf.1 hπf F hP hFsupp⟩
  exact essImage_completionFunctorProperOver_of_auxiliaryIdeal I X f hf hsep
    (definingIdealSheaf B (Spec (.of A)) hA X Z)
    (isQuasicoherentOnSite_definingIdealSheaf B (Spec (.of A)) hA X Z) h1 E H
    (ObjectProperty.homMk α) hα

end AlgebraicGeometry.Space

end
