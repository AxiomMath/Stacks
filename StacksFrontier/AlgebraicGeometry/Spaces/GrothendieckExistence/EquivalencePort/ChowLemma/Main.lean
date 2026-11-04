module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChowLemma.Approximation
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Chow's lemma for algebraic spaces

Let `f : X ⟶ Y` be a separated morphism of finite type of algebraic spaces over a scheme `S`,
with `Y` separated and Noetherian. Then there are a dense open subspace `U ⊆ X`, a
`U`-admissible blowup `X' ⟶ X` and an immersion `X' ⟶ ℙⁿ_Y` over `Y` (Stacks 088U, Knutson IV
Theorem 3.1).

## Main results

* `AlgebraicGeometry.Space.C1573.hasEtaleLocalProperty_relocalize`: an étale-local property of an
  algebraic space survives the lower-shriek extension.
* `AlgebraicGeometry.Space.C1573.exists_isAdmissibleBlowup_isImmersion_projectiveSpace`: Chow's
  lemma.

## References

* [Stacks Project, Tag 088U](https://stacks.math.columbia.edu/tag/088U)
* [Kn, IV, Theorem 3.1]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

open _root_.C1573 _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573
  _root_.CategoryTheory.Limits.C1573
/-- **An étale-local property survives the lower-shriek extension.** If an algebraic space over
`S` has a surjective étale atlas by a scheme with an étale-local property `P`, so has its
extension along `g : S ⟶ S'`. -/
theorem C1573.hasEtaleLocalProperty_relocalize {B : BigFppfSite.{u}} {S S' : Scheme.{u}}
    {hS : B.Contains S} {hS' : B.Contains S'} (g : B.obj hS ⟶ B.obj hS')
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.etalePrecoverage] (hF : HasEtaleLocalProperty B S hS F P) :
    HasEtaleLocalProperty B S' hS' ((OverShriek.relocalizePresheafFunctor g).obj F) P := by
  have := MorphismProperty.RespectsIso.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S' hS')
  have := MorphismProperty.RespectsIso.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S' hS')
  obtain ⟨A, a, hsurj, hetale, hP⟩ := hF
  have hpre : ∀ {Q : MorphismProperty Scheme.{u}} [Q.RespectsIso],
      MorphismProperty.presheaf (Q.inverseImage (BigFppfOver.toScheme B S hS)) a →
        MorphismProperty.presheaf (Q.inverseImage (BigFppfOver.toScheme B S' hS'))
          ((OverShriek.relocalizeYonedaIso g).inv.app A ≫
            (OverShriek.relocalizePresheafFunctor g).map a) := by
    intro Q _ hQ
    have := MorphismProperty.RespectsIso.inverseImage Q (BigFppfOver.toScheme B S' hS')
    have h := OverShriek.presheaf_map_relocalize g
      (P₂ := Q.inverseImage (BigFppfOver.toScheme B S' hS')) (fun _ hk => hk) hQ
    have sq : IsPullback ((OverShriek.relocalizeYonedaIso g).inv.app A)
        ((OverShriek.relocalizeYonedaIso g).inv.app A ≫
          (OverShriek.relocalizePresheafFunctor g).map a)
        ((OverShriek.relocalizePresheafFunctor g).map a) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by simp⟩
    exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sq h
  exact ⟨(Over.map g).obj A, _, hpre hsurj, hpre hetale, hP⟩

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 088U, Chow's lemma (Knutson IV Theorem 3.1).** Let `f : X ⟶ Y` be a separated
morphism of finite type of algebraic spaces over `S`, with `Y` separated and Noetherian. Then
there are a dense open subspace `U ⊆ X`, a `U`-admissible blowup `π : X' ⟶ X` and an immersion
`i : X' ⟶ ℙⁿ_Y` with `π ≫ f = i ≫ pr₁`.

Projective space over `Y` is the fibre product over the terminal presheaf of `Y` and the
restricted functor of points of `ℙⁿ_S`. Separatedness of `Y` is the absolute notion of Stacks
03BS, and so is the quasi-separatedness in its Noetherianity. -/
theorem C1573.exists_isAdmissibleBlowup_isImmersion_projectiveSpace
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hsep : IsSeparated B S hS f.hom)
    (hft : IsFiniteType B S hS f.hom) (hYsep : IsAbsolutelySeparated B S hS hZ Y.1)
    (hYnoeth : IsNoetherian B S hS hZ Y.1) :
    letI := pointTopology B S hS X.1
    ∃ (U : OpenSubspaces B S hS X.1), DenseRange (pointsMap B S hS U.1.toFunctor U.1.ι) ∧
      ∃ (n : ℕ) (X' : AlgebraicSpaces B S hS) (π : X' ⟶ X)
        (i : X'.1 ⟶ pullback (terminal.from Y.1)
          (terminal.from ((Over.post B.inclusion).op ⋙
            yoneda.obj (Over.mk (projectiveSpaceOver n S ↘ S))))),
        IsAdmissibleBlowup B S hS U π ∧ IsImmersion B S hS i ∧
          π.hom ≫ f.hom = i ≫ pullback.fst _ _ := by
  let := pointTopology B S hS X.1
  set g := integersMap B S hS hZ with hg
  set ΛX := viewOverIntegersSpace B S hS hZ X with hΛX
  set ΛY := viewOverIntegersSpace B S hS hZ Y with hΛY
  have hft' : IsFiniteType B (⊤_ Scheme.{u}) hZ
      ((OverShriek.relocalizePresheafFunctor g).map f.hom) :=
    (isFiniteType_relocalize_iff B S hS (⊤_ Scheme.{u}) hZ g f.hom).2 hft
  have hsep' : IsSeparated B (⊤_ Scheme.{u}) hZ
      ((OverShriek.relocalizePresheafFunctor g).map f.hom) :=
    isSeparated_relocalize B S hS hZ g hsep
  have hYN : HasEtaleLocalProperty B (⊤_ Scheme.{u}) hZ ΛY.1
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    hasEtaleLocalProperty_relocalize g _ hYnoeth.2.2
  have hfp' : IsFinitePresentation B (⊤_ Scheme.{u}) hZ
      ((OverShriek.relocalizePresheafFunctor g).map f.hom) :=
    isFinitePresentation_of_isFiniteType B (⊤_ Scheme.{u}) hZ ΛX.2 ΛY.2 _ hYN hft'
      (isQuasiSeparated_of_isSeparated B (⊤_ Scheme.{u}) hZ hsep')
  have hYqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ ΛY.1 :=
    (isQuasiCompactSpace_relocalize_iff B S hS (⊤_ Scheme.{u}) hZ g Y.1).2 hYnoeth.1
  have hYsep' : IsAbsolutelySeparated B (⊤_ Scheme.{u}) hZ hZ ΛY.1 :=
    (isAbsolutelySeparated_viewOverIntegers_iff B S hS hZ Y.1).2 hYsep
  have hXsep' : IsAbsolutelySeparated B (⊤_ Scheme.{u}) hZ hZ ΛX.1 :=
    (isAbsolutelySeparated_viewOverIntegers_iff B S hS hZ X.1).2
      (isAbsolutelySeparated_of_isSeparated B S hS hZ hYsep hsep)
  have hXqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ ΛX.1 :=
    isQuasiCompactSpace_source_of_isQuasiCompact B (⊤_ Scheme.{u}) hZ ΛY.2 hYqc hft'.2
  have hXN : HasEtaleLocalProperty B (⊤_ Scheme.{u}) hZ ΛX.1
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B (⊤_ Scheme.{u}) hZ ΛX.2 ΛY.2 _ hft'.1 hYN
  obtain ⟨d⟩ := exists_chowDatum_of_isFinitePresentation hZ (X := ΛX) (Y := ΛY) _ hfp' hYqc
    hYsep' hXsep' hXqc hXN
  obtain ⟨dS⟩ := ChowDatum.ofViewOverIntegers hZ Y.2 f.hom d
  obtain ⟨U, hU, N, W, π, iN, hadm, himm, hcomp, -⟩ := dS.exists_isAdmissibleBlowup
  have hT : IsIso (terminal.from (yoneda.obj (Over.mk (𝟙 (B.obj hS))) :
      (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
    isIso_of_isTerminal (isTerminal_yoneda_obj_base B S hS) terminalIsTerminal _
  let ψ : projectiveSpacePresheaf B S hS Y.1 N ⟶ pullback (terminal.from Y.1)
      (terminal.from ((Over.post B.inclusion).op ⋙
        yoneda.obj (Over.mk (projectiveSpaceOver N S ↘ S)))) :=
    pullback.map _ _ _ _ (𝟙 _) (projectiveSpaceFunctorIso B S hS N).inv
      (terminal.from _) (terminal.hom_ext _ _) (terminal.hom_ext _ _)
  have hψ : IsIso ψ := by
    dsimp only [ψ]
    infer_instance
  refine ⟨U, hU, N, schemeSpace W, π, iN ≫ ψ, hadm, ?_, ?_⟩
  · exact isImmersion_of_isPullback' (IsPullback.of_horiz_isIso (fst := 𝟙 _) (g := inv ψ)
      ⟨(Category.id_comp iN).trans ((Category.assoc _ _ _).trans
        ((congrArg (iN ≫ ·) (IsIso.hom_inv_id ψ)).trans (Category.comp_id iN))).symm⟩) himm
  · have hψfst : ψ ≫ pullback.fst _ _ = pullback.fst _ _ := by simp [ψ]
    exact ((Category.assoc _ _ _).trans ((congrArg (iN ≫ ·) hψfst).trans hcomp)).symm

end AlgebraicGeometry.Space

end
