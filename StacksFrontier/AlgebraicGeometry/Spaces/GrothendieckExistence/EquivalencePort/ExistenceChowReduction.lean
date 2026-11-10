module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ExistenceAlgebraizationStep
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ExistenceChowReductionAux
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.RepresentedAlgebraizationTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ModulePullbackIdealPowerCompatible
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChowLemma.Main
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProjectiveSpaceContracted
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.C1573Port.FormalGeometry.CompletionProper.OpenExtensionExistence

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# The Chow reduction of Grothendieck's existence theorem for algebraic spaces

In Situation 08B7, suppose completion is essentially surjective on every closed subspace of `X`
missing a point of `X`.  Then every coherent `I`-adic system on `X` with support proper over `A`
is the completion of a coherent module with support proper over `A`
(`AlgebraicGeometry.Space.C1573.essImage_completionFunctorProperOver_of_essSurj_closedSubspaces`).

This is the main step of the proof of Stacks 08BE: Chow's lemma (Stacks 088U) gives a blowup
`π : X' ⟶ X`, an isomorphism over a dense open, with `X'` immersed into `ℙⁿ_A`; so `X'` is a
scheme, open in a projective `A`-scheme `Y'` (Stacks 01WA); the pullback of `(𝓕_n)` to `X'` is
algebraized on the scheme (`Stacks.Algebraization.C1573.exists_completion_iso_of_opens`) and
carried back to the algebraic space; and Stacks 08BD with Stacks 08BC conclude.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open _root_.C1573 _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573
  _root_.CategoryTheory.C1573 _root_.CategoryTheory.Limits.C1573
attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}

/-- **A space immersed into projective space over a Noetherian base is an open subscheme of a
proper scheme over the base.**  The represented scheme of the immersion is H-quasi-projective,
so open in an H-projective scheme by Stacks 01WA. -/
theorem C1573.exists_yoneda_iso_opens_of_isImmersion_projectiveSpace [IsNoetherianRing A]
    {X' : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u} (n : ℕ)
    (i : X' ⟶ yoneda.obj (projectiveSpaceSiteObject B (Spec (.of A)) hA n))
    (hi : IsImmersion B (Spec (.of A)) hA i) :
    ∃ (Y' : Scheme.{u}) (p : Y' ⟶ Spec (.of A)) (V : Y'.Opens) (hV : B.Contains V.toScheme),
      _root_.AlgebraicGeometry.IsProper p ∧
        Nonempty (yoneda.obj (Over.mk (⟨V.ι ≫ p⟩ : B.obj hV ⟶ B.obj hA)) ≅ X') := by
  obtain ⟨Q, eX, g, -, himm⟩ := exists_yoneda_iso_of_isImmersion i hi
  let j0 : (BigFppfOver.toScheme B (Spec (.of A)) hA).obj Q ⟶
      projectiveSpaceOver n (Spec (.of A)) :=
    (BigFppfOver.toScheme B (Spec (.of A)) hA).map g
  have hstr : j0 ≫ (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A)) =
      B.inclusion.map Q.hom := by
    have h := congrArg B.inclusion.map (Over.w g)
    rwa [Functor.map_comp] at h
  have : _root_.AlgebraicGeometry.IsNoetherian (projectiveSpaceOver n (Spec (.of A))) :=
    projectiveSpaceOver_isNoetherian n (Spec (.of A))
  have : _root_.AlgebraicGeometry.IsImmersion j0 := himm
  have : TopologicalSpace.NoetherianSpace ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj Q) :=
    (j0.isEmbedding.isInducing).noetherianSpace
  have hHQP : IsHQuasiProjective (B.inclusion.map Q.hom) :=
    ⟨n, j0, himm, quasiCompact_of_noetherianSpace_source j0, hstr⟩
  obtain ⟨Y', j, p, _, hp, hjp⟩ :=
    exists_isOpenImmersion_isProjectiveMorphism_of_isHQuasiProjective hHQP
  have hV : B.Contains j.opensRange.toScheme :=
    contains_of_isImmersion B Q.left.2 j.isoOpensRange.inv
  let U' : BigFppfOver B (Spec (.of A)) hA :=
    Over.mk (⟨j.opensRange.ι ≫ p⟩ : B.obj hV ⟶ B.obj hA)
  let eB : Q.left ≅ U'.left := ObjectProperty.isoMk _ j.isoOpensRange
  let eQ : Q ≅ U' := Over.isoMk eB (B.inclusion.map_injective (by
    change j.isoOpensRange.hom ≫ j.opensRange.ι ≫ p = B.inclusion.map Q.hom
    rw [Scheme.Hom.isoOpensRange_hom_ι_assoc]
    exact hjp))
  exact ⟨Y', p, j.opensRange, hV, (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.1 hp).2,
    ⟨(yoneda.mapIso eQ).symm ≪≫ eX⟩⟩

/-- In Situation 08B7, if completion is essentially surjective on every closed subspace of `X`
missing a point, and `Z` is a closed subspace missing a point, then completion is an equivalence on
the closed subspace cut out by each power of the ideal of `Z`. -/
private theorem C1573.exists_closedImmersion_idealPowerMultiple_isEquivalence_completion
    [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsFiniteType B (Spec (.of A)) hA f.hom)
    (hsub : ∀ (W : AlgebraicSpaces B (Spec (.of A)) hA) (i : W ⟶ X)
      (hi : IsClosedImmersion B (Spec (.of A)) hA i.hom),
      Set.range (pointsMap B (Spec (.of A)) hA W.1 i.hom) ≠ Set.univ →
      letI := fact_isLocallyNoetherian_of_baseObject W (i ≫ f)
        (isLocallyOfFiniteType_closedImmersion_comp i hi f hf.1)
      (completionFunctorProperOver B (Spec (.of A)) hA W.1 (schemeSpace (baseObject A B hA)).1
        W.2 (schemeSpace (baseObject A B hA)).2 (i ≫ f).hom
        (isLocallyOfFiniteType_closedImmersion_comp i hi f hf.1) (baseIdealSubmodule W.1 W.2 I)
        (isQuasicoherentOnSite_baseIdealSubmodule (X := W.1) (hX := W.2) I)).EssSurj)
    (Z : ClosedSubspaces B (Spec (.of A)) hA X.1)
    (hZ : Set.range (pointsMap B (Spec (.of A)) hA Z.1.toFunctor Z.1.ι) ≠ Set.univ) (e : ℕ) :
    ∃ (W : AlgebraicSpaces B (Spec (.of A)) hA) (i : W ⟶ X)
      (hi : IsClosedImmersion B (Spec (.of A)) hA i.hom),
      SheafOfModules.kerIdeal (structureSharp B (Spec (.of A)) hA i) =
        idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 (definingIdealSheaf B (Spec (.of A)) hA X Z)
          e (SheafOfModules.unit _) ∧
      letI := fact_isLocallyNoetherian_of_baseObject W (i ≫ f)
        (isLocallyOfFiniteType_closedImmersion_comp i hi f hf.1)
      (completionFunctorProperOver B (Spec (.of A)) hA W.1 (schemeSpace (baseObject A B hA)).1
        W.2 (schemeSpace (baseObject A B hA)).2 (i ≫ f).hom
        (isLocallyOfFiniteType_closedImmersion_comp i hi f hf.1) (baseIdealSubmodule W.1 W.2 I)
        (isQuasicoherentOnSite_baseIdealSubmodule (X := W.1) (hX := W.2) I)).IsEquivalence := by
  have hKqc := isQuasicoherentOnSite_definingIdealSheaf B (Spec (.of A)) hA X Z
  have hJqc := isQuasicoherentOnSite_idealPowerMultiple B (Spec (.of A)) hA X.1 X.2
    (definingIdealSheaf B (Spec (.of A)) hA X Z) (SheafOfModules.unit _)
    (SheafOfModules.isQuasicoherentOnSite_unit _) hKqc e
  obtain ⟨Ze, hZe⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B (Spec (.of A)) hA X
    _ hJqc
  let ie : (⟨Ze.1.toFunctor, Ze.2.1⟩ : AlgebraicSpaces B (Spec (.of A)) hA) ⟶ X :=
    ObjectProperty.homMk Ze.1.ι
  have hie : IsClosedImmersion B (Spec (.of A)) hA ie.hom := Ze.2.2
  refine ⟨_, ie, hie, (kerIdeal_structureSharp_ι B (Spec (.of A)) hA X Ze).trans hZe, ?_⟩
  let := fact_isLocallyNoetherian_of_baseObject _ (ie ≫ f)
    (isLocallyOfFiniteType_closedImmersion_comp ie hie f hf.1)
  have hrange : Set.range (pointsMap B (Spec (.of A)) hA _ ie.hom) ≠ Set.univ := fun htop =>
    hZ <| Set.eq_univ_of_univ_subset fun x _ =>
      range_pointsMap_ι_subset_of_definingIdealSheaf_eq_idealPowerMultiple B (Spec (.of A)) hA X Z
        Ze e hZe (show x ∈ Set.range (pointsMap B (Spec (.of A)) hA _ ie.hom) from
          htop ▸ Set.mem_univ _)
  have := hsub _ ie hie hrange
  have hFF := completionFunctorProperOverFullyFaithful (X := ⟨Ze.1.toFunctor, Ze.2.1⟩) I (ie ≫ f)
    (isLocallyOfFiniteType_closedImmersion_comp ie hie f hf.1)
  have := hFF.full
  have := hFF.faithful
  exact { }

/-- In Situation 08B7, if completion is essentially surjective on every closed subspace of `X`
missing a point, and a proper `π : X' ⟶ X`, an isomorphism over the complement of a closed
subspace `Z` missing a point, has source an open of a proper `A`-scheme, then every coherent
`I`-adic system on `X` with support proper over `A` is in the essential image of completion. -/
private theorem C1573.essImage_completionFunctorProperOver_of_isProper_of_yoneda_iso_opens
    [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsFiniteType B (Spec (.of A)) hA f.hom)
    (hsep : IsSeparated B (Spec (.of A)) hA f.hom)
    (hsub : ∀ (W : AlgebraicSpaces B (Spec (.of A)) hA) (i : W ⟶ X)
      (hi : IsClosedImmersion B (Spec (.of A)) hA i.hom),
      Set.range (pointsMap B (Spec (.of A)) hA W.1 i.hom) ≠ Set.univ →
      letI := fact_isLocallyNoetherian_of_baseObject W (i ≫ f)
        (isLocallyOfFiniteType_closedImmersion_comp i hi f hf.1)
      (completionFunctorProperOver B (Spec (.of A)) hA W.1 (schemeSpace (baseObject A B hA)).1
        W.2 (schemeSpace (baseObject A B hA)).2 (i ≫ f).hom
        (isLocallyOfFiniteType_closedImmersion_comp i hi f hf.1) (baseIdealSubmodule W.1 W.2 I)
        (isQuasicoherentOnSite_baseIdealSubmodule (X := W.1) (hX := W.2) I)).EssSurj)
    (Z : ClosedSubspaces B (Spec (.of A)) hA X.1)
    (hZ : Set.range (pointsMap B (Spec (.of A)) hA Z.1.toFunctor Z.1.ι) ≠ Set.univ)
    {X' : AlgebraicSpaces B (Spec (.of A)) hA} (π : X' ⟶ X)
    (hπ0 : IsProper B (Spec (.of A)) hA π.hom)
    (hbl : IsIso ((openComplement B (Spec (.of A)) hA Z.1).fromPreimage π.hom))
    {Y' : Scheme.{u}} (p : Y' ⟶ Spec (.of A)) [_root_.AlgebraicGeometry.IsProper p]
    (V : Y'.Opens) (hV : B.Contains V.toScheme)
    (eX : yoneda.obj (Over.mk (⟨V.ι ≫ p⟩ : B.obj hV ⟶ B.obj hA)) ≅ X'.1)
    (E : CoherentAdicSystemsProperOver B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2
      f.hom hf.1 (baseIdealSubmodule X.1 X.2 I)) :
    letI := fact_isLocallyNoetherian_of_baseObject X f hf.1
    (completionFunctorProperOver B (Spec (.of A)) hA X.1 (schemeSpace (baseObject A B hA)).1 X.2
      (schemeSpace (baseObject A B hA)).2 f.hom hf.1 (baseIdealSubmodule X.1 X.2 I)
      (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).essImage E := by
  let := fact_isLocallyNoetherian_of_baseObject X f hf.1
  let U' : BigFppfOver B (Spec (.of A)) hA := Over.mk (⟨V.ι ≫ p⟩ : B.obj hV ⟶ B.obj hA)
  let π' : schemeSpace U' ⟶ X := ObjectProperty.homMk (eX.hom ≫ π.hom)
  have hπ : yoneda.relativelyRepresentable π'.hom :=
    relativelyRepresentable_of_isAlgebraicSpace B (Spec (.of A)) hA X.2 π'.hom
  have hπp : IsProper B (Spec (.of A)) hA π'.hom :=
    isProper_comp' B (Spec (.of A)) hA eX.hom π.hom X'.2 X.2
      (isProper_of_isIso B (Spec (.of A)) hA eX.hom) hπ0
  have hπf : IsFiniteType B (Spec (.of A)) hA (π' ≫ f).hom :=
    isFiniteType_comp' B (Spec (.of A)) hA π'.hom f.hom X.2 (schemeSpace (baseObject A B hA)).2
      hπp.2.1 hf
  have hX'' := isNoetherian_of_isFiniteType_baseObject (schemeSpace U') (π' ≫ f) hπf
    (isSeparated_comp B (Spec (.of A)) hA π'.hom f.hom hπp.1 hsep)
  let hN'' := fact_isLocallyNoetherian_of_baseObject (schemeSpace U') (π' ≫ f) hπf.1
  have hGc := isCoherentAdicSystem_modulePullback_of_representable B (Spec (.of A)) hA π' hπ
    (baseIdealSubmodule X.1 X.2 I)
    (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I) E.obj.property
  rw [inverseImageIdeal_baseIdealSheaf π' hπ I] at hGc
  let G : CoherentAdicSystems B (Spec (.of A)) hA (yoneda.obj U')
      (isAlgebraicSpace_yoneda B (Spec (.of A)) hA U')
      (baseIdealSubmodule (yoneda.obj U') (isAlgebraicSpace_yoneda B (Spec (.of A)) hA U') I) :=
    ⟨E.obj.obj ⋙ modulePullback B (Spec (.of A)) hA π', hGc⟩
  have hG0 := hasProperSupport_modulePullback_of_isProper π' hπp f hf.1 hπf.1 _
    (E.obj.property.1 0) E.property
  have : LocallyOfFiniteType (B.inclusion.map U'.hom) :=
    inferInstanceAs (LocallyOfFiniteType (V.ι ≫ p))
  have : IsLocallyNoetherian (B.inclusion.obj U'.left) :=
    LocallyOfFiniteType.isLocallyNoetherian (V.ι ≫ p)
  obtain ⟨F, hF, hFsupp, ⟨eG⟩⟩ := exists_adicQuotientSystem_iso_of_scheme_algebraization I U'
    (Stacks.Algebraization.C1573.exists_completion_iso_of_opens A I p V) (π' ≫ f) hπf.1 G hG0
  exact essImage_completionFunctorProperOver_of_pullback_algebraization I X f hf hsep Z
    (fun e _ =>
      exists_closedImmersion_idealPowerMultiple_isEquivalence_completion I X f hf hsub Z hZ e)
    E hX'' π' hπ hπp (isIso_fromPreimage_iso_comp eX.hom π.hom _ hbl) hπf.1 F hF hFsupp eG

/-- **The Chow reduction of Stacks 08BE.**  In Situation 08B7 with `X` nonempty, if completion is
essentially surjective on every closed subspace of `X` missing a point of `X`, then every
coherent `I`-adic system on `X` with support proper over `A` is in the essential image of the
completion functor. -/
theorem C1573.essImage_completionFunctorProperOver_of_essSurj_closedSubspaces [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A] (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsFiniteType B (Spec (.of A)) hA f.hom)
    (hsep : IsSeparated B (Spec (.of A)) hA f.hom)
    (hne : Nonempty (points B (Spec (.of A)) hA X.1))
    (hsub : ∀ (W : AlgebraicSpaces B (Spec (.of A)) hA) (i : W ⟶ X)
      (hi : IsClosedImmersion B (Spec (.of A)) hA i.hom),
      Set.range (pointsMap B (Spec (.of A)) hA W.1 i.hom) ≠ Set.univ →
      letI := fact_isLocallyNoetherian_of_baseObject W (i ≫ f)
        (isLocallyOfFiniteType_closedImmersion_comp i hi f hf.1)
      (completionFunctorProperOver B (Spec (.of A)) hA W.1 (schemeSpace (baseObject A B hA)).1
        W.2 (schemeSpace (baseObject A B hA)).2 (i ≫ f).hom
        (isLocallyOfFiniteType_closedImmersion_comp i hi f hf.1) (baseIdealSubmodule W.1 W.2 I)
        (isQuasicoherentOnSite_baseIdealSubmodule (X := W.1) (hX := W.2) I)).EssSurj)
    (E : CoherentAdicSystemsProperOver B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2
      f.hom hf.1 (baseIdealSubmodule X.1 X.2 I)) :
    letI := fact_isLocallyNoetherian_of_baseObject X f hf.1
    (completionFunctorProperOver B (Spec (.of A)) hA X.1 (schemeSpace (baseObject A B hA)).1 X.2
      (schemeSpace (baseObject A B hA)).2 f.hom hf.1 (baseIdealSubmodule X.1 X.2 I)
      (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).essImage E := by
  let := fact_isLocallyNoetherian_of_baseObject X f hf.1
  -- Chow's lemma
  have hbase := isProper_of_isIso B (Spec (.of A)) hA (𝟙 (schemeSpace (baseObject A B hA)).1)
  have hYsep : IsAbsolutelySeparated B (Spec (.of A)) hA B.contains_terminal
      (schemeSpace (baseObject A B hA)).1 :=
    isAbsolutelySeparated_of_isSeparated_to_affine B (Spec (.of A)) hA B.contains_terminal
      (baseObject A B hA) (inferInstanceAs (IsAffine (Spec (.of A)))) (𝟙 _) hbase.1
  have hYnoeth := isNoetherian_of_isFiniteType_baseObject (schemeSpace (baseObject A B hA))
    (𝟙 _) hbase.2.1 hbase.1
  obtain ⟨U, hU, n, X', π, i, hadm, himm, -⟩ :=
    exists_isAdmissibleBlowup_isImmersion_projectiveSpace B.contains_terminal f hsep hf hYsep
      hYnoeth
  have hπ0 := IsAdmissibleBlowup.isProper B (Spec (.of A)) hA hadm
  obtain ⟨Z, -, hdisj, hbl⟩ := hadm
  -- the immersion into projective space over the base
  have hT : IsIso (terminal.from (schemeSpace (baseObject A B hA)).1) :=
    isIso_of_isTerminal (isTerminal_yoneda_obj_base B (Spec (.of A)) hA) terminalIsTerminal _
  have hsnd : IsIso (pullback.snd (terminal.from (schemeSpace (baseObject A B hA)).1)
      (terminal.from (projectiveSpaceFunctor B (Spec (.of A)) hA n))) :=
    (IsPullback.of_hasPullback _ _).isIso_snd_of_isIso
  let i' := i ≫ pullback.snd _ _ ≫ (projectiveSpaceFunctorIso B (Spec (.of A)) hA n).hom
  have hi' : IsImmersion B (Spec (.of A)) hA i' :=
    (MorphismProperty.RespectsIso.postcomp _ _ _ himm)
  obtain ⟨Y', p, V, hV, hp, ⟨eX⟩⟩ := exists_yoneda_iso_opens_of_isImmersion_projectiveSpace n i' hi'
  have h0 := isIso_fromPreimage_openComplement hbl
  rw [openComplementOfClosedSubspace_val] at h0
  have hZ : Set.range (pointsMap B (Spec (.of A)) hA Z.1.toFunctor Z.1.ι) ≠ Set.univ := by
    obtain ⟨u⟩ := hU.nonempty
    exact fun h => Set.disjoint_left.1 hdisj ⟨u, rfl⟩ (h.symm ▸ Set.mem_univ _ :
      _ ∈ Set.range (pointsMap B (Spec (.of A)) hA Z.1.toFunctor Z.1.ι))
  exact essImage_completionFunctorProperOver_of_isProper_of_yoneda_iso_opens I X f hf hsep hsub Z
    hZ π hπ0 h0 p V hV eX E

end AlgebraicGeometry.Space

end
