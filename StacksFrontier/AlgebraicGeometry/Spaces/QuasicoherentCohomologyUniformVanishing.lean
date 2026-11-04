module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentUniverseDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyOverBaseUniverseLift
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageLeray
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageUniformBound
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperModuleCohomologyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport

/-!
# A uniform vanishing degree for the cohomology of quasi-coherent modules

Let `X` be a quasi-compact and quasi-separated algebraic space over `Spec A`. There is a single
degree `N` such that `Hᑫ(X, 𝓕) = 0` for every quasi-coherent `𝒪_X`-module `𝓕` and every
`q ≥ N`. This is the content of [Stacks, Tag 072C], which the base registers on
`AlgebraicGeometry.Space.SpacesEtale.exists_forall_isZero_sheafH_of_isQuasiCompactSpace_072C`
for the cohomology of the underlying abelian sheaves on the spaces-étale site; this file gives
the same vanishing for the cohomology of modules on the small étale site, the cohomology in which
direct images, the finiteness theorem of [Stacks, Tag 08AS] and the Euler characteristic of
[Stacks, Tag 0DN1] are stated. Nothing here is registered.

The degree comes from the higher direct images along the structure morphism `f : X ⟶ Spec A`:
by [Stacks, Tag 073G] there is `N` with `Rᑫ f_* 𝓕 = 0` for `q ≥ N` and all quasi-coherent `𝓕`;
over the affine base these higher direct images are quasi-coherent ([Stacks, Tag 0720]), hence
acyclic for sections over `Spec A`, so the Leray spectral sequence of `Γ(Spec A, f_* −)`
degenerates and `Hᑫ(X, 𝓕) = Γ(Spec A, Rᑫ f_* 𝓕)`.

## Main results

* `AlgebraicGeometry.Space.exists_forall_isZero_rightDerived_globalSections_of_qcqs`: the
  uniform vanishing for `𝒪_X`-modules with sections in the universe of the structure sheaf.
* `AlgebraicGeometry.Space.exists_forall_isZero_cohomologyOverBase_of_isCoherent_of_qcqs`: the
  uniform vanishing of `AlgebraicGeometry.Space.cohomologyOverBase` for coherent modules with
  sections in any universe containing the site.

## References

* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
* [Stacks Project, Tag 073G](https://stacks.math.columbia.edu/tag/073G)
* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

universe u w

namespace AlgebraicGeometry.Space

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

/-- Restriction of scalars preserves finite limits. -/
private instance preservesFiniteLimits_restrictScalars {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) : PreservesFiniteLimits (ModuleCat.restrictScalars.{u} f) :=
  ⟨fun _ _ _ ↦ ⟨fun {_} ↦ inferInstance⟩⟩

/-- Restriction of scalars preserves finite colimits. -/
private instance preservesFiniteColimits_restrictScalars {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) : PreservesFiniteColimits (ModuleCat.restrictScalars.{u} f) :=
  ⟨fun _ _ _ ↦ ⟨fun {_} ↦ inferInstance⟩⟩

/-- **A uniform vanishing degree for the cohomology of quasi-coherent modules**, with sections in
the universe of the structure sheaf: on a quasi-compact and quasi-separated algebraic space over
`Spec A` there is `N` with `Hᑫ(X, 𝓕) = 0` for all quasi-coherent `𝓕` and all `q ≥ N`. -/
theorem exists_forall_isZero_rightDerived_globalSections_of_qcqs
    (hqc : IsQuasiCompactSpace B (Spec (.of A)) hA X)
    (hqs : IsAbsolutelyQuasiSeparated B (Spec (.of A)) hA hZ X) :
    have := hasInjectiveResolutions_modules B (Spec (.of A)) hA X hX
    ∃ N : ℕ, ∀ F : Modules.{u, u} B (Spec (.of A)) hA X hX, F.IsQuasicoherentOnSite →
      ∀ q, N ≤ q → IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)).rightDerived q).obj F) := by
  intro
  let V := baseObject A B hA
  let Y : AlgebraicSpaces B (Spec (.of A)) hA :=
    ⟨yoneda.obj V, isAlgebraicSpace_yoneda B (Spec (.of A)) hA V⟩
  let X' : AlgebraicSpaces B (Spec (.of A)) hA := ⟨X, hX⟩
  let g : X' ⟶ Y := ObjectProperty.homMk ((isTerminal_yoneda_obj_base B (Spec (.of A)) hA).from X)
  have hV : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj V) := by
    change IsAffine (Spec (.of A))
    infer_instance
  have hgqc : IsQuasiCompact B (Spec (.of A)) hA g.hom :=
    isQuasiCompact_of_isQuasiCompactSpace B (Spec (.of A)) hA hZ Y.2
      (isAbsolutelyQuasiSeparated_yoneda_obj B (Spec (.of A)) hA hZ V
        (by change QuasiSeparatedSpace (Spec (.of A)); infer_instance)) hqc g.hom
  have hgqs : IsQuasiSeparated B (Spec (.of A)) hA g.hom :=
    isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B (Spec (.of A)) hA hZ hX hqs g.hom
  obtain ⟨N, hN⟩ := exists_forall_isZero_rightDerived_modulePushforward_of_qcqs B (Spec (.of A)) hA
    g hgqc hgqs (isQuasiCompactSpace_yoneda_of_isAffine B (Spec (.of A)) hA V hV)
  refine ⟨N, fun F hF q hq ↦ ?_⟩
  have := enoughInjectives_modules B (Spec (.of A)) hA X hX
  have := enoughInjectives_modules B (Spec (.of A)) hA Y.1 Y.2
  have := hasInjectiveResolutions_modules B (Spec (.of A)) hA Y.1 Y.2
  have := modulePushforward_additive B (Spec (.of A)) hA g
  let W := idEtaleChart B (Spec (.of A)) hA V
  let O :=
    Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA Y.1 Y.2).O
  have : (SheafOfModules.evaluation.{u} O (op W)).Additive := ⟨fun {_ _ _ _} ↦ rfl⟩
  have hR : IsZero (((modulePushforward B (Spec (.of A)) hA g).rightDerived q).obj F) :=
    hN Y X' (𝟙 Y) (𝟙 X') g IsPullback.of_id_fst F hF q hq
  have hQ : IsZero (((modulePushforward B (Spec (.of A)) hA g ⋙
      SheafOfModules.evaluation.{u} O (op W)).rightDerived q).obj F) := by
    refine IsZero.of_iso ((SheafOfModules.evaluation.{u} O (op W)).map_isZero hR)
      (evaluationRightDerivedIso B (Spec (.of A)) hA
        (isTerminalIdEtaleChart B (Spec (.of A)) hA V) g F (fun p n hn ↦ ?_) q)
    have : F.IsQuasicoherentOnSite := hF
    exact isZero_rightDerived_evaluation_of_isAffineChart B (Spec (.of A)) hA _ _ _
      (isQuasicoherentOnSite_rightDerived_modulePushforward' B (Spec (.of A)) hA g hgqc hgqs F p)
      W hV n hn
  have : (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X hX)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  let E := ModuleCat.restrictScalars.{u} (idEtaleChartBaseRingHom V) ⋙
    ModuleCat.uliftFunctor.{u + 1} A
  have : E.PreservesHomology := Functor.preservesHomologyOfExact _
  let Q := modulePushforward B (Spec (.of A)) hA g ⋙ SheafOfModules.evaluation.{u} O (op W)
  let Γ := globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
  have e₁ := (Functor.rightDerivedCompIso Γ
    (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X hX)) q).app F
  have e₂ := (Functor.rightDerivedIsoOfNatIso
    (F := Γ ⋙ ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X hX)) (G := Q ⋙ E)
    (globalSectionsOverBaseIso V g) q).app F
  have h₃ : IsZero (((Q ⋙ E).rightDerived q).obj F) :=
    (E.map_isZero hQ).of_iso ((Functor.rightDerivedCompIso Q E q).app F)
  have h₁ := (h₃.of_iso e₂).of_iso e₁.symm
  rwa [ModuleCat.isZero_iff_subsingleton] at h₁ ⊢

/-- **A uniform vanishing degree for the cohomology over the base of coherent modules**: on a
quasi-compact and quasi-separated algebraic space over `Spec A` there is `N` with
`Hᑫ(X, 𝓕) = 0` over `A` for every coherent `𝓕` with sections in a universe containing the site
and every `q ≥ N`. Every such `𝓕` is the universe lift of a coherent module with sections in the
universe of the structure sheaf
(`AlgebraicGeometry.Space.exists_iso_uliftForPresentation_of_isCoherent`), whose cohomology is
the universe lift of the cohomology at that universe
(`AlgebraicGeometry.Space.cohomologyOverBaseUliftForPresentationIso`). -/
theorem exists_forall_isZero_cohomologyOverBase_of_isCoherent_of_qcqs
    (hqc : IsQuasiCompactSpace B (Spec (.of A)) hA X)
    (hqs : IsAbsolutelyQuasiSeparated B (Spec (.of A)) hA hZ X) :
    ∃ N : ℕ, ∀ F : Modules.{u, max (u + 1) w} B (Spec (.of A)) hA X hX,
      IsCoherent B (Spec (.of A)) hA X hX F → ∀ q, N ≤ q →
        IsZero (cohomologyOverBase.{u, w} A B hA X hX F q) := by
  obtain ⟨N, hN⟩ := exists_forall_isZero_rightDerived_globalSections_of_qcqs A B hA hZ X hX hqc hqs
  refine ⟨N, fun F hF q hq ↦ ?_⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_iso_uliftForPresentation_of_isCoherent.{u, w} B (Spec (.of A)) hA
    X hX F
  refine IsZero.of_iso ?_ (cohomologyOverBaseIso.{u, w} A B hA X hX e q).symm
  exact (isZero_cohomologyOverBase_uliftForPresentation_iff_rightDerived.{u, w} A B hA X hX M q).2
    (hN M hM.toIsQuasicoherentOnSite q hq)

end AlgebraicGeometry.Space

end
