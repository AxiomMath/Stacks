module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorLimitPreservingCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardAffineGeometry
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactQuasiSeparatedOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Stacks 082Q reduced to an affine source over an affine base

Stacks 082Q, in its corrected form, asserts that for `f : X ⟶ Y` of finite presentation (locally
of finite presentation, quasi-compact and quasi-separated) and `F` of finite presentation, the
functor `Q^{fp}_{F/X/Y}` is limit preserving.  It is reduced here to the case of an affine source
over an affine base, in two steps.

* **Change of base to a stage** ("we may set `B = S = T_{i₀}` and replace `X` by `X_{T₀}`",
  Remark 08IT): `QuotientSituation.limitPreserving_finitePresentationQuotientsFunctor_of_stages`.
* **Two affine charts** (Stacks 03H6 and 08IV).  Over an affine base the source of a
  quasi-compact and quasi-separated morphism is quasi-compact and quasi-separated; choose an
  affine scheme `U` surjective and étale over `X` and an affine scheme `V` surjective and étale
  over `U ×_X U`.  Then `Q^{fp}_{F/X/Y}` is the equalizer of the two restrictions between the
  functors of finitely presented quotients of `U` and of `V`
  (`QuotientSituation.limitPreserving_finitePresentationQuotientsFunctor_of_charts`), both of
  which are functors of quotients of a situation whose source and base are affine schemes, whose
  morphism is locally of finite presentation and whose module is of finite presentation:
  `QuotientSituation.limitPreserving_finitePresentationQuotientsFunctor_of_affineBase`.

## Main results

* `QuotientSituation.limitPreserving_finitePresentationQuotientsFunctor_of_affineBase`:
  the chart step over an affine base.
* `QuotientSituation.limitPreserving_finitePresentationQuotientsFunctor_of_affineCase`:
  `Q^{fp}_{F/X/Y}` is limit preserving for `f` and `F` of finite presentation, given the case of
  an affine source over an affine base.

## References

* [Stacks Project, Tag 082Q](https://stacks.math.columbia.edu/tag/082Q)
* [Stacks Project, Tag 08IT](https://stacks.math.columbia.edu/tag/08IT)
* [Stacks Project, Tag 08IV](https://stacks.math.columbia.edu/tag/08IV)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotientSituation

/-! ### The chart step over an affine base -/

/-- A quasi-compact algebraic space has an affine scheme `U` with a surjective étale morphism
`a : U ⟶ X` which is locally of finite presentation. -/
private theorem exists_affine_etale_surjective_lfp_of_isQuasiCompactSpace
    (X : AlgebraicSpaces B S hS) (hX : IsQuasiCompactSpace B S hS X.1) :
    ∃ (U : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
      (a : (schemeSpaceFunctor B S hS).obj U ⟶ X), IsEtale B S hS a.hom ∧
        IsSurjective B S hS a.hom ∧ IsLocallyOfFinitePresentation B S hS a.hom := by
  obtain ⟨U, p, hU, hpsurj, hpet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hX
  exact ⟨U, hU, ObjectProperty.homMk p, hpet,
    (surjective_iff_surjective_pointsMap B S hS X.1 X.2 U p).1 hpsurj,
    isLocallyOfFinitePresentation_of_isEtale B S hS hpet⟩

/-- Let `f : X ⟶ T₀` be a morphism of finite presentation to the algebraic space of an affine
scheme `T₀` of the site, and let `F` be a quasi-coherent module of finite presentation.  Then
`Q^{fp}_{F/X/T₀}` is limit preserving as soon as the functor of finitely presented quotients of
every situation whose source is an affine scheme `U` over `T₀`, locally of finite presentation
over it, and whose module is of finite presentation is. -/
theorem limitPreserving_finitePresentationQuotientsFunctor_of_affineBase
    {T₀ : BigFppfOver B S hS} (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
    (X : AlgebraicSpaces B S hS) (f : X ⟶ (schemeSpaceFunctor B S hS).obj T₀)
    (F : Modules.{u, u} B S hS X.1 X.2) (hFq : F.IsQuasicoherentOnSite)
    (hF : F.IsFinitePresentationOnSite) (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (hqc : IsQuasiCompact B S hS f.hom) (hqs : IsQuasiSeparated B S hS f.hom)
    (haff : ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      ∀ (fU : (schemeSpaceFunctor B S hS).obj U ⟶ (schemeSpaceFunctor B S hS).obj T₀),
        IsLocallyOfFinitePresentation B S hS fU.hom →
      ∀ (F' : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj U).1
          ((schemeSpaceFunctor B S hS).obj U).2)
        (hF'q : F'.IsQuasicoherentOnSite), F'.IsFinitePresentationOnSite →
        LimitPreserving.{u, u + 1, u, u} (QuotientSituation.mk _ _ fU F' hF'q).testScheme
          (QuotientSituation.mk _ _ fU F' hF'q).finitePresentationQuotientsFunctor) :
    LimitPreserving.{u, u + 1, u, u} (QuotientSituation.mk X _ f F hFq).testScheme
      (QuotientSituation.mk X _ f F hFq).finitePresentationQuotientsFunctor := by
  set D : QuotientSituation B S hS := QuotientSituation.mk X _ f F hFq with hD
  have hT₀sp : IsAffineSpace B S hS (yoneda.obj T₀) := ⟨T₀, hT₀, ⟨Iso.refl _⟩⟩
  have hlfpBC := isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  have hXqc : IsQuasiCompactSpace B S hS X.1 :=
    isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS f.hom hT₀sp hqc
  obtain ⟨U, hU, a, hpet, ha', halfp⟩ :=
    exists_affine_etale_surjective_lfp_of_isQuasiCompactSpace X hXqc
  have hUqc : IsQuasiCompactSpace B S hS (yoneda.obj U) :=
    isQuasiCompactSpace_yoneda_of_isAffine B S hS U hU
  have hpf : IsQuasiCompact B S hS (a.hom ≫ f.hom) :=
    isQuasiCompact_yoneda_of_isAffine B S hS (a.hom ≫ f.hom) hU hT₀
  have hRqc : IsQuasiCompactSpace B S hS (pullback a.hom a.hom) :=
    isQuasiCompactSpace_selfPullback B S hS a.hom f.hom (isAlgebraicSpace_yoneda B S hS U)
      (isAlgebraicSpace_yoneda B S hS T₀) hUqc hqs hpf
  let R := AlgebraicSpaces.fiberProduct B S hS a a
  obtain ⟨V, hV, b, hqet, hb', hblfp⟩ :=
    exists_affine_etale_surjective_lfp_of_isQuasiCompactSpace R hRqc
  have hfstlfp : IsLocallyOfFinitePresentation B S hS (fiberFst a a).hom :=
    hlfpBC.of_isPullback (AlgebraicSpaces.isPullback_fiberProduct B S hS a a).flip halfp
  have hUlfp : IsLocallyOfFinitePresentation B S hS (a ≫ f).hom :=
    isLocallyOfFinitePresentation_comp B S hS (isAlgebraicSpace_yoneda B S hS U) X.2
      (isAlgebraicSpace_yoneda B S hS T₀) a.hom f.hom halfp hlfp
  have hbfst : IsLocallyOfFinitePresentation B S hS (b ≫ fiberFst a a).hom :=
    isLocallyOfFinitePresentation_comp B S hS (isAlgebraicSpace_yoneda B S hS V) R.2
      (isAlgebraicSpace_yoneda B S hS U) b.hom (fiberFst a a).hom hblfp hfstlfp
  have hVa : IsLocallyOfFinitePresentation B S hS ((b ≫ fiberFst a a) ≫ a).hom :=
    isLocallyOfFinitePresentation_comp B S hS (isAlgebraicSpace_yoneda B S hS V)
      (isAlgebraicSpace_yoneda B S hS U) X.2 _ a.hom hbfst halfp
  have hVlfp : IsLocallyOfFinitePresentation B S hS (((b ≫ fiberFst a a) ≫ a) ≫ f).hom :=
    isLocallyOfFinitePresentation_comp B S hS (isAlgebraicSpace_yoneda B S hS V) X.2
      (isAlgebraicSpace_yoneda B S hS T₀) _ f.hom hVa hlfp
  exact D.limitPreserving_finitePresentationQuotientsFunctor_of_charts a b hpet ha' hqet hb'
    (haff U hU (a ≫ f) hUlfp _ _ (isFinitePresentationOnSite_modulePullback B S hS a F hF))
    (haff V hV (((b ≫ fiberFst a a) ≫ a) ≫ f) hVlfp _ _
      (isFinitePresentationOnSite_modulePullback B S hS _ F hF))

/-! ### Reduction to the affine case -/

/-- In Situation 082M, if `F` is of finite presentation and `f` is of finite presentation
(locally of finite presentation, quasi-compact and quasi-separated), the functor `Q^{fp}_{F/X/Y}`
is limit preserving as soon as the functor of finitely presented quotients of every situation
whose source and base are affine schemes of the site, whose morphism is locally of finite
presentation and whose module is of finite presentation is. -/
theorem limitPreserving_finitePresentationQuotientsFunctor_of_affineCase
    (D : QuotientSituation B S hS) (hF : D.F.IsFinitePresentationOnSite)
    (hfp : IsFinitePresentation B S hS D.f.hom)
    (haff : ∀ (U T₀ : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj T₀) →
      ∀ (fU : (schemeSpaceFunctor B S hS).obj U ⟶ (schemeSpaceFunctor B S hS).obj T₀),
        IsLocallyOfFinitePresentation B S hS fU.hom →
      ∀ (F' : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj U).1
          ((schemeSpaceFunctor B S hS).obj U).2)
        (hF'q : F'.IsQuasicoherentOnSite), F'.IsFinitePresentationOnSite →
        LimitPreserving.{u, u + 1, u, u} (QuotientSituation.mk _ _ fU F' hF'q).testScheme
          (QuotientSituation.mk _ _ fU F' hF'q).finitePresentationQuotientsFunctor) :
    LimitPreserving.{u, u + 1, u, u} D.testScheme D.finitePresentationQuotientsFunctor :=
  D.limitPreserving_finitePresentationQuotientsFunctor_of_stages fun T₀ hT₀ ↦
    limitPreserving_finitePresentationQuotientsFunctor_of_affineBase hT₀
      (D.baseChangedSource T₀.hom) (D.baseChangedMorphism T₀.hom) _ _
      (isFinitePresentationOnSite_modulePullback B S hS _ D.F hF)
      ((isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
        (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T₀.hom) hfp.1)
      (isQuasiCompact_pullback_snd_of_isQuasiCompact B S hS hfp.2.1 T₀.left T₀.hom.hom)
      (isQuasiSeparated_pullback_snd B S hS D.f.hom T₀.hom.hom hfp.2.2)
      (fun U hU ↦ haff U T₀.left hU hT₀)

end QuotientSituation

end AlgebraicGeometry.Space

end
