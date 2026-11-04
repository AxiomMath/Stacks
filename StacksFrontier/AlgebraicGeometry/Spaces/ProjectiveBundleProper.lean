module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjProper

/-!
# The projection of the projective bundle of an algebraic space is proper

Let `X` be an algebraic space over a scheme `S` and `ℰ` a finite locally free `𝒪_X`-module.
The projection `π : 𝐏(ℰ) ⟶ X` of `AlgebraicGeometry.Space.projectiveBundle` is proper.

Over the presenting chart `U` of `X` the base change of `π` is the projection of the projective
bundle `𝐏(ℰ|_U)` of the chart restriction, which is the relative `Proj` of the symmetric algebra
of `ℰ|_U`; this is a chart presentation of `π` in the sense of
`AlgebraicGeometry.Space.RelativeProjChart`.  The symmetric algebra of a quasi-coherent module of
finite type satisfies the two hypotheses of the properness clause of Stacks 084I: its degree-zero
part is the structure sheaf, and over an affine open its graded ring of sections is generated
over the degree-zero part by finitely many sections of degree one.

## Main definitions

* `AlgebraicGeometry.Space.projectiveBundleRelativeProjChart`: the chart presentation of `π` at
  the presenting chart.

## Main results

* `Stacks.RelativeProj.isDegreeZeroFiniteType_symmetricSituationOfQuasicoherent` and
  `Stacks.RelativeProj.isFiniteTypeOverDegreeZero_symmetricSituationOfQuasicoherent`: the two
  finiteness conditions for the symmetric algebra of a quasi-coherent module of finite type.
* `AlgebraicGeometry.Space.isProper_projectiveBundleProj`: **`π` is proper.**

## References

* [Stacks Project, Tag 084I](https://stacks.math.columbia.edu/tag/084I)
* [Stacks Project, Tag 0ERT](https://stacks.math.columbia.edu/tag/0ERT)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.RelativeProj

variable (X : Scheme.{u}) (E : X.Modules) [E.IsQuasicoherent]

/-- **The degree-zero part of the symmetric algebra is of finite type over the structure
sheaf**: on the sections over an open it is the ring of functions itself. -/
theorem isDegreeZeroFiniteType_symmetricSituationOfQuasicoherent :
    (symmetricSituationOfQuasicoherent X E).IsDegreeZeroFiniteType := fun U _ => by
  have := isIso_sectionRingZeroMap_symmetricSituationOfQuasicoherent X E U
  exact RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso
      (Situation.sectionRingZeroMap (symmetricSituationOfQuasicoherent X E) U)).2

/-- **The symmetric algebra of a quasi-coherent module of finite type is of finite type over its
degree-zero part** on every affine open: it is generated there by the finitely many degree-one
sections spanning the module. -/
theorem isFiniteTypeOverDegreeZero_symmetricSituationOfQuasicoherent [E.IsFiniteType] :
    (symmetricSituationOfQuasicoherent X E).IsFiniteTypeOverDegreeZero := fun U hU => by
  obtain ⟨g, hg⟩ := exists_finset_span_sectionPieces_one X E U
    (AlgebraicGeometry.SheafOfModules.exists_finset_span_of_isFiniteType E U hU)
  exact (symmetricSituationOfQuasicoherent X E).finiteType_sectionRing_of_adjoin_eq_top U
    (adjoin_sectionRingGrading_one_eq_top_symmetricSituationOfQuasicoherent X E U hU) g hg

end Stacks.RelativeProj

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

/-- **The chart presentation of the projection of the projective bundle**, at the presenting
chart `U` of `X`: the base change of `π` along `U ⟶ X` is the relative `Proj` of the symmetric
algebra of `ℰ|_U`. -/
def projectiveBundleRelativeProjChart :
    RelativeProjChart B S hS (projectiveBundleProj E hfree).hom
      (Stacks.RelativeProj.symmetricSituationOfQuasicoherent
        (chartScheme (presentationChart (projectiveBundlePresentation X)))
        (chartBundleModule E (presentationChart (projectiveBundlePresentation X)))) where
  chart := (SmallEtale.toOver B S hS X.1).obj (presentationChart (projectiveBundlePresentation X))
  chartHom := (presentationChart (projectiveBundlePresentation X)).obj.hom
  chartHom_etale := (presentationChart (projectiveBundlePresentation X)).property
  chartHom_surjective := surjective_projectiveBundlePresentation X
  baseIso := Iso.refl _
  proj := (projectiveBundleChartFamily E hfree).site
    (presentationChart (projectiveBundlePresentation X))
  projHom := (projectiveBundleChartFamily E hfree).siteToChart
    (presentationChart (projectiveBundlePresentation X))
  projIso := Iso.refl _
  projHom_comp := (Category.comp_id _).trans (Category.id_comp _).symm
  projToSpace := projectiveBundleChart E hfree
  isPullback := isPullback_projectiveBundleProj E hfree

/-- **The projection `π : 𝐏(ℰ) ⟶ X` of the projective bundle of a finite locally free module is
proper.** -/
theorem isProper_projectiveBundleProj :
    IsProper B S hS (projectiveBundleProj E hfree).hom := by
  have := isFiniteLocallyFree_chartBundleModule E hfree
    (presentationChart (projectiveBundlePresentation X))
  have : (chartBundleModule E (presentationChart (projectiveBundlePresentation X))).IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isFiniteType_of_isFiniteLocallyFree _
  exact isProper_relativeProj B S hS (projectiveBundle E hfree).2 X.2 _
    (projectiveBundleRelativeProjChart E hfree)
    (Stacks.RelativeProj.isDegreeZeroFiniteType_symmetricSituationOfQuasicoherent _ _)
    (Stacks.RelativeProj.isFiniteTypeOverDegreeZero_symmetricSituationOfQuasicoherent _ _)

end AlgebraicGeometry.Space

end
