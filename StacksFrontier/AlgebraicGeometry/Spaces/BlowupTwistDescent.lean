module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCongr
public import StacksFrontier.AlgebraicGeometry.ConormalSourceTransport.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealChartPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# Descending `𝒪(1)` from the étale chart of the blowup of an algebraic space

Let `b : X' ⟶ X` be the blowing up of an algebraic space along a closed subspace `Z` (Stacks
085Q), with exceptional divisor `E = b⁻¹(Z)`, presented by the étale equivalence relation
`P_R ⇉ P_U` of the relative `Proj` of the Rees algebra on an étale chart `U` of `X`.  Part (3) of
Stacks 085T says `𝒪_{X'}(-1) ≅ 𝒪_{X'}(E)`; its proof descends the scheme case, Stacks 02OS (3),
from `P_U` to `X'`.  This file carries out the descent of the modules: it forms the quasi-coherent
module `(𝒪_{P_U}(1)^a, α')` on the groupoid of the presentation and applies the inverse of the
equivalence of Stacks 03M3 (`AlgebraicGeometry.Space.equivalenceQuasicoherentFromSpaceBase`).

## Main definitions

* `AlgebraicGeometry.Space.blowUpChartTwistOne`: the twisting sheaf `𝒪_{P_U}(1)` on the scheme
  of `P_U`, the twisting sheaf `AlgebraicGeometry.blowUpTwist` of the blowup of `U` in `ℐ|_U`
  read on `P_U` through the comparison `Stacks.Blowup.reesSituationBlowUpIso` of the two Rees
  constructions of this repository.
* `AlgebraicGeometry.Space.blowUpChartTwistOneIsoIdealSheaf`: **Stacks 02OS (3) on `P_U`**, as an
  isomorphism of `𝒪_{P_U}(1)` with the ideal sheaf of the closed immersion `E ×_{X'} P_U ⟶ P_U`.
* `AlgebraicGeometry.Space.blowUpChartTwistOneAssociatedIso`: the module associated with
  `𝒪_{P_U}(1)` is the pullback of `𝓘_E` along the atlas `P_U ⟶ X'`; this composes the previous
  isomorphism with `AlgebraicGeometry.Space.modulePullbackBlowUpAtlasExceptionalIdealIso`.
* `AlgebraicGeometry.Space.transportedQuasicoherentModule`: a quasi-coherent module on a groupoid
  in algebraic spaces, carried along an isomorphism of its underlying module.
* `AlgebraicGeometry.Space.blowUpTwistDescentDatum`: the quasi-coherent module
  `(𝒪_{P_U}(1)^a, α')` on the groupoid of the presentation of `X'`.
* `AlgebraicGeometry.Space.blowUpTwistOne`: the descended quasi-coherent `𝒪_{X'}`-module
  `𝒪_{X'}(1)`, and `AlgebraicGeometry.Space.blowUpTwistSpace` its integer tensor powers
  `𝒪_{X'}(n)` (Stacks 01CU).
* `AlgebraicGeometry.Space.blowUpTwistOneIso` and
  `AlgebraicGeometry.Space.blowUpTwistSpaceNegOneIso`: `𝒪_{X'}(1) ≅ 𝓘_E`, and
  `𝒪_{X'}(-1) ≅ 𝒪_{X'}(E)` with `𝒪_{X'}(E)` the invertible sheaf
  `AlgebraicGeometry.Space.associatedInvertibleSheaf` of the effective Cartier divisor `E`
  (part (2) of Stacks 085T).

## The descent datum and its canonicity

The transition morphism `α'` of `AlgebraicGeometry.Space.blowUpTwistDescentDatum` is the canonical
transition morphism of the pullback of `𝓘_E` along the atlas
(`AlgebraicGeometry.Space.quasicoherentFromSpaceBase`), conjugated by the chart identification
`AlgebraicGeometry.Space.blowUpChartTwistOneAssociatedIso`.  The cocycle and unit conditions are
therefore inherited, and full faithfulness of Stacks 03M3 gives `𝒪_{X'}(1) ≅ 𝓘_E` at once.  That
`α'` does not depend on `E` — it is the unique transition compatible with the canonical map
`𝒪_{P_U}(1) ⟶ 𝒪_{P_U}` and the canonical descent datum of `𝒪_{X'}` — is
`AlgebraicGeometry.Space.eq_blowUpTwistDescentDatum_alpha_iff`, in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupTwistDescentCanonical.lean`, where part (3) of
Stacks 085T is registered; no `stacks` attribute is attached to anything here.

## References

* [Stacks Project, Tag 085T](https://stacks.math.columbia.edu/tag/085T)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0841](https://stacks.math.columbia.edu/tag/0841)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- A closed immersion `f : E ⟶ T` is isomorphic, over an isomorphism `β : T ≅ T'`, to the closed
subscheme of `T'` cut out by the inverse image along `β⁻¹` of the kernel of `f`. -/
def closedImmersionIsoComapSubscheme {E T T' : Scheme.{u}} (f : E ⟶ T) [IsClosedImmersion f]
    (β : T ≅ T') : E ≅ (f.ker.comap β.inv).subscheme :=
  haveI : IsIso (pullback.snd β.inv f.ker.subschemeι) :=
    (IsPullback.of_hasPullback β.inv f.ker.subschemeι).isIso_snd_of_isIso
  asIso f.toImage ≪≫ (asIso (pullback.snd β.inv f.ker.subschemeι)).symm ≪≫
    (f.ker.comapIso β.inv).symm

/-- The isomorphism `AlgebraicGeometry.closedImmersionIsoComapSubscheme` lies over `β`. -/
theorem closedImmersionIsoComapSubscheme_hom_comp {E T T' : Scheme.{u}} (f : E ⟶ T)
    [IsClosedImmersion f] (β : T ≅ T') :
    (closedImmersionIsoComapSubscheme f β).hom ≫ (f.ker.comap β.inv).subschemeι = f ≫ β.hom := by
  have : IsIso (pullback.snd β.inv f.ker.subschemeι) :=
    (IsPullback.of_hasPullback β.inv f.ker.subschemeι).isIso_snd_of_isIso
  have h1 : inv (pullback.snd β.inv f.ker.subschemeι) ≫ pullback.fst β.inv f.ker.subschemeι =
      f.ker.subschemeι ≫ β.hom := by
    rw [IsIso.inv_comp_eq]
    calc pullback.fst β.inv f.ker.subschemeι
        = pullback.fst β.inv f.ker.subschemeι ≫ β.inv ≫ β.hom := by simp
      _ = pullback.snd β.inv f.ker.subschemeι ≫ f.ker.subschemeι ≫ β.hom := by
        rw [← Category.assoc, pullback.condition, Category.assoc]
  simp only [closedImmersionIsoComapSubscheme, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    asIso_inv, Category.assoc, Scheme.IdealSheafData.comapIso_inv_subschemeι]
  rw [h1, ← Category.assoc, Scheme.Hom.toImage_imageι]

/-- A square `f ≫ β = ε ≫ ι_J` onto the closed subscheme of a sheaf of ideals `J` gives one onto
the closed subscheme of any `J'` equal to `J`, through the identification of the two
subschemes. -/
theorem comp_eq_trans_eqToIso_subschemeι {E T T' : Scheme.{u}} {J J' : T'.IdealSheafData}
    (h : J = J') (f : E ⟶ T) (β : T ≅ T') (ε : E ≅ J.subscheme)
    (hsq : f ≫ β.hom = ε.hom ≫ J.subschemeι) :
    f ≫ β.hom = (ε ≪≫ eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫
      J'.subschemeι := by
  subst h
  simpa using hsq

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

section Transport

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : AlgebraicSpaces B S hS} {G : GroupoidInAlgebraicSpaces B S hS A}

/-- **A quasi-coherent module on a groupoid, carried along an isomorphism of its underlying
module.**  The transition morphism is conjugated by the isomorphism; cocycle and unit conditions
follow from those of `Y`, through `AlgebraicGeometry.Space.restrictedQuasicoherentModule`. -/
def transportedQuasicoherentModule (Y : QuasicoherentModule B S hS G)
    (E : QuasicoherentSheaves.{u, u} B S hS G.objects.obj G.objects.property)
    (e : E.obj ≅ Y.F.obj) : QuasicoherentModule B S hS G :=
  restrictedQuasicoherentModule Y E e.hom
    ((modulePullback B S hS G.target).map e.hom ≫ Y.alpha ≫
      (modulePullback B S hS G.source).map e.inv)
    (by simp only [Category.assoc, Iso.map_inv_hom_id, Category.comp_id])
    (@IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom ((modulePullback B S hS _).mapIso e)))
    (@IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom ((modulePullback B S hS _).mapIso e)))

/-- The transported module is isomorphic to the module it was transported from. -/
def transportedQuasicoherentModuleIso (Y : QuasicoherentModule B S hS G)
    (E : QuasicoherentSheaves.{u, u} B S hS G.objects.obj G.objects.property)
    (e : E.obj ≅ Y.F.obj) : transportedQuasicoherentModule Y E e ≅ Y where
  hom := ⟨e.hom, by
    change ((modulePullback B S hS G.target).map e.hom ≫ Y.alpha ≫
      (modulePullback B S hS G.source).map e.inv) ≫ (modulePullback B S hS G.source).map e.hom =
        _
    simp only [Category.assoc, Iso.map_inv_hom_id, Category.comp_id]
    rfl⟩
  inv := ⟨e.inv, by
    change _ = (modulePullback B S hS G.target).map e.inv ≫
      ((modulePullback B S hS G.target).map e.hom ≫ Y.alpha ≫
        (modulePullback B S hS G.source).map e.inv)
    simp only [Iso.map_inv_hom_id_assoc]
    rfl⟩
  hom_inv_id := QuasicoherentModule.Hom.ext e.hom_inv_id
  inv_hom_id := QuasicoherentModule.Hom.ext e.inv_hom_id

end Transport

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  (Z : ClosedSubspaces B S hS X.obj) (P : Presentation B S hS X.obj X.property)
  (hcU : B.Contains (reesChartSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
  (hcR : B.Contains (reesRelationSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
  (heq : CategoryTheory.IsEquivalenceRelation
      ((Over.post B.inclusion).map (reesProjTarget (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR))
      ((Over.post B.inclusion).map (reesProjSource (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR)))

/-- **The twisting sheaf `𝒪_{P_U}(1)` on the étale chart of the blowup.**  The chart `P_U` is the
relative `Proj` of the Rees algebra `Stacks.Blowup.reesSituation (ℐ|_U)`, and this is the twisting
sheaf `𝒪(1)` of the blowup `AlgebraicGeometry.blowUp (ℐ|_U)` read on `P_U` through the comparison
isomorphism `Stacks.Blowup.reesSituationBlowUpIso` of the two Rees constructions. -/
abbrev blowUpChartTwistOne :
    ((BigFppfOver.toScheme B S hS).obj (reesGlueingData (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR heq).projChart).Modules :=
  (RingedSpaceModuleAdjunction.modulePullback (Stacks.Blowup.reesSituationBlowUpIso
      (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
        P)).hom.toLRSHom.toShHom).obj
    (AlgebraicGeometry.blowUpTwist
      (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P) 1)

/-- The base change `E ×_{X'} P_U ⟶ P_U` of the exceptional divisor to the chart is a closed
immersion. -/
theorem isClosedImmersion_exceptionalDivisor_snd_chart :
    AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      ((exceptionalDivisor Z P hcU hcR heq).2.2.rep.snd
        (reesGlueingData (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
          P hcU hcR heq).chart)) :=
  (exceptionalDivisor Z P hcU hcR heq).2.2.property_snd _

/-- **Stacks 02OS (3) on the chart, against the ideal sheaf of the base change.**  The twisting
sheaf `𝒪_{P_U}(1)` is the ideal sheaf of the closed immersion `E ×_{X'} P_U ⟶ P_U`.  The base
change of `E` is, over the comparison `β = Stacks.Blowup.reesSituationBlowUpIso` of the two Rees
constructions, the exceptional divisor of `AlgebraicGeometry.blowUp (ℐ|_U)`
(`AlgebraicGeometry.Space.comap_ker_rep_snd_chart_exceptionalDivisor`), so
`Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoPullbackOfSquare` identifies its
ideal sheaf with `β^*` of the exceptional ideal sheaf, and this is `β^*` of the isomorphism
`AlgebraicGeometry.twistOneIsoExceptionalIdealModule` of Stacks 02OS (3) followed by that
identification (compare `AlgebraicGeometry.Space.chartTwistOneIsoExceptionalDivisorIdealSheaf`). -/
def blowUpChartTwistOneIsoIdealSheaf :
    blowUpChartTwistOne Z P hcU hcR heq ≅
      Stacks.ClosedImmersion.idealSheaf ((BigFppfOver.toScheme B S hS).map
          ((exceptionalDivisor Z P hcU hcR heq).2.2.rep.snd
            (reesGlueingData (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
              P hcU hcR heq).chart)).toLRSHom.toShHom :=
  (RingedSpaceModuleAdjunction.modulePullback
      (Stacks.Blowup.reesSituationBlowUpIso (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P)).hom.toLRSHom.toShHom).mapIso
      (AlgebraicGeometry.twistOneIsoExceptionalIdealModule (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P)) ≪≫
    (Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoPullbackOfSquare ((BigFppfOver.toScheme B S hS).map
          ((exceptionalDivisor Z P hcU hcR heq).2.2.rep.snd
            (reesGlueingData (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
              P hcU hcR heq).chart))
      (@closedImmersionIsoComapSubscheme _ _ _ ((BigFppfOver.toScheme B S hS).map
          ((exceptionalDivisor Z P hcU hcR heq).2.2.rep.snd
            (reesGlueingData (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
              P hcU hcR heq).chart))
          (isClosedImmersion_exceptionalDivisor_snd_chart Z P hcU hcR heq)
          (Stacks.Blowup.reesSituationBlowUpIso (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P)) ≪≫
        eqToIso (congrArg Scheme.IdealSheafData.subscheme
          (comap_ker_rep_snd_chart_exceptionalDivisor Z P hcU hcR heq)))
      (AlgebraicGeometry.exceptionalIdeal (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P)).subschemeι
      (Stacks.Blowup.reesSituationBlowUpIso (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P))
      (comp_eq_trans_eqToIso_subschemeι
        (comap_ker_rep_snd_chart_exceptionalDivisor Z P hcU hcR heq) _ _ _
        (@closedImmersionIsoComapSubscheme_hom_comp _ _ _ ((BigFppfOver.toScheme B S hS).map
          ((exceptionalDivisor Z P hcU hcR heq).2.2.rep.snd
            (reesGlueingData (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
              P hcU hcR heq).chart))
          (isClosedImmersion_exceptionalDivisor_snd_chart Z P hcU hcR heq)
          (Stacks.Blowup.reesSituationBlowUpIso (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P))).symm)).symm


/-- The presentation of the blowup `X'` by `P_R ⇉ P_U`. -/
abbrev blowUpPresentation :
    Presentation B S hS (blowUpAlong Z P hcU hcR heq).obj (blowUpAlong Z P hcU hcR heq).property :=
  (reesGlueingData (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
    P hcU hcR heq).presentationRelativeProj

/-- **The module associated with `𝒪_{P_U}(1)` is the pullback of `𝓘_E` along the atlas.**
`AlgebraicGeometry.Space.blowUpChartTwistOneIsoIdealSheaf` followed by
`AlgebraicGeometry.Space.modulePullbackBlowUpAtlasExceptionalIdealIso`. -/
def blowUpChartTwistOneAssociatedIso :
    (presentationObjectsFunctor (blowUpPresentation Z P hcU hcR heq)).obj
        (blowUpChartTwistOne Z P hcU hcR heq) ≅
      (modulePullback B S hS (presentationAtlas (blowUpPresentation Z P hcU hcR heq))).obj
        (definingIdealSheaf B S hS (blowUpAlong Z P hcU hcR heq)
          (exceptionalDivisor Z P hcU hcR heq)).toSheafOfModules :=
  (presentationObjectsFunctor _).mapIso (blowUpChartTwistOneIsoIdealSheaf Z P hcU hcR heq) ≪≫
    (modulePullbackBlowUpAtlasExceptionalIdealIso Z P hcU hcR heq).symm

/-- The module associated with `𝒪_{P_U}(1)` is quasi-coherent on the small étale site of `P_U`. -/
theorem isQuasicoherentOnSite_blowUpChartTwistOneAssociated :
    ((presentationObjectsFunctor (blowUpPresentation Z P hcU hcR heq)).obj
        (blowUpChartTwistOne Z P hcU hcR heq)).IsQuasicoherentOnSite :=
  (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso
    (blowUpChartTwistOneAssociatedIso Z P hcU hcR heq).symm
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _
      (isQuasicoherentOnSite_definingIdealSheaf B S hS _ _))

/-- The ideal sheaf `𝓘_E` of the exceptional divisor, as a quasi-coherent `𝒪_{X'}`-module. -/
abbrev exceptionalIdealQcoh :
    QuasicoherentSheaves.{u, u} B S hS (blowUpAlong Z P hcU hcR heq).obj
      (blowUpAlong Z P hcU hcR heq).property :=
  ⟨(definingIdealSheaf B S hS (blowUpAlong Z P hcU hcR heq)
      (exceptionalDivisor Z P hcU hcR heq)).toSheafOfModules,
    isQuasicoherentOnSite_definingIdealSheaf B S hS _ _⟩

/-- The module associated with `𝒪_{P_U}(1)`, as a quasi-coherent module on the small étale site
of `P_U`. -/
abbrev blowUpChartTwistOneQcoh :
    QuasicoherentSheaves.{u, u} B S hS
      (presentationGroupoid (blowUpPresentation Z P hcU hcR heq)).objects.obj
      (presentationGroupoid (blowUpPresentation Z P hcU hcR heq)).objects.property :=
  ⟨(presentationObjectsFunctor (blowUpPresentation Z P hcU hcR heq)).obj
      (blowUpChartTwistOne Z P hcU hcR heq),
    isQuasicoherentOnSite_blowUpChartTwistOneAssociated Z P hcU hcR heq⟩

/-- **The quasi-coherent module `(𝒪_{P_U}(1)^a, α')` on the groupoid of the presentation of the
blowup.**  Its underlying module is the module associated with `𝒪_{P_U}(1)`, and its transition
morphism `α'` is the canonical transition morphism of the pullback of `𝓘_E` conjugated by
`AlgebraicGeometry.Space.blowUpChartTwistOneAssociatedIso`. -/
def blowUpTwistDescentDatum :
    QuasicoherentModule B S hS (presentationGroupoid (blowUpPresentation Z P hcU hcR heq)) :=
  transportedQuasicoherentModule
    ((quasicoherentFromSpaceBase B S hS _ _
      (presentationAtlas_comm (blowUpPresentation Z P hcU hcR heq))).obj
      (exceptionalIdealQcoh Z P hcU hcR heq))
    (blowUpChartTwistOneQcoh Z P hcU hcR heq)
    (blowUpChartTwistOneAssociatedIso Z P hcU hcR heq)

/-- The equivalence of Stacks 03M3 for the presentation of the blowup by `P_R ⇉ P_U`. -/
abbrev blowUpQcohEquivalence :
    QuasicoherentSheaves.{u, u} B S hS (blowUpAlong Z P hcU hcR heq).obj
        (blowUpAlong Z P hcU hcR heq).property ≌
      QuasicoherentModule B S hS (presentationGroupoid (blowUpPresentation Z P hcU hcR heq)) :=
  equivalenceQuasicoherentFromSpaceBase B S hS _ _
    (presentationAtlas_isEtale (blowUpPresentation Z P hcU hcR heq))
    (presentationAtlas_comm (blowUpPresentation Z P hcU hcR heq))
    (presentationAtlas_isEtaleCovering (blowUpPresentation Z P hcU hcR heq))
    (presentationAtlas_relativelyRepresentable (blowUpPresentation Z P hcU hcR heq))
    (presentationGroupoid_isPullback (blowUpPresentation Z P hcU hcR heq))

/-- **The descended twisting sheaf `𝒪_{X'}(1)`** of the blowup of an algebraic space: the
quasi-coherent `𝒪_{X'}`-module corresponding to `(𝒪_{P_U}(1)^a, α')` under the equivalence of
Stacks 03M3 for the presentation by `P_R ⇉ P_U`. -/
def blowUpTwistOne :
    QuasicoherentSheaves.{u, u} B S hS (blowUpAlong Z P hcU hcR heq).obj
      (blowUpAlong Z P hcU hcR heq).property :=
  (blowUpQcohEquivalence Z P hcU hcR heq).inverse.obj (blowUpTwistDescentDatum Z P hcU hcR heq)

/-- **`𝒪_{X'}(1) ≅ 𝓘_E`.**  The descent datum of `𝒪_{X'}(1)` is isomorphic to that of the pullback
of `𝓘_E`, and the equivalence of Stacks 03M3 carries the isomorphism back to `X'`. -/
def blowUpTwistOneIso : blowUpTwistOne Z P hcU hcR heq ≅ exceptionalIdealQcoh Z P hcU hcR heq :=
  (blowUpQcohEquivalence Z P hcU hcR heq).inverse.mapIso
      (transportedQuasicoherentModuleIso _ _ _) ≪≫
    ((blowUpQcohEquivalence Z P hcU hcR heq).unitIso.app
      (exceptionalIdealQcoh Z P hcU hcR heq)).symm

/-- The isomorphism `𝒪_{X'}(1) ≅ 𝓘_E` of `AlgebraicGeometry.Space.blowUpTwistOneIso`, read on the
underlying sheaves of modules. -/
def blowUpTwistOneModuleIso :
    (blowUpTwistOne Z P hcU hcR heq).obj ≅
      idealSheafOfModules B S hS (blowUpAlong Z P hcU hcR heq)
        (exceptionalDivisor Z P hcU hcR heq) :=
  (ObjectProperty.ι _).mapIso (blowUpTwistOneIso Z P hcU hcR heq)

/-- The ideal sheaf of the exceptional divisor is invertible: part (2) of Stacks 085T. -/
instance isInvertible_idealSheafOfModules_exceptionalDivisor :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureCommRings B S hS (blowUpAlong Z P hcU hcR heq))
      (structureRingSheaf B S hS (blowUpAlong Z P hcU hcR heq)).property
      (idealSheafOfModules B S hS (blowUpAlong Z P hcU hcR heq)
        (exceptionalDivisor Z P hcU hcR heq)) :=
  isEffectiveCartierDivisor_exceptionalDivisor_blowUpAlong Z P hcU hcR heq

/-- The descended twisting sheaf `𝒪_{X'}(1)` is invertible. -/
instance isInvertible_blowUpTwistOne :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (structureCommRings B S hS (blowUpAlong Z P hcU hcR heq))
      (structureRingSheaf B S hS (blowUpAlong Z P hcU hcR heq)).property
      (blowUpTwistOne Z P hcU hcR heq).obj :=
  Stacks.SheafOfModules.isInvertible_of_iso _ _ (blowUpTwistOneModuleIso Z P hcU hcR heq).symm

/-- **The twisting sheaves `𝒪_{X'}(n)`**, the integer tensor powers of the descended
`𝒪_{X'}(1)` (Stacks 01CU). -/
def blowUpTwistSpace (n : ℤ) :
    SheafOfModules.{u} (structureRingSheaf B S hS (blowUpAlong Z P hcU hcR heq)) :=
  Stacks.SheafOfModules.Invertible.tensorPower
    (structureCommRings B S hS (blowUpAlong Z P hcU hcR heq))
    (structureRingSheaf B S hS (blowUpAlong Z P hcU hcR heq)).property
    (blowUpTwistOne Z P hcU hcR heq).obj n

/-- `𝒪_{X'}(n)` is the `n`th tensor power of `𝓘_E`, by
`AlgebraicGeometry.Space.blowUpTwistOneIso`. -/
def blowUpTwistSpaceIso (n : ℤ) :
    blowUpTwistSpace Z P hcU hcR heq n ≅
      Stacks.SheafOfModules.Invertible.tensorPower
        (structureCommRings B S hS (blowUpAlong Z P hcU hcR heq))
        (structureRingSheaf B S hS (blowUpAlong Z P hcU hcR heq)).property
        (idealSheafOfModules B S hS (blowUpAlong Z P hcU hcR heq)
          (exceptionalDivisor Z P hcU hcR heq)) n :=
  @Stacks.SheafOfModules.TensorPower.tensorPowerCongr _ _ _
    (structureCommRings B S hS (blowUpAlong Z P hcU hcR heq))
    (structureRingSheaf B S hS (blowUpAlong Z P hcU hcR heq)).property _ _ _ _
    (Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence _ _ _)
    (Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence _ _ _)
    (blowUpTwistOneModuleIso Z P hcU hcR heq) n

/-- **`𝒪_{X'}(-1) ≅ 𝒪_{X'}(E)`** for the descended twisting sheaves, where `𝒪_{X'}(E)` is the
invertible sheaf of the effective Cartier divisor `E` of Stacks 0841 (1).  That it is the
canonical isomorphism of part (3) of Stacks 085T — the descent datum of `𝒪_{X'}(1)` being the
unique one compatible with the canonical map `𝒪(1) ⟶ 𝒪` — is recorded, and registered, in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupTwistDescentCanonical.lean`
(`AlgebraicGeometry.Space.blowUpTwistSpaceNegOneIsoAssociatedInvertibleSheaf`). -/
def blowUpTwistSpaceNegOneIso :
    blowUpTwistSpace Z P hcU hcR heq (-1) ≅
      associatedInvertibleSheaf B S hS (blowUpAlong Z P hcU hcR heq)
        (exceptionalDivisor Z P hcU hcR heq)
        (isEffectiveCartierDivisor_exceptionalDivisor_blowUpAlong Z P hcU hcR heq) :=
  blowUpTwistSpaceIso Z P hcU hcR heq (-1)

end AlgebraicGeometry.Space
