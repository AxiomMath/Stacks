module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectEssSurjAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentHomDescentZariskiLeaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentZariskiSchemeChartFlat
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentPerfectColimit

/-!
# The affine case of the essential surjectivity in Stacks 0DKW, from Stacks 0DI8

Let `D` be Situation 0DKU whose limit is a limit of schemes on affine charts, and let the space
`X₀` over the chosen stage be affine, `e₀ : h_{Z'} ≅ X₀`, with structure morphism through an étale
`w' : h_{V'} ⟶ Y₀` from an affine object `V'` of the site, `h_{t'} ≫ w' = e₀ ≫ p₀`.  The source
proves essential surjectivity in Stacks 0DKW in this case from Stacks 0DI8 for the inverse system
of affine schemes `Yᵢ ×_{Y₀} V'`, read through Stacks 0DKQ.  This file carries that out on the
model source data of `D` (`AlgebraicGeometry.Space.RelativeDescentSituation.modelSourceData`):

1. a `Y`-perfect object `E` of `D(𝒪_{h_W})` lies in `D_QCoh` (Stacks 08JL), so it is `ε^*E₀` for
   an `E₀ ∈ D_QCoh(𝒪_W)` (Stacks 071Q), and `E₀` is perfect relative to `W ⟶ W_{V'}` (Stacks
   0DKQ);
2. `E₀` comes from a stage by Stacks 0DI8, once read on the chart situation
   `AlgebraicGeometry.Space.RelativeDescentSituation.AffineBaseChangeRepresentation.chartSituation`
   of the base-change representation;
3. its `ε^*` at that stage is `Yⱼ`-perfect (Stacks 0DKQ), and pulls back to `E` through the
   comparison of the derived pullbacks of the Zariski and the small étale sites.

## Main definitions

* `AlgebraicGeometry.Space.RelativelyPerfectRepresentedChart`: Stacks 0DKQ, (1) ⇔ (2), at a
  represented chart, carried below as a hypothesis and proved by
  `AlgebraicGeometry.Space.relativelyPerfectRepresentedChart`.

## Main results

* `RelativeDescentSituation.relativelyPerfectEssentiallySurjective_modelSourceData`:
  essential surjectivity of the model, from Stacks 0DI8.
* `AlgebraicGeometry.Space.RelativeDescentSituation.relativelyPerfectAffineEssentiallySurjective`:
  the affine case of the essential surjectivity in Stacks 0DKW.
* `AlgebraicGeometry.Space.RelativeDescentSituation.relativelyPerfectColimit_of_representedChart`:
  Stacks 0DKW from full faithfulness, Stacks 0DKQ at represented charts and the comparison.

## Implementation notes

The comparison of the derived pullbacks of the Zariski and the small étale sites is an arbitrary
datum `Φ : AlgebraicGeometry.Space.RelativeDescentSituation.RepresentedDerivedPullbackComparison`
(piece (iv) of the affine leaf of Stacks 0DKV), for an arbitrary
pseudofunctoriality datum `P`; only its isomorphisms are used.  The instance environment is that
of `RelativeDescentHomDescentModel.lean`.  Stacks 0DI8 is stated for index types in the universe of
the schemes, so `I` lives in universe `u`.

Nothing here is registered.

## References

* [Stacks Project, Tag 0DKW](https://stacks.math.columbia.edu/tag/0DKW)
* [Stacks Project, Tag 0DI8](https://stacks.math.columbia.edu/tag/0DI8)
* [Stacks Project, Tag 0DKQ](https://stacks.math.columbia.edu/tag/0DKQ)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 08JL](https://stacks.math.columbia.edu/tag/08JL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 6000] preadditive_smallEtaleModules_model

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0DKQ, (1) ⇔ (2), at a represented chart.**  Let
`f : h_T ⟶ Y` be a flat morphism, locally of finite presentation, from the algebraic space
represented by an object `T` of the site, factoring as `h_g ≫ b` through an étale `b : h_{T'} ⟶ Y`
with `g : T ⟶ T'`.  For `E₀ ∈ D_QCoh(𝒪_T)`, the object `ε^*E₀` of `D(𝒪_{h_T})` (its counterpart
under Stacks 071Q) is `Y`-perfect exactly when `E₀` is `T'`-perfect in the sense of schemes.  This
is (1) ⇔ (2) of Stacks 0DKQ for the square `h_T ⟶ h_{T'}` of étale scheme charts over `f`, the
chart of the source being the identity.  In the direction (2) ⇒ (1) the hypothesis `E₀ ∈ D_QCoh`
is not asked: a `T'`-perfect `E₀` is pseudo-coherent, hence in `D_QCoh`
(`AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent`).  This proposition is proved by
`AlgebraicGeometry.Space.relativelyPerfectRepresentedChart`.  For a general square of étale
scheme charts the library's (1) ⇒ (2) and (3) ⇒ (1) are
`AlgebraicGeometry.Space.isPerfectRelativeTo_chartObject_of_isPerfectRelativeToCanonical` and
`AlgebraicGeometry.Space.isPerfectRelativeToCanonical_of_isPerfectRelativeTo_chartObject`, and
Stacks 0DKQ itself is registered on
`AlgebraicGeometry.Space.isPerfectRelativeToCanonical_tfae_chartDiagram`. -/
def RelativelyPerfectRepresentedChart : Prop :=
  ∀ {T T' : BigFppfOver B S hS} {Y : AlgebraicSpaces B S hS} (g : T ⟶ T')
    (b : yoneda.obj T' ⟶ Y.1) (f : yoneda.obj T ⟶ Y.1), IsEtale B S hS b →
    yoneda.map g ≫ b = f → ∀ (hfl : IsFlat B S hS f) (hlfp : IsLocallyOfFinitePresentation B S hS f)
      [Flat ((BigFppfOver.toScheme B S hS).map g)]
      [LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map g)]
      (E₀ : DerivedCategory (SheafOfModules.{u}
        (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace))),
      ((∀ i : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)) i).obj
          E₀).IsQuasicoherent) →
        RelativeDescentSituation.IsPerfectAlong
          (ObjectProperty.homMk f :
            (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ Y)
          hfl hlfp ((zariskiEtaleDerived B S hS T).obj E₀) →
        ((BigFppfOver.toScheme B S hS).map g).IsPerfectRelativeTo
          (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u} _) E₀) ∧
      (((BigFppfOver.toScheme B S hS).map g).IsPerfectRelativeTo
          (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u} _) E₀ →
        RelativeDescentSituation.IsPerfectAlong
          (ObjectProperty.homMk f :
            (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ Y)
          hfl hlfp ((zariskiEtaleDerived B S hS T).obj E₀))

namespace RelativeDescentSituation

attribute [local instance] isDirected_laterIndex

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation B S hS hZ I)

section ModelSourceData

variable {F : SourceData B S hS D.Y D.limitCone D.i₀} {Z' V' : BigAffineFppf B S hS}
  {e₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z') ≅ F.X₀}
  {R : (D.withSource F).AffineBaseChangeRepresentation Z' (e₀.hom ≫ F.p₀)}
  {w' : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V') ⟶ D.Y.obj (op D.i₀)}
  (hw' : IsEtale B S hS w')
  {t' : (BigAffineFppf.inclusion B S hS).obj Z' ⟶ (BigAffineFppf.inclusion B S hS).obj V'}
  (ht' : yoneda.map t' ≫ w' = e₀.hom ≫ F.p₀)
  (hflat : Flat ((BigFppfOver.toScheme B S hS).map t'))
  (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map t'))
  (RV : (D.withSource F).AffineBaseChangeRepresentation V' w')
  (hRV : IsLimit ((BigFppfOver.toScheme B S hS).mapCone RV.c))

/-- A property holding on every étale chart holds on the scheme map `g : T ⟶ T'` of a morphism
over an étale chart `w` of the target. -/
private theorem toScheme_map_of_holdsOnEveryEtaleChart {P : MorphismProperty Scheme.{u}}
    {T T' : BigFppfOver B S hS} {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : yoneda.obj T ⟶ G}
    (hf : HoldsOnEveryEtaleChart B S hS P f) {g : T ⟶ T'} {w : yoneda.obj T' ⟶ G}
    (hw : IsEtale B S hS w) (hgw : yoneda.map g ≫ w = f) :
    P ((BigFppfOver.toScheme B S hS).map g) :=
  holdsOnEveryEtaleChart_apply_of_isEtale hf (isEtale_of_isIso B S hS (𝟙 _)) hw
    (by simpa using hgw) (Iso.refl _) (Iso.refl _) _ (Category.id_comp _).symm

include hw' in
/-- **The limit side of the affine case**: a `Y`-perfect object `E` over the limit of the model is
`ε^*E₀` for some `E₀ ∈ D_QCoh(𝒪_W)` (Stacks 08JL, 071Q) whose transport to the limit of the chart
situation comes, by Stacks 0DI8, from a relatively perfect object at a stage `j`. -/
theorem exists_chartStage_of_isLimitPerfect (hchart : RelativelyPerfectRepresentedChart B S hS)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (schemeSpace R.c.pt))))
    (hE : (D.withSource (modelSourceData F e₀ R)).IsLimitPerfect E) :
    ∃ (E₀ : DerivedCategory (SheafOfModules.{u}
        (structureSheafRing ((BigFppfOver.toScheme B S hS).obj R.c.pt).toRingedSpace)))
      (_ : (zariskiEtaleDerived B S hS R.c.pt).obj E₀ ≅ E)
      (j : (RV.chartSituation hRV t' hflat hlfp).LaterIndex)
      (Ej : DerivedCategory (StrictlyPerfect.OXMod.{u, u}
        ((RV.chartSituation hRV t' hflat hlfp).schemeAt j).toRingedSpace)),
      (RV.chartSituation hRV t' hflat hlfp).IsPerfectAt j Ej ∧
        Nonempty ((derivedPullback
            ((RV.chartSituation hRV t' hflat hlfp).projection j).toLRSHom.toShHom).obj Ej ≅
          (derivedPullback (RV.chartLimitIso hRV t' hflat hlfp ht' R).inv.toLRSHom.toShHom).obj
            E₀) := by
  have : Flat (RV.chartSituation hRV t' hflat hlfp).X₀.hom :=
    (RV.chartSituation hRV t' hflat hlfp).flat
  have : LocallyOfFinitePresentation (RV.chartSituation hRV t' hflat hlfp).X₀.hom :=
    (RV.chartSituation hRV t' hflat hlfp).finitePresentation.locallyOfFinitePresentation
  have hsl : Flat (pullback.snd (RV.chartSituation hRV t' hflat hlfp).X₀.hom
      ((RV.chartSituation hRV t' hflat hlfp).descent.limitCone.π.app
        (op (RV.chartSituation hRV t' hflat hlfp).descent.base))) := inferInstance
  have hsl' : LocallyOfFinitePresentation
      (pullback.snd (RV.chartSituation hRV t' hflat hlfp).X₀.hom
        ((RV.chartSituation hRV t' hflat hlfp).descent.limitCone.π.app
          (op (RV.chartSituation hRV t' hflat hlfp).descent.base))) := inferInstance
  obtain ⟨E₀, hE₀q, ⟨α⟩⟩ := exists_zariskiEtaleDerived_iso B S hS R.c.pt E
    (derivedCategoryB_of_isPseudoCoherent_unconditional B S hS _ _ E hE.1)
  have hpc : IsEtale B S hS RV.pc := isEtale_of_isPullback_yoneda B S hS RV.isPullback_pt.flip hw'
  have : Flat ((BigFppfOver.toScheme B S hS).map (RV.mapOfCompPt R t' ht')) :=
    toScheme_map_of_holdsOnEveryEtaleChart
      (D.withSource (modelSourceData F e₀ R)).isFlat_limitStructure hpc
      (RV.mapOfCompPt_p R t' ht')
  have : LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (RV.mapOfCompPt R t' ht')) :=
    toScheme_map_of_holdsOnEveryEtaleChart
      (D.withSource (modelSourceData F e₀ R)).isLocallyOfFinitePresentation_limitStructure hpc
      (RV.mapOfCompPt_p R t' ht')
  have hE' : (D.withSource (modelSourceData F e₀ R)).IsLimitPerfect
      ((zariskiEtaleDerived B S hS R.c.pt).obj E₀) :=
    isPerfectAlong_of_iso _ _ _ α.symm hE
  have hE₀ := (hchart (Y := (D.withSource (modelSourceData F e₀ R)).limitTarget)
    (RV.mapOfCompPt R t' ht') RV.pc R.pc hpc (RV.mapOfCompPt_p R t' ht') _ _ E₀).1 hE₀q hE'
  have := (RV.chartSituation hRV t' hflat hlfp).compactSpace_limitScheme
  have hE₂ := (@Scheme.Hom.isPerfectRelativeTo_iso_over_iff _ _ _
    ((BigFppfOver.toScheme B S hS).map (RV.mapOfCompPt R t' ht')) _ _ _ hsl hsl' _
    (RV.chartLimitIso hRV t' hflat hlfp ht' R).symm
    ((Iso.inv_comp_eq _).2 (RV.chartLimitIso_hom_snd hRV t' hflat hlfp ht' R).symm) E₀).2 hE₀
  obtain ⟨j, Ej, hEj, hφ⟩ :=
    (RV.chartSituation hRV t' hflat hlfp).perfectEssentiallySurjectiveCanonical _ hE₂
  exact ⟨E₀, α, j, Ej, hEj, hφ⟩

include hw' in
/-- The morphism of schemes `W_j ⟶ W_{V',j}` of a stage of the model is flat and locally of
finite presentation: it is an étale chart of `Xⱼ ⟶ Yⱼ` (Stacks 03ML, 03XP). -/
theorem flat_toScheme_mapOfComp (j : D.LaterIndex) :
    Flat ((BigFppfOver.toScheme B S hS).map (RV.mapOfComp R t' ht' j)) ∧
      LocallyOfFinitePresentation
        ((BigFppfOver.toScheme B S hS).map (RV.mapOfComp R t' ht' j)) := by
  have hpj : IsEtale B S hS (RV.p j) :=
    isEtale_of_isPullback_yoneda B S hS (RV.isPullback j).flip hw'
  exact ⟨toScheme_map_of_holdsOnEveryEtaleChart
      ((D.withSource (modelSourceData F e₀ R)).isFlat_stageStructure j) hpj
      (RV.mapOfComp_p R t' ht' j),
    toScheme_map_of_holdsOnEveryEtaleChart
      ((D.withSource (modelSourceData F e₀ R)).isLocallyOfFinitePresentation_stageStructure j) hpj
      (RV.mapOfComp_p R t' ht' j)⟩

/-- The transport to the model of a relatively perfect object at a stage of the chart situation
is perfect relative to `W_j ⟶ W_{V',j}`. -/
theorem isPerfectRelativeTo_chartStage (j : (RV.chartSituation hRV t' hflat hlfp).LaterIndex)
    [hfj : Flat ((BigFppfOver.toScheme B S hS).map (RV.mapOfComp R t' ht' j.1))]
    [hlj : LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (RV.mapOfComp R t' ht' j.1))]
    (Ej : DerivedCategory (StrictlyPerfect.OXMod.{u, u}
      ((RV.chartSituation hRV t' hflat hlfp).schemeAt j).toRingedSpace))
    (hEj : (RV.chartSituation hRV t' hflat hlfp).IsPerfectAt j Ej) :
    ((BigFppfOver.toScheme B S hS).map (RV.mapOfComp R t' ht' j.1)).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u} _)
      ((derivedPullback (RV.chartStageIso hRV t' hflat hlfp ht' R j).hom.toLRSHom.toShHom).obj
        Ej) := by
  have : Flat (RV.chartSituation hRV t' hflat hlfp).X₀.hom :=
    (RV.chartSituation hRV t' hflat hlfp).flat
  have : LocallyOfFinitePresentation (RV.chartSituation hRV t' hflat hlfp).X₀.hom :=
    (RV.chartSituation hRV t' hflat hlfp).finitePresentation.locallyOfFinitePresentation
  have hst : Flat (pullback.snd (RV.chartSituation hRV t' hflat hlfp).X₀.hom
      ((RV.chartSituation hRV t' hflat hlfp).baseMap j)) := inferInstance
  have hst' : LocallyOfFinitePresentation
      (pullback.snd (RV.chartSituation hRV t' hflat hlfp).X₀.hom
        ((RV.chartSituation hRV t' hflat hlfp).baseMap j)) := inferInstance
  have := R.isAffine_W j.1
  exact (@Scheme.Hom.isPerfectRelativeTo_iso_over_iff _ _ _
    (pullback.snd (RV.chartSituation hRV t' hflat hlfp).X₀.hom
      ((RV.chartSituation hRV t' hflat hlfp).baseMap j))
    ((BigFppfOver.toScheme B S hS).map (RV.mapOfComp R t' ht' j.1)) hst hst' hfj hlj _
    (RV.chartStageIso hRV t' hflat hlfp ht' R j)
    (RV.chartStageIso_hom_snd hRV t' hflat hlfp ht' R j) Ej).2 hEj

include hw' in
/-- **The stage side of the affine case**: the transport to the model of a relatively perfect
object at a stage of the chart situation is, through `ε^*`, `Yⱼ`-perfect (Stacks 0DKQ). -/
theorem isStagePerfect_of_isPerfectAt_chart (hchart : RelativelyPerfectRepresentedChart B S hS)
    (j : (RV.chartSituation hRV t' hflat hlfp).LaterIndex)
    (Ej : DerivedCategory (StrictlyPerfect.OXMod.{u, u}
      ((RV.chartSituation hRV t' hflat hlfp).schemeAt j).toRingedSpace))
    (hEj : (RV.chartSituation hRV t' hflat hlfp).IsPerfectAt j Ej) :
    (D.withSource (modelSourceData F e₀ R)).IsStagePerfect j.1 ((zariskiEtaleDerived B S hS _).obj
      ((derivedPullback (RV.chartStageIso hRV t' hflat hlfp ht' R j).hom.toLRSHom.toShHom).obj
        Ej)) := by
  obtain ⟨hfj, hlj⟩ := D.flat_toScheme_mapOfComp (R := R) hw' ht' RV j.1
  have hEj' := D.isPerfectRelativeTo_chartStage (R := R) ht' hflat hlfp RV hRV j Ej hEj
  exact (hchart (Y := (D.withSource (modelSourceData F e₀ R)).stageTarget j.1)
    (RV.mapOfComp R t' ht' j.1) (RV.p j.1) (R.p j.1)
    (isEtale_of_isPullback_yoneda B S hS (RV.isPullback j.1).flip hw')
    (RV.mapOfComp_p R t' ht' j.1) _ _ _).2 hEj'

/-- **The comparison of the affine case**: the derived pullback to the limit of the model of the
object of `isStagePerfect_of_isPerfectAt_chart` is `ε^*E₀`, through the comparison `Φ` of the
derived pullbacks of the Zariski and the small étale sites and the identifications of the
stages and the limit of the chart situation. -/
def chartStageComparison {P : DerivedPullbackComposition B S hS}
    (Φ : RepresentedDerivedPullbackComparison B S hS P)
    (E₀ : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj R.c.pt).toRingedSpace)))
    (j : (RV.chartSituation hRV t' hflat hlfp).LaterIndex)
    (Ej : DerivedCategory (StrictlyPerfect.OXMod.{u, u}
      ((RV.chartSituation hRV t' hflat hlfp).schemeAt j).toRingedSpace))
    (φ : (derivedPullback
        ((RV.chartSituation hRV t' hflat hlfp).projection j).toLRSHom.toShHom).obj Ej ≅
      (derivedPullback (RV.chartLimitIso hRV t' hflat hlfp ht' R).inv.toLRSHom.toShHom).obj E₀) :
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS (R.c.π.app (op j.1)))).obj
        ((zariskiEtaleDerived B S hS _).obj
          ((derivedPullback (RV.chartStageIso hRV t' hflat hlfp ht' R j).hom.toLRSHom.toShHom).obj
            Ej)) ≅
      (zariskiEtaleDerived B S hS R.c.pt).obj E₀ :=
  (Φ.iso (R.c.π.app (op j.1))).app _ ≪≫ (zariskiEtaleDerived B S hS _).mapIso
    (((Stacks.DerivedPullback.schemeFactorSquareIso
        ((BigFppfOver.toScheme B S hS).map (R.c.π.app (op j.1)))
        (RV.chartStageIso hRV t' hflat hlfp ht' R j).hom
        (RV.chartLimitIso hRV t' hflat hlfp ht' R).hom
        ((RV.chartSituation hRV t' hflat hlfp).projection j)
        (RV.toScheme_map_π_comp_chartStageIso hRV t' hflat hlfp ht' R j)).app Ej).symm ≪≫
      (derivedPullback (RV.chartLimitIso hRV t' hflat hlfp ht' R).hom.toLRSHom.toShHom).mapIso φ ≪≫
      (Stacks.Cohomology.TorAmplitude.derivedPullbackHomCompInvIso
        (Scheme.forgetToRingedSpace.mapIso (RV.chartLimitIso hRV t' hflat hlfp ht' R).symm)).app E₀)

end ModelSourceData

/-- **Essential surjectivity of the model source data, from Stacks 0DI8.**  Let `F` be source
data over the inverse system of `D` with `e₀ : h_{Z'} ≅ F.X₀`, `Z'` affine, and let `R` represent
the base changes along `e₀ ≫ p₀`.  Suppose `e₀ ≫ p₀ = h_{t'} ≫ w'` with `w' : h_{V'} ⟶ Y₀` étale,
`V'` affine and `t'` flat and locally of finite presentation on underlying schemes.  Then the
situation of the model source data is essentially surjective.  The inputs are Stacks 0DKQ at
represented charts (`hchart`, proved by
`AlgebraicGeometry.Space.relativelyPerfectRepresentedChart`) and the comparison `Φ` of the derived
pullbacks of the Zariski and the small étale sites. -/
theorem relativelyPerfectEssentiallySurjective_modelSourceData
    {P : DerivedPullbackComposition B S hS} (Φ : RepresentedDerivedPullbackComparison B S hS P)
    (hchart : RelativelyPerfectRepresentedChart B S hS)
    (F : SourceData B S hS D.Y D.limitCone D.i₀) {Z' V' : BigAffineFppf B S hS}
    (e₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z') ≅ F.X₀)
    (R : (D.withSource F).AffineBaseChangeRepresentation Z' (e₀.hom ≫ F.p₀))
    (w' : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V') ⟶ D.Y.obj (op D.i₀))
    (hw' : IsEtale B S hS w')
    (t' : (BigAffineFppf.inclusion B S hS).obj Z' ⟶ (BigAffineFppf.inclusion B S hS).obj V')
    (ht' : yoneda.map t' ≫ w' = e₀.hom ≫ F.p₀)
    (hflat : Flat ((BigFppfOver.toScheme B S hS).map t'))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map t')) :
    (D.withSource (modelSourceData F e₀ R)).RelativelyPerfectEssentiallySurjective := by
  intro hM E₁ hE₁
  have hD' : (D.withSource F).IsSchemeLimit :=
    isSchemeLimit_withSource (D.withSource (modelSourceData F e₀ R)) F hM
  obtain ⟨RV⟩ : Nonempty ((D.withSource F).AffineBaseChangeRepresentation V' w') :=
    ⟨(D.withSource F).affineBaseChangeRepresentation V' w' hD'.1⟩
  have hRV := Classical.choice (hD'.2 V' w' RV)
  obtain ⟨E, hE⟩ : ∃ E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj R.c.pt, isAlgebraicSpace_yoneda B S hS R.c.pt⟩)), E = E₁ := ⟨E₁, rfl⟩
  subst hE
  obtain ⟨E₀, α, j, Ej, hEj, ⟨φ⟩⟩ :=
    D.exists_chartStage_of_isLimitPerfect hw' ht' hflat hlfp RV hRV hchart E hE₁
  exact ⟨j.1, _, D.isStagePerfect_of_isPerfectAt_chart hw' ht' hflat hlfp RV hRV hchart j Ej hEj,
    ⟨D.chartStageComparison ht' hflat hlfp RV hRV Φ E₀ j Ej φ ≪≫ α⟩⟩

/-- **The affine case of the essential surjectivity in Stacks 0DKW, from Stacks 0DI8.**  For a
situation with `I` in the universe of the schemes, every situation with its inverse system whose
space over the chosen stage is affine, with structure morphism through an étale `V ⟶ Y₀` from an
affine algebraic space, is essentially surjective.  The space and `V` are read as affine objects
`Z'`, `V'` of the site (`RelativeDescentSituation.exists_affineChart_of_etale_factorization`),
the situation as its model source data
(`RelativeDescentSituation.relativelyPerfectEssentiallySurjective_of_modelSourceData`),
and the model is essentially surjective by Stacks 0DI8
(`RelativeDescentSituation.relativelyPerfectEssentiallySurjective_modelSourceData`).
The inputs are Stacks 0DKQ at represented charts (`hchart`, proved by
`AlgebraicGeometry.Space.relativelyPerfectRepresentedChart`) and the comparison `Φ` of the
derived pullbacks of the Zariski and the small étale sites. -/
theorem relativelyPerfectAffineEssentiallySurjective {P : DerivedPullbackComposition B S hS}
    (Φ : RepresentedDerivedPullbackComparison B S hS P)
    (hchart : RelativelyPerfectRepresentedChart B S hS) :
    D.RelativelyPerfectAffineEssentiallySurjective := by
  intro F hF V w t hV hw ht
  obtain ⟨T, hT, ⟨e⟩⟩ := hF
  let Z' : BigAffineFppf B S hS := ⟨T, hT⟩
  obtain ⟨V', w', t', ht', hw', hflat, hlfp⟩ :=
    (D.withSource F).exists_affineChart_of_etale_factorization (𝟙 F.X₀)
      (isEtale_of_isIso B S hS (𝟙 _)) w t hV hw (ht.symm.trans (Category.id_comp _).symm)
      (Z' := Z') e.symm
  have ht'' : yoneda.map t' ≫ w' = e.symm.hom ≫ F.p₀ := by rw [ht', Category.id_comp]
  intro hD
  exact D.relativelyPerfectEssentiallySurjective_of_modelSourceData F (Z' := Z') e.symm
    ((D.withSource F).affineBaseChangeRepresentation Z' (e.symm.hom ≫ F.p₀) hD.1)
    (D.relativelyPerfectEssentiallySurjective_modelSourceData Φ hchart F (Z' := Z') e.symm _ w'
      hw' t' ht'' hflat hlfp) hD

/-- **Stacks 0DKW from full faithfulness, Stacks 0DKQ at represented charts and the comparison
of the Zariski and the small étale derived pullbacks.**
`AlgebraicGeometry.Space.RelativeDescentSituation.relativelyPerfectColimit_of_held'` with the
affine case discharged by Stacks 0DI8
(`AlgebraicGeometry.Space.RelativeDescentSituation.relativelyPerfectAffineEssentiallySurjective`).
The inputs are full faithfulness of every situation (`hff`, clauses (4), (5) of Stacks 0DKW, from
Stacks 0DKV, proved by
`AlgebraicGeometry.Space.RelativeDescentSituation.relativelyPerfectFullyFaithful_proved`),
Stacks 0DKQ at represented charts (`hchart`) and the comparison `Φ`. -/
theorem relativelyPerfectColimit_of_representedChart {P : DerivedPullbackComposition B S hS}
    (Φ : RepresentedDerivedPullbackComparison B S hS P)
    (hchart : RelativelyPerfectRepresentedChart B S hS)
    (hff : ∀ D' : RelativeDescentSituation B S hS hZ I, D'.RelativelyPerfectFullyFaithful) :
    D.RelativelyPerfectColimit :=
  D.relativelyPerfectColimit_of_held' hff (D.relativelyPerfectAffineEssentiallySurjective Φ hchart)

end RelativeDescentSituation

end AlgebraicGeometry.Space

end
