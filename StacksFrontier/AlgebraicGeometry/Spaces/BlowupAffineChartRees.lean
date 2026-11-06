module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFinality
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSmoothLocalCriterion
import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# The blowup of an algebraic space over an affine étale chart

Let `S` be a scheme, let `X` be an algebraic space over `S`, let `Z ⊆ X` be a closed subspace
with defining quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_X` and let `b : X' ⟶ X` be the blowup of `X`
in `Z`.  Let `U = Spec A` be an affine scheme of the site étale over `X` and let `I ⊆ A` be the
ideal corresponding to `ℐ|_U`.  Stacks 085R says that `U ×_X X'` is canonically the homogeneous
spectrum `Proj(⨁_{d ≥ 0} Iᵈ)` of the Rees algebra of `I` in `A`, as a scheme over `U`, and that
it has an affine open covering by the spectra of the affine blowup algebras `A[I/a]`, `a ∈ I`.
Both assertions are proved here.

## Main definitions

* `AlgebraicGeometry.Space.selfPresentation` is the presentation of the algebraic space of a
  scheme of the site by that scheme itself, with the identity for atlas and the diagonal for
  relation.
* `Stacks.Blowup.reesRelativeProjIsoProj` identifies, over an *affine* scheme, the relative
  `Proj` of the Rees algebra sheaf of a quasi-coherent sheaf of ideals with the ordinary `Proj`
  of the Rees algebra of its ideal of global sections.

## Main results

* `AlgebraicGeometry.Space.exists_iso_proj_reesGrading_affineChart` is **Stacks 085R, the
  canonical isomorphism**: the fibre product `U ×_X X'` is the algebraic space of a scheme of
  the site, by an isomorphism over `U`, and that scheme is `Proj` of the Rees algebra of `I`,
  again over `U`.
* `AlgebraicGeometry.Space.exists_iSup_opensRange_specAffineBlowupι_affineChart` is **Stacks
  085R, the affine open covering**: the morphisms `Spec A[I/a] ⟶ U ×_X X'`, for `a ∈ I`, are
  open immersions whose images have supremum the whole space.
* `AlgebraicGeometry.Space.exists_iso_schemeSpace_reesProjChart_of_isEtale` is the engine of
  both, for an arbitrary -- not necessarily affine -- étale scheme chart.
* `AlgebraicGeometry.Space.reesChartIdeal_selfPresentation_eq_ofIdealTop`: on an affine chart
  the sheaf of ideals induced by the centre is the ideal sheaf of the single ideal
  `AlgebraicGeometry.Space.definingIdealAt`, which is the ideal `I ⊆ A` of the source.

## Implementation notes

**The route.**  The source reads the statement off the construction of Stacks 085Q.  Here it is
derived instead from the universal property of Stacks 085U together with flat base change,
Stacks 085S, both of which are in the library:

* blowing up commutes with flat base change and an étale morphism is flat, so the projection
  `q : U ×_X X' ⟶ U` is the blowup of `U` in the inverse image of `Z`
  (`AlgebraicGeometry.Space.isBlowupAlong_preimage_of_isPullback_of_isFlat`);
* the algebraic space of the scheme `U` is presented by `U` itself,
  `AlgebraicGeometry.Space.selfPresentation`, so the construction of Stacks 085Q applies to it
  and `AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'` (Stacks 085U) exhibits
  `AlgebraicGeometry.Space.blowUpAlong'` of that presentation as a blowup of `U` in the same
  centre;
* for that presentation the two projections `P_R ⇉ P_U` of the relation of relative `Proj`s are
  the *same* morphism -- both are the comparison morphism along the identity of `U` -- so the
  quotient defining the blowup is `P_U` itself, which is
  `AlgebraicGeometry.Space.exists_iso_relativeProj_of_projSource_eq`;
* any two blowups of `U` in the same centre are isomorphic over `U`,
  `AlgebraicGeometry.Space.IsBlowupAlong.exists_iso`, which gives the isomorphism.

**What the statements carry.**  The blowup `b` is named by the universal property of Stacks
085U rather than by the construction, exactly as elsewhere in this development, and the fibre
product is taken as a hypothesis in the form of a cartesian square.  The only side conditions
are the three `B.Contains` conditions on the relative `Proj`s of the chart's own
self-presentation; they are the set-theoretic conditions that the construction of Stacks 085Q,
`AlgebraicGeometry.Space.blowUpAlong'`, already takes.  No hypothesis asserts any part of what
the tag asserts.

**The affine step.**  Over an affine base the relative `Proj` of a Rees algebra sheaf is the
ordinary `Proj` of the Rees algebra of the ideal of global sections: the chart of
`Stacks.Blowup.blowUp` over the affine open `⊤` is the base change of the isomorphism `⊤ ⟶ Y`,
hence an isomorphism, and the two remaining comparisons of constructions are
`Stacks.Blowup.reesSituationBlowUpIso` and `AlgebraicGeometry.blowUpIso`.  This is where the
affineness of `U` is used, and it is the content of Stacks 0804.

The ideal `I` is passed as a named parameter together with the equation identifying it, because
the graded-ring instance on `Stacks.Blowup.reesGrading` is not found when the ideal is spelled
out as the large term `(reesChartIdeal …).ideal ⊤`.

## References

* [Stacks Project, Tag 085R](https://stacks.math.columbia.edu/tag/085R)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 085S](https://stacks.math.columbia.edu/tag/085S)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### The diagonal is an equivalence relation -/

/-- The pair `(𝟙, 𝟙)` is an internal equivalence relation on any object: the diagonal. -/
def equivalenceRelationId {C : Type*} [Category C] (U : C) :
    CategoryTheory.EquivalenceRelation (𝟙 U) (𝟙 U) where
  right_cancellation _ _ _ _ := by simp
  r := 𝟙 U
  s := 𝟙 U
  c := (IsPullback.of_id_fst (f := 𝟙 U)).cone
  isLimit := (IsPullback.of_id_fst (f := 𝟙 U)).isLimit
  t := 𝟙 U
  transitivity₁ := by simp [IsPullback.cone]
  transitivity₂ := by simp [IsPullback.cone]

/-- The pair `(𝟙 U, 𝟙 U)` is an internal equivalence relation on `U`. -/
instance isEquivalenceRelationId {C : Type*} [Category C] (U : C) :
    CategoryTheory.IsEquivalenceRelation (𝟙 U) (𝟙 U) :=
  (equivalenceRelationId U).isEquivalenceRelation

/-! ### A scheme of the site presents itself -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The identity pre-relation on a scheme of the site is an étale equivalence relation. -/
theorem isEtaleEquivalenceRelation_id (V : BigFppfOver B S hS) :
    Stacks.Groupoids.IsEtaleEquivalenceRelation
      (prod.lift ((Over.post B.inclusion).map (𝟙 V)) ((Over.post B.inclusion).map (𝟙 V))) := by
  have hs : Stacks.Groupoids.PreRelation.source
      (prod.lift ((Over.post B.inclusion).map (𝟙 V)) ((Over.post B.inclusion).map (𝟙 V))) =
      𝟙 ((Over.post B.inclusion).obj V) :=
    (prod.lift_snd _ _).trans (CategoryTheory.Functor.map_id _ _)
  have ht : Stacks.Groupoids.PreRelation.target
      (prod.lift ((Over.post B.inclusion).map (𝟙 V)) ((Over.post B.inclusion).map (𝟙 V))) =
      𝟙 ((Over.post B.inclusion).obj V) :=
    (prod.lift_fst _ _).trans (CategoryTheory.Functor.map_id _ _)
  have _ : CategoryTheory.IsEquivalenceRelation
      (Stacks.Groupoids.PreRelation.target
        (prod.lift ((Over.post B.inclusion).map (𝟙 V)) ((Over.post B.inclusion).map (𝟙 V))))
      (Stacks.Groupoids.PreRelation.source
        (prod.lift ((Over.post B.inclusion).map (𝟙 V)) ((Over.post B.inclusion).map (𝟙 V)))) := by
    rw [hs, ht]; infer_instance
  have _ : Etale (Stacks.Groupoids.PreRelation.source
      (prod.lift ((Over.post B.inclusion).map (𝟙 V))
        ((Over.post B.inclusion).map (𝟙 V)))).left := by
    rw [hs]; exact inferInstanceAs (Etale (𝟙 _))
  have _ : Etale (Stacks.Groupoids.PreRelation.target
      (prod.lift ((Over.post B.inclusion).map (𝟙 V))
        ((Over.post B.inclusion).map (𝟙 V)))).left := by
    rw [ht]; exact inferInstanceAs (Etale (𝟙 _))
  exact ⟨⟩

/-- **A scheme of the site is presented by itself.**  The identity is a surjective étale atlas
of the algebraic space of a scheme, and its kernel pair is the diagonal. -/
abbrev selfPresentation (V : BigFppfOver B S hS) :
    Presentation B S hS (schemeSpace V).obj (schemeSpace V).property where
  U := V
  R := V
  target := 𝟙 V
  source := 𝟙 V
  isEtaleEquivalenceRelation := isEtaleEquivalenceRelation_id B S hS V
  toSpace := 𝟙 (yoneda.obj V)
  surjective :=
    have _ : MorphismProperty.ContainsIdentities
        (@Surjective.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsMultiplicative.toContainsIdentities
    have _ : MorphismProperty.ContainsIdentities
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) :=
      MorphismProperty.ContainsIdentities.inverseImage (BigFppfOver.toScheme B S hS)
    have _ : MorphismProperty.RespectsIso
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) :=
      MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme B S hS)
    MorphismProperty.presheaf_of_isIso _ (𝟙 (yoneda.obj V))
  etale :=
    have _ : MorphismProperty.ContainsIdentities
        (@Etale.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsMultiplicative.toContainsIdentities
    have _ : MorphismProperty.ContainsIdentities
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) :=
      MorphismProperty.ContainsIdentities.inverseImage (BigFppfOver.toScheme B S hS)
    have _ : MorphismProperty.RespectsIso
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) :=
      MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme B S hS)
    MorphismProperty.presheaf_of_isIso _ (𝟙 (yoneda.obj V))
  isPullback := by
    rw [CategoryTheory.Functor.map_id]
    exact IsPullback.of_id_fst (f := 𝟙 (yoneda.obj V))

/-! ### A relative Proj glued along the identity relation is its own chart -/

open Stacks.Groupoids in
/-- **If the two projections of the relation of relative Projs coincide, the quotient is the
chart.**  The quotient sheaf of a pre-relation whose source and target maps are equal is the
object itself: a map out of the chart identifying the two projections is any map at all, so the
chart has the universal property of the quotient. -/
theorem exists_iso_relativeProj_of_projSource_eq
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (d : ProjDescentData B S hS X hX) (h : d.projSource = d.projTarget) :
    ∃ e : yoneda.obj d.projChart ≅ d.relativeProj, e.hom = d.chart := by
  obtain ⟨e, he⟩ := exists_iso_quotientSheaf_of_descent (BigFppfOver.topology B S hS)
    (Over.post B.inclusion) d.projSource d.projTarget (prod.lift_snd _ _) (prod.lift_fst _ _)
    (isAlgebraicSpace_yoneda B S hS d.projChart).isSheaf (𝟙 (yoneda.obj d.projChart))
    (by rw [h]) (fun _ k _ =>
      ⟨k, Category.id_comp k, fun m hm => (Category.id_comp m).symm.trans hm⟩)
  exact ⟨e, ((Category.id_comp _).symm.trans he).trans d.chart_eq.symm⟩

/-! ### The two projections of the relation coincide for a self-presentation -/

/-- For the self-presentation of a scheme the two projections `P_R ⇉ P_U` of the relation of
relative Projs are the *same* morphism: both are the comparison morphism of relative Projs
along the identity of the chart. -/
theorem reesProjSource_eq_reesProjTarget_self (V : BigFppfOver B S hS)
    (N : (SheafOfModules.unit (structureRingSheaf B S hS (schemeSpace V))).Submodule)
    (hN : IsCartesianOnAffineCharts N.toSheafOfModules)
    (hcU : B.Contains (reesChartSituation N hN (selfPresentation B S hS V)).relativeProj)
    (hcR : B.Contains (reesRelationSituation N hN (selfPresentation B S hS V)).relativeProj) :
    reesProjSource N hN (selfPresentation B S hS V) hcU hcR =
      reesProjTarget N hN (selfPresentation B S hS V) hcU hcR :=
  rfl

/-! ### The blowup over an affine étale chart -/

section AffineChart

variable {B S hS} [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **The blowup of an algebraic space, pulled back to an étale scheme chart, is the relative
`Proj` of the Rees algebra of the induced sheaf of ideals on that chart.** -/
theorem exists_iso_schemeSpace_reesProjChart_of_isEtale
    {X X' W : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS X.obj}
    {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b)
    (V : BigFppfOver B S hS) {a : schemeSpace V ⟶ X} (ha : IsEtale B S hS a.hom)
    (hcU : B.Contains (reesChartSituation (centreIdeal (preimageClosedSubspace a Z))
      (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)).relativeProj)
    (hcR : B.Contains (reesRelationSituation (centreIdeal (preimageClosedSubspace a Z))
      (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)).relativeProj)
    (hcRR : B.Contains (reesDoubleSituation (centreIdeal (preimageClosedSubspace a Z))
      (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)).relativeProj)
    {q : W ⟶ schemeSpace V} {r : W ⟶ X'} (sq : IsPullback q r a b) :
    ∃ e : W ≅ schemeSpace (reesProjChart (centreIdeal (preimageClosedSubspace a Z))
        (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V) hcU),
      e.hom ≫ schemeSpaceMap (reesProjChartHom (centreIdeal (preimageClosedSubspace a Z))
        (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V) hcU) = q := by
  set P := selfPresentation B S hS V
  set ZV := preimageClosedSubspace a Z
  have hcart := isCartesianOnAffineCharts_centreIdeal ZV
  have hbW : IsBlowupAlong B S hS ZV q :=
    isBlowupAlong_preimage_of_isPullback_of_isFlat (isFlat_of_isEtale B S hS ha) hb sq
  obtain ⟨e₀, he₀⟩ := hbW.exists_iso (isBlowupAlong_blowUpAlongHom' ZV P hcU hcR hcRR)
  obtain ⟨e₁, he₁⟩ := exists_iso_relativeProj_of_projSource_eq B S hS
    (reesGlueingData (centreIdeal ZV) hcart P hcU hcR
      (isEquivalenceRelation_post_reesProj (centreIdeal ZV) hcart P hcU hcR
        hcRR)).toProjDescentData
    (reesProjSource_eq_reesProjTarget_self B S hS V (centreIdeal ZV) hcart hcU hcR)
  have hover : e₁.hom ≫ (reesGlueingData (centreIdeal ZV) hcart P hcU hcR
        (isEquivalenceRelation_post_reesProj (centreIdeal ZV) hcart P hcU hcR
          hcRR)).toProjDescentData.toBase =
      yoneda.map (reesProjChartHom (centreIdeal ZV) hcart P hcU) := by
    rw [he₁, ProjDescentData.chart_comp_toBase]
    exact Category.comp_id _
  let E : schemeSpace (reesProjChart (centreIdeal ZV) hcart P hcU) ≅
      blowUpAlong' ZV P hcU hcR hcRR :=
    { hom := ObjectProperty.homMk e₁.hom
      inv := ObjectProperty.homMk e₁.inv
      hom_inv_id := ObjectProperty.hom_ext _ e₁.hom_inv_id
      inv_hom_id := ObjectProperty.hom_ext _ e₁.inv_hom_id }
  have hEinv : E.inv ≫ schemeSpaceMap (reesProjChartHom (centreIdeal ZV) hcart P hcU) =
      blowUpAlongHom' ZV P hcU hcR hcRR :=
    E.inv_comp_eq.2 <| Eq.symm <| ObjectProperty.hom_ext _ hover
  refine ⟨e₀ ≪≫ E.symm, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hEinv, he₀]

end AffineChart

end AlgebraicGeometry.Space

namespace Stacks.Blowup

/-- The standard affine chart of `Proj` of the Rees algebra, followed by an isomorphism, is an
open immersion. -/
instance isOpenImmersion_specAffineBlowupι_comp {R : Type u} [CommRing R] (I : Ideal R) {a : R}
    (ha : a ∈ I) {T : Scheme.{u}} (g : AlgebraicGeometry.Proj (reesGrading I) ≅ T) :
    _root_.AlgebraicGeometry.IsOpenImmersion (specAffineBlowupι I a ha ≫ g.hom) :=
  _root_.AlgebraicGeometry.IsOpenImmersion.comp _ _

/-- **The spectra of the affine blowup algebras cover any scheme isomorphic to `Proj` of the
Rees algebra.**  Transport of `Stacks.Blowup.iSup_opensRange_specAffineBlowupι` along an
isomorphism. -/
theorem iSup_opensRange_specAffineBlowupι_comp {R : Type u} [CommRing R] (I : Ideal R)
    {T : Scheme.{u}} (g : AlgebraicGeometry.Proj (reesGrading I) ≅ T) :
    ⨆ r : I, (specAffineBlowupι I (r : R) r.2 ≫ g.hom).opensRange = ⊤ := by
  simp only [Scheme.Hom.opensRange_comp, ← Scheme.Hom.image_iSup,
    iSup_opensRange_specAffineBlowupι, Scheme.Hom.image_top_eq_opensRange,
    Scheme.Hom.opensRange_of_isIso]

/-- The whole space of an affine scheme, as an affine open. -/
def topAffineOpen (Y : Scheme.{u}) [IsAffine Y] : Y.affineOpens :=
  ⟨⊤, isAffineOpen_top Y⟩

/-- The inclusion of the whole space of an affine scheme is an isomorphism. -/
instance isIso_ι_topAffineOpen (Y : Scheme.{u}) [IsAffine Y] :
    IsIso ((topAffineOpen Y).1.ι) :=
  inferInstanceAs (IsIso Y.topIso.hom)

variable {Y : Scheme.{u}} [IsAffine Y] (J : Y.IdealSheafData)

/-- The chart of the blowup of an affine scheme over its whole space is an isomorphism: it is
the base change of the isomorphism `⊤ ⟶ Y`. -/
@[sga "6 VII 1.8" "special case"]
instance isIso_blowUpChart_topAffineOpen : IsIso (blowUpChart J (topAffineOpen Y)) :=
  (isPullback_blowUpChart J (topAffineOpen Y)).isIso_snd_of_isIso

/-- **On an affine scheme the relative `Proj` of the Rees algebra sheaf of a quasi-coherent
sheaf of ideals is the homogeneous spectrum of the Rees algebra of its ideal of global
sections.**  The chart of `Stacks.Blowup.blowUp` over the affine open `⊤` is an isomorphism
because it is the base change of the isomorphism `⊤ ⟶ Y`, and the two other comparisons are
`Stacks.Blowup.reesSituationBlowUpIso` and `AlgebraicGeometry.blowUpIso`. -/
@[sga "6 VII 1.8" "special case"]
def reesRelativeProjIsoProj :
    AlgebraicGeometry.Proj (reesGrading (J.ideal (topAffineOpen Y))) ≅
      (reesSituation J).relativeProj :=
  asIso (blowUpChart J (topAffineOpen Y)) ≪≫
    (AlgebraicGeometry.blowUpIso J).symm ≪≫ (reesSituationBlowUpIso J).symm

/-- **The comparison is an isomorphism over the affine base.** -/
theorem reesRelativeProjIsoProj_hom_comp :
    (reesRelativeProjIsoProj J).hom ≫ (reesSituation J).relativeProjToBase =
      toSpec (J.ideal (topAffineOpen Y)) ≫
        (Stacks.RelativeProj.isAffineOpen (topAffineOpen Y)).isoSpec.inv ≫
          (topAffineOpen Y).1.ι := by
  have hw := (isPullback_blowUpChart J (topAffineOpen Y)).w
  rw [chartToOpen_eq] at hw
  have hhom : (reesRelativeProjIsoProj J).hom = blowUpChart J (topAffineOpen Y) ≫
      ((AlgebraicGeometry.blowUpIso J).inv ≫ (reesSituationBlowUpIso J).inv) := rfl
  have hh : (reesRelativeProjIsoProj J).hom ≫ (reesSituation J).relativeProjToBase =
      blowUpChart J (topAffineOpen Y) ≫ ((AlgebraicGeometry.blowUpIso J).inv ≫
        ((reesSituationBlowUpIso J).inv ≫ (reesSituation J).relativeProjToBase)) := by
    rw [hhom, Category.assoc, Category.assoc]
  have e1 : ((reesSituationBlowUpIso J).inv ≫ (reesSituation J).relativeProjToBase :
      AlgebraicGeometry.blowUp J ⟶ Y) = AlgebraicGeometry.blowUpToBase J :=
    (reesSituationBlowUpIso J).inv_comp_eq.2 (reesSituationBlowUpIso_hom_blowUpToBase J).symm
  have e2 : ((AlgebraicGeometry.blowUpIso J).inv ≫ AlgebraicGeometry.blowUpToBase J :
      blowUp J ⟶ Y) = blowUpToBase J :=
    (AlgebraicGeometry.blowUpIso J).inv_comp_eq.2
      (AlgebraicGeometry.blowUpIso_hom_blowUpToBase J).symm
  have e3 : ((AlgebraicGeometry.blowUpIso J).inv ≫ ((reesSituationBlowUpIso J).inv ≫
      (reesSituation J).relativeProjToBase) : blowUp J ⟶ Y) = blowUpToBase J :=
    (congrArg (fun k : AlgebraicGeometry.blowUp J ⟶ Y =>
      (AlgebraicGeometry.blowUpIso J).inv ≫ k) e1).trans e2
  exact (hh.trans (congrArg (fun k : blowUp J ⟶ Y =>
    blowUpChart J (topAffineOpen Y) ≫ k) e3)).trans
    (hw.symm.trans (Category.assoc _ _ _))

/-- **The affine comparison, with the ideal of global sections named.**  Stating the
isomorphism with a named ideal `I` keeps the graded-ring instance on `Stacks.Blowup.reesGrading`
small enough to be found when the sheaf of ideals is a large term. -/
theorem exists_iso_proj_reesGrading_of_ideal_eq
    (I : Ideal ↥Γ(Y, (topAffineOpen Y).1)) (hI : J.ideal (topAffineOpen Y) = I) :
    ∃ f : AlgebraicGeometry.Proj (reesGrading I) ≅ (reesSituation J).relativeProj,
      f.hom ≫ (reesSituation J).relativeProjToBase =
        toSpec I ≫ (Stacks.RelativeProj.isAffineOpen (topAffineOpen Y)).isoSpec.inv ≫
          (topAffineOpen Y).1.ι := by
  subst hI
  exact ⟨reesRelativeProjIsoProj J, reesRelativeProjIsoProj_hom_comp J⟩

end Stacks.Blowup

namespace AlgebraicGeometry.Space

/-! ### The sheaf of ideals on an affine étale chart is a single ideal of `A` -/

variable {B S hS}

/-- **On an affine étale chart the sheaf of ideals whose Rees algebra the blowup is the relative
`Proj` of is the ideal sheaf of a single ideal `I ⊆ A`.**  The ideal is the defining ideal of
the centre on that chart. -/
theorem reesChartIdeal_selfPresentation_eq_ofIdealTop (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (Z : ClosedSubspaces B S hS (schemeSpace V).obj) :
    reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
        (selfPresentation B S hS V) =
      Scheme.IdealSheafData.ofIdealTop
        (definingIdealAt B S hS (schemeSpace V) Z
          (op (presentationChart (selfPresentation B S hS V)))) :=
  have : IsAffine (chartScheme (presentationChart (selfPresentation B S hS V))) :=
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj V))
  idealSheafDataOfChart_eq_ofIdealTop B S hS (schemeSpace V) Z
    (presentationChart (selfPresentation B S hS V))

/-- The scheme underlying `P_U` is the relative `Proj` of the Rees algebra of the sheaf of
ideals induced on the chart. -/
theorem toScheme_obj_reesProjChart {X : AlgebraicSpaces B S hS}
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hN : IsCartesianOnAffineCharts N.toSheafOfModules)
    (P : Presentation B S hS X.obj X.property)
    (hcU : B.Contains (reesChartSituation N hN P).relativeProj) :
    (BigFppfOver.toScheme B S hS).obj (reesProjChart N hN P hcU) =
      (Stacks.Blowup.reesSituation (reesChartIdeal N hN P)).relativeProj :=
  rfl

/-- The structure morphism of `P_U` over the chart is the structure morphism of that relative
`Proj`. -/
theorem toScheme_map_reesProjChartHom {X : AlgebraicSpaces B S hS}
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hN : IsCartesianOnAffineCharts N.toSheafOfModules)
    (P : Presentation B S hS X.obj X.property)
    (hcU : B.Contains (reesChartSituation N hN P).relativeProj) :
    (BigFppfOver.toScheme B S hS).map (reesProjChartHom N hN P hcU) =
      (Stacks.Blowup.reesSituation (reesChartIdeal N hN P)).relativeProjToBase :=
  rfl

/-! ### Stacks 085R: the blowup over an affine étale chart -/

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

set_option synthInstance.maxHeartbeats 400000 in
omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **Stacks 085R, the canonical isomorphism.**  Let `S` be a scheme, let `X` be an algebraic
space over `S`, let `Z ⊆ X` be a closed subspace with quasi-coherent defining sheaf of ideals
`ℐ ⊆ 𝒪_X` and let `b : X' ⟶ X` be the blowup of `X` in `Z`.  Let `U = Spec A` be an affine
scheme of the site étale over `X` and let `I ⊆ A` be the ideal corresponding to `ℐ|_U`.  Then
`U ×_X X'` is a scheme, and it is canonically isomorphic over `U` to the homogeneous spectrum
`Proj(⨁_{d ≥ 0} Iᵈ)` of the Rees algebra of `I` in `A`.

The first isomorphism exhibits the fibre product as the algebraic space of a scheme of the
site, namely the relative `Proj` `P_U` of the Rees algebra of `ℐ|_U`, compatibly with the
projections to `U`; the second identifies that scheme over `U` with `Proj` of the Rees algebra
of `I`, where `I` is the ideal of sections of `ℐ|_U` over `A`, which is the defining ideal of
the centre on the chart by
`AlgebraicGeometry.Space.reesChartIdeal_selfPresentation_eq_ofIdealTop`. -/
@[stacks 085R "the canonical isomorphism clause: for an affine scheme U = Spec A of the site \
étale over X, the fibre product U ×_X X' is the scheme Proj of the Rees algebra of the ideal \
I of A corresponding to the restriction of the centre's defining sheaf of ideals, by an \
isomorphism over U; the blowup b is named by the universal property of Stacks 085U, and the \
only side conditions are the three B.Contains conditions on the relative Projs of the chart's \
own presentation that the construction of Stacks 085Q already takes; the tag's affine open \
covering clause is a separate registration"]
theorem exists_iso_proj_reesGrading_affineChart
    {X X' W : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS X.obj}
    {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b)
    (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    {a : schemeSpace V ⟶ X} (ha : IsEtale B S hS a.hom)
    (hcU : B.Contains (reesChartSituation (centreIdeal (preimageClosedSubspace a Z))
      (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)).relativeProj)
    (hcR : B.Contains (reesRelationSituation (centreIdeal (preimageClosedSubspace a Z))
      (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)).relativeProj)
    (hcRR : B.Contains (reesDoubleSituation (centreIdeal (preimageClosedSubspace a Z))
      (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)).relativeProj)
    {q : W ⟶ schemeSpace V} {r : W ⟶ X'} (sq : IsPullback q r a b)
    (I : Ideal ↥Γ((BigFppfOver.toScheme B S hS).obj V,
      (Stacks.Blowup.topAffineOpen ((BigFppfOver.toScheme B S hS).obj V)).1))
    (hI : (reesChartIdeal (centreIdeal (preimageClosedSubspace a Z))
        (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)).ideal
        (Stacks.Blowup.topAffineOpen ((BigFppfOver.toScheme B S hS).obj V)) = I) :
    ∃ e : W ≅ schemeSpace (reesProjChart (centreIdeal (preimageClosedSubspace a Z))
        (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V) hcU),
      e.hom ≫ schemeSpaceMap (reesProjChartHom (centreIdeal (preimageClosedSubspace a Z))
          (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V) hcU) = q ∧
      ∃ f : AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading I) ≅
          (BigFppfOver.toScheme B S hS).obj
            (reesProjChart (centreIdeal (preimageClosedSubspace a Z))
              (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V) hcU),
        f.hom ≫ (BigFppfOver.toScheme B S hS).map
            (reesProjChartHom (centreIdeal (preimageClosedSubspace a Z))
              (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V) hcU) =
          Stacks.Blowup.toSpec I ≫
            (Stacks.RelativeProj.isAffineOpen (Stacks.Blowup.topAffineOpen
              ((BigFppfOver.toScheme B S hS).obj V))).isoSpec.inv ≫
              (Stacks.Blowup.topAffineOpen ((BigFppfOver.toScheme B S hS).obj V)).1.ι := by
  obtain ⟨e, he⟩ := exists_iso_schemeSpace_reesProjChart_of_isEtale hb V ha hcU hcR hcRR sq
  exact ⟨e, he, Stacks.Blowup.exists_iso_proj_reesGrading_of_ideal_eq _ I hI⟩

set_option synthInstance.maxHeartbeats 400000 in
omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **Stacks 085R, the affine open covering.**  In the situation of
`AlgebraicGeometry.Space.exists_iso_proj_reesGrading_affineChart`, the scheme representing
`U ×_X X'` has an affine open covering by the spectra of the affine blowup algebras
`A[I/a]`, `a ∈ I`: the morphisms `Spec A[I/a] ⟶ U ×_X X'` obtained by composing the standard
chart `Stacks.Blowup.specAffineBlowupι` with the identification of the previous theorem -- the
same isomorphism over `U`, whose compatibility with the projections to `U` is restated here --
are open immersions whose images have supremum the whole space.

The sources of the covering morphisms are the spectra of the affine blowup algebras
`Stacks.Blowup.affineBlowup I a` by construction, so this is the tag's "Moreover" clause. -/
@[stacks 085R "the affine open covering clause: the scheme U ×_X X' is covered by the images \
of the open immersions Spec A[I/a] ⟶ U ×_X X', a ∈ I, out of the spectra of the affine blowup \
algebras; same hypotheses and same side conditions as the canonical-isomorphism clause"]
theorem exists_iSup_opensRange_specAffineBlowupι_affineChart
    {X X' W : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS X.obj}
    {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b)
    (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    {a : schemeSpace V ⟶ X} (ha : IsEtale B S hS a.hom)
    (hcU : B.Contains (reesChartSituation (centreIdeal (preimageClosedSubspace a Z))
      (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)).relativeProj)
    (hcR : B.Contains (reesRelationSituation (centreIdeal (preimageClosedSubspace a Z))
      (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)).relativeProj)
    (hcRR : B.Contains (reesDoubleSituation (centreIdeal (preimageClosedSubspace a Z))
      (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)).relativeProj)
    {q : W ⟶ schemeSpace V} {r : W ⟶ X'} (sq : IsPullback q r a b)
    (I : Ideal ↥Γ((BigFppfOver.toScheme B S hS).obj V,
      (Stacks.Blowup.topAffineOpen ((BigFppfOver.toScheme B S hS).obj V)).1))
    (hI : (reesChartIdeal (centreIdeal (preimageClosedSubspace a Z))
        (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V)).ideal
        (Stacks.Blowup.topAffineOpen ((BigFppfOver.toScheme B S hS).obj V)) = I) :
    ∃ e : W ≅ schemeSpace (reesProjChart (centreIdeal (preimageClosedSubspace a Z))
        (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V) hcU),
      e.hom ≫ schemeSpaceMap (reesProjChartHom (centreIdeal (preimageClosedSubspace a Z))
          (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V) hcU) = q ∧
      ∃ f : AlgebraicGeometry.Proj (Stacks.Blowup.reesGrading I) ≅
          (BigFppfOver.toScheme B S hS).obj
            (reesProjChart (centreIdeal (preimageClosedSubspace a Z))
              (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V) hcU),
        (f.hom ≫ (BigFppfOver.toScheme B S hS).map
            (reesProjChartHom (centreIdeal (preimageClosedSubspace a Z))
              (isCartesianOnAffineCharts_centreIdeal _) (selfPresentation B S hS V) hcU) =
          Stacks.Blowup.toSpec I ≫
            (Stacks.RelativeProj.isAffineOpen (Stacks.Blowup.topAffineOpen
              ((BigFppfOver.toScheme B S hS).obj V))).isoSpec.inv ≫
              (Stacks.Blowup.topAffineOpen ((BigFppfOver.toScheme B S hS).obj V)).1.ι) ∧
        (∀ c : I, _root_.AlgebraicGeometry.IsOpenImmersion
            (Stacks.Blowup.specAffineBlowupι I (c : _) c.2 ≫ f.hom)) ∧
          ⨆ c : I, (Stacks.Blowup.specAffineBlowupι I (c : _) c.2 ≫ f.hom).opensRange = ⊤ := by
  obtain ⟨e, he, f, hf⟩ :=
    exists_iso_proj_reesGrading_affineChart hb V ha hcU hcR hcRR sq I hI
  exact ⟨e, he, f, hf, fun c => Stacks.Blowup.isOpenImmersion_specAffineBlowupι_comp I c.2 f,
    Stacks.Blowup.iSup_opensRange_specAffineBlowupι_comp I f⟩

end AlgebraicGeometry.Space

end
