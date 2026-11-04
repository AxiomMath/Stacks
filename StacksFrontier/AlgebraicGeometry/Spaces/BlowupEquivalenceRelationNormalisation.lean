module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.ReesProjBaseChangeComposition

/-!
# Reflexivity and symmetry of the two projections of the relative Proj of a Rees algebra

`StacksFrontier/AlgebraicGeometry/Spaces/BlowupEquivalenceRelation.lean` reduces the
equivalence-relation condition on the two projections `P_R ⇉ P_U` of the relative Proj of the
Rees algebra of a quasi-coherent sheaf of ideals to three equations — reflexivity, symmetry and
transitivity — and records that each is an instance of a composition law for the base-change
comparison morphism of relative Proj. That law is now available, as
`Stacks.Blowup.reesSituationBaseChange_comp`, together with the identity law
`Stacks.Blowup.reesSituationBaseChange_id`. This file discharges **two of the three equations**
with them.

The input is that the relation scheme of an étale presentation is the kernel pair of the atlas,
so it carries a diagonal `Δ : U ⟶ R` with `Δ ≫ t = Δ ≫ s = 𝟙` and a symmetry `σ : R ⟶ R` with
`σ ≫ t = s` and `σ ≫ s = t`. Both are morphisms of étale charts, so both carry the induced sheaf
of ideals on one chart to the induced sheaf of ideals on the other, and both are étale — being
étale after composition with an étale morphism. Hence both induce comparison morphisms of
relative Projs, and the composition law turns each of the four identities above into the
corresponding identity for the projections `P_R ⇉ P_U`. The reflexivity and symmetry witnesses of
`StacksFrontier/AlgebraicGeometry/Spaces/DescentEquivalenceRelation.lean` are unique, so that is
exactly the first two of the three equations.

**Transitivity is not proved here**, and nothing in this file claims the equivalence-relation
condition of Tag 085Q. That equation lives over `R ×_U R`, and it needs the Rees algebra and the
relative Proj of the sheaf of ideals induced on that scheme, which is not a chart supplied by the
presentation.

## Main definitions

* `AlgebraicGeometry.Space.presentationDiag` and `AlgebraicGeometry.Space.presentationSym`: the
  diagonal and the symmetry of the relation of an étale presentation, obtained from the kernel
  pair property through the fullness of `CategoryTheory.yoneda`.
* `AlgebraicGeometry.Space.presentationRelationDiagHom` and
  `AlgebraicGeometry.Space.presentationRelationSymHom`: the same two, as morphisms of étale
  charts.
* `AlgebraicGeometry.Space.reesProjDiag` and `AlgebraicGeometry.Space.reesProjSym`: the induced
  comparison morphisms `P_U ⟶ P_R` and `P_R ⟶ P_R`.

## Main results

* `AlgebraicGeometry.Space.reesSituationBaseChange_comp_str`: a comparison morphism of relative
  Projs over a morphism of the big fppf category over `S` is a morphism over `S`.

* `AlgebraicGeometry.Space.reesProjDiag_comp_reesProjTarget` and
  `AlgebraicGeometry.Space.reesProjDiag_comp_reesProjSource`: the diagonal comparison is a
  section of both projections.
* `AlgebraicGeometry.Space.reesProjSym_comp_reesProjTarget` and
  `AlgebraicGeometry.Space.reesProjSym_comp_reesProjSource`: the symmetry comparison exchanges
  the two projections.
* `AlgebraicGeometry.Space.reflexivity_post_reesProj` and
  `AlgebraicGeometry.Space.symmetry_post_reesProj`: **the first two of the three equations** of
  `AlgebraicGeometry.Space.isEquivalenceRelation_post_reesProj_of_normalisation`.

## Implementation notes

The diagonal and the symmetry are produced at the level of presheaves, where the kernel pair
property `AlgebraicGeometry.Space.Presentation.isPullback` lives, and then transported to the big
fppf category by the fullness of `CategoryTheory.yoneda`; their defining identities are checked
back in presheaves by its faithfulness.

That both are étale is `AlgebraicGeometry.Etale.of_comp`: `Δ ≫ t` is the identity and `σ ≫ t` is
`s`, both étale, and `t` is étale.

The two equations are proved by `BigFppfOver.map_toScheme_injective`, which reduces an identity
of morphisms of the big fppf category over `S` to the identity of the underlying morphisms of
schemes, where `Stacks.Blowup.reesSituationBaseChange_comp` applies. The morphism of base
schemes of the resulting single comparison is `Δ ≫ t` rather than `𝟙`, so
`Stacks.Blowup.reesSituationBaseChange_congr` is used to replace it before
`Stacks.Blowup.reesSituationBaseChange_id`.

Two global instances are added, `AlgebraicGeometry.Space.flat_toScheme_map_presentationDiag` and
`AlgebraicGeometry.Space.flat_toScheme_map_presentationSym`, so that the comparison morphisms
along the diagonal and the symmetry can be written down at all; the existing
`AlgebraicGeometry.Space.flat_toScheme_map_presentation_source` and `_target` are theorems, and
are introduced by `have` where they are needed.

No `@[stacks 085Q]` attribute is attached. The three declarations of Tag 085Q in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupRelativeProj.lean` still carry the
equivalence-relation condition as a parameter, and they must: with transitivity open, that
condition is not discharged, and a fourth copy of the tag on a statement that still assumes it
would add no coverage.

## References

* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS}

/-! ### The diagonal and the symmetry of the relation -/

/-- **The diagonal of the relation of an étale presentation.** The relation scheme is the kernel
pair of the atlas, so the pair `(𝟙, 𝟙)` of maps out of the presenting scheme factors through it;
the factorisation exists in the big fppf category because `CategoryTheory.yoneda` is full. -/
def presentationDiag (P : Presentation B S hS X.obj X.property) : P.U ⟶ P.R :=
  yoneda.preimage (P.isPullback.lift (𝟙 (yoneda.obj P.U)) (𝟙 (yoneda.obj P.U)) rfl)

/-- The diagonal is a section of the target leg. -/
theorem presentationDiag_comp_target (P : Presentation B S hS X.obj X.property) :
    presentationDiag P ≫ P.target = 𝟙 P.U := by
  refine yoneda.map_injective ?_
  rw [CategoryTheory.Functor.map_comp, presentationDiag, yoneda.map_preimage,
    P.isPullback.lift_fst]
  exact (CategoryTheory.Functor.map_id yoneda P.U).symm

/-- The diagonal is a section of the source leg. -/
theorem presentationDiag_comp_source (P : Presentation B S hS X.obj X.property) :
    presentationDiag P ≫ P.source = 𝟙 P.U := by
  refine yoneda.map_injective ?_
  rw [CategoryTheory.Functor.map_comp, presentationDiag, yoneda.map_preimage,
    P.isPullback.lift_snd]
  exact (CategoryTheory.Functor.map_id yoneda P.U).symm

/-- **The symmetry of the relation of an étale presentation.** The relation scheme is the kernel
pair of the atlas, so the pair `(s, t)` of maps out of it factors through it. -/
def presentationSym (P : Presentation B S hS X.obj X.property) : P.R ⟶ P.R :=
  yoneda.preimage (P.isPullback.lift (yoneda.map P.source) (yoneda.map P.target)
    P.isPullback.w.symm)

/-- The symmetry carries the target leg to the source leg. -/
theorem presentationSym_comp_target (P : Presentation B S hS X.obj X.property) :
    presentationSym P ≫ P.target = P.source := by
  refine yoneda.map_injective ?_
  rw [CategoryTheory.Functor.map_comp, presentationSym, yoneda.map_preimage,
    P.isPullback.lift_fst]

/-- The symmetry carries the source leg to the target leg. -/
theorem presentationSym_comp_source (P : Presentation B S hS X.obj X.property) :
    presentationSym P ≫ P.source = P.target := by
  refine yoneda.map_injective ?_
  rw [CategoryTheory.Functor.map_comp, presentationSym, yoneda.map_preimage,
    P.isPullback.lift_snd]

/-! ### The two morphisms are étale -/

/-- The diagonal is a section of the target leg, read on the underlying schemes. -/
theorem toScheme_map_presentationDiag_comp_target
    (P : Presentation B S hS X.obj X.property) :
    (BigFppfOver.toScheme B S hS).map (presentationDiag P) ≫
        (BigFppfOver.toScheme B S hS).map P.target =
      𝟙 ((BigFppfOver.toScheme B S hS).obj P.U) := by
  rw [← CategoryTheory.Functor.map_comp, presentationDiag_comp_target,
    CategoryTheory.Functor.map_id]

/-- The diagonal is a section of the source leg, read on the underlying schemes. -/
theorem toScheme_map_presentationDiag_comp_source
    (P : Presentation B S hS X.obj X.property) :
    (BigFppfOver.toScheme B S hS).map (presentationDiag P) ≫
        (BigFppfOver.toScheme B S hS).map P.source =
      𝟙 ((BigFppfOver.toScheme B S hS).obj P.U) := by
  rw [← CategoryTheory.Functor.map_comp, presentationDiag_comp_source,
    CategoryTheory.Functor.map_id]

/-- The symmetry exchanges the two legs, read on the underlying schemes. -/
theorem toScheme_map_presentationSym_comp_target
    (P : Presentation B S hS X.obj X.property) :
    (BigFppfOver.toScheme B S hS).map (presentationSym P) ≫
        (BigFppfOver.toScheme B S hS).map P.target =
      (BigFppfOver.toScheme B S hS).map P.source := by
  rw [← CategoryTheory.Functor.map_comp, presentationSym_comp_target]

/-- The symmetry exchanges the two legs, read on the underlying schemes. -/
theorem toScheme_map_presentationSym_comp_source
    (P : Presentation B S hS X.obj X.property) :
    (BigFppfOver.toScheme B S hS).map (presentationSym P) ≫
        (BigFppfOver.toScheme B S hS).map P.source =
      (BigFppfOver.toScheme B S hS).map P.target := by
  rw [← CategoryTheory.Functor.map_comp, presentationSym_comp_source]

/-- **The diagonal is étale**: composed with the étale target leg it is the identity. -/
theorem etale_toScheme_map_presentationDiag (P : Presentation B S hS X.obj X.property) :
    Etale ((BigFppfOver.toScheme B S hS).map (presentationDiag P)) := by
  have := etale_toScheme_map_presentation_target P
  have : Etale ((BigFppfOver.toScheme B S hS).map (presentationDiag P) ≫
      (BigFppfOver.toScheme B S hS).map P.target) := by
    rw [toScheme_map_presentationDiag_comp_target]
    infer_instance
  exact Etale.of_comp _ ((BigFppfOver.toScheme B S hS).map P.target)

/-- The diagonal is flat: it is étale. -/
instance flat_toScheme_map_presentationDiag (P : Presentation B S hS X.obj X.property) :
    AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map (presentationDiag P)) :=
  have := etale_toScheme_map_presentationDiag P
  inferInstance

/-- **The symmetry is étale**: composed with the étale target leg it is the étale source leg. -/
theorem etale_toScheme_map_presentationSym (P : Presentation B S hS X.obj X.property) :
    Etale ((BigFppfOver.toScheme B S hS).map (presentationSym P)) := by
  have := etale_toScheme_map_presentation_target P
  have := etale_toScheme_map_presentation_source P
  have : Etale ((BigFppfOver.toScheme B S hS).map (presentationSym P) ≫
      (BigFppfOver.toScheme B S hS).map P.target) := by
    rw [toScheme_map_presentationSym_comp_target]
    infer_instance
  exact Etale.of_comp _ ((BigFppfOver.toScheme B S hS).map P.target)

/-- The symmetry is flat: it is étale. -/
instance flat_toScheme_map_presentationSym (P : Presentation B S hS X.obj X.property) :
    AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map (presentationSym P)) :=
  have := etale_toScheme_map_presentationSym P
  inferInstance

/-! ### The two morphisms are morphisms of étale charts -/

/-- The diagonal, as a morphism of étale charts: its composite with the atlas is the structure
morphism of the chart, because it is a section of the source leg. -/
def presentationRelationDiagHom (P : Presentation B S hS X.obj X.property) :
    presentationChart P ⟶ presentationRelationChart P :=
  ObjectProperty.homMk (CostructuredArrow.homMk (presentationDiag P) (by
    change yoneda.map (presentationDiag P) ≫ yoneda.map P.source ≫ P.toSpace = P.toSpace
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, presentationDiag_comp_source,
      CategoryTheory.Functor.map_id, Category.id_comp]))

/-- The symmetry, as a morphism of étale charts: its composite with the source leg is the target
leg, and the two legs have the same composite with the atlas. -/
def presentationRelationSymHom (P : Presentation B S hS X.obj X.property) :
    presentationRelationChart P ⟶ presentationRelationChart P :=
  ObjectProperty.homMk (CostructuredArrow.homMk (presentationSym P) (by
    change yoneda.map (presentationSym P) ≫ yoneda.map P.source ≫ P.toSpace =
      yoneda.map P.source ≫ P.toSpace
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, presentationSym_comp_source]
    exact P.isPullback.w))

variable (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
  (hN : IsCartesianOnAffineCharts N.toSheafOfModules)
  (P : Presentation B S hS X.obj X.property)

/-- **The diagonal carries `ℐ|_R` to `ℐ|_U`.** Both are the sheaf of ideals that the same
construction produces on the chart. -/
theorem comap_reesRelationIdeal_diag :
    (reesRelationIdeal N hN P).comap ((BigFppfOver.toScheme B S hS).map (presentationDiag P))
      = reesChartIdeal N hN P :=
  comap_idealSheafDataOfChart B S hS X N hN (presentationRelationDiagHom P)

/-- **The symmetry carries `ℐ|_R` to itself.** -/
theorem comap_reesRelationIdeal_sym :
    (reesRelationIdeal N hN P).comap ((BigFppfOver.toScheme B S hS).map (presentationSym P))
      = reesRelationIdeal N hN P :=
  comap_idealSheafDataOfChart B S hS X N hN (presentationRelationSymHom P)

/-! ### The induced comparison morphisms of relative Proj -/

variable (hcU : B.Contains (reesChartSituation N hN P).relativeProj)
  (hcR : B.Contains (reesRelationSituation N hN P).relativeProj)

/-- **The comparison morphism of relative Projs is a morphism over `S`.** For a morphism
`g : V ⟶ W` of the big fppf category over `S`, flat on underlying schemes, and a presentation of
the sheaf of ideals on `V` as the inverse image of one on `W`, the comparison morphism commutes
with the two structure morphisms to `S` up to `g`, which is itself a morphism over `S`. This is
the general form of `AlgebraicGeometry.Space.reesSituationBaseChange_comp_structureMap`, which is
stated only for a morphism out of the relation chart. -/
theorem reesSituationBaseChange_comp_str {V W : BigFppfOver B S hS}
    (IW : ((BigFppfOver.toScheme B S hS).obj W).IdealSheafData) (g : V ⟶ W)
    [AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map g)]
    {IV : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData}
    (h : IW.comap ((BigFppfOver.toScheme B S hS).map g) = IV) :
    Stacks.Blowup.reesSituationBaseChange ((BigFppfOver.toScheme B S hS).map g) IW h ≫
        ((Stacks.Blowup.reesSituation IW).relativeProjToBase ≫ B.inclusion.map W.hom) =
      (Stacks.Blowup.reesSituation IV).relativeProjToBase ≫ B.inclusion.map V.hom := by
  have hw : (BigFppfOver.toScheme B S hS).map g ≫ B.inclusion.map W.hom =
      B.inclusion.map V.hom := by
    have h2 := congrArg B.inclusion.map (Over.w g)
    rwa [CategoryTheory.Functor.map_comp] at h2
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ B.inclusion.map W.hom)
      (Stacks.Blowup.reesSituationBaseChange_comp_relativeProjToBase _ _ h)).trans <|
    (Category.assoc _ _ _).trans (congrArg _ hw)

/-- **The diagonal comparison morphism `P_U ⟶ P_R`.** -/
def reesProjDiag : reesProjChart N hN P hcU ⟶ reesProjRelation N hN P hcR :=
  BigFppfOver.homMk B S hS hcR
    ((reesRelationSituation N hN P).relativeProjToBase ≫ B.inclusion.map P.R.hom)
    (Stacks.Blowup.reesSituationBaseChange
      ((BigFppfOver.toScheme B S hS).map (presentationDiag P)) (reesRelationIdeal N hN P)
      (comap_reesRelationIdeal_diag N hN P))
    (reesSituationBaseChange_comp_str (reesRelationIdeal N hN P) (presentationDiag P)
      (comap_reesRelationIdeal_diag N hN P))

/-- **The symmetry comparison morphism `P_R ⟶ P_R`.** -/
def reesProjSym : reesProjRelation N hN P hcR ⟶ reesProjRelation N hN P hcR :=
  BigFppfOver.homMk B S hS hcR
    ((reesRelationSituation N hN P).relativeProjToBase ≫ B.inclusion.map P.R.hom)
    (Stacks.Blowup.reesSituationBaseChange
      ((BigFppfOver.toScheme B S hS).map (presentationSym P)) (reesRelationIdeal N hN P)
      (comap_reesRelationIdeal_sym N hN P))
    (reesSituationBaseChange_comp_str (reesRelationIdeal N hN P) (presentationSym P)
      (comap_reesRelationIdeal_sym N hN P))

/-! ### Reflexivity and symmetry of the two projections -/

/-- Composing the comparison morphisms of relative Projs along `q` and `g` gives the comparison
along any `k` equal to `q ≫ g`. -/
private theorem reesSituationBaseChange_comp_eq {Y Z X : Scheme.{u}} (q : Y ⟶ Z) (g : Z ⟶ X)
    (k : Y ⟶ X) [AlgebraicGeometry.Flat q] [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.Flat k] (I : X.IdealSheafData) {J : Z.IdealSheafData}
    (hJ : I.comap g = J) {K : Y.IdealSheafData} (hK : J.comap q = K) (hk : q ≫ g = k)
    (hKk : I.comap k = K) :
    Stacks.Blowup.reesSituationBaseChange q J hK ≫ Stacks.Blowup.reesSituationBaseChange g I hJ =
      Stacks.Blowup.reesSituationBaseChange k I hKk := by
  subst hk
  exact Stacks.Blowup.reesSituationBaseChange_comp q g I hJ hK hKk

/-- **The diagonal comparison is a section of the target projection.** -/
theorem reesProjDiag_comp_reesProjTarget :
    reesProjDiag N hN P hcU hcR ≫ reesProjTarget N hN P hcU hcR =
      𝟙 (reesProjChart N hN P hcU) := by
  have := flat_toScheme_map_presentation_target P
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  exact (reesSituationBaseChange_comp_eq _ _ _ (reesChartIdeal N hN P)
    (comap_reesChartIdeal_target N hN P) (comap_reesRelationIdeal_diag N hN P)
    (toScheme_map_presentationDiag_comp_target P) (Scheme.IdealSheafData.comap_id _)).trans
    (Stacks.Blowup.reesSituationBaseChange_id (reesChartIdeal N hN P) _)

/-- **The diagonal comparison is a section of the source projection.** -/
theorem reesProjDiag_comp_reesProjSource :
    reesProjDiag N hN P hcU hcR ≫ reesProjSource N hN P hcU hcR =
      𝟙 (reesProjChart N hN P hcU) := by
  have := flat_toScheme_map_presentation_source P
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  exact (reesSituationBaseChange_comp_eq _ _ _ (reesChartIdeal N hN P)
    (comap_reesChartIdeal_source N hN P) (comap_reesRelationIdeal_diag N hN P)
    (toScheme_map_presentationDiag_comp_source P) (Scheme.IdealSheafData.comap_id _)).trans
    (Stacks.Blowup.reesSituationBaseChange_id (reesChartIdeal N hN P) _)

/-- **The symmetry comparison carries the target projection to the source projection.** -/
theorem reesProjSym_comp_reesProjTarget :
    reesProjSym N hN P hcR ≫ reesProjTarget N hN P hcU hcR =
      reesProjSource N hN P hcU hcR := by
  have := flat_toScheme_map_presentation_target P
  have := flat_toScheme_map_presentation_source P
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [CategoryTheory.Functor.map_comp]
  exact reesSituationBaseChange_comp_eq _ _ _ (reesChartIdeal N hN P)
    (comap_reesChartIdeal_target N hN P) (comap_reesRelationIdeal_sym N hN P)
    (toScheme_map_presentationSym_comp_target P) (comap_reesChartIdeal_source N hN P)

/-- **The symmetry comparison carries the source projection to the target projection.** -/
theorem reesProjSym_comp_reesProjSource :
    reesProjSym N hN P hcR ≫ reesProjSource N hN P hcU hcR =
      reesProjTarget N hN P hcU hcR := by
  have := flat_toScheme_map_presentation_target P
  have := flat_toScheme_map_presentation_source P
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [CategoryTheory.Functor.map_comp]
  exact reesSituationBaseChange_comp_eq _ _ _ (reesChartIdeal N hN P)
    (comap_reesChartIdeal_source N hN P) (comap_reesRelationIdeal_sym N hN P)
    (toScheme_map_presentationSym_comp_source P) (comap_reesChartIdeal_target N hN P)

/-- **The reflexivity equation.** The canonical reflexivity candidate of the two projections
satisfies its condition against the source projection: the diagonal comparison satisfies both
conditions, and the reflexivity witness of a pulled-back relation is unique. -/
theorem reflexivity_post_reesProj
    (e : EquivalenceRelation ((Over.post B.inclusion).map P.target)
      ((Over.post B.inclusion).map P.source)) :
    Stacks.Descent.reflHom e.toReflexiveRelation
        (isPullback_post_reesProjTarget N hN P hcU hcR) ≫
      (Over.post B.inclusion).map (reesProjSource N hN P hcU hcR) = 𝟙 _ := by
  have hρ₁ : (Over.post B.inclusion).map (reesProjDiag N hN P hcU hcR) ≫
      (Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, reesProjDiag_comp_reesProjTarget,
      CategoryTheory.Functor.map_id]
  have hρ₂ : (Over.post B.inclusion).map (reesProjDiag N hN P hcU hcR) ≫
      (Over.post B.inclusion).map (reesProjSource N hN P hcU hcR) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, reesProjDiag_comp_reesProjSource,
      CategoryTheory.Functor.map_id]
  rw [← Stacks.Descent.eq_reflHom e.toReflexiveRelation
    (isPullback_post_reesProjTarget N hN P hcU hcR)
    (isPullback_post_reesProjSource N hN P hcU hcR) hρ₁ hρ₂]
  exact hρ₂

/-- **The symmetry equation.** The canonical symmetry candidate of the two projections satisfies
its condition against the source projection: the symmetry comparison satisfies both conditions,
and the symmetry witness of a pulled-back relation is unique. -/
theorem symmetry_post_reesProj
    (e : EquivalenceRelation ((Over.post B.inclusion).map P.target)
      ((Over.post B.inclusion).map P.source)) :
    Stacks.Descent.symHom e.toSymmetricRelation
        (isPullback_post_reesProjTarget N hN P hcU hcR)
        (isPullback_post_reesProjSource N hN P hcU hcR) ≫
      (Over.post B.inclusion).map (reesProjSource N hN P hcU hcR) =
    (Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR) := by
  have hσ₁ : (Over.post B.inclusion).map (reesProjSym N hN P hcR) ≫
      (Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR) =
      (Over.post B.inclusion).map (reesProjSource N hN P hcU hcR) := by
    rw [← CategoryTheory.Functor.map_comp, reesProjSym_comp_reesProjTarget]
  have hσ₂ : (Over.post B.inclusion).map (reesProjSym N hN P hcR) ≫
      (Over.post B.inclusion).map (reesProjSource N hN P hcU hcR) =
      (Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR) := by
    rw [← CategoryTheory.Functor.map_comp, reesProjSym_comp_reesProjSource]
  rw [← Stacks.Descent.eq_symHom e.toSymmetricRelation
    (isPullback_post_reesProjTarget N hN P hcU hcR)
    (isPullback_post_reesProjSource N hN P hcU hcR) hσ₁ hσ₂]
  exact hσ₂

end AlgebraicGeometry.Space

end
