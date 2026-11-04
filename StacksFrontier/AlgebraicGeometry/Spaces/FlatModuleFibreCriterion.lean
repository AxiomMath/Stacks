module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FibrewisePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreFlatnessGeometricPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleLocusOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.FinitePresentation

/-!
# Critère de platitude par fibres for algebraic spaces

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S`, let `F` be
an `𝒪_X`-module and let `x̄` be a geometric point of `X` with images `ȳ` in `Y` and `z̄` in `Z`.
Assume `X` is locally of finite presentation over `Z`, that `F` is of finite presentation and
that `Y` is locally of finite type over `Z`. If `F_{x̄} ≠ 0` then the two conditions of
Stacks 05X0 are equivalent:

1. `F` is flat over `Z` at `x̄`, and the restriction of `F` to its fibre over `z̄` is flat at
   `x̄` over the fibre of `Y` over `z̄`;
2. `Y` is flat over `Z` at `ȳ`, and `F` is flat over `Y` at `x̄`.

Moreover the set of points of `|X|` where they hold is the intersection of the support of `F`
with an open subset of `|X|`.

## Main results

* `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_and_isFibreFlat_iff`: **Stacks 05X0**, the
  equivalence of the two conditions at a geometric point.
* `AlgebraicGeometry.Space.setOf_isFlatOverAtGeometricPoint_and_isFibreFlat_eq`: the locus of
  points of `|X|` at which both conditions hold is the intersection of the support of `F` with
  the relative flat loci of `f` and of `f ≫ g`, and
  `AlgebraicGeometry.Space.isOpen_flatLocus_inter_flatLocus`: that intersection is open.  These
  two together are the openness assertion of Stacks 05X0.

## Implementation notes

Condition (1) of the source refers to the fibre condition of Stacks 05WY, and that is what is
used here: `AlgebraicGeometry.Space.IsFibreFlatOverAtGeometricPoint`, read on the étale local
rings as part (1) of that lemma reads it.  Likewise flatness of `F` over `Z` and over `Y` at a
geometric point is condition (2) of Stacks 05VU
(`AlgebraicGeometry.Space.IsFlatOverAtGeometricPoint`) and flatness of `Y` over `Z` at `ȳ` is
`AlgebraicGeometry.Space.IsFlatAt` at the image point of `ȳ`, which is condition (1) of
Stacks 04NG by `AlgebraicGeometry.Space.isFlatAt_iff_etaleLocalRingMap_flat`.

The Noetherian form of the same comparison is Stacks 0APR, already available as
`AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_and_isFlatOnFibre_iff`; it is proved over
the étale local rings, because Stacks 00MP needs only that the three rings be Noetherian local
and the étale local rings of a locally Noetherian space are Noetherian.  That route is **not**
available here: the local form of the non-Noetherian criterion (Stacks 05UV, available as
`Stacks.Flatness.flat_and_flat_quotient_smul_top_iff`) needs the ring map
`𝒪_{Z, z̄} → 𝒪_{Y, ȳ}` to be essentially of finite type, which a map of strict henselizations is
not.  So the forward implication is proved where the source proves it, on a pair of composable
commuting squares of étale scheme charts `U ⟶ V ⟶ W`, whose stalk maps are the stalk maps of
morphisms of schemes locally of finite type respectively locally of finite presentation.  Such a
pair, carrying the fibre condition, is exactly what Stacks 05WY produces
(`AlgebraicGeometry.Space.exists_flatQuotSMul_chart_iff_isFibreFlatOverAtGeometricPoint`).

Only flatness of `F` over `Y` at `x̄` is read off the charts; flatness of `Y` over `Z` at `ȳ`,
the other half of condition (2), is then part (2) of Stacks 05VX
(`AlgebraicGeometry.Space.isFlatAt_of_nontrivial_fibre_of_isFlatOverAtGeometricPoint`), whose
nonvanishing hypothesis is Nakayama's lemma for the geometric stalk.  Finiteness of the
geometric stalk over `𝒪_{X, x̄}` — which Stacks 0APR has to hypothesise, the chartwise
comparison being unavailable there — is here a consequence of finite presentation on charts,
since the geometric stalk is the base change of the chart's Zariski stalk along
`𝒪_{U, u} → 𝒪_{X, x̄}` by Stacks 05VP.

The converse implication needs no finiteness and is proved over the étale local rings, as in
Stacks 0APR: part (1) of Stacks 05VX for the first conjunct and base change along
`𝒪_{Y, ȳ} → 𝒪_{Y, ȳ}/𝔪_{z̄}𝒪_{Y, ȳ}` for the second.

The fibre of a module over a tower `A → C` of rings is written by Stacks 05WY as the quotient
by the ideal generated in `C`, and by Stacks 05UV as the quotient by the ideal of `A`; the two
are the same subgroup, and `Stacks.Flatness.flatQuotSMul_iff_flat_quotient_smul_top` identifies
the two readings of flatness of the fibre.

For the openness assertion the locus is described, as in the source, through the two relative
flat loci: a point of the support at which both conditions hold lies in the flat locus of `f`
and in that of `f ≫ g`, and conversely at a point of the support lying in both loci condition
(1) holds — the fibre condition being a base change of flatness over `Y` — hence so does
condition (2) by the equivalence.  Both loci are open by Stacks 05WV, the second because
`f ≫ g` is locally of finite presentation and the first because `f` is, being locally of finite
presentation after Stacks 05WT cancels the finite type hypothesis on `g`.

## References

* [Stacks Project, Tag 05X0](https://stacks.math.columbia.edu/tag/05X0)
* [Stacks Project, Tag 05WZ](https://stacks.math.columbia.edu/tag/05WZ)
* [Stacks Project, Tag 05WY](https://stacks.math.columbia.edu/tag/05WY)
* [Stacks Project, Tag 05VX](https://stacks.math.columbia.edu/tag/05VX)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 05WV](https://stacks.math.columbia.edu/tag/05WV)
* [Stacks Project, Tag 05UV](https://stacks.math.columbia.edu/tag/05UV)
* [Stacks Project, Tag 039C](https://stacks.math.columbia.edu/tag/039C)
* [Stacks Project, Tag 0APR](https://stacks.math.columbia.edu/tag/0APR)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace Stacks.Flatness

/-- **The fibre of a module read over either ring of a tower.** For commutative rings `A → C`,
an ideal `I` of `A` and a `C`-module `M`, the subgroup `I M` computed over `A` is the subgroup
`(I C) M` computed over `C`, so flatness of the fibre of `M` over `A ⧸ I` is the same condition
whichever of the two ideals is used to form it.

Stacks 05WY states the fibre condition with the ideal of `C`, Stacks 05UV with the ideal of
`A`. -/
theorem flatQuotSMul_iff_flat_quotient_smul_top {A C M : Type*} [CommRing A] [CommRing C]
    [Algebra A C] [AddCommGroup M] [Module A M] [Module C M] [IsScalarTower A C M]
    (I : Ideal A) (J : Ideal C) (hJ : J = I.map (algebraMap A C)) :
    Module.FlatQuotSMul (algebraMap A C) I J hJ M ↔
      Module.Flat (A ⧸ I) (M ⧸ (I • (⊤ : Submodule A M))) := by
  subst hJ
  have hsub : ((I.map (algebraMap A C)) • (⊤ : Submodule C M)).restrictScalars A
      = I • (⊤ : Submodule A M) := by
    rw [Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]
  let : Module (A ⧸ I) (M ⧸ ((I.map (algebraMap A C)) • (⊤ : Submodule C M))) :=
    Module.compHom _ (Ideal.quotientMap (I.map (algebraMap A C)) (algebraMap A C)
      Ideal.le_comap_map)
  let e0 := Submodule.quotEquivOfEq
    (((I.map (algebraMap A C)) • (⊤ : Submodule C M)).restrictScalars A)
    (I • (⊤ : Submodule A M)) hsub
  refine Module.Flat.equiv_iff (R := A ⧸ I)
    { toFun := fun z => e0 z
      map_add' := fun z w => map_add e0 z w
      map_smul' := ?_
      invFun := fun z => e0.symm z
      left_inv := e0.left_inv
      right_inv := e0.right_inv }
  intro r z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  induction z using Submodule.Quotient.induction_on with
  | H m =>
    have hl : (Ideal.Quotient.mk I a) •
        (Submodule.Quotient.mk (p := (I.map (algebraMap A C)) • (⊤ : Submodule C M)) m) =
        Submodule.Quotient.mk (p := (I.map (algebraMap A C)) • (⊤ : Submodule C M))
          (algebraMap A C a • m) := rfl
    rw [hl]
    show e0 (Submodule.Quotient.mk (p := ((I.map (algebraMap A C)) •
      (⊤ : Submodule C M)).restrictScalars A) (algebraMap A C a • m)) = _
    rw [Submodule.quotEquivOfEq_mk, algebraMap_smul]
    exact (Module.Quotient.mk_smul_mk M I a m).symm

/-- **Nakayama's lemma** (Stacks 00DV, part (2)) in the form used below: a finite nonzero module
over a local ring is not equal to its maximal ideal times itself. -/
theorem maximalIdeal_smul_top_ne_top_of_finite (A : Type*) (N : Type*) [CommRing A]
    [IsLocalRing A] [AddCommGroup N] [Module A N] [Module.Finite A N] [Nontrivial N] :
    IsLocalRing.maximalIdeal A • (⊤ : Submodule A N) ≠ ⊤ := fun h =>
  top_ne_bot (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ ⊤ Module.Finite.fg_top h.ge
    (IsLocalRing.maximalIdeal_le_jacobson _))

/-- **The implication (1) ⇒ (2) of Stacks 039C over a tower of local rings**, in the spelling
in which a pair of composable commuting squares of étale charts delivers the fibre condition:
the fibre is the quotient by the ideal generated in the last ring of the tower. -/
theorem flat_base_and_flat_of_flatQuotSMul {R A C M : Type*} [CommRing R] [CommRing A]
    [CommRing C] [IsLocalRing R] [IsLocalRing A] [IsLocalRing C]
    [Algebra R A] [Algebra A C] [Algebra R C] [IsScalarTower R A C]
    [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap A C)]
    [AddCommGroup M] [Module R M] [Module A M] [Module C M]
    [IsScalarTower R A M] [IsScalarTower A C M]
    [Algebra.EssFiniteType R A] [Module.FinitePresentation C M] [Nontrivial M]
    (hRC : (algebraMap R C).EssentiallyOfFinitePresentation)
    (hflat : Module.Flat R M)
    (hfibre : Module.FlatQuotSMul (algebraMap A C)
      ((maximalIdeal R).map (algebraMap R A))
      (((maximalIdeal R).map (algebraMap R A)).map (algebraMap A C)) rfl M) :
    Module.Flat R A ∧ Module.Flat A M :=
  (flat_and_flat_quotient_smul_top_iff hRC).1
    ⟨hflat, (flatQuotSMul_iff_flat_quotient_smul_top _ _ rfl).1 hfibre⟩

end Stacks.Flatness

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Finiteness of the geometric stalk from finite presentation on charts -/

/-- The Zariski stalk of the restriction of a module of finite presentation on charts to a
scheme chart is a finitely presented module over the local ring of the chart.

The Zariski stalk of Stacks 05VP is the ordinary stalk of the chart restriction
(`AlgebraicGeometry.Space.chartZariskiModuleStalkStalkEquiv`), and the stalk of a finitely
presented module on a scheme is finitely presented. -/
theorem finitePresentation_chartZariskiModuleStalk {X : AlgebraicSpaces B S hS}
    {xbar : GeometricPoint B S hS X.1} (N : SmallEtaleNeighborhood xbar)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (hfp : IsFinitePresentationOnCharts B S hS X.2 F) :
    Module.FinitePresentation (chartLocalRing B S hS X.1 N)
      (chartZariskiModuleStalk B S hS X.1 X.2 N F) := by
  have _ := hfp N.chart
  -- the repository carries a second module structure on the stalk, which instance search
  -- prefers in this import closure; Mathlib's is the one the comparison is stated over
  let : Module (chartLocalRing B S hS X.1 N)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (chartRestrictionPresheafOfModules B S hS X.2 N F).presheaf
        (chartPoint B S hS X.1 N)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (chartRestrictionPresheafOfModules B S hS X.2 N F) (chartPoint B S hS X.1 N)
  have h := Stacks.StalkFiniteType.finitePresentation_stalk
    (restrictToChart B S hS X.2 F N.chart) (chartPoint B S hS X.1 N)
  exact (LinearEquiv.finitePresentation_iff
    (chartZariskiModuleStalkStalkEquiv B S hS X.2 N F)).2 h

/-- The geometric stalk of a module of finite presentation on charts is a finite module over the
étale local ring.

By Stacks 05VP the geometric stalk is the base change of the chart's Zariski stalk along
`𝒪_{U, u} → 𝒪_{X, x̄}`, and the Zariski stalk is finitely presented, hence finite. -/
theorem finite_geometricModuleStalk {X : AlgebraicSpaces B S hS}
    {xbar : GeometricPoint B S hS X.1} (N : SmallEtaleNeighborhood xbar)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (hfp : IsFinitePresentationOnCharts B S hS X.2 F) :
    Module.Finite (etaleLocalRing B S hS X.1 xbar)
      (geometricModuleStalk B S hS X xbar F) := by
  let : Algebra (chartLocalRing B S hS X.1 N) (etaleLocalRing B S hS X.1 xbar) :=
    (chartLocalRingToEtaleLocalRing B S hS X.1 X.2 N).toAlgebra
  have _ := finitePresentation_chartZariskiModuleStalk B S hS N F hfp
  have hbc : Module.Finite (etaleLocalRing B S hS X.1 xbar)
      (chartStalkTensorEtaleLocalRing.{u, u} B S hS X.1 X.2 N F) :=
    Module.Finite.base_change _ _ _
  have hiso := isIso_chartStalkTensorComparison B S hS X.2 N F
  exact Module.Finite.equiv (@asIso _ _ _ _ _ hiso).toLinearEquiv

/-! ### The fibre condition from flatness over the intermediate space -/

/-- **The fibre condition of Stacks 05WY holds wherever the module is flat over the intermediate
space.** For `f : X ⟶ Y`, `g : Y ⟶ Z` and a geometric point `x̄` of `X`, if `F` is flat over `Y`
at `x̄` then the restriction of `F` to its fibre over `z̄` is flat at `x̄` over the fibre of `Y`
over `z̄`.

The fibre `F_{x̄}/𝔪_{z̄}F_{x̄}` is the base change of the flat module `F_{x̄}` along
`𝒪_{Y, ȳ} → 𝒪_{Y, ȳ}/𝔪_{z̄}𝒪_{Y, ȳ}`, so this is Stacks 00HI.  No finiteness is used. -/
theorem isFibreFlatOverAtGeometricPoint_of_isFlatOverAtGeometricPoint
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) (xbar : GeometricPoint B S hS X.1)
    (hFflat : IsFlatOverAtGeometricPoint B S hS f F xbar) :
    IsFibreFlatOverAtGeometricPoint B S hS f g F xbar := by
  let : IsLocalRing (etaleLocalRing B S hS Z.1
      (geometricPointMap g.hom (geometricPointMap f.hom xbar))) :=
    isLocalRing_etaleLocalRing B S hS Z.1 Z.2 _
  let : Algebra (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
      (etaleLocalRing B S hS X.1 xbar) :=
    (etaleLocalRingMap X.2 f.hom xbar).toAlgebra
  let : Module (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
      (geometricModuleStalk B S hS X xbar F) :=
    Module.compHom _ (etaleLocalRingMap X.2 f.hom xbar)
  have : IsScalarTower (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
      (etaleLocalRing B S hS X.1 xbar) (geometricModuleStalk B S hS X xbar F) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat (etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
      (geometricModuleStalk B S hS X xbar F) := hFflat
  refine (Stacks.Flatness.flatQuotSMul_iff_flat_quotient_smul_top
    ((maximalIdeal (etaleLocalRing B S hS Z.1
      (geometricPointMap g.hom (geometricPointMap f.hom xbar)))).map
        (etaleLocalRingMap Y.2 g.hom (geometricPointMap f.hom xbar)))
    ((maximalIdeal (etaleLocalRing B S hS Z.1
      (geometricPointMap g.hom (geometricPointMap f.hom xbar)))).map
        ((etaleLocalRingMap X.2 f.hom xbar).comp
          (etaleLocalRingMap Y.2 g.hom (geometricPointMap f.hom xbar))))
    (Ideal.map_map _ _).symm).2 ?_
  exact Stacks.Flatness.flat_quotient_smul_top_of_flat _

/-- Flatness of the Zariski stalk over a chart of the target is flatness at the geometric point,
for scalars restricted along `φ` compatible with the maps to the étale local rings. -/
private theorem flat_chartZariskiModuleStalk_iff_isFlatOverAtGeometricPoint
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] {xbar : GeometricPoint B S hS X.1} (N : SmallEtaleNeighborhood xbar)
    (V : SmallEtaleNeighborhood (geometricPointMap f.hom xbar))
    (φ : chartLocalRing B S hS Y.1 V →+* chartLocalRing B S hS X.1 N)
    (hφ : (chartLocalRingToEtaleLocalRing B S hS X.1 X.2 N).comp φ =
      (etaleLocalRingMap X.2 f.hom xbar).comp
        (chartLocalRingToEtaleLocalRing B S hS Y.1 Y.2 V)) :
    letI : Module (chartLocalRing B S hS Y.1 V) (chartZariskiModuleStalk B S hS X.1 X.2 N F) :=
      Module.compHom _ φ
    Module.Flat (chartLocalRing B S hS Y.1 V) (chartZariskiModuleStalk B S hS X.1 X.2 N F) ↔
      IsFlatOverAtGeometricPoint B S hS f F xbar :=
  (flat_chartZariskiModuleStalk_iff_flat_geometricModuleStalk B S hS f N V F φ _ hφ).trans
    (flat_chartLocalRing_geometricModuleStalk_iff B S hS f F xbar V)

/-! ### Stacks 05X0 -/

/-- **Stacks 05X0.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a
scheme `S`, let `F` be an `𝒪_X`-module which is quasi-coherent on the small étale site and of
finite presentation on charts, and let `x̄` be a geometric point of `X` with images `ȳ` and `z̄`.
Assume `X` is locally of finite presentation over `Z` and `Y` is locally of finite type over
`Z`, and assume `F_{x̄} ≠ 0`.  Then

1. `F` is flat over `Z` at `x̄` and the restriction of `F` to its fibre over `z̄` is flat at `x̄`
   over the fibre of `Y` over `z̄`

holds exactly when

2. `Y` is flat over `Z` at `ȳ` and `F` is flat over `Y` at `x̄`

holds.  The fibre condition of (1) is the one of Stacks 05WY, as the source's definition
(Stacks 05WZ) prescribes. -/
@[stacks 05X0 "the equivalence of (1) and (2) at a geometric point `x̄`: flatness over `Z` and \
over `Y` at `x̄` are condition (2) of Stacks 05VU, the fibre condition of (1) is the one of \
Stacks 05WY named by the source's definition 05WZ, and flatness of `Y` over `Z` at `ȳ` is \
Space.IsFlatAt at its image point. Hypothesis (2) of the source is read on the Zariski site of \
every etale chart; the openness assertion is isOpen_setOf_... below."]
theorem isFlatOverAtGeometricPoint_and_isFibreFlat_iff {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (hp : IsLocallyOfFinitePresentation B S hS (f ≫ g).hom)
    (hq : IsLocallyOfFiniteType B S hS g.hom)
    (hfp : IsFinitePresentationOnCharts B S hS X.2 F)
    (xbar : GeometricPoint B S hS X.1)
    (hne : Nontrivial (geometricModuleStalk B S hS X xbar F)) :
    (IsFlatOverAtGeometricPoint B S hS (f ≫ g) F xbar ∧
        IsFibreFlatOverAtGeometricPoint B S hS f g F xbar) ↔
      (IsFlatAt B S hS g.hom (geometricPointMap f.hom xbar).image ∧
        IsFlatOverAtGeometricPoint B S hS f F xbar) := by
  classical
  constructor
  · rintro ⟨hbase, hfibre⟩
    -- The forward implication, on a pair of composable commuting squares of étale charts.
    obtain ⟨N, Vc, g₁, hcomm₁, Wc, g₂, hcomm₂, hchart⟩ :=
      (exists_flatQuotSMul_chart_iff_isFibreFlatOverAtGeometricPoint B S hS f g F xbar).2 hfibre
    have hfY : IsFlatOverAtGeometricPoint B S hS f F xbar := by
      -- the two commuting squares of local rings, named before the abbreviations are set
      have hsq₁ := etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing
        B S hS f xbar N Vc g₁ hcomm₁
      have hsq₂ := etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing
        B S hS g (geometricPointMap f.hom xbar) (targetNeighborhood B S hS N Vc g₁ hcomm₁)
        Wc g₂ hcomm₂
      have hcomp := etaleLocalRingMap_comp X.2 Y.2 f.hom g.hom xbar
      set Vn := targetNeighborhood B S hS N Vc g₁ hcomm₁ with hVn
      set Wn := targetNeighborhood B S hS Vn Wc g₂ hcomm₂ with hWn
      set φ₁ : chartLocalRing B S hS Y.1 Vn →+* chartLocalRing B S hS X.1 N :=
        (((BigFppfOver.toScheme B S hS).map g₁).stalkMap (chartPoint B S hS X.1 N)).hom with hφ₁
      set φ₂ : chartLocalRing B S hS Z.1 Wn →+* chartLocalRing B S hS Y.1 Vn :=
        (((BigFppfOver.toScheme B S hS).map g₂).stalkMap
          (chartPoint B S hS Y.1 Vn)).hom with hφ₂
      -- the three local rings of the charts, with the two stalk maps
      let : Algebra (chartLocalRing B S hS Y.1 Vn) (chartLocalRing B S hS X.1 N) :=
        φ₁.toAlgebra
      let : Algebra (chartLocalRing B S hS Z.1 Wn) (chartLocalRing B S hS Y.1 Vn) :=
        φ₂.toAlgebra
      let : Algebra (chartLocalRing B S hS Z.1 Wn) (chartLocalRing B S hS X.1 N) :=
        (φ₁.comp φ₂).toAlgebra
      have : IsScalarTower (chartLocalRing B S hS Z.1 Wn) (chartLocalRing B S hS Y.1 Vn)
          (chartLocalRing B S hS X.1 N) := IsScalarTower.of_algebraMap_eq fun _ => rfl
      have : IsLocalHom (algebraMap (chartLocalRing B S hS Z.1 Wn)
          (chartLocalRing B S hS Y.1 Vn)) :=
        ((BigFppfOver.toScheme B S hS).map g₂).prop (chartPoint B S hS Y.1 Vn)
      have : IsLocalHom (algebraMap (chartLocalRing B S hS Y.1 Vn)
          (chartLocalRing B S hS X.1 N)) :=
        ((BigFppfOver.toScheme B S hS).map g₁).prop (chartPoint B S hS X.1 N)
      -- the module structures on the Zariski stalk of the chart restriction
      let : Module (chartLocalRing B S hS Y.1 Vn)
          (chartZariskiModuleStalk B S hS X.1 X.2 N F) := Module.compHom _ φ₁
      let : Module (chartLocalRing B S hS Z.1 Wn)
          (chartZariskiModuleStalk B S hS X.1 X.2 N F) := Module.compHom _ (φ₁.comp φ₂)
      have : IsScalarTower (chartLocalRing B S hS Y.1 Vn) (chartLocalRing B S hS X.1 N)
          (chartZariskiModuleStalk B S hS X.1 X.2 N F) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      have : IsScalarTower (chartLocalRing B S hS Z.1 Wn) (chartLocalRing B S hS Y.1 Vn)
          (chartZariskiModuleStalk B S hS X.1 X.2 N F) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      -- the commuting square of the composite
      have hcomm : N.chart.obj.hom ≫ (f ≫ g).hom
          = yoneda.map (g₁ ≫ g₂) ≫ Wc.obj.hom :=
        (Category.assoc _ _ _).symm.trans <| by
          rw [hcomm₁, Category.assoc, hcomm₂, Functor.map_comp, Category.assoc]
      -- the finiteness hypotheses, read on the charts
      have hft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g₂) :=
        hq Vc.obj.left Wc.obj.left Vc.obj.hom Wc.obj.hom g₂ Vc.property Wc.property hcomm₂.symm
      have hfpc : LocallyOfFinitePresentation
          ((BigFppfOver.toScheme B S hS).map g₁ ≫ (BigFppfOver.toScheme B S hS).map g₂) := by
        rw [← Functor.map_comp]
        exact hp N.chart.obj.left Wc.obj.left N.chart.obj.hom Wc.obj.hom (g₁ ≫ g₂)
          N.chart.property Wc.property hcomm.symm
      have : Algebra.EssFiniteType (chartLocalRing B S hS Z.1 Wn)
          (chartLocalRing B S hS Y.1 Vn) := by
        rw [← RingHom.essFiniteType_algebraMap]
        exact LocallyOfFiniteType.stalkMap ((BigFppfOver.toScheme B S hS).map g₂)
          (chartPoint B S hS Y.1 Vn)
      have hRC : (algebraMap (chartLocalRing B S hS Z.1 Wn)
          (chartLocalRing B S hS X.1 N)).EssentiallyOfFinitePresentation := by
        have h := LocallyOfFinitePresentation.essentiallyOfFinitePresentation_stalkMap
          ((BigFppfOver.toScheme B S hS).map g₁ ≫ (BigFppfOver.toScheme B S hS).map g₂)
          (chartPoint B S hS X.1 N)
        rwa [Scheme.Hom.stalkMap_comp] at h
      have : Module.FinitePresentation (chartLocalRing B S hS X.1 N)
          (chartZariskiModuleStalk B S hS X.1 X.2 N F) :=
        finitePresentation_chartZariskiModuleStalk B S hS N F hfp
      have : Nontrivial (chartZariskiModuleStalk.{u, u} B S hS X.1 X.2 N F) :=
        (nontrivial_chartZariskiModuleStalk_iff_mem_supp B S hS X.1 X.2 N F).2
          ((nontrivial_geometricModuleStalk_iff_mem_supp_restrictToChart B S hS X N F).1 hne)
      -- flatness of the Zariski stalk over the chart of `Z`, from condition (1)
      have hbaseChart : Module.Flat (chartLocalRing B S hS Z.1 Wn)
          (chartZariskiModuleStalk B S hS X.1 X.2 N F) := by
        refine (flat_chartZariskiModuleStalk_iff_isFlatOverAtGeometricPoint B S hS (f ≫ g) F N
          Wn (φ₁.comp φ₂) (RingHom.ext fun c => ?_)).2 hbase
        have h1 := RingHom.congr_fun hsq₁ (φ₂ c)
        have h2 := RingHom.congr_fun hsq₂ c
        have h3 := RingHom.congr_fun hcomp
          (chartLocalRingToEtaleLocalRing B S hS Z.1 Z.2 Wn c)
        exact h1.trans ((congrArg (etaleLocalRingMap X.2 f.hom xbar) h2).trans h3)
      -- the local criterion on the charts
      have hout := Stacks.Flatness.flat_base_and_flat_of_flatQuotSMul
        (R := chartLocalRing B S hS Z.1 Wn) (A := chartLocalRing B S hS Y.1 Vn)
        (C := chartLocalRing B S hS X.1 N)
        (M := chartZariskiModuleStalk B S hS X.1 X.2 N F) hRC hbaseChart hchart
      -- transport flatness over the chart of `Y` back to the geometric point
      exact (flat_chartZariskiModuleStalk_iff_isFlatOverAtGeometricPoint B S hS f F N Vn φ₁
        hsq₁).1 hout.2
    refine ⟨?_, hfY⟩
    -- flatness of `Y` over `Z` at `ȳ` is part (2) of Stacks 05VX
    refine isFlatAt_of_nontrivial_fibre_of_isFlatOverAtGeometricPoint B S hS f g F xbar hfY
      ?_ hbase
    have : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
      isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
    have : Module.Finite (etaleLocalRing B S hS X.1 xbar)
        (geometricModuleStalk B S hS X xbar F) :=
      finite_geometricModuleStalk B S hS N F hfp
    have := hne
    exact not_subsingleton_iff_nontrivial.1 fun hsub =>
      Stacks.Flatness.maximalIdeal_smul_top_ne_top_of_finite
        (etaleLocalRing B S hS X.1 xbar) (geometricModuleStalk B S hS X xbar F)
        (Submodule.Quotient.subsingleton_iff.1 hsub)
  · rintro ⟨hgflat, hFflat⟩
    exact ⟨isFlatOverAtGeometricPoint_comp B S hS f g F xbar hFflat hgflat,
      isFibreFlatOverAtGeometricPoint_of_isFlatOverAtGeometricPoint B S hS f g F xbar hFflat⟩

/-! ### The openness assertion of Stacks 05X0 -/

section Openness

attribute [local instance] pointTopology

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **Both relative flat loci are open.** For `f : X ⟶ Y` and `g : Y ⟶ Z` with `f ≫ g` locally
of finite presentation and `g` locally of finite type, and an `𝒪_X`-module quasi-coherent of
finite presentation on charts, the set of points of `|X|` at which the module is flat both over
`Z` and over `Y` is open.

Both halves are Stacks 05WV: for `f ≫ g` directly, and for `f` after Stacks 05WT makes `f`
locally of finite presentation. -/
@[ega "IV 11.3.1" "more general"]
theorem isOpen_flatLocus_inter_flatLocus (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (hp : IsLocallyOfFinitePresentation B S hS (f ≫ g).hom)
    (hq : IsLocallyOfFiniteType B S hS g.hom)
    (hqc : IsQuasicoherentOnCharts B S hS X.2 F)
    (hfp : IsFinitePresentationOnCharts B S hS X.2 F) :
    IsOpen (flatLocus B S hS X.2 (f ≫ g).hom F ∩ flatLocus B S hS X.2 f.hom F) :=
  IsOpen.inter
    (isOpen_flatLocus_of_isFinitePresentationOnCharts B S hS X.2 (f ≫ g).hom F hp hqc hfp)
    (isOpen_flatLocus_of_isFinitePresentationOnCharts B S hS X.2 f.hom F
      (isLocallyOfFinitePresentation_of_comp B S hS X.2 Y.2 Z.2 f.hom g.hom hp hq) hqc hfp)

/-- **Stacks 05X0, the openness assertion.** Under the hypotheses of Stacks 05X0, the set of
points of `|X|` lying in the support of `F` at which conditions (1) and (2) hold at every
geometric point above them is the intersection of that support with the open set
`AlgebraicGeometry.Space.isOpen_flatLocus_inter_flatLocus` is about, namely the locus where `F`
is flat both over `Z` and over `Y`.  So that set is open in the support of `F`.

A point of the support at which (1) and (2) hold lies in both flat loci by (1) and (2); and at a
point of the support lying in both loci condition (1) holds, the fibre condition being a base
change of flatness over `Y`, hence so does condition (2) by the equivalence. -/
@[stacks 05X0 "the openness assertion: the locus where (1) and (2) hold is the support of the \
module intersected with the locus where the module is flat over both `Z` and `Y`, which is \
open by Space.isOpen_flatLocus_inter_flatLocus. Conditions (1) and (2) are read at every \
geometric point above the point of `|X|`, which is no restriction: by Stacks 05VU the \
conditions do not depend on the geometric point chosen above it."]
theorem setOf_isFlatOverAtGeometricPoint_and_isFibreFlat_eq (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (hp : IsLocallyOfFinitePresentation B S hS (f ≫ g).hom)
    (hq : IsLocallyOfFiniteType B S hS g.hom)
    (hfp : IsFinitePresentationOnCharts B S hS X.2 F) :
    {x : points B S hS X.1 |
        x ∈ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) ∧
        ∀ xbar : GeometricPoint B S hS X.1, xbar.image = x →
          (IsFlatOverAtGeometricPoint B S hS (f ≫ g) F xbar ∧
              IsFibreFlatOverAtGeometricPoint B S hS f g F xbar) ∧
            (IsFlatAt B S hS g.hom (geometricPointMap f.hom xbar).image ∧
              IsFlatOverAtGeometricPoint B S hS f F xbar)} =
      (flatLocus B S hS X.2 (f ≫ g).hom F ∩ flatLocus B S hS X.2 f.hom F) ∩
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) := by
  refine Set.ext fun x => ⟨?_, ?_⟩
  · rintro ⟨hsupp, hcond⟩
    obtain ⟨xbar, rfl⟩ := exists_geometricRepresentative B S hS X.1 x
    obtain ⟨⟨hbase, -⟩, -, hfY⟩ := hcond xbar rfl
    exact ⟨⟨(mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS (f ≫ g) F xbar).2 hbase,
      (mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS f F xbar).2 hfY⟩, hsupp⟩
  · rintro ⟨⟨h1, h2⟩, hsupp⟩
    refine ⟨hsupp, fun xbar hxbar => ?_⟩
    subst hxbar
    have hbase := (mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS (f ≫ g) F xbar).1 h1
    have hfY := (mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS f F xbar).1 h2
    have hne := (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk_of_liesOver
      B S hS X F xbar xbar.image rfl).1 hsupp
    have hone : IsFlatOverAtGeometricPoint B S hS (f ≫ g) F xbar ∧
        IsFibreFlatOverAtGeometricPoint B S hS f g F xbar :=
      ⟨hbase, isFibreFlatOverAtGeometricPoint_of_isFlatOverAtGeometricPoint
        B S hS f g F xbar hfY⟩
    exact ⟨hone, (isFlatOverAtGeometricPoint_and_isFibreFlat_iff
      B S hS f g F hp hq hfp xbar hne).1 hone⟩

/-- **Stacks 05X0, the openness assertion in the subspace of the support.** Under the hypotheses
of Stacks 05X0 the set of points of the support of `F` at which conditions (1) and (2) hold is
open in the support.

This is `AlgebraicGeometry.Space.setOf_isFlatOverAtGeometricPoint_and_isFibreFlat_eq` read in
the subspace topology: the set is the inverse image in the support of the open set of
`AlgebraicGeometry.Space.isOpen_flatLocus_inter_flatLocus`. -/
@[stacks 05X0 "the openness assertion, read in the subspace topology of the support: the locus \
where (1) and (2) hold is open in Supp(F). Conditions (1) and (2) are read at every geometric \
point above the point of `|X|`, which by Stacks 05VU does not depend on the geometric point \
chosen. Finite presentation of the module is read on the Zariski site of every etale scheme \
chart."]
theorem isOpen_setOf_isFlatOverAtGeometricPoint_and_isFibreFlat (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (hp : IsLocallyOfFinitePresentation B S hS (f ≫ g).hom)
    (hq : IsLocallyOfFiniteType B S hS g.hom)
    (hfp : IsFinitePresentationOnCharts B S hS X.2 F) :
    IsOpen {x : (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) :
        Set (points B S hS X.1)) |
      ∀ xbar : GeometricPoint B S hS X.1, xbar.image = (x : points B S hS X.1) →
        (IsFlatOverAtGeometricPoint B S hS (f ≫ g) F xbar ∧
            IsFibreFlatOverAtGeometricPoint B S hS f g F xbar) ∧
          (IsFlatAt B S hS g.hom (geometricPointMap f.hom xbar).image ∧
            IsFlatOverAtGeometricPoint B S hS f F xbar)} := by
  have hset := setOf_isFlatOverAtGeometricPoint_and_isFibreFlat_eq B S hS f g F hp hq hfp
  have hpre : {x : (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) :
        Set (points B S hS X.1)) |
      ∀ xbar : GeometricPoint B S hS X.1, xbar.image = (x : points B S hS X.1) →
        (IsFlatOverAtGeometricPoint B S hS (f ≫ g) F xbar ∧
            IsFibreFlatOverAtGeometricPoint B S hS f g F xbar) ∧
          (IsFlatAt B S hS g.hom (geometricPointMap f.hom xbar).image ∧
            IsFlatOverAtGeometricPoint B S hS f F xbar)}
      = Subtype.val ⁻¹' (flatLocus B S hS X.2 (f ≫ g).hom F ∩
        flatLocus B S hS X.2 f.hom F) := by
    refine Set.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · exact ((Set.ext_iff.1 hset (x : points B S hS X.1)).1 ⟨x.2, hx⟩).1
    · exact ((Set.ext_iff.1 hset (x : points B S hS X.1)).2 ⟨hx, x.2⟩).2
  rw [hpre]
  exact (isOpen_flatLocus_inter_flatLocus B S hS f g F hp hq
    (fun U => isQuasicoherent_restrictToChart B S hS X F ‹_› U) hfp).preimage
    continuous_subtype_val

end Openness

end AlgebraicGeometry.Space

end
