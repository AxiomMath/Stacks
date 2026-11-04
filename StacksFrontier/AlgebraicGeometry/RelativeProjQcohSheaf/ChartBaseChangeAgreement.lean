module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.SectionIso
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartAgreement
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.SituationRestrict

/-!
# The chart-wise classes of a quadruple and of its base change

Let `g : S' ⟶ S` be a morphism of schemes and `𝒜` a quasi-coherent graded `𝒪_S`-algebra
(Situation 01NN), with inverse image `g^*𝒜` on `S'`.  The base-change morphism
`Proj_{S'}(g^*𝒜) ⟶ Proj_S(𝒜)` of Tag 01O3,
`Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom`, is defined chart by chart:
over affine opens `U' ⊆ g⁻¹U` it is `Proj` of the graded ring map
`Γ(U, 𝒜) ⟶ Γ(U', g^*𝒜)` (`...RelativeProjBaseChangeTwist.chart_baseChangeHom`).

This file compares, on the charts, the morphism into a relative homogeneous spectrum which the
representation of Tag 01NY attaches to a quadruple for `g^*𝒜`, and the one it attaches to the
quadruple for `𝒜` that the base change of Tag 01NT makes of it: on the chart over `U'`, the
first followed by `Proj(Γ(U, 𝒜) ⟶ Γ(U', g^*𝒜))` is the second.  The computational core is that
the Veronese family of the chart-wise class of the base-changed quadruple at `U` is the pullback,
along `Γ(U, 𝒜) ⟶ Γ(U', g^*𝒜)`, of the Veronese family of the chart-wise class of the original
quadruple at `U'` (`...RelativeProjQcohSheaf.veroneseSections_chartTwisting_toFun_baseChange`).

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.veroneseSections_chartTwisting_toFun_baseChange`:
  the comparison of the two Veronese families, degreewise, and
  `...RelativeProjQcohSheaf.heq_comapVeronese_chartTwisting_baseChange`, the same read at the
  gradings of homogeneous sections.
* `...RelativeProjQcohSheaf.Fd.toProj_chartEquiv_chartClass_comp_projMap_baseChange`: the
  comparison of the morphisms into the projective spectra of the section rings.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.chartHom_comp_baseChangeHom`: the chart-wise
  morphism of a class for `g^*𝒜` followed by the base-change morphism of Tag 01O3 is the chart-wise
  morphism of its base change.

## References

* [Stacks Project, Tag 01NT](https://stacks.math.columbia.edu/tag/01NT)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry Stacks.RingedSpace RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.MorphismToProjUniversal
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.ProjTripleClassifying
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

section BaseChange

variable {S S' : Scheme.{u}} (A : SheafGradedAlgebra S) (g : S' ⟶ S)
  {U : S.Opens} {U' : S'.Opens} {k : ℕ} {T : Scheme.{u}}
  (gU : T ⟶ U.toScheme) (gU' : T ⟶ U'.toScheme) {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L]

/-- **The chart-wise Veronese family of a base-changed quadruple.** Let `g_U ≫ U.ι` and
`(g_{U'} ≫ U'.ι) ≫ g` be two factorizations of one morphism `T ⟶ S`, let `χ'` be a twisting for
`g^*𝒜` over `g_{U'} ≫ U'.ι` and `χ_U` a twisting for `𝒜` over `g_U ≫ U.ι` heterogeneously equal to
its base change of Tag 01NT. Then the Veronese family of the chart-wise class of `χ'` at `U'`,
evaluated on the restriction of the pullback of a homogeneous section `a` of `𝒜` over the image of
`U`, is the Veronese family of the chart-wise class of `χ_U` at `U` evaluated on `a`. -/
theorem veroneseSections_chartTwisting_toFun_baseChange
    (hUU : U'.ι ''ᵁ (⊤ : Opens U'.toScheme.toRingedSpace.carrier) ≤
      g ⁻¹ᵁ (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier)))
    (hbase : (gU' ≫ U'.ι) ≫ g = gU ≫ U.ι)
    (χU : Twisting (gU ≫ U.ι) (situationAlgebra A) (k : ℤ) L)
    (χ' : Twisting (gU' ≫ U'.ι) (situationAlgebra (A.pullback g)) (k : ℤ) L)
    (hχ : HEq (χ'.baseChangeUp g (gU' ≫ U'.ι) (situationAlgebra A) (k : ℤ)) χU) (n : ℕ)
    (a : (A.restrict U.ι).grading (⊤ : U.toScheme.Opens) (n * k))
    (b : ((A.pullback g).restrict U'.ι).grading (⊤ : U'.toScheme.Opens) (n * k))
    (hab : (b : ((A.pullback g).restrict U'.ι).sectionRing (⊤ : U'.toScheme.Opens)) (n * k)
      = Scheme.Modules.pullbackSection g (A.piece ((n * k : ℕ) : ℤ))
          (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier))
          (U'.ι ''ᵁ (⊤ : Opens U'.toScheme.toRingedSpace.carrier)) hUU
          ((a : (A.restrict U.ι).sectionRing (⊤ : U.toScheme.Opens)) (n * k))) :
    (veroneseSections (chartTwisting (A.pullback g) U' gU' χ')).toFun n b
      = (veroneseSections (chartTwisting A U gU χU)).toFun n a := by
  set a' := (a : (A.restrict U.ι).sectionRing (⊤ : U.toScheme.Opens)) (n * k) with ha'
  set χb := χ'.baseChangeUp g (gU' ≫ U'.ι) (situationAlgebra A) (k : ℤ) with hχb
  set X := χb.sectionHom (n : ℤ) (op (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier))) a'
    with hX
  set eU' := (homOfLE (top_le_preimage_image_top (V := U') (gV := gU'))).op with heU'
  set eU := (homOfLE (top_le_preimage_image_top (V := U) (gV := gU))).op with heU
  set mU := (opensMap (ringedSpaceHom (gU' ≫ U'.ι))).op.map (homOfLE hUU).op with hmU
  set e₁ := eqToHom (congrArg
    (fun w : T ⟶ S => ((opensMap (ringedSpaceHom w)).op.obj
      (op (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier)))
        : (Opens T.toRingedSpace.carrier)ᵒᵖ)) hbase) with he₁
  -- the `U'`-side value of the transposed map
  have hU'comp : χ'.sectionHom (n : ℤ)
        (op (U'.ι ''ᵁ (⊤ : Opens U'.toScheme.toRingedSpace.carrier)))
        (Scheme.Modules.pullbackSection g (A.piece ((n * k : ℕ) : ℤ))
          (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier))
          (U'.ι ''ᵁ (⊤ : Opens U'.toScheme.toRingedSpace.carrier)) hUU a')
      = ((laurent L).piece (n : ℤ)).val.restrictₛₗ mU X :=
    (Twisting.sectionHom_restrict χ' (n : ℤ) (homOfLE hUU).op
        (Twisting.baseUnit g (situationAlgebra A) ((n : ℤ) * (k : ℤ))
          (op (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier))) a')).trans
      (congrArg (fun z => ((laurent L).piece (n : ℤ)).val.restrictₛₗ mU z)
        (Twisting.baseChangeUp_sectionHom g (gU' ≫ U'.ι) (situationAlgebra A) (k : ℤ) χ'
          (n : ℤ) (op (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier))) a').symm)
  -- the `U`-side value of the transposed map
  have hUcomp : χU.sectionHom (n : ℤ)
        (op (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier))) a'
      = ((laurent L).piece (n : ℤ)).val.restrictₛₗ e₁ X :=
    Twisting.sectionHom_heq hbase χb χU hχ (n : ℤ)
      (op (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier))) a' e₁
  refine Eq.trans (veroneseSections_chartTwisting' (A.pullback g) U' gU' χ' n b eU') ?_
  refine Eq.trans ?_ (veroneseSections_chartTwisting' A U gU χU n a eU).symm
  refine congrArg (fun z => (powCompare L n).inv.app ⊤ z) ?_
  refine Eq.trans (congrArg
    (fun y => ((laurent L).piece (n : ℤ)).val.restrictₛₗ eU'
      (χ'.sectionHom (n : ℤ)
        (op (U'.ι ''ᵁ (⊤ : Opens U'.toScheme.toRingedSpace.carrier))) y)) hab) ?_
  refine Eq.trans (congrArg
    (fun z => ((laurent L).piece (n : ℤ)).val.restrictₛₗ eU' z) hU'comp) ?_
  refine Eq.trans ?_ (congrArg
    (fun z => ((laurent L).piece (n : ℤ)).val.restrictₛₗ eU z) hUcomp).symm
  refine Eq.trans
    (PresheafOfModules.map_comp_apply ((laurent L).piece (n : ℤ)).val mU eU' X).symm ?_
  refine Eq.trans ?_
    (PresheafOfModules.map_comp_apply ((laurent L).piece (n : ℤ)).val e₁ eU X)
  exact congrArg (fun r => ((laurent L).piece (n : ℤ)).val.restrictₛₗ r X)
    (Subsingleton.elim _ _)

/-- On a homogeneous section the graded ring map `Γ(U, 𝒜) ⟶ Γ(U', g^*𝒜)` is, in the degree of
the section, the restriction to `U'` of the pullback. -/
theorem sectionBaseChange_apply_of_mem (UZ : S.AffineZariskiSite) (UZ' : S'.AffineZariskiSite)
    (h : UZ'.toOpens ≤ g ⁻¹ᵁ UZ.toOpens) {m : ℕ} (y : A.sectionRing UZ.toOpens)
    (hy : y ∈ A.grading UZ.toOpens m) :
    (RelativeProjBaseChangeTwist.sectionBaseChange A g UZ UZ' h y :
        (A.pullback g).sectionRing UZ'.toOpens) m =
      Scheme.Modules.pullbackSection g (A.piece (m : ℤ)) UZ.toOpens UZ'.toOpens h (y m) := by
  obtain ⟨a, rfl⟩ := hy
  rw [RelativeProjBaseChangeTwist.sectionBaseChange_of, DirectSum.of_eq_same]
  exact DirectSum.of_eq_same _ _

/-- `veroneseSections_chartTwisting_toFun_baseChange` with the section of `g^*𝒜` taken to be the
image of the one of `𝒜` under the graded ring map of sections, at the image opens. -/
theorem veroneseSections_chartTwisting_toFun_sectionBaseChange
    (hUa : IsAffineOpen (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier)))
    (hU'a : IsAffineOpen (U'.ι ''ᵁ (⊤ : Opens U'.toScheme.toRingedSpace.carrier)))
    (hUU : U'.ι ''ᵁ (⊤ : Opens U'.toScheme.toRingedSpace.carrier) ≤
      g ⁻¹ᵁ (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier)))
    (hbase : (gU' ≫ U'.ι) ≫ g = gU ≫ U.ι)
    (χU : Twisting (gU ≫ U.ι) (situationAlgebra A) (k : ℤ) L)
    (χ' : Twisting (gU' ≫ U'.ι) (situationAlgebra (A.pullback g)) (k : ℤ) L)
    (hχ : HEq (χ'.baseChangeUp g (gU' ≫ U'.ι) (situationAlgebra A) (k : ℤ)) χU) (n : ℕ)
    (y : A.grading (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier)) (n * k)) :
    (veroneseSections (chartTwisting (A.pullback g) U' gU' χ')).toFun n
        (⟨RelativeProjBaseChangeTwist.sectionBaseChange A g ⟨_, hUa⟩ ⟨_, hU'a⟩ hUU
          (y : A.sectionRing (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier))),
          GradedRingHom.map_mem
            (RelativeProjBaseChangeTwist.sectionBaseChange A g ⟨_, hUa⟩ ⟨_, hU'a⟩ hUU) y.2⟩ :
          (A.pullback g).grading (U'.ι ''ᵁ (⊤ : Opens U'.toScheme.toRingedSpace.carrier))
            (n * k))
      = (veroneseSections (chartTwisting A U gU χU)).toFun n y :=
  veroneseSections_chartTwisting_toFun_baseChange A g gU gU' hUU hbase χU χ' hχ n y _
    (sectionBaseChange_apply_of_mem A g ⟨_, hUa⟩ ⟨_, hU'a⟩ hUU _ y.2)

/-- **The Veronese family of the chart-wise class of a base-changed quadruple is `comapVeronese`
of the one of the original quadruple**, degreewise, at gradings read at arbitrary affine opens
`V = U.ι ''ᵁ ⊤` and `V' = U'.ι ''ᵁ ⊤`. -/
theorem chartVeronese_baseChange_toFun {V : S.AffineZariskiSite} {V' : S'.AffineZariskiSite}
    (hV : U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier) = V.toOpens)
    (hV' : U'.ι ''ᵁ (⊤ : Opens U'.toScheme.toRingedSpace.carrier) = V'.toOpens)
    (hVV : V'.toOpens ≤ g ⁻¹ᵁ V.toOpens)
    (hbase : (gU' ≫ U'.ι) ≫ g = gU ≫ U.ι)
    (χU : Twisting (gU ≫ U.ι) (situationAlgebra A) (k : ℤ) L)
    (χ' : Twisting (gU' ≫ U'.ι) (situationAlgebra (A.pullback g)) (k : ℤ) L)
    (hχ : HEq (χ'.baseChangeUp g (gU' ≫ U'.ι) (situationAlgebra A) (k : ℤ)) χU)
    (ψU : VeroneseSections (A.grading V.toOpens) k L)
    (ψ' : VeroneseSections ((A.pullback g).grading V'.toOpens) k L)
    (hψU : HEq (veroneseSections (chartTwisting A U gU χU)) ψU)
    (hψ' : HEq (veroneseSections (chartTwisting (A.pullback g) U' gU' χ')) ψ')
    (n : ℕ) (y : A.grading V.toOpens (n * k)) :
    ψU.toFun n y = (ProjChartGradedClassifying.comapVeronese
      (RelativeProjBaseChangeTwist.sectionBaseChange A g V V' hVV) ψ').toFun n y := by
  obtain ⟨V, hVa⟩ := V
  obtain ⟨V', hV'a⟩ := V'
  change U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier) = V at hV
  change U'.ι ''ᵁ (⊤ : Opens U'.toScheme.toRingedSpace.carrier) = V' at hV'
  subst hV
  subst hV'
  exact ((veroneseSections_restrict_toFun_image A U L _ ψU hψU n y).symm.trans
      (veroneseSections_chartTwisting_toFun_sectionBaseChange A g gU gU' hVa hV'a hVV hbase
        χU χ' hχ n y).symm).trans
    (veroneseSections_restrict_toFun_image (A.pullback g) U' L _ ψ' hψ' n _)

/-- **The hypothesis of the base-change comparison of charts.** For affine opens `U` of `S` and
`U'` of `S'` with `U' ⊆ g⁻¹U`, two factorizations `(g_{U'} ≫ U'.ι) ≫ g = g_U ≫ U.ι` of one
morphism `T ⟶ S`, a twisting `χ'` for `g^*𝒜` and a twisting `χ_U` for `𝒜` heterogeneously equal to
its base change, a Veronese family `ψ'` for `Γ(U', g^*𝒜)` heterogeneously equal to the one of the
chart-wise class of `χ'` determines the one of the chart-wise class of `χ_U`: it is
`comapVeronese` of `ψ'` along `Γ(U, 𝒜) ⟶ Γ(U', g^*𝒜)`. -/
theorem heq_comapVeronese_chartTwisting_baseChange (V : S.AffineZariskiSite)
    (V' : S'.AffineZariskiSite) (hVV : V'.toOpens ≤ g ⁻¹ᵁ V.toOpens)
    (gU : T ⟶ V.toOpens.toScheme) (gU' : T ⟶ V'.toOpens.toScheme)
    (hbase : (gU' ≫ V'.toOpens.ι) ≫ g = gU ≫ V.toOpens.ι)
    (χU : Twisting (gU ≫ V.toOpens.ι) (situationAlgebra A) (k : ℤ) L)
    (χ' : Twisting (gU' ≫ V'.toOpens.ι) (situationAlgebra (A.pullback g)) (k : ℤ) L)
    (hχ : HEq (χ'.baseChangeUp g (gU' ≫ V'.toOpens.ι) (situationAlgebra A) (k : ℤ)) χU)
    (ψ' : VeroneseSections ((A.pullback g).grading V'.toOpens) k L)
    (hψ' : HEq (veroneseSections (chartTwisting (A.pullback g) V'.toOpens gU' χ')) ψ') :
    HEq (veroneseSections (chartTwisting A V.toOpens gU χU))
      (ProjChartGradedClassifying.comapVeronese
        (RelativeProjBaseChangeTwist.sectionBaseChange A g V V' hVV) ψ') := by
  obtain ⟨ψU, hψU⟩ := exists_veroneseSections_restrict A V.toOpens L V.toOpens.ι_image_top
    (veroneseSections (chartTwisting A V.toOpens gU χU))
  exact hψU.trans (heq_of_eq (veroneseSections_ext fun n y =>
    chartVeronese_baseChange_toFun A g gU gU' V.toOpens.ι_image_top V'.toOpens.ι_image_top hVV
      hbase χU χ' hχ ψU ψ' hψU hψ' n y))

end BaseChange

/-! ### The comparison of charts -/

section Charts

variable {S S' : Scheme.{u}} (A : SheafGradedAlgebra S) (g : S' ⟶ S)

/-- **The base-change comparison of charts for the classifying morphisms.** For affine opens `V`
of `S` and `V'` of `S'` with `V' ⊆ g⁻¹V`, two factorizations `(g_{V'} ≫ V'.ι) ≫ g = g_V ≫ V.ι` of
one morphism `T ⟶ S` and a quadruple `P'` for `g^*𝒜` over `g_{V'} ≫ V'.ι`, the morphism into
`Proj Γ(V', g^*𝒜)` attached to the chart-wise class of `P'`, followed by
`Proj(Γ(V, 𝒜) ⟶ Γ(V', g^*𝒜))`, is the morphism into `Proj Γ(V, 𝒜)` attached to the chart-wise class
of the base change of `P'` of Tag 01NT. -/
theorem Fd.toProj_chartEquiv_chartClass_comp_projMap_baseChange (V : S.AffineZariskiSite)
    (V' : S'.AffineZariskiSite) (hVV : V'.toOpens ≤ g ⁻¹ᵁ V.toOpens) {k : ℕ} (hk : 0 < k)
    {T : Scheme.{u}} (gV : T ⟶ V.toOpens.toScheme) (gV' : T ⟶ V'.toOpens.toScheme)
    (hbase : (gV' ≫ V'.toOpens.ι) ≫ g = gV ≫ V.toOpens.ι)
    (P' : Quadruple (gV' ≫ V'.toOpens.ι) (situationAlgebra (A.pullback g)) (k : ℤ)) :
    toProj ((A.pullback g).grading V'.toOpens)
          (Fd.chartEquiv (A.pullback g) V'.toOpens V'.2 hk T
            (Fd.chartClass (A.pullback g) V'.toOpens gV' (Quotient.mk _ P')))
        ≫ AlgebraicGeometry.Proj.map (RelativeProjBaseChangeTwist.sectionBaseChange A g V V' hVV)
          (RelativeProjBaseChangeTwist.irrelevant_le_map_sectionBaseChange A g V V' hVV)
      = toProj (A.grading V.toOpens)
          (Fd.chartEquiv A V.toOpens V.2 hk T
            (Fd.chartClass A V.toOpens gV (Quotient.mk _ (Quadruple.congrBaseStrict hbase
              (P'.baseChangeUp g (gV' ≫ V'.toOpens.ι) (situationAlgebra A) (k : ℤ)))))) := by
  have : IsAffine V.toOpens.toScheme := V.2
  have : IsAffine V'.toOpens.toScheme := V'.2
  set PV := Quadruple.congrBaseStrict hbase
    (P'.baseChangeUp g (gV' ≫ V'.toOpens.ι) (situationAlgebra A) (k : ℤ)) with hPV
  rw [Fd.chartClass_mk (A.pullback g) V'.toOpens gV' P', Fd.chartClass_mk A V.toOpens gV PV]
  set Q' := (P'.baseChangeDown V'.toOpens.ι gV' (situationAlgebra (A.pullback g))
      (k : ℤ)).algebraTransport
      (unitalHomInverse (restrictPullbackUnitalHom (A.pullback g) V'.toOpens.ι)
        (isIso_restrictPullbackUnitalHom_app_forall (A.pullback g) V'.toOpens.ι))
      (isIso_unitalHomInverse_app (restrictPullbackUnitalHom (A.pullback g) V'.toOpens.ι)
        (isIso_restrictPullbackUnitalHom_app_forall (A.pullback g) V'.toOpens.ι)) with hQ'
  set QV := (PV.baseChangeDown V.toOpens.ι gV (situationAlgebra A) (k : ℤ)).algebraTransport
      (unitalHomInverse (restrictPullbackUnitalHom A V.toOpens.ι)
        (isIso_restrictPullbackUnitalHom_app_forall A V.toOpens.ι))
      (isIso_unitalHomInverse_app (restrictPullbackUnitalHom A V.toOpens.ι)
        (isIso_restrictPullbackUnitalHom_app_forall A V.toOpens.ι)) with hQV
  -- the Veronese family of the chart-wise class of `P'`, read at the grading `Γ(V', g^*𝒜)`
  obtain ⟨ψ, hψ⟩ := exists_veroneseSections_restrict (A.pullback g) V'.toOpens (L := P'.L)
    V'.toOpens.ι_image_top (veroneseSections Q'.twisting)
  have hψV : HEq (veroneseSections QV.twisting)
      (ProjChartGradedClassifying.comapVeronese
        (RelativeProjBaseChangeTwist.sectionBaseChange A g V V' hVV) ψ) :=
    heq_comapVeronese_chartTwisting_baseChange A g V V' hVV gV gV' hbase
      (Twisting.congrBase hbase
        (P'.twisting.baseChangeUp g (gV' ≫ V'.toOpens.ι) (situationAlgebra A) (k : ℤ)))
      P'.twisting (Twisting.heq_congrBase hbase _).symm ψ hψ
  have hgen : (⨆ f : A.grading V.toOpens k, nonvanishingOpen T P'.L
      (psiSection (A.grading V.toOpens)
        (ProjChartGradedClassifying.comapVeronese
          (RelativeProjBaseChangeTwist.sectionBaseChange A g V V' hVV) ψ) f)) = ⊤ :=
    iSup_nonvanishingOpen_psiSection_restrict_heq A V.toOpens (L := P'.L)
      V.toOpens.ι_image_top (veroneseSections QV.twisting) _ hψV
      (Quadruple.iSup_nonvanishingOpen_psiSection_eq_top (B := A.restrict V.toOpens.ι) (d := k)
        (fun n => (A.restrict V.toOpens.ι).isQuasicoherent n) QV)
  rw [Fd.toProj_chartEquiv_mk (A.pullback g) V'.toOpens V'.2 hk gV' Q' rfl ψ hψ
      (ProjChartGradedClassifying.iSup_nonvanishingOpen_psiSection_comapVeronese
        (RelativeProjBaseChangeTwist.sectionBaseChange A g V V' hVV) ψ hgen),
    Fd.toProj_chartEquiv_mk A V.toOpens V.2 hk gV QV rfl _ hψV hgen]
  exact ProjChartGradedClassifying.toProj_classifyingHom_comp_projMap
    (RelativeProjBaseChangeTwist.sectionBaseChange A g V V' hVV) ψ
    (RelativeProjBaseChangeTwist.irrelevant_le_map_sectionBaseChange A g V V' hVV) hk hgen

/-- A fiber point of a chart is the chart-wise class of any quotient class equal to the one of its
inverse image. -/
private theorem eq_chartClass_of_snd_eq {S : Scheme.{u}} (B : SheafGradedAlgebra S) (V : S.Opens)
    {k : ℤ} {T : Scheme.{u}} (η : Fd (situationAlgebra (B.restrict V.ι)) k T)
    (q : Quotient (Quadruple.setoid (η.1 ≫ V.ι) (situationAlgebra B) k))
    (hq : (Fd.chartClassInv B V η).2 = q) : η = Fd.chartClass B V η.1 q := by
  subst hq
  exact (Fd.chartClass_chartClassInv B V η).symm

/-- **The chart-wise morphisms of a quadruple for `g^*𝒜` and of its base change agree after the
base-change morphism of Tag 01O3.** For affine opens `V ⊆ S`, `V' ⊆ g⁻¹V ⊆ S'` and chart-wise
classes `η'` for `(g^*𝒜)|_{V'}` and `η` for `𝒜|_V` whose images in `F_d(T)` correspond under the
base change of Tag 01NT, the morphism into `Proj_{S'}(g^*𝒜)` attached to `η'` followed by
`Proj_{S'}(g^*𝒜) ⟶ Proj_S(𝒜)` is the morphism into `Proj_S(𝒜)` attached to `η`. -/
theorem Fd.chartHom_comp_baseChangeHom (V : S.AffineZariskiSite) (V' : S'.AffineZariskiSite)
    (hVV : V'.toOpens ≤ g ⁻¹ᵁ V.toOpens) {k : ℕ} (hk : 0 < k) {T : Scheme.{u}}
    (η' : Fd (situationAlgebra ((A.pullback g).restrict V'.toOpens.ι)) (k : ℤ) T)
    (η : Fd (situationAlgebra (A.restrict V.toOpens.ι)) (k : ℤ) T)
    (h : Fd.baseChangeUp g (situationAlgebra A) (k : ℤ)
        (Fd.chartClassInv (A.pullback g) V'.toOpens η') = Fd.chartClassInv A V.toOpens η) :
    Fd.chartHom (A.pullback g) V'.toOpens (relativeProj (A.pullback g)) V'.2 hk T η'
        ≫ RelativeProjBaseChangeTwist.baseChangeHom A g
      = Fd.chartHom A V.toOpens (relativeProj A) V.2 hk T η := by
  obtain ⟨gV', q'⟩ := η'
  obtain ⟨gV, q⟩ := η
  have hbase : (gV' ≫ V'.toOpens.ι) ≫ g = gV ≫ V.toOpens.ι := congrArg Sigma.fst h
  obtain ⟨P', hP'⟩ := Quotient.exists_rep
    (show Quotient (Quadruple.setoid (gV' ≫ V'.toOpens.ι) (situationAlgebra (A.pullback g))
        (k : ℤ)) from
      (Fd.chartClassInv (A.pullback g) V'.toOpens
        (⟨gV', q'⟩ : Fd (situationAlgebra ((A.pullback g).restrict V'.toOpens.ι)) (k : ℤ) T)).2)
  have h'class := eq_chartClass_of_snd_eq (A.pullback g) V'.toOpens ⟨gV', q'⟩ _ hP'.symm
  have hbc : Fd.baseChangeUp g (situationAlgebra A) (k : ℤ)
      (Fd.chartClassInv (A.pullback g) V'.toOpens
        (⟨gV', q'⟩ : Fd (situationAlgebra ((A.pullback g).restrict V'.toOpens.ι)) (k : ℤ) T))
      = Fd.mk ((gV' ≫ V'.toOpens.ι) ≫ g)
        (P'.baseChangeUp g (gV' ≫ V'.toOpens.ι) (situationAlgebra A) (k : ℤ)) := by
    rw [h'class, Fd.chartClassInv_chartClass]
    rfl
  have hq2 : (show Quotient (Quadruple.setoid (gV ≫ V.toOpens.ι) (situationAlgebra A) (k : ℤ))
        from (Fd.chartClassInv A V.toOpens
          (⟨gV, q⟩ : Fd (situationAlgebra (A.restrict V.toOpens.ι)) (k : ℤ) T)).2)
      = Quotient.mk _ (Quadruple.congrBaseStrict hbase
          (P'.baseChangeUp g (gV' ≫ V'.toOpens.ι) (situationAlgebra A) (k : ℤ))) :=
    Quadruple.eq_mk_congrBaseStrict_of_heq hbase _ _
      ((Fd.heq_snd h).symm.trans (Fd.heq_snd hbc))
  have hclass := eq_chartClass_of_snd_eq A V.toOpens ⟨gV, q⟩ _ hq2
  rw [h'class, hclass, Fd.chartHom_eq_toProj_comp_chart (A.pullback g) V'.toOpens _ V'.2 hk T,
    Fd.chartHom_eq_toProj_comp_chart A V.toOpens _ V.2 hk T]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun φ => toProj ((A.pullback g).grading V'.toOpens) _ ≫ φ)
    (RelativeProjBaseChangeTwist.chart_baseChangeHom A g V V' hVV)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (fun φ => φ ≫ (relativeProj A).chart V.toOpens V.2)
    (Fd.toProj_chartEquiv_chartClass_comp_projMap_baseChange A g V V' hVV hk gV gV' hbase P')

end Charts

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
