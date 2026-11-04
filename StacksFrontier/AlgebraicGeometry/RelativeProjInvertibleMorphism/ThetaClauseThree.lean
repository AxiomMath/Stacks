module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.Characterization
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaUnit
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictCanHom

/-!
# Clause (3) of Stacks Tag 01O9 for `θ`

Over an affine open `V` of the base, the inverse image of `θ` along the inclusion
`j : U(ψ') ⟶ U(ψ)`, read through the identifications `…Triple.sourceIso` and `…Triple.targetIso`
of its source and target, is [Stacks, Tag 01NK]'s `θ` for the induced datum `ψ'`. Both are maps out
of an inverse image along `r_{ℒ|_{f^{-1}(V)}, ψ'}`, so it suffices to compare them on pulled-back
sections (`pullback_hom_ext`); there the source identification undoes the two pull-backs, `θ` on a
pulled-back section is its pushforward form, over the chart of `V` that is the local datum
`…GradedPowerMap.thetaLoc` (`…GradedPowerMap.restrict_thetaPush`), and the target identification
is `…GradedPowerMap.lam`, which inverts the target comparison of the local datum.

## Main results

* `…GradedPowerMap.theta_clauseThree_app`: the `θ` half of clause (3), in every degree.
* `…GradedPowerMap.isClauseThree_theta`: **clause (3) for `(U(ψ), r_{ℒ,ψ}, θ)`**, as
  `…Triple.IsClauseThree` states it.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules (pullbackSection)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

section Generic

variable {X Y Z : Scheme.{u}}

/-- **A morphism out of an inverse image is determined by its values on pulled-back sections.** -/
theorem pullback_hom_ext (g : Y ⟶ X) {M : X.Modules} {N : Y.Modules}
    {φ ψ : (Scheme.Modules.pullback g).obj M ⟶ N}
    (h : ∀ (W : X.Opens) (s : M.val.obj (op W)),
      φ.val.app (op (g ⁻¹ᵁ W)) (pullbackSection g M W (g ⁻¹ᵁ W) le_rfl s) =
        ψ.val.app (op (g ⁻¹ᵁ W)) (pullbackSection g M W (g ⁻¹ᵁ W) le_rfl s)) : φ = ψ := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv M N).injective
  refine Scheme.Modules.hom_ext _ _ fun W => ConcreteCategory.hom_ext _ _ fun s => ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have e := Stacks.Conormal.pullbackSection_self g M W s
  exact (congrArg (φ.val.app (op (g ⁻¹ᵁ W))) e).symm.trans
    ((h W s).trans (congrArg (ψ.val.app (op (g ⁻¹ᵁ W))) e))

/-- An open set lies in the preimage of its image under an open immersion. -/
private theorem le_preimage_image_opens (f : Y ⟶ X) [IsOpenImmersion f] (W : Y.Opens) :
    W ≤ f ⁻¹ᵁ (f ''ᵁ W) :=
  (f.preimage_image_eq W).ge

/-- The identification of a restriction with an inverse image, on a section. -/
theorem restrictFunctorIsoPullback_hom_val_app (f : Y ⟶ X) [IsOpenImmersion f] (M : X.Modules)
    (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ (f ''ᵁ V)) (x : Γ(M.restrict f, V)) :
    ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M).val.app (op V) x =
      pullbackSection f M (f ''ᵁ V) V h x := by
  have hi := Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection f M (f ''ᵁ V) V h
    le_rfl x
  have hm : M.val.map (homOfLE (le_refl (f ''ᵁ V))).op x = x :=
    map_id_apply M (homOfLE (le_refl (f ''ᵁ V))).op x
  refine (congrArg (((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M).val.app (op V))
    (hm.symm.trans hi.symm)).trans ?_
  exact ConcreteCategory.congr_hom (congrArg (fun φ => φ.val.app (op V))
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M).inv_hom_id) _

/-- The inverse of the congruence of two equal morphisms, on a pulled-back section. -/
theorem pullbackSection_congr_inv {f g : Y ⟶ X} (hfg : f = g) (M : X.Modules) (U : X.Opens)
    (V : Y.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) (a : M.val.obj (op U)) :
    ((Scheme.Modules.pullbackCongr hfg).inv.app M).val.app (op V)
      (pullbackSection g M U V hg a) = pullbackSection f M U V hf a := by
  subst g
  rfl

/-- The source identification of clause (3), with every object a variable, on a pulled-back
section. -/
theorem src_inv_pullbackSection {Y' U' X' Z' : Scheme.{u}} (j : Y' ⟶ U') (r : U' ⟶ X')
    (g : Y' ⟶ Z') (c : Z' ⟶ X') [IsOpenImmersion c] (hj : j ≫ r = g ≫ c) (M : X'.Modules)
    {N : Z'.Modules}
    (E : (Scheme.Modules.pullback c).obj M ≅ N) (W : Z'.Opens) (s : N.val.obj (op W))
    (x : M.val.obj (op (c ''ᵁ W))) (hc : W ≤ c ⁻¹ᵁ (c ''ᵁ W))
    (hx : E.inv.val.app (op W) s = pullbackSection c M (c ''ᵁ W) W hc x)
    (h4 : g ⁻¹ᵁ W ≤ j ⁻¹ᵁ (r ⁻¹ᵁ (c ''ᵁ W))) :
    ((Scheme.Modules.pullbackComp j r).app M ≪≫ (Scheme.Modules.pullbackCongr hj).app M
        ≪≫ (Scheme.Modules.pullbackComp g c).symm.app M
        ≪≫ (Scheme.Modules.pullback g).mapIso E).inv.val.app (op (g ⁻¹ᵁ W))
      (pullbackSection g N W (g ⁻¹ᵁ W) le_rfl s) =
      pullbackSection j ((Scheme.Modules.pullback r).obj M) (r ⁻¹ᵁ (c ''ᵁ W)) (g ⁻¹ᵁ W) h4
        (pullbackSection r M (c ''ᵁ W) (r ⁻¹ᵁ (c ''ᵁ W)) le_rfl x) := by
  have h2 : g ⁻¹ᵁ W ≤ (g ≫ c) ⁻¹ᵁ (c ''ᵁ W) := g.preimage_mono hc
  have h3 : g ⁻¹ᵁ W ≤ (j ≫ r) ⁻¹ᵁ (c ''ᵁ W) := hj ▸ h2
  have e1 := (Scheme.Modules.pullbackSection_naturality g E.inv W _ le_rfl s).trans
      (congrArg (pullbackSection g _ W _ le_rfl) hx)
  have e2 := Scheme.Modules.pullbackSection_comp g c M _ W _ hc le_rfl h2 x
  have e3 := pullbackSection_congr_inv hj M _ _ h3 h2 x
  have e4 := Stacks.AlgebraicGeometry.ModuleLimits.pullbackComp_inv_val_app_pullbackSection j r M
    _ _ _ le_rfl h4 h3 x
  have e12 : ((Scheme.Modules.pullbackComp g c).hom.app M).val.app (op (g ⁻¹ᵁ W))
      (((Scheme.Modules.pullback g).map E.inv).val.app (op (g ⁻¹ᵁ W))
        (pullbackSection g N W (g ⁻¹ᵁ W) le_rfl s)) =
      pullbackSection (g ≫ c) M (c ''ᵁ W) (g ⁻¹ᵁ W) h2 x :=
    (congrArg (((Scheme.Modules.pullbackComp g c).hom.app M).val.app (op (g ⁻¹ᵁ W))) e1).trans e2
  have e34 := (congrArg (((Scheme.Modules.pullbackCongr hj).inv.app M).val.app (op (g ⁻¹ᵁ W)))
    e12).trans e3
  exact (congrArg (((Scheme.Modules.pullbackComp j r).inv.app M).val.app (op (g ⁻¹ᵁ W)))
      e34).trans e4

/-- The target identification of clause (3), with every object a variable, on a pulled-back
section. -/
theorem tgt_hom_pullbackSection {Y' U' T' F' : Scheme.{u}} (j : Y' ⟶ U') (e : U' ⟶ T')
    [IsOpenImmersion e] (a : Y' ⟶ F') [IsOpenImmersion a] (b : F' ⟶ T') (hjι : j ≫ e = a ≫ b)
    (K : T'.Modules) {K' : F'.Modules} (I : (Scheme.Modules.pullback b).obj K ≅ K')
    (O' : U'.Opens) (V : Y'.Opens) (h4 : V ≤ j ⁻¹ᵁ O') (t : Γ(K.restrict e, O'))
    (hV' : a ''ᵁ V ≤ b ⁻¹ᵁ (e ''ᵁ O')) :
    ((Scheme.Modules.pullback j).mapIso ((Scheme.Modules.restrictFunctorIsoPullback e).app K)
        ≪≫ (Scheme.Modules.pullbackComp j e).app _
        ≪≫ (Scheme.Modules.pullbackCongr hjι).app _
        ≪≫ (Scheme.Modules.pullbackComp a b).symm.app _
        ≪≫ (Scheme.Modules.pullback a).mapIso I
        ≪≫ ((Scheme.Modules.restrictFunctorIsoPullback a).app K').symm).hom.val.app (op V)
      (pullbackSection j (K.restrict e) O' V h4 t) =
      K'.val.map (homOfLE hV').op (I.hom.val.app (op (b ⁻¹ᵁ (e ''ᵁ O')))
        (pullbackSection b K (e ''ᵁ O') (b ⁻¹ᵁ (e ''ᵁ O')) le_rfl t)) := by
  have hO := le_preimage_image_opens e O'
  have h5 : V ≤ (j ≫ e) ⁻¹ᵁ (e ''ᵁ O') := h4.trans (j.preimage_mono hO)
  have h6 : V ≤ (a ≫ b) ⁻¹ᵁ (e ''ᵁ O') := hjι ▸ h5
  have h7 : V ≤ a ⁻¹ᵁ (b ⁻¹ᵁ (e ''ᵁ O')) := h6
  have g1 := (Scheme.Modules.pullbackSection_naturality j
    ((Scheme.Modules.restrictFunctorIsoPullback e).hom.app K) O' V h4 t).trans
      (congrArg (pullbackSection j _ O' V h4) (restrictFunctorIsoPullback_hom_val_app e K O' hO t))
  have g2 := Scheme.Modules.pullbackSection_comp j e K (e ''ᵁ O') O' V hO h4 h5 t
  have g3 := Scheme.Modules.pullbackSection_congr hjι K (e ''ᵁ O') V h5 h6 t
  have g4 := Stacks.AlgebraicGeometry.ModuleLimits.pullbackComp_inv_val_app_pullbackSection a b K
    (e ''ᵁ O') (b ⁻¹ᵁ (e ''ᵁ O')) V le_rfl h7 h6 t
  have g5 := Scheme.Modules.pullbackSection_naturality a I.hom (b ⁻¹ᵁ (e ''ᵁ O')) V h7
    (pullbackSection b K (e ''ᵁ O') (b ⁻¹ᵁ (e ''ᵁ O')) le_rfl t)
  have g6 := Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection a K'
    (b ⁻¹ᵁ (e ''ᵁ O')) V h7 hV' (I.hom.val.app (op (b ⁻¹ᵁ (e ''ᵁ O')))
      (pullbackSection b K (e ''ᵁ O') (b ⁻¹ᵁ (e ''ᵁ O')) le_rfl t))
  have g12 := (congrArg (((Scheme.Modules.pullbackComp j e).hom.app K).val.app (op V)) g1).trans g2
  have g123 :=
    (congrArg (((Scheme.Modules.pullbackCongr hjι).hom.app K).val.app (op V)) g12).trans g3
  have g4' :=
    (congrArg (((Scheme.Modules.pullbackComp a b).inv.app K).val.app (op V)) g123).trans g4
  have g5' := (congrArg (((Scheme.Modules.pullback a).map I.hom).val.app (op V)) g4').trans g5
  exact (congrArg (((Scheme.Modules.restrictFunctorIsoPullback a).inv.app K').val.app (op V))
    g5').trans g6

end Generic

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

namespace GradedPowerMap

attribute [local irreducible] GradedPowerMap.globalMorphism
  Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.glued

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f)

/-- The inverse of the chart identification of the twists is the inverse of the chart
identification of the glued twist data followed by the comparison of restriction with pull-back. -/
theorem chartTwistIso_inv_eq (V : S.affineOpens) (n : ℤ) :
    (Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistIso A n V).inv =
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).chartData.chartIso V.1 V.2 n).inv ≫
        (Scheme.Modules.restrictFunctorIsoPullback ((relativeProj A).chart V.1 V.2)).hom.app
          (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwist A n) := rfl

/-- The inverse of the chart identification of the twists, on sections. -/
theorem chartTwistIso_inv_val_app (V : S.affineOpens) (n : ℤ)
    (W : (AlgebraicGeometry.Proj (A.grading V.1)).Opens)
    (s : (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (A.grading V.1) n).val.obj
      (op W))
    (hc : W ≤ ((relativeProj A).chart V.1 V.2) ⁻¹ᵁ (((relativeProj A).chart V.1 V.2) ''ᵁ W)) :
    (Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistIso A n V).inv.val.app (op W) s =
      pullbackSection ((relativeProj A).chart V.1 V.2)
        (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwist A n) _ W hc
        (((GluedTwistAlgebra.twistDataOfGradedAlgebra A).chartData.chartIso V.1 V.2 n).inv.val.app
          (op W) s) := by
  rw [chartTwistIso_inv_eq]
  exact restrictFunctorIsoPullback_hom_val_app ((relativeProj A).chart V.1 V.2)
    (Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwist A n) W hc _

/-- The source identification of clause (3) is the composite of the pull-back composition
isomorphisms along `j` and the chart, followed by the chart identification of the twists. -/
theorem sourceIso_eq (V : S.affineOpens)
    (j : ((P.affineDatum V.1).coveringOpen).toScheme ⟶ P.coveringOpen.toScheme)
    (hj : j ≫ P.globalMorphism (relativeProj A) =
      (P.affineDatum V.1).glued ≫ (relativeProj A).chart V.1 V.2) (n : ℤ) :
    Triple.sourceIso P
        ⟨P.coveringOpen, P.globalMorphism (relativeProj A), GradedNonnegHom.ofHom P.theta⟩
        V j hj n =
      (Scheme.Modules.pullbackComp j (P.globalMorphism (relativeProj A))).app (Otw A n)
        ≪≫ (Scheme.Modules.pullbackCongr hj).app (Otw A n)
        ≪≫ (Scheme.Modules.pullbackComp (P.affineDatum V.1).glued
          ((relativeProj A).chart V.1 V.2)).symm.app (Otw A n)
        ≪≫ (Scheme.Modules.pullback (P.affineDatum V.1).glued).mapIso
          (Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistIso A n V) := rfl

/-- **The source identification of clause (3), on a pulled-back section**: it carries the
pull-back along `r_{ℒ,ψ}` and then along `j` of the section of `𝒪(n)` over the chart image of
`W` to the pull-back along the morphism of [Stacks, Tag 01NK] of the corresponding section of the
absolute twist. -/
theorem sourceIso_inv_pullbackSection (V : S.affineOpens)
    (j : ((P.affineDatum V.1).coveringOpen).toScheme ⟶ P.coveringOpen.toScheme)
    (hj : j ≫ P.globalMorphism (relativeProj A) =
      (P.affineDatum V.1).glued ≫ (relativeProj A).chart V.1 V.2) (n : ℤ)
    (W : (AlgebraicGeometry.Proj (A.grading V.1)).Opens)
    (s : (Stacks.AlgebraicGeometry.ProjChartGradedTheta.twistM (A.grading V.1) n).val.obj (op W))
    (h4 : (P.affineDatum V.1).glued ⁻¹ᵁ W ≤ j ⁻¹ᵁ (P.globalMorphism (relativeProj A) ⁻¹ᵁ
      ((relativeProj A).chart V.1 V.2 ''ᵁ W))) :
    (Triple.sourceIso P
        ⟨P.coveringOpen, P.globalMorphism (relativeProj A), GradedNonnegHom.ofHom P.theta⟩ V j hj
        n).inv.val.app (op ((P.affineDatum V.1).glued ⁻¹ᵁ W))
      (pullbackSection (P.affineDatum V.1).glued _ W _ le_rfl s) =
      pullbackSection j ((Scheme.Modules.pullback (P.globalMorphism (relativeProj A))).obj
          (Otw A n)) _ _ h4
        (pullbackSection (P.globalMorphism (relativeProj A)) (Otw A n)
          ((relativeProj A).chart V.1 V.2 ''ᵁ W) _ le_rfl
          (((twD A).chartData.chartIso V.1 V.2 n).inv.app W s)) := by
  have hc := le_preimage_image_opens ((relativeProj A).chart V.1 V.2) W
  rw [P.sourceIso_eq V j hj n]
  exact src_inv_pullbackSection j (P.globalMorphism (relativeProj A)) (P.affineDatum V.1).glued
    ((relativeProj A).chart V.1 V.2) hj (Otw A n)
    (Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistIso A n V) W s _ hc
    (chartTwistIso_inv_val_app V n W s hc) h4

/-- The target identification of clause (3) is the composite of the comparisons of restriction
with pull-back, the pull-back composition isomorphisms along `j`, and `intPullIso`. -/
theorem targetIso_eq (V : S.affineOpens)
    (j : ((P.affineDatum V.1).coveringOpen).toScheme ⟶ P.coveringOpen.toScheme)
    (hjι : j ≫ P.coveringOpen.ι = ((P.affineDatum V.1).coveringOpen).ι ≫ (f ⁻¹ᵁ V.1).ι) (n : ℤ) :
    Triple.targetIso P
        ⟨P.coveringOpen, P.globalMorphism (relativeProj A), GradedNonnegHom.ofHom P.theta⟩
        V j hjι n =
      (Scheme.Modules.pullback j).mapIso ((Scheme.Modules.restrictFunctorIsoPullback
          P.coveringOpen.ι).app (tensorPowerModule T P.L n))
        ≪≫ (Scheme.Modules.pullbackComp j P.coveringOpen.ι).app _
        ≪≫ (Scheme.Modules.pullbackCongr hjι).app _
        ≪≫ (Scheme.Modules.pullbackComp ((P.affineDatum V.1).coveringOpen).ι
              (f ⁻¹ᵁ V.1).ι).symm.app _
        ≪≫ (Scheme.Modules.pullback ((P.affineDatum V.1).coveringOpen).ι).mapIso
              (Stacks.AlgebraicGeometry.ProjChartIntPullbackMul.intPullIso (f ⁻¹ᵁ V.1).ι P.L n)
        ≪≫ ((Scheme.Modules.restrictFunctorIsoPullback
              ((P.affineDatum V.1).coveringOpen).ι).app _).symm := rfl

/-- `pullPow` is [Stacks, Tag 01CD]'s comparison of the integer powers after a pulled-back
section. -/
theorem pullPow_eq_pullbackSection (V : S.Opens) (n : ℤ) (O : T.Opens)
    (t : Γ(tensorPowerModule T P.L n, O)) :
    P.pullPow V n O t =
      (Stacks.AlgebraicGeometry.ProjChartIntPullbackMul.intPullIso (f ⁻¹ᵁ V).ι P.L n).hom.val.app
        (op ((f ⁻¹ᵁ V).ι ⁻¹ᵁ O))
        (pullbackSection (f ⁻¹ᵁ V).ι (tensorPowerModule T P.L n) O _ le_rfl t) :=
  (P.pullPow_eq V n O t).trans (congrArg _
    (Stacks.Conormal.pullbackSection_self (f ⁻¹ᵁ V).ι (tensorPowerModule T P.L n) O t).symm)

/-- **The target identification of clause (3), on a pulled-back section**, is `lam`. -/
theorem targetIso_hom_pullbackSection (V : S.affineOpens)
    (j : ((P.affineDatum V.1).coveringOpen).toScheme ⟶ P.coveringOpen.toScheme)
    (hjι : j ≫ P.coveringOpen.ι = ((P.affineDatum V.1).coveringOpen).ι ≫ (f ⁻¹ᵁ V.1).ι) (n : ℤ)
    (W : (AlgebraicGeometry.Proj (A.grading V.1)).Opens)
    (h4 : (P.affineDatum V.1).glued ⁻¹ᵁ W ≤ j ⁻¹ᵁ (P.globalMorphism (relativeProj A) ⁻¹ᵁ
      ((relativeProj A).chart V.1 V.2 ''ᵁ W)))
    (t : Γ(tensorPowerModule T P.L n, P.targetOpen V.1 V.2 W)) :
    (Triple.targetIso P
        ⟨P.coveringOpen, P.globalMorphism (relativeProj A), GradedNonnegHom.ofHom P.theta⟩ V j hjι
        n).hom.val.app (op ((P.affineDatum V.1).glued ⁻¹ᵁ W))
      (pullbackSection j ((tensorPowerModule T P.L n).restrict P.coveringOpen.ι) _ _ h4 t) =
      P.lam V.1 V.2 n W t := by
  rw [P.targetIso_eq V j hjι n]
  refine (tgt_hom_pullbackSection j P.coveringOpen.ι ((P.affineDatum V.1).coveringOpen).ι
    (f ⁻¹ᵁ V.1).ι hjι (tensorPowerModule T P.L n)
    (Stacks.AlgebraicGeometry.ProjChartIntPullbackMul.intPullIso (f ⁻¹ᵁ V.1).ι P.L n) _ _ h4 t
    (P.sourceOpen_le V.1 V.2 W)).trans ?_
  exact congrArg _ (P.pullPow_eq_pullbackSection V.1 n _ t).symm

/-- `θ` on a pulled-back section is its pushforward form on the section. -/
theorem theta_app_pullbackSection (n : ℤ) (O : (relativeProj A).scheme.Opens)
    (x : Γ(Otw A n, O)) :
    (P.theta.app n).val.app (op (P.globalMorphism (relativeProj A) ⁻¹ᵁ O))
        (pullbackSection (P.globalMorphism (relativeProj A)) (Otw A n) O _ le_rfl x) =
      (P.thetaPush n).app O x := by
  have h0 := Stacks.Conormal.pullbackSection_self (P.globalMorphism (relativeProj A)) (Otw A n) O x
  have h1 : (P.theta.app n).val.app (op (P.globalMorphism (relativeProj A) ⁻¹ᵁ O))
        (Stacks.RingedSpace.pullbackUnit (P.globalMorphism (relativeProj A)).toLRSHom.toShHom
          (Otw A n) (op O) x) =
      (P.thetaPushHom.app n).val.app (op O) x :=
    Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.transposeAppHom_pullbackUnit
      (P.globalMorphism (relativeProj A)).toLRSHom.toShHom P.thetaPushHom n O x
  have h1' : (P.thetaPushHom.app n).val.app (op O) x = (P.thetaPush n).app O x := rfl
  exact (congrArg ((P.theta.app n).val.app (op (P.globalMorphism (relativeProj A) ⁻¹ᵁ O)))
    h0).trans (h1.trans h1')

/-- `thetaLoc` on sections is `chartTargetHom` applied to `pushTheta` of the image of the section
under the chart identification. -/
theorem thetaLoc_app (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ)
    (W : (AlgebraicGeometry.Proj (A.grading V)).Opens)
    (x : Γ(Scheme.Modules.restrict (Otw A n) ((relativeProj A).chart V hV), W)) :
    (P.thetaLoc V hV n).app W x = (P.chartTargetHom V hV n).app W
      ((Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.pushTheta (A.grading V)
        (P.affineDatum V) n).app W (((twD A).chartData.chartIso V hV n).hom.app W x)) := rfl

/-- The pushforward form of `θ` on the chart image of `W` agrees with `thetaLoc` on `W`. -/
theorem thetaPush_app_chart (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ)
    (W : (AlgebraicGeometry.Proj (A.grading V)).Opens)
    (x : Γ(Otw A n, (relativeProj A).chart V hV ''ᵁ W)) :
    (P.thetaPush n).app ((relativeProj A).chart V hV ''ᵁ W) x = (P.thetaLoc V hV n).app W x :=
  congrArg (fun φ => Scheme.Modules.Hom.app φ W x) (P.restrict_thetaPush V hV n)

/-- **The `θ` half of clause (3) of [Stacks, Tag 01O9]**: over an affine open `V` of the base,
the inverse image of `θ` along `j : U(ψ') ⟶ U(ψ)`, read through the identifications of its source
and target, is [Stacks, Tag 01NK]'s `θ` for the induced datum `ψ'`, in every degree. -/
theorem theta_clauseThree_app (V : S.affineOpens)
    (j : ((P.affineDatum V.1).coveringOpen).toScheme ⟶ P.coveringOpen.toScheme)
    (hjι : j ≫ P.coveringOpen.ι = ((P.affineDatum V.1).coveringOpen).ι ≫ (f ⁻¹ᵁ V.1).ι) (n : ℤ) :
    (Triple.sourceIso P
        ⟨P.coveringOpen, P.globalMorphism (relativeProj A), GradedNonnegHom.ofHom P.theta⟩ V j
        (P.comp_globalMorphism_eq (relativeProj A) V j hjι) n).inv ≫
      (Scheme.Modules.pullback j).map (P.theta.app n) ≫
      (Triple.targetIso P
          ⟨P.coveringOpen, P.globalMorphism (relativeProj A), GradedNonnegHom.ofHom P.theta⟩ V j hjι
        n).hom =
      (Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.theta (A.grading V.1)
        (P.affineDatum V.1)).app n := by
  have hj := P.comp_globalMorphism_eq (relativeProj A) V j hjι
  refine pullback_hom_ext (P.affineDatum V.1).glued fun W s => ?_
  have hc := le_preimage_image_opens ((relativeProj A).chart V.1 V.2) W
  have h4 : (P.affineDatum V.1).glued ⁻¹ᵁ W ≤ j ⁻¹ᵁ (P.globalMorphism (relativeProj A) ⁻¹ᵁ
      ((relativeProj A).chart V.1 V.2 ''ᵁ W)) := by
    rw [← Scheme.Hom.comp_preimage, hj]
    exact (P.affineDatum V.1).glued.preimage_mono hc
  have a1 := P.sourceIso_inv_pullbackSection V j hj n W s h4
  have a2 := Scheme.Modules.pullbackSection_naturality j (P.theta.app n) _ _ h4
    (pullbackSection (P.globalMorphism (relativeProj A)) (Otw A n)
      ((relativeProj A).chart V.1 V.2 ''ᵁ W) _ le_rfl
      (((twD A).chartData.chartIso V.1 V.2 n).inv.app W s))
  have a3 := P.theta_app_pullbackSection n ((relativeProj A).chart V.1 V.2 ''ᵁ W)
    (((twD A).chartData.chartIso V.1 V.2 n).inv.app W s)
  have hs : ((twD A).chartData.chartIso V.1 V.2 n).hom.app W
      (((twD A).chartData.chartIso V.1 V.2 n).inv.app W s) = s :=
    Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app
      ((twD A).chartData.chartIso V.1 V.2 n) W s
  have a4 : (P.thetaPush n).app ((relativeProj A).chart V.1 V.2 ''ᵁ W)
      (((twD A).chartData.chartIso V.1 V.2 n).inv.app W s) =
      (P.chartTargetHom V.1 V.2 n).app W
        ((Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.pushTheta (A.grading V.1)
          (P.affineDatum V.1) n).app W s) :=
    (P.thetaPush_app_chart V.1 V.2 n W _).trans ((P.thetaLoc_app V.1 V.2 n W _).trans
      (congrArg (fun z => (P.chartTargetHom V.1 V.2 n).app W
        ((Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.pushTheta (A.grading V.1)
          (P.affineDatum V.1) n).app W z)) hs))
  have a5 := P.targetIso_hom_pullbackSection V j hjι n W h4 ((P.chartTargetHom V.1 V.2 n).app W
    ((Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.pushTheta (A.grading V.1)
      (P.affineDatum V.1) n).app W s))
  have a6 := P.lam_chartTargetHom_app V.1 V.2 n W
    ((Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.pushTheta (A.grading V.1)
      (P.affineDatum V.1) n).app W s)
  have rhs := Stacks.AlgebraicGeometry.ProjChartGradedTriple.theta_app_pullbackSection
    (P.affineDatum V.1) n W s
  refine Eq.trans ?_ rhs.symm
  refine Eq.trans (congrArg (fun z =>
    (Triple.targetIso P
        ⟨P.coveringOpen, P.globalMorphism (relativeProj A), GradedNonnegHom.ofHom P.theta⟩ V j hjι
      n).hom.val.app (op ((P.affineDatum V.1).glued ⁻¹ᵁ W))
      (((Scheme.Modules.pullback j).map (P.theta.app n)).val.app
        (op ((P.affineDatum V.1).glued ⁻¹ᵁ W)) z)) a1) ?_
  refine Eq.trans (congrArg (fun z =>
    (Triple.targetIso P
        ⟨P.coveringOpen, P.globalMorphism (relativeProj A), GradedNonnegHom.ofHom P.theta⟩ V j hjι
      n).hom.val.app (op ((P.affineDatum V.1).glued ⁻¹ᵁ W)) z) a2) ?_
  refine Eq.trans (congrArg (fun z =>
    (Triple.targetIso P
        ⟨P.coveringOpen, P.globalMorphism (relativeProj A), GradedNonnegHom.ofHom P.theta⟩ V j hjι
      n).hom.val.app (op ((P.affineDatum V.1).glued ⁻¹ᵁ W))
      (pullbackSection j ((tensorPowerModule T P.L n).restrict P.coveringOpen.ι) _ _ h4 z))
    (a3.trans a4)) ?_
  exact a5.trans a6

/-- **Clause (3) of [Stacks, Tag 01O9] for `(U(ψ), r_{ℒ,ψ}, θ)`, in full**: for every affine open
`V` of the base, `U(ψ) ∩ f^{-1}(V) = U(ψ')`, the inclusion `j : U(ψ') ⟶ U(ψ)` satisfies
`j ≫ r_{ℒ,ψ} = r_{ℒ|_{f^{-1}(V)}, ψ'} ≫ i_V`, and the inverse image of `θ` along `j` is
[Stacks, Tag 01NK]'s `θ` for the induced datum `ψ'`, in every degree. -/
theorem isClauseThree_theta :
    Triple.IsClauseThree P
        ⟨P.coveringOpen, P.globalMorphism (relativeProj A), GradedNonnegHom.ofHom P.theta⟩ :=
  fun V => ⟨P.image_coveringOpen_affineDatum_eq V.2, fun j hjι =>
    ⟨P.comp_globalMorphism_eq (relativeProj A) V j hjι, fun n =>
      P.theta_clauseThree_app V j hjι n⟩⟩

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
