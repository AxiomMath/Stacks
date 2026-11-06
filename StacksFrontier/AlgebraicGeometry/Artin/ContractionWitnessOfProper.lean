module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionRepresents
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionModification
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionModificationEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismsFromProperModificationExistence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalModificationBaseChangeAdic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionLift
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation

/-!
# Compatibility of a triple from a proper modification that need not be cartesian

In the situation of Stacks 0GH8, recorded by `AlgebraicGeometry.Artin.ContractionSituation`,
the compatibility condition on a triple `(Z, u', x̂)` over a locally Noetherian scheme `V` asks
for a witness `V' ⟶ V`, `x̂'`, `x'`
(`AlgebraicGeometry.Artin.ContractionSituation.CompatibilityWitness`) whose completion square
`V'_{/Z} = V_{/Z} ×_{x̂, W, g} X'_{/T'}` is *cartesian*. This file shows that the cartesian
condition can be dropped when testing compatibility: it suffices to have *some* proper morphism
`q : Y ⟶ V` of algebraic spaces which is an isomorphism over `V ∖ Z`, together with a morphism
`y : Y ⟶ X'` restricting to `u'` over `V ∖ Z` and satisfying `g ∘ y_{/Z} = x̂ ∘ q_{/Z}`.

This is the step that the source leaves to the reader at the end of the proof of Stacks 0GI5
("the compatibility will be witnessed by the proper morphism `V'_μ ⟶ V_μ` and the morphisms
`x'_μ` and `x̂'_μ = x'_{μ,/Z_μ}`"): there the proper morphism descended to a finite stage is not
known to have a cartesian completion square, and this lemma is what makes it a witness anyway.

## The argument

1. The base change `V_{/Z} ×_{x̂, W, g} X'_{/T'} ⟶ V_{/Z}` of the formal modification `g` along the
   adic morphism `x̂` is a formal modification (Stacks 0GDN).
2. By the main theorem on dilatations it is the completion of a proper `p : V' ⟶ V` which is an
   isomorphism over `V ∖ Z` (Stacks 0GDU, existence).
3. The pair `(y_{/Z}, q_{/Z})` is a morphism `Y_{/Z} ⟶ V_{/Z} ×_W X'_{/T'} ≅ V'_{/Z}` over
   `V_{/Z}`, so it is the completion of a morphism `h : Y ⟶ V'` over `V` (Stacks 0GDR).
4. `h` is proper and an isomorphism over `V' ∖ p⁻¹Z`, so `y` and the projection
   `V'_{/Z} ⟶ X'_{/T'}` glue to `x' : V' ⟶ X'` (Stacks 0GI3), and `(V', p, x')` is a witness.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.nonempty_compatibilityWitness_of_isProper`:
  compatibility from a proper modification with the two restriction conditions.
* `AlgebraicGeometry.Artin.ContractionSituation.completionSheafRestrict_comp_xhat_eq_of_hom`: two
  witnesses related by a morphism over `V` compatible with the morphisms to `X'` force the two
  formal components to agree on the first witness.
* `AlgebraicGeometry.Artin.ContractionSituation.isPullback_id_of_isIso_pullback_snd` and
  `AlgebraicGeometry.Artin.ContractionSituation.isIso_pullback_snd_of_isPullback`: two pieces of
  pullback bookkeeping used for the isomorphism-over-the-open conditions.

## References

* [Stacks Project, Tag 0GDN](https://stacks.math.columbia.edu/tag/0GDN)
* [Stacks Project, Tag 0GDR](https://stacks.math.columbia.edu/tag/0GDR)
* [Stacks Project, Tag 0GDU](https://stacks.math.columbia.edu/tag/0GDU)
* [Stacks Project, Tag 0GI3](https://stacks.math.columbia.edu/tag/0GI3)
* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_ContractionWitnessOfProper
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ContractionWitnessOfProper
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of fppf sheaves (instance search times out without this shortcut). -/
local instance hasPullbacks_fppfSheaf_ContractionWitnessOfProper
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks (FormalSpace.FppfSheaf B S hS) := inferInstance

local instance (priority := high) hasPullback_fppfSheaf_ContractionWitnessOfProper
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : FormalSpace.FppfSheaf B S hS} (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism `j : U ⟶ V'` over `U ⟶ V` is the identification of `U` with the fibre product
`U ×_V V'` as soon as the second projection of that fibre product is an isomorphism. -/
theorem isPullback_id_of_isIso_pullback_snd {C : Type*} [Category C] [HasPullbacks C]
    {U V V' : C} (ι : U ⟶ V) (p : V' ⟶ V) [IsIso (pullback.snd p ι)] (j : U ⟶ V')
    (hj : j ≫ p = ι) : IsPullback (𝟙 U) j ι p := by
  have hσ : pullback.lift j (𝟙 U) (by rw [hj, Category.id_comp]) = inv (pullback.snd p ι) := by
    rw [← cancel_mono (pullback.snd p ι), IsIso.inv_hom_id, pullback.lift_snd]
  refine IsPullback.of_iso (IsPullback.of_hasPullback p ι).flip (asIso (pullback.snd p ι))
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · have hj' : j = inv (pullback.snd p ι) ≫ pullback.fst p ι := by
      rw [← hσ, pullback.lift_fst]
    rw [Iso.refl_hom, Category.comp_id, asIso_hom, hj', IsIso.hom_inv_id_assoc]
  · simp
  · simp

/-- Over a cartesian square `U₃ = V₃ ×_V U`, a morphism `h : Y ⟶ V₃` is an isomorphism over `U₃`
as soon as `V₃ ⟶ V` and the composite `Y ⟶ V` are isomorphisms over `U`. -/
theorem isIso_pullback_snd_of_isPullback {C : Type*} [Category C] [HasPullbacks C]
    {Y V₃ V U₃ U : C} (h : Y ⟶ V₃) (p : V₃ ⟶ V) {ι₃ : U₃ ⟶ V₃} {r : U₃ ⟶ U} {ι : U ⟶ V}
    (hsq : IsPullback ι₃ r p ι) [IsIso (pullback.snd p ι)] {q : Y ⟶ V} (hq : h ≫ p = q)
    [IsIso (pullback.snd q ι)] : IsIso (pullback.snd h ι₃) := by
  subst hq
  have hr : IsIso r := by
    rw [← hsq.isoPullback_hom_snd]
    infer_instance
  have hpaste := (IsPullback.of_hasPullback h ι₃).paste_vert hsq
  have hc : IsIso (pullback.snd h ι₃ ≫ r) := by
    rw [← hpaste.isoPullback_hom_snd]
    infer_instance
  exact IsIso.of_isIso_comp_right _ r

variable (c : ContractionSituation B S hS)

/-- **Compatibility from a proper modification that need not be cartesian.** In the situation of
Stacks 0GH8 let `V` be a locally Noetherian scheme over `S`, let `Z ⊆ |V|` be closed, and let
`u' : V ∖ Z ⟶ U'` and an adic `x̂ : V_{/Z} ⟶ W` be given. Suppose there are a proper morphism
`q : Y ⟶ V` of algebraic spaces which is an isomorphism over `V ∖ Z` (with section `jY` over
`V ∖ Z`) and a morphism `y : Y ⟶ X'` restricting to `u'` over `V ∖ Z`, carrying `|q|⁻¹ Z` into
`T'`, and with `g ∘ y_{/Z} = x̂ ∘ q_{/Z}`. Then `u'` and `x̂` are compatible.

The square need not be cartesian: the witness is the dilatation `V' ⟶ V` of the formal
modification `V_{/Z} ×_{x̂, W, g} X'_{/T'} ⟶ V_{/Z}` (Stacks 0GDN, 0GDU); the morphism of formal
modifications `Y_{/Z} ⟶ V'_{/Z}` given by `(q_{/Z}, y_{/Z})` comes from a morphism `h : Y ⟶ V'`
over `V` (Stacks 0GDR); and `y` together with the projection `V'_{/Z} ⟶ X'_{/T'}` glues along the
proper modification `h` to `x' : V' ⟶ X'` (Stacks 0GI3). -/
theorem nonempty_compatibilityWitness_of_isProper {V : BigFppfOver B S hS}
    (hVN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V))
    {Z : Set (Space.points B S hS (yoneda.obj V))} (hZ : IsClosed Z)
    (u : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor)
    (xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W)
    (hxhat : FormalSpace.IsAdicMorphism B S hS xhat)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (q : Y ⟶ yoneda.obj V) (hq : Space.IsProper B S hS q)
    (hqU : IsIso (pullback.snd q (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι))
    (jY : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ Y)
    (hjY : jY ≫ q = (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι)
    (y : Y ⟶ c.X') (hy : jY ≫ y = u ≫ c.U'.ι)
    (hT : Space.pointsMap B S hS Y q ⁻¹' Z ⊆ Space.pointsMap B S hS Y y ⁻¹' c.T')
    (hformal : Space.completionSheafRestrict B S hS q (Space.pointsMap B S hS Y q ⁻¹' Z) Z
        (fun _ hz => hz) ≫ xhat =
      Space.completionSheafRestrict B S hS y (Space.pointsMap B S hS Y q ⁻¹' Z) c.T' hT ≫ c.g) :
    Nonempty (CompatibilityWitness c V Z u xhat) := by
  have hVsp := isAlgebraicSpace_yoneda B S hS V
  have hVN' := Space.isLocallyNoetherian_yoneda B S hS V hVN
  have hVet := FormalSpace.hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyNoetherian hVsp
    hVN'
  -- the formal modification `V_{/Z} ×_{x̂, W, g} X'_{/T'} ⟶ V_{/Z}` (Stacks 0GDN)
  have h𝔣 : FormalSpace.IsFormalModification B S hS (pullback.snd c.g xhat) :=
    FormalSpace.isFormalModification_pullback_snd_of_isAdicMorphism B S hS c.g xhat
      (FormalSpace.isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian hVsp hVN' Z hZ)
      hxhat c.isFormalModification_g
  -- its dilatation (Stacks 0GDU)
  obtain ⟨V₃, hV₃, p, hp, hpU, ⟨e⟩⟩ :=
    FormalSpace.exists_isProper_completion_iso_of_isFormalModification hVsp hVN' Z hZ h𝔣
  -- the morphism `Y_{/Z} ⟶ V_{/Z} ×_W X'_{/T'}` given by `(y_{/Z}, q_{/Z})`
  let κ : Space.completionSheaf B S hS Y (Space.pointsMap B S hS Y q ⁻¹' Z) ⟶
      pullback c.g xhat :=
    pullback.lift (Space.completionSheafRestrict B S hS y _ c.T' hT)
      (Space.completionSheafRestrict B S hS q _ Z (fun _ hz => hz)) hformal.symm
  have hκ : κ ≫ pullback.snd c.g xhat = Space.completionSheafMap B S hS q Z := by
    rw [pullback.lift_snd]
    exact Space.completionSheafRestrict_self B S hS q Z _
  let eL : Space.completionSheaf B S hS V₃ (Space.pointsMap B S hS V₃ p ⁻¹' Z) ≅
      pullback c.g xhat :=
    (Over.forget _).mapIso e
  have heinv : eL.inv ≫ eL.hom = 𝟙 _ := eL.inv_hom_id
  have hehom : eL.hom ≫ pullback.snd c.g xhat = Space.completionSheafMap B S hS p Z :=
    Over.w e.hom
  have hw : eL.inv ≫ Space.completionSheafMap B S hS p Z = pullback.snd c.g xhat :=
    Over.w e.inv
  let α : (Space.completionOverFunctor B S hS Z).obj (Over.mk q) ⟶
      (Space.completionOverFunctor B S hS Z).obj (Over.mk p) :=
    Over.homMk (κ ≫ eL.inv) (by
      exact (Category.assoc _ _ _).trans ((congrArg (κ ≫ ·) hw).trans hκ))
  -- it comes from a morphism `h : Y ⟶ V'` over `V` (Stacks 0GDR)
  have hYet := Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hY hVsp q hq.2.1.1 hVet
  have hV₃et := Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hV₃ hVsp p hp.2.1.1
    hVet
  obtain ⟨a, ha⟩ := (Space.completionOverFunctor_map_bijective hVsp hVet hZ hV₃ hp.2.1.1 hpU q hY
    hYet).2 α
  let h : Y ⟶ V₃ := a.left
  have hh : h ≫ p = q := Over.w a
  have hcompl : Space.completionOverMap B S hS Z a = κ ≫ eL.inv :=
    congrArg (fun b => b.left) ha
  -- `h` is a proper modification of `V'` along `|p|⁻¹ Z`
  have hZ₃ : IsClosed (Space.pointsMap B S hS V₃ p ⁻¹' Z) :=
    hZ.preimage (Space.continuous_pointsMap B S hS p)
  have hhproper : Space.IsProper B S hS h :=
    Space.isProper_of_comp_of_isSeparated B S hS hY hV₃ hVsp h p (hh ▸ hq) hp.1
  have hsq := FormalSpace.isPullback_ι_openSubspaceOfPoints_compl B S hS p Z
    (Space.openSubspaceOfPointsRestrict B S hS p _ Zᶜ (fun _ hz => hz)) rfl
  have := hpU
  have := hqU
  have hhU := isIso_pullback_snd_of_isPullback h p hsq hh
  -- the formal morphism `V'_{/Z} ⟶ X'`, read on the completion subfunctor
  let μ : Space.completionSheaf B S hS V₃ (Space.pointsMap B S hS V₃ p ⁻¹' Z) ⟶
      Space.completionSheaf B S hS c.X' c.T' :=
    eL.hom ≫ pullback.fst c.g xhat
  have hX'sh := c.isAlgebraicSpace_X'.isSheaf
  let ŵ : (Space.completionSubfunctor B S hS V₃ (Space.pointsMap B S hS V₃ p ⁻¹' Z)).toFunctor ⟶
      c.X' ⋙ uliftFunctor.{u + 1} :=
    (BigFppfOver.topology B S hS).toSheafify _ ≫ μ.hom ≫
      ((BigFppfOver.topology B S hS).isoSheafify
        (Space.isSheaf_completionSubfunctor B S hS hX'sh c.T')).inv ≫
        (Space.completionSubfunctor B S hS c.X' c.T').ι
  have hŵ : ŵ ≫ (BigFppfOver.topology B S hS).toSheafify (c.X' ⋙ uliftFunctor.{u + 1}) =
      (BigFppfOver.topology B S hS).toSheafify _ ≫
        (μ ≫ Space.completionSheafInclusion B S hS c.X' c.T').hom := by
    have hnat : ((BigFppfOver.topology B S hS).isoSheafify
        (Space.isSheaf_completionSubfunctor B S hS hX'sh c.T')).hom ≫
          (Space.completionSheafInclusion B S hS c.X' c.T').hom =
        (Space.completionSubfunctor B S hS c.X' c.T').ι ≫
          (BigFppfOver.topology B S hS).toSheafify (c.X' ⋙ uliftFunctor.{u + 1}) :=
      ((BigFppfOver.topology B S hS).toSheafify_naturality _).symm
    have hiso : ((BigFppfOver.topology B S hS).isoSheafify
        (Space.isSheaf_completionSubfunctor B S hS hX'sh c.T')).inv ≫
          (Space.completionSubfunctor B S hS c.X' c.T').ι ≫
            (BigFppfOver.topology B S hS).toSheafify (c.X' ⋙ uliftFunctor.{u + 1}) =
        (Space.completionSheafInclusion B S hS c.X' c.T').hom :=
      (Iso.inv_comp_eq _).2 hnat.symm
    simp only [ŵ, Category.assoc]
    exact congrArg (fun k => (BigFppfOver.topology B S hS).toSheafify _ ≫ μ.hom ≫ k) hiso
  -- the sheaf-level compatibility of `y` with `μ`
  have hE := Space.preimage_pointsMap_over B S hS Z a
  have h1 : Space.completionSheafMap B S hS h (Space.pointsMap B S hS V₃ p ⁻¹' Z) =
      eqToHom (congrArg (Space.completionSheaf B S hS Y) hE.symm) ≫ κ ≫ eL.inv := by
    rw [← hcompl]
    simp [Space.completionOverMap, h]
  have hfst : κ ≫ pullback.fst c.g xhat = Space.completionSheafRestrict B S hS y _ c.T' hT :=
    pullback.lift_fst _ _ _
  have hκμ : (κ ≫ eL.inv) ≫ μ = Space.completionSheafRestrict B S hS y _ c.T' hT := by
    have h2 : eL.inv ≫ eL.hom ≫ pullback.fst c.g xhat = pullback.fst c.g xhat :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ pullback.fst c.g xhat) heinv).trans (Category.id_comp _))
    exact (Category.assoc _ _ _).trans ((congrArg (κ ≫ ·) h2).trans hfst)
  have hkey : Space.completionSheafMap B S hS h (Space.pointsMap B S hS V₃ p ⁻¹' Z) ≫ μ ≫
        Space.completionSheafInclusion B S hS c.X' c.T' =
      Space.completionSheafInclusion B S hS Y
          (Space.pointsMap B S hS Y h ⁻¹' (Space.pointsMap B S hS V₃ p ⁻¹' Z)) ≫
        Space.sheafifiedULiftMap B S hS y := by
    rw [h1, Category.assoc, ← Category.assoc (κ ≫ eL.inv), hκμ,
      Space.completionSheafRestrict_comp_inclusion, ← Category.assoc]
    exact congrArg (· ≫ Space.sheafifiedULiftMap B S hS y)
      (Space.completionSheafInclusion_transport B S hS Y hE.symm)
  -- the compatibility hypothesis of Stacks 0GI3 for `h`, `y` and the formal morphism
  have hcompat : Space.completionMap B S hS h (Space.pointsMap B S hS V₃ p ⁻¹' Z) ≫ ŵ =
      (Space.completionSubfunctor B S hS Y
          (Space.pointsMap B S hS Y h ⁻¹' (Space.pointsMap B S hS V₃ p ⁻¹' Z))).ι ≫
        Functor.whiskerRight y uliftFunctor.{u + 1} := by
    have : IsIso ((BigFppfOver.topology B S hS).toSheafify (c.X' ⋙ uliftFunctor.{u + 1})) :=
      (BigFppfOver.topology B S hS).isIso_toSheafify
        (FormalSpace.isSheaf_comp_uliftFunctor B S hS c.isAlgebraicSpace_X')
    have hnat : Space.completionMap B S hS h (Space.pointsMap B S hS V₃ p ⁻¹' Z) ≫
          (BigFppfOver.topology B S hS).toSheafify _ =
        (BigFppfOver.topology B S hS).toSheafify _ ≫
          (Space.completionSheafMap B S hS h (Space.pointsMap B S hS V₃ p ⁻¹' Z)).hom :=
      (BigFppfOver.topology B S hS).toSheafify_naturality _
    haveI : Mono ((BigFppfOver.topology B S hS).toSheafify (c.X' ⋙ uliftFunctor.{u + 1})) :=
      IsIso.mono_of_iso _
    rw [← cancel_mono ((BigFppfOver.topology B S hS).toSheafify (c.X' ⋙ uliftFunctor.{u + 1}))]
    refine (Category.assoc _ _ _).trans
      ((congrArg (Space.completionMap B S hS h (Space.pointsMap B S hS V₃ p ⁻¹' Z) ≫ ·) hŵ).trans
        ?_)
    refine ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (μ ≫ Space.completionSheafInclusion B S hS c.X' c.T').hom) hnat).trans
        (Category.assoc _ _ _))).trans ?_
    have h3 := congrArg (fun k => (BigFppfOver.topology B S hS).toSheafify
      (Space.completionSubfunctor B S hS Y
        (Space.pointsMap B S hS Y h ⁻¹' (Space.pointsMap B S hS V₃ p ⁻¹' Z))).toFunctor ≫ k.hom)
      hkey
    exact h3.trans ((Solution.toSheafify_comp_completionSheafInclusion (X := c.X') _ y).trans
      (Category.assoc _ _ _).symm)
  -- the glued morphism `x' : V' ⟶ X'` (Stacks 0GI3)
  obtain ⟨x', hx'⟩ := Space.exists_morToModificationCompletion_eq B S hS hV₃ hY
    c.isAlgebraicSpace_X' hV₃et hZ₃ h hhproper hhU y ŵ hcompat
  have hx1 : h ≫ x' = y := congrArg Prod.fst hx'
  have hx2 : (Space.completionSubfunctor B S hS V₃ (Space.pointsMap B S hS V₃ p ⁻¹' Z)).ι ≫
      Functor.whiskerRight x' uliftFunctor.{u + 1} = ŵ := congrArg Prod.snd hx'
  -- the witness
  have hcompl_p : eL.hom ≫ pullback.snd c.g xhat =
      Space.completionSheafRestrict B S hS p (Space.pointsMap B S hS V₃ p ⁻¹' Z) Z
        (fun _ hz => hz) :=
    hehom.trans (Space.completionSheafRestrict_self B S hS p Z _).symm
  refine ⟨{ V' := V₃
            isAlgebraicSpace_V' := hV₃
            p := p
            isProper_p := hp
            j := jY ≫ h
            isPullback_j := isPullback_id_of_isIso_pullback_snd _ p (jY ≫ h)
              (by rw [Category.assoc, hh, hjY])
            xhat' := μ
            isPullback_xhat' := ?_
            x' := x'
            restrict_x' := by rw [Category.assoc, hx1, hy]
            completion_x' := ?_ }⟩
  · refine (IsPullback.of_iso_pullback ⟨?_⟩ eL rfl hcompl_p).flip
    rw [← hcompl_p]
    exact (Category.assoc _ _ _).trans ((congrArg (eL.hom ≫ ·) pullback.condition).trans
      (Category.assoc _ _ _).symm)
  · refine Sheaf.hom_ext ((BigFppfOver.topology B S hS).sheafify_hom_ext _ _
      (Space.sheafifiedULift B S hS c.X').property ?_)
    exact (Solution.toSheafify_comp_completionSheafInclusion (X := c.X') _ x').trans
      (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hx2)).trans hŵ)

/-- **Two witnesses related by a morphism force the two formal components to agree on the first.**
Let `(V'₁, x'₁)` and `(V'₂, x'₂)` witness the compatibility of `u'` with `x̂₁` and with `x̂₂`, over
the same `V` and `Z`. If `a : V'₁ ⟶ V'₂` is a morphism over `V` with `x'₂ ∘ a = x'₁`, then `x̂₁`
and `x̂₂` agree after restriction to `V'_{1,/Z}`: both are `g ∘ x̂'₁` there (the two second
components `u'₁`, `u'₂` play no role and need not agree), by the two cartesian completion squares
and the monomorphism `X'_{/T'} ⟶ X'`. -/
theorem completionSheafRestrict_comp_xhat_eq_of_hom {V : BigFppfOver B S hS}
    {Z : Set (Space.points B S hS (yoneda.obj V))}
    {u₁ u₂ : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor}
    {xhat₁ xhat₂ : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W}
    (w₁ : CompatibilityWitness c V Z u₁ xhat₁) (w₂ : CompatibilityWitness c V Z u₂ xhat₂)
    (a : w₁.V' ⟶ w₂.V') (hap : a ≫ w₂.p = w₁.p) (hax : a ≫ w₂.x' = w₁.x') :
    Space.completionSheafRestrict B S hS w₁.p (Space.pointsMap B S hS w₁.V' w₁.p ⁻¹' Z) Z
        (fun _ hz => hz) ≫ xhat₁ =
      Space.completionSheafRestrict B S hS w₁.p (Space.pointsMap B S hS w₁.V' w₁.p ⁻¹' Z) Z
        (fun _ hz => hz) ≫ xhat₂ := by
  have hsub : Space.pointsMap B S hS w₁.V' w₁.p ⁻¹' Z ⊆
      Space.pointsMap B S hS w₁.V' a ⁻¹' (Space.pointsMap B S hS w₂.V' w₂.p ⁻¹' Z) := by
    intro x hx
    show Space.pointsMap B S hS w₂.V' w₂.p (Space.pointsMap B S hS w₁.V' a x) ∈ Z
    rw [← Space.pointsMap_comp_apply, hap]
    exact hx
  let ah := Space.completionSheafRestrict B S hS a _ _ hsub
  have hfac : Space.completionSheafRestrict B S hS w₁.p
      (Space.pointsMap B S hS w₁.V' w₁.p ⁻¹' Z) Z (fun _ hz => hz) =
        ah ≫ Space.completionSheafRestrict B S hS w₂.p
          (Space.pointsMap B S hS w₂.V' w₂.p ⁻¹' Z) Z (fun _ hz => hz) := by
    have hpq : Space.pointsMap B S hS w₁.V' w₁.p ⁻¹' Z ⊆
        Space.pointsMap B S hS w₁.V' (a ≫ w₂.p) ⁻¹' Z := by rw [hap]
    exact (Space.completionSheafRestrict_congr B S hS hap.symm _ _ _ hpq).trans
      (Space.completionSheafRestrict_comp B S hS a w₂.p _ _ Z hsub (fun _ hz => hz) hpq)
  have hxhat' : ah ≫ w₂.xhat' = w₁.xhat' := by
    have := Space.mono_completionSheafInclusion B S hS c.X' c.T'
    rw [← cancel_mono (Space.completionSheafInclusion B S hS c.X' c.T'), Category.assoc,
      ← w₂.completion_x', ← w₁.completion_x', ← Category.assoc,
      Space.completionSheafRestrict_comp_inclusion, Category.assoc,
      ← Space.sheafifiedULiftMap_comp, hax]
  rw [w₁.isPullback_xhat'.w, hfac, Category.assoc, w₂.isPullback_xhat'.w, ← Category.assoc,
    hxhat']

end AlgebraicGeometry.Artin.ContractionSituation

end
