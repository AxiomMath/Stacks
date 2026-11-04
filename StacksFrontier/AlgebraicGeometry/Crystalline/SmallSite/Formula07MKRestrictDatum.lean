module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChangeBaseIsoEquivalence
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Formula07MKRestrict
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SituationRestrict

/-!
# Transporting `Cris(U_W/T_W)` onto the small site of the restricted situation

Let `(U', T', δ')` be an object of `Cris(X'/S')` and let `W` be an open of `T'`.  The remark
[Stacks, Tag 07MJ] attaches to `(U', T', δ')` the crystalline situation `U/T`, and
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Formula07MKRestrict.lean` compares it with
the situation attached to `(U', T', δ')|_W`: the divided power base `S ×_{S'} (T'|_W)` is the
restriction of `T = S ×_{S'} T'` to `g⁻¹W`, for `g : T ⟶ T'` the second projection
(`...pullbackBaseRestrictOpenIso`), and the scheme `X ×_{X'} (U'|_{W₀})` is the restriction of
`U = X ×_{X'} U'` to the preimage of `W₀ = U' ∩ W` (`...pullbackSourceRestrictOpenIso`).

Those two comparisons are a change of divided power base, [Stacks, Tag 07IC], only once their
**compatibility with the two structure morphisms to the closed fibres** is known, and that is what
this file supplies: `pullbackSituationRestrict_changeBase_condition`.  Both comparison morphisms
being isomorphisms, `Crystalline.GlobalCrystallineSituation.smallChangeBaseEquivalenceOfIsIso`
then makes change of base an equivalence of the two small crystalline sites.

## The computation

The datum is an equation of morphisms into the closed fibre of the divided power fibre product
`S ×_{S'} (T'|_W)`.  That scheme is only a closed subscheme of the fibre product of the underlying
schemes, so the two sides cannot be compared projection by projection on `T`; but their closed
fibre **is** an honest fibre product, by [Stacks, Tag 07ME]
(`...DividedPowerScheme.closedFiberPullbackComparison_isIso`), so they can be compared there.

* On the first projection the datum is the compatibility datum of the restricted situation itself,
  `Crystalline.GlobalCrystallineSituation.restrict_changeBase_condition`, followed by
  `...pullbackToClosedFiber_comp_fst`.
* On the second projection both sides become, after composing with the two monomorphisms
  `T'|_W ↪ T'` and the closed fibre inclusion, the composite `V ↪ U ⟶ U' ↪ T'`; the left-hand
  route uses `...restrict_sourceToBase` and
  `...sourceToBase_pullbackSituation_comp_snd`, the right-hand one
  `AlgebraicGeometry.morphismRestrict_ι` twice.

## The types of the restricted morphisms

`Crystalline.GlobalCrystallineSituation.restrict`, `...pullbackSituation` and
`...CrystallineThickening.restrictOpen` are plain `def`s, so `(restrict ...).S`,
`(pullbackSituation ...).X` and `(A'.restrictOpen W).obj.thickening.target.scheme` do not reduce
at the transparency the rewriting tactics run at — a `rw` whose motive mentions them is rejected
as not type-correct.  Every statement below is therefore phrased with the fibre products and the
open immersions **named at the types they have**: `restrictOpenTargetι`, `restrictOpenSourceι`,
`pullbackSourceRestrictSnd` and `pullbackSituationRestrictToClosedFiber`.  The passage to the
types of the two situations is left to elaboration, in
`pullbackSituationRestrict_changeBase_condition`.  Compare `...restrictXι` and `...restrictSι` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/SituationRestrict.lean`, which solve the same
problem for the restriction of a situation.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation`.

* `pullbackSituationRestrict` — the situation `U/T` restricted to `g⁻¹W` and to the open of `U`
  above it.
* `pullbackSituationRestrictEquivalence` — **`Cris((U/T)|_{g⁻¹W}) ≌ Cris(U_W/T_W)`.**
* `pullbackSituationRestrictEssImageEquivalence` — hence `Cris(U_W/T_W)` is the full subcategory
  of `Cris(U/T)` on the objects whose thickened scheme lies in the open of `U` above `g⁻¹W`.

## Main results

* `pullbackSituationRestrict_changeBase_condition` — **the compatibility datum**, and
  `pullbackSituationRestrictToClosedFiber_comp_closedFiberMap` the same equation with the fibre
  products named directly.
* `pullbackSituationRestrictToClosedFiber_comp_fst` and `...comp_snd` — the datum read on the two
  projections of the closed fibre.

## What is and is not proved

(07MK) is **not** proved and no `@[stacks]` attribute is placed; as in
`Formula07MKRestrict.lean`, what is proved is the geometric and site-level comparison that the
sheaf-level statement needs, not the equation of sheaves.  Nothing here compares the direct image
computed on one site with the one computed on the other: the equivalence of sites is available,
but the identification of `Rτ_*` across it is not carried out.  The *underived* half of that —
the two global sections functors identified across the equivalence — is
`Crystalline.GlobalCrystallineSituation.SmallSite.pullbackSituationRestrictGlobalSectionsIso` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Formula07MKRestrictSections.lean`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

open DividedPowerScheme

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (A' : CrystallineThickening S') (W : A'.obj.thickening.target.scheme.Opens)

/-- The open `g⁻¹W` of `T = S ×_{S'} T'`. -/
abbrev pullbackBaseOpen : (pullbackBase S S' fS A').scheme.Opens :=
  (pullback.snd fS A'.obj.toBase).hom ⁻¹ᵁ W

/-- The open `q⁻¹W₀` of `U = X ×_{X'} U'`. -/
abbrev pullbackSourceOpen : (pullbackSource S S' fX A').Opens :=
  pullback.snd fX A'.obj.toX ⁻¹ᵁ (A'.obj.thickening.immersion ⁻¹ᵁ W)

/-- The open immersion `W ⟶ T'`, at the type it has out of the ambient scheme of
`(U', T', δ')|_W`. -/
def restrictOpenTargetι :
    (A'.restrictOpen W).obj.thickening.target.scheme ⟶ A'.obj.thickening.target.scheme :=
  W.ι

/-- The morphism `restrictOpenTargetι` is an open immersion. -/
instance isOpenImmersion_restrictOpenTargetι : IsOpenImmersion (restrictOpenTargetι S' A' W) :=
  inferInstanceAs (IsOpenImmersion W.ι)

/-- The open immersion `W₀ ⟶ U'`, at the type it has out of the thickened scheme of
`(U', T', δ')|_W`. -/
def restrictOpenSourceι :
    (A'.restrictOpen W).obj.thickening.source ⟶ A'.obj.thickening.source :=
  (A'.obj.thickening.immersion ⁻¹ᵁ W).ι

/-- The restriction of the immersion of `(U', T', δ')` to `W` is the immersion of
`(U', T', δ')|_W`, read through the two open immersions named above. -/
theorem restrictOpen_immersion_restrictOpenTargetι :
    (A'.restrictOpen W).obj.thickening.immersion ≫ restrictOpenTargetι S' A' W =
      restrictOpenSourceι S' A' W ≫ A'.obj.thickening.immersion :=
  morphismRestrict_ι A'.obj.thickening.immersion W

/-- The second projection `U ⟶ U'` restricted to the two opens, at the type it has into the
thickened scheme of `(U', T', δ')|_W`. -/
def pullbackSourceRestrictSnd :
    (pullbackSourceOpen S S' fX A' W).toScheme ⟶ (A'.restrictOpen W).obj.thickening.source :=
  pullback.snd fX A'.obj.toX ∣_ (A'.obj.thickening.immersion ⁻¹ᵁ W)

/-- The restricted second projection is a morphism over the second projection. -/
theorem pullbackSourceRestrictSnd_restrictOpenSourceι :
    pullbackSourceRestrictSnd S S' fX A' W ≫ restrictOpenSourceι S' A' W =
      (pullbackSourceOpen S S' fX A' W).ι ≫ pullback.snd fX A'.obj.toX :=
  morphismRestrict_ι (pullback.snd fX A'.obj.toX) (A'.obj.thickening.immersion ⁻¹ᵁ W)

/-! ### The two comparisons read against the projections -/

/-- The comparison of divided power bases, followed by the projection to `S`. -/
theorem pullbackBaseRestrictOpenIso_hom_fst :
    (pullbackBaseRestrictOpenIso S S' fS A' W).hom ≫
        pullback.fst fS (A'.restrictOpen W).obj.toBase =
      (pullbackBase S S' fS A').restrictι (pullbackBaseOpen S S' fS A' W) ≫
        pullback.fst fS A'.obj.toBase :=
  (isPullback_pullbackBase_restrictOpen S S' fS A' W).flip.isoPullback_hom_fst

/-- The comparison of divided power bases, followed by the projection to `T'|_W`. -/
theorem pullbackBaseRestrictOpenIso_hom_snd :
    (pullbackBaseRestrictOpenIso S S' fS A' W).hom ≫
        pullback.snd fS (A'.restrictOpen W).obj.toBase =
      (pullback.snd fS A'.obj.toBase).restrictPreimage W :=
  (isPullback_pullbackBase_restrictOpen S S' fS A' W).flip.isoPullback_hom_snd

/-- The comparison of divided power bases, followed by the projection to `T'|_W` and the
restriction morphism of `T'`. -/
theorem pullbackBaseRestrictOpenIso_hom_snd_restrictι :
    ((pullbackBaseRestrictOpenIso S S' fS A' W).hom ≫
          pullback.snd fS (A'.restrictOpen W).obj.toBase) ≫
        A'.obj.thickening.target.restrictι W =
      (pullbackBase S S' fS A').restrictι (pullbackBaseOpen S S' fS A' W) ≫
        pullback.snd fS A'.obj.toBase :=
  (congrArg (· ≫ A'.obj.thickening.target.restrictι W)
      (pullbackBaseRestrictOpenIso_hom_snd S S' fS A' W)).trans
    (Hom.restrictPreimage_restrictι (pullback.snd fS A'.obj.toBase) W)

/-- `pullbackBaseRestrictOpenIso_hom_snd_restrictι` on underlying schemes, with the two open
immersions named at the types they have. -/
theorem pullbackBaseRestrictOpenIso_hom_snd_hom_ι :
    ((pullbackBaseRestrictOpenIso S S' fS A' W).hom ≫
          pullback.snd fS (A'.restrictOpen W).obj.toBase).hom ≫ restrictOpenTargetι S' A' W =
      ((pullbackBase S S' fS A').restrictι (pullbackBaseOpen S S' fS A' W)).hom ≫
        (pullback.snd fS A'.obj.toBase).hom :=
  congrArg DividedPowerScheme.Hom.hom
    (pullbackBaseRestrictOpenIso_hom_snd_restrictι S S' fS A' W)

/-- The comparison of schemes, followed by the projection to `X`. -/
@[reassoc]
theorem pullbackSourceRestrictOpenIso_hom_fst :
    (pullbackSourceRestrictOpenIso S S' fX A' W).hom ≫
        pullback.fst fX (A'.restrictOpen W).obj.toX =
      (pullbackSourceOpen S S' fX A' W).ι ≫ pullback.fst fX A'.obj.toX :=
  (isPullback_pullbackSource_restrictOpen S S' fX A' W).flip.isoPullback_hom_fst

/-- The comparison of schemes, followed by the projection to `U'|_{W₀}`. -/
@[reassoc]
theorem pullbackSourceRestrictOpenIso_hom_snd :
    (pullbackSourceRestrictOpenIso S S' fX A' W).hom ≫
        pullback.snd fX (A'.restrictOpen W).obj.toX =
      pullbackSourceRestrictSnd S S' fX A' W :=
  (isPullback_pullbackSource_restrictOpen S S' fX A' W).flip.isoPullback_hom_snd

/-! ### The restricted situation -/

variable (hf : S.toClosedFiber ≫ closedFiberMap fS = fX ≫ S'.toClosedFiber)

include hf

/-- The open of `U` above `g⁻¹W` is contained in the preimage of `g⁻¹W`. -/
theorem pullbackSourceOpen_le :
    pullbackSourceOpen S S' fX A' W ≤
      sourceToBase (pullbackSituation S S' fS fX hf A') ⁻¹ᵁ pullbackBaseOpen S S' fS A' W :=
  le_of_eq (preimage_sourceToBase_pullbackSituation S S' fS fX A' W hf).symm

/-- The situation `U/T` restricted to `g⁻¹W` and the open of `U` above it. -/
abbrev pullbackSituationRestrict : GlobalCrystallineSituation.{u} :=
  restrict (pullbackSituation S S' fS fX hf A') (pullbackBaseOpen S S' fS A' W)
    (pullbackSourceOpen S S' fX A' W) (pullbackSourceOpen_le S S' fS fX A' W hf)

/-- The structure morphism of the restricted situation, at the type carrying the two fibre
products by name. -/
def pullbackSituationRestrictToClosedFiber :
    (pullbackSourceOpen S S' fX A' W).toScheme ⟶
      closedFiber ((pullbackBase S S' fS A').restrict (pullbackBaseOpen S S' fS A' W)) :=
  (pullbackSituationRestrict S S' fS fX A' W hf).toClosedFiber

/-- The compatibility datum of the restricted situation with `U/T` itself. -/
theorem pullbackSituationRestrictToClosedFiber_comp_closedFiberMap_restrictι :
    pullbackSituationRestrictToClosedFiber S S' fS fX A' W hf ≫
        closedFiberMap ((pullbackBase S S' fS A').restrictι (pullbackBaseOpen S S' fS A' W)) =
      (pullbackSourceOpen S S' fX A' W).ι ≫ pullbackToClosedFiber S S' fS fX hf A' :=
  restrict_changeBase_condition (pullbackSituation S S' fS fX hf A') _ _ _

/-- The structure morphism of the restricted situation, read in `T`. -/
@[reassoc]
theorem pullbackSituationRestrictToClosedFiber_comp_closedFiberι :
    pullbackSituationRestrictToClosedFiber S S' fS fX A' W hf ≫
        closedFiberι ((pullbackBase S S' fS A').restrict (pullbackBaseOpen S S' fS A' W)) ≫
          ((pullbackBase S S' fS A').restrictι (pullbackBaseOpen S S' fS A' W)).hom =
      (pullbackSourceOpen S S' fX A' W).ι ≫
        sourceToBase (pullbackSituation S S' fS fX hf A') :=
  (Category.assoc _ _ _).symm.trans
    (restrict_sourceToBase (pullbackSituation S S' fS fX hf A') _ _ _)

/-- The structure morphism of the restricted situation, read on the first projection. -/
theorem pullbackSituationRestrictToClosedFiber_comp_fst :
    pullbackSituationRestrictToClosedFiber S S' fS fX A' W hf ≫
        closedFiberMap (pullbackBaseRestrictOpenIso S S' fS A' W).hom ≫
          closedFiberMap (pullback.fst fS (A'.restrictOpen W).obj.toBase) =
      (pullbackSourceOpen S S' fX A' W).ι ≫ pullbackSourceToClosedFiber S S' fX A' := by
  rw [← closedFiberMap_comp, pullbackBaseRestrictOpenIso_hom_fst, closedFiberMap_comp,
    ← Category.assoc, pullbackSituationRestrictToClosedFiber_comp_closedFiberMap_restrictι,
    Category.assoc, pullbackToClosedFiber_comp_fst]

/-- The structure morphism of the restricted situation, read on the second projection. -/
theorem pullbackSituationRestrictToClosedFiber_comp_snd :
    pullbackSituationRestrictToClosedFiber S S' fS fX A' W hf ≫
        closedFiberMap (pullbackBaseRestrictOpenIso S S' fS A' W).hom ≫
          closedFiberMap (pullback.snd fS (A'.restrictOpen W).obj.toBase) =
      pullbackSourceRestrictSnd S S' fX A' W ≫
        (A'.restrictOpen W).obj.thickening.toClosedFiber := by
  have hL : pullbackSituationRestrictToClosedFiber S S' fS fX A' W hf ≫
      closedFiberMap ((pullbackBaseRestrictOpenIso S S' fS A' W).hom ≫
          pullback.snd fS (A'.restrictOpen W).obj.toBase) ≫
        closedFiberι (A'.restrictOpen W).obj.thickening.target ≫ restrictOpenTargetι S' A' W =
      (pullbackSourceOpen S S' fX A' W).ι ≫
        pullback.snd fX A'.obj.toX ≫ A'.obj.thickening.immersion := by
    rw [← Category.assoc (closedFiberMap _), closedFiberMap_comp_closedFiberι, Category.assoc,
      pullbackBaseRestrictOpenIso_hom_snd_hom_ι,
      pullbackSituationRestrictToClosedFiber_comp_closedFiberι_assoc]
    exact (Category.assoc _ _ _).trans
      (congrArg (fun k ↦ (pullbackSourceOpen S S' fX A' W).ι ≫ k)
        (sourceToBase_pullbackSituation_comp_snd S S' fS fX A' hf))
  have hR : pullbackSourceRestrictSnd S S' fX A' W ≫
      (A'.restrictOpen W).obj.thickening.toClosedFiber ≫
        closedFiberι (A'.restrictOpen W).obj.thickening.target ≫ restrictOpenTargetι S' A' W =
      (pullbackSourceOpen S S' fX A' W).ι ≫
        pullback.snd fX A'.obj.toX ≫ A'.obj.thickening.immersion := by
    rw [← Category.assoc ((A'.restrictOpen W).obj.thickening.toClosedFiber),
      SchemeThickening.toClosedFiber_comp_closedFiberι,
      restrictOpen_immersion_restrictOpenTargetι, ← Category.assoc,
      pullbackSourceRestrictSnd_restrictOpenSourceι, Category.assoc]
  rw [← closedFiberMap_comp]
  refine (cancel_mono (closedFiberι (A'.restrictOpen W).obj.thickening.target)).mp ?_
  refine (cancel_mono (restrictOpenTargetι S' A' W)).mp ?_
  simp only [Category.assoc]
  rw [hL, hR]

/-- **The compatibility datum of [Stacks, Tag 07IC] for the two comparisons.** -/
theorem pullbackSituationRestrictToClosedFiber_comp_closedFiberMap :
    pullbackSituationRestrictToClosedFiber S S' fS fX A' W hf ≫
        closedFiberMap (pullbackBaseRestrictOpenIso S S' fS A' W).hom =
      (pullbackSourceRestrictOpenIso S S' fX A' W).hom ≫
        pullbackToClosedFiber S S' fS fX hf (A'.restrictOpen W) := by
  have := closedFiberPullbackComparison_isIso fS (A'.restrictOpen W).obj.toBase
  refine (cancel_mono (closedFiberPullbackComparison fS (A'.restrictOpen W).obj.toBase)).mp ?_
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, closedFiberPullbackComparison_fst]
    rw [pullbackSituationRestrictToClosedFiber_comp_fst, pullbackToClosedFiber_comp_fst]
    simp only [pullbackSourceToClosedFiber]
    rw [pullbackSourceRestrictOpenIso_hom_fst_assoc]
  · simp only [Category.assoc, closedFiberPullbackComparison_snd]
    rw [pullbackSituationRestrictToClosedFiber_comp_snd, pullbackToClosedFiber_comp_snd,
      pullbackSourceRestrictOpenIso_hom_snd_assoc]

/-- **The compatibility datum of [Stacks, Tag 07IC] for the two comparisons**, at the types the
two situations have. -/
theorem pullbackSituationRestrict_changeBase_condition :
    (pullbackSituationRestrict S S' fS fX A' W hf).toClosedFiber ≫
        closedFiberMap (pullbackBaseRestrictOpenIso S S' fS A' W).hom =
      (pullbackSourceRestrictOpenIso S S' fX A' W).hom ≫
        (pullbackSituation S S' fS fX hf (A'.restrictOpen W)).toClosedFiber :=
  pullbackSituationRestrictToClosedFiber_comp_closedFiberMap S S' fS fX A' W hf

/-- **Forming the situation `U/T` commutes with restriction to an open of `T'`, on the small
crystalline sites.** -/
def pullbackSituationRestrictEquivalence :
    CrystallineThickening (pullbackSituationRestrict S S' fS fX A' W hf) ≌
      CrystallineThickening (pullbackSituation S S' fS fX hf (A'.restrictOpen W)) :=
  haveI : @IsIso DividedPowerScheme _ (pullbackSituationRestrict S S' fS fX A' W hf).S
      (pullbackSituation S S' fS fX hf (A'.restrictOpen W)).S
      (pullbackBaseRestrictOpenIso S S' fS A' W).hom := Iso.isIso_hom _
  haveI : @IsIso Scheme _ (pullbackSituationRestrict S S' fS fX A' W hf).X
      (pullbackSituation S S' fS fX hf (A'.restrictOpen W)).X
      (pullbackSourceRestrictOpenIso S S' fX A' W).hom := Iso.isIso_hom _
  smallChangeBaseEquivalenceOfIsIso _ _ (pullbackBaseRestrictOpenIso S S' fS A' W).hom
    (pullbackSourceRestrictOpenIso S S' fX A' W).hom
    (pullbackSituationRestrict_changeBase_condition S S' fS fX A' W hf)

/-- **`Cris(U_W/T_W)` is the full subcategory of `Cris(U/T)` on the objects lying over the open
of `U` above `g⁻¹W`.** -/
def pullbackSituationRestrictEssImageEquivalence :
    CrystallineThickening (pullbackSituation S S' fS fX hf (A'.restrictOpen W)) ≌
      (smallExtend (pullbackSituation S S' fS fX hf A') (pullbackBaseOpen S S' fS A' W)
          (pullbackSourceOpen S S' fX A' W)
          (pullbackSourceOpen_le S S' fS fX A' W hf)).EssImageSubcategory :=
  (pullbackSituationRestrictEquivalence S S' fS fX A' W hf).symm.trans
    (smallExtendEquivalence _ _ _ _)

end Crystalline.GlobalCrystallineSituation

end

end
