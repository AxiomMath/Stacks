module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaChartNested
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartIntPullbackComp

/-!
# The target identifications of the relative `θ` over a nested pair of affine opens of the base

Over the piece `O_V = U(ψ) ∩ f^{-1}(V)` of `U(ψ)` over an affine open `V` of the base,
`GradedPowerMap.chartTargetLegIso` identifies the target of the relative `θ` of [Stacks, Tag 01O9]
with the inverse image of `ℒ^{⊗ n}|_{f^{-1}(V)}` along the leg `O_V ⟶ f^{-1}(V)`. This file shows
that these identifications are compatible along an inclusion `Z ≤ V` of affine opens of the base,
the comparison of the integer tensor powers under pullback of [Stacks, Tag 01CU] along
`f^{-1}(Z) ↪ f^{-1}(V)` entering as the tail. Apart from the coherences of the inverse-image
pseudofunctor, the compatibility amounts to the cocycle law
`Stacks.AlgebraicGeometry.ProjChartIntPullbackComp.intPullIso_nested` for these comparisons.

## Main definitions

* `GradedPowerMap.targetModuleIso`: the identification of the inverse image along
  `f^{-1}(Z) ↪ f^{-1}(V)` of `ℒ|_{f^{-1}(V)}` with `ℒ|_{f^{-1}(Z)}`.
* `GradedPowerMap.chartTargetLegTail`: the tail of the nested comparison of the targets.

## Main results

* `GradedPowerMap.three_comp_leg_nested_tail`: the compatibility of a three-factor morphism out of
  an inverse image with a nested pair of legs.
* `GradedPowerMap.five_comp_leg_nested_tail`: the same for a five-factor identification.
* `GradedPowerMap.chartTargetLegIso_hom_nested`: the target identifications are compatible along an
  inclusion `Z ≤ V` of affine opens of the base.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.ProjChartIntPullbackMul (intPullIso)
open Stacks.AlgebraicGeometry.ProjChartIntPullbackComp (compPullIso intPullIsoAt
  intPullIso_nested)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.Tag07ZGTwist (comp_congr_right comp_comp_congr
  pullback_three_comp_leg_assoc pullback_three_leg_congr_assoc prefix_nested_rearrange)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

namespace GradedPowerMap

/-! ### Nested coherences of inverse images -/

/-- The image under a functor of a four-fold composite `a ≫ b ≫ c ≫ t` is the image of `a ≫ b ≫ c`
followed by the image of `t`. -/
private theorem map_comp₄ {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟)
    {W X Y Z A : 𝒞} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (t : Z ⟶ A) :
    F.map (a ≫ b ≫ c ≫ t) = F.map (a ≫ b ≫ c) ≫ F.map t := by
  rw [← F.map_comp, Category.assoc, Category.assoc]

/-- Let `aT : V₁ ⟶ Xs` and `aU : V₂ ⟶ Xs` satisfy `pim ≫ aU = aT`, and let `tw` compare the inverse
image along `pim` of `N₂` with `N₁`. If `χ₁` is the inverse image of `χ₂` along `pim`, prefixed by
the pseudofunctoriality factors of `pim ≫ aU = aT` and followed by `tw` (the hypothesis `hbase`),
then the same compatibility holds at an arbitrary pair of legs `d' : Z' ⟶ V₁` and `d : Z ⟶ V₂`
joined by `k : Z' ⟶ Z`, with `twAtP` the transport of `tw` given by `htwAtP`. -/
public theorem three_comp_leg_nested_tail {V₁ V₂ Xs : Scheme.{u}}
    (aT : V₁ ⟶ Xs) (aU : V₂ ⟶ Xs) (pim : V₁ ⟶ V₂) (ct : pim ≫ aU = aT)
    {M : Xs.Modules} {N₁ : V₁.Modules} {N₂ : V₂.Modules}
    (χ₁ : (Scheme.Modules.pullback aT).obj M ⟶ N₁)
    (χ₂ : (Scheme.Modules.pullback aU).obj M ⟶ N₂)
    (tw : (Scheme.Modules.pullback pim).obj N₂ ⟶ N₁)
    {Z' Z : Scheme.{u}} (k : Z' ⟶ Z) {d : Z ⟶ V₂} {c : Z ⟶ Xs} (hc : d ≫ aU = c)
    {d' : Z' ⟶ V₁} {c' : Z' ⟶ Xs} (hc' : d' ≫ aT = c') (hkc : k ≫ c = c')
    (hpd : d' ≫ pim = k ≫ d)
    (twAtP : (Scheme.Modules.pullback (k ≫ d)).obj N₂ ⟶ (Scheme.Modules.pullback d').obj N₁)
    (htwAtP : twAtP =
      (Scheme.Modules.pullbackCongr hpd).inv.app N₂ ≫
        (Scheme.Modules.pullbackComp d' pim).inv.app N₂ ≫
        (Scheme.Modules.pullback d').map tw)
    (hbase : (Scheme.Modules.pullbackCongr ct).inv.app M ≫
        (Scheme.Modules.pullbackComp pim aU).inv.app M ≫
        (Scheme.Modules.pullback pim).map χ₂ ≫ tw = χ₁) :
    (Scheme.Modules.pullbackCongr hc').inv.app M ≫
        (Scheme.Modules.pullbackComp d' aT).inv.app M ≫
        (Scheme.Modules.pullback d').map χ₁ =
      (Scheme.Modules.pullbackCongr hkc).inv.app M ≫
        (Scheme.Modules.pullbackComp k c).inv.app M ≫
        (Scheme.Modules.pullback k).map
          ((Scheme.Modules.pullbackCongr hc).inv.app M ≫
            (Scheme.Modules.pullbackComp d aU).inv.app M ≫
            (Scheme.Modules.pullback d).map χ₂) ≫
        (Scheme.Modules.pullbackComp k d).hom.app N₂ ≫ twAtP := by
  subst htwAtP
  have hc₂ : (d' ≫ pim) ≫ aU = c' := by rwa [Category.assoc, ct]
  have hc₃ : (k ≫ d) ≫ aU = c' := by rwa [Category.assoc, hc]
  rw [← pullback_three_comp_leg_assoc k d aU χ₂ hc hc₃ hkc,
    ← pullback_three_leg_congr_assoc aU χ₂ hpd hc₂ hc₃,
    pullback_three_comp_leg_assoc d' pim aU χ₂ ct hc₂ hc',
    Iso.hom_inv_id_app_assoc (Scheme.Modules.pullbackComp d' pim) N₂, ← hbase]
  exact comp_comp_congr _ _ (map_comp₄ _ _ _ _ _)

/-- For `k ≫ g = gT`, the inverse image along `gT` of a morphism `ρ`, followed by the congruence of
the two readings of `gT` and the contraction of the iterated inverse image, is those two factors
followed by the iterated inverse image of `ρ`. -/
private theorem congr_comp_naturality {W Z V : Scheme.{u}} (k : W ⟶ Z) (g : Z ⟶ V)
    {gT : W ⟶ V} (hk : k ≫ g = gT) {M N : V.Modules} (ρ : M ⟶ N) :
    (Scheme.Modules.pullback gT).map ρ ≫
        (Scheme.Modules.pullbackCongr hk).inv.app N ≫
        (Scheme.Modules.pullbackComp k g).inv.app N =
      (Scheme.Modules.pullbackCongr hk).inv.app M ≫
        (Scheme.Modules.pullbackComp k g).inv.app M ≫
        (Scheme.Modules.pullback k).map ((Scheme.Modules.pullback g).map ρ) := by
  rw [reassoc_of% (Scheme.Modules.pullbackCongr hk).inv.naturality ρ,
    (Scheme.Modules.pullbackComp k g).inv.naturality ρ]
  rfl

/-! ### The five-factor target identification, nested -/

/-- The nested compatibility of a five-factor identification. Over `bV : BV ⟶ C` (and likewise over
`bZ`), `LV` is the inverse image of a comparison `ρ` of a module `RM` on `C` with the inverse image
of `M` along `r : C ⟶ Xs`, followed by the contraction of the iterated inverse image, the
congruence of the two readings of the leg `gV ≫ aU = bV ≫ r`, the contraction again and the inverse
image along `gV` of `χ₂`. Given `hbase` as in `three_comp_leg_nested_tail`, `LZ` is the inverse
image of `LV` along `kP`, prefixed by the pseudofunctoriality factors of `kP ≫ bV = bZ` and
followed by the contraction along `kP` and the transport `twAtP` of `tw`. -/
public theorem five_comp_leg_nested_tail {Xs C BV BZ V₁ V₂ : Scheme.{u}}
    (r : C ⟶ Xs) (bV : BV ⟶ C) {bZ : BZ ⟶ C} (kP : BZ ⟶ BV) (hkP : kP ≫ bV = bZ)
    (aT : V₁ ⟶ Xs) (aU : V₂ ⟶ Xs) (pim : V₁ ⟶ V₂) (ct : pim ≫ aU = aT)
    {M : Xs.Modules} {RM : C.Modules} (ρ : RM ⟶ (Scheme.Modules.pullback r).obj M)
    {N₁ : V₁.Modules} {N₂ : V₂.Modules}
    (χ₁ : (Scheme.Modules.pullback aT).obj M ⟶ N₁)
    (χ₂ : (Scheme.Modules.pullback aU).obj M ⟶ N₂)
    (tw : (Scheme.Modules.pullback pim).obj N₂ ⟶ N₁)
    {gV : BV ⟶ V₂} (hgV : gV ≫ aU = bV ≫ r)
    {gZ : BZ ⟶ V₁} (hgZ : gZ ≫ aT = bZ ≫ r)
    (hnest : gZ ≫ pim = kP ≫ gV)
    (twAtP : (Scheme.Modules.pullback (kP ≫ gV)).obj N₂ ⟶
      (Scheme.Modules.pullback gZ).obj N₁)
    (htwAtP : twAtP =
      (Scheme.Modules.pullbackCongr hnest).inv.app N₂ ≫
        (Scheme.Modules.pullbackComp gZ pim).inv.app N₂ ≫
        (Scheme.Modules.pullback gZ).map tw)
    (hbase : (Scheme.Modules.pullbackCongr ct).inv.app M ≫
        (Scheme.Modules.pullbackComp pim aU).inv.app M ≫
        (Scheme.Modules.pullback pim).map χ₂ ≫ tw = χ₁)
    (LV : (Scheme.Modules.pullback bV).obj RM ⟶ (Scheme.Modules.pullback gV).obj N₂)
    (hLV : LV = (Scheme.Modules.pullback bV).map ρ ≫
      (Scheme.Modules.pullbackComp bV r).hom.app M ≫
        ((Scheme.Modules.pullbackCongr hgV).inv.app M ≫
          (Scheme.Modules.pullbackComp gV aU).inv.app M ≫
          (Scheme.Modules.pullback gV).map χ₂))
    (LZ : (Scheme.Modules.pullback bZ).obj RM ⟶ (Scheme.Modules.pullback gZ).obj N₁)
    (hLZ : LZ = (Scheme.Modules.pullback bZ).map ρ ≫
      (Scheme.Modules.pullbackComp bZ r).hom.app M ≫
        ((Scheme.Modules.pullbackCongr hgZ).inv.app M ≫
          (Scheme.Modules.pullbackComp gZ aT).inv.app M ≫
          (Scheme.Modules.pullback gZ).map χ₁)) :
    LZ = (Scheme.Modules.pullbackCongr hkP).inv.app RM ≫
      (Scheme.Modules.pullbackComp kP bV).inv.app RM ≫
      (Scheme.Modules.pullback kP).map LV ≫
      (Scheme.Modules.pullbackComp kP gV).hom.app N₂ ≫ twAtP := by
  subst hLV hLZ
  have hkc : kP ≫ bV ≫ r = bZ ≫ r := by
    rw [← Category.assoc, hkP]
  have hengine := three_comp_leg_nested_tail aT aU pim ct χ₁ χ₂ tw kP hgV hgZ hkc hnest
    twAtP htwAtP hbase
  refine Eq.trans (comp_congr_right _ (comp_congr_right _ hengine)) ?_
  rw [prefix_nested_rearrange kP bV r hkP hkc M
    ((Scheme.Modules.pullbackCongr hgV).inv.app M ≫
      (Scheme.Modules.pullbackComp gV aU).inv.app M ≫
      (Scheme.Modules.pullback gV).map χ₂)
    ((Scheme.Modules.pullbackComp kP gV).hom.app N₂ ≫ twAtP),
    reassoc_of% congr_comp_naturality kP bV hkP ρ]
  simp only [Functor.map_comp, Category.assoc]

/-! ### The target identifications of the relative `θ`, nested -/

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f)

variable {Z V : S.affineOpens} (h : (Z.1 : S.Opens) ≤ (V.1 : S.Opens))

/-- The identification of the inverse image along `f^{-1}(Z) ↪ f^{-1}(V)` of `ℒ|_{f^{-1}(V)}` with
`ℒ|_{f^{-1}(Z)}`: the contraction of the iterated inverse image followed by the congruence of the
two readings of the composite inclusion. -/
public def targetModuleIso :
    (Scheme.Modules.pullback (T.homOfLE (f.preimage_mono h))).obj
        ((Scheme.Modules.pullback (f ⁻¹ᵁ (V.1 : S.Opens)).ι).obj P.L) ≅
      (Scheme.Modules.pullback (f ⁻¹ᵁ (Z.1 : S.Opens)).ι).obj P.L :=
  compPullIso (f ⁻¹ᵁ (V.1 : S.Opens)).ι (T.homOfLE (f.preimage_mono h)) P.L ≪≫
    (Scheme.Modules.pullbackCongr (T.homOfLE_ι (f.preimage_mono h))).app P.L

/-- `GradedPowerMap.targetModuleIso` is the composite of the contraction of the iterated inverse
image and the congruence of the two readings of the composite inclusion. -/
public theorem targetModuleIso_eq :
    P.targetModuleIso h =
      compPullIso (f ⁻¹ᵁ (V.1 : S.Opens)).ι (T.homOfLE (f.preimage_mono h)) P.L ≪≫
        (Scheme.Modules.pullbackCongr (T.homOfLE_ι (f.preimage_mono h))).app P.L :=
  rfl

/-- The tail of the nested comparison of the targets of the chart data: out of the inverse image
along the leg out of the larger piece composed with the inclusion of the smaller piece, the
congruence of the two readings of that leg (`GradedPowerMap.pieceTargetLeg_comp_homOfLE`), the
contraction of the iterated inverse image, and the inverse image along the leg out of the smaller
piece of the comparison of the integer tensor powers along `f^{-1}(Z) ↪ f^{-1}(V)` of [Stacks, Tag
01CU], taken at `GradedPowerMap.targetModuleIso`. -/
public def chartTargetLegTail (n : ℤ) :
    (Scheme.Modules.pullback (P.coveringOpen.toScheme.homOfLE (P.toBase.preimage_mono h) ≫
          P.pieceTargetLeg (V.1 : S.Opens) V.2)).obj
        (tensorPowerModule (f ⁻¹ᵁ (V.1 : S.Opens)).toScheme
          ((Scheme.Modules.pullback (f ⁻¹ᵁ (V.1 : S.Opens)).ι).obj P.L) n) ⟶
      (Scheme.Modules.pullback (P.pieceTargetLeg (Z.1 : S.Opens) Z.2)).obj
        (tensorPowerModule (f ⁻¹ᵁ (Z.1 : S.Opens)).toScheme
          ((Scheme.Modules.pullback (f ⁻¹ᵁ (Z.1 : S.Opens)).ι).obj P.L) n) :=
  (Scheme.Modules.pullbackCongr (P.pieceTargetLeg_comp_homOfLE h)).inv.app
      (tensorPowerModule (f ⁻¹ᵁ (V.1 : S.Opens)).toScheme
        ((Scheme.Modules.pullback (f ⁻¹ᵁ (V.1 : S.Opens)).ι).obj P.L) n) ≫
    (Scheme.Modules.pullbackComp (P.pieceTargetLeg (Z.1 : S.Opens) Z.2)
          (T.homOfLE (f.preimage_mono h))).inv.app
        (tensorPowerModule (f ⁻¹ᵁ (V.1 : S.Opens)).toScheme
          ((Scheme.Modules.pullback (f ⁻¹ᵁ (V.1 : S.Opens)).ι).obj P.L) n) ≫
      (Scheme.Modules.pullback (P.pieceTargetLeg (Z.1 : S.Opens) Z.2)).map
        (intPullIsoAt (T.homOfLE (f.preimage_mono h)) (P.targetModuleIso h) n)

/-- The target identifications of the relative `θ` of [Stacks, Tag 01O9] are compatible along an
inclusion `Z ≤ V` of affine opens of the base: the identification over `Z` is the identification
over `V`, pulled back along the inclusion of the piece over `Z` into the piece over `V` and
prefixed by the two pseudofunctoriality factors of that inclusion, followed by the contraction of
the iterated inverse image and the three factors of `GradedPowerMap.chartTargetLegTail`. -/
public theorem chartTargetLegIso_hom_nested (n : ℤ) :
    (P.chartTargetLegIso (Z.1 : S.Opens) Z.2 n).hom =
      (Scheme.Modules.pullbackCongr
            (P.coveringOpen.toScheme.homOfLE_ι (P.toBase.preimage_mono h))).inv.app
          ((tensorPowerModule T P.L n).restrict P.coveringOpen.ι) ≫
        (Scheme.Modules.pullbackComp
              (P.coveringOpen.toScheme.homOfLE (P.toBase.preimage_mono h))
              (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).ι).inv.app
            ((tensorPowerModule T P.L n).restrict P.coveringOpen.ι) ≫
          (Scheme.Modules.pullback
                (P.coveringOpen.toScheme.homOfLE (P.toBase.preimage_mono h))).map
              ((P.chartTargetLegIso (V.1 : S.Opens) V.2 n).hom) ≫
            (Scheme.Modules.pullbackComp
                  (P.coveringOpen.toScheme.homOfLE (P.toBase.preimage_mono h))
                  (P.pieceTargetLeg (V.1 : S.Opens) V.2)).hom.app
                (tensorPowerModule (f ⁻¹ᵁ (V.1 : S.Opens)).toScheme
                  ((Scheme.Modules.pullback (f ⁻¹ᵁ (V.1 : S.Opens)).ι).obj P.L) n) ≫
      (Scheme.Modules.pullbackCongr (P.pieceTargetLeg_comp_homOfLE h)).inv.app
          (tensorPowerModule (f ⁻¹ᵁ (V.1 : S.Opens)).toScheme
            ((Scheme.Modules.pullback (f ⁻¹ᵁ (V.1 : S.Opens)).ι).obj P.L) n) ≫
        (Scheme.Modules.pullbackComp (P.pieceTargetLeg (Z.1 : S.Opens) Z.2)
              (T.homOfLE (f.preimage_mono h))).inv.app
            (tensorPowerModule (f ⁻¹ᵁ (V.1 : S.Opens)).toScheme
              ((Scheme.Modules.pullback (f ⁻¹ᵁ (V.1 : S.Opens)).ι).obj P.L) n) ≫
          (Scheme.Modules.pullback (P.pieceTargetLeg (Z.1 : S.Opens) Z.2)).map
            (intPullIsoAt (T.homOfLE (f.preimage_mono h)) (P.targetModuleIso h) n) :=
  five_comp_leg_nested_tail P.coveringOpen.ι (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).ι
    (P.coveringOpen.toScheme.homOfLE (P.toBase.preimage_mono h))
    (P.coveringOpen.toScheme.homOfLE_ι (P.toBase.preimage_mono h))
    (f ⁻¹ᵁ (Z.1 : S.Opens)).ι (f ⁻¹ᵁ (V.1 : S.Opens)).ι
    (T.homOfLE (f.preimage_mono h)) (T.homOfLE_ι (f.preimage_mono h))
    ((Scheme.Modules.restrictFunctorIsoPullback P.coveringOpen.ι).hom.app
      (tensorPowerModule T P.L n))
    (intPullIso (f ⁻¹ᵁ (Z.1 : S.Opens)).ι P.L n).hom
    (intPullIso (f ⁻¹ᵁ (V.1 : S.Opens)).ι P.L n).hom
    (intPullIsoAt (T.homOfLE (f.preimage_mono h)) (P.targetModuleIso h) n)
    (P.pieceTargetLeg_comp_ι (V.1 : S.Opens) V.2)
    (P.pieceTargetLeg_comp_ι (Z.1 : S.Opens) Z.2)
    (P.pieceTargetLeg_comp_homOfLE h)
    _ rfl
    (intPullIso_nested (f ⁻¹ᵁ (V.1 : S.Opens)).ι (T.homOfLE (f.preimage_mono h)) P.L
      (T.homOfLE_ι (f.preimage_mono h)) (P.targetModuleIso h)
      (P.targetModuleIso_eq h) n).symm
    ((P.chartTargetLegIso (V.1 : S.Opens) V.2 n).hom)
    (P.chartTargetLegIso_hom (V.1 : S.Opens) V.2 n)
    ((P.chartTargetLegIso (Z.1 : S.Opens) Z.2 n).hom)
    (P.chartTargetLegIso_hom (Z.1 : S.Opens) Z.2 n)

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
