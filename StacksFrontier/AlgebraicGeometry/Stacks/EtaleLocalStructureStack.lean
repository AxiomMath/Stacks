module

public import StacksFrontier.AlgebraicGeometry.Groupoids.More.OverPullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.RestrictionProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasiSplittingAffineLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RestrictionArrowsDerealization
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteObjectOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SitePullbackContainment
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureChartExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion

/-!
# The étale local structure of a quasi-DM algebraic stack (Stacks 0DU3)

**Stacks 0DU3.** Let `𝒳` be an algebraic stack which is quasi-DM with separated diagonal, and let
`x ∈ |𝒳|`. Then there is a 1-morphism of algebraic stacks `𝒰 ⟶ 𝒳` such that

1. some point `u ∈ |𝒰|` maps to `x`,
2. `𝒰 ⟶ 𝒳` is representable by algebraic spaces and étale,
3. `𝒰 = [U/R]` for a groupoid scheme `(U, R, s, t, c)` with `U`, `R` affine and `s`, `t` finite,
   flat and locally of finite presentation.

The proof is the source's. A quotient chart `[U/R] ⟶ 𝒳` through `x` with `U` affine
(`AlgebraicGeometry.Stack.EtaleLocalStructure.exists_chartGroupoid`: Stacks 06MF, 04XL, 03XX,
04WY) satisfies the assumptions of **Stacks 04S0** at a point `u` over `x`, which produces an
affine étale neighbourhood `U'' ⟶ U` of `u` over which the restriction `R|_{U''}` is quasi-split
by an open finite subgroupoid `P`. The 1-morphisms

    [U''/P] ⟶ [U''/R|_{U''}] ⟶ [U/R] ⟶ 𝒳

are representable by algebraic spaces and étale (**Stacks 0DU2**, its argument for a restriction,
and the quotient chart), and `P` has the shape of clause (3).

## Main results

* `Stack.EtaleLocalStructure.exists_etale_quotientStack_of_openFiniteSubgroupoid`: the étale chain
  for any restriction of a quotient chart along an étale morphism and any open finite subgroupoid
  of it.
* `Stack.exists_etale_quotientStack_of_isQuasiDM`: a quasi-DM algebraic stack with separated
  diagonal admits, through each of its points, an étale chart representable by algebraic spaces
  by a quotient stack of a groupoid scheme with affine objects and arrows and finite, flat, locally
  finitely presented source and target (**Stacks 0DU3**).

## Implementation notes

`𝒰` is the small model of the quotient stack of the realization of `P`
(`AlgebraicGeometry.Stack.smallAlgebraicQuotientStack`), so that it is an object of the 2-category
of algebraic stacks; clause (3) is the equivalence over the site between it and the quotient stack
of the realization. "Quasi-DM" is the absolute notion of Stacks 050D and the separated diagonal is
`Δ_{𝒳/S}` separated in the sense of Stacks 04XB, the reading of Stacks 0CL0 that the source's
parenthetical refers to.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u w

namespace AlgebraicGeometry.Stack.EtaleLocalStructure

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS}

namespace ChartGroupoid

variable (K : ChartGroupoid B S hS 𝒳)

/-- The object scheme of the groupoid of a quotient chart lies in the site. -/
theorem contains_objects : B.Contains K.groupoid.objects.left :=
  Space.contains_representedGroupoidScheme_objects K.s K.t K.c K.hG

/-- The arrow scheme of the groupoid of a quotient chart lies in the site. -/
theorem contains_arrows : B.Contains K.groupoid.arrows.left :=
  Space.contains_representedGroupoidScheme_arrows K.s K.t K.c K.hG

/-- The fibre product of the source and target of the groupoid of a quotient chart lies in the
site. -/
theorem contains_pullback : B.Contains (pullback K.groupoid.source K.groupoid.target).left :=
  Space.contains_representedGroupoidScheme_pullback K.s K.t K.c K.hG

end ChartGroupoid

section Chain

variable (K : ChartGroupoid B S hS 𝒳) {U'' : Over S} (g : U'' ⟶ K.groupoid.objects)
  [Etale g.left] (hU'' : B.Contains U''.left)
  (R : AlgebraicGeometry.GroupoidScheme.Restriction K.groupoid g)
  (P : GroupoidScheme.OpenFiniteSubgroupoid R.groupoid)

omit [Etale g.left] in
include hU'' in
/-- The object scheme of a restriction of the chart groupoid lies in the site. -/
theorem contains_restriction_objects : B.Contains R.groupoid.objects.left := by
  rwa [R.objects_eq]

omit [Etale g.left] in
include hU'' in
/-- The arrow scheme of a restriction of the chart groupoid lies in the site. -/
theorem contains_restriction_arrows : B.Contains R.groupoid.arrows.left := by
  rw [R.arrows_eq]
  exact GroupoidScheme.contains_restrictionArrows_left K.groupoid B K.contains_arrows hU'' g

omit [Etale g.left] in
include hU'' in
/-- The fibre product of the source and target of a restriction of the chart groupoid lies in the
site. -/
theorem contains_restriction_pullback :
    B.Contains (pullback R.groupoid.source R.groupoid.target).left :=
  BigFppfSite.contains_pullback_left B _ _ (contains_restriction_arrows K g hU'' R)
    (contains_restriction_arrows K g hU'' R)

omit [Etale g.left] in
include hU'' in
/-- The object scheme of an open finite subgroupoid of a restriction lies in the site. -/
theorem contains_subgroupoid_objects : B.Contains P.subgroupoid.objects.left := by
  rw [P.objects_eq]
  exact contains_restriction_objects K g hU'' R

omit [Etale g.left] in
include hU'' in
/-- The arrow scheme of an open finite subgroupoid of a restriction lies in the site. -/
theorem contains_subgroupoid_arrows : B.Contains P.subgroupoid.arrows.left := by
  have := P.arrows_open
  exact BigFppfSite.contains_of_isOpenImmersion B P.inclusion.mapArrows.left
    (contains_restriction_arrows K g hU'' R)

omit [Etale g.left] in
include hU'' in
/-- The fibre product of the source and target of an open finite subgroupoid of a restriction lies
in the site. -/
theorem contains_subgroupoid_pullback :
    B.Contains (pullback P.subgroupoid.source P.subgroupoid.target).left :=
  BigFppfSite.contains_pullback_left B _ _ (contains_subgroupoid_arrows K g hU'' R P)
    (contains_subgroupoid_arrows K g hU'' R P)

omit [Etale g.left] in
/-- A property of morphisms of schemes stable under base change and composition, held by the
source of the chart groupoid and by the restricting morphism, is held by the source and the target
of the restriction. -/
theorem restriction_source_target_mem (Q : MorphismProperty Scheme.{u})
    [Q.IsStableUnderBaseChange] [Q.IsStableUnderComposition]
    (hs : Q K.groupoid.source.left) (hg : Q g.left) :
    Q R.groupoid.source.left ∧ Q R.groupoid.target.left := by
  have h := AlgebraicGeometry.overFibreProduct_comp (pullback.snd g K.groupoid.target)
    K.groupoid.source (AlgebraicGeometry.overFibreProduct_snd _ K.groupoid.target hg) hs
  exact ⟨AlgebraicGeometry.restriction_source_mem K.groupoid g R Q h,
    AlgebraicGeometry.restriction_target_mem K.groupoid g R Q h⟩

omit [Etale g.left] in
/-- The source of an open finite subgroupoid is the ambient source restricted along the open
immersion of arrow schemes, transported along the equality of object schemes. -/
theorem subgroupoid_source_left :
    P.subgroupoid.source.left =
      P.inclusion.mapArrows.left ≫ R.groupoid.source.left ≫ (eqToHom P.objects_eq.symm).left := by
  rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc, P.inclusion.map_source,
    P.mapObjects_eq, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

omit [Etale g.left] in
/-- The target of an open finite subgroupoid is the ambient target restricted along the open
immersion of arrow schemes, transported along the equality of object schemes. -/
theorem subgroupoid_target_left :
    P.subgroupoid.target.left =
      P.inclusion.mapArrows.left ≫ R.groupoid.target.left ≫ (eqToHom P.objects_eq.symm).left := by
  rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc, P.inclusion.map_target,
    P.mapObjects_eq, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

omit [Etale g.left] in
/-- A property of morphisms of schemes respecting isomorphisms, stable under composition and held
by open immersions, held by the source and the target of the ambient groupoid, is held by those of
an open finite subgroupoid. -/
theorem subgroupoid_source_target_mem (Q : MorphismProperty Scheme.{u}) [Q.RespectsIso]
    [Q.IsStableUnderComposition]
    (hopen : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), _root_.AlgebraicGeometry.IsOpenImmersion f → Q f)
    (hs : Q R.groupoid.source.left) (ht : Q R.groupoid.target.left) :
    Q P.subgroupoid.source.left ∧ Q P.subgroupoid.target.left := by
  have : IsIso (eqToHom P.objects_eq.symm).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (eqToHom P.objects_eq.symm)))
  have hP := hopen _ P.arrows_open
  refine ⟨?_, ?_⟩
  · rw [subgroupoid_source_left]
    exact Q.comp_mem _ _ hP ((Q.cancel_right_of_respectsIso _ _).2 hs)
  · rw [subgroupoid_target_left]
    exact Q.comp_mem _ _ hP ((Q.cancel_right_of_respectsIso _ _).2 ht)

include hU'' in
/-- **The étale chain of Stacks 0DU3 and 0DU4.** For a quotient chart `[U/R] ⟶ 𝒳`, a restriction
`R''` of its groupoid scheme along an étale morphism `g : U'' ⟶ U` from an affine scheme, and an
open finite subgroupoid `P ⊆ R''`, the 1-morphisms

    [U''/P] ⟶ [U''/R''] ⟶ [U/R] ⟶ 𝒳

between the small models of the quotient stacks of the realizations are representable by
algebraic spaces and étale, the composite of the last two is fully faithful, and a point of the
object scheme of `P` is sent to the image of its image in `U`. The groupoid scheme `P` has affine
object and arrow schemes, and its source and target are finite, flat and locally of finite
presentation. -/
theorem exists_etale_quotientStack_of_openFiniteSubgroupoid [IsAffine U''.left] :
    ∃ (hPU : B.Contains P.subgroupoid.objects.left) (hPR : B.Contains P.subgroupoid.arrows.left)
      (hPP : B.Contains (pullback P.subgroupoid.source P.subgroupoid.target).left)
      (hRU : B.Contains R.groupoid.objects.left) (hRR : B.Contains R.groupoid.arrows.left)
      (hRP : B.Contains (pullback R.groupoid.source R.groupoid.target).left)
      (algP : IsAlgebraicStack.{u, w} B S hS
        (quotientStack (P.subgroupoid.realization B hS hPU hPR hPP)))
      (algR : IsAlgebraicStack.{u, w} B S hS
        (quotientStack (R.groupoid.realization B hS hRU hRR hRP)))
      (Ψ : smallAlgebraicQuotientStack.{u, w} (R.groupoid.realization B hS hRU hRR hRP) algR ⟶ 𝒳),
      IsRelativelyEtale B S hS Ψ.hom ∧ (CatFiberedInGroupoids.homFunctor Ψ.hom).Full ∧
        (CatFiberedInGroupoids.homFunctor Ψ.hom).Faithful ∧
        IsRelativelyEtale B S hS
          (smallQuotientStackMap.{u, w} (GroupoidScheme.Hom.realization B hS P.inclusion hPU hPR hPP
            hRU hRR hRP) algP algR ≫ Ψ).hom ∧
        (∀ z : Space.points B S hS (yoneda.obj (Space.schemeSiteObject B hS hPU)),
          AlgebraicStacks.pointsMap B S hS
              (smallQuotientStackMap.{u, w} (GroupoidScheme.Hom.realization B hS P.inclusion hPU hPR
                hPP hRU hRR hRP) algP algR ≫ Ψ)
              (smallQuotientStackPoint _ algP z) =
            AlgebraicStacks.pointsMap B S hS K.map (K.point
              (Space.pointsMap B S hS _ (yoneda.map (Space.schemeSiteMap B hS hRU K.contains_objects
                R.hom.mapObjects))
                (Space.pointsMap B S hS _ (yoneda.map (Space.schemeSiteMap B hS hPU hRU
                  P.inclusion.mapObjects)) z)))) ∧
        IsAffine P.subgroupoid.objects.left ∧ IsAffine P.subgroupoid.arrows.left ∧
        IsFinite P.subgroupoid.source.left ∧ Flat P.subgroupoid.source.left ∧
        LocallyOfFinitePresentation P.subgroupoid.source.left ∧
        IsFinite P.subgroupoid.target.left ∧ Flat P.subgroupoid.target.left ∧
        LocallyOfFinitePresentation P.subgroupoid.target.left := by
  have hRU := contains_restriction_objects K g hU'' R
  have hRR := contains_restriction_arrows K g hU'' R
  have hRP := contains_restriction_pullback K g hU'' R
  have hPU := contains_subgroupoid_objects K g hU'' R P
  have hPR := contains_subgroupoid_arrows K g hU'' R P
  have hPP := contains_subgroupoid_pullback K g hU'' R P
  have : Flat K.groupoid.source.left := K.flat_s
  have : Flat K.groupoid.target.left := K.flat_t
  have : LocallyOfFinitePresentation K.groupoid.source.left := K.lfp_s
  have : LocallyOfFinitePresentation K.groupoid.target.left := K.lfp_t
  obtain ⟨hRs, hRt⟩ := restriction_source_target_mem K g R @Flat K.flat_s inferInstance
  obtain ⟨hRs', hRt'⟩ :=
    restriction_source_target_mem K g R @LocallyOfFinitePresentation K.lfp_s inferInstance
  have : MorphismProperty.RespectsIso @Flat.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso @LocallyOfFinitePresentation.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨hPs, hPt⟩ :=
    subgroupoid_source_target_mem K g R P @Flat (fun _ _ => inferInstance) hRs hRt
  obtain ⟨hPs', hPt'⟩ := subgroupoid_source_target_mem K g R P @LocallyOfFinitePresentation
    (fun _ _ => inferInstance) hRs' hRt'
  have algR := GroupoidScheme.isAlgebraicStack_quotientStack_realization.{u, w} B hS hRU hRR hRP
  have algP := GroupoidScheme.isAlgebraicStack_quotientStack_realization.{u, w} B hS hPU hPR hPP
  -- the restriction step
  let φR := GroupoidScheme.Hom.realization B hS R.hom hRU hRR hRP K.contains_objects
    K.contains_arrows K.contains_pullback
  let q₂ : smallAlgebraicQuotientStack.{u, w} (R.groupoid.realization B hS hRU hRR hRP) algR ⟶
      K.quotient := smallQuotientStackMap.{u, w} φR algR K.alg
  have hq₂ : IsRelativelyEtale B S hS q₂.hom :=
    GroupoidScheme.isRelativelyEtale_smallQuotientStackMap_restriction.{u, w} B hS
      K.contains_objects K.contains_arrows K.contains_pullback R hRU hRR hRP
  have hfull : ∀ T, (φR.toGroupoidHom.evaluation T).Full :=
    GroupoidScheme.Hom.realization_evaluation_full hS R.hom hRU hRR hRP K.contains_objects
      K.contains_arrows K.contains_pullback
      (fun T => (R.evaluation_fullyFaithful T).some.full)
  have hfaith : ∀ T, (φR.toGroupoidHom.evaluation T).Faithful :=
    GroupoidScheme.Hom.realization_evaluation_faithful hS R.hom hRU hRR hRP K.contains_objects
      K.contains_arrows K.contains_pullback
      (fun T => (R.evaluation_fullyFaithful T).some.faithful)
  obtain ⟨hFF₂⟩ := nonempty_fullyFaithful_smallQuotientStackMap.{u, w} φR algR K.alg
    (nonempty_fullyFaithful_quotientStackMap B S hS φR hfull hfaith)
  have := K.full
  have := K.faithful
  have hFFΨ : (CatFiberedInGroupoids.homFunctor (q₂ ≫ K.map).hom).FullyFaithful :=
    hFF₂.comp (Functor.FullyFaithful.ofFullyFaithful (CatFiberedInGroupoids.homFunctor K.map.hom))
  have hΨ : IsRelativelyEtale B S hS (q₂ ≫ K.map).hom :=
    isRelativelyEtale_comp B S hS _ _ hq₂ K.etale
  -- the open finite subgroupoid step
  let φP := GroupoidScheme.Hom.realization B hS P.inclusion hPU hPR hPP hRU hRR hRP
  have hq₁ : IsRelativelyEtale B S hS (smallQuotientStackMap.{u, w} φP algP algR).hom :=
    GroupoidScheme.isRelativelyEtale_smallQuotientStackMap_inclusion.{u, w} B hS hRU hRR hRP P
      hPU hPR hPP
  have : IsAffine P.subgroupoid.objects.left := by
    rw [P.objects_eq, R.objects_eq]
    infer_instance
  have := P.source_finite
  refine ⟨hPU, hPR, hPP, hRU, hRR, hRP, algP, algR, q₂ ≫ K.map, hΨ, hFFΨ.full,
    hFFΨ.faithful, isRelativelyEtale_comp B S hS _ _ hq₁ hΨ, fun z => ?_, inferInstance,
    isAffine_of_isAffineHom P.subgroupoid.source.left, P.source_finite, hPs, hPs',
    P.target_finite, hPt, hPt'⟩
  refine (congrFun (AlgebraicStacks.pointsMap_comp B S hS
    (smallQuotientStackMap.{u, w} φP algP algR) (q₂ ≫ K.map)) _).trans ?_
  rw [Function.comp_apply, pointsMap_smallQuotientStackMap_point.{u, w} φP algP algR z]
  refine (congrFun (AlgebraicStacks.pointsMap_comp B S hS q₂ K.map) _).trans ?_
  rw [Function.comp_apply, pointsMap_smallQuotientStackMap_point.{u, w} φR algR K.alg]
  rfl

omit [Etale g.left] in
/-- The point of the object scheme of an open finite subgroupoid of a restriction over a point
`u''` of the restricting scheme is sent to the image of `u''`. -/
theorem pointsToScheme_pointsMap_subgroupoid (_hU'' : B.Contains U''.left)
    (hRU : B.Contains R.groupoid.objects.left) (hPU : B.Contains P.subgroupoid.objects.left)
    (z : Space.points B S hS (yoneda.obj (Space.schemeSiteObject B hS hPU))) (u'' : U''.left)
    (hz : Space.pointsToScheme B S hS _ z =
      (eqToHom (P.objects_eq.trans R.objects_eq).symm).left.base u'') :
    Space.pointsToScheme B S hS (Space.schemeSiteObject B hS K.contains_objects)
        (Space.pointsMap B S hS _ (yoneda.map (Space.schemeSiteMap B hS hRU K.contains_objects
          R.hom.mapObjects))
          (Space.pointsMap B S hS _ (yoneda.map (Space.schemeSiteMap B hS hPU hRU
            P.inclusion.mapObjects)) z)) = g.left.base u'' := by
  rw [Space.pointsToScheme_pointsMap_yoneda, Space.pointsToScheme_pointsMap_yoneda, hz]
  show (R.hom.mapObjects.left.base (P.inclusion.mapObjects.left.base
    ((eqToHom (P.objects_eq.trans R.objects_eq).symm).left.base u''))) = _
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left,
    P.mapObjects_eq, R.mapObjects_eq, eqToHom_trans_assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]

end Chain

end AlgebraicGeometry.Stack.EtaleLocalStructure

namespace AlgebraicGeometry.Stack

open EtaleLocalStructure

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0DU3.** Let `𝒳` be an algebraic stack over `S` which is quasi-DM (Stacks 050D) with
separated diagonal `Δ_{𝒳/S}` (Stacks 04XB), and let `x ∈ |𝒳|`. Then there is a 1-morphism of
algebraic stacks `g : 𝒰 ⟶ 𝒳` such that

1. some point of `|𝒰|` maps to `x`,
2. `g` is representable by algebraic spaces and étale,
3. `𝒰` is the quotient stack `[U/R]` of (the realization of) a groupoid scheme `(U, R, s, t, c)`
   with `U` and `R` affine and `s`, `t` finite, flat and locally of finite presentation: there is
   an equivalence over the site between that quotient stack and `𝒰`.

The parenthetical equivalent hypothesis of the source (`I_𝒳 ⟶ 𝒳` locally quasi-finite and
separated) is Stacks 0CL0, parts (1) and (5). -/
@[stacks 0DU3]
theorem exists_etale_quotientStack_of_isQuasiDM (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hQ : AlgebraicStacks.IsAbsolutelyQuasiDM B S hS B.contains_terminal 𝒳)
    (hΔ : Stack.IsSeparated.{u, u, u + 1} B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (structureMorphism B S hS 𝒳).hom))
    (x : AlgebraicStacks.points B S hS 𝒳) :
    ∃ (𝒰 : AlgebraicStacks.{u, w} B S hS) (g : 𝒰 ⟶ 𝒳),
      (∃ v, AlgebraicStacks.pointsMap B S hS g v = x) ∧
      (IsRepresentableByAlgebraicSpaces B S hS g.hom.hom ∧ IsEtale B S hS g) ∧
      ∃ (G : GroupoidScheme S) (hU : B.Contains G.objects.left) (hR : B.Contains G.arrows.left)
        (hP : B.Contains (pullback G.source G.target).left),
        IsAffine G.objects.left ∧ IsAffine G.arrows.left ∧
        IsFinite G.source.left ∧ Flat G.source.left ∧ LocallyOfFinitePresentation G.source.left ∧
        IsFinite G.target.left ∧ Flat G.target.left ∧ LocallyOfFinitePresentation G.target.left ∧
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (quotientStack (G.realization B hS hU hR hP)).p 𝒰.val.val.p) := by
  obtain ⟨K, z, hz⟩ := exists_chartGroupoid 𝒳 hQ hΔ x
  have : IsAffine K.groupoid.objects.left := K.isAffine_U
  have : Flat K.groupoid.source.left := K.flat_s
  have : Flat K.groupoid.target.left := K.flat_t
  have : LocallyOfFinitePresentation K.groupoid.source.left := K.lfp_s
  have : LocallyOfFinitePresentation K.groupoid.target.left := K.lfp_t
  have : _root_.AlgebraicGeometry.IsSeparated K.groupoid.source.left := K.separated_s
  have : _root_.AlgebraicGeometry.IsSeparated K.groupoid.target.left := K.separated_t
  have : LocallyOfFiniteType K.groupoid.source.left := K.lft_s
  have : LocallyOfFiniteType K.groupoid.target.left := K.lft_t
  let D : Space.QuasiSplittingSituation.{u} :=
    { S := S
      groupoid := K.groupoid
      u := Space.pointsToScheme B S hS K.U z
      sourceQuasiFiniteAtIdentity :=
        (AlgebraicGeometry.forall_quasiFiniteAt_iff K.groupoid.source.left).mpr
          ⟨K.lft_s, K.lqf_s⟩ _ }
  have : IsAffine D.groupoid.objects.left := K.isAffine_U
  have : Flat D.groupoid.source.left := K.flat_s
  have : Flat D.groupoid.target.left := K.flat_t
  have : LocallyOfFinitePresentation D.groupoid.source.left := K.lfp_s
  have : LocallyOfFinitePresentation D.groupoid.target.left := K.lfp_t
  obtain ⟨U', gp, R', U'', j, u'', -, -, haff, -, het, hbase, -, -, hqs'⟩ :=
    GroupoidScheme.exists_isAffine_isQuasiSplitAt_of_quasiSplittingSituation D B hS
      K.contains_objects K.contains_arrows K.contains_pullback
      (BigFppfSite.residueField_spec_contains B K.contains_objects D.u)
  let g : U'' ⟶ K.groupoid.objects := j ≫ R'.hom.mapObjects
  have : Etale g.left := het
  have : IsAffine U''.left := haff
  have hU'' : B.Contains U''.left :=
    BigFppfSite.contains_of_locallyOfFinitePresentation B g.left K.contains_objects
  let R := AlgebraicGeometry.GroupoidScheme.restrict K.groupoid g
  obtain ⟨Pq⟩ := hqs' R
  let P := Pq.toOpenFiniteSubgroupoid
  obtain ⟨hPU, hPR, hPP, hRU, hRR, hRP, algP, algR, Ψ, -, -, -, hchain, hpts, hA₁, hA₂, hfs, hfls,
    hlfs, hft, hflt, hlft⟩ := exists_etale_quotientStack_of_openFiniteSubgroupoid K g hU'' R P
  obtain ⟨z'', hz''⟩ := Space.surjective_pointsToScheme B S hS (Space.schemeSiteObject B hS hPU)
    ((eqToHom (P.objects_eq.trans R.objects_eq).symm).left.base u'')
  refine ⟨smallAlgebraicQuotientStack.{u, w} (P.subgroupoid.realization B hS hPU hPR hPP) algP,
    _, ⟨smallQuotientStackPoint _ algP z'', ?_⟩,
    ⟨hchain.1, AlgebraicStacks.isEtale_of_isRelativelyEtale B S hS _ hchain⟩, P.subgroupoid,
    hPU, hPR, hPP, hA₁, hA₂, hfs, hfls, hlfs, hft, hflt, hlft,
    ⟨smallQuotientStackEquivalenceOver _⟩⟩
  rw [hpts z'', ← hz]
  congr 2
  exact Space.injective_pointsToScheme B S hS (Space.schemeSiteObject B hS K.contains_objects)
    ((pointsToScheme_pointsMap_subgroupoid K g R P hU'' hRU hPU z'' u'' hz'').trans hbase)

end AlgebraicGeometry.Stack

end
