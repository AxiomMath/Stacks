module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackSeparation
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackSubgroupoidSelfProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeQuasiDMExistence

/-!
# Stacks 0DU5 from the quotient chart, with the quasi-compact fibre as the only input

Let `𝒳` be an algebraic stack which is quasi-DM with separated diagonal and let `x ∈ |𝒳|`. The
proof of **Stacks 0DU5** runs the proof of **Stacks 0DU3** up to the quotient chart
`[U/R] ⟶ 𝒳` through `x` with `U` affine
(`AlgebraicGeometry.Stack.EtaleLocalStructure.exists_chartGroupoid`), and then, instead of the
quasi-splitting of Stacks 04S0, uses the **strong** splitting of Stacks 04RZ. The one extra input
the strong splitting needs is that the fibre `F = Spec κ(u) ×_{U, t} R` of the target of the
chart groupoid over the chart point `u` is quasi-compact; the source gets it from the hypothesis
that `x` is representable by a quasi-compact morphism `Spec k ⟶ 𝒳` (**Stacks 0DTK**) together
with affineness of `U`.

This file takes the quotient chart together with that quasi-compactness as an explicit
hypothesis `hChart` — a statement about schemes, not a Stacks tag — and derives the whole of
Stacks 0DU5 from it. Nothing is registered here; the registration lives with the proof of
`hChart`.

## The argument

The strong splitting `P ⊆ R|_{U''}` over an affine elementary étale neighbourhood
`(U'', u'') ⟶ (U, u)` comes from
`AlgebraicGeometry.Space.exists_isAffine_strongSplitting_of_compactSpace_targetFibre`, and is a
groupoid scheme with affine object and arrow schemes and finite, flat, locally finitely presented
source and target — clause (3). The étale chain
`[U''/P] ⟶ [U''/R|_{U''}] ⟶ [U/R] ⟶ 𝒳` is
`AlgebraicGeometry.Stack.EtaleLocalStructure.exists_etale_quotientStack_of_openFiniteSubgroupoid`
(**Stacks 0DU2**) — clause (2). Since the source and the target of `P` are finite they are
locally quasi-finite, so `[U''/P]` is quasi-DM by **Stacks 0DTY**, part (4), and the residual
gerbes at the point of `[U''/P]` over `u''` and at `x` exist by **Stacks 06UI**
(`AlgebraicGeometry.Stack.exists_isResidualGerbeAt_of_isAbsolutelyQuasiDM`). Finally `P`
contains every arrow of `R|_{U''}` with source and target `u''`, so the self 2-fibre product
comparison at that point is an equivalence
(`AlgebraicGeometry.Stack.hasSelfProductEquivalenceAt_of_quotientStackMap_realization`), and
**Stacks 0DTI** turns that into an isomorphism of residual gerbes — clause (1).

## Main results

* `Stack.exists_etale_quotientStack_residualGerbeMap_of_compactSpace_targetFibre`:
  the three clauses of Stacks 0DU5, from a quotient chart whose fibre is quasi-compact.

## References

* [Stacks Project, Tag 04RZ](https://stacks.math.columbia.edu/tag/04RZ)
* [Stacks Project, Tag 06UI](https://stacks.math.columbia.edu/tag/06UI)
* [Stacks Project, Tag 0DTI](https://stacks.math.columbia.edu/tag/0DTI)
* [Stacks Project, Tag 0DTK](https://stacks.math.columbia.edu/tag/0DTK)
* [Stacks Project, Tag 0DTY](https://stacks.math.columbia.edu/tag/0DTY)
* [Stacks Project, Tag 0DU2](https://stacks.math.columbia.edu/tag/0DU2)
* [Stacks Project, Tag 0DU3](https://stacks.math.columbia.edu/tag/0DU3)
* [Stacks Project, Tag 0DU5](https://stacks.math.columbia.edu/tag/0DU5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Groupoids

universe u w

namespace AlgebraicGeometry.Stack

open EtaleLocalStructure

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0DU5, from the quasi-compactness of the fibre of the quotient chart.** Let `𝒳` be an
algebraic stack over `S` which is quasi-DM (Stacks 050D), and let `x ∈ |𝒳|`. Assume there are a
quotient chart `[U/R] ⟶ 𝒳` of `𝒳`
(`AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid`) and a point `z` of `U` over `x`
such that the fibre `Spec κ(u) ×_{U, t} R` of the target of the groupoid over the point `u` of
`U` underlying `z` is quasi-compact. Then there is a 1-morphism of algebraic stacks
`g : 𝒰 ⟶ 𝒳` such that

1. some point `v ∈ |𝒰|` maps to `x`, the residual gerbes of `𝒰` at `v` and of `𝒳` at `x` exist,
   and the 1-morphism between them induced by `g` (Stacks 0DTH) is an isomorphism for every
   choice of them;
2. `g` is representable by algebraic spaces and étale;
3. `𝒰` is the quotient stack `[U/R]` of (the realization of) a groupoid scheme `(U, R, s, t, c)`
   with `U` and `R` affine and `s`, `t` finite, flat and locally of finite presentation: there is
   an equivalence over the site between that quotient stack and `𝒰`.

See the module documentation for the proof. The quotient chart comes from the first part of the
proof of Stacks 0DU3 (`AlgebraicGeometry.Stack.EtaleLocalStructure.exists_chartGroupoid`, which
needs `𝒳` to be quasi-DM with separated diagonal), and the quasi-compactness of the fibre is the
one place the hypothesis of Stacks 0DU5 that `x` is representable by a quasi-compact morphism
from the spectrum of a field is used. -/
theorem exists_etale_quotientStack_residualGerbeMap_of_compactSpace_targetFibre
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hQ : AlgebraicStacks.IsAbsolutelyQuasiDM B S hS B.contains_terminal 𝒳)
    (x : AlgebraicStacks.points B S hS 𝒳)
    (hChart : ∃ (K : ChartGroupoid B S hS 𝒳) (z : Space.points B S hS (yoneda.obj K.U)),
      AlgebraicStacks.pointsMap B S hS K.map (K.point z) = x ∧
      CompactSpace ↑(pullback (K.groupoid.objects.left.fromSpecResidueField
        (Space.pointsToScheme B S hS K.U z)) K.groupoid.target.left)) :
    ∃ (𝒰 : AlgebraicStacks.{u, w} B S hS) (g : 𝒰 ⟶ 𝒳)
      (v : AlgebraicStacks.points B S hS 𝒰),
      (AlgebraicStacks.pointsMap B S hS g v = x ∧
        (∃ P : ObjectProperty 𝒰.val.val.obj, IsResidualGerbeAt B S hS 𝒰 v P) ∧
        (∃ Q : ObjectProperty 𝒳.val.val.obj, IsResidualGerbeAt B S hS 𝒳 x Q) ∧
        ∀ (P : ObjectProperty 𝒰.val.val.obj) (Q : ObjectProperty 𝒳.val.val.obj)
          (hv : IsResidualGerbeAt B S hS 𝒰 v P)
          (hx : IsResidualGerbeAt B S hS 𝒳 (AlgebraicStacks.pointsMap B S hS g v) Q),
          Nonempty (Functor.IsEquivalenceOver
            (fullSubcategoryAlgebraicStack 𝒰 P hv.2.choose).val.val.p
            (fullSubcategoryAlgebraicStack 𝒳 Q hx.2.choose).val.val.p
            (CatFiberedInGroupoids.homFunctor
              (residualGerbeMap B S hS g hv.2.choose hx.2.choose
                (map_mem_of_isResidualGerbeAt B S hS g v _ rfl hv hx)).hom))) ∧
      (IsRepresentableByAlgebraicSpaces B S hS g.hom.hom ∧ IsEtale B S hS g) ∧
      ∃ (G : GroupoidScheme S) (hU : B.Contains G.objects.left) (hR : B.Contains G.arrows.left)
        (hP : B.Contains (pullback G.source G.target).left),
        IsAffine G.objects.left ∧ IsAffine G.arrows.left ∧
        IsFinite G.source.left ∧ Flat G.source.left ∧ LocallyOfFinitePresentation G.source.left ∧
        IsFinite G.target.left ∧ Flat G.target.left ∧ LocallyOfFinitePresentation G.target.left ∧
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (quotientStack (G.realization B hS hU hR hP)).p 𝒰.val.val.p) := by
  obtain ⟨K, z, hz, hcpt⟩ := hChart
  have : IsAffine K.groupoid.objects.left := K.isAffine_U
  have : Flat K.groupoid.source.left := K.flat_s
  have : Flat K.groupoid.target.left := K.flat_t
  have : LocallyOfFinitePresentation K.groupoid.source.left := K.lfp_s
  have : LocallyOfFinitePresentation K.groupoid.target.left := K.lfp_t
  have : _root_.AlgebraicGeometry.IsSeparated K.groupoid.source.left := K.separated_s
  have : _root_.AlgebraicGeometry.IsSeparated K.groupoid.target.left := K.separated_t
  have : LocallyOfFiniteType K.groupoid.source.left := K.lft_s
  have : LocallyOfFiniteType K.groupoid.target.left := K.lft_t
  have : LocallyQuasiFinite K.groupoid.source.left := K.lqf_s
  have := locallyQuasiFinite_target_of_source S K.groupoid
  obtain ⟨U'', g, u'', haffU, het, hbase, -, hall⟩ :=
    AlgebraicGeometry.Space.exists_isAffine_strongSplitting_of_compactSpace_targetFibre
      K.groupoid (Space.pointsToScheme B S hS K.U z) B hS K.contains_objects K.contains_arrows
      K.contains_pullback (BigFppfSite.residueField_spec_contains B K.contains_objects _)
  let R := AlgebraicGeometry.GroupoidScheme.restrict K.groupoid g
  obtain ⟨⟨hRsf, hRsl, hRtf, hRtl⟩, Psplit, hHo, hHa, hHsfin, hHsf, hHsl, hHtfin, hHtf, hHtl⟩ :=
    hall R
  have hU'' : B.Contains U''.left :=
    BigFppfSite.contains_of_locallyOfFinitePresentation B g.left K.contains_objects
  let P' := Psplit.toOpenFiniteSubgroupoid
  obtain ⟨hPU, hPR, hPP, hRU, hRR, hRP, algP, algR, Ψ, -, hΨfull, hΨfaith, hchain, hpts, hA₁, hA₂,
    hfs, hfls, hlfs, hft, hflt, hlft⟩ :=
    exists_etale_quotientStack_of_openFiniteSubgroupoid K g hU'' R P'
  obtain ⟨z'', hz''⟩ := Space.surjective_pointsToScheme B S hS (Space.schemeSiteObject B hS hPU)
    ((eqToHom (P'.objects_eq.trans R.objects_eq).symm).left.base u'')
  let HR := P'.subgroupoid.realization B hS hPU hPR hPP
  let KR := R.groupoid.realization B hS hRU hRR hRP
  let Φ := GroupoidScheme.Hom.realization B hS P'.inclusion hPU hPR hPP hRU hRR hRP
  let 𝒰 := smallAlgebraicQuotientStack.{u, w} HR algP
  let f : 𝒰 ⟶ 𝒳 := smallQuotientStackMap.{u, w} Φ algP algR ≫ Ψ
  let v : AlgebraicStacks.points B S hS 𝒰 := smallQuotientStackPoint HR algP z''
  -- the point of `𝒰` lies over `x`
  have hfv : AlgebraicStacks.pointsMap B S hS f v = x := by
    rw [hpts z'', ← hz]
    congr 2
    exact Space.injective_pointsToScheme B S hS (Space.schemeSiteObject B hS K.contains_objects)
      ((pointsToScheme_pointsMap_subgroupoid K g R P' hU'' hRU hPU z'' u'' hz'').trans hbase)
  -- `𝒰` is quasi-DM: the source and the target of `P` are finite, hence locally quasi-finite
  have := hHsf
  have := hHsl
  have := hHtf
  have := hHtl
  have := hHtfin
  have : LocallyQuasiFinite P'.subgroupoid.source.left := inferInstance
  have : LocallyQuasiFinite P'.subgroupoid.target.left := inferInstance
  have h𝒰DM : AlgebraicStacks.IsAbsolutelyQuasiDM B S hS B.contains_terminal 𝒰 :=
    isAbsolutelyQuasiDM_of_isLocallyQuasiFinite_source_target.{u, w} HR 𝒰 B.contains_terminal
      ⟨smallQuotientStackEquivalenceOver _⟩
      (GroupoidScheme.isFlat_realization_source B hS hPU hPR hPP)
      (GroupoidScheme.isFlat_realization_target B hS hPU hPR hPP)
      (GroupoidScheme.isLocallyOfFinitePresentation_realization_source B hS hPU hPR hPP)
      (GroupoidScheme.isLocallyOfFinitePresentation_realization_target B hS hPU hPR hPP)
      ((Space.isLocallyQuasiFinite_yoneda_map_iff B S hS
        (Space.schemeSiteMap B hS hPR hPU P'.subgroupoid.source)).2
          ⟨(inferInstance : LocallyOfFiniteType P'.subgroupoid.source.left),
            (inferInstance : LocallyQuasiFinite P'.subgroupoid.source.left)⟩)
      ((Space.isLocallyQuasiFinite_yoneda_map_iff B S hS
        (Space.schemeSiteMap B hS hPR hPU P'.subgroupoid.target)).2
          ⟨(inferInstance : LocallyOfFiniteType P'.subgroupoid.target.left),
            (inferInstance : LocallyQuasiFinite P'.subgroupoid.target.left)⟩)
  -- the self-product comparison at `v` is an equivalence: `P` contains the stabilizer over `u''`
  have hselfv : HasSelfProductEquivalenceAt B S hS f v := by
    have := P'.arrows_open
    let q := Quot.out z''
    let p := fieldValuedPointMap B S hS _ (smallQuotientStackProjection HR).hom
      (spaceFieldValuedPoint B S hS _ q)
    let E := (smallQuotientStackEquivalence HR).functor
    have hE : E.toFunctor.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _
    let F := BasedFunctor.comp (smallQuotientStackEquivalence KR).inverse Ψ.hom.hom
    have hF : F.toFunctor.FullyFaithful :=
      (Functor.FullyFaithful.ofFullyFaithful
        (smallQuotientStackEquivalence KR).inverse.toFunctor).comp
        (@Functor.FullyFaithful.ofFullyFaithful _ _ _ _ _ hΨfull hΨfaith)
    have hz₀ : Space.pointsToScheme B S hS _ z'' =
        (BigFppfOver.toScheme B S hS).map q.value (IsLocalRing.closedPoint q.carrier) :=
      (congrArg (Space.pointsToScheme B S hS _) (Quot.out_eq z'')).symm
    have hu : (eqToHom P'.objects_eq.symm).left.base
        ((eqToHom R.objects_eq.symm).left.base u'') =
          (eqToHom (P'.objects_eq.trans R.objects_eq).symm).left.base u'' := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, eqToHom_trans]
    have hx : GroupoidScheme.Hom.IsOverPoint B hS hPU hPR hPP
        ((eqToHom P'.objects_eq.symm).left.base ((eqToHom R.objects_eq.symm).left.base u''))
        p.base q.value := by
      intro τ
      have : Subsingleton ((Space.siteToOver B hS).obj p.base).left :=
        inferInstanceAs (Subsingleton (Spec (CommRingCat.of q.carrier)))
      rw [hu, ← hz'', hz₀, Subsingleton.elim τ (IsLocalRing.closedPoint q.carrier)]
      rfl
    exact hasSelfProductEquivalenceAt_of_quotientStackMap_realization B S hS P'.inclusion
      hPU hPR hPP hRU hRR hRP P'.objects_eq P'.mapObjects_eq
      ((eqToHom R.objects_eq.symm).left.base u'') Psplit.contains_stabilizer f E hE F hF
      (Iso.refl _) p q.value hx (Iso.refl _) (IsHomLift.id rfl)
  exact ⟨𝒰, f, v, ⟨hfv,
    exists_isResidualGerbeAt_of_isAbsolutelyQuasiDM.{u, w} B S hS B.contains_terminal 𝒰 h𝒰DM v,
    exists_isResidualGerbeAt_of_isAbsolutelyQuasiDM.{u, w} B S hS B.contains_terminal 𝒳 hQ x,
    fun P Q hv hx =>
      isEquivalenceOver_residualGerbeMap_of_hasSelfProductEquivalenceAt B S hS f v P Q hv hx
        hselfv⟩,
    ⟨hchain.1, AlgebraicStacks.isEtale_of_isRelativelyEtale B S hS _ hchain⟩, P'.subgroupoid,
    hPU, hPR, hPP, hA₁, hA₂, hHsfin, hHsf, hHsl, hHtfin, hHtf, hHtl,
    ⟨smallQuotientStackEquivalenceOver _⟩⟩

end AlgebraicGeometry.Stack

end
