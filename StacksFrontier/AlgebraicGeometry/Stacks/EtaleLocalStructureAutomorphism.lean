module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureStabilizerFinite
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackSubgroupoidAutomorphism

/-!
# An étale quotient chart preserving the automorphism group at a point (Stacks 0DU4)

Let `𝒳` be an algebraic stack which is quasi-DM with separated diagonal and let `x ∈ |𝒳|` be a
point at which the automorphism group of `𝒳` is finite (Remark 0DTU). **Stacks 0DU4** produces a
1-morphism `g : 𝒰 ⟶ 𝒳` with

1. a point `v ∈ |𝒰|` over `x` at which `g` induces an isomorphism between automorphism groups
   (Stacks 0DTW),
2. `g` representable by algebraic spaces and étale,
3. `𝒰 = [U/P]` for a groupoid scheme `(U, P, s, t, c)` with `U`, `P` affine and `s`, `t` finite,
   flat and locally of finite presentation.

The proof is the source's. The quotient chart `[U/R] ⟶ 𝒳` through `x` of the proof of Stacks 0DU3
(`AlgebraicGeometry.Stack.EtaleLocalStructure.exists_chartGroupoid`) has finitely many stabilizer
points over the chart point `u`, because the automorphism group at `x` is finite
(`AlgebraicGeometry.Stack.EtaleLocalStructure.ChartGroupoid.finite_stabilizer`). So Stacks 0DTE
applies: over an affine elementary étale neighbourhood `(U'', u'') ⟶ (U, u)` the restriction
`R''` of `R` is split over `u''`, by a splitting `P ⊆ R''`. Then
`[U''/P] ⟶ [U''/R''] ⟶ [U/R] ⟶ 𝒳` is representable by algebraic spaces and étale (Stacks 0DU2,
`AlgebraicGeometry.Stack.EtaleLocalStructure.exists_etale_quotientStack_of_openFiniteSubgroupoid`),
and since `P` contains the stabilizer over `u''` it induces an isomorphism on automorphism groups
at the point of `u''`
(`AlgebraicGeometry.Stack.inducesIsomorphismAt_of_quotientStackMap_realization`).

## Main results

* `AlgebraicGeometry.Stack.exists_etale_quotientStack_inducesIsomorphismAt`: **Stacks 0DU4**.

## Implementation notes

The hypotheses are those of `AlgebraicGeometry.Stack.exists_etale_quotientStack_of_isQuasiDM`
(Stacks 0DU3): quasi-DM in the absolute sense of Stacks 050D and `Δ_{𝒳/S}` separated in the sense
of Stacks 04XB, the reading of Stacks 0CL0 that the source's parenthetical refers to. "The
automorphism group of `𝒳` at `x` is finite" is
`AlgebraicGeometry.Stack.AutomorphismGroupHasProperty` (Stacks 0DTU) at the property
`AlgebraicGeometry.Stack.EtaleLocalStructure.IsFiniteOverBase`: for every field-valued
representative of `x` the automorphism group algebraic space is finite over the field.

`𝒰` is the small model of the quotient stack of the realization of `P`
(`AlgebraicGeometry.Stack.smallAlgebraicQuotientStack`); clause (3) is the equivalence over the
site between it and the quotient stack of the realization.

## References

* [Stacks Project, Tag 0DU4](https://stacks.math.columbia.edu/tag/0DU4)
* [Stacks Project, Tag 0DTE](https://stacks.math.columbia.edu/tag/0DTE)
* [Stacks Project, Tag 0DTU](https://stacks.math.columbia.edu/tag/0DTU)
* [Stacks Project, Tag 0DTW](https://stacks.math.columbia.edu/tag/0DTW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Groupoids

universe u w

namespace AlgebraicGeometry.Stack

open EtaleLocalStructure

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0DU4.** Let `𝒳` be an algebraic stack over `S` which is quasi-DM (Stacks 050D) with
separated diagonal `Δ_{𝒳/S}` (Stacks 04XB), and let `x ∈ |𝒳|` be a point at which the automorphism
group of `𝒳` is finite (Remark 0DTU). Then there is a 1-morphism of algebraic stacks
`g : 𝒰 ⟶ 𝒳` such that

1. some point `v ∈ |𝒰|` maps to `x` and `g` induces an isomorphism between the automorphism
   groups at `v` and `x` (Stacks 0DTW),
2. `g` is representable by algebraic spaces and étale,
3. `𝒰` is the quotient stack `[U/R]` of (the realization of) a groupoid scheme `(U, R, s, t, c)`
   with `U` and `R` affine and `s`, `t` finite, flat and locally of finite presentation: there is
   an equivalence over the site between that quotient stack and `𝒰`.

The parenthetical equivalent hypothesis of the source (`I_𝒳 ⟶ 𝒳` locally quasi-finite and
separated) is Stacks 0CL0, parts (1) and (5). -/
@[stacks 0DU4]
theorem exists_etale_quotientStack_inducesIsomorphismAt (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hQ : AlgebraicStacks.IsAbsolutelyQuasiDM B S hS B.contains_terminal 𝒳)
    (hΔ : Stack.IsSeparated.{u, u, u + 1} B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (structureMorphism B S hS 𝒳).hom))
    (x : AlgebraicStacks.points B S hS 𝒳)
    (hAut : AutomorphismGroupHasProperty B S hS (IsFiniteOverBase B S hS) x) :
    ∃ (𝒰 : AlgebraicStacks.{u, w} B S hS) (g : 𝒰 ⟶ 𝒳),
      (∃ v, AlgebraicStacks.pointsMap B S hS g v = x ∧ InducesIsomorphismAt B S hS g v) ∧
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
  have : LocallyQuasiFinite K.groupoid.source.left := K.lqf_s
  have hfin := K.finite_stabilizer z (hz ▸ hAut)
  have hqf : ∀ r, quasiFiniteAt K.groupoid.source.left r :=
    (AlgebraicGeometry.forall_quasiFiniteAt_iff K.groupoid.source.left).mpr ⟨K.lft_s, K.lqf_s⟩
  let D : Space.SplittingSituation.{u} :=
    { S := S
      groupoid := K.groupoid
      u := Space.pointsToScheme B S hS K.U z
      stabilizer_finite := hfin
      source_quasiFiniteAt := fun _ _ => hqf _ }
  obtain ⟨U', gp, R', U'', j, u'', haff, -, het, hbase, -, hsplit⟩ :=
    GroupoidScheme.exists_isAffine_isSplitAt D B hS K.contains_objects K.contains_arrows
      K.contains_pullback (BigFppfSite.residueField_spec_contains B K.contains_objects D.u)
  let g : U'' ⟶ K.groupoid.objects := j ≫ R'.hom.mapObjects
  have : Etale g.left := het
  have : IsAffine U''.left := haff
  have hU'' : B.Contains U''.left :=
    BigFppfSite.contains_of_locallyOfFinitePresentation B g.left K.contains_objects
  let R := AlgebraicGeometry.GroupoidScheme.restrict K.groupoid g
  obtain ⟨P⟩ := AlgebraicGeometry.GroupoidScheme.isSplitAt_of_iteratedRestriction' R'
    (AlgebraicGeometry.GroupoidScheme.restrict R'.groupoid j) R u''
    (hsplit (AlgebraicGeometry.GroupoidScheme.restrict R'.groupoid j))
  let P' := P.toOpenFiniteSubgroupoid
  obtain ⟨hPU, hPR, hPP, hRU, hRR, hRP, algP, algR, Ψ, -, hΨfull, hΨfaith, hchain, hpts, hA₁, hA₂,
    hfs, hfls, hlfs, hft, hflt, hlft⟩ :=
    exists_etale_quotientStack_of_openFiniteSubgroupoid K g hU'' R P'
  obtain ⟨z'', hz''⟩ := Space.surjective_pointsToScheme B S hS (Space.schemeSiteObject B hS hPU)
    ((eqToHom (P'.objects_eq.trans R.objects_eq).symm).left.base u'')
  let HR := P'.subgroupoid.realization B hS hPU hPR hPP
  let KR := R.groupoid.realization B hS hRU hRR hRP
  let Φ := GroupoidScheme.Hom.realization B hS P'.inclusion hPU hPR hPP hRU hRR hRP
  let f := smallQuotientStackMap.{u, w} Φ algP algR ≫ Ψ
  refine ⟨smallAlgebraicQuotientStack.{u, w} HR algP, f,
    ⟨smallQuotientStackPoint _ algP z'', ?_, ?_⟩,
    ⟨hchain.1, AlgebraicStacks.isEtale_of_isRelativelyEtale B S hS _ hchain⟩, P'.subgroupoid,
    hPU, hPR, hPP, hA₁, hA₂, hfs, hfls, hlfs, hft, hflt, hlft,
    ⟨smallQuotientStackEquivalenceOver _⟩⟩
  · rw [hpts z'', ← hz]
    congr 2
    apply Space.injective_pointsToScheme B S hS (Space.schemeSiteObject B hS K.contains_objects)
    exact (pointsToScheme_pointsMap_subgroupoid K g R P' hU'' hRU hPU z'' u'' hz'').trans hbase
  · -- the automorphism clause: `P` contains the stabilizer over `u''`
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
    exact inducesIsomorphismAt_of_quotientStackMap_realization B S hS P'.inclusion hPU hPR hPP
      hRU hRR hRP P'.objects_eq P'.mapObjects_eq ((eqToHom R.objects_eq.symm).left.base u'')
      P.contains_stabilizer f E hE F hF (Iso.refl _) p q.value hx (Iso.refl _)
      (IsHomLift.id rfl)

end AlgebraicGeometry.Stack

end
