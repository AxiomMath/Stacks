module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.OpenSubgroupoidQuotientStackEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatQuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.SmallQuotientStackMap

/-!
# The quotient stack of an open subgroupoid (Stacks 0DU2), with nothing carried

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces with `s`, `t` flat and locally of finite
presentation, and let `P ⊆ R` be an open subspace such that `(U, P, s|_P, t|_P, c|_P)` is a
groupoid in algebraic spaces. **Stacks 0DU2** says that `[U/P] ⟶ [U/R]` is a morphism of
algebraic stacks which is representable by algebraic spaces, surjective and étale.

An open subgroupoid is encoded, as in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.OpenSubgroupoidQuotientStack`, as a
morphism `φ : G ⟶ H` of groupoids in algebraic spaces whose map on objects is an isomorphism and
whose map on arrows is an open immersion; the 1-morphism is `[φ]` of Stacks 046Q.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_quotientStackMap_of_isOpenImmersion`:
  `[φ]` is representable by algebraic spaces.
* `AlgebraicGeometry.Stack.isAlgebraicStack_representable_surjective_etale_quotientStackMap`:
  **Stacks 0DU2.**

## The argument

Both quotient stacks are algebraic by Stacks 06FI
(`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_flat`), `s|_P` and `t|_P` being flat
and locally of finite presentation as composites of an open immersion, `s` or `t`, and an
isomorphism. Representability: the arrow map is a monomorphism, so `[φ]` is faithful, and
Stacks 04Y5 for 1-morphisms of algebraic quotient stacks
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_quotientStackMap_of_faithful`) turns
faithfulness into representability. Surjectivity is Stacks 06D7 from surjectivity on objects.
Étaleness is `AlgebraicGeometry.Stack.hasRelativeProperty_etale_quotientStackMap`
(Stacks 04XD, 04Y4, 0DU1).

## References

* [Stacks Project, Tag 0DU2](https://stacks.math.columbia.edu/tag/0DU2)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} {A : AlgebraicSpaces C S hS}

/-- **`[φ]` is representable by algebraic spaces** when `φ` is the inclusion of an open
subgroupoid of a groupoid whose source and target are flat and locally of finite presentation:
both quotient stacks are algebraic (Stacks 06FI), `[φ]` is faithful because the arrow map is a
monomorphism, and Stacks 04Y5 turns faithfulness into representability. -/
theorem isRepresentableByAlgebraicSpaces_quotientStackMap_of_isOpenImmersion
    {G H : GroupoidInAlgebraicSpaces C S hS A} (φ : GroupoidInAlgebraicSpaces.Hom G H)
    (hopen : Space.IsOpenImmersion C S hS φ.toGroupoidHom.mapArrows)
    (hobj : IsIso φ.toGroupoidHom.mapObjects)
    (hsflat : Space.IsFlat C S hS H.source.hom) (htflat : Space.IsFlat C S hS H.target.hom)
    (hslfp : Space.IsLocallyOfFinitePresentation C S hS H.source.hom)
    (htlfp : Space.IsLocallyOfFinitePresentation C S hS H.target.hom) :
    IsRepresentableByAlgebraicSpaces C S hS (quotientStackMap φ) :=
  isRepresentableByAlgebraicSpaces_quotientStackMap_of_faithful.{u, u} φ
    (isAlgebraicStack_quotientStack_of_flat.{u, u} G
      (isFlat_source_of_mapArrows_isOpenImmersion φ hopen hobj hsflat)
      (isFlat_target_of_mapArrows_isOpenImmersion φ hopen hobj htflat)
      (isLocallyOfFinitePresentation_source_of_mapArrows_isOpenImmersion φ hopen hobj hslfp)
      (isLocallyOfFinitePresentation_target_of_mapArrows_isOpenImmersion φ hopen hobj htlfp))
    (isAlgebraicStack_quotientStack_of_flat.{u, u} H hsflat htflat hslfp htlfp)
    (faithful_quotientStackMap_of_mono φ (mono_mapArrows_of_isOpenImmersion φ hopen))

/-- **Stacks 0DU2.** Let `(U, R, s, t, c)` be a groupoid in algebraic spaces (here over an
algebraic space `A` over `S`, which contains the case of a groupoid over `S`) with `s`, `t` flat
and locally of finite presentation, and let `P ⊆ R` be an open subspace such that
`(U, P, s|_P, t|_P, c|_P)` is a groupoid in algebraic spaces; that is, let `φ : G ⟶ H` be a
morphism of groupoids in algebraic spaces whose map on objects is an isomorphism and whose map on
arrows is an open immersion. Then `[U/P]` and `[U/R]` are algebraic stacks, and
`[φ] : [U/P] ⟶ [U/R]` is representable by algebraic spaces, surjective and étale, the last two in
the sense of Stacks 03YK. -/
@[stacks 0DU2]
theorem isAlgebraicStack_representable_surjective_etale_quotientStackMap
    {G H : GroupoidInAlgebraicSpaces C S hS A} (φ : GroupoidInAlgebraicSpaces.Hom G H)
    (hopen : Space.IsOpenImmersion C S hS φ.toGroupoidHom.mapArrows)
    (hobj : IsIso φ.toGroupoidHom.mapObjects)
    (hsflat : Space.IsFlat C S hS H.source.hom) (htflat : Space.IsFlat C S hS H.target.hom)
    (hslfp : Space.IsLocallyOfFinitePresentation C S hS H.source.hom)
    (htlfp : Space.IsLocallyOfFinitePresentation C S hS H.target.hom) :
    IsAlgebraicStack.{u, w} C S hS (quotientStack G) ∧
      IsAlgebraicStack.{u, w} C S hS (quotientStack H) ∧
      ∃ hrep : IsRepresentableByAlgebraicSpaces C S hS (quotientStackMap φ),
        HasRelativeProperty.{u, u + 1, u + 1, u} C S hS
          (Space.surjectiveMorphismProperty C S hS) (quotientStackMapCFGHom φ) hrep ∧
        HasRelativeProperty.{u, u + 1, u + 1, u} C S hS
          (Space.etaleMorphisms C S hS) (quotientStackMapCFGHom φ) hrep := by
  have hrep := isRepresentableByAlgebraicSpaces_quotientStackMap_of_isOpenImmersion φ hopen hobj
    hsflat htflat hslfp htlfp
  refine ⟨isAlgebraicStack_quotientStack_of_flat G
      (isFlat_source_of_mapArrows_isOpenImmersion φ hopen hobj hsflat)
      (isFlat_target_of_mapArrows_isOpenImmersion φ hopen hobj htflat)
      (isLocallyOfFinitePresentation_source_of_mapArrows_isOpenImmersion φ hopen hobj hslfp)
      (isLocallyOfFinitePresentation_target_of_mapArrows_isOpenImmersion φ hopen hobj htlfp),
    isAlgebraicStack_quotientStack_of_flat H hsflat htflat hslfp htlfp, hrep, ?_,
    hasRelativeProperty_etale_quotientStackMap φ hobj hopen hsflat hslfp hrep⟩
  exact (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u + 1, u + 1, u} C S hS
    (quotientStackMapCFGHom φ) hrep).1 (isSurjectiveOnObjects_quotientStackMap φ hobj)

end AlgebraicGeometry.Stack

end
