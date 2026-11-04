module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SourceTargetProductComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoidStabilizerDimension

/-!
# The pre-relation of a self-intersection groupoid

Let `𝒳` be an algebraic stack over `S` and `ξ : U ⟶ 𝒳` a 1-morphism out of the algebraic stack
represented by an object `U` of the big fppf site of `S`. The groupoid in algebraic spaces of
**Stacks 04T4 (4)** that `ξ` carries is
`AlgebraicGeometry.Stack.SelfIntersection.pointGroupoid`, a groupoid over the final algebraic
space, with pre-relation `j = (t, s) : R ⟶ U ×_S U`. Read at the binary product `prod.lift t s`
of presheaves, this pre-relation is unramified, separated or locally quasi-finite when `𝒳` is DM,
has separated relative diagonal, or is quasi-DM over `S`, respectively (**Stacks 050H**).

## Main results

* `AlgebraicGeometry.Stack.SelfIntersection.isUnramified_prodLift_pointGroupoid`:
  **Stacks 050H** part (4) at the pre-relation of the self-intersection groupoid — the
  pre-relation is unramified when `𝒳` is DM over `S`.
* `AlgebraicGeometry.Stack.SelfIntersection.isSeparated_prodLift_pointGroupoid`:
  **Stacks 050H** part (3) there — the pre-relation is separated when the relative diagonal
  `Δ_{𝒳/S}` is.
* `AlgebraicGeometry.Stack.SelfIntersection.isLocallyQuasiFinite_prodLift_pointGroupoid`:
  **Stacks 050H** part (5) there — the pre-relation is locally quasi-finite when `𝒳` is quasi-DM
  over `S`.

## References

* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 06N0](https://stacks.math.columbia.edu/tag/06N0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.SelfIntersection

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (kObj : BigFppfOver B S hS)
  (ξ : schemeStack.{u, w} B S hS kObj ⟶ 𝒳)
  (Rsp : AlgebraicSpaces B S hS)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (AlgebraicStacks.twoFibreProduct B S hS ξ ξ).val.val.p
    (presheafOfCategories (Rsp.obj ⋙ typeToCat)).p)

/-- **Stacks 050H, part (4), at the pre-relation of a self-intersection groupoid.** For `𝒳` DM
over `S`, the morphism `prod.lift t s` out of the arrow space of
`AlgebraicGeometry.Stack.SelfIntersection.pointGroupoid` into the binary product of the object
space with itself is unramified. -/
theorem isUnramified_prodLift_pointGroupoid (h𝒳 : IsDMOver B S hS 𝒳) :
    Space.IsUnramified B S hS
      (prod.lift (pointGroupoid B S hS kObj ξ Rsp eR).target.hom
        (pointGroupoid B S hS kObj ξ Rsp eR).source.hom) :=
  GroupoidInAlgebraicSpaces.isUnramified_prodLift_of_sourceTarget
    (pointGroupoid B S hS kObj ξ Rsp eR) (Space.baseTerminal_yonedaIsTerminal B S hS)
    (isUnramified_sourceTarget_pointGroupoid B S hS kObj ξ Rsp eR h𝒳)

/-- **Stacks 050H, part (3), at the pre-relation of a self-intersection groupoid.** When the
relative diagonal `Δ_{𝒳/S}` is separated in the sense of **Stacks 04XB**, the morphism
`prod.lift t s` out of the arrow space of
`AlgebraicGeometry.Stack.SelfIntersection.pointGroupoid` into the binary product of the object
space with itself is separated. -/
theorem isSeparated_prodLift_pointGroupoid
    (hΔ : Stack.IsSeparated.{u, u, u + 1} B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (structureMorphism B S hS 𝒳).hom)) :
    Space.IsSeparated B S hS
      (prod.lift (pointGroupoid B S hS kObj ξ Rsp eR).target.hom
        (pointGroupoid B S hS kObj ξ Rsp eR).source.hom) :=
  GroupoidInAlgebraicSpaces.isSeparated_prodLift_of_sourceTarget
    (pointGroupoid B S hS kObj ξ Rsp eR) (Space.baseTerminal_yonedaIsTerminal B S hS)
    (isSeparated_sourceTarget_pointGroupoid B S hS kObj ξ Rsp eR hΔ)

/-- **Stacks 050H, part (5), at the pre-relation of a self-intersection groupoid.** For `𝒳`
quasi-DM over `S`, the morphism `prod.lift t s` out of the arrow space of
`AlgebraicGeometry.Stack.SelfIntersection.pointGroupoid` into the binary product of the object
space with itself is locally quasi-finite — hence, local quasi-finiteness of a morphism of
algebraic spaces being **Stacks 03XJ** part (1), also locally of finite type. -/
theorem isLocallyQuasiFinite_prodLift_pointGroupoid (h𝒳 : IsQuasiDMOver B S hS 𝒳) :
    Space.IsLocallyQuasiFinite B S hS
      (prod.lift (pointGroupoid B S hS kObj ξ Rsp eR).target.hom
        (pointGroupoid B S hS kObj ξ Rsp eR).source.hom) :=
  GroupoidInAlgebraicSpaces.isLocallyQuasiFinite_prodLift_of_sourceTarget
    (pointGroupoid B S hS kObj ξ Rsp eR) (Space.baseTerminal_yonedaIsTerminal B S hS)
    (isLocallyQuasiFinite_sourceTarget_pointGroupoid B S hS kObj ξ Rsp eR h𝒳)

end AlgebraicGeometry.Stack.SelfIntersection

end
