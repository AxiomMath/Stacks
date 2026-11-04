module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.FieldPointImage
public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion
public import StacksFrontier.Deformation.ArtinCriteria.SmoothNeighborhood

/-!
# Artin's criterion at a morphism universe one step up

Moduli stacks whose morphisms carry a map of sheaves on the small étale site of an algebraic
space — the stack `Coh_{X/B}` of Stacks 08KB is one — are
`CategoryTheory.CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1}`: their morphisms do not lie in the
universe of the objects of the site.

This file records Artin's criterion at that shape, with axiom [0] given as the fppf stack
condition. It is the instance `v := u + 1`, `w := u` of
`AlgebraicGeometry.Stack.isAlgebraicStack_of_artinAxioms_of_isStack`, which is stated for a
`CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}`, the shape of Stacks 07XY,
`Deformation.Artin.exists_smooth_finiteType_neighborhood`.

## Main results

* `AlgebraicGeometry.Stack.hasSmoothFiniteTypeNeighborhoods_of_artinAxioms_succ`: the conclusion
  of Stacks 07XY for a category fibred in groupoids with morphisms in `Type (u + 1)`.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_artinAxioms_succ`: **Stacks 07Y4** for such a
  category.

## References

* [Stacks Project, Tag 07Y4](https://stacks.math.columbia.edu/tag/07Y4)
* [Stacks Project, Tag 07XY](https://stacks.math.columbia.edu/tag/07XY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 07XY, in the form Artin's criterion consumes it, for a morphism universe one step
up.** A category fibred in groupoids over the big fppf site of a locally Noetherian scheme whose
morphisms lie in `Type (u + 1)`, and which satisfies the deformation-theoretic hypotheses of
Stacks 07Y4, has a smooth finite type neighbourhood through each of its finite type
field-valued objects.

This is `AlgebraicGeometry.Stack.hasSmoothFiniteTypeNeighborhoods_of_artinAxioms` with the
morphism universe of `𝒳` raised from `u` to `u + 1`; the proof is the same appeal to
`Deformation.Artin.exists_smooth_finiteType_neighborhood`, now at `v := u + 1`. -/
public theorem hasSmoothFiniteTypeNeighborhoods_of_artinAxioms_succ [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒳)
    (hlimit : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B S hS 𝒳)
    (hRS : Deformation.Artin.SatisfiesRS B S hS 𝒳.val.p 𝒳.property)
    (htangent : HasFiniteDimensionalTangentSpaces B S hS 𝒳)
    (heffective : ∀ ξ : Deformation.Artin.FormalObject B S hS 𝒳.val.p,
      Deformation.Artin.FormalObject.IsEffective B S hS 𝒳.val.p 𝒳.property ξ)
    (hopen : ∀ U : Over S, LocallyOfFiniteType U.hom →
      ∀ (y : 𝒳.val.obj) (hy : (𝒳.val.p ⋙ Over.post B.inclusion).obj y = U) (u : U.left),
        AlgebraicGeometry.IsFiniteTypePoint u →
        Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 →
            AlgebraicGeometry.IsFiniteTypePoint u' →
            Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u' y hy)
    (hG : ∀ s : S, AlgebraicGeometry.IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    HasSmoothFiniteTypeNeighborhoods B S hS 𝒳 := by
  intro k _ i₀ x₀ hx₀ hfinite₀ hqc₀ s hs
  obtain ⟨x, u₀, e, r, f, hfin, hqc, hftp, hcart, hb, heval, hsmooth⟩ :=
    Deformation.Artin.exists_smooth_finiteType_neighborhood.{u, u + 1, u} B S hS 𝒳 k i₀ x₀ hx₀
      hfinite₀ hqc₀ s hs hdiag hlimit hRS
      (htangent k i₀ x₀ hx₀ hfinite₀ hqc₀ s hs) heffective hopen
      (hG s (hs ▸ isFiniteTypePoint_of_locallyOfFiniteType i₀ hfinite₀))
  exact ⟨𝒳.val.p.obj x, x, rfl, u₀, e, r, f, hfin, hqc, hftp, hcart, hb, heval, hsmooth⟩

/-- **Stacks 07Y4 (Artin's criterion), for a morphism universe one step up.** A category fibred
in groupoids over a locally Noetherian scheme `S`, whose morphisms lie in `Type (u + 1)`, is an
algebraic stack as soon as its diagonal is representable by algebraic spaces, it satisfies axiom
[-1] (the set-theoretic bound of Stacks 07Y3), axiom [0] (the stack condition), axiom [1] (limit
preservation), axiom [2] (the Rim–Schlessinger condition) and the tangent-space half of axiom
[3], all of its formal objects are effective, versality is open, and the local rings of `S` at
its finite type points are G-rings.

This is `AlgebraicGeometry.Stack.isAlgebraicStack_of_artinAxioms_of_isStack` at the morphism
universe `u + 1`, which is the shape of the stack of coherent sheaves of Stacks 09DS.

This is Stacks 07Y4; its `@[stacks]` registration lives elsewhere. -/
public theorem isAlgebraicStack_of_artinAxioms_succ [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒳)
    (hsize : IsSizeBounded B S hS 𝒳)
    (hfppf : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS))
    (hlimit : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B S hS 𝒳)
    (hRS : Deformation.Artin.SatisfiesRS B S hS 𝒳.val.p 𝒳.property)
    (htangent : HasFiniteDimensionalTangentSpaces B S hS 𝒳)
    (heffective : ∀ ξ : Deformation.Artin.FormalObject B S hS 𝒳.val.p,
      Deformation.Artin.FormalObject.IsEffective B S hS 𝒳.val.p 𝒳.property ξ)
    (hopen : ∀ U : Over S, LocallyOfFiniteType U.hom →
      ∀ (y : 𝒳.val.obj) (hy : (𝒳.val.p ⋙ Over.post B.inclusion).obj y = U) (u : U.left),
        AlgebraicGeometry.IsFiniteTypePoint u →
        Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 →
            AlgebraicGeometry.IsFiniteTypePoint u' →
            Deformation.Artin.IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u' y hy)
    (hG : ∀ s : S, AlgebraicGeometry.IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    IsAlgebraicStack.{u, u + 1, u + 1, u + 1} B S hS 𝒳.val :=
  isAlgebraicStack_of_artinAxioms_of_isStack.{u, u + 1, u} B S hS 𝒳 hdiag hsize hfppf hlimit hRS
    htangent heffective hopen hG

end AlgebraicGeometry.Stack

end
