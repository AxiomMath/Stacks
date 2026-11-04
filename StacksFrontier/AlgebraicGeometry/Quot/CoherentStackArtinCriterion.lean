module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackIsStackInGroupoids
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitFlatProperSupport
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushoutModules
public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FromThickeningPushouts
public import StacksFrontier.Deformation.Artin.Versality.OpennessOfVersality

/-!
# Artin's criterion for `Coh_{X/Y}`

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of finite presentation, the
standing data of Stacks 08KB, and let `Coh_{X/Y}` be its stack of coherent sheaves, flat over the
base with proper support, as the category fibred in groupoids
`AlgebraicGeometry.Space.CoherentSituation.coherentCFG` over the big fppf site of `S`. We verify
the conditions of Artin's criterion, Stacks 07Y4, for `Coh_{X/Y}` over a locally Noetherian base,
as in the proof of Stacks 09DS.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.satisfiesRSStar`: `Coh_{X/Y}` satisfies the
  Rim–Schlessinger condition (RS*) of Stacks 07Y8.
* `AlgebraicGeometry.Space.CoherentSituation.isOpenVersality_coherent`: condition (4) of Stacks
  07Y4 for `Coh_{X/Y}`, openness of versality, when square-zero systems of `Coh_{X/Y}` are
  effective.
* `AlgebraicGeometry.Space.CoherentSituation.isStackInGroupoids_etale`: `Coh_{X/Y}` is a stack in
  groupoids for the big étale topology over `S`.
* `AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_coherentCFG_of_artinInputs`:
  `Coh_{X/Y}` is an algebraic stack over a locally Noetherian base `S` with `Y` locally of finite
  presentation over `S`, given the remaining conditions of Stacks 07Y4.

## References

* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
* [Stacks Project, Tag 07Y4](https://stacks.math.columbia.edu/tag/07Y4)
* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
* [Stacks Project, Tag 08LQ](https://stacks.math.columbia.edu/tag/08LQ)
* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe z u

namespace AlgebraicGeometry.Space.CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS)

/-- `Coh_{X/Y}` satisfies the Rim–Schlessinger condition (RS*) of Stacks 07Y8. -/
theorem satisfiesRSStar :
    Deformation.Artin.SatisfiesRSStar B S hS D.coherentCFG.val.p
      D.coherentCFG.isFiberedInGroupoids := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  refine Deformation.Artin.satisfiesRSStar_of_fiberSquareComparison_isEquivalence B S hS
    (coherentSiteProjection D.categoryData) D.isFiberedInGroupoids_siteProjection ?_
  intro X X' Y Y' i f a b w hi hf hsq
  have := hf
  exact D.fiberSquareComparison_isEquivalence i f a b hi hsq

/-- Openness of versality for `Coh_{X/Y}`, condition (4) of Stacks 07Y4: over a locally
Noetherian base, with `Y` locally of finite presentation over `S`, the diagonal of `Coh_{X/Y}`
representable by algebraic spaces and square-zero systems of objects of `Coh_{X/Y}` effective,
an object of `Coh_{X/Y}` over a scheme locally of finite type over `S` which is versal at a
finite type point is versal at every finite type point of a neighbourhood. -/
theorem isOpenVersality_coherent [IsLocallyNoetherian S]
    (hY : IsLocallyOfFinitePresentation B S hS (terminal.from D.Y.1))
    (hdiag : Stack.HasRepresentableDiagonal B S hS D.coherentCFG)
    (heff : Deformation.Artin.IsSquareZeroEffective B S hS D.coherentCFG.val.p
      D.coherentCFG.isFiberedInGroupoids)
    (U : Over S) (hU : LocallyOfFiniteType U.hom) (y : D.coherentCFG.val.obj)
    (hy : (D.coherentCFG.val.p ⋙ Over.post B.inclusion).obj y = U) (u₀ : U.left)
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hversal : Deformation.Artin.IsVersalAt U (D.coherentCFG.val.p ⋙ Over.post B.inclusion)
      u₀ y hy) :
    ∃ V : U.left.Opens, u₀ ∈ V.1 ∧
      ∀ u ∈ V.1, AlgebraicGeometry.IsFiniteTypePoint u →
        Deformation.Artin.IsVersalAt U (D.coherentCFG.val.p ⋙ Over.post B.inclusion) u y hy :=
  Deformation.Artin.isOpenVersality_of_isSquareZeroEffective B S hS D.coherentCFG hdiag
    D.satisfiesRSStar (D.isLimitPreserving_coherent hY) heff U hU y hy u₀ hu₀ hversal

/-- `Coh_{X/Y}` is a stack in groupoids for the big étale topology over `S`, axiom [0] of Artin's
Axioms, Section 07XJ. -/
theorem isStackInGroupoids_etale :
    D.coherentCFG.val.p.IsStackInGroupoids.{z}
      ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)) :=
  (D.isStackInGroupoids.{z}).of_le (fun _ _ h => Stack.etaleTopology_le_topology B _ h)

/-- Let `S` be locally Noetherian and `Y` locally of finite presentation over `S`. If the
diagonal of `Coh_{X/Y}` is representable by algebraic spaces (Stacks 08W6), axiom [-1] holds, the
tangent spaces are finite dimensional (Stacks 08W8), formal objects are effective (Stacks 08W9),
square-zero systems are effective (Flatness on Spaces, Theorem 0CXB) and the local rings of `S`
at finite type points are G-rings, then `Coh_{X/Y}` is an algebraic stack. -/
theorem isAlgebraicStack_coherentCFG_of_artinInputs [IsLocallyNoetherian S]
    (hY : IsLocallyOfFinitePresentation B S hS (terminal.from D.Y.1))
    (hdiag : Stack.HasRepresentableDiagonal B S hS D.coherentCFG)
    (hsize : Stack.IsSizeBounded B S hS D.coherentCFG)
    (htangent : Stack.HasFiniteDimensionalTangentSpaces B S hS D.coherentCFG)
    (heffective : ∀ ξ : Deformation.Artin.FormalObject B S hS D.coherentCFG.val.p,
      Deformation.Artin.FormalObject.IsEffective B S hS D.coherentCFG.val.p
        D.coherentCFG.property ξ)
    (hsq : Deformation.Artin.IsSquareZeroEffective B S hS D.coherentCFG.val.p
      D.coherentCFG.isFiberedInGroupoids)
    (hG : ∀ s : S, AlgebraicGeometry.IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS D.coherentCFG.val :=
  Stack.isAlgebraicStack_of_artinAxioms.{u, u + 1, u + 1, z} B S hS D.coherentCFG hdiag hsize
    D.isStackInGroupoids_etale (D.isLimitPreserving_coherent hY) D.satisfiesRS htangent
    heffective (fun U hU y hy u hu hv => D.isOpenVersality_coherent hY hdiag hsq U hU y hy u hu hv)
    hG

end AlgebraicGeometry.Space.CoherentSituation

end
