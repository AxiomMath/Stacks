module

public import StacksFrontier.AlgebraicTopology.SimplicialSet.BoundaryColimits
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.PresheafObjects
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.JoinCovering

/-!
# Filling the boundary of a simplex of a hypercovering of the final presheaf

Let `(C, J)` be a site with equalizers and fibre products and let `K` be a hypercovering of the
final presheaf, in the sense of Stacks 09VU. This file proves that a compatible family of
`(n + 1)`-simplices of `K` over an object `A` of `C`, one for each face of `⦋n + 2⦌`, is locally
on `A` the boundary of a single `(n + 2)`-simplex of `K`.

This is the clause of the definition of a hypercovering which says that `K` maps onto the
coskeleton, read through the inclusion `∂Δ[n + 2] ⊆ Δ[n + 2]`: it is Tag 01GN for that
inclusion, which `Stacks.CategoryTheory.Hypercovering.isCoveringOver_subcomplexRestriction`
supplies for a hypercovering of an *object*, transported to a hypercovering of the final
presheaf along the Yoneda embedding into the slice over the final presheaf exactly as in
`Stacks.CategoryTheory.Hypercovering.joinLiftSieve_mem`.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.boundaryLiftSieve`: the sieve of arrows along which a
  family of simplices indexed by the faces of `⦋n + 1⦌` lifts to a single `(n + 1)`-simplex.

## Main results

* `Stacks.CategoryTheory.Hypercovering.boundaryLiftSieve_mem`: that sieve is covering, as soon
  as the family is compatible on the codimension-two faces.

## Implementation notes

The compatibility hypothesis is the one of `SSet.boundary.IsCompatible`, written out for the
simplicial set `K ⋙ Mor(A, -)` of simplices of `K` over `A`; it is what turns the family into a
morphism `∂Δ[n + 2] ⟶ K ⋙ Mor(A, -)`, and that morphism is the configuration to be lifted.

The statement is for `∂Δ[n + 2]` rather than for `∂Δ[n + 1]`: the boundary of a `1`-simplex is a
pair of points with no compatibility between them, and the lifting of such a pair is the
degree-one clause `joinLiftSieve_mem` at `m = n = 0`.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]

/-- The sieve on `A` of the arrows along which a family of `n`-simplices of `K` over `A`, one
for each face of `⦋n + 1⦌`, lifts to a single `(n + 1)`-simplex of `K` having them as its
faces. -/
def boundaryLiftSieve (K : SimplicialObject (FormalCoproduct.{w} C)) (n : ℕ) {A : C}
    (s : Fin (n + 2) → ((FormalCoproduct.incl C).obj A ⟶ K.obj (op ⦋n⦌))) : Sieve A where
  arrows _ g := ∃ t : (FormalCoproduct.incl C).obj _ ⟶ K.obj (op ⦋n + 1⦌),
    ∀ i, t ≫ K.map (SimplexCategory.δ i).op = (FormalCoproduct.incl C).map g ≫ s i
  downward_closed := by
    rintro A' A'' g ⟨t, ht⟩ h
    refine ⟨(FormalCoproduct.incl C).map h ≫ t, fun i ↦ ?_⟩
    rw [Category.assoc, ht i, ← Category.assoc, ← Functor.map_comp]

/-- **A compatible family of faces of a hypercovering of the final presheaf is locally the
boundary of a simplex.** For a hypercovering `K` of the final presheaf and a family of
`(n + 1)`-simplices of `K` over `A` indexed by the faces of `⦋n + 2⦌` which agree on the
codimension-two faces, the arrows `A' ⟶ A` along which the family lifts to a single
`(n + 2)`-simplex of `K` form a covering sieve of `A`.

This is Tag 01GN for the inclusion `∂Δ[n + 2] ⊆ Δ[n + 2]`, applied to the hypercovering of the
terminal presheaf which `isHypercovering_yonedaFormal` produces, and brought back to `C` by full
faithfulness of `yonedaFormal`. -/
theorem boundaryLiftSieve_mem (J : Pretopology C) (H : HypercoveringOfTerminal.{max w u v} J)
    (n : ℕ) {A : C}
    (s : Fin (n + 3) → ((FormalCoproduct.incl C).obj A ⟶
      H.toSimplicialObject.obj (op ⦋n + 1⦌)))
    (hs : ∀ (j k : Fin (n + 3)) (hjk : j < k),
      s j ≫ H.toSimplicialObject.map
          (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk))).op =
        s k ≫ H.toSimplicialObject.map
          (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk))).op) :
    boundaryLiftSieve H.toSimplicialObject (n + 1) s ∈ J.toGrothendieck A := by
  have hFF : (yonedaFormal : FormalCoproduct.{max w u v} C ⥤ _).FullyFaithful :=
    yonedaFormalFullyFaithful
  have hLhyp : IsHypercovering (localPretopology.{v, u, max w u v} J)
      (H.toSimplicialObject ⋙ yonedaFormal) := isHypercovering_yonedaFormal J H
  set L := H.toSimplicialObject ⋙ yonedaFormal with hL
  have hs' : SSet.boundary.IsCompatible
      (X := L ⋙ coyoneda.obj (op (testObjects.obj A)))
      (fun i ↦ SSet.yonedaEquiv.symm (yonedaFormal.map (s i))) := by
    intro j k hjk
    dsimp only
    rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm
      ((yonedaFormal.map_comp _ _).symm.trans
        ((congrArg yonedaFormal.map (hs j k hjk)).trans (yonedaFormal.map_comp _ _)))
  have _ : SSet.Nonempty ((SSet.boundary (n + 2) : SSet) : SSet) :=
    SSet.nonempty_of_hom (SSet.boundary.ι 0)
  set hA := representableByAppZero ((SSet.boundary (n + 2) : SSet)) L _ (homFromSSetIsHom _ L)
  have hcov := isCoveringOver_subcomplexRestriction (localPretopology.{v, u, max w u v} J) L
    hLhyp (n + 2) (SSet.boundary (n + 2)) hA
  have hhls := homLocallySurjective_of_covering' J _ hcov
  refine J.toGrothendieck.superset_covering ?_ (hhls A (hA.homEquiv.symm hs'.desc))
  rintro A' g ⟨t, ht⟩
  refine ⟨hFF.preimage t, fun i ↦ ?_⟩
  have hkey : (SSet.boundary (n + 2)).ι ≫ (representableByStdSimplex L (n + 2)).homEquiv t =
      hs'.desc ≫ Functor.whiskerLeft L (coyoneda.map (testObjects.map g).op) := by
    have h₁ := congrArg hA.homEquiv ht
    rw [hA.homEquiv_comp, hA.homEquiv_comp, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply] at h₁
    refine Eq.trans ?_ h₁
    show _ = ((SSet.boundary (n + 2)).ι ≫ (representableByStdSimplex L (n + 2)).homEquiv
      (𝟙 (L.obj (op ⦋n + 2⦌)))) ≫ Functor.whiskerLeft L (coyoneda.map t.op)
    rw [Category.assoc]
    congr 1
  have hface := SSet.boundary.ι i ≫= hkey
  rw [← Category.assoc, SSet.boundary.ι_ι, ← Category.assoc,
    SSet.boundary.IsCompatible.ι_desc] at hface
  rw [homEquiv_representableByStdSimplex, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
    SSet.yonedaEquiv_symm_comp] at hface
  have hface' := SSet.yonedaEquiv.symm.injective hface
  refine hFF.map_injective ?_
  rw [Functor.map_comp, Functor.map_comp, hFF.map_preimage]
  exact hface'

end Stacks.CategoryTheory.Hypercovering

end
