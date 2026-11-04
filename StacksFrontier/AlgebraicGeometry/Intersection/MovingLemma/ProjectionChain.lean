module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.LinearAction
public import StacksFrontier.AlgebraicGeometry.Limits.ProjGradedSurjection01N0
public import StacksFrontier.AlgebraicGeometry.Morphism.Composition
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLines
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinearSubspaceQuotientMap

/-!
# Factoring a linear projection through a larger submodule

For submodules `W ≤ W'` of `V` the projection away from the linear subspace cut out by `W`
factors through the projection away from the smaller linear subspace cut out by `W'`:

`𝐏(V) ⇢ 𝐏(W') ⇢ 𝐏(W)`

the second map being the projection of `𝐏(W')` away from the copy of `W` sitting inside `W'`.
Iterating this with a flag of submodules of coranks `1, 2, …, c` presents the projection away
from a corank-`c` submodule as the composite `r_{n+1} ∘ ⋯ ∘ r_N` of `c` projections away from
points, which is the chain the proof of Stacks 0B0E runs its induction along.

This module proves the factorization on the graded algebras — the level at which it is an
identity rather than an identity up to a canonical isomorphism — the comparison of the two
domains of definition, the factorization of the morphisms of schemes which Tag 01MZ reads off
the graded one, and the isomorphism of projective spaces induced by a linear equivalence, which
is what identifies the target of the second projection with `𝐏(W)`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.chainSymAlgMap`: the second map of the chain, on
  symmetric algebras.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mapOfLinearEquiv`: the isomorphism `𝐏(N) ≅ 𝐏(M)`
  induced by a linear equivalence `M ≃ₗ[k] N`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.subtype_eq_comp_comapSubtypeEquivOfLe`: the
  inclusion `W ≤ V` factors through `W'`, through the canonical identification of `W` with its
  copy inside `W'`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.gradedSymAlgMap_subtype_eq_comp`: the same on
  symmetric algebras, which is the factorization of the graded homomorphism inducing the
  projection.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.projectionDomain_le`: the projection away from `W`
  is defined wherever the projection away from `W'` is.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_projection_eq_comp`: the factorization of
  the morphisms of schemes.

## Implementation notes

**The copy of `W` inside `W'`.** The target of the second projection is `𝐏` of a submodule of
`W'`, not of `W`: what sits inside `W'` is `Submodule.comap W'.subtype W`, which the linear
equivalence `Submodule.comapSubtypeEquivOfLe` identifies with `W`. That equivalence is the
reason the factorization is stated as an equality of graded homomorphisms with three factors
rather than two — the third is the one induced by the identification, and it is an isomorphism.
Composing the two outer factors is the chain step; the inner one is bookkeeping, and the
isomorphism of projective spaces it induces is
`AlgebraicGeometry.ProjectiveSpaceOfModule.mapOfLinearEquiv`, built here because the library had
`𝐏` functorial in a linear map only through
`AlgebraicGeometry.ProjectiveSpaceOfModule.map`, which is for an element of the general linear
group of a single module, and through
`AlgebraicGeometry.ProjectiveSpaceOfModule.projectiveSpaceOfModuleIso`, which compares `𝐏(V)`
with `ℙⁿ` for a basis of `V`. A linear equivalence is surjective, so the graded homomorphism it
induces is surjective and `AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective` makes the
induced morphism defined everywhere; the two morphisms are mutually inverse because the two
graded homomorphisms are.

**From the graded factorization to the morphisms.** This is Tag 01MZ, in the transported form
`Stacks.AlgebraicGeometry.RelativeProjMapComp.mapHom_comp_of_eq`: for a graded homomorphism
*equal to* a composite, that lemma already produces the corestriction `q` of the outer morphism
together with both of its characterizing equations, so no canonical isomorphism of domains of
definition has to be introduced here and `mapHom_comp` is not applied directly. Since the
equality of graded homomorphisms is `gradedSymAlgMap_subtype_eq_comp` and the containment of
domains of definition is `projectionDomain_le`,
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_projection_eq_comp` is immediate.

**What the chain still needs.** The induction on `N - n` forming the images `X_j, Z_j, T_{i, j}`
of the source's chain is not here: it is what remains before conditions (2) and (3) of the proof
of Stacks 0B0E — étaleness of `π` at the chosen points and the local isomorphism of `π|_Z` — are
available for the composite rather than for a single point projection. The step which carries
them along the factorization above is `AlgebraicGeometry.etaleAt_comp`. Condition (1),
finiteness, needs no chain and is
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isFinite_projection_of_disjoint`.

The factorization in the form the induction consumes — with the second factor a projection of
`𝐏(W)` away from a submodule of `W`, so that the generic-projection lemmas apply to it — is
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_comp_eq_projection_map_subtype` of
`StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.ChainProjection`, whose chain step is
indexed by a submodule `P` of `W` rather than by a submodule of `V` below `W`: the equality
`Submodule.comap W.subtype W' = P` which the other indexing needs stands between two different
types, and taking `P.map W.subtype` for `W'` avoids it.

## References

* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
* [Stacks Project, Tag 0B1N](https://stacks.math.columbia.edu/tag/0B1N)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ProjShared

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- **The inclusion of a submodule factors through any larger one.** For `W ≤ W'` the inclusion
of `W` in `V` is the inclusion of `W'` composed with the inclusion in `W'` of the copy
`Submodule.comap W'.subtype W` of `W`, preceded by the canonical identification of `W` with that
copy. -/
public theorem subtype_eq_comp_comapSubtypeEquivOfLe {W W' : Submodule k V} (h : W ≤ W') :
    W.subtype = W'.subtype ∘ₗ ((Submodule.comap W'.subtype W).subtype ∘ₗ
      (Submodule.comapSubtypeEquivOfLe h).symm.toLinearMap) := by
  ext x
  rfl

/-- **The second map of the chain `𝐏(V) ⇢ 𝐏(W') ⇢ 𝐏(W)`, on symmetric algebras.** For `W ≤ W'`
this is the homomorphism inducing the projection of `𝐏(W')` away from the copy of `W` inside
`W'`, preceded by the isomorphism induced by the identification of `W` with that copy. -/
public def chainSymAlgMap {W W' : Submodule k V} (h : W ≤ W') :
    (fun n => SymPow.symmetricPower n k ↥W) →+*ᵍ (fun n => SymPow.symmetricPower n k ↥W') :=
  (SymPow.gradedSymAlgMap (Submodule.comap W'.subtype W).subtype).comp
    (SymPow.gradedSymAlgMap (Submodule.comapSubtypeEquivOfLe h).symm.toLinearMap)

/-- **The graded homomorphism of a projection factors through that of a larger submodule.** For
`W ≤ W'` the homomorphism of symmetric algebras inducing the projection away from `W` is the
composite of the one inducing the projection away from `W'`, the one inducing the projection of
`𝐏(W')` away from the copy of `W` inside `W'`, and the isomorphism induced by the identification
of `W` with that copy.

This is the chain `𝐏(V) ⇢ 𝐏(W') ⇢ 𝐏(W)` at the level at which it is an equality on the nose. -/
public theorem gradedSymAlgMap_subtype_eq_comp {W W' : Submodule k V} (h : W ≤ W') :
    SymPow.gradedSymAlgMap W.subtype =
      (SymPow.gradedSymAlgMap W'.subtype).comp (chainSymAlgMap k V h) := by
  rw [chainSymAlgMap, ← SymPow.gradedSymAlgMap_comp, ← SymPow.gradedSymAlgMap_comp,
    subtype_eq_comp_comapSubtypeEquivOfLe k V h]

/-- **More equations, a larger domain of definition.** For `W ≤ W'` the projection away from `W`
is defined wherever the projection away from `W'` is: its vertex, the linear subspace cut out by
`W`, contains the vertex of the latter. -/
public theorem projectionDomain_le {W W' : Submodule k V} (h : W ≤ W') :
    projectionDomain k V W ≤ projectionDomain k V W' := by
  have hsub : (projectionDomain k V W : Set (projectiveSpaceOfModule k V)) ⊆
      (projectionDomain k V W' : Set (projectiveSpaceOfModule k V)) := by
    rw [coe_mapDomain_subtype, coe_mapDomain_subtype]
    exact Set.compl_subset_compl.mpr (linearSubspace_antitone k V h)
  exact hsub

/-- **The chain `𝐏(V) ⇢ 𝐏(W') ⇢ 𝐏(W)` as a factorization of morphisms of schemes.** For
`W ≤ W'` the projection away from `W` is the projection away from `W'`, restricted to the smaller
domain of definition and corestricted along its own domain of definition, followed by the second
map of the chain.

The corestriction `q` is characterised by its defining equation, the first conjunct: the
inclusion of an open subscheme is a monomorphism, so there is exactly one morphism to the domain
of definition of `chainSymAlgMap` over the restricted projection away from `W'`.

Iterating this with a flag of submodules of coranks `1, 2, …, c` presents the projection away
from a corank-`c` submodule as the composite `r_{n+1} ∘ ⋯ ∘ r_N` of `c` projections away from
points, which is the chain the proof of Stacks 0B0E runs its induction along; what makes the
induction go is that `AlgebraicGeometry.etaleAt_comp` applies to this factorization. -/
public theorem exists_projection_eq_comp {W W' : Submodule k V} (h : W ≤ W') :
    ∃ q : (projectionDomain k V W).toScheme ⟶
        (mapDomain (fun n => SymPow.symmetricPower n k ↥W)
          (fun n => SymPow.symmetricPower n k ↥W') (chainSymAlgMap k V h)).toScheme,
      q ≫ (mapDomain (fun n => SymPow.symmetricPower n k ↥W)
            (fun n => SymPow.symmetricPower n k ↥W') (chainSymAlgMap k V h)).ι =
          (projectiveSpaceOfModule k V).homOfLE (projectionDomain_le k V h) ≫
            projection k V W' ∧
        projection k V W =
          q ≫ Stacks.AlgebraicGeometry.ProjTwistChain.mapHom _ _ (chainSymAlgMap k V h) :=
  Stacks.AlgebraicGeometry.RelativeProjMapComp.mapHom_comp_of_eq _ _ _ (chainSymAlgMap k V h)
    (SymPow.gradedSymAlgMap W'.subtype) (gradedSymAlgMap_subtype_eq_comp k V h)
    (projectionDomain_le k V h)

section LinearEquiv

variable {k M N : Type u} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- Equal graded homomorphisms induce the same morphism of projective spectra: the hypothesis on
the irrelevant ideals is a proposition. -/
public theorem Proj_map_eq_of_eq {A B : Type u} {σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] {f g : 𝒜 →+*ᵍ ℬ} (h : f = g)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    Proj.map f hf = Proj.map g hg := by
  subst h
  rfl

/-- The graded homomorphism induced by a linear equivalence carries the irrelevant ideal onto the
irrelevant ideal, so it induces a morphism of projective spaces defined everywhere. -/
public theorem irrelevant_le_map_gradedSymAlgMap_of_surjective {f : M →ₗ[k] N}
    (hf : Function.Surjective f) :
    HomogeneousIdeal.irrelevant (fun n => SymPow.symmetricPower n k N) ≤
      (HomogeneousIdeal.irrelevant (fun n => SymPow.symmetricPower n k M)).map
        (SymPow.gradedSymAlgMap f) :=
  Proj.irrelevant_le_map_of_surjective _ (SymPow.surjective_gradedSymAlgMap f hf)

/-- **A linear equivalence induces an isomorphism of projective spaces.** The two graded
homomorphisms of symmetric algebras induced by the equivalence and its inverse are mutually
inverse, so the two morphisms of projective spaces they induce are too.

This is what makes the chain of Stacks 0B0E formable: the target of the second projection in
`𝐏(V) ⇢ 𝐏(W') ⇢ 𝐏(W)` is `𝐏` of the copy of `W` inside `W'`, and this identifies it with
`𝐏(W)`. -/
public def mapOfLinearEquiv (e : M ≃ₗ[k] N) :
    projectiveSpaceOfModule k N ≅ projectiveSpaceOfModule k M where
  hom := Proj.map (SymPow.gradedSymAlgMap e.toLinearMap)
    (irrelevant_le_map_gradedSymAlgMap_of_surjective e.surjective)
  inv := Proj.map (SymPow.gradedSymAlgMap e.symm.toLinearMap)
    (irrelevant_le_map_gradedSymAlgMap_of_surjective e.symm.surjective)
  hom_inv_id := by
    have h : (SymPow.gradedSymAlgMap (e : M →ₗ[k] N)).comp
          (SymPow.gradedSymAlgMap (e.symm : N →ₗ[k] M)) =
        GradedRingHom.id (fun n => SymPow.symmetricPower n k N) := by
      rw [← SymPow.gradedSymAlgMap_comp]
      refine Eq.trans (congrArg SymPow.gradedSymAlgMap ?_) SymPow.gradedSymAlgMap_id
      ext x
      simp
    rw [← Proj.map_comp, Proj_map_eq_of_eq h _ (by simp), Proj.map_id]
  inv_hom_id := by
    have h : (SymPow.gradedSymAlgMap (e.symm : N →ₗ[k] M)).comp
          (SymPow.gradedSymAlgMap (e : M →ₗ[k] N)) =
        GradedRingHom.id (fun n => SymPow.symmetricPower n k M) := by
      rw [← SymPow.gradedSymAlgMap_comp]
      refine Eq.trans (congrArg SymPow.gradedSymAlgMap ?_) SymPow.gradedSymAlgMap_id
      ext x
      simp
    rw [← Proj.map_comp, Proj_map_eq_of_eq h _ (by simp), Proj.map_id]

end LinearEquiv

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
