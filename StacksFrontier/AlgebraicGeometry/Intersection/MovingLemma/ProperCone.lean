module

public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.ChainInduction
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.ConeDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.DimensionOfProjectiveSpace

/-!
# The subvariety `C` of Stacks 0B0E and its proper intersection with `X`

Let `X ⊆ 𝐏(V)` be a closed subvariety of dimension `n` of the projective space of a vector space
of dimension `N + 1`, with `n < N`, let `W ≤ V` be a submodule of dimension `n + 1` whose linear
subspace misses `X`, so that `π = r_W|_X : X ⟶ 𝐏(W)` is defined, and suppose `π` is finite. Let
`Z ⊆ X` be an irreducible closed subset of dimension `d`. Then the closure

`C = closure (r_W^{-1}(π(Z))) ⊆ 𝐏(V)`

is an irreducible closed subset which intersects `X` properly, and

`C ∩ X = π^{-1}(π(Z))`

set theoretically. This is the construction of `C` in the proof of Stacks 0B0E together with the
verification that it intersects `X` properly.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_coneCl_intersectProperly_inter_eq`: the
  subvariety `C`, its proper intersection with `X`, the identity `C ∩ X = π^{-1}(π(Z))`, the
  bound `dim (C ∩ X) ≤ d`, and the identification of `C` with the closure of the cone.

## Implementation notes

**Only a lower bound on `dim C` is proved.** Proper intersection is an inequality in one
direction, so `AlgebraicGeometry.intersectProperly_of_add_le` consumes a *lower* bound on
`dim C` — here `dim C ≥ d + (N - n)`, from the chain of cones of
`AlgebraicGeometry.ProjectiveSpaceOfModule.le_topologicalKrullDim_coneCl` — together with the
*upper* bound `dim (C ∩ X) ≤ d`. The exact dimension of `C` is never computed, and the repo has
no upper bound for it; that is why
`AlgebraicGeometry.TorFormula.torSupportBound_of_intersectProperly`, which needs the exact sum
`dim C + dim X = N + d`, is not usable here and
`AlgebraicGeometry.TorFormula.torSupportBound_of_topologicalKrullDim_le`, which needs only
`dim (C ∩ X) ≤ d`, is.

**The dimension of `π(Z)` is squeezed between the two directions of finiteness.** Upwards,
`dim π(Z) ≤ dim Z = d` because `π` is finite; downwards, `Z ⊆ π^{-1}(π(Z))` and
`dim π^{-1}(π(Z)) ≤ dim π(Z)` by
`AlgebraicGeometry.topologicalKrullDim_preimage_le_of_isIntegralHom`, so `d ≤ dim π(Z)`. The
lower bound is what the cone dimension needs and the upper bound is what the proper-intersection
criterion needs, and the same preimage bound supplies `dim (C ∩ X) ≤ d`.

**`n < N` is a hypothesis of this construction.** For `n = N` the submodule `W` is `V` itself,
the projection away from it is the identity and no cone is formed. Stacks 0B0E itself covers
`n = N`, and does so without a cone: there `X` is the whole of `𝐏(V)` and the conclusion holds
with `C = Z` and an empty family of `Z_j`. That is the branch
`exists_intersectProperly_torFormulaCycleIntersectionProduct_eq` of
`StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.KeyLemma` takes before reaching this
construction.

## References

* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- **The subvariety `C` of Stacks 0B0E.** Let `X ⊆ 𝐏(V)` be a closed subvariety of dimension
`n` of the projective space of a vector space of dimension `N + 1`, with `n < N`, let `W ≤ V` be
of dimension `n + 1` with `r_W` defined on `X` and `π = r_W|_X` finite, and let `Z ⊆ X` be
irreducible closed of dimension `d`. Then there is an irreducible closed `C ⊆ 𝐏(V)` which
intersects `X` properly, with `C ∩ X = π^{-1}(π(Z))` set theoretically and
`dim π^{-1}(π(Z)) ≤ d`.

`C` is the closure of the cone `r_W^{-1}(π(Z))` with vertex the linear subspace cut out by `W`,
which is `AlgebraicGeometry.ProjectiveSpaceOfModule.coneCl` of the image `π(Z)`; that
identification is returned, because the scheme-theoretic form of `C ∩ X = π^{-1}(π(Z))` which the
local form of Tag 0B1J consumes is stated about the closure of the cone and not about `C`.

The lower bound `d + N ≤ dim C + n` on the dimension of `C` is returned alongside the proper
intersection even though proper intersection is what it is used for here: the local
proper-intersection inequality that the Tor-formula display of Stacks 0B1J takes at the generic
point of `Z` is `dim 𝒪_ξ ≤ dim 𝒪_{C, ξ} + dim 𝒪_{X, ξ}`, which unwinds to exactly this
inequality and not to proper intersection, the two being the two directions of an equality
here. -/
public theorem exists_coneCl_intersectProperly_inter_eq [IsAlgClosed k] [FiniteDimensional k V]
    [Nontrivial V] {N n d : ℕ} (hV : Module.finrank k V = N + 1)
    {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion iX]
    [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)]
    (hdimX : topologicalKrullDim X = (n : WithBot ℕ∞)) (hnN : n < N)
    (W : Submodule k V) (hW : Module.finrank k ↥W = n + 1)
    (j : X ⟶ (projectionDomain k V W).toScheme) (hj : j ≫ (projectionDomain k V W).ι = iX)
    [IsFinite (j ≫ projection k V W)]
    (Z : Set X) (hZirr : IsIrreducible Z) (hZcl : IsClosed Z)
    (hZd : topologicalKrullDim ↥Z = (d : WithBot ℕ∞))
    (XC : IrreducibleCloseds (projectiveSpaceOfModule k V))
    (hXC : (XC : Set (projectiveSpaceOfModule k V)) = Set.range iX.base) :
    ∃ C : IrreducibleCloseds (projectiveSpaceOfModule k V),
      AlgebraicGeometry.IntersectProperly C XC ∧
      ((d + N : ℕ) : WithBot ℕ∞) ≤
        topologicalKrullDim (C : Set (projectiveSpaceOfModule k V)) + (n : WithBot ℕ∞) ∧
      (C : Set (projectiveSpaceOfModule k V)) ∩ (XC : Set (projectiveSpaceOfModule k V)) =
        iX.base '' ((j ≫ projection k V W).base ⁻¹'
          ((j ≫ projection k V W).base '' Z)) ∧
      topologicalKrullDim ↥((j ≫ projection k V W).base ⁻¹'
        ((j ≫ projection k V W).base '' Z)) ≤ (d : WithBot ℕ∞) ∧
      (C : Set (projectiveSpaceOfModule k V)) =
        closure (projectionPreimage k V W ((j ≫ projection k V W).base '' Z)) := by
  have : Nontrivial ↥W := Module.nontrivial_of_finrank_pos (R := k) (by rw [hW]; omega)
  -- the image `π(Z)` is irreducible and closed in `𝐏(W)`
  have himgcomp : (j ≫ projection k V W).base '' Z =
      (projection k V W).base '' (j.base '' Z) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp]
  have hpre : (projectionDomain k V W).ι.base ⁻¹' (iX.base '' Z) = j.base '' Z := by
    rw [← hj, Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp,
      Set.preimage_image_eq _ (projectionDomain k V W).ι.isOpenEmbedding.injective]
  have hZimcl : IsClosed ((j ≫ projection k V W).base '' Z) := by
    have h := isClosed_image_projection_of_subset_range k V W j
      (iX.isClosedMap _ hZcl) (by rw [hj]; exact Set.image_subset_range _ _)
    rwa [hpre, ← himgcomp] at h
  have hZimirr : IsIrreducible ((j ≫ projection k V W).base '' Z) :=
    hZirr.image _ (Scheme.Hom.continuous _).continuousOn
  -- the dimension of the image, squeezed between the two directions of finiteness
  have hprele : topologicalKrullDim ↥((j ≫ projection k V W).base ⁻¹'
        ((j ≫ projection k V W).base '' Z)) ≤
      topologicalKrullDim ↥((j ≫ projection k V W).base '' Z) :=
    topologicalKrullDim_preimage_le_of_isIntegralHom (j ≫ projection k V W) hZimcl
  have himgle : topologicalKrullDim ↥((j ≫ projection k V W).base '' Z) ≤
      (d : WithBot ℕ∞) := by
    rw [← hZd]
    exact (isClosed_image_and_topologicalKrullDim_image_le k (j ≫ projection k V W)
      (iX ≫ projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k ↥W)
      (by rw [Category.assoc, projection_comp_toSpec, ← Category.assoc, hj]) hZcl).2
  have hdle : (d : WithBot ℕ∞) ≤
      topologicalKrullDim ↥((j ≫ projection k V W).base '' Z) := by
    rw [← hZd]
    exact (topologicalKrullDim_le_of_subset (Set.subset_preimage_image _ _)).trans hprele
  -- the cone over the image, and its dimension
  have hc : Module.finrank k (V ⧸ W) = (N - n - 1) + 1 := by
    have h := Submodule.finrank_quotient_add_finrank (R := k) W
    omega
  have hCset : ((coneCl k V W ⟨(j ≫ projection k V W).base '' Z, hZimirr, hZimcl⟩ :
      IrreducibleCloseds (projectiveSpaceOfModule k V)) :
        Set (projectiveSpaceOfModule k V)) =
      closure (projectionPreimage k V W ((j ≫ projection k V W).base '' Z)) :=
    (closure_projectionPreimage_eq_coneCl k V W hZimirr hZimcl).symm
  have hCge : ((d + (N - n - 1) + 1 : ℕ) : WithBot ℕ∞) ≤
      topologicalKrullDim
        ((coneCl k V W ⟨(j ≫ projection k V W).base '' Z, hZimirr, hZimcl⟩ :
          IrreducibleCloseds (projectiveSpaceOfModule k V)) :
            Set (projectiveSpaceOfModule k V)) :=
    le_topologicalKrullDim_coneCl k V hc _ hdle
  refine ⟨coneCl k V W ⟨(j ≫ projection k V W).base '' Z, hZimirr, hZimcl⟩, ?_, ?_, ?_,
    hprele.trans himgle, hCset⟩
  · refine AlgebraicGeometry.intersectProperly_of_add_le (b := n) (e := d) (m := N) _ _
      hCge ?_ ?_ ?_ ?_
    · rw [hXC, ← hdimX]
      exact le_of_eq (IsHomeomorph.topologicalKrullDim_eq _
        iX.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph)
    · rw [hXC, hCset, ← Set.image_preimage_eq_inter_range,
        preimage_closure_projectionPreimage_eq k V W iX j hj hZimcl]
      exact le_trans (isClosed_image_and_topologicalKrullDim_image_le k iX
        (iX ≫ projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V) rfl
        (hZimcl.preimage (j ≫ projection k V W).continuous)).2 (hprele.trans himgle)
    · exact le_of_eq (topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hV)
    · omega
  · refine le_trans (le_of_eq ?_) (add_le_add hCge le_rfl)
    have h : d + N = d + (N - n - 1) + 1 + n := by omega
    rw [h]
    push_cast
    ring
  · rw [hXC, hCset]
    exact image_preimage_closure_projectionPreimage_eq k V W iX j hj hZimcl

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
