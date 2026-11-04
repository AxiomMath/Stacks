module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.StalkFreeOfRankIso
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPointsStalk
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteTypePullbackScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FreeAtGenericPointsTransition

/-!
# Descent of a free stalk at the generic point of a fibre along an fpqc covering of the base

This is the first step of the source's proof of the first assertion of Stacks 05MS. Let `T' ⟶ T`
be a flat morphism of schemes over the base of Situation 05MP and suppose the generic-point
condition holds over `T'`. Then for every point of `T'` the stalk of the base-changed module over
`T` at the generic point of the fibre over the image point is free of rank `p`: the condition
over `T'` gives freeness of rank `p` on a neighbourhood of the generic point of the fibre
upstairs, hence a free stalk of rank `p` there, the generic point upstairs lies over the generic
point downstairs, and freeness of a fixed rank of a stalk descends along the flat transition
morphism of the two base changes.

Because the members of an fpqc covering are flat and jointly surjective, this gives a free stalk
of rank `p` at the generic point of *every* fibre over `T`. That is as far as the stalk takes the
argument: the module of Situation 05MP is of finite type only, so a free stalk does not spread to
a neighbourhood, and the source completes the proof by a global argument resting on Stacks 05IA.

## Main results

* `AlgebraicGeometry.FreeAtGenericPointsSituation.stalkFreeOfRank_of_condition_of_flat`: the
  descent along a single flat morphism of schemes over the base.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.stalkFreeOfRank_of_fpqcCover`: the stalk at the
  generic point of every fibre over the base of an fpqc covering is free of rank `p`.

## Implementation notes

An fpqc covering is taken as a `CategoryTheory.Precoverage.ZeroHypercover` of
`AlgebraicGeometry.Scheme.fpqcPrecoverage`, as for the flatness functor of Stacks 05MY, and
flatness of its members together with their joint surjectivity is read off with
`AlgebraicGeometry.Scheme.presieve₀_mem_precoverage_iff` after
`AlgebraicGeometry.Scheme.propQCPrecoverage_le_precoverage` has discarded the quasi-compactness
half of the precoverage, which the argument does not use. Only joint surjectivity *on the base*
is needed, the descent statement being indexed by a point of `T'` rather than by a point of
`X ×_S T'`.

The module on `X ×_S T'` is only isomorphic to the pullback of the module on `X ×_S T` along the
transition morphism, so the descent of
`AlgebraicGeometry.StalkFreeOfRank.of_modulePullback` — which is stated for a pullback — is fed
through `AlgebraicGeometry.StalkFreeOfRank.of_moduleIso`.

## References

* [Stacks Project, Tag 05MS](https://stacks.math.columbia.edu/tag/05MS)
* [Stacks Project, Tag 05MP](https://stacks.math.columbia.edu/tag/05MP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u w

namespace AlgebraicGeometry.FreeAtGenericPointsSituation

variable (D : FreeAtGenericPointsSituation.{u}) (p : ℕ)

/-- **Descent of a free stalk at the generic point of a fibre along a flat morphism of the
base.** If the generic-point condition holds over `T'` and `T' ⟶ T` is flat, then the stalk of
the module base changed to `X ×_S T` at the generic point of the fibre over the image of a point
of `T'` is free of rank `p`. -/
theorem stalkFreeOfRank_of_condition_of_flat {T T' : Over D.S} (g : T' ⟶ T) [Flat g.left]
    (h : D.Condition p T') (t' : T'.left)
    {ξ : (D.baseChangeMap T).fiber (g.left t')}
    (hξ : IsGenericPoint ξ (Set.univ : Set _)) :
    StalkFreeOfRank (D.baseChangeModule T) ((D.baseChangeMap T).fiberι (g.left t') ξ) p := by
  obtain ⟨ξ', hξ'⟩ := D.exists_isGenericPoint_fiber_baseChangeMap T' t'
  have h2 : StalkFreeOfRank (D.baseChangeModule T') ((D.baseChangeMap T').fiberι t' ξ') p :=
    StalkFreeOfRank.of_freeAtPointOfRank _ _ p (h t' ξ' hξ')
  have h3 : StalkFreeOfRank ((Scheme.Modules.pullback (D.transitionHom g)).obj
      (D.baseChangeModule T)) ((D.baseChangeMap T').fiberι t' ξ') p :=
    StalkFreeOfRank.of_moduleIso (D.transitionModuleIso g).symm _ p h2
  have := D.flat_transitionHom g
  have h4 := StalkFreeOfRank.of_modulePullback (D.transitionHom g) (D.baseChangeModule T)
    ((D.baseChangeMap T').fiberι t' ξ') p h3
  rwa [D.transitionHom_fiberι_of_isGenericPoint g t' hξ' hξ] at h4

/-- **The stalk at the generic point of every fibre is free of rank `p` as soon as the
generic-point condition holds over every member of an fpqc covering of the base.** The members
are flat and jointly surjective, so every point of the base is the image of a point of some
member, where `stalkFreeOfRank_of_condition_of_flat` applies. -/
theorem stalkFreeOfRank_of_fpqcCover (T : Over D.S)
    (𝒰 : Precoverage.ZeroHypercover.{w} Scheme.fpqcPrecoverage T.left)
    (h : ∀ i, D.Condition p (Over.mk (𝒰.f i ≫ T.hom)))
    (t : T.left) (ξ : (D.baseChangeMap T).fiber t) (hξ : IsGenericPoint ξ (Set.univ : Set _)) :
    StalkFreeOfRank (D.baseChangeModule T) ((D.baseChangeMap T).fiberι t ξ) p := by
  have hmem : 𝒰.toPreZeroHypercover.presieve₀ ∈ Scheme.precoverage (@Flat) T.left :=
    Scheme.propQCPrecoverage_le_precoverage (P := @Flat) T.left 𝒰.mem₀
  have hdata := (Scheme.presieve₀_mem_precoverage_iff
    (P := @Flat) 𝒰.toPreZeroHypercover).mp hmem
  obtain ⟨i, t', ht'⟩ := hdata.1 t
  have hflat : Flat (𝒰.f i) := hdata.2 i
  let localHom : Over.mk (𝒰.f i ≫ T.hom) ⟶ T := Over.homMk (𝒰.f i) (by simp)
  have : Flat localHom.left := hflat
  subst ht'
  exact D.stalkFreeOfRank_of_condition_of_flat p localHom (h i) t' hξ

end AlgebraicGeometry.FreeAtGenericPointsSituation

end
