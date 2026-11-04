module

public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# Elementary distinguished squares of algebraic spaces

Let `W` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `U` be an
open subspace of `W` and let `f : V ⟶ W` be an étale morphism of algebraic spaces.  The square

```
U ×_W V ---> V
   |         | f
   v         v
   U   -j->  W
```

is an *elementary distinguished square* when, writing `T` for the complement `W \ U` carrying
the reduced induced subspace structure, the projection `f⁻¹(T) ⟶ T` is an isomorphism.  Such
squares are the induction step of the induction principle for quasi-compact algebraic spaces:
every property that holds on affines, is étale-local, and passes from the two upper corners of
an elementary distinguished square to `W`, holds on every quasi-compact algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.openComplementReducedSubspace` is the subspace `T = W \ U`: the
  reduced closed subspace of `W` on the complement of the point set of `U`.
* `AlgebraicGeometry.Space.IsElementaryDistinguishedSquare'` is the predicate of Stacks 08GM on
  the pair `(U ⊂ W, f : V ⟶ W)`, with condition (3) stated as the invertibility of the first
  projection of the fibre product `f⁻¹(T) ⟶ T`. The unprimed
  `AlgebraicGeometry.Space.IsElementaryDistinguishedSquare` is the same predicate with
  algebraicity of `V` and closedness of the complement carried as fields and condition (3)
  stated on `AlgebraicGeometry.Space.reducedClosedSubspace`.

## Main results

* `AlgebraicGeometry.Space.range_pointsMap_ι_openComplementReducedSubspace`: the point set of
  `T` is the complement of the point set of `U`, so `T` really is `W \ U`.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isReduced_openComplementReducedSubspace`: `T`
  is reduced, in the étale-local sense of Stacks 03E6.

## Implementation notes

The square of the source carries no information beyond the pair `(U, f)`: its upper left corner
is the fibre product `U ×_W V` and its two remaining arrows are the projections.  The predicate
is therefore stated on that pair, which is also the form in which the source abbreviates it
("let `(U ⊂ W, f : V → W)` be an elementary distinguished square").  Condition (1) of the source
is the field `isOpenSubspace`, which is `AlgebraicGeometry.Space.IsOpenSubspace` of Stacks
02YU(2) and so contains both that `U` is an algebraic space and that its inclusion `U.ι` — the
`j` of the source — is an open immersion.

The reduced induced subspace structure on `W \ U` is
`AlgebraicGeometry.Space.reducedClosedSubspace` of Stacks 03IQ, which consumes a *closed* set of
points; the set here is closed because the point set of an open subspace is open, by
`AlgebraicGeometry.Space.isOpen_range_pointsMap_of_isOpenImmersion`.  That proof is what forces
condition (3) to be stated as a field depending on condition (1), and `T` to be a separate
definition rather than an inline term: `openComplementReducedSubspace` takes the open-subspace
hypothesis, so that `isIso_pullback_fst` can name the `T` determined by `isOpenSubspace`.

The inverse image `f⁻¹(T)` is the fibre product `T ×_W V`, formed as a pullback in the presheaf
category exactly as every other fibre product of algebraic spaces in this layer, and the
morphism `f⁻¹(T) ⟶ T` of the source is its first projection.  No reducedness is asked of
`f⁻¹(T)`: `f` is étale, so the inverse image of a reduced subspace is reduced, and the source's
`f⁻¹(T)` is the plain base change.

Algebraicity of `W` is a parameter because `reducedClosedSubspace` needs it; algebraicity of `V`
is a parameter because the source's diagram is one of algebraic spaces, even though no
declaration here consumes it.  Both are passed explicitly, as in
`AlgebraicGeometry.Space.TorIndependent`.

## References

* [Stacks Project, Tag 08GM](https://stacks.math.columbia.edu/tag/08GM)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The subspace `T = W \ U` of an algebraic space `W` cut out by an open subspace `U`: the
reduced closed subspace of `W` on the complement of the point set of `U`.  The complement is
closed because the point set of an open subspace is open. -/
noncomputable def openComplementReducedSubspace
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (U : Subfunctor W) (hU : IsOpenSubspace B S hS U) : Subfunctor W :=
  reducedClosedSubspace B S hS W hW (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS U.ι hU.2).isClosed_compl

/-- The point set of `W \ U` is the complement of the point set of `U`. -/
theorem range_pointsMap_ι_openComplementReducedSubspace
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (U : Subfunctor W) (hU : IsOpenSubspace B S hS U) :
    Set.range (pointsMap B S hS (openComplementReducedSubspace B S hS hW U hU).toFunctor
        (openComplementReducedSubspace B S hS hW U hU).ι) =
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ :=
  range_pointsMap_ι_reducedClosedSubspace B S hS W hW _ _

/-- The subspace `W \ U` is reduced, in the étale-local sense of Stacks 03E6. -/
theorem hasEtaleLocalProperty_isReduced_openComplementReducedSubspace
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (U : Subfunctor W) (hU : IsOpenSubspace B S hS U) :
    HasEtaleLocalProperty B S hS (openComplementReducedSubspace B S hS hW U hU).toFunctor
      (fun Y : Scheme.{u} => IsReduced Y) :=
  hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS W hW _ _

/-- **Stacks 08GM.** The pair `(U ⊂ W, f : V ⟶ W)` is an *elementary distinguished square*
when `U` is an open subspace of `W`, `f` is étale, and the projection `f⁻¹(T) ⟶ T` is an
isomorphism, where `T = W \ U` carries the reduced induced subspace structure.  The square of
the source is the fibre product square of `U.ι` and `f`, which this pair determines. -/
structure IsElementaryDistinguishedSquare'
    {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (_hV : IsAlgebraicSpace B S hS V) (U : Subfunctor W) (f : V ⟶ W) : Prop where
  /-- Condition (1): `U` is an open subspace of `W`, its inclusion being the `j` of the
  source. -/
  isOpenSubspace : IsOpenSubspace B S hS U
  /-- Condition (2): `f` is étale. -/
  isEtale : IsEtale B S hS f
  /-- Condition (3): the projection `f⁻¹(T) ⟶ T` is an isomorphism, for `T = W \ U` with its
  reduced induced subspace structure. -/
  isIso_pullback_fst :
    IsIso (pullback.fst (openComplementReducedSubspace B S hS hW U isOpenSubspace).ι f)

end AlgebraicGeometry.Space

end
