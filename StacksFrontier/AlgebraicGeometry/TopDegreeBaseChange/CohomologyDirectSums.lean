module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CoproductsFromFiltered
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.ModuleCohomologyDeltaFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.CohomologyOverAQuasiCompactOpen

/-!
# Cohomology over a quasi-compact open commutes with direct sums

[Stacks, Tag 01FF] says that on a ringed space with a basis of quasi-compact opens whose
pairwise intersections are quasi-compact, cohomology over a quasi-compact open commutes with
*directed* colimits of sheaves of modules. The proof of [Stacks, Tag 0EX3] (b) cites it for
"commutes with *direct sums*", which is a different statement: a coproduct is not a directed
colimit, it is the directed colimit of its finite sub-coproducts.

This file supplies the direct-sum form. The cohomology functors are additive — which is not an
instance anywhere, and is read off the `δ`-functor structure of
`Stacks.Cohomology.ModuleDelta.cohomologyDeltaFunctor` — so they preserve finite coproducts, and
`Stacks.CoproductsFromFiltered.preservesColimitsOfShape_discrete` promotes that together with
Tag 01FF to preservation of arbitrary coproducts.

## Main results

* `Stacks.Cohomology.DirectSum.additive_Hfunctor`: the cohomology functor `H^q(U, -)` is
  additive.
* `Stacks.Cohomology.DirectSum.preservesColimitsOfShape_Hfunctor_of_isFiltered`: [Stacks, Tag
  01FF] as preservation of filtered colimits rather than as invertibility of the canonical map.
* `Stacks.Cohomology.DirectSum.preservesColimitsOfShape_discrete_Hfunctor`: **cohomology over a
  quasi-compact open commutes with arbitrary direct sums.**
* `Stacks.Cohomology.DirectSum.isColimitMapCofan_Hfunctor`: the same in the cofan form that
  `CategoryTheory.NatTrans.isIso_app_of_isColimit_cofan` — the propagation step of
  `Stacks.EilenbergWatts.iso` — consumes.

## Implementation notes

The tag attribute of [Stacks, Tag 01FF] is **withheld**: the tag states the directed-system
form, which is already carried by
`Stacks.Cohomology.Vanishing.isIso_colimit_post_Hfunctor_of_isCompact`, and the statements here
are consequences of it with an extra additivity input rather than members of a covering set for
it.

## References

* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Stacks.Cohomology.DirectSum

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} R)]

/-- **The cohomology functor `H^q(U, -)` is additive.** It is a right derived functor of an
additive functor, which Mathlib does not record as additive; what does record it is the
`δ`-functor `Stacks.Cohomology.ModuleDelta.cohomologyDeltaFunctor`, whose degree-`q` component
is `H^q(U, -)` by definition and whose additivity is one of its fields. -/
theorem additive_Hfunctor (U : Opens X) (q : ℕ) : (Hfunctor R U q).Additive :=
  (ModuleDelta.cohomologyDeltaFunctor R U).additive q

attribute [local instance] additive_Hfunctor

/-- **[Stacks, Tag 01FF] as a preservation statement.** On a ringed space with a basis of
quasi-compact opens whose pairwise intersections are quasi-compact, cohomology over a
quasi-compact open preserves filtered colimits. This is
`Stacks.Cohomology.Vanishing.isIso_colimit_post_Hfunctor_of_isCompact` read through
`CategoryTheory.Limits.preservesColimit_of_isIso_post`. -/
theorem preservesColimitsOfShape_Hfunctor_of_isFiltered
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X)
    (U : Opens X) (hU : IsCompact (U : Set X)) (q : ℕ)
    (I : Type u) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I (Hfunctor R U q) :=
  ⟨fun {F} =>
    have : IsIso (colimit.post F (Hfunctor R U q)) :=
      Vanishing.isIso_colimit_post_Hfunctor_of_isCompact R hBasis hInter F U hU q
    preservesColimit_of_isIso_post (F := F) (G := Hfunctor R U q)⟩

/-- **Cohomology over a quasi-compact open commutes with arbitrary direct sums.** The
hypotheses are those of [Stacks, Tag 01FF]; the direct sums come from its directed colimits
through `Stacks.CoproductsFromFiltered.preservesColimitsOfShape_discrete`, additivity supplying
the finite coproducts.

This is the input the proof of [Stacks, Tag 0EX3] (b) needs from Tag 01FF in order to run
`Stacks.EilenbergWatts.iso`, which asks for direct sums and not for directed colimits. -/
theorem preservesColimitsOfShape_discrete_Hfunctor
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X)
    (U : Opens X) (hU : IsCompact (U : Set X)) (q : ℕ) (J : Type u) :
    PreservesColimitsOfShape (Discrete J) (Hfunctor R U q) :=
  have : PreservesColimitsOfShape (Finset (Discrete J)) (Hfunctor R U q) :=
    preservesColimitsOfShape_Hfunctor_of_isFiltered R hBasis hInter U hU q _
  CoproductsFromFiltered.preservesColimitsOfShape_discrete (Hfunctor R U q)

/-- **Cohomology of a direct sum, in cofan form.** `H^q(U, ⨁ᵢ Fᵢ)` together with the maps
induced by the injections is the coproduct of the `H^q(U, Fᵢ)`. This is the shape consumed by
`CategoryTheory.NatTrans.isIso_app_of_isColimit_cofan`, the step by which
`Stacks.EilenbergWatts.iso` propagates from `R` to the free modules. -/
noncomputable def isColimitMapCofan_Hfunctor
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X)
    (U : Opens X) (hU : IsCompact (U : Set X)) (q : ℕ) {J : Type u}
    (G : J → SheafOfModules.{u} R) :
    IsColimit ((Hfunctor R U q).mapCocone (Cofan.mk (∐ G) (Sigma.ι G))) :=
  have : PreservesColimitsOfShape (Finset (Discrete J)) (Hfunctor R U q) :=
    preservesColimitsOfShape_Hfunctor_of_isFiltered R hBasis hInter U hU q _
  CoproductsFromFiltered.isColimitMapCofan (Hfunctor R U q) G

end Stacks.Cohomology.DirectSum

end
