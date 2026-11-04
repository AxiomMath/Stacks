module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank

/-!
# Two local-generator presentations of a locally free sheaf of modules through one point

This is the ringed-space half of the étale descent of finite local freeness *of a given rank*,
split out of `StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.RankEtaleDescent`
so that it elaborates. Nothing here mentions schemes, and that is the point: at the import
closure of the Brauer-group tree the two instances
`HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat` and its
`WEqualsLocallyBijective` companion, which every mention of `LocalGeneratorsData` and of
`GeneratingSections` needs, are expensive enough that a proof mentioning them a dozen times does
not fit in the elaborator's budget, while over a variable `X : TopCat` they are cheap.

The mathematical content is Tag 01C9: on a ringed space whose structure stalks are all nonzero,
the rank of a locally free sheaf of modules is a *single* locally constant function of the point,
so the index type of a member of a local-generator presentation through a point is determined by
the point and not by the presentation. Two presentations through one point therefore have
equinumerous index types, and that is what lets a rank read off a pullback be transported back to
the base.

## Main results

* `Stacks.EtaleCohomology.BrauerScheme.mk_generators_eq_mk_generators`: two locally free
  presentations of one sheaf of modules, through one point, have equinumerous index types there.
* `Stacks.EtaleCohomology.BrauerScheme.mk_generators_eq_of_presentations`: a member through a
  point of *any* locally free presentation of a sheaf of modules which is finite locally free of
  rank `r` has index type of cardinality `r`.
* `Stacks.EtaleCohomology.BrauerScheme.mk_generators_eq_of_presentations_scheme`: the same for a
  sheaf of modules on a scheme.
* `Stacks.EtaleCohomology.BrauerScheme.mk_generators_eq_of_transported`: **the rank of a sheaf of
  modules on a scheme is read back along any transported presentation**, which is what turns the
  pullback of a local-generator presentation into a statement about the rank on the base.

## Implementation notes

The re-ascription of a module over `X.ringCatSheaf` as one over
`LocallyFreeRank.toRingSheaf X.toTopCat X.sheaf` -- the same type, not the same term -- is
performed by `let` in `mk_generators_eq_of_presentations_scheme`, whose body does nothing else.
Each identification of that kind is expensive, so each gets a declaration to itself; here, and in
the consumers of this file, that discipline is what keeps the elaborator inside its budget. The
cardinal equalities are chained with `Eq.trans` rather than by `rw`, whose motive check at the
re-ascribed terms exhausts the elaborator. This is the idiom of
`Stacks.EtaleCohomology.BrauerScheme.rank_eq_of_point`.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

noncomputable section

namespace Stacks.EtaleCohomology.BrauerScheme

variable {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- **Two locally free presentations of one sheaf of modules, through one point, have
equinumerous index types there.** On a ringed space whose structure stalks are all nonzero the
rank of a locally free sheaf of modules is a single locally constant function of the point, Tag
01C9, and the index type of a member through a point computes its value there. -/
theorem mk_generators_eq_mk_generators (hO : LocallyFreeRank.StalksNontrivial X O)
    (N : _root_.SheafOfModules.{u} (LocallyFreeRank.toRingSheaf X O))
    (p p' : _root_.SheafOfModules.LocalGeneratorsData.{u} N)
    (hp : p.IsLocallyFreeData) (hp' : p'.IsLocallyFreeData)
    (i : p.I) (j : p'.I) (y : X) (hi : y ∈ p.X i) (hj : y ∈ p'.X j) :
    Cardinal.mk (p.generators i).I = Cardinal.mk (p'.generators j).I :=
  have : N.IsLocallyFree := ⟨p, hp⟩
  (LocallyFreeRank.locallyFreeRank_eq_mk_generators N hO p hp i y hi).symm.trans
    (LocallyFreeRank.locallyFreeRank_eq_mk_generators N hO p' hp' j y hj)

/-- **A member through a point of any locally free presentation of a sheaf of modules which is
finite locally free of rank `r` has index type of cardinality `r`.** The rank-`r` presentation
also has a member through that point, and the two index types there are equinumerous by
`Stacks.EtaleCohomology.BrauerScheme.mk_generators_eq_mk_generators`. -/
theorem mk_generators_eq_of_presentations (hO : LocallyFreeRank.StalksNontrivial X O)
    (N : _root_.SheafOfModules.{u} (LocallyFreeRank.toRingSheaf X O)) {r : ℕ}
    (hr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N r)
    (p' : _root_.SheafOfModules.LocalGeneratorsData.{u} N) (hp' : p'.IsLocallyFreeData)
    (j : p'.I) (y : X) (hj : y ∈ p'.X j) :
    Cardinal.mk (p'.generators j).I = (r : Cardinal.{u}) := by
  obtain ⟨p, hp, hpr⟩ := hr.exists_isFiniteLocallyFreeOfRankData
  obtain ⟨k, hk⟩ := ((Opens.coversTop_iff _ p.X).mp p.coversTop).exists_mem y
  exact (mk_generators_eq_mk_generators hO N p' p hp' hp j k y hj hk).trans
    (Cardinal.mk_eq_nat_iff.mpr ⟨(hpr k).some⟩)

/-- **A member through a point of any locally free presentation of a sheaf of modules on a
scheme which is finite locally free of rank `r` has index type of cardinality `r`.** This is
`mk_generators_eq_of_presentations` on the underlying ringed space, and it is the one declaration
in which a module over `T.ringCatSheaf` is read as a module over
`LocallyFreeRank.toRingSheaf T.toTopCat T.sheaf`: the same type, not the same term, and the
identification is expensive enough that nothing else may happen here. -/
theorem mk_generators_eq_of_presentations_scheme {T : Scheme.{u}} (N : T.Modules) {r : ℕ}
    (hr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N r)
    (p' : _root_.SheafOfModules.LocalGeneratorsData.{u} N) (hp' : p'.IsLocallyFreeData)
    (j : p'.I) (y : T) (hj : y ∈ p'.X j) :
    Cardinal.mk (p'.generators j).I = (r : Cardinal.{u}) :=
  let N' : _root_.SheafOfModules.{u} (LocallyFreeRank.toRingSheaf T.toTopCat T.sheaf) := N
  let p₁ : _root_.SheafOfModules.LocalGeneratorsData.{u} N' := p'
  mk_generators_eq_of_presentations (LocallyFreeRank.scheme_stalksNontrivial T) N' hr p₁ hp'
    j y hj

/-- **A member with a point of a locally free presentation of `M` has index type of cardinality
`r`, given a locally free presentation of a sheaf `N` of rank `r` with a member through a point
of `N`'s scheme carrying the same index type.** This is the glue of the rank descent, stated for
*variable* `M` and `N`: the caller supplies the transported presentation, and nothing in this
signature needs a pullback functor unfolded.

The transported presentation is reported at one index, with an equality of cardinals, rather than
through an equivalence of the two index types, because a statement of the second kind forces
`HasWeakSheafify ((Opens.grothendieckTopology S).over (q.X (e i)))` to be synthesized afresh at
the composite index, which exceeds the elaborator's budget. -/
theorem mk_generators_eq_of_transported {T S : Scheme.{u}} (N : T.Modules) {r : ℕ}
    (hr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens T)
      (J := Opens.grothendieckTopology T) N r)
    {M : S.Modules} (q : _root_.SheafOfModules.LocalGeneratorsData.{u} M) (i : q.I) (y : T)
    (h : ∃ (q' : _root_.SheafOfModules.LocalGeneratorsData.{u} N)
      (_ : q'.IsLocallyFreeData) (j : q'.I),
      y ∈ q'.X j ∧ Cardinal.mk (q'.generators j).I = Cardinal.mk (q.generators i).I) :
    Cardinal.mk (q.generators i).I = (r : Cardinal.{u}) := by
  obtain ⟨q', hq', j, hj, hcard⟩ := h
  exact hcard.symm.trans (mk_generators_eq_of_presentations_scheme N hr q' hq' j y hj)

end Stacks.EtaleCohomology.BrauerScheme

end

end
