module

public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.StalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul

/-!
# Detecting ideal sheaves after a flat preimmersion which covers the support

Let `q : W ⟶ X` be a flat preimmersion of schemes. Such a morphism is an isomorphism on every
local ring, so for an ideal sheaf `J` on `X` the inverse image `J.comap q` remembers the stalk
of `J` at every point in the image of `q`. Away from the support of `J` there is nothing to
remember: the stalk is the unit ideal there. Hence if the support of `J` is covered by the image
of `q`, the inverse image along `q` detects inclusions into `J`, and the inverse image detects
equality of two ideal sheaves whose supports are both covered.

The intended `q` is the projection of the cartesian square of
`Stacks.ResolutionOfSurfaces.CartierDescent.exists_isPullback_blowUpToBase_comap_fromSpecStalk`,
which base changes the blowup of a scheme `Y` in an ideal sheaf `M` supported at a single point
`y` along `Y.fromSpecStalk y` ([Stacks, Tag 0805]). That projection is a flat preimmersion and its
image contains the whole fibre of the blowup over `y`, which is exactly the support of the
exceptional ideal sheaf. So the bound "the inverse image of `I` on the blowup is contained in the
`d`-th power of the exceptional ideal", which [Stacks, Tag 0AGT] supplies over the local ring
`𝒪_{Y, y}`, transports up to the blowup of `Y` itself. That is the globalisation step in the
proof of [Stacks, Tag 0AHH].

## Main results

* `Stacks.ResolutionOfSurfaces.CartierDescent.le_of_comap_le_of_support_subset_range`: an
  inclusion of ideal sheaves follows from the inclusion of the inverse images along a flat
  preimmersion whose image contains the support of the larger one.
* `Stacks.ResolutionOfSurfaces.CartierDescent.eq_of_comap_eq_of_support_subset_range`: the same
  for equality, with both supports covered.
* `Stacks.ResolutionOfSurfaces.CartierDescent.le_exceptionalIdeal_pow_of_comap_le`: the bound by
  a power of the exceptional ideal sheaf descends from the blowup over `Spec 𝒪_{Y, y}`.

## Implementation notes

`le_of_comap_le_of_support_subset_range` takes `Flat q` and `IsPreimmersion q` as instance
arguments, which is the form in which an abstract flat preimmersion is most convenient. The
projection of the cartesian square above carries neither property as an instance — it is an
arbitrary morphism with a square as a hypothesis — so `le_exceptionalIdeal_pow_of_comap_le`
obtains the conjunction from the sibling
`Stacks.ResolutionOfSurfaces.CartierDescent.flat_and_isPreimmersion_of_isPullback` and installs
the two halves with `haveI` before applying it.

The ideal-theoretic step is that an isomorphism of rings reflects inclusions of ideals: from
`AlgebraicGeometry.IdealSheafData.stalk_comap` the hypothesis says
`Ideal.map (q.stalkMap z).hom (stalk I x) ≤ Ideal.map (q.stalkMap z).hom (stalk J x)`, and
applying `Ideal.comap_mono` and then `Ideal.comap_map_of_bijective` removes the `Ideal.map` on
both sides.

In `le_exceptionalIdeal_pow_of_comap_le` the morphism `q` is implicit, since it is determined by
the square `sq`, which is the argument a caller actually has in hand after invoking
`Stacks.ResolutionOfSurfaces.CartierDescent.exists_isPullback_blowUpToBase_comap_fromSpecStalk`.
The support hypothesis of `le_of_comap_le_of_support_subset_range` splits on `d`: for `d = 0` the
ideal sheaf is `⊤`, whose support is empty, and for `d = n + 1` the support of the power is the
support of `AlgebraicGeometry.exceptionalIdeal M = M.comap (AlgebraicGeometry.blowUpToBase M)`,
i.e. the preimage of `M.support = {y}`.

## References

* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 0AHH](https://stacks.math.columbia.edu/tag/0AHH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ResolutionOfSurfaces.CartierDescent

/-! ### Inclusions and equalities detected after base change -/

/-- **A flat preimmersion whose image contains the support of an ideal sheaf detects inclusions
into it.** If `q : W ⟶ X` is flat and a preimmersion, `I` and `J` are ideal sheaves on `X` with
`I.comap q ≤ J.comap q`, and the support of `J` is contained in the image of `q`, then `I ≤ J`.

By `AlgebraicGeometry.IdealSheafData.le_of_stalk_le` it suffices to compare stalks. Outside the
support of `J` the stalk of `J` is the unit ideal, so there is nothing to prove; at a point
`q z` of the support, `q` induces an isomorphism of local rings, and an isomorphism of rings
reflects inclusions of ideals. -/
public theorem le_of_comap_le_of_support_subset_range {W X : Scheme.{u}} (q : W ⟶ X)
    [Flat q] [IsPreimmersion q] (I J : X.IdealSheafData)
    (hcomap : I.comap q ≤ J.comap q)
    (hsupp : (J.support : Set X) ⊆ Set.range q.base) :
    I ≤ J := by
  refine AlgebraicGeometry.IdealSheafData.le_of_stalk_le I J fun x => ?_
  by_cases hx : x ∈ J.support
  · obtain ⟨z, rfl⟩ := hsupp hx
    have hiso := AlgebraicGeometry.isIso_stalkMap_of_flat_isPreimmersion q z
    have hz := AlgebraicGeometry.IdealSheafData.stalk_mono hcomap z
    rw [AlgebraicGeometry.IdealSheafData.stalk_comap,
      AlgebraicGeometry.IdealSheafData.stalk_comap] at hz
    have hc := Ideal.comap_mono (f := (q.stalkMap z).hom) hz
    simpa only [Ideal.comap_map_of_bijective _
      (ConcreteCategory.bijective_of_isIso (q.stalkMap z))] using hc
  · rw [(AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_not_mem_support J x).mpr hx]
    exact le_top

/-- **A flat preimmersion whose image contains both supports detects equality of ideal sheaves.**
Two applications of
`Stacks.ResolutionOfSurfaces.CartierDescent.le_of_comap_le_of_support_subset_range`. -/
public theorem eq_of_comap_eq_of_support_subset_range {W X : Scheme.{u}} (q : W ⟶ X)
    [Flat q] [IsPreimmersion q] (I J : X.IdealSheafData)
    (hcomap : I.comap q = J.comap q)
    (hI : (I.support : Set X) ⊆ Set.range q.base)
    (hJ : (J.support : Set X) ⊆ Set.range q.base) :
    I = J :=
  le_antisymm (le_of_comap_le_of_support_subset_range q I J hcomap.le hJ)
    (le_of_comap_le_of_support_subset_range q J I hcomap.ge hI)

/-! ### Descending the exceptional order from the local ring -/

/-- **The order of vanishing along the exceptional ideal sheaf descends from the blowup over the
local ring.** Let `M` be an ideal sheaf on `Y` supported exactly at `y`, let `I` be another ideal
sheaf on `Y` and let `sq` be the cartesian square base changing the blowup of `M` along
`Y.fromSpecStalk y`, with projection `q`. If on the blowup of `Spec 𝒪_{Y, y}` the inverse image
of `I` is contained in the `d`-th power of the exceptional ideal sheaf, then the same holds on
the blowup of `Y`.

This is the globalisation step of [Stacks, Tag 0AHH]: the local input is [Stacks, Tag 0AGT]. The
projection `q` is a flat preimmersion by
`Stacks.ResolutionOfSurfaces.CartierDescent.flat_and_isPreimmersion_of_isPullback`, and the
support of `AlgebraicGeometry.exceptionalIdeal M ^ d` — empty for `d = 0`, and the fibre of the
blowup over `y` otherwise — lies in its image by
`Stacks.ResolutionOfSurfaces.CartierDescent.fibre_subset_range_of_isPullback`, so
`Stacks.ResolutionOfSurfaces.CartierDescent.le_of_comap_le_of_support_subset_range` applies. -/
public theorem le_exceptionalIdeal_pow_of_comap_le {Y : Scheme.{u}} (y : Y)
    (M I : Y.IdealSheafData) (hM : (M.support : Set Y) = {y}) (d : ℕ)
    {q : AlgebraicGeometry.blowUp (M.comap (Y.fromSpecStalk y)) ⟶ AlgebraicGeometry.blowUp M}
    (sq : CategoryTheory.IsPullback
      (AlgebraicGeometry.blowUpToBase (M.comap (Y.fromSpecStalk y))) q
      (Y.fromSpecStalk y) (AlgebraicGeometry.blowUpToBase M))
    (hI : (I.comap (Y.fromSpecStalk y)).comap
        (AlgebraicGeometry.blowUpToBase (M.comap (Y.fromSpecStalk y))) ≤
      AlgebraicGeometry.exceptionalIdeal (M.comap (Y.fromSpecStalk y)) ^ d) :
    I.comap (AlgebraicGeometry.blowUpToBase M) ≤ AlgebraicGeometry.exceptionalIdeal M ^ d := by
  obtain ⟨hflat, hpre⟩ := flat_and_isPreimmersion_of_isPullback y sq
  have := hflat
  have := hpre
  refine le_of_comap_le_of_support_subset_range q _ _ ?_ ?_
  · rw [Stacks.IdealSheaf.comap_pow, comap_exceptionalIdeal_of_isPullback y q sq]
    simpa only [← Scheme.IdealSheafData.comap_comp, sq.w] using hI
  · cases d with
    | zero =>
      simp only [pow_zero]
      exact Set.empty_subset _
    | succ n =>
      rw [Scheme.IdealSheafData.support_pow_succ]
      simpa only [AlgebraicGeometry.exceptionalIdeal, Scheme.IdealSheafData.support_comap,
        TopologicalSpace.Closeds.coe_preimage, hM] using
        fibre_subset_range_of_isPullback y sq

end Stacks.ResolutionOfSurfaces.CartierDescent

end
