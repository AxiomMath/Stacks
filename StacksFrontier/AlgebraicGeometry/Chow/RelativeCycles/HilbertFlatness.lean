module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.HilbertCycleClass
public import StacksFrontier.AlgebraicGeometry.Etale.FlatFiniteTypeNeighborhood
public import StacksFrontier.AlgebraicGeometry.Flatness.FibreFlatnessSpecialization
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatInDimensionsGE
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.ClosedImmersionStalkVanishing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus
public import StacksFrontier.Topology.Dimension.Krull

/-!
# A member of `Hilb(X/S, r)` is flat over the base in every dimension

Let `f : X ⟶ S` be locally of finite type and let `Z` be a member of `Hilb(X/S, r)`, that is, a
closed subscheme `i : Z ⟶ X` whose structure morphism `i ≫ f` to the base is flat, of finite
presentation and of relative dimension at most `r`. Then the direct image `i_* 𝒪_Z` of its
structure sheaf is flat over `S` at *every* point of `X`, so the non-flat locus in every fibre
is empty and `i_* 𝒪_Z` is flat over `S` in dimensions `≥ n` for every `n`.

The flatness of `i ≫ f`, which is part of the data of a member of `Hilb(X/S, r)`, is all that is
used: at a point of the image the stalk of `i_* 𝒪_Z` is the local ring `𝒪_{Z,z}`, whose flatness
over `𝒪_{S, f (i z)}` is flatness of `i ≫ f` at `z`, and off the image the stalk vanishes.

## Main results

* `Stacks.Chow.HilbertCycleDatum.isFlatOverAt_structureModule` — the pushed-forward structure
  sheaf of a member of `Hilb(X/S, r)` is flat over the base at every point of `X`.
* `Stacks.Chow.HilbertCycleDatum.isFlatOverInDimensionsGE_structureModule` — hence it is flat
  over the base in dimensions `≥ n` for every `n`, Stacks 0CWG holding vacuously.

## Implementation notes

The two cases of the pointwise statement are the two halves of the computation of the stalks of
a direct image along a closed immersion. On the image, Tag 05B8 in the form
`AlgebraicGeometry.isFlatOverAt_pushforward_finite_iff` moves the question to the stalk of
`𝒪_Z` at `z` over `𝒪_{S, f (i z)}`, where the scalar action is the one of the stalk map of
`i ≫ f`; that is flatness of `i ≫ f` at `z` in the sense of Tag 02N3, by
`AlgebraicGeometry.isFlatOverAt_unit_iff_isFlatAt`, and `AlgebraicGeometry.Flat.stalkMap`
supplies it from the flatness field of the datum. Off the image the stalk has at most one
element by Tag 00AE, and a module with vanishing stalk is flat over the base by
`AlgebraicGeometry.isFlatOverAt_of_subsingleton_stalk`.

The dimension statement then only needs the boundary convention `dim ∅ = -∞` of Stacks 0055 (3),
in the form `topologicalKrullDim_eq_bot_iff_isEmpty`: the non-flat locus of a fibre is empty, so
its dimension is `⊥`, which is below every natural number. In particular the bound holds for
`n = 0` as well, where the source's `dim < 0` is exactly the emptiness of the locus.

## References

* [Stacks Project, Tag 0CWG](https://stacks.math.columbia.edu/tag/0CWG)
* [Stacks Project, Tag 0H6V](https://stacks.math.columbia.edu/tag/0H6V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

namespace HilbertCycleDatum

variable {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ}

/-- The pushed-forward structure sheaf of a member of `Hilb(X/S, r)` is flat over the base at
every point of `X`.

At a point `i z` of the closed subscheme the stalk of `i_* 𝒪_Z` is the local ring `𝒪_{Z,z}`
(Tag 05B8), on which the action of `𝒪_{S, f (i z)}` is through the stalk map of `i ≫ f`; so the
assertion is flatness of `i ≫ f` at `z`, which is part of the data of the member. At a point
outside the closed subscheme the stalk vanishes (Tag 00AE), and the zero module is flat. -/
theorem isFlatOverAt_structureModule (Z : HilbertCycleDatum f r) (x : X) :
    IsFlatOverAt f.toLRSHom.toShHom Z.structureModule x := by
  by_cases hx : x ∈ Set.range (ConcreteCategory.hom Z.ideal.subschemeι.base)
  · obtain ⟨z, hz⟩ := hx
    have := Z.flat
    refine hz ▸ (isFlatOverAt_pushforward_finite_iff Z.ideal.subschemeι f
      (SheafOfModules.unit Z.ideal.subscheme.ringCatSheaf) z
      (preimage_singleton_of_isClosedImmersion Z.ideal.subschemeι z)).mp ?_
    exact (isFlatOverAt_unit_iff_isFlatAt (Z.ideal.subschemeι ≫ f) z).mpr
      (Flat.stalkMap (Z.ideal.subschemeι ≫ f) z)
  · exact isFlatOverAt_of_subsingleton_stalk f Z.structureModule x
      (subsingleton_stalk_pushforward_of_notMemRange' Z.ideal.subschemeι
        (SheafOfModules.unit Z.ideal.subscheme.ringCatSheaf) x hx)

/-- **Stacks Project, Tag 0CWG for a member of `Hilb(X/S, r)`.** The pushed-forward structure
sheaf of a member of `Hilb(X/S, r)` is flat over the base in dimensions `≥ n`, for every `n`.

The non-flat locus of a fibre is empty by
`Stacks.Chow.HilbertCycleDatum.isFlatOverAt_structureModule`, so it has dimension `⊥`, and `⊥`
is less than every natural number. -/
theorem isFlatOverInDimensionsGE_structureModule [LocallyOfFiniteType f]
    (Z : HilbertCycleDatum f r) (n : ℕ) :
    IsFlatOverInDimensionsGE f Z.structureModule n := by
  intro s
  have hempty : IsEmpty
      ↥{y : f.fiber s | ¬ IsFlatOverAt f.toLRSHom.toShHom Z.structureModule (f.fiberι s y)} :=
    ⟨fun y => y.2 (Z.isFlatOverAt_structureModule (f.fiberι s y.1))⟩
  rw [(topologicalKrullDim_eq_bot_iff_isEmpty _).mpr hempty]
  exact bot_lt_iff_ne_bot.mpr (WithBot.natCast_ne_bot n)

end HilbertCycleDatum

end Stacks.Chow

end
