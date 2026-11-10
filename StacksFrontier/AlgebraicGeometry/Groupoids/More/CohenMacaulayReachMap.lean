module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.RestrictionAffineQuotient
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.CohenMacaulayRestriction
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.OverPullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.CoproductSliceRefinement
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksCore.Tactic.StacksAttribute

/-!
# The reach map of the Cohen–Macaulay open, and the refinement of Stacks 0489

Step 1 of the proof of **Stacks 0489** replaces a groupoid scheme with flat, locally finitely
presented source and target by its restriction to the open `W` over which the source map is
Cohen–Macaulay, which is legitimate because the *reach map* of that restriction — the morphism
`h : W ×_{W ↪ U, U, t} R ⟶ U` sending an arrow whose target lies in `W` to its source — is flat,
locally of finite presentation and surjective, hence an fppf covering.

Everything needed is already in `CohenMacaulayRestriction`, which is **Stacks 0460**: the open
`AlgebraicGeometry.cohenMacaulayOpen`, the Cohen–Macaulayness and local finite presentation of
the restricted source and target maps, and the surjectivity
`AlgebraicGeometry.source_from_target_surjective` of the composite `t⁻¹(W) ↪ R ⟶ U`.  What this
file adds is the identification of that composite with the reach map: the fibre product
`W ×_{U, t} R` is formed in `Over S`, while the surjectivity statement is about the open
`t⁻¹(W)` of the arrow scheme.  The two are matched by the canonical isomorphism of the underlying
scheme of a fibre product of `Over S` with the fibre product of the underlying schemes, followed
by the identification of a fibre product along an open immersion with the inverse image open.

Combining that with Steps 2 and 3 gives the whole geometric content of the refinement that
Stacks 0489 constructs, as a two-stage statement: first the Cohen–Macaulay open, whose reach map
is flat, locally of finite presentation and surjective, and then — for the restricted groupoid,
which is again an equivalence relation and now has Cohen–Macaulay structure maps — a further
morphism whose reach map is in addition locally quasi-finite.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.cohenMacaulayObjects` and
  `AlgebraicGeometry.GroupoidScheme.cohenMacaulayRestricting`: the Cohen–Macaulay open of
  **Stacks 0460**, as a scheme over `S` with its morphism to the object scheme.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_iso_reachMap_cohenMacaulay`: the reach map of the
  Cohen–Macaulay open is, up to a canonical isomorphism of its source, the source map restricted
  to the arrows whose target lies in that open.
* `AlgebraicGeometry.GroupoidScheme.flat_reachMap_cohenMacaulay`,
  `AlgebraicGeometry.GroupoidScheme.locallyOfFinitePresentation_reachMap_cohenMacaulay` and
  `AlgebraicGeometry.GroupoidScheme.surjective_reachMap_cohenMacaulay`: **Step 1** of the proof
  of **Stacks 0489**.
* `AlgebraicGeometry.GroupoidScheme.exists_cohenMacaulay_and_quasiFinite_refinement`:
  **Steps 1 to 3** of the proof of **Stacks 0489**.

## Implementation notes

The two-stage shape of the last result is forced, not a convenience.  The reach map of the
composite `U' ⟶ W ⟶ U` is not flat: it factors through the base change of the immersion
`U' ⟶ W`, so it is not a covering, and the source proof likewise passes to the quotient twice
rather than once.

Local quasi-finiteness is claimed only for the second stage, which is where the source proof
obtains it; Step 1 gives no quasi-finiteness and none is asserted.

## References

* [Stacks Project, Tag 0460](https://stacks.math.columbia.edu/tag/0460)
* [Stacks Project, Tag 04N0](https://stacks.math.columbia.edu/tag/04N0)
* [Stacks Project, Tag 0489](https://stacks.math.columbia.edu/tag/0489)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)
  [Flat G.source.left] [Flat G.target.left]
  [LocallyOfFinitePresentation G.source.left] [LocallyOfFinitePresentation G.target.left]

/-- The Cohen–Macaulay open of **Stacks 0460**, as a scheme over `S`. -/
public noncomputable abbrev cohenMacaulayObjects : Over S :=
  Over.mk ((cohenMacaulayOpen G).ι ≫ G.objects.hom)

/-- The inclusion of the Cohen–Macaulay open into the object scheme. -/
public noncomputable abbrev cohenMacaulayRestricting : cohenMacaulayObjects G ⟶ G.objects :=
  Over.homMk (cohenMacaulayOpen G).ι

/-- The source `W ×_{U, t} R` of the reach map of the Cohen–Macaulay open is canonically the
open `t⁻¹(W)` of the arrow scheme, and under that identification the reach map is the source
map restricted to that open. -/
public theorem exists_iso_reachMap_cohenMacaulay :
    ∃ e : (pullback (cohenMacaulayRestricting G) G.target).left ≅
        (G.target.left ⁻¹ᵁ cohenMacaulayOpen G).toScheme,
      e.hom ≫ (G.target.left ⁻¹ᵁ cohenMacaulayOpen G).ι ≫ G.source.left =
        (restrictionReachMap G (cohenMacaulayRestricting G)).left := by
  have hrange : Set.range (pullback.snd (cohenMacaulayOpen G).ι G.target.left) =
      Set.range (G.target.left ⁻¹ᵁ cohenMacaulayOpen G).ι := by
    simp [IsOpenImmersion.range_pullbackSnd]
  -- The fibre product square of `Over S`, read on underlying schemes with the inclusion of the
  -- Cohen-Macaulay open spelled as the open immersion rather than as a morphism of `Over S`.
  have hpb : IsPullback (pullback.fst (cohenMacaulayRestricting G) G.target).left
      (pullback.snd (cohenMacaulayRestricting G) G.target).left
      (cohenMacaulayOpen G).ι G.target.left :=
    overFibreProduct_isPullback (cohenMacaulayRestricting G) G.target
  let e₁ := hpb.isoPullback
  let e₂ := IsOpenImmersion.isoOfRangeEq
    (pullback.snd (cohenMacaulayOpen G).ι G.target.left)
    (G.target.left ⁻¹ᵁ cohenMacaulayOpen G).ι hrange
  have he₁ : e₁.hom ≫ pullback.snd (cohenMacaulayOpen G).ι G.target.left =
      (pullback.snd (cohenMacaulayRestricting G) G.target).left :=
    hpb.isoPullback_hom_snd
  have he₂ : e₂.hom ≫ (G.target.left ⁻¹ᵁ cohenMacaulayOpen G).ι =
      pullback.snd (cohenMacaulayOpen G).ι G.target.left :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange
  refine ⟨e₁ ≪≫ e₂, ?_⟩
  change e₁.hom ≫ e₂.hom ≫ (G.target.left ⁻¹ᵁ cohenMacaulayOpen G).ι ≫ G.source.left = _
  rw [← Category.assoc e₂.hom, he₂, ← Category.assoc, he₁, ← Over.comp_left]

/-- A property stable under isomorphisms holds for the reach map of the Cohen–Macaulay open as
soon as it holds for the source map restricted to the open `t⁻¹(W)`. -/
private theorem reachMap_cohenMacaulay_of_restricted_source (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] (h : P ((G.target.left ⁻¹ᵁ cohenMacaulayOpen G).ι ≫ G.source.left)) :
    P (restrictionReachMap G (cohenMacaulayRestricting G)).left := by
  obtain ⟨e, he⟩ := exists_iso_reachMap_cohenMacaulay G
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso P e.hom _).mpr h

/-- **Step 1 of the proof of Stacks 0489.** The reach map of the Cohen–Macaulay open is flat,
being the source map — flat by hypothesis — precomposed with an open immersion. -/
public theorem flat_reachMap_cohenMacaulay :
    Flat (restrictionReachMap G (cohenMacaulayRestricting G)).left := by
  have _ : MorphismProperty.RespectsIso (@Flat.{u}) := Flat.isStableUnderBaseChange.respectsIso
  exact reachMap_cohenMacaulay_of_restricted_source G (@Flat.{u}) inferInstance

/-- **Step 1 of the proof of Stacks 0489.** The reach map of the Cohen–Macaulay open is locally
of finite presentation, being the source map — locally of finite presentation by hypothesis —
precomposed with an open immersion. -/
public theorem locallyOfFinitePresentation_reachMap_cohenMacaulay :
    LocallyOfFinitePresentation (restrictionReachMap G (cohenMacaulayRestricting G)).left := by
  have _ : MorphismProperty.RespectsIso (@LocallyOfFinitePresentation.{u}) :=
    AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange.respectsIso
  exact reachMap_cohenMacaulay_of_restricted_source G (@LocallyOfFinitePresentation.{u})
    inferInstance

/-- **Step 1 of the proof of Stacks 0489.** The reach map of the Cohen–Macaulay open is
surjective: this is part (3) of **Stacks 0460**, that the inverse image of the Cohen–Macaulay
open under the target still maps onto the object scheme along the source. -/
public theorem surjective_reachMap_cohenMacaulay :
    Surjective (restrictionReachMap G (cohenMacaulayRestricting G)).left :=
  reachMap_cohenMacaulay_of_restricted_source G (@Surjective.{u}) (source_from_target_surjective G)

/-- **Steps 1 to 3 of the proof of Stacks 0489.** Let `(U, R, s, t, c, e, i)` be a groupoid
scheme over `S` whose target and source maps form an equivalence relation and are flat and
locally of finite presentation.  Then there is a morphism `g₁ : U₁ ⟶ U` whose reach map is flat,
locally of finite presentation and surjective, and, for the restricted groupoid on `U₁`, a
further morphism `g' : U' ⟶ U₁` whose reach map is flat, locally of finite presentation,
*locally quasi-finite* and surjective.

`g₁` is the inclusion of the Cohen–Macaulay open of **Stacks 0460**, and `g'` is the disjoint
union of the affine slices of **Stacks 04N0** over the finite type points of `U₁`, which
**Stacks 04MZ** and Stacks 04N0 make available because the restricted groupoid has
Cohen–Macaulay structure maps locally of finite presentation and — being again an equivalence
relation — a trivial stabilizer.

The two stages cannot be combined into one: see the implementation notes.

Each stage also carries its size estimate, which is what puts the refined object scheme inside a
size cutoff: the first stage is an *open* of `U`, so it does not increase size, and the second is
the disjoint union of the affine slices, of size at most `2 ^ size U₁ ≤ 2 ^ size U`. -/
public theorem exists_cohenMacaulay_and_quasiFinite_refinement
    [IsEquivalenceRelation G.target G.source] :
    ∃ (U₁ : Over S) (g₁ : U₁ ⟶ G.objects),
      Flat (restrictionReachMap G g₁).left ∧
      LocallyOfFinitePresentation (restrictionReachMap G g₁).left ∧
      Surjective (restrictionReachMap G g₁).left ∧
      U₁.left.size ≤ G.objects.left.size ∧
      ∃ (U' : Over S) (g' : U' ⟶ (GroupoidScheme.restrict G g₁).groupoid.objects),
        Flat (restrictionReachMap (GroupoidScheme.restrict G g₁).groupoid g').left ∧
        LocallyOfFinitePresentation
          (restrictionReachMap (GroupoidScheme.restrict G g₁).groupoid g').left ∧
        LocallyQuasiFinite
          (restrictionReachMap (GroupoidScheme.restrict G g₁).groupoid g').left ∧
        Surjective (restrictionReachMap (GroupoidScheme.restrict G g₁).groupoid g').left ∧
        U'.left.size ≤ 2 ^ G.objects.left.size := by
  have hopen : (cohenMacaulayObjects G).left.size ≤ G.objects.left.size :=
    Scheme.size_coe_opens_le G.objects.left (cohenMacaulayOpen G)
  refine ⟨cohenMacaulayObjects G, cohenMacaulayRestricting G,
    flat_reachMap_cohenMacaulay G, locallyOfFinitePresentation_reachMap_cohenMacaulay G,
    surjective_reachMap_cohenMacaulay G, hopen, ?_⟩
  have _ : LocallyOfFinitePresentation
      (GroupoidScheme.restrict G (cohenMacaulayRestricting G)).groupoid.source.left :=
    restricted_source_locallyOfFinitePresentation G
  have _ : LocallyOfFinitePresentation
      (GroupoidScheme.restrict G (cohenMacaulayRestricting G)).groupoid.target.left :=
    restricted_target_locallyOfFinitePresentation G
  obtain ⟨U', g', hflat, hlfp, hlqf, hsurj, hsz⟩ :=
    exists_reach_locallyQuasiFinite_surjective
      (GroupoidScheme.restrict G (cohenMacaulayRestricting G)).groupoid
      (restricted_source_cohenMacaulay G) (restricted_target_cohenMacaulay G)
  refine ⟨U', g', hflat, hlfp, hlqf, hsurj, hsz.trans ?_⟩
  have hobj : (GroupoidScheme.restrict G (cohenMacaulayRestricting G)).groupoid.objects.left =
      (cohenMacaulayObjects G).left :=
    congrArg Over.left (GroupoidScheme.restrict G (cohenMacaulayRestricting G)).objects_eq
  rw [hobj]
  exact Cardinal.power_le_power_left two_ne_zero hopen

end AlgebraicGeometry.GroupoidScheme

end
