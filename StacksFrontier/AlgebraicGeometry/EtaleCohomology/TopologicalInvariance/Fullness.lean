module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.MorphismDescent

/-!
# Fullness of small étale base change along a universal homeomorphism

Let `f : X ⟶ Y` be a universal homeomorphism. This file transports Stacks Project Tag 0BTY,
proved for slice categories in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/TopologicalInvariance/MorphismDescent.lean`, to
the small étale sites: base change along `f` is a full, and hence fully faithful, functor from
the schemes étale over `Y` to the schemes étale over `X`.

Together with `Stacks.EtaleCohomology.smallEtaleBaseChange_faithful` this makes the hom-level
half of Stacks Project Tag 04DZ unconditional for a universal homeomorphism. What remains of
Tag 04DZ is exactly its essential surjectivity half, which on the small étale site is
cover-density; `Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism_of_isCoverDense`
records that cover-density is now the *only* remaining hypothesis for base change to be a dense
subsite inclusion.

## Main results

* `Stacks.EtaleCohomology.smallEtaleBaseChange_full_of_universalHomeomorphism`: base change
  along a universal homeomorphism is full on small étale sites. This is Stacks Project,
  Tag 0BTY on the small étale site.
* `Stacks.EtaleCohomology.smallEtaleBaseChangeFullyFaithful_of_universalHomeomorphism`: base
  change along a universal homeomorphism is fully faithful on small étale sites.
* `Stacks.EtaleCohomology.isEquivalence_of_universalHomeomorphism_of_essSurj`: base change
  along a universal homeomorphism is an equivalence of small étale categories as soon as it is
  essentially surjective. This is the precise remaining content of Tag 04DZ.
* `Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism_of_isCoverDense`: base
  change along a universal homeomorphism is a dense subsite inclusion as soon as it is
  cover-dense.

## Implementation notes

The transport from the slice category to `AlgebraicGeometry.Scheme.Etale` is the same as in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/TopologicalInvariance/Basic.lean`: the
identification `Stacks.EtaleCohomology.forget_map_smallEtaleBaseChange_map` of base change on
the small étale site with the slice pullback, together with full faithfulness of
`AlgebraicGeometry.Scheme.Etale.forget`. No new geometry enters here.

Faithfulness is not reproved: it holds for any surjection, by
`Stacks.EtaleCohomology.smallEtaleBaseChange_faithful`, and a universal homeomorphism is
surjective.

Cover-density is *not* proved here and is not implied by fullness; see
`Stacks.EtaleCohomology.isCoverDense_smallEtaleBaseChange_iff` for what it asks for in
elementary terms.

## References

* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
* [Stacks Project, Tag 0BTZ](https://stacks.math.columbia.edu/tag/0BTZ)
* [Stacks Project, Tag 0BU0](https://stacks.math.columbia.edu/tag/0BU0)
* [Stacks Project, Tag 0BTL](https://stacks.math.columbia.edu/tag/0BTL)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}}

/-- **Base change along a universal homeomorphism is full on small étale sites.** For `V` and
`W` étale over `Y`, every morphism `X ×_Y V ⟶ X ×_Y W` over `X` is the base change of a
morphism `V ⟶ W` over `Y`.

This is Stacks Project, Tag 0BTY read on the small étale site; the content is
`Stacks.Etale.bijective_pullbackHom_of_universalHomeomorphism`. -/
@[stacks 0BTY "fullness of base change on the small étale site"]
instance smallEtaleBaseChange_full_of_universalHomeomorphism (f : X ⟶ Y)
    [UniversalHomeomorphism f] : (smallEtaleBaseChange f).Full where
  map_surjective {V W} a := by
    have hW : Etale ((Scheme.Etale.forget Y).obj W).hom := W.prop
    obtain ⟨b₀, hb₀⟩ := (Stacks.Etale.bijective_pullbackHom_of_universalHomeomorphism f
      ((Scheme.Etale.forget Y).obj W) ((Scheme.Etale.forget Y).obj V)).2
      ((Scheme.Etale.forget X).map a)
    obtain ⟨b, hb⟩ := (Scheme.Etale.forget Y).map_surjective b₀
    refine ⟨b, (Scheme.Etale.forget X).map_injective ?_⟩
    rw [forget_map_smallEtaleBaseChange_map, hb]
    exact hb₀

/-- **Base change along a universal homeomorphism is fully faithful on small étale sites.**
This is the hom-level half of Stacks Project, Tag 04DZ. -/
noncomputable def smallEtaleBaseChangeFullyFaithful_of_universalHomeomorphism (f : X ⟶ Y)
    [UniversalHomeomorphism f] : (smallEtaleBaseChange f).FullyFaithful :=
  have := smallEtaleBaseChange_faithful_of_universalHomeomorphism f
  Functor.FullyFaithful.ofFullyFaithful _

/-- **Essential surjectivity is all that is left of Tag 04DZ.** For a universal homeomorphism
`f`, base change is an equivalence of the small étale categories as soon as it is essentially
surjective, i.e. as soon as every scheme étale over `X` is isomorphic to the base change of a
scheme étale over `Y`.

Full faithfulness is now unconditional, by
`Stacks.EtaleCohomology.smallEtaleBaseChangeFullyFaithful_of_universalHomeomorphism`, so this
is the precise form in which Stacks Project, Tag 04DZ is still open in this development. -/
theorem isEquivalence_of_universalHomeomorphism_of_essSurj (f : X ⟶ Y)
    [UniversalHomeomorphism f] [(smallEtaleBaseChange f).EssSurj] :
    (smallEtaleBaseChange f).IsEquivalence :=
  have := smallEtaleBaseChange_faithful_of_universalHomeomorphism f
  { }

/-- **Cover-density is all that is left.** For a universal homeomorphism `f`, base change
exhibits the small étale site of `Y` as a dense subsite of that of `X` as soon as it is
cover-dense.

Of the four conditions for a dense subsite inclusion, faithfulness and the covering criterion
hold for any surjection
(`Stacks.EtaleCohomology.smallEtaleBaseChange_faithful` and
`Stacks.EtaleCohomology.functorPushforward_mem_smallEtaleTopology_iff`), and local fullness and
local faithfulness now follow from
`Stacks.EtaleCohomology.smallEtaleBaseChange_full_of_universalHomeomorphism`. So the hypothesis
carried in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/UniversalHomeomorphismInvariance.lean` reduces to
the single statement that base change is cover-dense, spelled out in
`Stacks.EtaleCohomology.isCoverDense_smallEtaleBaseChange_iff`. -/
theorem isDenseSubsite_of_universalHomeomorphism_of_isCoverDense (f : X ⟶ Y)
    [UniversalHomeomorphism f]
    [(smallEtaleBaseChange f).IsCoverDense (smallEtaleTopology X)] :
    (smallEtaleBaseChange f).IsDenseSubsite
      (smallEtaleTopology Y) (smallEtaleTopology X) :=
  isDenseSubsite_of_universalHomeomorphism_of_full_of_isCoverDense f

end Stacks.EtaleCohomology

end
