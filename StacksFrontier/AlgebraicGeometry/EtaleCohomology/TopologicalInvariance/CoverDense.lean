module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.Fullness

/-!
# Cover-density of small étale base change: the open immersion case

Let `f : X ⟶ Y` be a universal homeomorphism. By
`Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism_of_isCoverDense` the only
input still missing for base change along `f` to be a dense subsite inclusion of small étale
sites is *cover-density*, which
`Stacks.EtaleCohomology.isCoverDense_smallEtaleBaseChange_iff` unfolds to the elementary
statement that every point of every scheme étale over `X` lies in the image of a morphism to it
from a base change of a scheme étale over `Y`.

That statement is Stacks Project Tag 04DW, property (C) for an integral morphism which is a
homeomorphism onto a closed subset, and it **is** proved in this library, by
`Stacks.EtaleCohomology.hasPropertyC_of_isIntegralHom_of_isClosedEmbedding`; cover-density in
general is `Stacks.EtaleCohomology.isCoverDense_smallEtaleBaseChange_of_universalHomeomorphism`
in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DenseSubsite`, which
reads Tag 04DW through a homeomorphism on points.

What is proved here is the Zariski case of cover-density, which needs no descent at all: an
*open* subscheme of `X` is
the base change of an open subscheme of `Y`, because `f` is a homeomorphism on points. This is
the degree-one base case of the induction in the second proof of Tag 04DZ in the source, where
Tag 025G (`Stacks.Etale.tfae_isOpenImmersion`) reduces a degree-one étale morphism to an open
immersion.

## Main results

* `Stacks.EtaleCohomology.isHomeomorph_base_of_universalHomeomorphism`: a universal
  homeomorphism is a homeomorphism on underlying spaces.
* `Stacks.EtaleCohomology.mem_range_left_of_isIso_left`: a morphism of the small étale site
  which is an isomorphism of schemes is surjective on points.
* `Stacks.EtaleCohomology.exists_hom_isIso_left_of_isOpenImmersion`: for `U` étale over `X`
  with `U.hom` an open immersion, there is a scheme `V` étale over `Y` and a morphism
  `X ×_Y V ⟶ U` over `X` which is an isomorphism on underlying schemes.
* `Stacks.EtaleCohomology.exists_isoBaseChange_of_isOpenImmersion`: consequently such a `U` is
  isomorphic, in the small étale site of `X`, to the base change of a scheme étale over `Y`.
  This is the essential surjectivity half of Stacks Project Tag 04DZ for open immersions.
* `Stacks.EtaleCohomology.exists_mem_range_hom_of_isOpenImmersion`: consequently the
  cover-density clause of
  `Stacks.EtaleCohomology.isCoverDense_smallEtaleBaseChange_iff` holds for such a `U`.
* `Stacks.EtaleCohomology.isCoverDense_of_essSurj`: essential surjectivity of base change
  implies cover-density, for an arbitrary morphism of schemes. Cover-density is the weaker of
  the two conditions, and is the one that Tag 03SI needs.

## Implementation notes

The open subscheme of `Y` is produced set-theoretically: `f.base` is an open embedding, indeed
a homeomorphism, so the image `f.base '' Set.range U.hom.base` is open and its preimage is
`Set.range U.hom.base` again. Its base change along `f` is identified with `U` by the range
computation `AlgebraicGeometry.Scheme.Pullback.range_snd`: the first projection
`pullback V.ι f ⟶ X` is an open immersion with the same image as `U.hom`, so
`AlgebraicGeometry.IsOpenImmersion.lift` produces the comparison morphism and
`AlgebraicGeometry.IsOpenImmersion.of_comp` makes it an open immersion, hence an isomorphism
since it is surjective.

Nothing here is specific to étale morphisms beyond an open immersion being étale: the content
is that the Zariski site of `X` is the Zariski site of `Y`.

## References

* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 04DW](https://stacks.math.columbia.edu/tag/04DW)
* [Stacks Project, Tag 04DR](https://stacks.math.columbia.edu/tag/04DR)
* [Stacks Project, Tag 04DQ](https://stacks.math.columbia.edu/tag/04DQ)
* [Stacks Project, Tag 04DM](https://stacks.math.columbia.edu/tag/04DM)
* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
* [Stacks Project, Tag 025G](https://stacks.math.columbia.edu/tag/025G)
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}}

/-- A universal homeomorphism of schemes is a homeomorphism on underlying topological spaces:
it is its own base change along the identity. -/
theorem isHomeomorph_base_of_universalHomeomorphism (f : X ⟶ Y) [UniversalHomeomorphism f] :
    IsHomeomorph f.base :=
  UniversalHomeomorphism.universally_isHomeomorph _ _ _ IsPullback.of_id_snd

/-- A morphism of the small étale site of `X` which is an isomorphism on underlying schemes has
every point of its target in its image. -/
theorem mem_range_left_of_isIso_left {U U' : X.Etale} (m : U' ⟶ U) [IsIso m.left]
    (u : U.left) : u ∈ Set.range m.left := by
  refine ⟨(inv m.left).base u, ?_⟩
  rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
  rfl

/-- **An open subscheme of `X` is a base change from `Y`.** Let `f : X ⟶ Y` be a universal
homeomorphism and let `U` be a scheme étale over `X` whose structure morphism is an open
immersion. Then there is a scheme `V` étale over `Y` — an open subscheme of `Y` — and a
morphism `X ×_Y V ⟶ U` over `X` which is an isomorphism of schemes.

The open subscheme of `Y` is the image of `U` under the homeomorphism `f.base`. -/
theorem exists_hom_isIso_left_of_isOpenImmersion (f : X ⟶ Y) [UniversalHomeomorphism f]
    (U : X.Etale) [IsOpenImmersion U.hom] :
    ∃ (V : Y.Etale) (m : (smallEtaleBaseChange f).obj V ⟶ U), IsIso m.left := by
  have hf := isHomeomorph_base_of_universalHomeomorphism f
  let V₀ : Y.Opens :=
    ⟨f.base '' Set.range U.hom.base, hf.isOpenMap _ U.hom.isOpenEmbedding.isOpen_range⟩
  have hrange : Set.range (pullback.snd V₀.ι f) = Set.range U.hom := by
    rw [Scheme.Pullback.range_snd, Scheme.Opens.range_ι]
    exact Set.preimage_image_eq _ hf.injective
  set l := IsOpenImmersion.lift U.hom (pullback.snd V₀.ι f) hrange.le
  have hl : l ≫ U.hom = pullback.snd V₀.ι f := IsOpenImmersion.lift_fac _ _ _
  have hlsurj : Function.Surjective l.base := by
    intro x
    obtain ⟨y, hy⟩ : U.hom.base x ∈ Set.range (pullback.snd V₀.ι f) := by
      rw [hrange]
      exact Set.mem_range_self x
    refine ⟨y, U.hom.isOpenEmbedding.injective ?_⟩
    rwa [← Scheme.Hom.comp_apply, hl]
  have : IsOpenImmersion (l ≫ U.hom) := by
    rw [hl]
    infer_instance
  have : IsOpenImmersion l := IsOpenImmersion.of_comp l U.hom
  exact ⟨Scheme.Etale.mk V₀.ι, MorphismProperty.Over.homMk l hl trivial,
    isIso_of_isOpenImmersion_of_opensRange_eq_top l
      (TopologicalSpace.Opens.ext (Set.range_eq_univ.mpr hlsurj))⟩

/-- **Base change along a universal homeomorphism is essentially surjective on open
immersions.** A scheme étale over `X` whose structure morphism is an open immersion is
isomorphic, in the small étale site of `X`, to the base change of a scheme étale over `Y`.

This is the essential surjectivity half of Stacks Project, Tag 04DZ restricted to open
immersions; it is the degree-one case of the induction in the source. -/
theorem exists_isoBaseChange_of_isOpenImmersion (f : X ⟶ Y) [UniversalHomeomorphism f]
    (U : X.Etale) [IsOpenImmersion U.hom] :
    ∃ V : Y.Etale, Nonempty ((smallEtaleBaseChange f).obj V ≅ U) := by
  obtain ⟨V, m, hm⟩ := exists_hom_isIso_left_of_isOpenImmersion f U
  exact ⟨V, ⟨MorphismProperty.Over.isoMk (asIso m.left) (MorphismProperty.Over.w m)⟩⟩

/-- **The cover-density clause holds for open immersions.** For a universal homeomorphism `f`
and a scheme `U` étale over `X` whose structure morphism is an open immersion, every point of
`U` lies in the image of a morphism to `U` from a base change of a scheme étale over `Y`.

This is the instance of the condition of
`Stacks.EtaleCohomology.isCoverDense_smallEtaleBaseChange_iff` at such a `U`. The condition at
a general `U` is Stacks Project, Tag 04DW, which is proved in this library, by
`Stacks.EtaleCohomology.hasPropertyC_of_isIntegralHom_of_isClosedEmbedding`; what is special
about an open immersion is that the dominating morphism is here an isomorphism. -/
theorem exists_mem_range_hom_of_isOpenImmersion (f : X ⟶ Y) [UniversalHomeomorphism f]
    (U : X.Etale) [IsOpenImmersion U.hom] (u : U.left) :
    ∃ (V : Y.Etale) (m : (smallEtaleBaseChange f).obj V ⟶ U),
      u ∈ Set.range m.left := by
  obtain ⟨V, m, hm⟩ := exists_hom_isIso_left_of_isOpenImmersion f U
  exact ⟨V, m, mem_range_left_of_isIso_left m u⟩

/-- **Cover-density is weaker than essential surjectivity.** If base change along `f` is
essentially surjective on small étale sites then it is cover-dense.

The converse direction is false in general: cover-density only asks that the base changes be
jointly surjective onto each scheme étale over `X`, not that they exhaust it up to
isomorphism. So this is the implication that makes Stacks Project Tag 04DZ, the equivalence of
small étale categories, suffice for Tag 03SI; proving cover-density alone would not give
Tag 04DZ. Compare
`Stacks.EtaleCohomology.isEquivalence_of_universalHomeomorphism_of_essSurj`, which needs
essential surjectivity, with
`Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism_of_isCoverDense`, which needs
only cover-density. -/
theorem isCoverDense_of_essSurj (f : X ⟶ Y)
    [(smallEtaleBaseChange f).EssSurj] :
    (smallEtaleBaseChange f).IsCoverDense (smallEtaleTopology X) := by
  refine (isCoverDense_smallEtaleBaseChange_iff f).2 fun U u => ?_
  obtain ⟨V, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := smallEtaleBaseChange f) U
  have hiso : IsIso e.hom.left :=
    inferInstanceAs
      (IsIso ((Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X).map e.hom))
  exact ⟨V, e.hom, mem_range_left_of_isIso_left e.hom u⟩

end Stacks.EtaleCohomology

end
