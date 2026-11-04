module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.Fullness
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Reduction

/-!
# Reductions for essential surjectivity of small étale base change

Let `f : X ⟶ Y` be a universal homeomorphism. Full faithfulness of base change on the small
étale sites is unconditional, by
`Stacks.EtaleCohomology.smallEtaleBaseChangeFullyFaithful_of_universalHomeomorphism`, so the
whole of Stacks Project Tag 04DZ is the essential surjectivity of
`Stacks.EtaleCohomology.smallEtaleBaseChange f`; this is recorded in
`Stacks.EtaleCohomology.isEquivalence_of_universalHomeomorphism_of_essSurj`.

This file supplies the two formal moves available for that remaining statement. Base change on
small étale sites turns a composite into a composite of functors, so essential surjectivity is
stable under composition; and because base change along a universal homeomorphism is fully
faithful, essential surjectivity along a composite `f ≫ g` *descends* to its second factor `g`.

Together these say that the class of morphisms along which small étale base change is
essentially surjective is closed under composition and under cancelling a universal
homeomorphism on the left. The latter is the standard first step of Tag 04DZ: in proving
essential surjectivity along `g : X ⟶ Y` one may replace `X` by any scheme universally
homeomorphic to it over `X`, and in particular by its reduction.

Nothing here proves essential surjectivity in any case: that is Stacks Project Tag 0BTP
(effectivity of étale descent data along a surjective integral morphism), which this
development does not have. See the implementation notes.

## Main results

* `Stacks.EtaleCohomology.smallEtaleBaseChangeComp` (imported) : base change along a composite
  is the composite of the base changes.
* `Stacks.EtaleCohomology.essSurj_smallEtaleBaseChange_comp`: essential surjectivity of small
  étale base change is stable under composition.
* `Stacks.EtaleCohomology.essSurj_smallEtaleBaseChange_of_comp`: if small étale base change
  along `f ≫ g` is essentially surjective and `f` is a universal homeomorphism, then small
  étale base change along `g` is essentially surjective.
* `Stacks.EtaleCohomology.essSurj_smallEtaleBaseChange_of_essSurj_comp_nilradicalSubschemeι`:
  in proving essential surjectivity along `g : X ⟶ Y` one may assume the source is reduced.
* `Stacks.EtaleCohomology.isEquivalence_of_universalHomeomorphism_of_essSurj_comp`: Tag 04DZ for
  a universal homeomorphism `g` follows from essential surjectivity along `f ≫ g` for any
  universal homeomorphism `f` with target the source of `g`.

## Implementation notes

`Stacks.EtaleCohomology.smallEtaleBaseChange` is the restriction to étale objects of the
slice pullback, so `Stacks.EtaleCohomology.smallEtaleBaseChangeComp` is
`CategoryTheory.MorphismProperty.Over.pullbackComp` for the étale morphism property. The two
instances that definition needs are supplied locally rather than globally, matching how
`Stacks.EtaleCohomology.smallEtaleBaseChange` supplies them itself.

The same comparison for the small étale site of a big étale site is
`AlgebraicGeometry.smallEtaleBaseChange_compIso` (Tag 021J). That is a different category — the
small étale site cut out of a fixed big site — so the two do not subsume one another, and the
tag is left on the existing declaration.

Essential surjectivity is strictly stronger than cover-density and the two are deliberately
kept apart; `Stacks.EtaleCohomology.isCoverDense_of_essSurj` is the one-way implication. No
statement here is tagged 04DZ or 03SI, because neither is proved: the missing input is
Tag 0BTP, whose own proof needs fpqc descent for separated étale morphisms (Tag 02W8), full
faithfulness of the étale descent functor along a surjective universally closed morphism
(Tag 0BTL), Zariski-local effectivity (Tag 0BTM) and the henselian splitting of a
quasi-compact separated étale scheme (Tag 0BTN), none of which this development has.

## References

* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
* [Stacks Project, Tag 09ZL](https://stacks.math.columbia.edu/tag/09ZL)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
* [Stacks Project, Tag 054M](https://stacks.math.columbia.edu/tag/054M)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {X Y Z : Scheme.{u}}

-- Small étale base change along a composite is
-- `Stacks.EtaleCohomology.smallEtaleBaseChangeComp`, proved in
-- `StacksDraft.AlgebraicGeometry.EtaleCohomology.Ch59Rank.BaseChangeContinuous` and imported
-- above. It is `CategoryTheory.MorphismProperty.Over.pullbackComp` for the étale morphism
-- property; the proof is not repeated here.

/-- **Essential surjectivity of small étale base change is stable under composition.** If every
scheme étale over `Y` is a base change along `f` and every scheme étale over `Z` is a base
change along `g`, then every scheme étale over `X` is a base change along `f ≫ g`. -/
theorem essSurj_smallEtaleBaseChange_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [(smallEtaleBaseChange f).EssSurj]
    [(smallEtaleBaseChange g).EssSurj] :
    (smallEtaleBaseChange (f ≫ g)).EssSurj :=
  Functor.essSurj_of_iso (smallEtaleBaseChangeComp f g).symm

/-- **A universal homeomorphism may be cancelled on the left.** If small étale base change
along `f ≫ g` is essentially surjective and `f` is a universal homeomorphism, then small étale
base change along `g` is essentially surjective.

The point is that base change along the universal homeomorphism `f` is fully faithful
(`Stacks.EtaleCohomology.smallEtaleBaseChangeFullyFaithful_of_universalHomeomorphism`), hence
reflects isomorphisms, so an isomorphism produced over the source of `f` descends. Nothing is
assumed about `g`.

In proving Stacks Project Tag 04DZ for a universal homeomorphism `g : X ⟶ Y` this allows `X` to
be replaced by any scheme universally homeomorphic to it over `X`. -/
theorem essSurj_smallEtaleBaseChange_of_comp (f : X ⟶ Y) [UniversalHomeomorphism f] (g : Y ⟶ Z)
    [(smallEtaleBaseChange (f ≫ g)).EssSurj] :
    (smallEtaleBaseChange g).EssSurj :=
  have := smallEtaleBaseChange_faithful_of_universalHomeomorphism f
  have : (smallEtaleBaseChange g ⋙
      smallEtaleBaseChange f).EssSurj :=
    Functor.essSurj_of_iso (smallEtaleBaseChangeComp f g)
  Functor.essSurj_of_comp_fully_faithful (smallEtaleBaseChange g)
    (smallEtaleBaseChange f)

/-- **One may assume the source is reduced.** Essential surjectivity of small étale base change
along `g : X ⟶ Y` follows from essential surjectivity along the composite
`X_{red} ⟶ X ⟶ Y`, because the canonical closed immersion of the reduction of `X` is a
universal homeomorphism (Stacks Project, Tag 054M). -/
theorem essSurj_smallEtaleBaseChange_of_essSurj_comp_nilradicalSubschemeι (g : X ⟶ Y)
    [(smallEtaleBaseChange (X.nilradical.subschemeι ≫ g)).EssSurj] :
    (smallEtaleBaseChange g).EssSurj :=
  essSurj_smallEtaleBaseChange_of_comp X.nilradical.subschemeι g

/-- **Tag 04DZ after cancelling a universal homeomorphism.** Let `g : Y ⟶ Z` be a universal
homeomorphism and let `f : X ⟶ Y` be any universal homeomorphism. If small étale base change
along `f ≫ g` is essentially surjective, then small étale base change along `g` is an
equivalence of small étale categories.

This is not a proof of Stacks Project Tag 04DZ: it reduces that theorem for `g` to essential
surjectivity along `f ≫ g`, which for no `f` is available in this development. The input still
missing is Stacks Project Tag 0BTP. -/
theorem isEquivalence_of_universalHomeomorphism_of_essSurj_comp (f : X ⟶ Y)
    [UniversalHomeomorphism f] (g : Y ⟶ Z) [UniversalHomeomorphism g]
    [(smallEtaleBaseChange (f ≫ g)).EssSurj] :
    (smallEtaleBaseChange g).IsEquivalence :=
  have := essSurj_smallEtaleBaseChange_of_comp f g
  isEquivalence_of_universalHomeomorphism_of_essSurj g

end Stacks.EtaleCohomology

end

end
