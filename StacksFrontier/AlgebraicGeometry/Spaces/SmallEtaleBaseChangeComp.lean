module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange

/-!
# Base change of étale scheme charts along a composite

`AlgebraicGeometry.Space.smallBaseChange` (Stacks 03G2, part (4)) sends an étale scheme chart of
`Y` to its base change along a representable `g : X ⟶ Y`.  For a composite `g ≫ h` with
`h : Y ⟶ Z` there are two ways to carry a chart `W` of `Z` down to `X`: base change along
`g ≫ h` in one step, or along `h` and then along `g`.  Both are fibre products of `W` with `X`
over `Z`, so they agree; this file proves it.

## Main results

* `AlgebraicGeometry.Space.smallBaseChangeComp`: the composition isomorphism
  `h^* ⋙ g^* ≅ (g ≫ h)^*` of chart base change.
* `AlgebraicGeometry.Space.smallBaseChangeComp_comparison`: it is the transport of
  `AlgebraicGeometry.Space.spacesBaseChange_comp`, the composition isomorphism of base change on
  the spaces-étale site, through the comparison square
  `AlgebraicGeometry.Space.smallBaseChange_comparison`.  Since the comparison functor is
  faithful, this pins the isomorphism down.

## Implementation notes

The isomorphism is obtained by reflecting an isomorphism of the two composites with
`AlgebraicGeometry.Space.comparisonFunctor` along its full faithfulness
(`AlgebraicGeometry.Space.comparisonFunctor_full`,
`AlgebraicGeometry.Space.comparisonFunctor_faithful`), rather than by pasting the two cartesian
squares of `AlgebraicGeometry.Space.smallBaseChange_isPullback`.  The reflected isomorphism is
assembled from `AlgebraicGeometry.Space.smallBaseChange_comparison` at each of the three
morphisms and `AlgebraicGeometry.Space.spacesBaseChange_comp` in the middle, so no naturality
square has to be checked by hand: `CategoryTheory.Functor.fullyFaithfulCancelRight` produces the
natural isomorphism, not merely its components.

Note that the comparison functor is *not* an equivalence — the spaces-étale site has objects
that are not schemes — so the reflection is along full faithfulness alone and the three
representability witnesses stay as hypotheses: `AlgebraicGeometry.Space.smallBaseChange`
depends on the witness it is given, so the witness for the composite cannot be left implicit.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), parts (2) and (4).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Base change of étale scheme charts is compatible with composition.**  Base change
along a composite `g ≫ h` of representable morphisms of algebraic spaces is base change
along `h` followed by base change along `g`.

Both functors send a chart `W` of `Z` to a fibre product of `W` with `X` over `Z`; the
isomorphism is the transport through the comparison equivalences of Stacks 03G1 of the
composition isomorphism `AlgebraicGeometry.Space.spacesBaseChange_comp` of Stacks 03G2,
part (2), which is what `AlgebraicGeometry.Space.smallBaseChangeComp_comparison` records.

No `@[stacks]` attribute is placed: what is proved is the chart-level counterpart of the
composition isomorphism of Stacks 03G2, part (2), internal to this development, and the
attribute for that clause sits on `AlgebraicGeometry.Space.spacesBaseChange_comp`. -/
noncomputable def smallBaseChangeComp {X Y Z : AlgebraicSpaces B S hS} (g : X ⟶ Y) (h : Y ⟶ Z)
    (hg : yoneda.relativelyRepresentable g.hom)
    (hh : yoneda.relativelyRepresentable h.hom)
    (hgh : yoneda.relativelyRepresentable (g ≫ h).hom) :
    smallBaseChange B S hS h hh ⋙ smallBaseChange B S hS g hg ≅
      smallBaseChange B S hS (g ≫ h) hgh :=
  letI := comparisonFunctor_full B S hS X
  letI := comparisonFunctor_faithful B S hS X
  Functor.fullyFaithfulCancelRight (comparisonFunctor B S hS X)
    (Functor.isoWhiskerLeft (smallBaseChange B S hS h hh)
        (smallBaseChange_comparison B S hS g hg) ≪≫
      Functor.isoWhiskerRight (smallBaseChange_comparison B S hS h hh)
        (spacesBaseChange B S hS g).functor ≪≫
      Functor.isoWhiskerLeft (comparisonFunctor B S hS Z)
        (spacesBaseChange_comp B S hS g h) ≪≫
      (smallBaseChange_comparison B S hS (g ≫ h) hgh).symm)

/-- **The composition isomorphism of chart base change is the transport of the spaces-étale
one.**  Read through the comparison square
`AlgebraicGeometry.Space.smallBaseChangeComparisonIso` of Stacks 03G2, part (4),
`AlgebraicGeometry.Space.smallBaseChangeComp` becomes
`AlgebraicGeometry.Space.spacesBaseChange_comp`, the composition isomorphism of part (2).

Since `AlgebraicGeometry.Space.comparisonFunctor` is faithful and the three comparison
isomorphisms are isomorphisms, this determines `AlgebraicGeometry.Space.smallBaseChangeComp`
uniquely; it is the analogue for sites of
`AlgebraicGeometry.Space.smallBaseChange_topos_comparison`. -/
theorem smallBaseChangeComp_comparison {X Y Z : AlgebraicSpaces B S hS} (g : X ⟶ Y) (h : Y ⟶ Z)
    (hg : yoneda.relativelyRepresentable g.hom)
    (hh : yoneda.relativelyRepresentable h.hom)
    (hgh : yoneda.relativelyRepresentable (g ≫ h).hom) (W : SmallEtale B S hS Z.1) :
    (comparisonFunctor B S hS X).map
          ((smallBaseChangeComp B S hS g h hg hh hgh).hom.app W) ≫
        (smallBaseChangeComparisonIso B S hS (g ≫ h) hgh W).hom =
      (smallBaseChangeComparisonIso B S hS g hg
            ((smallBaseChange B S hS h hh).obj W)).hom ≫
        (spacesBaseChange B S hS g).functor.map
            ((smallBaseChangeComparisonIso B S hS h hh W).hom) ≫
          (spacesBaseChange_comp B S hS g h).hom.app
            ((comparisonFunctor B S hS Z).obj W) := by
  let := comparisonFunctor_full B S hS X
  let := comparisonFunctor_faithful B S hS X
  rw [smallBaseChangeComp, Functor.fullyFaithfulCancelRight]
  simp [smallBaseChange_comparison]

end AlgebraicGeometry.Space

end
