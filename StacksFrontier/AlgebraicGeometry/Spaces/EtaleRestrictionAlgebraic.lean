module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterionUnconditional

/-!
# Algebraicity descends along a surjective étale object of the site

Let `F` be an fppf sheaf of sets on the big fppf site over a scheme `S` and let `V` be an object
of that site whose structure morphism `V ⟶ S` is surjective and étale. If the restriction
`h_V × F` of `F` to `V` is an algebraic space, then so is `F`.

This is the étale counterpart of the last step of Stacks 04SK, and unlike that step it needs no
bootstrap input: the projection `h_V × F ⟶ F` is the base change of `V ⟶ S` along the structure
morphism of `F`, hence representable, surjective and étale, and a sheaf receiving a
representable, surjective, étale morphism from an algebraic space is an algebraic space by
Stacks 0BGR, which is unconditional in
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterionUnconditional`.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_of_surjective_etale_restriction`: a sheaf whose
  restriction to a surjective étale object of the site is an algebraic space is an algebraic
  space.

## Implementation notes

The three properties of the projection come from one square,
`AlgebraicGeometry.Space.isPullback_prod_fst_snd_yoneda_obj`: representability is
`AlgebraicGeometry.Space.relativelyRepresentable_prod_snd` and the two geometric properties are
`AlgebraicGeometry.Space.presheaf_prod_snd` at `Surjective` and at `Etale`, both of which are
stable under base change. Stacks 0BGR asks for the two separately rather than for their
intersection, so no `MorphismProperty.IsStableUnderBaseChange.inf` is needed.

## References

* [Stacks Project, Tag 04SK](https://stacks.math.columbia.edu/tag/04SK)
* [Stacks Project, Tag 0BGR](https://stacks.math.columbia.edu/tag/0BGR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **A sheaf whose restriction to a surjective étale object of the site is an algebraic space is
an algebraic space.** The projection `h_V × F ⟶ F` is the base change of `V ⟶ S` along the
structure morphism of `F`, so it is representable, surjective and étale; Stacks 0BGR concludes.

This is the step that Stacks 04SK takes along a surjective, flat, locally finitely presented
member of an fppf covering, where it consumes the bootstrap theorem Stacks 04S6. Along an étale
member no bootstrap is needed. -/
theorem isAlgebraicSpace_of_surjective_etale_restriction
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (V : BigFppfOver B S hS)
    (hsurj : Surjective ((BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from V)))
    (hetale : Etale ((BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from V)))
    (hVF : IsAlgebraicSpace B S hS (yoneda.obj V ⨯ F)) :
    IsAlgebraicSpace B S hS F :=
  isAlgebraicSpace_of_relativelyRepresentable_surjective_etale B S hS hVF hF prod.snd
    (presheaf_prod_snd (P := @Surjective.{u}) inferInstance V F hsurj)
    (presheaf_prod_snd (P := @Etale.{u}) inferInstance V F hetale)

end AlgebraicGeometry.Space

end
