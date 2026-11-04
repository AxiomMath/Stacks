module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Family.Flat
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.FlatPullbackExact

/-!
# Exactness of pullback along a morphism between ringed semi-representable localizations

The morphism of ringed topoi induced by a morphism of semi-representable objects over a ringed
site is flat, and therefore its pullback functor on sheaves of modules is exact.

## Main results

* `AlgebraicGeometry.RingedSite.familyMorphism_pullback_exact`: pullback of sheaves of modules
  along the induced morphism preserves finite limits and finite colimits.

## Implementation notes

This is exactness of pullback along a flat morphism of ringed topoi, specialised to the induced
morphism; both inputs are already available, namely
`Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap` and
`AlgebraicGeometry.RingedSite.familyMorphism_isFlat`.

The pullback functor is `Stacks.Sheaves.RingedToposModules.pullbackModules`, which is built over
the four-field morphism of ringed topoi that the modules development uses, whereas the induced
morphism is the canonical two-field structure of Stacks 01D3 part (2); the passage between them
is `AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`.

The hypotheses are the ones needed to form the pullback functor in the original coefficient
universe. Those for `forget₂ CommRingCat RingCat` are derivable from
`CategoryTheory.SemiRepresentable.componentwiseTopology_hasSheafCompose_forget₂`, but they are
kept as hypotheses because the statement being realised has them.

## References

* [Stacks Project, Tag 0D9U](https://stacks.math.columbia.edu/tag/0D9U)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedSite

universe w v u r

open CategoryTheory.SemiRepresentable

/-- **Stacks 0D9U.** Pullback of sheaves of modules along the morphism of ringed topoi induced
by a morphism of semi-representable objects is exact. -/
@[stacks 0D9U "f_flat"]
theorem familyMorphism_pullback_exact (X : RingedSite.{u, v, max u v w r})
    {K L : FormalCoproduct.{w} X.C} (f : K ⟶ L)
    [(componentwiseTopology X.J K).HasSheafCompose
      (forget₂ CommRingCat.{max u v w r} RingCat.{max u v w r})]
    [(componentwiseTopology X.J L).HasSheafCompose
      (forget₂ CommRingCat.{max u v w r} RingCat.{max u v w r})]
    [(componentwiseTopology X.J K).HasSheafCompose (forget RingCat.{max u v w r})]
    [(componentwiseTopology X.J L).HasSheafCompose (forget RingCat.{max u v w r})]
    [(componentwiseTopology X.J K).HasSheafCompose (forget AddCommGrpCat.{max u v w r})]
    [(componentwiseTopology X.J L).HasSheafCompose (forget AddCommGrpCat.{max u v w r})]
    [HasWeakSheafify (componentwiseTopology X.J K) AddCommGrpCat.{max u v w r}]
    [(componentwiseTopology X.J K).WEqualsLocallyBijective
      AddCommGrpCat.{max u v w r}] :
    exactFunctor _ _
      ((familyMorphism.{w, v, u, r} X f).val.toRingedToposModulesHom.pullbackModules) :=
  Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap
    (familyMorphism.{w, v, u, r} X f).val (familyMorphism_isFlat X f)

end AlgebraicGeometry.RingedSite

/-! ### The remaining clauses of Stacks 0D9U

The structure sheaf `O_K` and the localized ringed site are constructed in
`StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Ringed`; their clauses of the tag are
recorded here, since the tag is complete only once exactness is available. -/

add_to_stacks 0D9U "structure_sheaf_o_k"
  AlgebraicGeometry.RingedSite.localizationStructureSheaf

add_to_stacks 0D9U "ringed_site" AlgebraicGeometry.RingedSite.localization

end
