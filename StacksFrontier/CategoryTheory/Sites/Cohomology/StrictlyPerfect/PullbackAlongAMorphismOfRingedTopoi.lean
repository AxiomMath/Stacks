module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.Functoriality
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Pullback of a strictly perfect complex along a morphism of ringed topoi

Let `f : (C, O_C) → (D, O_D)` be a morphism of ringed topoi. The pullback `f^*` of sheaves of
modules, applied degreewise, carries a strictly perfect complex of `O_D`-modules to a strictly
perfect complex of `O_C`-modules.

## Main results

* `AlgebraicGeometry.RingedToposHom.isStrictlyPerfect_pullbackModules`: strict perfectness is
  preserved by the degreewise pullback of complexes.

## Implementation notes

The two structure sheaves have sections in a common universe `w`; the two sites keep independent
object and morphism universes.

## References

* [Stacks Project, Tag 08H3](https://stacks.math.columbia.edu/tag/08H3)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 03DF](https://stacks.math.columbia.edu/tag/03DF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u v' u' w

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Let `f : (C, O_C) → (D, O_D)` be a morphism of ringed topoi. If `E` is a strictly perfect
complex of `O_D`-modules, then `f^*E`, the degreewise pullback, is a strictly perfect complex of
`O_C`-modules. -/
@[stacks 08H3]
theorem isStrictlyPerfect_pullbackModules (f : RingedToposHom X Y)
    {E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (hE : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) E) :
    IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (((f.toModulesHom.pullbackModules).mapHomologicalComplex (ComplexShape.up ℤ)).obj E) := by
  have := pullbackModules_preservesFiniteColimits f
  exact SheafOfModules.isStrictlyPerfect_map (f.toModulesHom.pullbackModules)
    (Stacks.Sheaves.FinitePresentation.pullbackModulesUnitIso f.toModulesHom).symm hE

end AlgebraicGeometry.RingedToposHom

end
