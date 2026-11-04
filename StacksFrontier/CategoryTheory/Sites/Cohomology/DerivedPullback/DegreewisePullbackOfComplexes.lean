module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplex
public import StacksCore.Tactic.StacksAttribute

/-! # Degreewise pullback of complexes of modules on ringed topoi

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi. The pullback functor
`f^* = O_C ⊗_{f⁻¹O_D} f⁻¹(-)` of Stacks 03D6 part (2) preserves zero morphisms, being a left
adjoint (Stacks 03D7). Consequently it extends degreewise to complexes, which is the functor
appearing in the statement of Stacks 0G7E.

## Main results

* `Stacks.Sheaves.RingedToposModules.pullbackModules_preservesZeroMorphisms`: pullback of
  sheaves of modules along a morphism of ringed topoi preserves zero morphisms.

## Implementation notes

`Stacks.Sheaves.DerivedPullback.pullbackModules_additive` proves the stronger statement that
the pullback is additive, but only in the presence of `HasSheafify` for the abelian-group
sheafification on both sites. The statement here needs no sheafification beyond the
`HasWeakSheafify` already required to form `f^*`, since preservation of zero morphisms is a
formal consequence of being a left adjoint.

## References

* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' v u v' u'

namespace Stacks.Sheaves.RingedToposModules

open AlgebraicGeometry

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

/-- Pullback of sheaves of modules along a morphism of ringed topoi preserves zero
morphisms: it is a left adjoint by Stacks 03D7, and a left adjoint between categories with
zero morphisms carries zero morphisms to zero morphisms. This is what lets `f^*` be applied
degreewise to a complex of modules, as in Stacks 0G7E. -/
@[stacks 0G7E "degreewise pullback"]
instance pullbackModules_preservesZeroMorphisms (f : RingedToposHom X Y) :
    (f.pullbackModules).PreservesZeroMorphisms :=
  have := (pullbackAdjPushforwardModules f).isLeftAdjoint
  Functor.preservesZeroMorphisms_of_isLeftAdjoint _

end Stacks.Sheaves.RingedToposModules

end
