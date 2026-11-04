module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RestrictionDerivedDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Existence
import StacksCore.Tactic.StacksAttribute

/-!
# The unbounded derived direct image is invariant under a 2-isomorphism

A diagram of ringed topoi commutes, in the sense of [Stacks, Tag 04IC], when its two composites
are 2-isomorphic; so a commutative square of ringed topoi delivers an
`AlgebraicGeometry.RingedToposHom.TwoIso` of two parallel morphisms, and any conclusion read off
`Rf_*` has to be transported along it.
`AlgebraicGeometry.RingedToposHom.TwoIso.pushforwardToDerivedCategoryIso` carries a
2-isomorphism as far as the degreewise direct image followed by `DerivedCategory.Qh`; this file
carries it the remaining step, to the *total right derived* functors, by
`CategoryTheory.Functor.rightDerivedNatIso`.

This is one of the steps the reduction of [Stacks, Tag 03CR] needs in order to state
[Stacks, Tag 099J] for a morphism of ringed topoi: what Tag 03CR delivers about its square is a
2-isomorphism of the two composites, while the conclusion of Tag 099J is about `Rf_*`.

## Main results

* `AlgebraicGeometry.RingedToposHom.TwoIso.derivedPushforwardIso`: 2-isomorphic morphisms of
  ringed topoi have isomorphic unbounded derived direct images.

## References

* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedToposHom.TwoIso

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {f g : RingedToposHom X Y}

/-- Existence of the unbounded right derived functor of the degreewise direct image, registered
at the universes of this file. -/
local instance hasPointwiseRightDerivedFunctor_pushforwardOnHomotopy (h : RingedToposHom X Y) :
    (Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy.{u, u, u, u, u, u}
      h).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
        (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy_hasRightDerivedFunctor h

/-- **The unbounded derived direct image is invariant under a 2-isomorphism of morphisms of
ringed topoi.** Both `Rf_*` and `Rg_*` are total right derived functors, along
`DerivedCategory.Qh` and at the quasi-isomorphisms, of the two degreewise direct images, and
those are isomorphic by
`AlgebraicGeometry.RingedToposHom.TwoIso.pushforwardToDerivedCategoryIso`. -/
def derivedPushforwardIso (t : TwoIso f g) :
    Stacks.Cohomology.DerivedPushforward.derivedPushforward.{u, u, u, u, u, u} f ≅
      Stacks.Cohomology.DerivedPushforward.derivedPushforward.{u, u, u, u, u, u} g :=
  Functor.rightDerivedNatIso
    (Stacks.Cohomology.DerivedPushforward.derivedPushforward.{u, u, u, u, u, u} f)
    (Stacks.Cohomology.DerivedPushforward.derivedPushforward.{u, u, u, u, u, u} g)
    ((Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy.{u, u, u, u, u, u}
      f).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
          (ComplexShape.up ℤ)))
    ((Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy.{u, u, u, u, u, u}
      g).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
          (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
      (ComplexShape.up ℤ))
    t.pushforwardToDerivedCategoryIso

end AlgebraicGeometry.RingedToposHom.TwoIso

end
