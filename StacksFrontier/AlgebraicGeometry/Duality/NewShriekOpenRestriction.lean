module

public import StacksFrontier.AlgebraicGeometry.Duality.NewShriekPseudoFunctor
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDuality
public import StacksFrontier.AlgebraicGeometry.Duality.GlueingDualizingComplexesStandardModel

/-!
# `f_new^!` and restriction to opens

Let `ι : V ⟶ X` be an open immersion and `f : X ⟶ Y`, with complexes `ω_X^•` on `X` and `ω_Y^•`
on `Y`, and put `ω_V^• = ι^* ω_X^•`. Since the derived internal Hom commutes with restriction to
opens ([Stacks, Tag 08DL]) and `ι^* ∘ Lf^* = L(ι ≫ f)^*` ([Stacks, Tag 0D5S]),

`ι^* (f_new^! M) = ι^* D_X(Lf^* D_Y M) ≅ D_V(L(ι ≫ f)^* D_Y M) = (ι ≫ f)_new^! M`.

## Main definitions

* `Stacks.Duality.pullDualIso`: `ι^* ∘ D_X ≅ D_V ∘ ι^*` with `ω_V^• = ι^* ω_X^•`.
* `Stacks.Duality.fNewShriekRestrictIso`: `ι^* ∘ f_new^! ≅ (ι ≫ f)_new^!`.

## References

* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality

open Stacks.Duality.TwistedInverseImageDuality (Std pull sheafHom stdMonoidal stdSymmetric
  stdMonoidalClosed)
open CategoryTheory.MonoidalClosed (dualInto)

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] stdMonoidal stdSymmetric stdMonoidalClosed

variable {V X Y : Scheme.{u}} (ι : V ⟶ X) [IsOpenImmersion ι]

/-- For an open immersion `ι`, restriction commutes with the duality:
`ι^*(R𝓗om(K, ω_X^•)) ≅ R𝓗om(ι^*K, ι^*ω_X^•)` ([Stacks, Tag 08DL]). -/
def pullDualIso (ωX : Std X) :
    dualInto ωX ⋙ pull ι ≅ (pull ι).op ⋙ dualInto ((pull ι).obj ωX) :=
  Functor.isoWhiskerRight (relativeDualIsoSheafHom ωX) (pull ι) ≪≫
    UpperShriekDuality.pullSheafHomIso ι ωX ≪≫
    Functor.isoWhiskerLeft (pull ι).op (relativeDualIsoSheafHom _).symm

/-- **`f_new^!` commutes with restriction to opens**: for an open immersion `ι : V ⟶ X` and
`ι ≫ f = k`, `ι^*(f_new^! M) ≅ k_new^! M` where `k_new^!` is formed with `ω_V^• = ι^* ω_X^•`. -/
def fNewShriekRestrictIso (f : X ⟶ Y) (k : V ⟶ Y) (e : ι ≫ f = k) (ωX : Std X) (ωY : Std Y) :
    fNewShriekStd f ωX ωY ⋙ pull ι ≅ fNewShriekStd k ((pull ι).obj ωX) ωY :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (dualInto ωY).rightOp
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (pull f).op (pullDualIso ι ωX) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (NatIso.op (UpperShriekDuality.pullCompIso ι f k e)).symm _)

end Stacks.Duality

end
