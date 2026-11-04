module

public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.Evaluation
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.KernelBaseChange

/-!
# Base change of the conormal source `ker q ⊗ L^{⊗ -1}` of an invertible quotient

Tag 0B3V identifies the conormal sheaf of the section of `𝐏(ℰ) ⟶ X` cut out by an invertible
quotient `q : ℰ ⟶ L` with `(\ker q) ⊗ L^{⊗ -1}`. The base-change clause of the tag therefore
compares that module for a quotient `Q` of `ℰ` on `X` with the one for a quotient `Q'` of `ℰ'`
on `X'`, along a morphism `g : X' ⟶ X` and identifications `hE : ℰ' ≅ g^*ℰ`,
`hL : Q'.L ≅ g^*Q.L` compatible with the two quotient maps.

This file builds that comparison. It is the tensor product of the two base-change comparisons
that are already available unconditionally,

* `Stacks.Divisors.quotientKernelBaseChange`: `g^*(\ker q) ≅ \ker q'`, and
* `Stacks.Divisors.inverseQuotientBaseChange`: `g^*(L^{⊗ -1}) ≅ (L')^{⊗ -1}`,

taken after Tag 01CD's identification of the pullback of a tensor product with the tensor
product of the pullbacks, `Stacks.RingedSpace.comparisonBifunctorIso`. So no hypothesis is
added beyond the three the two factors already take, and in particular nothing here is
conditional on the bijection of Tag 0B3V or on any property of `g`.

## Main definitions

* `Stacks.Divisors.conormalSourceBaseChange`: **the comparison
  `g^*((\ker q) ⊗ Q.L^{⊗ -1}) ≅ (\ker q') ⊗ Q'.L^{⊗ -1}`**, for every morphism of schemes and
  every pair of invertible quotients identified by `hE`, `hL` and the compatibility `hq`.

## Main results

* `Stacks.Divisors.conormalSourceBaseChange_hom`: its forward map, named, as the composite of
  the Tag 01CD comparison with the tensor product of the two factors. The composite is given a
  name here because decomposing an `Iso.trans` of these two factors downstream is expensive,
  whereas rewriting with this equation is not.

## Implementation notes

**Both factors are used at their unconditional spellings.**
`Stacks.Divisors.quotientKernelBaseChange` is the kernel comparison with its monomorphism
hypothesis already discharged, and it is packaged as a subtype carrying the compatibility with
`kernel.ι`; only its first component is needed to build the comparison, the compatibility being
what a consumer of the comparison needs. `Stacks.Divisors.inverseQuotientBaseChange` is the
inverse-line comparison with its Tag 01CD pairing hypothesis already discharged, and
`Stacks.Divisors.inverseQuotientBaseChange_evaluation` is its normalization, so the factor used
here is pinned rather than merely existing.

**The invertibility instances are introduced by `letI` in the type.** `InvertibleQuotient`
records the invertibility of its line as a field rather than as an instance, and
`Stacks.SheafOfModules.Invertible.tensorPower` takes it as an instance argument; the two are
crossed at the statement exactly as in `Stacks.Divisors.inverseQuotientBaseChange`.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Invertible

universe u

namespace Stacks.Divisors

variable {X X' : Scheme.{u}} (g : X' ⟶ X)

/-- **Tag 01CD at the conormal source**: the pullback of `(\ker q) ⊗ L^{⊗ -1}` is the tensor
product of the pullbacks. This is the first of the two factors of
`Stacks.Divisors.conormalSourceBaseChange`, named and given a declared type so that the
composite can be decomposed without unfolding an `Iso.trans`. -/
noncomputable def conormalSourcePullbackTensor
    (E : X.Modules) (Q : InvertibleQuotient X E) :
    (Scheme.Modules.pullback g).obj
        (letI := Q.invertible
         (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
              (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩).obj
            (kernel Q.q)).obj
            (tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1)))) ≅
      (letI := Q.invertible
       (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X'.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X'.presheaf)
            (forget₂ CommRingCat RingCat) (X'.ringCatSheaf.2)⟩).obj
          ((Scheme.Modules.pullback g).obj (kernel Q.q))).obj
          ((Scheme.Modules.pullback g).obj
            (tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1))))) :=
  letI := Q.invertible
  (Stacks.RingedSpace.comparisonBifunctorIso g.toLRSHom.toShHom).app
    (kernel Q.q, tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1))

/-- **The tensor product of Tag 0B3V's two base-change comparisons**: the kernel
comparison `Stacks.Divisors.quotientKernelBaseChange` on the left factor and the inverse-line
comparison `Stacks.Divisors.inverseQuotientBaseChange` on the right. This is the second of the
two factors of `Stacks.Divisors.conormalSourceBaseChange`. -/
noncomputable def conormalSourceFactors
    (E : X.Modules) (E' : X'.Modules)
    (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
    (Q : InvertibleQuotient X E) (Q' : InvertibleQuotient X' E')
    (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L)
    (hq : Q'.q ≫ hL.hom = hE.hom ≫ (Scheme.Modules.pullback g).map Q.q) :
    (letI := Q.invertible
     (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X'.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X'.presheaf)
          (forget₂ CommRingCat RingCat) (X'.ringCatSheaf.2)⟩).obj
        ((Scheme.Modules.pullback g).obj (kernel Q.q))).obj
        ((Scheme.Modules.pullback g).obj
          (tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1))))) ≅
      (letI := Q'.invertible
       (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X'.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X'.presheaf)
            (forget₂ CommRingCat RingCat) (X'.ringCatSheaf.2)⟩).obj
          (kernel Q'.q)).obj
          (tensorPower X'.presheaf X'.ringCatSheaf.2 Q'.L (-1)))) :=
  letI := Q.invertible
  letI := Q'.invertible
  tensorProductIso X'.presheaf X'.ringCatSheaf.2
    (quotientKernelBaseChange g E E' hE Q Q' hL hq).1
    (inverseQuotientBaseChange g E E' Q Q' hL)

/-- **Tag 0B3V's base-change comparison of the conormal source `(\ker q) ⊗ L^{⊗ -1}`**, with no
hypothesis beyond the three identifications its two factors take: the Tag 01CD comparison of
the pullback of a tensor product, followed by the tensor product of
`Stacks.Divisors.quotientKernelBaseChange` with
`Stacks.Divisors.inverseQuotientBaseChange`. -/
noncomputable def conormalSourceBaseChange
    (E : X.Modules) (E' : X'.Modules)
    (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
    (Q : InvertibleQuotient X E) (Q' : InvertibleQuotient X' E')
    (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L)
    (hq : Q'.q ≫ hL.hom = hE.hom ≫ (Scheme.Modules.pullback g).map Q.q) :
    (Scheme.Modules.pullback g).obj
        (letI := Q.invertible
         (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
              (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩).obj
            (kernel Q.q)).obj
            (tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1)))) ≅
      (letI := Q'.invertible
       (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X'.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X'.presheaf)
            (forget₂ CommRingCat RingCat) (X'.ringCatSheaf.2)⟩).obj
          (kernel Q'.q)).obj
          (tensorPower X'.presheaf X'.ringCatSheaf.2 Q'.L (-1)))) :=
  conormalSourcePullbackTensor g E Q ≪≫ conormalSourceFactors g E E' hE Q Q' hL hq

/-- The forward map of `Stacks.Divisors.conormalSourceBaseChange`, named: the Tag 01CD
comparison followed by the tensor product of the two base-change comparisons. -/
theorem conormalSourceBaseChange_hom
    (E : X.Modules) (E' : X'.Modules)
    (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
    (Q : InvertibleQuotient X E) (Q' : InvertibleQuotient X' E')
    (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L)
    (hq : Q'.q ≫ hL.hom = hE.hom ≫ (Scheme.Modules.pullback g).map Q.q) :
    (conormalSourceBaseChange g E E' hE Q Q' hL hq).hom =
      (conormalSourcePullbackTensor g E Q).hom ≫
        (conormalSourceFactors g E E' hE Q Q' hL hq).hom := rfl

/-- The inverse of `Stacks.Divisors.conormalSourceBaseChange`, named. -/
theorem conormalSourceBaseChange_inv
    (E : X.Modules) (E' : X'.Modules)
    (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
    (Q : InvertibleQuotient X E) (Q' : InvertibleQuotient X' E')
    (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L)
    (hq : Q'.q ≫ hL.hom = hE.hom ≫ (Scheme.Modules.pullback g).map Q.q) :
    (conormalSourceBaseChange g E E' hE Q Q' hL hq).inv =
      (conormalSourceFactors g E E' hE Q Q' hL hq).inv ≫
        (conormalSourcePullbackTensor g E Q).inv := rfl

end Stacks.Divisors

end
