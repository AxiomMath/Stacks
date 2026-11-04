module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedSheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedTensorProductComposition

/-!
# The derived internal hom out of a tensor product of bimodules

Let `(C, O)` be a ringed site, let `𝒜`, `𝒜'` and `𝒜''` be sheaves of differential graded
`O`-algebras, let `𝒩` be a differential graded `(𝒜, 𝒜')`-bimodule and `𝒩'` a differential graded
`(𝒜', 𝒜'')`-bimodule. If the canonical map `𝒩 ⊗^𝐋_{𝒜'} 𝒩' ⟶ 𝒩 ⊗_{𝒜'} 𝒩'` of `D(𝒜'', d)` is a
quasi-isomorphism, then

`RSheafHom_{𝒜''}(𝒩 ⊗_{𝒜'} 𝒩', -) = RSheafHom_{𝒜'}(𝒩, RSheafHom_{𝒜''}(𝒩', -))`

as functors `D(𝒜'', d) ⥤ D(𝒜, d)`; this is
[Stacks, Tag 0FTV](https://stacks.math.columbia.edu/tag/0FTV).

## Main results

* `SheafOfModules.DifferentialGradedModule.derivedSheafHomTensorBimoduleIso`: **Tag 0FTV.**

## Implementation notes

The proof is the source's: under the hypothesis the composite of the two derived tensor products
is the derived tensor product with `𝒩 ⊗_{𝒜'} 𝒩'` (Tag 0FTL,
`derivedTensorProductCompIso`), each derived internal hom is right adjoint to the corresponding
derived tensor product (Tag 0FTQ, `derivedTensorProductSheafHomAdjunction`), a composite of
adjunctions is an adjunction, and right adjoints are unique. The equality of functors of the
source is read as the isomorphism this produces. The hypothesis is the source's, stated about the
comparison map `derivedTensorProductCounit` of the derived tensor product `- ⊗^𝐋_{𝒜'} 𝒩'` at `𝒩`
read as a right differential graded `𝒜'`-module.

The sites, the algebras, the bimodules and the modules are taken in one universe, which is where
the derived categories `D(𝒜, d)` are localizations with a calculus of fractions and where the
relative tensor product is constructed.

## References

* [Stacks Project, Tag 0FTV](https://stacks.math.columbia.edu/tag/0FTV)
* [Stacks Project, Tag 0FTL](https://stacks.math.columbia.edu/tag/0FTL)
* [Stacks Project, Tag 0FTQ](https://stacks.math.columbia.edu/tag/0FTQ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A A' A'' : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  (N : DifferentialGradedBimodule.{u, u, u} A A') (N' : DifferentialGradedBimodule.{u, u, u} A' A'')

/-- **Stacks 0FTV**: let `(C, O)` be a ringed site, let `𝒜`, `𝒜'`, `𝒜''` be sheaves of
differential graded `O`-algebras, let `𝒩` be a differential graded `(𝒜, 𝒜')`-bimodule and `𝒩'` a
differential graded `(𝒜', 𝒜'')`-bimodule, and assume that the canonical map
`𝒩 ⊗^𝐋_{𝒜'} 𝒩' ⟶ 𝒩 ⊗_{𝒜'} 𝒩'` of `D(𝒜'', d)` is a quasi-isomorphism, `𝒩` being read as a right
differential graded `𝒜'`-module. Then

`RSheafHom_{𝒜''}(𝒩 ⊗_{𝒜'} 𝒩', -) ≅ RSheafHom_{𝒜'}(𝒩, RSheafHom_{𝒜''}(𝒩', -))`

as functors `D(𝒜'', d) ⥤ D(𝒜, d)`. Both are right adjoint to `- ⊗^𝐋_𝒜 (𝒩 ⊗_{𝒜'} 𝒩')`: the first
by Tag 0FTQ, the second as the composite of the adjunctions of Tag 0FTQ for `𝒩` and `𝒩'`,
transported along the isomorphism `(- ⊗^𝐋_𝒜 𝒩) ⊗^𝐋_{𝒜'} 𝒩' ≅ - ⊗^𝐋_𝒜 (𝒩 ⊗_{𝒜'} 𝒩')` of
Tag 0FTL. -/
@[stacks 0FTV]
def derivedSheafHomTensorBimoduleIso
    (hN : IsIso ((derivedTensorProductCounit N').app
      ((HomotopyCategory.quotient A').obj N.toRightModule))) :
    derivedSheafHom (DifferentialGradedBimodule.tensorBimodule N N') ≅
      derivedSheafHom N' ⋙ derivedSheafHom N :=
  Adjunction.rightAdjointUniq
    (derivedTensorProductSheafHomAdjunction (DifferentialGradedBimodule.tensorBimodule N N'))
    (((derivedTensorProductSheafHomAdjunction N).comp
      (derivedTensorProductSheafHomAdjunction N')).ofNatIsoLeft
        (derivedTensorProductCompIso N N' hN))

end SheafOfModules.DifferentialGradedModule

end
