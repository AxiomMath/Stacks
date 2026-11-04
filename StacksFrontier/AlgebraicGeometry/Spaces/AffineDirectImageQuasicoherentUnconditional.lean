module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitComp
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffinePushforwardQuasicoherent

/-!
# The direct image along an affine morphism of algebraic spaces is quasi-coherent

`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isAffineHom` reduces the
first assertion of Stacks 07U8 to the case of a target represented by a scheme of the site,
which it carries as the hypothesis
`AlgebraicGeometry.Space.SchemeTargetAffinePushforwardQuasicoherent`.  That hypothesis is
discharged by `AlgebraicGeometry.Space.schemeTargetAffinePushforwardQuasicoherent` in
`StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentUnconditional`, so the
assertion holds with nothing carried.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional`:
  **the first assertion of Stacks 07U8**, an alias of
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_isAffineHom`.  For an affine
  morphism `f : X ⟶ Y` of algebraic spaces over `S` and a quasi-coherent `𝒪_X`-module `F`, the
  direct image `f_*F` is quasi-coherent.

## References

* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Space

/-- **Stacks 07U8, the quasi-coherence of the direct image.**  Let `f : X ⟶ Y` be an affine
morphism of algebraic spaces over `S` and let `F` be a quasi-coherent `𝒪_X`-module.  Then the
direct image `f_*F` is quasi-coherent.

This is `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_isAffineHom`. -/
alias isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional :=
  AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_isAffineHom

end AlgebraicGeometry.Space

end
