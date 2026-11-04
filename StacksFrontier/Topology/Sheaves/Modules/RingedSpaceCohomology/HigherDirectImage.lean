module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.LongExactSequence
import StacksCore.Tactic.StacksAttribute

/-!
# Higher direct images of modules on a ringed space are computed by injective resolutions

Let `f : (X, 𝒪_X) → (Y, 𝒪_Y)` be a morphism of ringed spaces. The `i`-th higher direct image
`R^i f_* : Mod(𝒪_X) ⥤ Mod(𝒪_Y)` is the `i`-th right derived functor of the direct image
`f_*`; it is `Stacks.Cohomology.RelativeMayerVietoris.higherDirectImage`. If `ℱ → ℐ^•` is an
injective resolution of an `𝒪_X`-module `ℱ`, then `R^i f_* ℱ = H^i(f_* ℐ^•)`.

## Main results

* `Stacks.RingedSpace.higherDirectImageIso`: for any injective resolution `ℐ^•` of `ℱ`,
  `R^i f_* ℱ ≅ H^i(f_* ℐ^•)`.

## Implementation notes

The right derived functors are Mathlib's `CategoryTheory.Functor.rightDerived`, which computes
them from a chosen injective resolution of each object; the isomorphism is the comparison of
that chosen resolution with the given one.

## References

* [Stacks Project, Tag 0715](https://stacks.math.columbia.edu/tag/0715)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace Stacks.RingedSpace

/-- **Higher direct images are computed by any injective resolution**: if `ℱ → ℐ^•` is an
injective resolution of an `𝒪_X`-module `ℱ`, then `R^i f_* ℱ ≅ H^i(f_* ℐ^•)`. -/
@[stacks 0715 "R^i f_* F = H^i(f_* I)"]
noncomputable def higherDirectImageIso {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)
    {F : SheafOfModules (structureSheafRing X)} (I : InjectiveResolution F) (i : ℕ) :
    (Stacks.Cohomology.RelativeMayerVietoris.higherDirectImage f i).obj F ≅
      (HomologicalComplex.homologyFunctor (SheafOfModules (structureSheafRing Y)) _ i).obj
        (((modulePushforward f).mapHomologicalComplex _).obj I.cocomplex) :=
  I.isoRightDerivedObj (modulePushforward f) i

end Stacks.RingedSpace
