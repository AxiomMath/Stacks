module

public import StacksFrontier.AlgebraicGeometry.ConormalComparison.IdealSheafComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The conormal sheaf of a closed subscheme is the pullback of its ideal sheaf

For an immersion `i : Z ⟶ X`, the conormal sheaf of `i` is the module pullback along `i` of the
ideal sheaf of `i`. For the closed subscheme `D` cut out by an ideal sheaf `ℐ_D`, this identifies
the conormal sheaf of `D ⟶ X` with the restriction `𝒪_X(-D)|_D` of `ℐ_D` to `D`.

## Main definitions

* `Stacks.CartierConormal.conormalSheafIsoPullbackSelf`: for an immersion `i : Z ⟶ X`, the
  conormal sheaf of `i` is isomorphic to the module pullback along `i` of the ideal sheaf of `i`.
* `Stacks.CartierConormal.conormalSheafIsoNegativeTwist`: for an ideal sheaf datum `D`, the
  conormal sheaf of the closed immersion `D.subschemeι` is isomorphic to the pullback along
  `D.subschemeι` of its ideal sheaf.

## Implementation notes

The conormal sheaf is defined through the canonical factorization
`i.liftCoborder ≫ i.coborderRange.ι = i`, whose second factor is an open immersion, as
`conormalSheaf i = (i.liftCoborder)^* ℐ(i.liftCoborder)`. The isomorphism is
`Stacks.Conormal.pullbackIdealSheafIsoOfCompEq` applied to this factorization, reversed.

## References

* [Stacks, Tag 0B3P](https://stacks.math.columbia.edu/tag/0B3P)
* [Stacks, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.CartierConormal

/-- The conormal sheaf of an immersion `i : Z ⟶ X` is the module pullback along `i` of the ideal
sheaf of `i`: `conormalSheaf i ≅ i^* ℐ(i)`. -/
noncomputable def conormalSheafIsoPullbackSelf {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] :
    Stacks.Conormal.conormalSheaf i ≅
      (modulePullback i.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom) :=
  (Stacks.Conormal.pullbackIdealSheafIsoOfCompEq i.liftCoborder i.coborderRange.ι i
    i.liftCoborder_ι).symm

/-- For an ideal sheaf datum `D` on a scheme `X`, the conormal sheaf of the closed immersion
`D.subschemeι` is the restriction to the subscheme of the ideal sheaf `ℐ_D`, that is, of
`𝒪_X(-D)`. -/
@[stacks 0B3P "conormal sheaf", ega "II 8.9.4" "partial"]
noncomputable def conormalSheafIsoNegativeTwist {X : Scheme.{u}} (D : X.IdealSheafData) :
    Stacks.Conormal.conormalSheaf D.subschemeι ≅
      (modulePullback D.subschemeι.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf D.subschemeι.toLRSHom.toShHom) :=
  conormalSheafIsoPullbackSelf D.subschemeι

end Stacks.CartierConormal

end
