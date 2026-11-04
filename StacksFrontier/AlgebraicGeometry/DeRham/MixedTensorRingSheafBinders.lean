module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.MixedDerivedTensorOnARingedSpace
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage

/-!
# The ring sheaves of the mixed tensor product

The identity `F ⊗_{𝒪_X} f^*G ≅ F ⊗_{f^{-1}𝒪_Y} f^{-1}G` is
`Stacks.Cohomology.MixedDerivedTensorOnARingedSpace.spaceUnderivedLinearMixedTensorIso`, stated
over the ring sheaves of the ringed topoi `Stacks.ToposBridge.ringedTopos X` and
`StacksPullbackFactorization.auxTopos (ringedToposSiteHom f)`. Section 0FMK uses the sheaves of
rings `structureSheafRing X` and the structure ring sheaf of the inverse-image ringed space
`Stacks.DeRhamDirectImage.inverseImageBase f`. This file shows that the two pairs are equal,
definitionally.

## Main results

* `Stacks.DeRhamDirectImage.ringedTopos_ringSheaf`: the ring sheaf of the ringed topos presented
  by a ringed space is its structure ring sheaf.
* `Stacks.DeRhamDirectImage.invRing_ringedToposSiteHom`: the inverse image of the structure sheaf
  of the target in the topos factorization of `f` is the structure sheaf of `(X, f^{-1}𝒪_Y)`.
* `Stacks.DeRhamDirectImage.auxTopos_ringedToposSiteHom_ringSheaf`: the ring sheaf of the
  auxiliary ringed topos of a morphism of schemes is the structure ring sheaf of `(X, f^{-1}𝒪_Y)`.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 08DE](https://stacks.math.columbia.edu/tag/08DE)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.Cohomology.MixedDerivedTensorOnARingedSpace

universe u

namespace Stacks.DeRhamDirectImage

/-- The ring sheaf of the ringed topos presented by a ringed space `X` is its structure ring
sheaf: both are the image of `𝒪_X` under `CategoryTheory.sheafCompose` along
`forget₂ CommRingCat RingCat`. -/
theorem ringedTopos_ringSheaf (X : RingedSpace.{u, u}) :
    Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.ToposBridge.ringedTopos X).O =
      structureSheafRing X :=
  rfl

/-- The inverse image of the structure sheaf of the target, as the topos factorization of `f`
presents it, is the structure sheaf of the ringed space `(X, f^{-1}𝒪_Y)`. -/
theorem invRing_ringedToposSiteHom (X S : Scheme.{u}) (f : X ⟶ S) :
    StacksPullbackFactorization.invRing (ringedToposSiteHom f.toLRSHom.toShHom) =
      (inverseImageBase f).sheaf :=
  rfl

/-- The ring sheaf of the auxiliary ringed topos of `f` is the structure ring sheaf of
`(X, f^{-1}𝒪_Y)`, the coefficient ring of `F ⊗_{f^{-1}𝒪_Y} f^{-1}G`. -/
theorem auxTopos_ringedToposSiteHom_ringSheaf (X S : Scheme.{u}) (f : X ⟶ S) :
    Stacks.SheafOfModules.Tensor.ringSheaf
        (StacksPullbackFactorization.auxTopos
          (ringedToposSiteHom f.toLRSHom.toShHom)).O =
      structureSheafRing (inverseImageBase f) :=
  rfl

end Stacks.DeRhamDirectImage

end
