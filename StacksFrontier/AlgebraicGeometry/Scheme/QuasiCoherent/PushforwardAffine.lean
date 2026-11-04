module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Groupoids.FittingIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentLocal
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentQuasicoherent

/-!
# Pushforward of a quasi-coherent module along an affine morphism

Pushforward along an affine morphism of schemes preserves quasi-coherence, and in particular
the direct image `f_* 𝒪_X` of the structure sheaf along an affine morphism is quasi-coherent.
The two quasi-coherence results are restated here from
`StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic` with the quasi-coherence of the module
as an explicit argument, which is the form the consumers of this file apply.

## Main definitions

* `Stacks.Modules.pushforwardRestrictFunctorIso` identifies the restriction to an open `V` of a
  pushforward along `q` with the pushforward along the restricted morphism `q ∣_ V` of the
  restriction to `q ⁻¹ᵁ V`. It is
  `Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso` under this namespace's name
  for it, not a second construction.

## Main results

* `Stacks.Modules.isQuasicoherent_pushforward_of_isAffine`: pushforward between affine schemes
  preserves quasi-coherence.
* `Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom`: pushforward along an affine
  morphism preserves quasi-coherence.
* `Stacks.Modules.isQuasicoherent_pushforwardStructureSheaf`: `f_* 𝒪_X` is quasi-coherent for
  `f` affine.

## Implementation notes

The quasi-coherence assertion of [Stacks, Tag 02KG] is proved, and carries the project tag, at
`Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom`; the
affine case it rests on is
`Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_pushforward_of_isAffine`. The two
results below cite those rather than reproving them. The open-immersion base change
`pushforwardRestrictFunctorIso` cites
`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso` in the same way, so nothing
here is proved twice.

Mathlib has no compatibility of `AlgebraicGeometry.Scheme.Modules.pushforward` with
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, but both functors are instances of
`CategoryTheory.SheafOfModules.pushforward` — the first along `TopologicalSpace.Opens.map` of
the underlying continuous map, the second along `AlgebraicGeometry.Scheme.Hom.opensFunctor` —
so each of the two composites is, by `CategoryTheory.SheafOfModules.pushforwardComp`, *equal*
to a single `SheafOfModules.pushforward`, and the comparison is
`CategoryTheory.SheafOfModules.pushforwardCongr₂` applied to the identification of opens
`AlgebraicGeometry.image_morphismRestrict_preimage`. The two hypotheses of that lemma are a
naturality square in `TopologicalSpace.Opens`, where all homs between fixed objects are equal,
and the compatibility of the two maps on sections of the structure sheaf, which is
`AlgebraicGeometry.morphismRestrict_app`. No `set_option` is needed: the appearances of
`AlgebraicGeometry.Scheme.Hom.appIso` of an open immersion `ι` reduce to the identity by
`AlgebraicGeometry.Scheme.Opens.ι_appIso`, and the resulting equality of ring maps is checked
by `exact`, at default transparency, rather than by `rw`.

That isomorphism is used outside this file, by
`Stacks.Morphisms.pushforwardStructureSheafRestrictIso`, and not by the two results below.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01S5](https://stacks.math.columbia.edu/tag/01S5)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules (restrictFunctor)

universe u

namespace Stacks.Modules

/-- **Restriction of a pushforward to an open of the target.** For a morphism of schemes
`q : P ⟶ Z` and an open `V` of `Z`, restricting `q_* M` to `V` is the same as pushing the
restriction of `M` to `q ⁻¹ᵁ V` forward along the restricted morphism `q ∣_ V`.

This is `Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso` under the name this
namespace uses for it. -/
noncomputable def pushforwardRestrictFunctorIso {P Z : Scheme.{u}} (q : P ⟶ Z) (V : Z.Opens) :
    Scheme.Modules.pushforward q ⋙ restrictFunctor V.ι ≅
      restrictFunctor (q ⁻¹ᵁ V).ι ⋙ Scheme.Modules.pushforward (q ∣_ V) :=
  Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso q V

/-- **Pushforward between affine schemes preserves quasi-coherence.** This is
`Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_pushforward_of_isAffine`, which
takes the quasi-coherence of `M` as an instance rather than as the explicit argument `hM`. -/
theorem isQuasicoherent_pushforward_of_isAffine {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : X.Modules) (hM : M.IsQuasicoherent) :
    ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent :=
  have := hM
  Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_pushforward_of_isAffine f M

/-- **Pushforward along an affine morphism preserves quasi-coherence.** This is the instance
`Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom`, the
quasi-coherence assertion of [Stacks, Tag 02KG], with the quasi-coherence of `M` taken as the
explicit argument `hM` rather than as an instance. -/
theorem isQuasicoherent_pushforward_of_isAffineHom {P Z : Scheme.{u}} (q : P ⟶ Z)
    [IsAffineHom q] (M : P.Modules) (hM : M.IsQuasicoherent) :
    ((Scheme.Modules.pushforward q).obj M).IsQuasicoherent :=
  have := hM
  Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom q M

/-- **The direct image of the structure sheaf along an affine morphism is quasi-coherent.** -/
instance isQuasicoherent_pushforwardStructureSheaf {P Z : Scheme.{u}} (q : P ⟶ Z)
    [IsAffineHom q] : (Stacks.Morphisms.pushforwardStructureSheaf q).IsQuasicoherent :=
  isQuasicoherent_pushforward_of_isAffineHom q _ inferInstance

end Stacks.Modules

end
