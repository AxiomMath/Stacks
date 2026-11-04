module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeTorAmplitudeAffine
import StacksCore.Tactic.StacksAttribute

/-!
# Tor amplitude on a ringed space is a stalkwise condition

Let `(X, 𝒪_X)` be a ringed space, `E` an object of `D(𝒪_X)` and `a, b` integers. Then `E` has
Tor amplitude in `[a, b]` if and only if, for every point `x` of `X`, the stalk `E_x` has Tor
amplitude in `[a, b]` as an object of `D(𝒪_{X, x})`. On the left Tor amplitude is the
definition of Stacks 08CG, read against the derived tensor product `- ⊗^L_{𝒪_X} -` of
Stacks 06YU; on the right it is the definition of Stacks 0652 over the commutative ring
`𝒪_{X, x}`, read against the derived tensor product of `𝒪_{X, x}`-modules of Stacks 0BYI.

The proof is the source's: taking stalks is exact and commutes with derived tensor products
(the derived form of Stacks 01CB), and a sheaf of modules vanishes exactly when all its stalks
do (Stacks 01AG).

Two consequences are recorded, in the form in which they are used to verify finiteness of Tor
dimension. An object has finite Tor dimension exactly when its stalks have Tor amplitude in one
interval independent of the point; and on a quasi-compact ringed space an object locally of finite
Tor dimension has finite Tor dimension, which is then again a uniform stalkwise bound.

## Main results

* `Stacks.Cohomology.TorAmplitude.hasTorAmplitude_iff_forall_hasTorAmplitudeCanonical_stalk`:
  **Stacks 09U9**.
* `Stacks.Cohomology.TorAmplitude.hasFiniteTorDimension_iff_exists_forall_stalk`: finite Tor
  dimension is a stalkwise bound uniform in the point.
* `Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_iff_exists_forall_stalk`: on a
  quasi-compact ringed space, locally finite Tor dimension is a uniform stalkwise bound.

## Implementation notes

The stalk ring `𝒪_{X, x}` is spelled as the stalk of the structure presheaf with commutativity
forgotten, `X.presheaf ⋙ forget₂ CommRingCat RingCat`, which is the ring over which the stalk
functor of `𝒪_X`-modules takes values; its commutative ring structure is
`StacksDraft.StalkTensor.commRing_stalk`, transported from the stalk of commutative rings.

The source assumes `a ≤ b`. The equivalence holds for all integers `a` and `b` (for `b < a` both
sides say that the object is zero after tensoring with every module), so that hypothesis is not
taken.

The derived categories of the stalk rings are the standard ones, as for every statement of
Stacks 0652 at the canonical derived tensor product; the derived category of `𝒪_X`-modules is an
arbitrary model, except in the quasi-compact statement, whose input
`locallyHasFiniteTorDimension_iff_hasFiniteTorDimension` (in the namespace
`AlgebraicGeometry.AffineRelativeTorAmplitude`) is stated at the standard model.

## References

* [Stacks Project, Lemma 20.48.5 (Tag 09U9)](https://stacks.math.columbia.edu/tag/09U9)
* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 0652](https://stacks.math.columbia.edu/tag/0652)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u d

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Cohomology.TorAmplitude

open _root_.StrictlyPerfect

section Stalkwise

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u, u} X)]

/-- **Stacks 09U9.** Let `(X, 𝒪_X)` be a ringed space and `E` an object of `D(𝒪_X)`. Then `E`
has Tor amplitude in `[a, b]` if and only if, for every point `x` of `X`, the stalk `E_x` has
Tor amplitude in `[a, b]` as an object of `D(𝒪_{X, x})`.

The left side is the Tor amplitude of Stacks 08CG for the derived tensor product of Stacks 06YU,
`Stacks.Cohomology.TorAmplitude.HasTorAmplitude`; the right side is the Tor amplitude of
Stacks 0652 over the ring `𝒪_{X, x}` for its derived tensor product of Stacks 0BYI,
`StacksDraft.TorAmplitude.HasTorAmplitudeCanonical`. The stalk `E_x` is the image of `E` under
the exact stalk functor `Mod(𝒪_X) ⥤ Mod(𝒪_{X, x})`. -/
@[stacks 09U9, sga "4 XVII 4.2.8" "(iii), special case"]
theorem hasTorAmplitude_iff_forall_hasTorAmplitudeCanonical_stalk
    (E : DerivedCategory (OXMod.{u, u} X)) (a b : ℤ) :
    HasTorAmplitude X E a b ↔
      ∀ x : X.carrier, StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
        (TopCat.Presheaf.stalk (C := RingCat.{u}) (X.presheaf ⋙ forget₂ CommRingCat RingCat) x)
        ((SheafOfModules.stalkFunctor (structureSheafOfRings X) x).mapDerivedCategory.obj E)
        a b :=
  (hasTorAmplitude_iff_forall_stalk X E a b).trans <| forall_congr' fun x =>
    StacksDraft.TorAmplitude.hasTorAmplitudeIn_canonicalDerivedTensorProduct_iff
      (TopCat.Presheaf.stalk (C := RingCat.{u}) (X.presheaf ⋙ forget₂ CommRingCat RingCat) x) _ a b

/-- **Finite Tor dimension is a uniform stalkwise bound.** An object `E` of `D(𝒪_X)` has finite
Tor dimension if and only if there is one interval `[a, b]` such that every stalk `E_x` has Tor
amplitude in `[a, b]` over `𝒪_{X, x}`. -/
@[sga "4 XVII 4.2.8" "(iii)"]
theorem hasFiniteTorDimension_iff_exists_forall_stalk (E : DerivedCategory (OXMod.{u, u} X)) :
    HasFiniteTorDimension X E ↔
      ∃ a b : ℤ, ∀ x : X.carrier, StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
        (TopCat.Presheaf.stalk (C := RingCat.{u}) (X.presheaf ⋙ forget₂ CommRingCat RingCat) x)
        ((SheafOfModules.stalkFunctor (structureSheafOfRings X) x).mapDerivedCategory.obj E)
        a b :=
  exists_congr fun a => exists_congr fun b =>
    hasTorAmplitude_iff_forall_hasTorAmplitudeCanonical_stalk X E a b

end Stalkwise

section Compact

attribute [local instance] restrictModules_preservesFiniteLimits
  restrictModules_preservesFiniteColimits

variable (X : RingedSpace.{u, u})

/-- **On a quasi-compact ringed space, locally finite Tor dimension is a uniform stalkwise
bound.** If `X` is quasi-compact, an object `E` of `D(𝒪_X)` locally has finite Tor dimension if
and only if there is one interval `[a, b]` such that every stalk `E_x` has Tor amplitude in
`[a, b]` over `𝒪_{X, x}`; equivalently, by
`hasFiniteTorDimension_iff_exists_forall_stalk`, `E` has finite Tor dimension. -/
theorem locallyHasFiniteTorDimension_iff_exists_forall_stalk [CompactSpace X.carrier]
    (E : DerivedCategory (OXMod.{u, u} X)) :
    LocallyHasFiniteTorDimension X E ↔
      ∃ a b : ℤ, ∀ x : X.carrier, StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
        (TopCat.Presheaf.stalk (C := RingCat.{u}) (X.presheaf ⋙ forget₂ CommRingCat RingCat) x)
        ((SheafOfModules.stalkFunctor (structureSheafOfRings X) x).mapDerivedCategory.obj E)
        a b :=
  (AffineRelativeTorAmplitude.locallyHasFiniteTorDimension_iff_hasFiniteTorDimension
    E).trans (hasFiniteTorDimension_iff_exists_forall_stalk X E)

end Compact

end Stacks.Cohomology.TorAmplitude

end
