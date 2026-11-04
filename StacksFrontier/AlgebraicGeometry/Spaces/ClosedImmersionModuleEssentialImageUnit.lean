module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward

/-!
# The essential image of the direct image of modules, as a unit-isomorphism condition

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` contained in a big
fppf site `B`. The essential-image clause of the space-level [Stacks, Tag 08KS] asserts that an
`𝒪_X`-module `𝒢` is a direct image along `i` exactly when the ideal `ℐ = ker(i♯)` cutting out `Z`
annihilates it. One inclusion, `essImage i_* ⊆ {𝒢 | ℐ𝒢 = 0}`, is unconditional and proved; the
reverse one is not.

This file records the **exact remaining content of that reverse inclusion**, by converting
membership of the essential image into a condition on the adjunction unit. Because the direct
image is fully faithful (`AlgebraicGeometry.Space.fullyFaithfulModulePushforward`) and is the
right adjoint of the adjunction of Stacks 03LU
(`AlgebraicGeometry.Space.modulePullbackAdjunction`), the counit/unit calculus of a fully
faithful right adjoint applies verbatim:

`(i_*).essImage 𝒢 ↔ IsIso (η_𝒢 : 𝒢 ⟶ i_* i^* 𝒢)`.

That equivalence is unconditional and costs nothing beyond what is already in the library. Combined with
the unconditional inclusion it reduces the whole missing conjunct to the single implication

`ℐ𝒢 = 0 → IsIso (η_𝒢)`,

which is therefore the statement any future proof should target, and the statement against which
the obstruction should be recorded.

## Main results

* `AlgebraicGeometry.Space.essImage_modulePushforward_iff_isIso_modulePullbackAdjunction_unit`:
  for a closed immersion, a module is a direct image exactly when the unit of Stacks 03LU is an
  isomorphism at it. Unconditional.
* `AlgebraicGeometry.Space.annihilatedByKerIdeal_of_isIso_modulePullbackAdjunction_unit`: if the
  unit is an isomorphism at `𝒢` then `ℐ𝒢 = 0`. Unconditional; this is the unconditional inclusion read
  through the previous statement.

## Why no `@[stacks]` attribute is carried here

Neither statement is an assertion of Stacks 08KS. The first is the standard adjunction calculus
of a fully faithful right adjoint, and the second is a restatement of the already-tagged
`AlgebraicGeometry.Space.annihilatedByKerIdeal_of_essImage_modulePushforward` (Stacks 04CJ,
part (3)). Tagging either would claim the essential-image clause, which is **not** proved: the
implication `ℐ𝒢 = 0 → IsIso (η_𝒢)` is open.

## Implementation notes

**Why this sharpens the recorded obstruction.** The obstruction had been recorded against
"Stacks 04E5, part (1) for sheaves of sets", reached through
`MorphismOfTopoi.IsClosedImmersion` (Stacks 08M0) for
`AlgebraicGeometry.Space.smallToposMorphismTypeU` and
`Stacks.Sheaves.PushforwardEssentialImage.essImage_pushforwardModules_iff_of_isClosedImmersion`.
That route is real, but 04E5, part (1) is not the binding half of it. `IsClosedImmersion` of a
morphism of topoi unfolds to `IsEmbedding ∧ IsClosedSubtopos J f_*.essImage`, and the embedding
half — full faithfulness of the small étale direct image — **is already available at the module
universe**, as
`AlgebraicGeometry.Space.fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion`, which is what
`AlgebraicGeometry.Space.fullyFaithfulModulePushforward` consumes. What is missing on that route
is only the closed-subtopos half, namely a subterminal sheaf whose `closedComplement`
(Stacks 08LY) is the essential image — and the subterminal sheaf is available in principle, since
the open complement of a closed subspace is an open subspace
(`AlgebraicGeometry.Space.isOpenSubspace_openComplement`). So the obstruction on that route is
the essential-image/closed-subtopos clause at the universe `u` of the modules, not full
faithfulness.

**The module universe.** Everything here is at `u`, the universe of the schemes, which is where
`AlgebraicGeometry.Space.Modules` and `AlgebraicGeometry.Space.modulePullbackAdjunction` live.
This is why the abelian analogue of the missing clause does not transfer as it stands: the
abelian form is `smallEtalePushforward_essImage_iff_abelian_of_isClosedImmersion`, in the same
namespace, of `StacksFrontier/AlgebraicGeometry/Spaces/ComplexesWithSupport.lean`, and it sits at
coefficient universe `u + 1`, the universe of the objects of the small étale site, one above the
universe the modules live at.

**A second route to the missing implication, which does not pass through Stacks 04E5 at all.**
The unit may instead be tested on stalks at geometric points, which is how the ringed-space form
of the tag is proved. That route is available at the universe `u` of the modules: geometric
points are a conservative family for the small étale site of an algebraic space
(`AlgebraicGeometry.Space.isConservativeFamilyOfPoints_etaleSitePoint`, at `Point.{u}`), and
`Stacks.isIso_of_isIso_sheafModuleFiber` turns that into detection of isomorphisms of
`AlgebraicGeometry.Space.Modules` by their module fibres, the module universe being forced equal
to the point universe. The stalk of the structure map is surjective
(`AlgebraicGeometry.Space.surjective_etaleLocalRingMap_of_isClosedImmersion`), and the algebra
`A/I ⊗_A M ≅ M/IM` with `IM = 0` is Mathlib's `TensorProduct.quotTensorEquivQuotSMul`. What that
route still needs is the module analogue of the two stalk computations for `i_*`: at a point of
the image, where `AlgebraicGeometry.Space.stalkPushforwardIsoOfIsClosedImmersion`
(Stacks 0DK1) is for sheaves of sets at `Type (u + 1)`; and off the image, where the known
vanishing is abelian at `u + 1`
(`AlgebraicGeometry.Space.isZero_stalkFunctor_smallEtaleAbelianPushforward_of_notMem`) over a
support bound, `AlgebraicGeometry.Space.supportOfSheaf_smallEtaleAbelianPushforward_subset`, that
is stated at a free coefficient universe.

**The ringed-space form of Stacks 08KS does not apply.** The library's
`Stacks.Tag08KS.modulePushforward_essImage_iff_kernelIdeal_annihilates` is the complete iff, but
for `AlgebraicGeometry.RingedSpace`, whose modules are sheaves on `Opens X.carrier` of a
topological space. The modules here are sheaves on `AlgebraicGeometry.Space.SmallEtale`, the
category of étale charts. The two are different sites and the two categories of modules are not
identified anywhere in this development; see the module docstring of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforward.lean`, which records the
missing comparison as Descent, Proposition 03DX (2).

## References

* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 08M0](https://stacks.math.columbia.edu/tag/08M0)
* [Stacks Project, Tag 08LY](https://stacks.math.columbia.edu/tag/08LY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS}

/-- **Membership of the essential image of `i_*` is invertibility of the unit.** For a closed
immersion `i : Z ⟶ X` of algebraic spaces, an `𝒪_X`-module `𝒢` lies in the essential image of
the direct image of Stacks 03LU exactly when the unit `η_𝒢 : 𝒢 ⟶ i_* i^* 𝒢` of the adjunction of
Stacks 03LU is an isomorphism.

This is the adjunction calculus of a fully faithful right adjoint
(`CategoryTheory.Adjunction.isIso_unit_app_iff_mem_essImage`) applied to
`AlgebraicGeometry.Space.fullyFaithfulModulePushforward`. It is unconditional, and it is what
reduces the missing reverse inclusion of the essential-image clause of Stacks 08KS to the single
implication `ℐ𝒢 = 0 → IsIso (η_𝒢)`. -/
theorem essImage_modulePushforward_iff_isIso_modulePullbackAdjunction_unit (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (G : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforward B S hS i).essImage G ↔
      IsIso ((modulePullbackAdjunction B S hS i).unit.app G) :=
  have := (fullyFaithfulModulePushforward B S hS i hi).full
  have := (fullyFaithfulModulePushforward B S hS i hi).faithful
  ((modulePullbackAdjunction B S hS i).isIso_unit_app_iff_mem_essImage).symm

/-- **The unconditional inclusion of the essential-image clause, in unit form.** If the unit of the
adjunction of Stacks 03LU is an isomorphism at an `𝒪_X`-module `𝒢`, then the ideal cutting out
the closed subspace annihilates `𝒢`.

This is `AlgebraicGeometry.Space.annihilatedByKerIdeal_of_essImage_modulePushforward`, which
carries the Stacks 04CJ tag for the same content, read through
`AlgebraicGeometry.Space.essImage_modulePushforward_iff_isIso_modulePullbackAdjunction_unit`.
The converse implication is the missing half and is not proved anywhere. -/
theorem annihilatedByKerIdeal_of_isIso_modulePullbackAdjunction_unit (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (G : Modules.{u, u} B S hS X.1 X.2)
    (hG : IsIso ((modulePullbackAdjunction B S hS i).unit.app G)) :
    AnnihilatedByKerIdeal B S hS i G :=
  annihilatedByKerIdeal_of_essImage_modulePushforward B S hS i
    ((essImage_modulePushforward_iff_isIso_modulePullbackAdjunction_unit B S hS i hi G).2 hG)

end AlgebraicGeometry.Space

end
