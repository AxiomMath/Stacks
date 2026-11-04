module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleDualEvaluation
public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierAdjunctionModule
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalIdealTwist
import StacksCore.Tactic.StacksAttribute

/-!
# The dualizing sheaf of the exceptional curve of a blowup

Let `(A, 𝔪)` be a Noetherian local ring, let `X` be the blowup of `Spec(A)` in `𝔪`, let
`i : E ⟶ X` be its exceptional divisor and let `𝒪_X(n)` be the `n`-th power of the twisting
sheaf of the blowup. Write `a(-)` for the right adjoint of derived pushforward along `i` of
[Stacks, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76), derived sheaf Hom with exact
support. Clause (1) of [Stacks, Tag 0B64](https://stacks.math.columbia.edu/tag/0B64) asserts

`ω_E = ω_X|_E ⊗ 𝒪_E(-1)`.

**This file proves it**, for `ω_E` the module `H¹(a(ω_X))` — the source obtains the dualizing
sheaf of `E` from that of `X` as `ω_E^• = a(ω_X^•)` (Duality for Schemes, Lemma 0A9X), and with
the normalization `ω_X^• = ω_X[2]`, `ω_E^• = ω_E[1]` of [Stacks, Remark 0B4R] the module `ω_E`
sits in degree one of `a(ω_X)` — and for `ω_X` an arbitrary `𝒪_X`-module, so in particular for
the dualizing module of `X`.

## Main definitions

* `AlgebraicGeometry.BlowUpDualizing.exceptionalDualizingModule`: `ω_E = H¹(a(ω_X))`.

## Main results

* `AlgebraicGeometry.BlowUpDualizing.nonempty_exceptionalDualizingModule_iso_curveTwist`:
  **clause (1) of [Stacks, Tag 0B64]** for the module `ω_E = H¹(a(ω_X))`. The attribute of
  that clause sits on
  `AlgebraicGeometry.BlowUpDualizing.nonempty_dualizingSheafOverField_iso_curveTwist` of
  `…/Duality/ExceptionalDualizingSheafIdentification.lean`, which identifies this module with the
  dualizing sheaf of `E` over `κ` for the normalized `ω_X`.
* `AlgebraicGeometry.BlowUpDualizing.exceptionalIdealTensorTwistNegOneIso`:
  `ℐ_E ⊗ 𝒪_X(-1) ≅ 𝒪_X`.
* `AlgebraicGeometry.BlowUpDualizing.twistNegOneIsoDivisorSheaf`: `𝒪_X(-1) ≅ 𝒪_X(E)`, the
  invertible sheaf of the exceptional divisor.
* `AlgebraicGeometry.BlowUpDualizing.normalSheafIsoCurveTwistSheaf`: `i^* 𝒪_X(E) ≅ 𝒪_E(-1)`,
  the identification of the normal sheaf of `E` inside `X`.

## The proof

The adjunction formula of [Stacks, Tag 0AA4] at the level of modules,
`Stacks.Divisors.nonempty_homologyOne_derivedSheafHomExactSupport_iso`, gives

`H¹(a(ω_X)) ≅ i^* 𝒪_X(E) ⊗ i^* ω_X`

for every effective Cartier divisor and every module, with no hypothesis. What is left is the
normal sheaf of the exceptional divisor. `ℐ_E ≅ 𝒪_X(1)` is part (3) of [Stacks, Tag 02OS] in
degree one (`AlgebraicGeometry.BlowUpDualizing.exceptionalIdealModuleIsoTwistSheaf`), so
`𝒪_X(-1) ⊗ ℐ_E ≅ 𝒪_X` by the addition law for the tensor powers, and a tensor inverse of an
invertible module is its dual ([Stacks, Tag 0B8K],
`Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf`), which identifies `𝒪_X(-1)` with
`𝒪_X(E) = ℐ_E^∨`. Restricting to `E` and using that pullback commutes with tensor powers
(`AlgebraicGeometry.BlowUpDualizing.pullbackTwistSheafIso`) turns `i^* 𝒪_X(E)` into `𝒪_E(-1)`.

**`ω_E` is a construction, not a parameter.** `AlgebraicGeometry.BlowUpDualizing` states clause
(1) with `ω_E` a parameter, and needs the adjunction formula supplied as the datum
`AlgebraicGeometry.BlowUpDualizing.ExceptionalAdjunction`. Defining `ω_E` as `H¹(a(ω_X))`
removes that datum.

## Provenance

The declarations of this file concern clause (1); the further statements (that `ω_E` is a
dualizing module, and the consequences of identifying `ω_E` with the dualizing sheaf of `E` over
`κ`) are not part of this module.

## References

* [Stacks Project, Tag 0B64](https://stacks.math.columbia.edu/tag/0B64)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A9X](https://stacks.math.columbia.edu/tag/0A9X)
* [Stacks Project, Tag 0AA4](https://stacks.math.columbia.edu/tag/0AA4)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.RelativeVeryAmple

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.BlowUpDualizing

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- **`ℐ_E ⊗ 𝒪_X(-1) ≅ 𝒪_X`.** The ideal sheaf of the exceptional divisor is `𝒪_X(1)`, by part
(3) of [Stacks, Tag 02OS] in degree one, and the tensor powers of `𝒪_X(-1)` add. -/
def exceptionalIdealTensorTwistNegOneIso :
    Stacks.RelativeVeryAmple.tensorModules (blowUpScheme A) (exceptionalIdealModule A)
        (twistSheaf A (-1)) ≅
      unitModule (blowUpScheme A) :=
  Stacks.RelativeVeryAmple.tensorModulesMapIso (blowUpScheme A)
      (exceptionalIdealModuleIsoTwistSheaf A) (Iso.refl _) ≪≫
    tensorPowModuleAddIso (blowUpScheme A) (twistNegOne A) (-1) (-(-1)) ≪≫
    Stacks.RelativeVeryAmple.tensorPowModuleCongr (blowUpScheme A) (twistNegOne A)
      (show (-1 : ℤ) + -(-1) = 0 by ring) ≪≫
    tensorPowModuleZeroIso (blowUpScheme A) (twistNegOne A)

/-- **`𝒪_X(-1) ≅ 𝒪_X(E)`.** The inverse of the twisting sheaf of the blowup is the invertible
sheaf `ℐ_E^∨` of the exceptional divisor: it is a tensor inverse of `ℐ_E` by
`AlgebraicGeometry.BlowUpDualizing.exceptionalIdealTensorTwistNegOneIso`, and a tensor inverse
of an invertible module is its dual ([Stacks, Tag 0B8K]). -/
def twistNegOneIsoDivisorSheaf :
    twistSheaf A (-1) ≅ Stacks.Divisors.divisorSheaf (exceptionalIdeal (centre A)) :=
  Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf
    (blowUpScheme A).presheaf
    (structureSheafRing (blowUpScheme A).toRingedSpace).property
    (exceptionalIdealModule A) (twistSheaf A (-1))
    (exceptionalIdealTensorTwistNegOneIso A)

section Noetherian

variable [IsNoetherianRing A]

/-- **The normal sheaf of the exceptional curve is `𝒪_E(-1)`**, `i^* 𝒪_X(E) ≅ 𝒪_E(-1)`: it is
the restriction of `AlgebraicGeometry.BlowUpDualizing.twistNegOneIsoDivisorSheaf`, pullback
commuting with the tensor powers of an invertible module. -/
def normalSheafIsoCurveTwistSheaf :
    (Scheme.Modules.pullback (exceptionalImmersion A)).obj
        (Stacks.Divisors.divisorSheaf (exceptionalIdeal (centre A))) ≅
      curveTwistSheaf A (-1) :=
  (Scheme.Modules.pullback (exceptionalImmersion A)).mapIso
      (twistNegOneIsoDivisorSheaf A).symm ≪≫
    pullbackTwistSheafIso A (-1)

/-- **`ω_E`, the dualizing sheaf of the exceptional curve of the blowup**: the first cohomology
of `a(ω_X)`, for `a(-)` the right adjoint of derived pushforward along `i : E ⟶ X` of
[Stacks, Tag 0A76] and `ω_X` a module on the blowup. Degree one is the degree
[Stacks, Remark 0B4R] selects: that remark normalizes the dualizing complexes of `X` and of `E`
to `ω_X^• = ω_X[2]` and `ω_E^• = ω_E[1]`, so in the source's `ω_E^• = a(ω_X^•)` the module
`ω_E` sits in degree one of `a(ω_X)`. -/
def exceptionalDualizingModule (ωX : (blowUpScheme A).Modules) : (exceptionalCurve A).Modules :=
  (DerivedCategory.homologyFunctor (exceptionalCurve A).Modules 1).obj
    ((Stacks.Divisors.closedQuotient (exceptionalIdeal (centre A))).derivedSheafHomExactSupport.obj
      ((DerivedCategory.singleFunctor (blowUpScheme A).Modules 0).obj ωX))

omit [IsNoetherianRing A] in
/-- **[Stacks, Tag 0B64], clause (1).** The dualizing sheaf of the exceptional curve of the
blowup of a Noetherian local ring in its maximal ideal is `ω_E = ω_X|_E ⊗ 𝒪_E(-1)`, for
`ω_E = H¹(a(ω_X))` and `ω_X` an arbitrary module on the blowup.

The adjunction formula of [Stacks, Tag 0AA4] at the level of modules,
`Stacks.Divisors.nonempty_homologyOne_derivedSheafHomExactSupport_iso`, computes `H¹(a(ω_X))`
as `i^* 𝒪_X(E) ⊗ i^* ω_X`, and
`AlgebraicGeometry.BlowUpDualizing.normalSheafIsoCurveTwistSheaf` identifies `i^* 𝒪_X(E)` with
`𝒪_E(-1)`. -/
theorem nonempty_exceptionalDualizingModule_iso_curveTwist (ωX : (blowUpScheme A).Modules) :
    Nonempty (exceptionalDualizingModule A ωX ≅
      curveTwist A ((Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX) (-1)) := by
  obtain ⟨e⟩ := Stacks.Divisors.nonempty_homologyOne_derivedSheafHomExactSupport_iso
    (exceptionalIdeal (centre A)) ωX
  refine ⟨e ≪≫ Stacks.SheafOfModules.tensorSheafBraiding (exceptionalCurve A).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (exceptionalCurve A)) _ _ ≪≫ ?_⟩
  exact Stacks.RelativeVeryAmple.tensorModulesMapIso (exceptionalCurve A) (Iso.refl _)
    (normalSheafIsoCurveTwistSheaf A)

end Noetherian

end AlgebraicGeometry.BlowUpDualizing

end
