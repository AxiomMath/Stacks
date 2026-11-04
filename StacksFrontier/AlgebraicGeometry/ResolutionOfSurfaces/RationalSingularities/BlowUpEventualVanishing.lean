module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerCohomologySequence
public import StacksFrontier.AlgebraicGeometry.AmpleTwistAcyclicity.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeVanishing

/-!
# Eventual vanishing of `H¹(X, ω_X(n))` on the blowup of a local ring

Let `(A, 𝔪)` be a Noetherian local ring, let `X` be the blowup of `Spec(A)` in `𝔪` and let `ω_X`
be a dualizing module on `X`. This file proves

`H¹(X, ω_X(n)) = 0` for all `n` large enough,

which is the hypothesis `heventual` of
`AlgebraicGeometry.BlowUpDualizing.isZero_firstCohomology_dualizingTwist`, the descent step of
clause (2) of [Stacks, Tag 0B64]. Nothing else is assumed: the local ring is Noetherian and
`ω_X` carries `Stacks.Duality.IsDualizingModule`.

## Main results

* `AlgebraicGeometry.BlowUpDualizing.exists_isZero_firstCohomology_schemeTwist`: the vanishing
  itself.
* `AlgebraicGeometry.BlowUpDualizing.isFiniteType_centre`: the centre of the blowup is an ideal
  sheaf of finite type, the hypothesis under which `𝒪_X(1)` is relatively ample.
* `AlgebraicGeometry.BlowUpDualizing.schemeTwistNatIso`: `ℱ(n) ≅ ℱ ⊗ 𝒪_X(1)^{⊗ n}` for `n ≥ 0`,
  the twists of this chapter rewritten as the tensor powers [Stacks, Tag 02O1] speaks about.

## The argument

The relative statement is [Stacks, Tag 02O1], formalized with no carried hypothesis as
`Stacks.AlgebraicGeometry.AmpleTwistAcyclicity`
`.exists_isZero_rightDerivedPlus_pushforward_tensorPowModule`: for `f : X ⟶ S` proper with `S`
Noetherian, `ℱ` coherent and `ℒ` invertible and relatively ample, one bound `n₀` makes
`Rᵖf_*(ℱ ⊗ ℒ^{⊗ n})` vanish for all `n ≥ n₀` and all `p > 0`. Its three inputs here are:

* **The morphism.** `b : X ⟶ Spec(A)` is `AlgebraicGeometry.blowUpToBase`, proper by
  `AlgebraicGeometry.isProper_blowUpToBase` because `Spec(A)` is locally Noetherian, and
  `Spec(A)` is Noetherian because `A` is.
* **The module.** `ω_X` is coherent: that is the first half of `Stacks.Duality.IsDualizingModule`,
  the same half `AlgebraicGeometry.BlowUpDualizing.isQuasicoherent_curveTwist_pullback` uses.
* **The invertible sheaf.** `𝒪_X(1)` is `AlgebraicGeometry.blowUpTwist` of the blowup
  (`AlgebraicGeometry.BlowUpDualizing.twistSheafNatIso`), invertible by
  `AlgebraicGeometry.isInvertibleModule_blowUpTwist` and relatively ample for `b` by
  `AlgebraicGeometry.isRelativelyAmple_blowUpTwist`, whose hypothesis that the centre is of
  finite type is `isFiniteType_centre` below: on a locally Noetherian scheme the ideal of a
  quasi-coherent ideal sheaf on an affine open is an ideal of a Noetherian ring.

What remains is the passage from the higher direct image to the cohomology of this chapter, which
is the affine-base comparison [Stacks, Tag 01XK] used to *reflect* a zero object. That direction
is formalized as `Stacks.AlgebraicGeometry.TopDegreeBaseChange`
`.isZero_cohomology_of_isZero_rightDerivedPlus_pushforward` — for a quasi-compact
quasi-separated morphism onto an affine base and a quasi-coherent module, the vanishing of
`Rᵖb_*ℱ` forces the vanishing of `Hᵖ(X, ℱ)`. The base `Spec(A)` is affine and
`b` is proper, hence quasi-compact and quasi-separated; the twist `ω_X(n)` is quasi-coherent by
`Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.isQuasicoherent_tensorPowTwist`.

Both indexings of the right derived functors occur: [Stacks, Tag 01XK] and [Stacks, Tag 02O1] are
stated for the `ℤ`-indexed `CategoryTheory.Functor.rightDerivedPlus`, while
`Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor` has Mathlib's
`ℕ`-indexed `CategoryTheory.Functor.rightDerived` for its components. The crossing is
`Stacks.DerivedIndexing.isZero_rightDerived_obj_iff`.

## References

* [Stacks Project, Tag 0B64](https://stacks.math.columbia.edu/tag/0B64)
* [Stacks Project, Tag 02O1](https://stacks.math.columbia.edu/tag/02O1)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence
open Stacks.Cohomology.FormalFunctions (cohomologyDeltaFunctor)
open Stacks.Cohomology.AffineBase (moduleGlobalSections)
open Stacks.AlgebraicGeometry.AmpleTwistAcyclicity
  (exists_isZero_rightDerivedPlus_pushforward_tensorPowModule)
open Stacks.AlgebraicGeometry.TopDegreeBaseChange
  (isZero_cohomology_of_isZero_rightDerivedPlus_pushforward)

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.BlowUpDualizing

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- **The twists of the restriction of a coherent module to the exceptional curve are
quasi-coherent.** The restriction is coherent by [Stacks, Tag 0EBF]
(`AlgebraicGeometry.isCoherent_pullback`), hence quasi-coherent by [Stacks, Tag 01BW]; the
twisting sheaf is quasi-coherent because it is invertible; and the tensor product of two
quasi-coherent modules is quasi-coherent by [Stacks, Tag 01CE]. -/
theorem isQuasicoherent_curveTwist_pullback [IsNoetherianRing A]
    (ωX : (blowUpScheme A).Modules) (hωX : ωX.IsCoherent) (n : ℤ) :
    (curveTwist A ((Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX)
      n).IsQuasicoherent :=
  let : IsLocallyNoetherian (exceptionalCurve A) := isLocallyNoetherian_exceptionalCurve A
  let := hωX
  let : ((Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX).IsCoherent :=
    isCoherent_pullback (exceptionalImmersion A) ωX
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent (exceptionalCurve A).toRingedSpace _ _
    (_root_.isQuasicoherent_of_isCoherent
      ((Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX))
    (Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule (curveTwistNegOne A) (-n))

/-- **The centre of the blowup is an ideal sheaf of finite type.** `Spec(A)` is locally
Noetherian, so the ideal cut out on an affine open is an ideal of a Noetherian ring, hence
finitely generated. This is the hypothesis of
`AlgebraicGeometry.isRelativelyAmple_blowUpTwist`. -/
theorem isFiniteType_centre [IsNoetherianRing A] : (centre A).IsFiniteType := fun U =>
  have : IsNoetherianRing Γ(Spec (.of A), U.1) :=
    IsLocallyNoetherian.component_noetherian U
  Ideal.fg_of_isNoetherianRing _

/-- `ℱ(n) ≅ ℱ ⊗ 𝒪_X(1)^{⊗ n}` for `n ≥ 0`: the twist of this chapter, written with the `n`-th
tensor power of `AlgebraicGeometry.blowUpTwist`, which is the shape [Stacks, Tag 02O1] is stated
in. This is `AlgebraicGeometry.BlowUpDualizing.twistSheafNatIso` tensored with `ℱ`. -/
def schemeTwistNatIso (F : (blowUpScheme A).Modules) (n : ℕ) :
    schemeTwist A F (n : ℤ) ≅
      Stacks.RelativeVeryAmple.tensorModules (blowUpScheme A) F
        (tensorPowModule (blowUpScheme A) (blowUpTwist (centre A) 1) (n : ℤ)) :=
  tensorModulesMapIso (blowUpScheme A) (Iso.refl F) (twistSheafNatIso A n)

/-- **`H¹(X, ω_X(n)) = 0` for all large `n`**, the hypothesis `heventual` of
`AlgebraicGeometry.BlowUpDualizing.isZero_firstCohomology_dualizingTwist`.

[Stacks, Tag 02O1] applied to the proper morphism `X ⟶ Spec(A)`, the coherent module `ω_X` and
the relatively ample invertible module `𝒪_X(1)` gives one bound above which every higher direct
image `Rᵖb_*(ω_X(n))` vanishes; the affine-base comparison [Stacks, Tag 01XK], read in the
direction that reflects a zero object, turns the vanishing in degree `1` into the vanishing of
`H¹(X, ω_X(n))`. -/
theorem exists_isZero_firstCohomology_schemeTwist [IsNoetherianRing A]
    (ωX : (blowUpScheme A).Modules)
    (hωX : letI : IsLocallyNoetherian (blowUpScheme A) := isLocallyNoetherian_blowUpScheme A
      Stacks.Duality.IsDualizingModule ωX) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      IsZero (((cohomologyDeltaFunctor (blowUpScheme A)).functor 1).obj
        (schemeTwist A ωX n)) := by
  let : IsLocallyNoetherian (blowUpScheme A) := isLocallyNoetherian_blowUpScheme A
  have : ωX.IsCoherent := hωX.1
  obtain ⟨n₀, hn₀⟩ := exists_isZero_rightDerivedPlus_pushforward_tensorPowModule
    (blowUpToBase (centre A)) ωX (blowUpTwist (centre A) 1)
    (isRelativelyAmple_blowUpTwist (centre A) (isFiniteType_centre A))
  refine ⟨n₀, fun n hn => ?_⟩
  have : (schemeTwist A ωX (n : ℤ)).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.isQuasicoherent_tensorPowTwist
      ωX (twistNegOne A) (-(n : ℤ))
  have hpush : IsZero (((Scheme.Modules.pushforward (blowUpToBase (centre A))).rightDerivedPlus
      ((1 : ℕ) : ℤ)).obj (schemeTwist A ωX (n : ℤ))) :=
    IsZero.of_iso (hn₀ n 1 hn Nat.one_pos)
      (((Scheme.Modules.pushforward (blowUpToBase (centre A))).rightDerivedPlus
        ((1 : ℕ) : ℤ)).mapIso (schemeTwistNatIso A ωX n))
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
      (moduleGlobalSections (blowUpScheme A)) 1 _).mpr
    (isZero_cohomology_of_isZero_rightDerivedPlus_pushforward (blowUpToBase (centre A))
      ((1 : ℕ) : ℤ) (schemeTwist A ωX (n : ℤ)) hpush)

end AlgebraicGeometry.BlowUpDualizing

end
