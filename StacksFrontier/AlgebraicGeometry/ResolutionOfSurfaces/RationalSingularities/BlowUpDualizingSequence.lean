module

public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.AssociatedPointsCompat
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Twist
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequenceTwist
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeSequence
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleAssociatedPoint
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerCohomologySequence
public import StacksFrontier.AlgebraicGeometry.IdealSheafSequence.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.StalkMono
public import StacksFrontier.AlgebraicGeometry.Modules.TensorInvertible
public import StacksFrontier.AlgebraicGeometry.Modules.TensorStalkNaturality
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpEventualVanishing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurveSections
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalIdealTwist
import StacksCore.Tactic.StacksAttribute

/-!
# The restriction sequence of the dualizing module on the blowup

Let `(A, 𝔪)` be a Noetherian local ring, let `X` be the blowup of `Spec(A)` in `𝔪`, let
`i : E ⟶ X` be its exceptional divisor and let `ω_X` be a dualizing module on `X`
([Stacks, Tag 0B4R]). This file proves that the sequence

`0 ⟶ ω_X(1) ⟶ ω_X ⟶ i_*(ω_X|_E) ⟶ 0`

is short exact, in two forms: with its second map left arbitrary, and with that map pinned to
the canonical restriction `ω_X ⟶ i_*(ω_X|_E)`, the unit of `i^* ⊣ i_*`, which is the
sequence the source of [Stacks, Tag 0B64] writes down and the one whose long exact cohomology
sequence lifts global sections off `E`.

## Main results

* `AlgebraicGeometry.BlowUpDualizing.exists_shortExact_schemeTwist_dualizing`: **the sequence
  exists and is short exact**, with no hypothesis beyond `ω_X` being a dualizing module.
* `AlgebraicGeometry.BlowUpDualizing.exists_shortExact_schemeTwist_dualizing_unit`: **the same
  with the second map the unit of `i^* ⊣ i_*`**, again with no further hypothesis.
* `AlgebraicGeometry.BlowUpDualizing`
  `.isZero_firstCohomology_dualizingTwist_of_restrictionVanishing`: `H¹(X, ω_X(n)) = 0` for every
  `n ≥ 0`, from the curve vanishing `H¹(E, (ω_X|_E)(n)) = 0` alone. Neither a module `ω_E` on `E`
  nor the clause-(1) isomorphism occurs in it.
* `AlgebraicGeometry.BlowUpDualizing.isZero_firstCohomology_dualizingTwist_of_curveVanishing`:
  the same with the curve vanishing given at an `ω_E` identified with `(ω_X|_E)(-1)` by clause
  (1) of that tag.
* `AlgebraicGeometry.BlowUpDualizing.bijective_stalkLinearMap_exceptionalIdealMap`: at an
  associated point of `ω_X` the stalk of `ℐ_E ⟶ 𝒪_X` is bijective.
* `AlgebraicGeometry.BlowUpDualizing.mono_whiskerLeft_exceptionalIdealMap`: **the irreducible
  content**, that `ω_X ⊗ ℐ_E ⟶ ω_X ⊗ 𝒪_X` is a monomorphism, i.e. that the local equation of
  `E` is a nonzerodivisor on `ω_X`.
* `AlgebraicGeometry.BlowUpDualizing.exceptionalIdealMap_comp_unit_eq_zero` and
  `.pullback_exceptionalIdealMap_eq_zero`: the unit of `i^* ⊣ i_*`, respectively `i^*`, kills the
  inclusion `ℐ_E ⟶ 𝒪_X`. This is what pins the second map above.

## The curve vanishing

The single input of `isZero_firstCohomology_dualizingTwist_of_restrictionVanishing` is the
vanishing `H¹(E, (ω_X|_E)(n)) = 0` for `n ≥ 0`. It does not follow from `ω_X` being *a* dualizing
module, which is invariant under an invertible twist while the vanishing is not. For the
dualizing module normalized relative to `ω_A` it follows from the global generation of `ω_X|_E`
([Stacks, Tag 0B5H] at `E`), by
`AlgebraicGeometry.BlowUpDualizing.isZero_firstCohomology_curveTwist_of_generatingSections` of
`…/RationalSingularities/ExceptionalGlobalGenerationVanishing.lean`.

## Why the monomorphy holds, and what replaces the depth theory

Tensoring the ideal sequence `0 ⟶ ℐ_E ⟶ 𝒪_X ⟶ i_*𝒪_E ⟶ 0` of [Stacks, Tag 0C6K] with `ω_X` is
only right exact; exactness on the left is the statement that the local equation of `E` is a
nonzerodivisor on `ω_X`. The source proves it from `ω_X` being maximal Cohen--Macaulay. Here it
is proved instead from [Stacks, Tag 0AVL] and the associated points of a dualizing module:

* `ℐ_E` is invertible — it is `𝒪_X(1)` by part (3) of [Stacks, Tag 02OS] — so its stalk at a
  point is free of rank one, and the stalk of `𝒪_X` as a module over itself is free of rank one
  on the germ of the unit section. The inclusion `ℐ_E ⟶ 𝒪_X` is a kernel, hence a
  monomorphism, hence injective on every stalk; read through those two trivializations it is
  multiplication by an element `t` of `𝒪_{X,x}`, and injectivity says exactly that `t` is a
  nonzerodivisor. **No effective-Cartier theory is used**: the nonzerodivisor is produced by the
  invertibility of the ideal sheaf together with the injectivity of its inclusion.
* At an associated point of `ω_X` every nonzerodivisor of `𝒪_{X,x}` is a unit
  (`Stacks.Duality.isUnit_of_isSMulRegular_of_isAssociatedPoint`, which rests on the stalk of a
  dualizing module being a dualizing module over the local ring). So `t` is a unit there and the
  stalk of `ℐ_E ⟶ 𝒪_X` is *bijective* at every associated point of `ω_X`.
* Tensoring with `ω_X` on the right preserves injectivity of a bijective stalk map
  (`AlgebraicGeometry.injective_stalkLinearMap_tensorRightMap`), and the associated points of
  `ω_X ⊗ ℐ_E` are those of `ω_X` because `ℐ_E` is invertible
  (`Stacks.Divisors.associatedPoints_tensorModules_eq_of_isInvertibleModule`). So
  [Stacks, Tag 0AVL] applies and the tensored inclusion is a monomorphism.

So the depth theory of a dualizing module is not needed for this step; what is needed is that a
dualizing module has no associated point on an effective Cartier divisor, and that is what the
unit statement above says at a stalk.

## Implementation notes

**The two forms of the sequence, and why the second is not a transport of the first.**
`exists_shortExact_schemeTwist_dualizing` asks only for *some* morphism `ω_X ⟶ i_* i^* ω_X`
making the sequence short exact, and the cheapest such morphism is the cokernel projection
followed by an identification of the cokernel. That identification is assembled from
isomorphisms only — right exactness of `ω_X ⊗ -` ([Stacks, Tag 05NB]), the cokernel `i_*𝒪_E` of
[Stacks, Tag 0C6K], the symmetry of the tensor product, the projection formula at a closed
immersion ([Stacks, Tag 0FZE]) and the left unit constraint — so no compatibility with the unit
of `i^* ⊣ i_*` has to be checked there.

`exists_shortExact_schemeTwist_dualizing_unit` does pin that morphism to the unit, which is what
the section-lifting step of clause (3) of [Stacks, Tag 0B64] needs, and it is obtained the other
way round: the cokernel criterion
`AlgebraicGeometry.exists_cokernelIso_of_isIso_unit_app`, as in
`StacksFrontier/AlgebraicGeometry/Divisors/ZeroSchemeExactSequenceTwist.lean`, produces the
identification of the cokernel *with* its compatibility with the unit, out of two facts: that
`i^*` kills the first map, which reduces by [Stacks, Tag 01CD] — an isomorphism unconditionally —
to its killing `ℐ_E ⟶ 𝒪_X`; and that the unit is an isomorphism at the cokernel, which holds by
the essential-image half of [Stacks, Tag 08KS] because that cokernel is `ω_X ⊗ i_*𝒪_E`, a direct
image along `i` by the projection formula. Transporting the first form instead would leave the
comparison between its arbitrary third map and the unit unknown.

**Which monoidal structure.** `Stacks.SheafOfModules.sheafTensorMonoidal`, in the form of the
instance `AlgebraicGeometry.schemeModulesMonoidal` of
`StacksFrontier/AlgebraicGeometry/Divisors/ZeroSchemeExactSequenceTwist.lean`, which is imported
above and re-enabled here by `attribute [local instance]` because the instance attribute there
is file-local. `sheafTensorMonoidal` itself has the sheaf of rings and its sheaf condition as
explicit arguments, so `attribute [local instance]` does not fire on *it*; it does fire on
`schemeModulesMonoidal`, which has those two arguments applied. At it `A ⊗ B` is
`AlgebraicGeometry.Scheme.Modules.tensorObj A B` and
`Stacks.RelativeVeryAmple.tensorModules X A B`, and `f ▷ G` is
`AlgebraicGeometry.Scheme.Modules.tensorRightMap f G`, all by `rfl`, so the twist
`AlgebraicGeometry.BlowUpDualizing.schemeTwist A ω_X 1` is `ω_X ⊗ 𝒪_X(1)` with no transport.
The braiding `β_` used in the monomorphy below is the symmetry of [Stacks, Tag 01CU] at that
same structure, `AlgebraicGeometry.schemeModulesSymmetric` of the same file, re-enabled the same
way.

**The arithmetic core is stated over an abstract commutative ring.**
`AlgebraicGeometry.BlowUpDualizing.bijective_of_rankOne_of_isUnit_of_isSMulRegular` says that an
injective linear map between two free rank-one modules is bijective as soon as every
nonzerodivisor of the ring is a unit; the geometric input enters only through that hypothesis,
which is `Stacks.Duality.isUnit_of_isSMulRegular_of_isAssociatedPoint` at the point in question.

## References

* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 0AVL](https://stacks.math.columbia.edu/tag/0AVL)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 02O1](https://stacks.math.columbia.edu/tag/02O1)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 0B62](https://stacks.math.columbia.edu/tag/0B62)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0B64](https://stacks.math.columbia.edu/tag/0B64)
* [Stacks Project, Tag 0BS4](https://stacks.math.columbia.edu/tag/0BS4)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
* [Stacks Project, Tag 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0AA2](https://stacks.math.columbia.edu/tag/0AA2)
* [Stacks Project, Tag 0A7F](https://stacks.math.columbia.edu/tag/0A7F)
* [Stacks Project, Tag 0A7M](https://stacks.math.columbia.edu/tag/0A7M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.Ample
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence
open Stacks.Cohomology.FormalFunctions (cohomologyDeltaFunctor)

universe u

namespace AlgebraicGeometry.BlowUpDualizing

attribute [local instance] AlgebraicGeometry.schemeModulesMonoidal
  AlgebraicGeometry.schemeModulesSymmetric

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The arithmetic core -/

/-- **An injective linear map between two free rank-one modules over a commutative ring in which
every nonzerodivisor is a unit is bijective.** Read through the two trivializations the map is
multiplication by a scalar `t`; injectivity makes `t` a nonzerodivisor, hence a unit, and
multiplication by a unit is surjective. -/
theorem bijective_of_rankOne_of_isUnit_of_isSMulRegular {R M N : Type*} [CommRing R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (a : M ≃ₗ[R] R) (b : R ≃ₗ[R] N) (φ : M →ₗ[R] N) (hinj : Function.Injective φ)
    (hunit : ∀ t : R, IsSMulRegular R t → IsUnit t) :
    Function.Bijective φ := by
  obtain ⟨t, key⟩ : ∃ t : R, ∀ r : R, b.symm (φ (a.symm r)) = r * t := by
    refine ⟨b.symm (φ (a.symm 1)), fun r => ?_⟩
    have h1 : a.symm r = r • a.symm (1 : R) := by
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [h1, map_smul, map_smul, smul_eq_mul]
  have hmul : Function.Injective fun r : R => r * t := by
    intro r r' h
    refine a.symm.injective (hinj (b.symm.injective ?_))
    rw [key, key]
    exact h
  have hreg : IsSMulRegular R t := by
    intro r r' h
    refine hmul ?_
    have h' : t * r = t * r' := h
    exact (mul_comm r t).trans (h'.trans (mul_comm t r'))
  obtain ⟨u, hu⟩ := hunit t hreg
  refine ⟨hinj, fun y => ⟨a.symm (b.symm y * (↑u⁻¹ : R)), b.symm.injective ?_⟩⟩
  rw [key, ← hu, mul_assoc, Units.inv_mul, mul_one]

/-- The stalk map of a morphism whose precomposition with a surjective-on-stalks morphism is
injective on stalks is itself injective on stalks. -/
theorem injective_stalkLinearMap_of_comp_of_surjective {X : Scheme.{u}} {F G H : X.Modules}
    (u : F ⟶ G) (v : G ⟶ H) (x : X)
    (hu : Function.Surjective (stalkLinearMap F G u x))
    (h : Function.Injective (stalkLinearMap F H (u ≫ v) x)) :
    Function.Injective (stalkLinearMap G H v x) := by
  intro z w hzw
  obtain ⟨z', rfl⟩ := hu z
  obtain ⟨w', rfl⟩ := hu w
  exact congrArg (stalkLinearMap F G u x) (h
    ((Scheme.Modules.stalkLinearMap_comp u v x z').trans
      (hzw.trans (Scheme.Modules.stalkLinearMap_comp u v x w').symm)))

/-! ### The ideal sheaf of the exceptional divisor -/

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The inclusion `ℐ_E ⟶ 𝒪_X` of the ideal sheaf of the exceptional divisor, which is the
first map of the ideal sequence of [Stacks, Tag 0C6K]. -/
abbrev exceptionalIdealMap : exceptionalIdealModule A ⟶ 𝟙_ ((blowUpScheme A).Modules) :=
  Stacks.IdealSheafSequence.divisorIdealMap (exceptionalIdeal (centre A))

/-- `ℐ_E` is invertible: it is `𝒪_X(1)`, by part (3) of [Stacks, Tag 02OS] in degree one. -/
instance isInvertibleModule_exceptionalIdealModule :
    IsInvertibleModule (blowUpScheme A) (exceptionalIdealModule A) :=
  Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso
    (exceptionalIdealModuleIsoTwistSheaf A).symm

/-- `ℐ_E` is quasi-coherent, being invertible. -/
instance isQuasicoherent_exceptionalIdealModule :
    (exceptionalIdealModule A).IsQuasicoherent :=
  Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _

/-- The inclusion of the ideal sheaf of the exceptional divisor is a monomorphism: it is the
first map of the short exact sequence of [Stacks, Tag 0C6K]. -/
theorem mono_exceptionalIdealMap : Mono (exceptionalIdealMap A) := by
  obtain ⟨hz, hSE⟩ :=
    Stacks.IdealSheafSequence.divisorIdeal_shortExact (exceptionalIdeal (centre A))
  exact hSE.mono_f

/-- **The restriction of the ideal sheaf of the exceptional divisor to it vanishes**, in the
form that the unit of `i^* ⊣ i_*` kills the inclusion `ℐ_E ⟶ 𝒪_X`.

The quotient arrow `𝒪_X ⟶ i_*𝒪_E` of [Stacks, Tag 0C6K] is the unit at `𝒪_X` followed by `i_*`
of the identification `i^*𝒪_X ≅ 𝒪_E` — both are adjoint transposes of that identification,
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_homEquiv` — and the inclusion is the kernel of
the quotient arrow, so the composite with the unit vanishes after an isomorphism. -/
theorem exceptionalIdealMap_comp_unit_eq_zero :
    exceptionalIdealMap A ≫ (Scheme.Modules.pullbackPushforwardAdjunction
      (exceptionalImmersion A)).unit.app (𝟙_ ((blowUpScheme A).Modules)) = 0 := by
  obtain ⟨m, hmiso, hq⟩ : ∃ m : (Scheme.Modules.pullback (exceptionalImmersion A) ⋙
        Scheme.Modules.pushforward (exceptionalImmersion A)).obj
          (𝟙_ ((blowUpScheme A).Modules)) ⟶
      (Scheme.Modules.pushforward (exceptionalImmersion A)).obj
        (𝟙_ ((exceptionalCurve A).Modules)),
      IsIso m ∧ (Scheme.Modules.pullbackPushforwardAdjunction
          (exceptionalImmersion A)).unit.app (𝟙_ ((blowUpScheme A).Modules)) ≫ m =
        Stacks.IdealSheafSequence.divisorQuotientMap (exceptionalIdeal (centre A)) :=
    ⟨(Scheme.Modules.pushforward (exceptionalImmersion A)).map
        (Scheme.Modules.pullbackUnitIso (exceptionalImmersion A)).hom,
      ((Scheme.Modules.pushforward (exceptionalImmersion A)).mapIso
        (Scheme.Modules.pullbackUnitIso (exceptionalImmersion A))).isIso_hom,
      ((Scheme.Modules.pullbackPushforwardAdjunction
          (exceptionalImmersion A)).homEquiv_unit _ _ _).symm.trans
        (Scheme.Modules.pullbackUnitIso_homEquiv (exceptionalImmersion A))⟩
  obtain ⟨hz, -⟩ :=
    Stacks.IdealSheafSequence.divisorIdeal_shortExact (exceptionalIdeal (centre A))
  have := hmiso
  refine (cancel_mono m).mp ?_
  exact (Category.assoc _ _ _).trans
    (((congrArg (fun k => exceptionalIdealMap A ≫ k) hq).trans hz).trans zero_comp.symm)

/-- **The restriction of the ideal sheaf of the exceptional divisor to it vanishes**, in the
form that `i^*` kills the inclusion `ℐ_E ⟶ 𝒪_X`. This is
`AlgebraicGeometry.BlowUpDualizing.exceptionalIdealMap_comp_unit_eq_zero` read through the
adjunction. -/
theorem pullback_exceptionalIdealMap_eq_zero :
    (Scheme.Modules.pullback (exceptionalImmersion A)).map (exceptionalIdealMap A) = 0 :=
  pullback_eq_zero_of_comp_unit_eq_zero (exceptionalImmersion A) (exceptionalIdealMap A)
    (exceptionalIdealMap_comp_unit_eq_zero A)

/-! ### The stalk of the ideal sheaf at an associated point of the dualizing module -/

/-- A dualizing module on the blowup is quasi-coherent. -/
private theorem isQuasicoherent_of_isDualizingModule [IsNoetherianRing A]
    (ωX : (blowUpScheme A).Modules)
    (hωX : letI : IsLocallyNoetherian (blowUpScheme A) := isLocallyNoetherian_blowUpScheme A
      Stacks.Duality.IsDualizingModule ωX) :
    ωX.IsQuasicoherent :=
  letI : IsLocallyNoetherian (blowUpScheme A) := isLocallyNoetherian_blowUpScheme A
  (((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae (blowUpScheme A) ωX).out 1 2 rfl
    rfl).mp hωX.1).1

/-- **At an associated point of a dualizing module the stalk of `ℐ_E ⟶ 𝒪_X` is bijective.**
Both stalks are free of rank one over `𝒪_{X,x}` — the first because `ℐ_E` is invertible, the
second on the germ of the unit section — and the map is injective because it is a kernel
inclusion, so it is multiplication by a nonzerodivisor; at an associated point of a dualizing
module a nonzerodivisor is a unit. -/
theorem bijective_stalkLinearMap_exceptionalIdealMap [IsNoetherianRing A]
    (ωX : (blowUpScheme A).Modules)
    (hωX : letI : IsLocallyNoetherian (blowUpScheme A) := isLocallyNoetherian_blowUpScheme A
      Stacks.Duality.IsDualizingModule ωX)
    {x : blowUpScheme A} (hx : Stacks.Divisors.IsAssociatedPoint ωX x) :
    Function.Bijective (stalkLinearMap _ _ (exceptionalIdealMap A) x) := by
  let : IsLocallyNoetherian (blowUpScheme A) := isLocallyNoetherian_blowUpScheme A
  let := isQuasicoherent_of_isDualizingModule A ωX hωX
  obtain ⟨n, hn⟩ := hωX.2
  obtain ⟨a⟩ := Stacks.Divisors.nonempty_stalk_linearEquiv_of_isInvertible
    (exceptionalIdealModule A) x
  refine bijective_of_rankOne_of_isUnit_of_isSMulRegular a
    (Stacks.Divisors.unitStalkLinearEquiv x) _
    (Scheme.Modules.injective_stalkLinearMap_of_mono _ (mono_exceptionalIdealMap A) x)
    fun t ht => Stacks.Duality.isUnit_of_isSMulRegular_of_isAssociatedPoint ωX n hn hx ht

/-! ### The monomorphy, which is the nonzerodivisor statement -/

/-- **The local equation of the exceptional divisor is a nonzerodivisor on a dualizing module**,
in the form that `ω_X ⊗ ℐ_E ⟶ ω_X ⊗ 𝒪_X` is a monomorphism. This is the step the source of
[Stacks, Tag 0B64] passes over.

By [Stacks, Tag 0AVL] it is enough to be injective on the stalk at every associated point of
`ω_X ⊗ ℐ_E`, and those are the associated points of `ω_X` because `ℐ_E` is invertible. There the
stalk of `ℐ_E ⟶ 𝒪_X` is bijective, so the stalk of `ℐ_E ⊗ ω_X ⟶ 𝒪_X ⊗ ω_X` is injective, and
the symmetry of the tensor product carries that to the whiskering on the other side. -/
theorem mono_whiskerLeft_exceptionalIdealMap [IsNoetherianRing A]
    (ωX : (blowUpScheme A).Modules)
    (hωX : letI : IsLocallyNoetherian (blowUpScheme A) := isLocallyNoetherian_blowUpScheme A
      Stacks.Duality.IsDualizingModule ωX) :
    Mono (ωX ◁ exceptionalIdealMap A) := by
  let : IsLocallyNoetherian (blowUpScheme A) := isLocallyNoetherian_blowUpScheme A
  have hωq := isQuasicoherent_of_isDualizingModule A ωX hωX
  let : ωX.IsQuasicoherent := hωq
  let : (ωX ⊗ exceptionalIdealModule A).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_tensorObj ωX (exceptionalIdealModule A) hωq inferInstance
  let : (ωX ⊗ 𝟙_ ((blowUpScheme A).Modules)).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_tensorObj ωX _ hωq
      (Stacks.Divisors.isQuasicoherent_structureModule (blowUpScheme A))
  have hass : Stacks.Divisors.associatedPoints (ωX ⊗ exceptionalIdealModule A) =
      Stacks.Divisors.associatedPoints ωX :=
    Stacks.Divisors.associatedPoints_tensorModules_eq_of_isInvertibleModule ωX _
  have hβ : ∀ x : blowUpScheme A,
      Function.Surjective (stalkLinearMap _ _ (β_ (exceptionalIdealModule A) ωX).hom x) :=
    fun x => Scheme.Modules.surjective_stalkLinearMap_of_section _
      (β_ (exceptionalIdealModule A) ωX).inv (Iso.inv_hom_id _) x
  refine Stacks.Divisors.mono_of_stalk_injective_on_associatedPoints _ fun x => ?_
  refine Or.imp id id ?_
  by_cases hx : x ∈ Stacks.Divisors.associatedPoints (ωX ⊗ exceptionalIdealModule A)
  · refine Or.inl ?_
    have hbij := bijective_stalkLinearMap_exceptionalIdealMap A ωX hωX
      ((Stacks.Divisors.mem_associatedPoints_iff ωX x).1 (hass ▸ hx))
    have hR : Function.Injective
        (stalkLinearMap _ _ (exceptionalIdealMap A ▷ ωX) x) :=
      injective_stalkLinearMap_tensorRightMap (exceptionalIdealMap A) ωX x hbij
    have hcomp : Function.Injective (stalkLinearMap _ _
        ((β_ (exceptionalIdealModule A) ωX).hom ≫ ωX ◁ exceptionalIdealMap A) x) := by
      rw [← BraidedCategory.braiding_naturality_left (exceptionalIdealMap A) ωX]
      exact Scheme.Modules.injective_stalkLinearMap_comp _ _ x hR
        (Scheme.Modules.injective_stalkLinearMap_of_retraction _
          (β_ (𝟙_ ((blowUpScheme A).Modules)) ωX).inv (Iso.hom_inv_id _) x)
    exact injective_stalkLinearMap_of_comp_of_surjective (β_ (exceptionalIdealModule A) ωX).hom
      (ωX ◁ exceptionalIdealMap A) x (hβ x) hcomp
  · exact Or.inr hx

/-! ### The sequence -/

/-- The cokernel of `ℐ_E ⟶ 𝒪_X` is `i_*𝒪_E`, by [Stacks, Tag 0C6K]. -/
private theorem nonempty_cokernelIso_exceptionalIdealMap :
    Nonempty (cokernel (exceptionalIdealMap A) ≅
      (Scheme.Modules.pushforward (exceptionalImmersion A)).obj
        (𝟙_ ((exceptionalCurve A).Modules))) := by
  obtain ⟨hz, hSE⟩ :=
    Stacks.IdealSheafSequence.divisorIdeal_shortExact (exceptionalIdeal (centre A))
  obtain ⟨e0, -⟩ := CategoryTheory.ShortComplex.exists_cokernelIso_of_shortExact hz hSE
  exact ⟨e0⟩

/-- **The restriction sequence of the dualizing module on the blowup.** For `ω_X` a dualizing
module on the blowup of the spectrum of a Noetherian local ring in its maximal ideal, there is a
short exact sequence

`0 ⟶ ω_X(1) ⟶ ω_X ⟶ i_*(ω_X|_E) ⟶ 0`,

`i : E ⟶ X` being the exceptional divisor.

It is the ideal sequence of [Stacks, Tag 0C6K] tensored with `ω_X`: the first map is the
inclusion `ℐ_E = 𝒪_X(1) ⟶ 𝒪_X` whiskered by `ω_X`, a monomorphism by
`AlgebraicGeometry.BlowUpDualizing.mono_whiskerLeft_exceptionalIdealMap`, and the third term is
its cokernel, identified with `i_*(ω_X|_E)` by right exactness of `ω_X ⊗ -` and the projection
formula at the closed immersion `i`. -/
theorem exists_shortExact_schemeTwist_dualizing [IsNoetherianRing A]
    (ωX : (blowUpScheme A).Modules)
    (hωX : letI : IsLocallyNoetherian (blowUpScheme A) := isLocallyNoetherian_blowUpScheme A
      Stacks.Duality.IsDualizingModule ωX) :
    ∃ (f : schemeTwist A ωX 1 ⟶ ωX)
      (g : ωX ⟶ (Scheme.Modules.pushforward (exceptionalImmersion A)).obj
        ((Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX))
      (w : f ≫ g = 0), (ShortComplex.mk f g w).ShortExact := by
  let := preservesFiniteColimits_tensorLeft (blowUpScheme A) ωX
  -- The cokernel of the ideal inclusion is `i_*𝒪_E`, by [Stacks, Tag 0C6K].
  obtain ⟨e0'⟩ := nonempty_cokernelIso_exceptionalIdealMap A
  -- The cokernel of the whiskered inclusion is `i_*(ω_X|_E)`.
  have e : cokernel (ωX ◁ exceptionalIdealMap A) ≅
      (Scheme.Modules.pushforward (exceptionalImmersion A)).obj
        ((Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX) :=
    (PreservesCokernel.iso (tensorLeft ωX) (exceptionalIdealMap A)).symm ≪≫
      (tensorLeft ωX).mapIso e0' ≪≫ β_ ωX _ ≪≫
      Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso
        (exceptionalImmersion A) (𝟙_ ((exceptionalCurve A).Modules)) ωX ≪≫
      (Scheme.Modules.pushforward (exceptionalImmersion A)).mapIso (λ_ _)
  obtain ⟨w₁, hS₁⟩ := CategoryTheory.ShortComplex.shortExact_of_cokernelIso
    (ωX ◁ exceptionalIdealMap A) (mono_whiskerLeft_exceptionalIdealMap A ωX hωX) e rfl
  -- Transport the sequence onto `ω_X(1) ⟶ ω_X`.
  have α : ωX ⊗ exceptionalIdealModule A ≅ schemeTwist A ωX 1 :=
    whiskerLeftIso ωX (exceptionalIdealModuleIsoTwistSheaf A)
  refine ⟨α.inv ≫ (ωX ◁ exceptionalIdealMap A) ≫ (ρ_ ωX).hom,
    (ρ_ ωX).inv ≫ cokernel.π (ωX ◁ exceptionalIdealMap A) ≫ e.hom, ?_, ?_⟩
  · have h0 : (ωX ◁ exceptionalIdealMap A) ≫
        cokernel.π (ωX ◁ exceptionalIdealMap A) ≫ e.hom = 0 :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ e.hom) (cokernel.condition _)).trans zero_comp)
    calc (α.inv ≫ (ωX ◁ exceptionalIdealMap A) ≫ (ρ_ ωX).hom) ≫
          ((ρ_ ωX).inv ≫ cokernel.π (ωX ◁ exceptionalIdealMap A) ≫ e.hom)
        = α.inv ≫ ((ωX ◁ exceptionalIdealMap A) ≫
            cokernel.π (ωX ◁ exceptionalIdealMap A) ≫ e.hom) := by simp
      _ = 0 := by rw [h0, comp_zero]
  · refine ShortComplex.shortExact_of_iso
      (S₁ := ShortComplex.mk (ωX ◁ exceptionalIdealMap A)
        (cokernel.π (ωX ◁ exceptionalIdealMap A) ≫ e.hom) w₁)
      (ShortComplex.isoMk α (ρ_ ωX) (Iso.refl _) ?_ ?_) hS₁ <;> simp

/-- **The restriction sequence of the dualizing module on the blowup, with its second map the
canonical restriction `ω_X ⟶ i_*(ω_X|_E)`.** For `ω_X` a dualizing module on the blowup of the
spectrum of a Noetherian local ring in its maximal ideal, the unit of `i^* ⊣ i_*` at `ω_X` fits
into a short exact sequence

`0 ⟶ ω_X(1) ⟶ ω_X ⟶ i_*(ω_X|_E) ⟶ 0`.

This is `AlgebraicGeometry.BlowUpDualizing.exists_shortExact_schemeTwist_dualizing` with the
third map pinned to the unit instead of left arbitrary, which is the sequence the source of
[Stacks, Tag 0B64] writes down and the one whose long exact cohomology sequence makes
`Γ(X, ω_X) ⟶ Γ(E, ω_X|_E)` surjective.

The pinning is the cokernel criterion
`AlgebraicGeometry.exists_cokernelIso_of_isIso_unit_app` rather than a transport of the previous
statement, exactly as in
`StacksFrontier/AlgebraicGeometry/Divisors/ZeroSchemeExactSequenceTwist.lean`: the criterion asks
that `i^*` kill the first map, which it does because it kills `ℐ_E ⟶ 𝒪_X`
(`AlgebraicGeometry.BlowUpDualizing.pullback_exceptionalIdealMap_eq_zero`) and the comparison of
[Stacks, Tag 01CD] is an isomorphism unconditionally, and that the unit be an isomorphism at the
cokernel of the first map, which holds because that cokernel is `ω_X ⊗ i_*𝒪_E` by right exactness
of `ω_X ⊗ -` ([Stacks, Tag 05NB]) and so is a direct image along `i` by the projection formula at
a closed immersion, whence the essential-image half of [Stacks, Tag 08KS] applies. -/
theorem exists_shortExact_schemeTwist_dualizing_unit [IsNoetherianRing A]
    (ωX : (blowUpScheme A).Modules)
    (hωX : letI : IsLocallyNoetherian (blowUpScheme A) := isLocallyNoetherian_blowUpScheme A
      Stacks.Duality.IsDualizingModule ωX) :
    ∃ (f : schemeTwist A ωX 1 ⟶ ωX)
      (w : f ≫ (Scheme.Modules.pullbackPushforwardAdjunction (exceptionalImmersion A)).unit.app
        ωX = 0),
      (ShortComplex.mk f ((Scheme.Modules.pullbackPushforwardAdjunction
        (exceptionalImmersion A)).unit.app ωX) w).ShortExact := by
  let := preservesZeroMorphisms_tensorLeft (blowUpScheme A) ωX
  let := preservesFiniteColimits_tensorLeft (blowUpScheme A) ωX
  have α : ωX ⊗ exceptionalIdealModule A ≅ schemeTwist A ωX 1 :=
    whiskerLeftIso ωX (exceptionalIdealModuleIsoTwistSheaf A)
  have hmid : Mono (ωX ◁ exceptionalIdealMap A) :=
    mono_whiskerLeft_exceptionalIdealMap A ωX hωX
  have hmono : Mono (α.inv ≫ (ωX ◁ exceptionalIdealMap A) ≫ (ρ_ ωX).hom) := inferInstance
  -- `i^*` kills the first map, hence so does the unit.
  have hwl : (Scheme.Modules.pullback (exceptionalImmersion A)).map
      (ωX ◁ exceptionalIdealMap A) = 0 :=
    pullback_whiskerLeft_eq_zero' (exceptionalImmersion A) ωX (exceptionalIdealMap A)
      (pullback_exceptionalIdealMap_eq_zero A)
  have hF0 : (Scheme.Modules.pullback (exceptionalImmersion A)).map
      (α.inv ≫ (ωX ◁ exceptionalIdealMap A) ≫ (ρ_ ωX).hom) = 0 := by
    rw [Functor.map_comp, Functor.map_comp, hwl, zero_comp, comp_zero]
  have hw := comp_unit_eq_zero_of_pullback_eq_zero (exceptionalImmersion A)
    (α.inv ≫ (ωX ◁ exceptionalIdealMap A) ≫ (ρ_ ωX).hom) hF0
  -- The cokernel of the first map is `ω_X ⊗ i_*𝒪_E`, by [Stacks, Tag 0C6K] and right exactness.
  obtain ⟨e0'⟩ := nonempty_cokernelIso_exceptionalIdealMap A
  have ecok : cokernel (α.inv ≫ (ωX ◁ exceptionalIdealMap A) ≫ (ρ_ ωX).hom) ≅
      ωX ⊗ (Scheme.Modules.pushforward (exceptionalImmersion A)).obj
        (𝟙_ ((exceptionalCurve A).Modules)) :=
    cokernelEpiComp α.inv ((ωX ◁ exceptionalIdealMap A) ≫ (ρ_ ωX).hom) ≪≫
      cokernelCompIsIso (ωX ◁ exceptionalIdealMap A) (ρ_ ωX).hom ≪≫
      (PreservesCokernel.iso (tensorLeft ωX) (exceptionalIdealMap A)).symm ≪≫
      (tensorLeft ωX).mapIso e0'
  -- That is a direct image along `i`, so the unit is an isomorphism there.
  have := Stacks.ClosedImmersion.full_pushforward (exceptionalImmersion A)
  have := Stacks.ClosedImmersion.faithful_pushforward (exceptionalImmersion A)
  obtain ⟨N, ⟨eN⟩⟩ := essImage_tensor_pushforward' (exceptionalImmersion A)
    (𝟙_ ((exceptionalCurve A).Modules)) ωX
  have : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (exceptionalImmersion A)).unit.app
      (cokernel (α.inv ≫ (ωX ◁ exceptionalIdealMap A) ≫ (ρ_ ωX).hom))) :=
    (Adjunction.isIso_unit_app_iff_mem_essImage _).mpr ⟨N, ⟨eN ≪≫ ecok.symm⟩⟩
  obtain ⟨e, he⟩ := exists_cokernelIso_of_isIso_unit_app
    (Scheme.Modules.pullbackPushforwardAdjunction (exceptionalImmersion A)) _ hw
  exact ⟨_, ShortComplex.shortExact_of_cokernelIso _ hmono e he⟩

/-- **`H¹(X, ω_X(n)) = 0` for every `n ≥ 0`, from the vanishing on the exceptional curve of the
twists of the restriction of `ω_X` itself.**

This is `AlgebraicGeometry.BlowUpDualizing.isZero_firstCohomology_dualizingTwist` with its `f`,
`g`, `w`, `hS` supplied by
`AlgebraicGeometry.BlowUpDualizing.exists_shortExact_schemeTwist_dualizing`, its `hqc` by
`AlgebraicGeometry.BlowUpDualizing.isQuasicoherent_curveTwist_pullback` and its `heventual` by
`AlgebraicGeometry.BlowUpDualizing.exists_isZero_firstCohomology_schemeTwist`, so the single
input is the curve vanishing, phrased at `(ω_X|_E)(n)` — the module that actually appears in the
restriction sequence. No module `ω_E` on `E`, no dualizing hypothesis on one and no isomorphism
`ω_E ≅ (ω_X|_E)(-1)` occurs: clause (1) of [Stacks, Tag 0B64] is what converts this input into
the [Stacks, Tag 0B62] vanishing `H¹(E, ω_E(n+1)) = 0`. -/
theorem isZero_firstCohomology_dualizingTwist_of_restrictionVanishing [IsNoetherianRing A]
    (ωX : (blowUpScheme A).Modules)
    (hωX : letI : IsLocallyNoetherian (blowUpScheme A) := isLocallyNoetherian_blowUpScheme A
      Stacks.Duality.IsDualizingModule ωX)
    (hcurve : ∀ n : ℕ, IsZero (((cohomologyDeltaFunctor (exceptionalCurve A)).functor 1).obj
      (curveTwist A ((Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX) (n : ℤ))))
    (n : ℕ) :
    IsZero (((cohomologyDeltaFunctor (blowUpScheme A)).functor 1).obj (schemeTwist A ωX n)) := by
  obtain ⟨f, g, w, hS⟩ := exists_shortExact_schemeTwist_dualizing A ωX hωX
  exact isZero_firstCohomology_dualizingTwist A ωX f g w hS
    (fun m => isQuasicoherent_curveTwist_pullback A ωX hωX.1 (m : ℤ)) hcurve
    (exists_isZero_firstCohomology_schemeTwist A ωX hωX) n

/-- `H¹(X, ω_X(n)) = 0` for every `n ≥ 0`, with the curve vanishing given at a module `ω_E` on
`E` identified with `(ω_X|_E)(-1)` by clause (1) of [Stacks, Tag 0B64].

This is `isZero_firstCohomology_dualizingTwist_of_restrictionVanishing` with its `hcurve`
obtained by twisting the clause-(1) isomorphism, so the dualizing hypothesis on `ω_E` is not
used. -/
theorem isZero_firstCohomology_dualizingTwist_of_curveVanishing [IsNoetherianRing A]
    (ωX : (blowUpScheme A).Modules) (ωE : (exceptionalCurve A).Modules)
    (hωX : letI : IsLocallyNoetherian (blowUpScheme A) := isLocallyNoetherian_blowUpScheme A
      Stacks.Duality.IsDualizingModule ωX)
    (_hωE : letI : IsLocallyNoetherian (exceptionalCurve A) :=
        isLocallyNoetherian_exceptionalCurve A
      Stacks.Duality.IsDualizingModule ωE)
    (e : ωE ≅ curveTwist A ((Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX) (-1))
    (hcurveE : ∀ n : ℕ, IsZero (((cohomologyDeltaFunctor (exceptionalCurve A)).functor 1).obj
      (curveTwist A ωE ((n : ℤ) + 1))))
    (n : ℕ) :
    IsZero (((cohomologyDeltaFunctor (blowUpScheme A)).functor 1).obj (schemeTwist A ωX n)) :=
  isZero_firstCohomology_dualizingTwist_of_restrictionVanishing A ωX hωX
    (fun m => IsZero.of_iso (hcurveE m)
      (((cohomologyDeltaFunctor (exceptionalCurve A)).functor 1).mapIso
        (nonempty_pullback_curveTwist_iso e (m : ℤ)).some)) n

end AlgebraicGeometry.BlowUpDualizing

end
