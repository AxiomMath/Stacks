module

public import StacksFrontier.AlgebraicGeometry.AmpleSurjectiveThickening.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CohomologicalCriterion
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic

/-!
# The obstruction group of [Stacks, Tag 09MS], and the first instance of its cohomological lift

Let `i : Z ⟶ X` be a closed immersion with ideal sheaf `𝓘` and let `L` be an invertible
`𝒪_X`-module. The converse half of [Stacks, Tag 09MS] is proved in
`StacksFrontier/AlgebraicGeometry/AmpleSurjectiveThickening/Basic.lean` from the vanishing

    ∀ n ≥ 1, ∃ m ≥ 1, n ∣ m ∧ H¹(X, 𝓘 ⊗ L^{⊗ m}) = 0

of the obstruction group in arbitrarily high degrees, and that vanishing is in turn the only
input of `Stacks.AmpleClosedImmersion.SectionsLiftAfterPower`, the cohomological lift which the
whole 09MS cluster of this repository carries as a hypothesis.

**Nothing in this repository had a term of either type.** The lift is a `def … : Prop` and the
vanishing is written out as a hypothesis; between them they are assumed by a dozen declarations
in ten files, and no declaration produced one, so no build and no `#print axioms` could see
whether they are satisfiable at all. This file produces the first terms of both, from the
cohomological criterion for ampleness.

## Main results

* `Stacks.AmpleSurjectiveThickening.isCoherent_idealSheaf`: the ideal sheaf of a closed immersion
  into a locally Noetherian scheme is coherent. It is quasi-coherent by
  [Stacks, Tag 01QY] and a subsheaf of the coherent `𝒪_X`, so [Stacks, Tag 01Y1] applies.
* `Stacks.AmpleSurjectiveThickening.isZero_h1_idealSheaf_tensorPowModule_of_eventualTwistVanishing`
  says that **the obstruction group vanishes in arbitrarily high degrees** as soon as `L` satisfies
  condition (2) of [Stacks, Tag 0B5U] — eventual vanishing of the higher cohomology of the
  twists of a coherent module. This is the hypothesis of
  `Stacks.AmpleSurjectiveThickening.isAmple_of_isAmple_modulePullback_of_isZero_h1`, discharged.
* `Stacks.AmpleSurjectiveThickening.sectionsLiftAfterPower_of_eventualTwistVanishing`:
  consequently `Stacks.AmpleClosedImmersion.SectionsLiftAfterPower i L` holds under condition (2),
  which is the **first term of that type in this repository**.
* `Stacks.AmpleSurjectiveThickening.isZero_h1_idealSheaf_tensorPowModule_of_isAmple` and
  `Stacks.AmpleSurjectiveThickening.sectionsLiftAfterPower_of_isAmple`: the same two, at the
  hypotheses of [Stacks, Tag 0B5U] itself — `X` proper over a Noetherian ring and `L` ample.

## What this is and is not

Condition (2) of [Stacks, Tag 0B5U] implies ampleness of `L` on a quasi-compact locally
Noetherian scheme, by the two unconditional implications
`AlgebraicGeometry.Scheme.Modules.hasIdealTwistH1Vanishing_of_eventualTwistVanishing` and
`AlgebraicGeometry.Scheme.Modules.isAmple_of_hasIdealTwistH1Vanishing` ([Stacks, Tag 0B5P]).
**So this is not a route to the converse of [Stacks, Tag 09MS]**: it discharges the obstruction
hypothesis only where the conclusion of that converse is already available, and it is recorded
as what it is — a witness that the hypothesis is satisfiable, and satisfiable away from the
degenerate cases where it holds because the group is zero for trivial reasons (`𝓘 = 0`, or `X`
affine). At `X = ℙ¹` over a field thickened by a square-zero ideal and `L = 𝒪(1)` every binder
below is met and `𝓘 ≠ 0`.

The source's own route to the lift does not go through the vanishing of the obstruction group at
all: it kills the obstruction *class* by replacing the section by a power, which needs
[Stacks, Tag 01XR] in degree one on a scheme that is not affine, and of that this repository has
only the cases where the group vanishes outright
(`../SectionPowerCohomology/Basic.lean:122` and `:143`). That is unchanged by this file.

## References

* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 0B5U](https://stacks.math.columbia.edu/tag/0B5U)
* [Stacks Project, Tag 0B5P](https://stacks.math.columbia.edu/tag/0B5P)
* [Stacks Project, Tag 01QY](https://stacks.math.columbia.edu/tag/01QY)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.AmpleTheory

universe u

namespace Stacks.AmpleSurjectiveThickening

variable {Z X : Scheme.{u}} (i : Z ⟶ X) (L : X.Modules) [IsInvertibleModule X L]

/-- **The ideal sheaf of a closed immersion into a locally Noetherian scheme is coherent.** It is
quasi-coherent by [Stacks, Tag 01QY], and it is a subsheaf of `𝒪_X`, which is coherent; a
quasi-coherent subsheaf of a coherent module on a locally Noetherian scheme is coherent
([Stacks, Tag 01Y1]).

The inclusion is the kernel map of `𝒪_X ⟶ i_* 𝒪_Z`, of which the ideal sheaf is by definition the
kernel. Its monomorphism instance is applied by hand: `AlgebraicGeometry.Scheme.Modules` is a
`def`, so instance search does not see the zero morphisms of the category of sheaves of modules
through it. -/
theorem isCoherent_idealSheaf [IsClosedImmersion i] [IsLocallyNoetherian X] :
    (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).IsCoherent :=
  @Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono X _
    (SheafOfModules.unit X.ringCatSheaf)
    (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom)
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
    (Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf i)
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom))
    (inferInstanceAs
      (Mono (kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom))))

/-- **The obstruction group of [Stacks, Tag 09MS] vanishes in arbitrarily high degrees** whenever
`L` satisfies condition (2) of [Stacks, Tag 0B5U]: for every coherent `𝒪_X`-module the higher
cohomology of its twists by `L^{⊗ n}` vanishes for all large `n`.

The ideal sheaf is coherent by `Stacks.AmpleSurjectiveThickening.isCoherent_idealSheaf`, so
condition (2) applies to it; a degree divisible by `n` and at least the threshold is
`n * max n₀ 1`. The two spellings of the tensor powers meet here: condition (2) is stated over
`Stacks.SheafOfModules.Invertible.tensorPower` and the hypothesis being discharged over
`Stacks.Ample.tensorPowModule`, and
`Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso` is the comparison. -/
theorem isZero_h1_idealSheaf_tensorPowModule_of_eventualTwistVanishing [IsClosedImmersion i]
    [IsLocallyNoetherian X]
    (h : AlgebraicGeometry.Scheme.Modules.HasEventualTwistCohomologyVanishing L) :
    ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 1 ≤ m ∧ n ∣ m ∧
      IsZero (((moduleGlobalSections X).rightDerived 1).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
            (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom)).obj
              (tensorPowModule X L (m : ℤ))))) := by
  obtain ⟨n₀, hn₀⟩ := h _ (isCoherent_idealSheaf i)
  intro n hn
  refine ⟨n * max n₀ 1, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
    Dvd.intro _ rfl, ?_⟩
  refine (hn₀ (n * max n₀ 1) 1 ?_ Nat.one_pos).of_iso
    (((moduleGlobalSections X).rightDerived 1).mapIso
      (Stacks.RelativeVeryAmple.tensorModulesMapIso X (Iso.refl _)
        (Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso X L
          ((n * max n₀ 1 : ℕ) : ℤ))).symm)
  calc n₀ ≤ max n₀ 1 := le_max_left _ _
    _ = 1 * max n₀ 1 := (one_mul _).symm
    _ ≤ n * max n₀ 1 := Nat.mul_le_mul_right _ hn

/-- **The cohomological lift of [Stacks, Tag 09MS] under condition (2) of [Stacks, Tag 0B5U].**
This is the first term of type `Stacks.AmpleClosedImmersion.SectionsLiftAfterPower` in this
repository: the predicate is assumed by a dozen declarations in ten files and was produced by
none, so nothing recorded that it is satisfiable. -/
theorem sectionsLiftAfterPower_of_eventualTwistVanishing [IsClosedImmersion i]
    [IsLocallyNoetherian X]
    (h : AlgebraicGeometry.Scheme.Modules.HasEventualTwistCohomologyVanishing L) :
    Stacks.AmpleClosedImmersion.SectionsLiftAfterPower i L :=
  sectionsLiftAfterPower_of_isZero_h1 i L
    (isZero_h1_idealSheaf_tensorPowModule_of_eventualTwistVanishing i L h)

/-- **The obstruction group of [Stacks, Tag 09MS] vanishes in arbitrarily high degrees** for an
ample `L` on a scheme proper over a Noetherian ring. Those are the hypotheses of
[Stacks, Tag 0B5U], whose implication (1) ⟹ (2) is
`AlgebraicGeometry.Scheme.Modules.hasEventualTwistCohomologyVanishing_of_isAmple`. The two
ampleness predicates of [Stacks, Tag 01PS] are exchanged by
`Stacks.AmpleBridge.isAmple_iff_isAmple`. -/
theorem isZero_h1_idealSheaf_tensorPowModule_of_isAmple {R : Type u} [CommRing R]
    [IsNoetherianRing R] (f : X ⟶ Spec (.of R)) [IsProper f] [IsClosedImmersion i]
    (hL : IsAmple X L) :
    ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 1 ≤ m ∧ n ∣ m ∧
      IsZero (((moduleGlobalSections X).rightDerived 1).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
            (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom)).obj
              (tensorPowModule X L (m : ℤ))))) :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  isZero_h1_idealSheaf_tensorPowModule_of_eventualTwistVanishing i L
    (AlgebraicGeometry.Scheme.Modules.hasEventualTwistCohomologyVanishing_of_isAmple L f
      ((Stacks.AmpleBridge.isAmple_iff_isAmple X L).mp hL))

/-- **The cohomological lift of [Stacks, Tag 09MS] for an ample `L` on a scheme proper over a
Noetherian ring**, and hence a non-degenerate instantiation of every binder of
`Stacks.AmpleClosedImmersion.SectionsLiftAfterPower`. -/
theorem sectionsLiftAfterPower_of_isAmple {R : Type u} [CommRing R] [IsNoetherianRing R]
    (f : X ⟶ Spec (.of R)) [IsProper f] [IsClosedImmersion i] (hL : IsAmple X L) :
    Stacks.AmpleClosedImmersion.SectionsLiftAfterPower i L :=
  sectionsLiftAfterPower_of_isZero_h1 i L
    (isZero_h1_idealSheaf_tensorPowModule_of_isAmple i L f hL)

end Stacks.AmpleSurjectiveThickening

end
