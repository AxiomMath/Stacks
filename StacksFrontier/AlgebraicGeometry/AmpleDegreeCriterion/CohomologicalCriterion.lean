module

public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.TFAE
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.QuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The cohomological criterion for ampleness

[Stacks, Tag 0B5U] says: let `R` be a Noetherian ring, let `f : X ⟶ Spec R` be proper and let
`𝓛` be an invertible `𝒪_X`-module. Then the following are equivalent.

1. `𝓛` is ample.
2. For every coherent `𝒪_X`-module `ℱ` there is an `n₀ ≥ 0` with
   `Hᵖ(X, ℱ ⊗ 𝓛^{⊗ n}) = 0` for all `n ≥ n₀` and all `p > 0`.
3. For every quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_X` there is an `n ≥ 1` with
   `H¹(X, ℐ ⊗ 𝓛^{⊗ n}) = 0`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.HasEventualTwistCohomologyVanishing`: condition (2).
* `AlgebraicGeometry.Scheme.Modules.HasIdealTwistH1Vanishing`: condition (3).

## Main results

* `AlgebraicGeometry.Scheme.Modules.hasEventualTwistCohomologyVanishing_of_isAmple`: **the
  implication (1) ⟹ (2)**, at the tag's own hypotheses.
* `AlgebraicGeometry.Scheme.Modules.hasIdealTwistH1Vanishing_of_eventualTwistVanishing`:
  **the implication (2) ⟹ (3)**, unconditionally on a locally Noetherian scheme.
* `AlgebraicGeometry.Scheme.Modules.isAmple_of_hasIdealTwistH1Vanishing`: **the implication
  (3) ⟹ (1)**, unconditionally on a quasi-compact scheme.
* `AlgebraicGeometry.Scheme.Modules.isAmple_of_eventualTwistVanishing`: the composite
  (2) ⟹ (1) at the tag's own hypotheses.
* `AlgebraicGeometry.Scheme.Modules.tfae_isAmple_twistCohomologyVanishing`: **the three
  equivalent conditions**.

## How each implication is proved

The source proves (1) ⟹ (2) by citing clause (4) of [Stacks, Tag 0B5T], (2) ⟹ (3) as trivial,
and (3) ⟹ (1) by citing [Stacks, Tag 0B5P]. Here:

* **(1) ⟹ (2) is clause (4) of [Stacks, Tag 0B5T]**, proved at the tag's own hypotheses as
  `Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist` in
  `../ProperAmpleCohomology/Basic.lean`. All this file adds is the passage between the two
  spellings of the tensor powers and of cohomology described below.
* **(2) ⟹ (3) is proved**, and with none of the tag's hypotheses beyond local Noetherianness of
  `X`, which is what makes a quasi-coherent subsheaf of `𝒪_X` coherent ([Stacks, Tag 01Y1],
  `Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono`, the structure sheaf being
  coherent by `Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit`). Condition (2) is
  then applied at `p = 1` and at an exponent at least `max n₀ 1`.
* **(3) ⟹ (1) is proved**, and with none of the tag's hypotheses beyond quasi-compactness of
  `X`: it is [Stacks, Tag 0B5P], proved as
  `AlgebraicGeometry.Scheme.Modules.isAmple_of_forall_isZero_h1_quasicoherentIdeal`.

## Implementation notes

**Two spellings of the tensor powers meet here, and two of cohomology.** Conditions (2) and (3)
are stated over `Stacks.SheafOfModules.Invertible.tensorPower`, the family
`AlgebraicGeometry.Scheme.Modules.IsAmple` and [Stacks, Tag 0B5P] are stated over, and with the
module-valued global sections functor `AlgebraicGeometry.moduleGlobalSections`; clause
(4) of [Stacks, Tag 0B5T] is stated over `Stacks.Ample.tensorPowModule` and
`Stacks.Ample.IsAmple`, and with the group-valued `Hgroup`. Three existing comparisons close the
gap, and each is used once: `Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso` for the
powers, `Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple` for the ampleness predicates, and
`Stacks.Cohomology.Affine.isZero_rightDerived_evaluation_of_isZero_Hgroup` for the cohomology;
the first and the last are collected in
`isZero_rightDerived_moduleGlobalSections_of_isZero_Hgroup`. The two spellings of the tensor
product itself — `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf X.toRingedSpace` and
`Stacks.RelativeVeryAmple.tensorModules X` — are the same term, so nothing transports them.

## References

* [Stacks Project, Tag 0B5U](https://stacks.math.columbia.edu/tag/0B5U)
* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
* [Stacks Project, Tag 0B5P](https://stacks.math.columbia.edu/tag/0B5P)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Invertible (tensorPower)
-- (open removed: its only name was the merged moduleGlobalSections)
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

/-- **Condition (2) of [Stacks, Tag 0B5U].** For every coherent `𝒪_X`-module `ℱ` there is an
exponent `n₀` beyond which all the higher cohomology of `ℱ ⊗ 𝓛^{⊗ n}` vanishes. -/
public def HasEventualTwistCohomologyVanishing : Prop :=
  ∀ F : X.Modules, F.IsCoherent → ∃ n₀ : ℕ, ∀ n p : ℕ, n₀ ≤ n → 0 < p →
    IsZero (((moduleGlobalSections X).rightDerived p).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj
        ((tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (n : ℤ))))))

/-- **Condition (3) of [Stacks, Tag 0B5U].** Every quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_X` —
a quasi-coherent module with a monomorphism into the structure sheaf — admits an `n ≥ 1` with
`H¹(X, ℐ ⊗ 𝓛^{⊗ n}) = 0`. -/
public def HasIdealTwistH1Vanishing : Prop :=
  ∀ (J : X.Modules) (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf), Mono ι →
    J.IsQuasicoherent → ∃ n : ℕ, 1 ≤ n ∧
      IsZero (((moduleGlobalSections X).rightDerived 1).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (J)).obj
          ((tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ))))))

/-- **A vanishing twist, carried into the spelling conditions (2) and (3) are stated at.**
Vanishing of the group-valued `H ᵖ(X, ℱ ⊗ 𝓛^{⊗ n})` taken over `Stacks.Ample.tensorPowModule`
gives vanishing of the module-valued one taken over
`Stacks.SheafOfModules.Invertible.tensorPower`. -/
theorem isZero_rightDerived_moduleGlobalSections_of_isZero_Hgroup (F : X.Modules) (n : ℤ)
    (p : ℕ) (h : IsZero (Hgroup X.ringCatSheaf ⊤ p
      (Stacks.RelativeVeryAmple.tensorModules X F (Stacks.Ample.tensorPowModule X L n)))) :
    IsZero (((moduleGlobalSections X).rightDerived p).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj
        ((tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L n))))) :=
  (Stacks.Cohomology.Affine.isZero_rightDerived_evaluation_of_isZero_Hgroup
      X.ringCatSheaf ⊤ p _ h).of_iso
    (((moduleGlobalSections X).rightDerived p).mapIso
      (Stacks.RelativeVeryAmple.tensorModulesMapIso X (Iso.refl F)
        (Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso X L n)))

/-- **The implication (1) ⟹ (2) of [Stacks, Tag 0B5U]**, at the tag's own hypotheses: `R`
Noetherian, `f : X ⟶ Spec R` proper, `𝓛` ample.

This is clause (4) of [Stacks, Tag 0B5T],
`Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist`,
read through the two comparisons of the implementation notes: ampleness is carried across by
`Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple` and the conclusion by
`isZero_rightDerived_moduleGlobalSections_of_isZero_Hgroup`. -/
@[stacks 0B5U "the implication (1) ⟹ (2)"]
public theorem hasEventualTwistCohomologyVanishing_of_isAmple {R : Type u} [CommRing R]
    [IsNoetherianRing R] (f : X ⟶ Spec (.of R)) [IsProper f] (hL : IsAmple X L) :
    HasEventualTwistCohomologyVanishing L := by
  intro F hF
  obtain ⟨n₀, hn₀⟩ :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist f F L
      (Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple X L hL)
  exact ⟨n₀, fun n p hn hp =>
    isZero_rightDerived_moduleGlobalSections_of_isZero_Hgroup L F (n : ℤ) p (hn₀ n p hn hp)⟩

/-- **The implication (2) ⟹ (3) of [Stacks, Tag 0B5U]**, on a locally Noetherian scheme and with
none of the tag's remaining hypotheses.

A quasi-coherent sheaf of ideals is a quasi-coherent submodule of the structure sheaf, which on a
locally Noetherian scheme is coherent ([Stacks, Tag 01Y1], the structure sheaf itself being
coherent); condition (2) then applies to it, and is read at `p = 1` and at an exponent at least
one. -/
@[stacks 0B5U "the implication (2) ⟹ (3)"]
public theorem hasIdealTwistH1Vanishing_of_eventualTwistVanishing [IsLocallyNoetherian X]
    (h : HasEventualTwistCohomologyVanishing L) : HasIdealTwistH1Vanishing L := by
  intro J ι hι hJ
  have hunit : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have hJc : J.IsCoherent :=
    @Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono X _
      (SheafOfModules.unit X.ringCatSheaf) J hunit hJ ι hι
  obtain ⟨n₀, hn₀⟩ := h J hJc
  exact ⟨max n₀ 1, Nat.le_max_right _ _,
    hn₀ (max n₀ 1) 1 (Nat.le_max_left _ _) Nat.one_pos⟩

/-- **The implication (3) ⟹ (1) of [Stacks, Tag 0B5U]**, on a quasi-compact scheme and with none
of the tag's remaining hypotheses. This is [Stacks, Tag 0B5P]. -/
@[stacks 0B5U "the implication (3) ⟹ (1)"]
public theorem isAmple_of_hasIdealTwistH1Vanishing [CompactSpace X]
    (h : HasIdealTwistH1Vanishing L) : IsAmple X L :=
  isAmple_of_forall_isZero_h1_quasicoherentIdeal L h

/-- A proper scheme over a Noetherian ring is locally Noetherian and quasi-compact. -/
private theorem isLocallyNoetherian_and_compactSpace_of_isProper {R : Type u} [CommRing R]
    [IsNoetherianRing R] (f : X ⟶ Spec (.of R)) [IsProper f] :
    IsLocallyNoetherian X ∧ CompactSpace X :=
  ⟨LocallyOfFiniteType.isLocallyNoetherian f, QuasiCompact.compactSpace_of_compactSpace f⟩

/-- **The implication (2) ⟹ (1) of [Stacks, Tag 0B5U]**, at the tag's own hypotheses: `R`
Noetherian, `f : X ⟶ Spec R` proper. Both steps are unconditional; properness and the Noetherian
base enter only through `IsLocallyNoetherian X` and `CompactSpace X`. -/
@[stacks 0B5U "the implication (2) ⟹ (1)"]
public theorem isAmple_of_eventualTwistVanishing {R : Type u} [CommRing R] [IsNoetherianRing R]
    (f : X ⟶ Spec (.of R)) [IsProper f] (h : HasEventualTwistCohomologyVanishing L) :
    IsAmple X L := by
  obtain ⟨_, _⟩ := isLocallyNoetherian_and_compactSpace_of_isProper f
  exact isAmple_of_hasIdealTwistH1Vanishing L
    (hasIdealTwistH1Vanishing_of_eventualTwistVanishing L h)

/-- **[Stacks, Tag 0B5U].** For `R` Noetherian, `f : X ⟶ Spec R` proper and `𝓛` an invertible
`𝒪_X`-module, the three conditions

1. `𝓛` is ample;
2. the higher cohomology of `ℱ ⊗ 𝓛^{⊗ n}` vanishes for every coherent `ℱ` and all large `n`;
3. `H¹(X, ℐ ⊗ 𝓛^{⊗ n}) = 0` for some `n ≥ 1`, for every quasi-coherent sheaf of ideals `ℐ`

are equivalent. The implication (1) ⟹ (2) is clause (4) of [Stacks, Tag 0B5T]; the other two are
proved with none of the tag's hypotheses. -/
@[stacks 0B5U "the three equivalent conditions", ega "III 5.2.3" "(ii), special case"]
public theorem tfae_isAmple_twistCohomologyVanishing {R : Type u} [CommRing R]
    [IsNoetherianRing R] (f : X ⟶ Spec (.of R)) [IsProper f] :
    List.TFAE
      [IsAmple X L, HasEventualTwistCohomologyVanishing L, HasIdealTwistH1Vanishing L] := by
  obtain ⟨_, _⟩ := isLocallyNoetherian_and_compactSpace_of_isProper f
  tfae_have 1 → 2 := hasEventualTwistCohomologyVanishing_of_isAmple L f
  tfae_have 2 → 3 := hasIdealTwistH1Vanishing_of_eventualTwistVanishing L
  tfae_have 3 → 1 := isAmple_of_hasIdealTwistH1Vanishing L
  tfae_finish

end AlgebraicGeometry.Scheme.Modules

end
