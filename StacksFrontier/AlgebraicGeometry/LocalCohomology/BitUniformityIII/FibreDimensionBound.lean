module

public import StacksFrontier.AlgebraicGeometry.HigherDirectImageFibreDimension.GeneralDimensionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.LerayAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupSituation
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Bounded
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The integer `d(S)` of Tag 0GA6, and the vanishing of cohomology above it

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `p : X → Spec(A)` the blowing up of
`Spec(A)` in `I`. [Stacks, Tag 0GA6] denotes by `d = d(S)` *the maximum of the dimensions of the
fibres of `p`* (and `0` if `X = ∅`), says that this is well defined, and observes that
`Hⁱ(X, ℱ) = 0` for every coherent `𝒪_X`-module `ℱ` and every `i > d`, by
[Stacks, Tags 02V7, 01XK].

This file makes all three statements theorems about the blowup `X = Proj(⨁ₙ Iⁿ)`,
`Stacks.Blowup.toSpec I : X ⟶ Spec A`:

* `fibreDim I` is the least natural number bounding the topological Krull dimension of every
  fibre of `p`. A fibre with empty underlying space has dimension `⊥`, so it imposes nothing, and
  `fibreDim I = 0` when `X = ∅`, as the source stipulates.
* It is well defined, i.e. the dimensions of the fibres are bounded at all, by [Stacks, Tag 0A3V]
  (`AlgebraicGeometry.exists_topologicalKrullDim_fiber_le`): `p` is of finite type, being proper
  (`Stacks.Blowup.instIsProperToSpec`), over the quasi-compact `Spec A`. Hence every fibre has
  dimension at most `fibreDim I` (`topologicalKrullDim_fiber_le_fibreDim`), and `fibreDim I` is
  the least such bound (`fibreDim_le`), i.e. the maximum. It agrees with the description of
  `d(S)` through the fibres of `Proj(Gr_I(A)) → Spec(Gr_I(A)₀)`, `AssociatedGraded.dInvariant`
  (`Stacks.LocalCohomology.UniformityIII.dInvariant_eq_fibreDim` in
  `BitUniformityIII/FibreDimensionAssociatedGraded.lean`), which is clause (2) of the source's
  paragraph defining `d`.
* `Hⁱ(X, ℱ) = 0` for `i > d(S)` holds for every **quasi-coherent** `ℱ`, not only for coherent
  ones (`subsingleton_blowupHmod_of_fibreDim_lt`). The input is [Stacks, Tag 02V7] at the stalks
  of the higher direct images, in the quasi-coherent form (in `Stacks.AlgebraicGeometry`)
  `FibreDimension.isZero_stalk_rightDerivedPlus_of_fiber_dimension_le_of_isQuasicoherent`, and
  the Leray comparison over the affine base `Spec A`
  (`Stacks.AlgebraicGeometry.LerayAffineBase.isZero_hgroup_of_isZero_rightDerivedPlus`), which
  turns the vanishing of `Rⁱp_*ℱ` into that of `Hⁱ(X, ℱ)`.

With `d(S)` available, the Situation of [Stacks, Tag 0GA6] is rebuilt at the source's own
integers: `blowupSituationAt I q₀ h` is `blowupSituationOf I q₀ h` with its field `d` replaced
by `fibreDim I` — the Čech bound used there is a valid but in general larger vanishing degree —
and `blowupSituationQS I` is the case `q₀ = q(S)`. The integer `q(S)` itself is
`Stacks.LocalCohomology.UniformityIII.qS`, and `qS_isLeast_isBaseThresholdUpTo_fibreDim` says it
is the least `q₀` such that for `q ≥ q₀` one has `Hⁱ(Y, 𝒪_Y(q)) = 0` for `1 ≤ i ≤ d(S)` and
`H⁰(Y, 𝒪_Y(q)) = Iᑫ/I^{q+1}`, which is the source's definition read with `d = d(S)`.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.fibreDim`: the integer `d(S)`.
* `Stacks.LocalCohomology.UniformityIII.blowupSituationAt`: the Situation of Tag 0GA6 on the
  blowup with `d = d(S)`, at a threshold `q₀` with the defining property of `q(S)`.
* `Stacks.LocalCohomology.UniformityIII.blowupSituationQS`: the same at `q₀ = q(S)`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.topologicalKrullDim_fiber_le_fibreDim` and
  `Stacks.LocalCohomology.UniformityIII.fibreDim_le`: `d(S)` is the maximum of the dimensions of
  the fibres of `p`.
* `Stacks.LocalCohomology.UniformityIII.subsingleton_blowupHmod_of_fibreDim_lt`:
  `Hⁱ(X, ℱ) = 0` for `ℱ` quasi-coherent and `i > d(S)`.

## References

* [Stacks Project, Tag 0GA6](https://stacks.math.columbia.edu/tag/0GA6)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
* [Stacks Project, Tag 0A3V](https://stacks.math.columbia.edu/tag/0A3V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- **The integer `d = d(S)` of [Stacks, Tag 0GA6]**: the maximum of the dimensions of the fibres
of the blowing up `p : X → Spec(A)` of `Spec(A)` in `I`, and `0` if `X = ∅`. It is the least
natural number bounding the topological Krull dimension of every fibre; that such a bound exists
for `A` Noetherian is `exists_forall_topologicalKrullDim_fiber_le`. -/
def fibreDim : ℕ :=
  sInf {D : ℕ | ∀ s : Spec (CommRingCat.of A),
    topologicalKrullDim ((Stacks.Blowup.toSpec I).fiber s) ≤ (D : WithBot ℕ∞)}

/-- **The dimensions of the fibres of the blowup are bounded** ([Stacks, Tag 0A3V]): the blowup
of a Noetherian affine scheme is of finite type over it, being proper. This is the source's
"this is well defined". -/
@[ega "IV 13.1.7" "special case"]
theorem exists_forall_topologicalKrullDim_fiber_le [IsNoetherianRing A] :
    ∃ D : ℕ, ∀ s : Spec (CommRingCat.of A),
      topologicalKrullDim ((Stacks.Blowup.toSpec I).fiber s) ≤ (D : WithBot ℕ∞) :=
  AlgebraicGeometry.exists_topologicalKrullDim_fiber_le (Stacks.Blowup.toSpec I)

/-- Every fibre of the blowup has dimension at most `d(S)`. -/
@[ega "IV 13.1.7" "special case"]
theorem topologicalKrullDim_fiber_le_fibreDim [IsNoetherianRing A] (s : Spec (CommRingCat.of A)) :
    topologicalKrullDim ((Stacks.Blowup.toSpec I).fiber s) ≤ (fibreDim I : WithBot ℕ∞) :=
  Nat.sInf_mem (exists_forall_topologicalKrullDim_fiber_le I) s

/-- `d(S)` is at most every bound for the dimensions of the fibres: together with
`topologicalKrullDim_fiber_le_fibreDim`, it is their maximum. -/
theorem fibreDim_le {D : ℕ} (h : ∀ s : Spec (CommRingCat.of A),
    topologicalKrullDim ((Stacks.Blowup.toSpec I).fiber s) ≤ (D : WithBot ℕ∞)) :
    fibreDim I ≤ D :=
  Nat.sInf_le h

/-- **`Hⁱ(X, ℱ) = 0` for `ℱ` quasi-coherent and `i > d(S)`**, as abelian groups: [Stacks,
Tag 02V7] at the stalks of the higher direct images `Rⁱp_*ℱ`, which therefore vanish, and the
Leray comparison over the affine base. -/
theorem isZero_blowupH_of_fibreDim_lt [IsNoetherianRing A] (F : (blowupScheme I).Modules)
    [F.IsQuasicoherent] {i : ℕ} (hi : fibreDim I < i) : IsZero (blowupH I i F) := by
  have hvan : ∀ q : ℕ, fibreDim I + 1 ≤ q →
      IsZero (((Scheme.Modules.pushforward (Stacks.Blowup.toSpec I)).rightDerivedPlus
        (q : ℤ)).obj F) := fun q hq =>
    isZero_of_forall_isZero_stalk _ fun s => open Stacks.AlgebraicGeometry in
      FibreDimension.isZero_stalk_rightDerivedPlus_of_fiber_dimension_le_of_isQuasicoherent
        (Stacks.Blowup.toSpec I) s (fibreDim I) (topologicalKrullDim_fiber_le_fibreDim I s) F
        (q : ℤ) (by lia)
  exact Stacks.AlgebraicGeometry.LerayAffineBase.isZero_hgroup_of_isZero_rightDerivedPlus
    (Stacks.Blowup.toSpec I) (fibreDim I + 1) F hvan i (by lia) (by lia)

/-- **`Hⁱ(X, ℱ) = 0` for `ℱ` quasi-coherent and `i > d(S)`**, as `A`-modules. This is the
observation of [Stacks, Tag 0GA6] that `d(S)` bounds the cohomological degrees on `X`, for
quasi-coherent rather than only coherent `ℱ`. -/
@[ega "III 3.2.3" "special case"]
theorem subsingleton_blowupHmod_of_fibreDim_lt [IsNoetherianRing A] (F : (blowupScheme I).Modules)
    [F.IsQuasicoherent] {i : ℕ} (hi : fibreDim I < i) : Subsingleton (blowupHmod I i F) :=
  subsingleton_blowupHmod I i F
    (AddCommGrpCat.subsingleton_of_isZero (isZero_blowupH_of_fibreDim_lt I F hi))

/-- **`q(S)` is the least integer satisfying the source's definition at `d = d(S)`**: `qS I` is
the least `q₀` such that for all `q ≥ q₀` one has `Hⁱ(Y, 𝒪_Y(q)) = 0` for `1 ≤ i ≤ d(S)` and
`H⁰(Y, 𝒪_Y(q)) = Iᑫ/I^{q+1}`. -/
theorem qS_isLeast_isBaseThresholdUpTo_fibreDim [IsNoetherianRing A] :
    IsLeast {q₀ | IsBaseThresholdUpTo I (fibreDim I) q₀} (qS I) :=
  qS_isLeast_isBaseThresholdUpTo I fun _ q hi =>
    subsingleton_blowupHmod_of_fibreDim_lt I (thickeningTwist I 1 q) hi

/-- **The Situation of [Stacks, Tag 0GA6] on the blowup with `d = d(S)`**, at every threshold
`q₀` with the defining property of `q(S)`: `blowupSituationOf I q₀ h` with the vanishing degree
`d` taken to be the maximal fibre dimension `fibreDim I`, the two vanishing fields being
`subsingleton_blowupHmod_of_fibreDim_lt`. -/
def blowupSituationAt [IsNoetherianRing A] (q₀ : ℕ) (h : IsBaseThreshold I q₀) :
    Situation A I :=
  { blowupSituationOf I q₀ h with
    d := fibreDim I
    base_vanishing := fun i q hi _ hq => h.1 i q hi hq
    div_vanishing_gt := fun n _ q hi =>
      subsingleton_blowupHmod_of_fibreDim_lt I (thickeningTwist I n q) hi
    amb_vanishing_gt := fun _ q hi =>
      subsingleton_blowupHmod_of_fibreDim_lt I (blowupTwist I q) hi }

/-- The Situation of [Stacks, Tag 0GA6] on the blowup at the source's own integers,
`d = d(S)` and `q₀ = q(S)`. -/
def blowupSituationQS [IsNoetherianRing A] : Situation A I :=
  blowupSituationAt I (qS I) (isBaseThreshold_qS I)

/-- The vanishing degree of `blowupSituationAt` is the maximal fibre dimension `fibreDim I`. -/
@[simp] theorem blowupSituationAt_d [IsNoetherianRing A] (q₀ : ℕ) (h : IsBaseThreshold I q₀) :
    (blowupSituationAt I q₀ h).d = fibreDim I :=
  rfl

/-- The threshold of `blowupSituationAt I q₀ h` is `q₀`. -/
@[simp] theorem blowupSituationAt_q₀ [IsNoetherianRing A] (q₀ : ℕ) (h : IsBaseThreshold I q₀) :
    (blowupSituationAt I q₀ h).q₀ = q₀ :=
  rfl

/-- The vanishing degree of `blowupSituationQS` is the maximal fibre dimension `fibreDim I`. -/
@[simp] theorem blowupSituationQS_d [IsNoetherianRing A] :
    (blowupSituationQS I).d = fibreDim I :=
  rfl

/-- The threshold of `blowupSituationQS` is `qS I`. -/
@[simp] theorem blowupSituationQS_q₀ [IsNoetherianRing A] :
    (blowupSituationQS I).q₀ = qS I :=
  rfl

end Stacks.LocalCohomology.UniformityIII

end
