module

public import StacksFrontier.RingTheory.Smoothing.TwistedQuotientResolution

/-!
# Localizing the twisted quotient chain of Stacks 07FJ

The proof of Stacks 07FJ is a twenty-six item argument. Items (1)–(17) are carried out in
`StacksFrontier.RingTheory.Smoothing.PositiveCharacteristicResolution` and item (20) in
`StacksFrontier.RingTheory.Smoothing.TwistedQuotientResolution`, which together reduce 07FJ to
`Stacks.Smoothing.HasArtinianApproximationData` (item (9), Stacks 07FT) and
`Stacks.Smoothing.TwistedQuotientLocallyResolvable` (items (22)–(26), Stacks 07G6, 07G7, 07G8,
07G9 and 07GA).

This file carries out items (22) and (23) — Stacks 07G6 and 07G7 — in a form general enough to
be applied to the twisted quotient chain, together with the localization models they are stated
over, and then applies them to that chain. The result is
`Stacks.Smoothing.twistedQuotientLocallyResolvable_of_smoothFactorization`, which reduces
`Stacks.Smoothing.TwistedQuotientLocallyResolvable` to items (24)–(26) alone, in the form of the
single residual hypothesis `Stacks.Smoothing.TwistedQuotientSmoothFactorization`.

A `Stacks.Smoothing.LocalSmoothingSituation` `R → A → Λ ⊃ 𝔮` has three canonical localizations:
`R_𝔭` at the base prime `𝔭 = R ∩ 𝔮`, the localization `A_𝔭` of `A` at the image of `R ∖ 𝔭`, and
`Λ_𝔮`. These are `locBase`, `locMid` and `locTarget` below; `locBase` and `locMid` already carry
the structure maps Mathlib provides for a localization of an algebra, and the two maps into
`locTarget` are the localizations of `R → Λ` and `A → Λ` at `𝔮`. Exhibiting these three with
their compatibilities is exactly the data
`Stacks.Smoothing.LocalSmoothingSituation.IsResolvableAfterLocalizing` asks for, so that
predicate reduces to resolvability of `R_𝔭 → A_𝔭 → Λ_𝔮`.

The content of items (22) and (23) is then one base change. In the source, item (22) passes from
the chain over `(R/I)_𝔯` to the chain over `(R/JR)_𝔭` and item (23) from there to the chain over
`(R/𝔭ⁿR)_𝔭`; each step replaces the base by one it is a base change of, and `A` is throughout
the base change of a fixed `k[x_1, …, x_d]`-algebra `C`. Since a composite of base changes is a
base change, both steps together are the single statement
`Stacks.Smoothing.isResolvableAfterLocalizing_of_hasSmoothFactorization`: a smooth factorization
of the chain over any base `R₀` mapping to `R_𝔭` compatibly, with middle term the base change of
`C` along `k[x_1, …, x_d] → R₀`, makes the original chain resolvable after localizing. Over a
local Artinian target resolvability *is* the existence of a smooth factorization, which is why
the two source items can be run in that form — this is `canBeResolved_of_hasSmoothFactorization`
and `hasSmoothFactorization_baseChange` of
`StacksFrontier.RingTheory.Smoothing.ArtinianFactorizationDescent`.

The auxiliary chain over `Λ₀[t_1, …, t_d]` with `Λ₀ = k[y_1, …, y_m]_𝔭/𝔭ⁿ`, its two structure
maps and all the compatibilities between them are built here. What is **not** done is the smooth
factorization of that chain, namely items (24)–(26) (Stacks 07G8, 07G9, 07GA), which is left as
the hypothesis `Stacks.Smoothing.TwistedQuotientSmoothFactorization`: that definition repeats the
telescope of `TwistedQuotientLocallyResolvable` up to its `hcompat` and asks only for a smooth
`Λ₀[t_1, …, t_d]`-algebra through which `C → Λ_𝔮/𝔮ⁿΛ_𝔮` factors. No localization or quotient of
the chain occurs in it.

## Main definitions

* `Stacks.Smoothing.LocalSmoothingSituation.locBase`,
  `Stacks.Smoothing.LocalSmoothingSituation.locMid`,
  `Stacks.Smoothing.LocalSmoothingSituation.locTarget`: the three localizations `R_𝔭`, `A_𝔭`,
  `Λ_𝔮` of a local smoothing situation.
* `Stacks.Smoothing.ExistsTwistedSmoothFactorization`: the conclusion of items (24)–(26) at one
  choice of the data of item (18).
* `Stacks.Smoothing.TwistedQuotientSmoothFactorization`: items (24)–(26), Stacks 07G8, 07G9 and
  07GA, as a standing hypothesis over the whole telescope of item (18).

## Main results

* `Stacks.Smoothing.isResolvableAfterLocalizing_of_hasSmoothFactorization`: items (22) and (23)
  of the proof of Stacks 07FJ.
* `Stacks.Smoothing.isResolvableAfterLocalizing_of_hasSmoothFactorization_tensor`: the same with
  the middle term of the auxiliary chain built as `R₀ ⊗_{k[x]} C`.
* `Stacks.Smoothing.primePowerQuotient_ringHom_ext`: two maps out of `R_𝔭/𝔭ⁿR_𝔭` agreeing on
  the images of `R` are equal.
* `Stacks.Smoothing.exists_primePowerQuotient_lift`: a map inverting `R ∖ 𝔭` and killing the
  `e`-th powers of a regular system of parameters factors through `R_𝔭/𝔭ⁿR_𝔭`.
* `Stacks.Smoothing.algebraMap_locTarget_comp_eq_of_quotient`: the compatibility hypothesis of
  the two previous theorems, in the form items (22)–(26) supply it.
* `Stacks.Smoothing.primePowerQuotient_map_algebraMap`: the structure map
  `Λ₀ = k[y_1, …, y_m]_𝔭/𝔭ⁿ → Λ̄ = Λ_𝔮/𝔮ⁿΛ_𝔮` of items (22)–(26) is `φ` on the image of
  `k[y_1, …, y_m]`.
* `Stacks.Smoothing.eval₂Hom_comp_twistedStructure`: the `k[x_1, …, x_d]`-algebra structure on
  `Λ₀[t_1, …, t_d]` of items (22)–(26), pinned down on generators.
* `Stacks.Smoothing.exists_twistedLocBaseLift`: the structure map
  `Λ₀ = k[y_1, …, y_m]_𝔭/𝔭ⁿ → (R/I)_𝔯` of item (23).
* `Stacks.Smoothing.hasSmoothFactorization_tensor_of_exists` and
  `Stacks.Smoothing.exists_of_hasSmoothFactorization_tensor`: a joint factorization of
  `R₀ → L₀` and `C → L₀` through a smooth `R₀`-algebra is the *same datum* as a smooth
  factorization of `R₀ → R₀ ⊗_{k[x]} C → L₀`.
* `Stacks.Smoothing.isPushout_locBase_locMid`: the localized chain is again the base change of
  `C`, which is what makes that base change available.
* `Stacks.Smoothing.isPushout_quotient_of_isPushout`: a base change square stays one after
  dividing by an ideal of the base.
* `Stacks.Smoothing.LocalSmoothingSituation.map_q_locTarget_ne_top`: the prime of the localized
  target is not the unit ideal.
* `Stacks.Smoothing.isResolvableAfterLocalizing_twistedQuotient`: the assembly of items (22) and
  (23) at the twisted quotient chain, with the chain opaque.
* `Stacks.Smoothing.twistedQuotientLocallyResolvable_of_smoothFactorization`: items (22)–(26)
  from items (24)–(26).

## Implementation notes

`isResolvableAfterLocalizing_of_hasSmoothFactorization` is stated with the auxiliary chain
`R₀ → A₀ → L₀` and its maps to the localized chain as hypotheses rather than constructed,
because the two source items are instances of it for two different `R₀` and the composite is a
third. Its hypothesis `hC` is the only non-instance compatibility: the square
`C → A₀ → L₀ → Λ_𝔮` equals `C → A → A_𝔭 → Λ_𝔮`.

The assembly of items (22)–(26) at the twisted quotient chain
`R/I → (R ⊗_{k[x]} C)/I → Λ/IΛ ⊃ 𝔮/IΛ`, with `R = k[y_1, …, y_m, t_1, …, t_d]`,
`γ_i = π_i t_i`, `e = 8c` and `I = (γ_1^e, …, γ_d^e)`, runs as follows. The base change square
`Algebra.IsPushout k[x] (R/I) C ((R ⊗_{k[x]} C)/I)` is `isPushout_quotient_of_isPushout`; the
extension `IΛ` of `I` to `Λ` is `((δ_iφ(π_i))^e)` and lies in `𝔮`, so `𝔮/IΛ` has `𝔮` as
preimage; the two structure maps of the chain over `Λ₀[t_1, …, t_d]` come from
`exists_twistedLocBaseLift` and `exists_primePowerQuotient_lift`, the scalar towers between them
from `eval₂Hom_comp_twistedStructure`, and the compatibility of the two maps out of `C` from
`algebraMap_locTarget_comp_eq_of_quotient`; and
`isResolvableAfterLocalizing_of_hasSmoothFactorization_tensor` finishes. Only items (24)–(26) —
Stacks 07G8, 07G9, 07GA — are left over: the smooth factorization of
`Λ₀[t] → Λ₀[t] ⊗_{k[x]} C → Λ_𝔮/𝔮ⁿΛ_𝔮` through `D'[t_1, …, t_d]`
(`Stacks.Smoothing.canBeResolved_of_factorization_mvPolynomial` and
`Stacks.Smoothing.exists_algHom_parameterPowerAlgebra_mvPolynomial`) together with the passage
from `B` back to `C` through the retraction `grt`
(`Stacks.Smoothing.hasSmoothFactorization_of_algHom`).

The assembly is written over the whole telescope of `TwistedQuotientLocallyResolvable` and so
must be split across top-level lemmas: in one tactic block it exceeds the default elaboration
budget, because the rings of the situation are written out as localizations of quotients of a
tensor product and every instance search and definitional check unfolds them. That is why the
theorems here take the rings of the situation as opaque variables and the structure maps as
hypotheses; each piece is then cheap. In particular
`isResolvableAfterLocalizing_twistedQuotient` carries out everything from the structure maps
onwards with the situation a variable, and
`twistedQuotientLocallyResolvable_of_smoothFactorization` only has to build the situation, the
base change square, the ideal `IΛ` and the half-dozen pointwise compatibilities that identify
the opaque rings with the written-out ones.

That the residual hypothesis is not accidentally over-strong is itself checked: by
`hasSmoothFactorization_tensor_of_exists` and `exists_of_hasSmoothFactorization_tensor` the
conclusion of `ExistsTwistedSmoothFactorization` is *equivalent* to
`HasSmoothFactorization (Λ₀[t_1, …, t_d]) (Λ₀[t_1, …, t_d] ⊗_{k[x]} C) (Λ_𝔮/𝔮ⁿΛ_𝔮)`, which is
exactly what the source's items (24)–(26) produce; and
`TwistedQuotientSmoothFactorization` repeats the telescope of
`TwistedQuotientLocallyResolvable`, so every datum and every hypothesis available at that point
of the source proof is available to a prover of the residual. The residual is in fact discharged,
in `StacksFrontier.RingTheory.Smoothing.TwistedQuotientClosure`, from the items (24)–(26) of
`StacksFrontier.RingTheory.Smoothing.SmoothFactorizationFromParameters`; so
`Stacks.Smoothing.twistedQuotientLocallyResolvable` is unconditional and the only hypothesis
Stacks 07FJ still owes is `Stacks.Smoothing.HasArtinianApproximationData`.

## References

* [Stacks Project, Tag 07FJ](https://stacks.math.columbia.edu/tag/07FJ)
* [Stacks Project, Tag 07G6](https://stacks.math.columbia.edu/tag/07G6)
* [Stacks Project, Tag 07G7](https://stacks.math.columbia.edu/tag/07G7)
* [Stacks Project, Tag 07G8](https://stacks.math.columbia.edu/tag/07G8)
* [Stacks Project, Tag 07G9](https://stacks.math.columbia.edu/tag/07G9)
* [Stacks Project, Tag 07GA](https://stacks.math.columbia.edu/tag/07GA)
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

namespace Stacks.Smoothing

universe u

namespace LocalSmoothingSituation

variable (Sit : LocalSmoothingSituation.{u, u, u})

/-- `R_𝔭`. -/
abbrev locBase : Type u := Localization.AtPrime Sit.basePrime

/-- `A_𝔭`. -/
abbrev locMid : Type u :=
  Localization (Algebra.algebraMapSubmonoid Sit.A Sit.basePrime.primeCompl)

/-- `Λ_𝔮`. -/
abbrev locTarget : Type u := Localization.AtPrime Sit.q

/-- Every element of `R ∖ 𝔭` maps to a unit of `Λ_𝔮`. -/
theorem isUnit_algebraMap_locTarget_of_primeCompl (s : Sit.basePrime.primeCompl) :
    IsUnit (algebraMap Sit.R (locTarget Sit) (s : Sit.R)) := by
  rw [IsScalarTower.algebraMap_apply Sit.R Sit.Λ (locTarget Sit)]
  exact IsLocalization.map_units (locTarget Sit)
    (⟨algebraMap Sit.R Sit.Λ (s : Sit.R), s.2⟩ : Sit.q.primeCompl)

/-- Every element of the image of `R ∖ 𝔭` in `A` maps to a unit of `Λ_𝔮`. -/
theorem isUnit_algebraMap_locTarget
    (s : Algebra.algebraMapSubmonoid Sit.A Sit.basePrime.primeCompl) :
    IsUnit (algebraMap Sit.A (locTarget Sit) (s : Sit.A)) := by
  obtain ⟨x, hx, hxs⟩ := s.2
  rw [← hxs, ← IsScalarTower.algebraMap_apply Sit.R Sit.A (locTarget Sit)]
  exact isUnit_algebraMap_locTarget_of_primeCompl Sit ⟨x, hx⟩

/-- The `A_𝔭`-algebra structure on `Λ_𝔮` induced by `A → Λ_𝔮`. -/
noncomputable instance algebraLocMidLocTarget : Algebra (locMid Sit) (locTarget Sit) :=
  (IsLocalization.lift (M := Algebra.algebraMapSubmonoid Sit.A Sit.basePrime.primeCompl)
    (S := locMid Sit) (isUnit_algebraMap_locTarget Sit)).toAlgebra

/-- The composite `A → A_𝔭 → Λ_𝔮` is the structure map `A → Λ_𝔮`. -/
instance isScalarTower_mid_locMid_locTarget : IsScalarTower Sit.A (locMid Sit) (locTarget Sit) :=
  IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.lift_eq (M := Algebra.algebraMapSubmonoid Sit.A Sit.basePrime.primeCompl)
      (S := locMid Sit) (isUnit_algebraMap_locTarget Sit) x).symm

/-- The `R_𝔭`-algebra structure on `Λ_𝔮` induced by `R → Λ_𝔮`. -/
noncomputable instance algebraLocBaseLocTarget : Algebra (locBase Sit) (locTarget Sit) :=
  (IsLocalization.lift (M := Sit.basePrime.primeCompl) (S := locBase Sit)
    (isUnit_algebraMap_locTarget_of_primeCompl Sit)).toAlgebra

/-- The composite `R → R_𝔭 → Λ_𝔮` is the structure map `R → Λ_𝔮`. -/
instance isScalarTower_base_locBase_locTarget :
    IsScalarTower Sit.R (locBase Sit) (locTarget Sit) :=
  IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.lift_eq (M := Sit.basePrime.primeCompl) (S := locBase Sit)
      (isUnit_algebraMap_locTarget_of_primeCompl Sit) x).symm

/-- The square `R_𝔭 → A_𝔭 → Λ_𝔮` equals `R_𝔭 → Λ_𝔮`. -/
instance isScalarTower_locBase_locMid_locTarget :
    IsScalarTower (locBase Sit) (locMid Sit) (locTarget Sit) := by
  refine IsScalarTower.of_algebraMap_eq' (IsLocalization.ringHom_ext Sit.basePrime.primeCompl
    (RingHom.ext fun x => ?_))
  change algebraMap (locBase Sit) (locTarget Sit) (algebraMap Sit.R (locBase Sit) x) =
    algebraMap (locMid Sit) (locTarget Sit)
      (algebraMap (locBase Sit) (locMid Sit) (algebraMap Sit.R (locBase Sit) x))
  rw [← IsScalarTower.algebraMap_apply Sit.R (locBase Sit) (locMid Sit),
    ← IsScalarTower.algebraMap_apply Sit.R (locBase Sit) (locTarget Sit),
    IsScalarTower.algebraMap_apply Sit.R Sit.A (locMid Sit),
    ← IsScalarTower.algebraMap_apply Sit.A (locMid Sit) (locTarget Sit),
    ← IsScalarTower.algebraMap_apply Sit.R Sit.A (locTarget Sit)]

/-- The prime of the localized target is not the unit ideal. -/
theorem map_q_locTarget_ne_top : Ideal.map (algebraMap Sit.Λ (locTarget Sit)) Sit.q ≠ ⊤ := by
  rw [IsLocalization.AtPrime.map_eq_maximalIdeal Sit.q (locTarget Sit)]
  exact (maximalIdeal.isMaximal (locTarget Sit)).ne_top

end LocalSmoothingSituation

section Core

open LocalSmoothingSituation

/-- The composite `k[x] → (R/I)_𝔯 → (A/ID)_𝔯` is the structure map. -/
instance isScalarTower_locBase_locMid (Sit : LocalSmoothingSituation.{u, u, u}) (kx : Type u)
    [CommRing kx] [Algebra kx Sit.R] [Algebra kx Sit.A] [IsScalarTower kx Sit.R Sit.A] :
    IsScalarTower kx (locBase Sit) (locMid Sit) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply kx Sit.R (locBase Sit),
      ← IsScalarTower.algebraMap_apply Sit.R (locBase Sit) (locMid Sit),
      IsScalarTower.algebraMap_apply Sit.R Sit.A (locMid Sit),
      ← IsScalarTower.algebraMap_apply kx Sit.R Sit.A,
      ← IsScalarTower.algebraMap_apply kx Sit.A (locMid Sit)]

/-- **Stacks 07FJ, item (22)** in its pushout form: the localized chain is the base change of
`C` along `k[x] → (R/I)_𝔯`. -/
theorem isPushout_locBase_locMid (Sit : LocalSmoothingSituation.{u, u, u}) (kx C : Type u)
    [CommRing kx] [CommRing C]
    [Algebra kx C] [Algebra kx Sit.R] [Algebra C Sit.A] [Algebra kx Sit.A]
    [IsScalarTower kx Sit.R Sit.A] [IsScalarTower kx C Sit.A]
    [Algebra.IsPushout kx Sit.R C Sit.A] :
    Algebra.IsPushout kx (locBase Sit) C (locMid Sit) :=
  (Algebra.IsPushout.comp_iff kx Sit.R C Sit.A).mpr
    (Algebra.IsPushout.symm (Algebra.isPushout_of_isLocalization Sit.basePrime.primeCompl
      (locBase Sit) Sit.A (locMid Sit)))

/-- **Stacks 07FJ, items (22) and (23).** Let `R → A → Λ ⊃ 𝔮` be a chain whose middle term is
the base change of a `k[x]`-algebra `C`, and let `R₀ → A₀ → L₀` be a second such chain, with
`A₀` the base change of the same `C` along `k[x] → R₀`, together with a map of the second chain
to the localization of the first. If the chain over `R₀` has a smooth factorization, then the
localized chain over `R_𝔭` can be resolved; that is, the original chain is resolvable after
localizing.

The two source items are both instances of this: item (22) (tag 07G6) is the base change along
`(R/JR)_𝔭 → (R/I)_𝔯` and item (23) (tag 07G7) the one along `(R/𝔭ⁿR)_𝔭 → (R/JR)_𝔭`, and a
composite of base changes is a base change. -/
theorem isResolvableAfterLocalizing_of_hasSmoothFactorization
    (Sit : LocalSmoothingSituation.{u, u, u}) (kx C R₀ A₀ L₀ : Type u)
    [CommRing kx] [CommRing C] [CommRing R₀] [CommRing A₀] [CommRing L₀]
    [Algebra kx C] [Algebra kx Sit.R] [Algebra C Sit.A] [Algebra kx Sit.A]
    [IsScalarTower kx Sit.R Sit.A] [IsScalarTower kx C Sit.A]
    [Algebra.IsPushout kx Sit.R C Sit.A]
    [Algebra kx R₀] [Algebra R₀ A₀] [Algebra C A₀] [Algebra kx A₀]
    [IsScalarTower kx R₀ A₀] [IsScalarTower kx C A₀] [Algebra.IsPushout kx R₀ C A₀]
    [Algebra R₀ L₀] [Algebra A₀ L₀] [Algebra C L₀]
    [IsScalarTower R₀ A₀ L₀] [IsScalarTower C A₀ L₀]
    [Algebra R₀ (locBase Sit)] [IsScalarTower kx R₀ (locBase Sit)]
    [Algebra L₀ (locTarget Sit)] [Algebra R₀ (locTarget Sit)]
    [IsScalarTower R₀ L₀ (locTarget Sit)]
    [IsScalarTower R₀ (locBase Sit) (locTarget Sit)]
    (hC : ∀ c : C, algebraMap L₀ (locTarget Sit) (algebraMap C L₀ c)
      = algebraMap Sit.A (locTarget Sit) (algebraMap C Sit.A c))
    (h : HasSmoothFactorization R₀ A₀ L₀) :
    Sit.IsResolvableAfterLocalizing := by
  -- `R₀ → (A/ID)_𝔯` through `(R/I)_𝔯`
  let instR₀M : Algebra R₀ (locMid Sit) :=
    ((algebraMap (locBase Sit) (locMid Sit)).comp (algebraMap R₀ (locBase Sit))).toAlgebra
  have instTR₀BM : IsScalarTower R₀ (locBase Sit) (locMid Sit) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have instTkxR₀M : IsScalarTower kx R₀ (locMid Sit) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply R₀ (locBase Sit) (locMid Sit),
        ← IsScalarTower.algebraMap_apply kx R₀ (locBase Sit),
        ← IsScalarTower.algebraMap_apply kx (locBase Sit) (locMid Sit)]
  -- `A₀ → (A/ID)_𝔯`
  let instA₀M : Algebra A₀ (locMid Sit) :=
    (Algebra.pushoutDesc A₀ (IsScalarTower.toAlgHom kx R₀ (locMid Sit))
      (IsScalarTower.toAlgHom kx C (locMid Sit))
      (fun _ _ => Commute.all _ _)).toRingHom.toAlgebra
  have instTR₀A₀M : IsScalarTower R₀ A₀ (locMid Sit) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (Algebra.pushoutDesc_left A₀ (IsScalarTower.toAlgHom kx R₀ (locMid Sit))
        (IsScalarTower.toAlgHom kx C (locMid Sit)) (fun _ _ => Commute.all _ _) x).symm
  have instTCA₀M : IsScalarTower C A₀ (locMid Sit) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (Algebra.pushoutDesc_right A₀ (IsScalarTower.toAlgHom kx R₀ (locMid Sit))
        (IsScalarTower.toAlgHom kx C (locMid Sit)) (fun _ _ => Commute.all _ _) x).symm
  have instTkxA₀M : IsScalarTower kx A₀ (locMid Sit) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply kx R₀ A₀,
        ← IsScalarTower.algebraMap_apply R₀ A₀ (locMid Sit),
        ← IsScalarTower.algebraMap_apply kx R₀ (locMid Sit)]
  -- `A₀ → Λ_𝔮`
  let instA₀T : Algebra A₀ (locTarget Sit) :=
    ((algebraMap (locMid Sit) (locTarget Sit)).comp (algebraMap A₀ (locMid Sit))).toAlgebra
  have instTA₀MT : IsScalarTower A₀ (locMid Sit) (locTarget Sit) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let instkxT : Algebra kx (locTarget Sit) :=
    ((algebraMap (locMid Sit) (locTarget Sit)).comp (algebraMap kx (locMid Sit))).toAlgebra
  have instTkxMT : IsScalarTower kx (locMid Sit) (locTarget Sit) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have instTkxA₀T : IsScalarTower kx A₀ (locTarget Sit) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply A₀ (locMid Sit) (locTarget Sit),
        ← IsScalarTower.algebraMap_apply kx A₀ (locMid Sit),
        ← IsScalarTower.algebraMap_apply kx (locMid Sit) (locTarget Sit)]
  have instTkxR₀T : IsScalarTower kx R₀ (locTarget Sit) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply R₀ (locBase Sit) (locTarget Sit),
        ← IsScalarTower.algebraMap_apply kx R₀ (locBase Sit),
        IsScalarTower.algebraMap_apply kx (locMid Sit) (locTarget Sit),
        IsScalarTower.algebraMap_apply kx (locBase Sit) (locMid Sit),
        ← IsScalarTower.algebraMap_apply (locBase Sit) (locMid Sit) (locTarget Sit)]
  let instkxL₀ : Algebra kx L₀ := ((algebraMap R₀ L₀).comp (algebraMap kx R₀)).toAlgebra
  have instTkxR₀L₀ : IsScalarTower kx R₀ L₀ := IsScalarTower.of_algebraMap_eq' rfl
  have instTkxA₀L₀ : IsScalarTower kx A₀ L₀ :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply kx R₀ A₀,
        ← IsScalarTower.algebraMap_apply R₀ A₀ L₀,
        ← IsScalarTower.algebraMap_apply kx R₀ L₀]
  have instTkxL₀T : IsScalarTower kx L₀ (locTarget Sit) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply kx R₀ L₀,
        ← IsScalarTower.algebraMap_apply R₀ L₀ (locTarget Sit),
        ← IsScalarTower.algebraMap_apply kx R₀ (locTarget Sit)]
  have instTR₀A₀T : IsScalarTower R₀ A₀ (locTarget Sit) :=
    IsScalarTower.of_algebraMap_eq fun y => by
      rw [IsScalarTower.algebraMap_apply A₀ (locMid Sit) (locTarget Sit),
        ← IsScalarTower.algebraMap_apply R₀ A₀ (locMid Sit),
        IsScalarTower.algebraMap_apply R₀ (locBase Sit) (locMid Sit),
        ← IsScalarTower.algebraMap_apply (locBase Sit) (locMid Sit) (locTarget Sit),
        ← IsScalarTower.algebraMap_apply R₀ (locBase Sit) (locTarget Sit)]
  -- the square `A₀ → L₀ → Λ_𝔮` equals `A₀ → (A/ID)_𝔯 → Λ_𝔮`
  have key : (IsScalarTower.toAlgHom kx A₀ (locTarget Sit)) =
      ((IsScalarTower.toAlgHom R₀ L₀ (locTarget Sit)).restrictScalars kx).comp
        (IsScalarTower.toAlgHom kx A₀ L₀) := by
    refine Algebra.IsPushout.algHom_ext (R := kx) (S := R₀) (R' := C) A₀
      (AlgHom.ext fun x => ?_) (AlgHom.ext fun x => ?_)
    · change algebraMap A₀ (locTarget Sit) (algebraMap C A₀ x) =
        algebraMap L₀ (locTarget Sit) (algebraMap A₀ L₀ (algebraMap C A₀ x))
      rw [← IsScalarTower.algebraMap_apply C A₀ L₀, hC,
        IsScalarTower.algebraMap_apply A₀ (locMid Sit) (locTarget Sit),
        ← IsScalarTower.algebraMap_apply C A₀ (locMid Sit),
        IsScalarTower.algebraMap_apply C Sit.A (locMid Sit),
        ← IsScalarTower.algebraMap_apply Sit.A (locMid Sit) (locTarget Sit)]
    · change algebraMap A₀ (locTarget Sit) (algebraMap R₀ A₀ x) =
        algebraMap L₀ (locTarget Sit) (algebraMap A₀ L₀ (algebraMap R₀ A₀ x))
      rw [← IsScalarTower.algebraMap_apply R₀ A₀ (locTarget Sit),
        ← IsScalarTower.algebraMap_apply R₀ A₀ L₀,
        ← IsScalarTower.algebraMap_apply R₀ L₀ (locTarget Sit)]
  have instTA₀L₀T : IsScalarTower A₀ L₀ (locTarget Sit) :=
    IsScalarTower.of_algebraMap_eq fun x => AlgHom.congr_fun key x
  -- the base-change square
  have instPush : Algebra.IsPushout R₀ A₀ (locBase Sit) (locMid Sit) :=
    Algebra.IsPushout.symm
      ((Algebra.IsPushout.comp_iff kx R₀ C A₀).mp (isPushout_locBase_locMid Sit kx C))
  refine ⟨locBase Sit, inferInstance, inferInstance, inferInstance,
    locMid Sit, inferInstance, inferInstance, inferInstance, inferInstance,
      Localization.isLocalization, inferInstance, inferInstance,
    locTarget Sit, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact canBeResolved_of_hasSmoothFactorization (map_q_locTarget_ne_top Sit)
    (hasSmoothFactorization_baseChange h)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The lift out of `R₀ ⊗_{k[x]} C` restricts to the given map on the left factor. -/
private theorem lift_algebraMap_left {kx R₀ C L : Type*} [CommRing kx] [CommRing R₀] [CommRing C]
    [CommRing L] [Algebra kx R₀] [Algebra kx C] [Algebra kx L] (f : R₀ →ₐ[kx] L) (g : C →ₐ[kx] L)
    (hfg : ∀ x y, Commute (f x) (g y)) (x : R₀) :
    Algebra.TensorProduct.lift f g hfg (algebraMap R₀ (R₀ ⊗[kx] C) x) = f x :=
  AlgHom.congr_fun (Algebra.TensorProduct.lift_comp_includeLeft f g hfg) x

/-- The lift out of `R₀ ⊗_{k[x]} C` restricts to the given map on the right factor. -/
private theorem lift_algebraMap_right {kx R₀ C L : Type*} [CommRing kx] [CommRing R₀] [CommRing C]
    [CommRing L] [Algebra kx R₀] [Algebra kx C] [Algebra kx L] (f : R₀ →ₐ[kx] L) (g : C →ₐ[kx] L)
    (hfg : ∀ x y, Commute (f x) (g y)) (c : C) :
    Algebra.TensorProduct.lift f g hfg (algebraMap C (R₀ ⊗[kx] C) c) = g c :=
  AlgHom.congr_fun (Algebra.TensorProduct.lift_comp_includeRight' f g hfg) c

section Tensor

variable (kx C R₀ L₀ : Type u) [CommRing kx] [CommRing C] [CommRing R₀] [CommRing L₀]
  [Algebra kx C] [Algebra kx R₀] [Algebra kx L₀] [Algebra R₀ L₀] [Algebra C L₀]
  [IsScalarTower kx R₀ L₀] [IsScalarTower kx C L₀]

/-- The algebra structure on `R₀ ⊗_{k[x]} C` over a `k[x]`-algebra `L₀` receiving both factors
compatibly. -/
@[instance_reducible]
noncomputable def tensorLiftAlgebra : Algebra (R₀ ⊗[kx] C) L₀ :=
  (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom kx R₀ L₀)
    (IsScalarTower.toAlgHom kx C L₀) fun _ _ => Commute.all _ _).toRingHom.toAlgebra

/-- `R₀ → R₀ ⊗_{k[x]} C → L₀` is the given map `R₀ → L₀`. -/
theorem isScalarTower_left_tensorLiftAlgebra :
    letI := tensorLiftAlgebra kx C R₀ L₀
    IsScalarTower R₀ (R₀ ⊗[kx] C) L₀ := by
  let := tensorLiftAlgebra kx C R₀ L₀
  exact IsScalarTower.of_algebraMap_eq fun x =>
    (lift_algebraMap_left (IsScalarTower.toAlgHom kx R₀ L₀) (IsScalarTower.toAlgHom kx C L₀)
      (fun _ _ => Commute.all _ _) x).symm

/-- `C → R₀ ⊗_{k[x]} C → L₀` is the given map `C → L₀`. -/
theorem isScalarTower_right_tensorLiftAlgebra :
    letI := tensorLiftAlgebra kx C R₀ L₀
    IsScalarTower C (R₀ ⊗[kx] C) L₀ := by
  let := tensorLiftAlgebra kx C R₀ L₀
  exact IsScalarTower.of_algebraMap_eq fun x =>
    (lift_algebraMap_right (IsScalarTower.toAlgHom kx R₀ L₀) (IsScalarTower.toAlgHom kx C L₀)
      (fun _ _ => Commute.all _ _) x).symm

end Tensor

/-- A joint factorization of the two maps `R₀ → L₀` and `C → L₀` through an `R₀`-algebra smooth
over `R₀` is a smooth factorization of the chain `R₀ → R₀ ⊗_{k[x]} C → L₀`. This is the shape in
which items (24)–(26) of the proof of Stacks 07FJ produce one: a smooth `R₀`-algebra `T`, a ring
map `C → T` over `k[x]`, and a ring map `T → L₀` over `R₀` compatible with `C → L₀`. -/
theorem hasSmoothFactorization_tensor_of_exists (kx C R₀ L₀ : Type u)
    [CommRing kx] [CommRing C] [CommRing R₀] [CommRing L₀]
    [Algebra kx C] [Algebra kx R₀] [Algebra kx L₀] [Algebra R₀ L₀] [Algebra C L₀]
    [IsScalarTower kx R₀ L₀] [IsScalarTower kx C L₀]
    (h : ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R₀ T), Algebra.Smooth R₀ T ∧
      ∃ (gC : C →+* T) (kk : T →+* L₀),
        (∀ x : kx, gC (algebraMap kx C x) = algebraMap R₀ T (algebraMap kx R₀ x)) ∧
        (∀ x : R₀, kk (algebraMap R₀ T x) = algebraMap R₀ L₀ x) ∧
        ∀ c : C, kk (gC c) = algebraMap C L₀ c) :
    letI := tensorLiftAlgebra kx C R₀ L₀
    haveI := isScalarTower_left_tensorLiftAlgebra kx C R₀ L₀
    HasSmoothFactorization R₀ (R₀ ⊗[kx] C) L₀ := by
  obtain ⟨T, instT, instR₀T, hsm, gC, kk, hgCkx, hkkR₀, hkkC⟩ := h
  let := instT
  let := instR₀T
  let := tensorLiftAlgebra kx C R₀ L₀
  have := isScalarTower_left_tensorLiftAlgebra kx C R₀ L₀
  have := isScalarTower_right_tensorLiftAlgebra kx C R₀ L₀
  let instkxT : Algebra kx T := ((algebraMap R₀ T).comp (algebraMap kx R₀)).toAlgebra
  have instTkxR₀T : IsScalarTower kx R₀ T := IsScalarTower.of_algebraMap_eq' rfl
  let gCalg : C →ₐ[kx] T := { toRingHom := gC, commutes' := hgCkx }
  let gg : (R₀ ⊗[kx] C) →ₐ[kx] T :=
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom kx R₀ T) gCalg
      (fun _ _ => Commute.all _ _)
  have hggleft : ∀ x : R₀, gg (algebraMap R₀ (R₀ ⊗[kx] C) x) = algebraMap R₀ T x :=
    lift_algebraMap_left (IsScalarTower.toAlgHom kx R₀ T) gCalg _
  have hggright : ∀ c : C, gg (algebraMap C (R₀ ⊗[kx] C) c) = gC c :=
    lift_algebraMap_right (IsScalarTower.toAlgHom kx R₀ T) gCalg _
  have hkkkx : ∀ x : kx, kk (algebraMap kx T x) = algebraMap kx L₀ x := by
    intro x
    change kk (algebraMap R₀ T (algebraMap kx R₀ x)) = _
    rw [hkkR₀, ← IsScalarTower.algebraMap_apply kx R₀ L₀]
  have key : ({ toRingHom := kk, commutes' := hkkkx } : T →ₐ[kx] L₀).comp gg =
      IsScalarTower.toAlgHom kx (R₀ ⊗[kx] C) L₀ := by
    refine Algebra.IsPushout.algHom_ext (R := kx) (S := R₀) (R' := C) (R₀ ⊗[kx] C)
      (AlgHom.ext fun c => ?_) (AlgHom.ext fun x => ?_)
    · change kk (gg (algebraMap C (R₀ ⊗[kx] C) c)) = _
      rw [hggright, hkkC, IsScalarTower.algebraMap_apply C (R₀ ⊗[kx] C) L₀]
      rfl
    · change kk (gg (algebraMap R₀ (R₀ ⊗[kx] C) x)) = _
      rw [hggleft, hkkR₀, IsScalarTower.algebraMap_apply R₀ (R₀ ⊗[kx] C) L₀]
      rfl
  exact ⟨T, instT, instR₀T, hsm, { toRingHom := (gg : _ →+* T), commutes' := hggleft },
    { toRingHom := kk, commutes' := hkkR₀ }, AlgHom.ext fun y => AlgHom.congr_fun key y⟩

/-- **The converse of `Stacks.Smoothing.hasSmoothFactorization_tensor_of_exists`.** A smooth
factorization of `R₀ → R₀ ⊗_{k[x]} C → L₀` is the same datum as a joint factorization of the two
maps `R₀ → L₀` and `C → L₀` through an `R₀`-algebra smooth over `R₀`: restrict the middle map
along `C → R₀ ⊗_{k[x]} C` and keep the map to `L₀`.

Together with `hasSmoothFactorization_tensor_of_exists` this says that the hypothesis `hres` of
`Stacks.Smoothing.isResolvableAfterLocalizing_twistedQuotient`, that is the conclusion of
`Stacks.Smoothing.ExistsTwistedSmoothFactorization`, is *equivalent* to
`HasSmoothFactorization R₀ (R₀ ⊗_{k[x]} C) L₀`. That is what makes the residual hypothesis of
this file satisfiable rather than accidentally over-strong: items (24)–(26) produce such a
factorization by `Stacks.Smoothing.hasSmoothFactorization_of_indSmooth` from the ind-smooth
`D'[t_1, …, t_d]` over `R₀ = Λ₀[t_1, …, t_d]`, the middle term `R₀ ⊗_{k[x]} C` being of finite
presentation over `R₀` because `C` is one over `k[x_1, …, x_d]`. -/
theorem exists_of_hasSmoothFactorization_tensor (kx C R₀ L₀ : Type u)
    [CommRing kx] [CommRing C] [CommRing R₀] [CommRing L₀]
    [Algebra kx C] [Algebra kx R₀] [Algebra kx L₀] [Algebra R₀ L₀] [Algebra C L₀]
    [IsScalarTower kx R₀ L₀] [IsScalarTower kx C L₀]
    (h : letI := tensorLiftAlgebra kx C R₀ L₀
         haveI := isScalarTower_left_tensorLiftAlgebra kx C R₀ L₀
         HasSmoothFactorization R₀ (R₀ ⊗[kx] C) L₀) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R₀ T), Algebra.Smooth R₀ T ∧
      ∃ (gC : C →+* T) (kk : T →+* L₀),
        (∀ x : kx, gC (algebraMap kx C x) = algebraMap R₀ T (algebraMap kx R₀ x)) ∧
        (∀ x : R₀, kk (algebraMap R₀ T x) = algebraMap R₀ L₀ x) ∧
        ∀ c : C, kk (gC c) = algebraMap C L₀ c := by
  let := tensorLiftAlgebra kx C R₀ L₀
  have := isScalarTower_left_tensorLiftAlgebra kx C R₀ L₀
  have := isScalarTower_right_tensorLiftAlgebra kx C R₀ L₀
  obtain ⟨T, instT, instR₀T, hT, g, kk, hgk⟩ := h
  let := instT
  let := instR₀T
  refine ⟨T, instT, instR₀T, hT,
    (g : (R₀ ⊗[kx] C) →+* T).comp (algebraMap C (R₀ ⊗[kx] C)),
    (kk : T →+* L₀), fun x => ?_, fun x => kk.commutes x, fun c => ?_⟩
  · change g (algebraMap C (R₀ ⊗[kx] C) (algebraMap kx C x)) = _
    rw [← IsScalarTower.algebraMap_apply kx C (R₀ ⊗[kx] C),
      IsScalarTower.algebraMap_apply kx R₀ (R₀ ⊗[kx] C), g.commutes]
  · change kk (g (algebraMap C (R₀ ⊗[kx] C) c)) = _
    rw [show kk (g (algebraMap C (R₀ ⊗[kx] C) c)) =
        algebraMap (R₀ ⊗[kx] C) L₀ (algebraMap C (R₀ ⊗[kx] C) c) from
      AlgHom.congr_fun hgk (algebraMap C (R₀ ⊗[kx] C) c),
      ← IsScalarTower.algebraMap_apply C (R₀ ⊗[kx] C) L₀]

/-- The compatibility hypothesis `hC` of
`Stacks.Smoothing.isResolvableAfterLocalizing_of_hasSmoothFactorization`, in the form in which
items (22)–(26) supply it: both routes from `C` to `Λ_𝔮/IΛ_𝔮` factor through a map `C → Λ` and
the quotient map `Λ → Λ/IΛ`. -/
theorem algebraMap_locTarget_comp_eq_of_quotient (Sit : LocalSmoothingSituation.{u, u, u})
    (C Λ L₀ : Type u) [CommRing C] [CommRing Λ] [CommRing L₀]
    [Algebra C L₀] [Algebra L₀ (locTarget Sit)] [Algebra C Sit.A]
    (w : Λ →+* Sit.Λ) (fC : C →+* Λ) (wb : Λ →+* L₀)
    (hCL₀ : ∀ c : C, algebraMap C L₀ c = wb (fC c))
    (hwb : ∀ y : Λ, algebraMap L₀ (locTarget Sit) (wb y) =
      algebraMap Sit.Λ (locTarget Sit) (w y))
    (hCA : ∀ c : C, algebraMap Sit.A Sit.Λ (algebraMap C Sit.A c) = w (fC c)) :
    ∀ c : C, algebraMap L₀ (locTarget Sit) (algebraMap C L₀ c) =
      algebraMap Sit.A (locTarget Sit) (algebraMap C Sit.A c) := by
  intro c
  rw [hCL₀, hwb, ← hCA, ← IsScalarTower.algebraMap_apply Sit.A Sit.Λ (locTarget Sit)]

/-- **Stacks 07FJ, items (22) and (23)**, with the middle term of the auxiliary chain built as a
tensor product. This is `Stacks.Smoothing.isResolvableAfterLocalizing_of_hasSmoothFactorization`
specialized to `A₀ = R₀ ⊗_{k[x]} C` with the `L₀`-algebra structure on that tensor product
assembled from the two maps `R₀ → L₀` and `C → L₀`, so that a caller only has to produce the
auxiliary base `R₀`, its map to `R_𝔭`, and the two maps into `L₀`. -/
theorem isResolvableAfterLocalizing_of_hasSmoothFactorization_tensor
    (Sit : LocalSmoothingSituation.{u, u, u}) (kx C R₀ L₀ : Type u)
    [CommRing kx] [CommRing C] [CommRing R₀] [CommRing L₀]
    [Algebra kx C] [Algebra kx Sit.R] [Algebra C Sit.A] [Algebra kx Sit.A]
    [IsScalarTower kx Sit.R Sit.A] [IsScalarTower kx C Sit.A]
    [Algebra.IsPushout kx Sit.R C Sit.A]
    [Algebra kx R₀] [Algebra kx L₀] [Algebra R₀ L₀] [Algebra C L₀]
    [IsScalarTower kx R₀ L₀] [IsScalarTower kx C L₀]
    [Algebra R₀ (locBase Sit)] [IsScalarTower kx R₀ (locBase Sit)]
    [Algebra L₀ (locTarget Sit)] [Algebra R₀ (locTarget Sit)]
    [IsScalarTower R₀ L₀ (locTarget Sit)]
    [IsScalarTower R₀ (locBase Sit) (locTarget Sit)]
    (hC : ∀ c : C, algebraMap L₀ (locTarget Sit) (algebraMap C L₀ c)
      = algebraMap Sit.A (locTarget Sit) (algebraMap C Sit.A c))
    (h : letI := tensorLiftAlgebra kx C R₀ L₀
         haveI := isScalarTower_left_tensorLiftAlgebra kx C R₀ L₀
         HasSmoothFactorization R₀ (R₀ ⊗[kx] C) L₀) :
    Sit.IsResolvableAfterLocalizing := by
  let := tensorLiftAlgebra kx C R₀ L₀
  have := isScalarTower_left_tensorLiftAlgebra kx C R₀ L₀
  have := isScalarTower_right_tensorLiftAlgebra kx C R₀ L₀
  exact isResolvableAfterLocalizing_of_hasSmoothFactorization Sit kx C R₀ (R₀ ⊗[kx] C) L₀ hC h



/-- Two ring maps out of `R_𝔭/𝔭ⁿR_𝔭` agreeing on the images of `R` are equal. -/
theorem primePowerQuotient_ringHom_ext {R Y : Type u} [CommRing R] [CommRing Y] (p : Ideal R)
    [p.IsPrime] {n : ℕ} {f g : primePowerQuotient p n →+* Y}
    (h : ∀ x : R, f (algebraMap R (primePowerQuotient p n) x) =
      g (algebraMap R (primePowerQuotient p n) x)) : f = g := by
  have h2 : f.comp (Ideal.Quotient.mk
        (Ideal.map (algebraMap R (Localization.AtPrime p)) (p ^ n))) =
      g.comp (Ideal.Quotient.mk
        (Ideal.map (algebraMap R (Localization.AtPrime p)) (p ^ n))) := by
    refine IsLocalization.ringHom_ext p.primeCompl (RingHom.ext fun x => ?_)
    have hx := h x
    rwa [← Ideal.Quotient.mk_algebraMap (R₁ := R) (A := Localization.AtPrime p) _ x] at hx
  refine RingHom.ext fun z => ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact RingHom.congr_fun h2 y

/-- **The numeric input of items (22) and (23).** A ring map `ν : R → Y` which inverts
everything outside a prime `𝔭` and kills the `e`-th powers of a family `π_1, …, π_d` generating
the maximal ideal of `R_𝔭` factors through `R_𝔭/𝔭ⁿR_𝔭`, as soon as `d(e - 1) < n`.

In item (23) this is what produces the structure map `Λ₀ = k[y_1, …, y_m]_𝔭/𝔭ⁿ → (R/I)_𝔯`: the
twisted parameters `γ_i = π_i t_i` have `γ_i^e ∈ I` and the `t_i` are invertible in `(R/I)_𝔯`,
so `π_i^e` dies there, and `𝔭ⁿk[y]_𝔭 ⊆ (π_1^e, …, π_d^e)` by
`Stacks.Smoothing.span_range_pow_le_span_range_pow_of_le`. -/
theorem exists_primePowerQuotient_lift {R Y : Type u} [CommRing R] [CommRing Y] {d e n : ℕ}
    (p : Ideal R) [p.IsPrime] (π : Fin d → R) (ν : R →+* Y)
    (hνunit : ∀ s ∈ p.primeCompl, IsUnit (ν s)) (hνpow : ∀ i, ν (π i) ^ e = 0)
    (he : 1 ≤ e) (hn : d * (e - 1) + 1 ≤ n)
    (hπspan : Ideal.span (Set.range fun i => algebraMap R (Localization.AtPrime p) (π i)) =
      maximalIdeal (Localization.AtPrime p)) :
    ∃ f : primePowerQuotient p n →+* Y,
      ∀ g : R, f (algebraMap R (primePowerQuotient p n) g) = ν g := by
  let g₀ : Localization.AtPrime p →+* Y :=
    IsLocalization.lift (M := p.primeCompl) (S := Localization.AtPrime p)
      (g := ν) fun y => hνunit (y : R) y.2
  have hg₀ : ∀ x : R, g₀ (algebraMap R (Localization.AtPrime p) x) = ν x := fun x =>
    IsLocalization.lift_eq (fun y => hνunit (y : R) y.2) x
  have hker : Ideal.map (algebraMap R (Localization.AtPrime p)) (p ^ n) ≤ RingHom.ker g₀ := by
    rw [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal, ← hπspan]
    refine le_trans (span_range_pow_le_span_range_pow_of_le _ he hn) ?_
    rw [Ideal.span_le]
    rintro x ⟨i, rfl⟩
    exact RingHom.mem_ker.mpr (by rw [map_pow, hg₀, hνpow])
  refine ⟨Ideal.Quotient.lift _ g₀ fun x hx => RingHom.mem_ker.mp (hker hx), fun x => ?_⟩
  rw [← Ideal.Quotient.mk_algebraMap (R₁ := R) (A := Localization.AtPrime p) _ x]
  change g₀ _ = _
  rw [hg₀]

/-- **The structure map `Λ₀ → Λ̄` of items (22)–(26) on the image of `k[y_1, …, y_m]`.** If
`gl : k[y_1, …, y_m]_𝔭 → Λ_𝔮` is `φ` on `k[y_1, …, y_m]` and `u : Λ₀ → Λ̄` is the map it induces
on the quotients by the `n`-th powers of the two primes, then `u` carries the image of
`f ∈ k[y_1, …, y_m]` to the image of `φ f`.

The two hypotheses are `hgφ` and `hu` of
`Stacks.Smoothing.TwistedQuotientLocallyResolvable` verbatim; this is the form in which items
(22)–(26) use them. -/
theorem primePowerQuotient_map_algebraMap {k Λ : Type u} [CommRing k] [CommRing Λ] [Algebra k Λ]
    {m n : ℕ} (q : Ideal Λ) [q.IsPrime] (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
    (gl : Localization.AtPrime (Ideal.comap φ.toRingHom q) →+* Localization.AtPrime q)
    (u : primePowerQuotient (Ideal.comap φ.toRingHom q) n →+* primePowerQuotient q n)
    (hgφ : ∀ f, gl (algebraMap (MvPolynomial (Fin m) k)
          (Localization.AtPrime (Ideal.comap φ.toRingHom q)) f)
        = algebraMap Λ (Localization.AtPrime q) (φ f))
    (hu : ∀ y, u (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (Ideal.comap φ.toRingHom q)))
            (Ideal.comap φ.toRingHom q ^ n)) y)
        = Ideal.Quotient.mk (Ideal.map (algebraMap Λ (Localization.AtPrime q)) (q ^ n)) (gl y))
    (f : MvPolynomial (Fin m) k) :
    u (algebraMap (MvPolynomial (Fin m) k)
        (primePowerQuotient (Ideal.comap φ.toRingHom q) n) f) =
      algebraMap Λ (primePowerQuotient q n) (φ f) := by
  rw [← Ideal.Quotient.mk_algebraMap (R₁ := MvPolynomial (Fin m) k)
      (A := Localization.AtPrime (Ideal.comap φ.toRingHom q)) _ f, hu, hgφ,
    IsScalarTower.algebraMap_apply Λ (Localization.AtPrime q) (primePowerQuotient q n),
    Ideal.Quotient.algebraMap_eq]

/-- The `k[x_1, …, x_d]`-algebra structure of items (22)–(26) on `Λ₀[t_1, …, t_d]` sends `x_i` to
`π̄_i t_i`; composing it with an evaluation of `Λ₀[t_1, …, t_d]` is therefore pinned down by its
values on the constants and on `x_i`. -/
theorem eval₂Hom_comp_twistedStructure {k Λ₀ Y : Type u} [CommRing k] [CommRing Λ₀] [CommRing Y]
    [Algebra k Λ₀] {m d : ℕ} [Algebra (MvPolynomial (Fin m) k) Λ₀]
    [IsScalarTower k (MvPolynomial (Fin m) k) Λ₀] (π : Fin d → MvPolynomial (Fin m) k)
    (f₀ : Λ₀ →+* Y) (τ : Fin d → Y) (g : MvPolynomial (Fin d) k →+* Y)
    (hC : ∀ r : k, g (MvPolynomial.C r) = f₀ (algebraMap k Λ₀ r))
    (hX : ∀ i, g (MvPolynomial.X i) =
      f₀ (algebraMap (MvPolynomial (Fin m) k) Λ₀ (π i)) * τ i) :
    g = (MvPolynomial.eval₂Hom f₀ τ).comp
      (MvPolynomial.eval₂Hom ((MvPolynomial.C (σ := Fin d)).comp (algebraMap k Λ₀))
        (fun i => MvPolynomial.C (algebraMap (MvPolynomial (Fin m) k) Λ₀ (π i)) *
          MvPolynomial.X i)) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) fun i => ?_
  · rw [hC]
    change _ = MvPolynomial.eval₂Hom f₀ τ (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C r))
    rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
  · rw [hX]
    change _ = MvPolynomial.eval₂Hom f₀ τ (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X i))
    rw [MvPolynomial.eval₂Hom_X', map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']

/-- **The structure map of item (23).** For a chain whose base `R/I` receives
`R = k[y_1, …, y_m, t_1, …, t_d]` by a map `ν` killing the twisted parameter powers `γ_i^e`, and
whose target `Λ/IΛ` receives `Λ` by a map `w` whose preimage of the chosen prime is `𝔮`, the
composite `k[y_1, …, y_m] → R → (R/I)_𝔯` factors through `Λ₀ = k[y_1, …, y_m]_𝔭/𝔭ⁿ` as soon as
`d(e - 1) < n`.

This is where the twist is used: `ν(t_i)` is invertible in `(R/I)_𝔯` because `t_i ↦ δ_i ∉ 𝔮`, so
`ν(π_i)^e = 0` follows from `ν(γ_i^e) = 0`, and then
`Stacks.Smoothing.exists_primePowerQuotient_lift` applies. -/
theorem exists_twistedLocBaseLift {k Λ : Type u} [Field k] [CommRing Λ] [Algebra k Λ]
    {m d e n : ℕ} (q : Ideal Λ) [q.IsPrime] (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
    (π : Fin d → MvPolynomial (Fin m) k) (δ : Fin d → Λ)
    (Sit : LocalSmoothingSituation.{u, u, u})
    (ν : MvPolynomial (Fin m ⊕ Fin d) k →+* Sit.R) (w : Λ →+* Sit.Λ)
    (hνw : ∀ x, algebraMap Sit.R Sit.Λ (ν x) = w (twistedBaseToTarget φ δ x))
    (hwq : ∀ y : Λ, w y ∈ Sit.q ↔ y ∈ q)
    (hνI : ∀ i, ν (twistedParameter π i ^ e) = 0) (hδq : ∀ i, δ i ∈ q.primeCompl)
    (he : 1 ≤ e) (hn : d * (e - 1) + 1 ≤ n)
    (hπspan : Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin m) k)
        (Localization.AtPrime (Ideal.comap φ.toRingHom q)) (π i)) =
      maximalIdeal (Localization.AtPrime (Ideal.comap φ.toRingHom q))) :
    ∃ f : primePowerQuotient (Ideal.comap φ.toRingHom q) n →+* locBase Sit,
      ∀ g : MvPolynomial (Fin m) k,
        f (algebraMap (MvPolynomial (Fin m) k)
            (primePowerQuotient (Ideal.comap φ.toRingHom q) n) g) =
          algebraMap Sit.R (locBase Sit) (ν (MvPolynomial.rename Sum.inl g)) := by
  have hunit : ∀ x : MvPolynomial (Fin m ⊕ Fin d) k, twistedBaseToTarget φ δ x ∉ q →
      IsUnit (algebraMap Sit.R (locBase Sit) (ν x)) := by
    intro x hx
    refine IsLocalization.map_units (locBase Sit)
      (⟨ν x, fun hmem => hx ?_⟩ : Sit.basePrime.primeCompl)
    have h1 : algebraMap Sit.R Sit.Λ (ν x) ∈ Sit.q := hmem
    rw [hνw] at h1
    exact (hwq _).mp h1
  have htu : ∀ i, IsUnit (algebraMap Sit.R (locBase Sit) (ν (MvPolynomial.X (Sum.inr i)))) := by
    intro i
    refine hunit _ ?_
    rw [twistedBaseToTarget_X_inr]
    exact hδq i
  have hπpow : ∀ i, algebraMap Sit.R (locBase Sit)
      (ν (MvPolynomial.rename Sum.inl (π i))) ^ e = 0 := by
    intro i
    have h0 : algebraMap Sit.R (locBase Sit) (ν (twistedParameter π i ^ e)) = 0 := by
      rw [hνI i, map_zero]
    rw [twistedParameter, map_pow, map_mul, map_pow, map_mul, mul_pow] at h0
    refine ((htu i).pow e).mul_left_cancel ?_
    rw [mul_zero, mul_comm]
    exact h0
  have hkyu : ∀ s ∈ (Ideal.comap φ.toRingHom q).primeCompl,
      IsUnit (algebraMap Sit.R (locBase Sit) (ν (MvPolynomial.rename Sum.inl s))) := by
    intro s hs
    refine hunit _ ?_
    rw [show twistedBaseToTarget φ δ (MvPolynomial.rename Sum.inl s) = φ s from
      AlgHom.congr_fun (twistedBaseToTarget_comp_rename φ δ) s]
    exact hs
  exact exists_primePowerQuotient_lift (Ideal.comap φ.toRingHom q) π
    ((algebraMap Sit.R (locBase Sit)).comp
      (ν.comp (MvPolynomial.rename (R := k) (σ := Fin m)
        (τ := Fin m ⊕ Fin d) Sum.inl).toRingHom))
    hkyu hπpow he hn hπspan

end Core

/-- The quotient of a chain `R → S → A` by an ideal of `S` and its extension to `A` is again a
chain over `R`. -/
instance isScalarTower_quotient_map_quotient {R S A : Type*} [CommRing R] [CommRing S]
    [CommRing A] [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A] (I : Ideal S) :
    IsScalarTower R (S ⧸ I) (A ⧸ Ideal.map (algebraMap S A) I) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [← Ideal.Quotient.mk_algebraMap (R₁ := R) (A := S) I x,
      Ideal.Quotient.algebraMap_quotient_map_quotient,
      ← Ideal.Quotient.mk_algebraMap (R₁ := R) (A := A) (Ideal.map (algebraMap S A) I) x,
      IsScalarTower.algebraMap_apply R S A]

/-! ### The reduction of items (22)-(26) to items (24)-(26) -/

section Residual

open LocalSmoothingSituation

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- If `A` is the base change of `C` along `R → S`, then `A/IA` is the base change of `C` along
`R → S/I`, for every ideal `I` of `S` and its extension `IA = I·A`. This is the base-change
square that items (22)–(26) are applied to at the twisted quotient chain: there
`R = k[x_1, …, x_d]`, `S = k[y_1, …, y_m, t_1, …, t_d]`, `A = S ⊗_R C` and
`I = (γ_1^e, …, γ_d^e)`, so `S/I → A/IA` is again the base change of `C`. -/
theorem isPushout_quotient_of_isPushout (R S C A : Type u) [CommRing R] [CommRing S]
    [CommRing C] [CommRing A] [Algebra R S] [Algebra R C] [Algebra S A] [Algebra C A]
    [Algebra R A] [IsScalarTower R S A] [IsScalarTower R C A] [Algebra.IsPushout R S C A]
    (I : Ideal S) :
    Algebra.IsPushout R (S ⧸ I) C (A ⧸ Ideal.map (algebraMap S A) I) :=
  (Algebra.IsPushout.comp_iff R S C A).mpr
    (Algebra.IsPushout.symm (isPushout_quotient_idealMap S A I))

/-- **The conclusion of items (24)–(26) of the proof of Stacks 07FJ** — Stacks 07G8, 07G9 and
07GA — at one choice of the data of item (18).

The three `letI`s pin down the three structure maps the statement is about, all of them built
from the given data and none of them involving a localization or a quotient of the chain:

* `k[x_1, …, x_d] → Λ₀[t_1, …, t_d]`, `x_i ↦ π̄_i t_i`, the twisted structure map of item (25) on
  the polynomial ring over `Λ₀ = k[y_1, …, y_m]_𝔭/𝔭ⁿ`;
* `Λ₀[t_1, …, t_d] → Λ̄ = Λ_𝔮/𝔮ⁿΛ_𝔮`, which is `u` on `Λ₀` and `t_i ↦ δ_i`;
* `C → Λ̄`, the composite of `Stacks.Smoothing.improvedAlgebraToTarget` with `Λ → Λ̄`.

Asked for is a `Λ₀[t_1, …, t_d]`-algebra `T` smooth over `Λ₀[t_1, …, t_d]`, a ring map
`gC : C → T` over `k[x_1, …, x_d]`, and a ring map `kk : T → Λ̄` over `Λ₀[t_1, …, t_d]` with
`kk ∘ gC` the structure map `C → Λ̄`. In the source `T` is a finite stage of the ind-smooth
`D'[t_1, …, t_d]` and `gC` is the twisted map of 07GA. By
`Stacks.Smoothing.hasSmoothFactorization_tensor_of_exists` and
`Stacks.Smoothing.exists_of_hasSmoothFactorization_tensor` this is equivalent to
`HasSmoothFactorization (Λ₀[t_1, …, t_d]) (Λ₀[t_1, …, t_d] ⊗_{k[x]} C) Λ̄`.

The only hypothesis is `hrel`, the defining relation `(δ_iφ(π_i))^{2N} = Σ_j a_jλ_{ij}` of item
(18), which the map `C → Λ` depends on. -/
def ExistsTwistedSmoothFactorization (k A Λ : Type u) [Field k] [CommRing A] [CommRing Λ]
    [Algebra k A] [Algebra k Λ] [Algebra A Λ] [IsScalarTower k A Λ] (q : Ideal Λ) [q.IsPrime]
    {t d m N n : ℕ} (a : Fin t → A) (C : Type u) [CommRing C]
    [Algebra (MvPolynomial (Fin d) k) C] [Algebra (parameterPowerAlgebra A d N a) C]
    (grt : C →ₐ[MvPolynomial (Fin d) k] parameterPowerAlgebra A d N a)
    (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
    (u : primePowerQuotient (Ideal.comap φ.toRingHom q) n →+* primePowerQuotient q n)
    (π : Fin d → MvPolynomial (Fin m) k) (δ : Fin d → Λ) (lam : Fin d → Fin t → Λ)
    (hrel : ∀ i, (δ i * φ (π i)) ^ (2 * N) = ∑ j, algebraMap A Λ (a j) * lam i j) : Prop :=
    letI : Algebra (MvPolynomial (Fin d) k)
        (MvPolynomial (Fin d) (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) :=
      (MvPolynomial.eval₂Hom ((MvPolynomial.C (σ := Fin d)).comp
          (algebraMap k (primePowerQuotient (Ideal.comap φ.toRingHom q) n)))
        (fun i => MvPolynomial.C (algebraMap (MvPolynomial (Fin m) k)
            (primePowerQuotient (Ideal.comap φ.toRingHom q) n) (π i)) *
          MvPolynomial.X i)).toAlgebra
    letI : Algebra (MvPolynomial (Fin d)
        (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) (primePowerQuotient q n) :=
      (MvPolynomial.eval₂Hom u
        (fun i => algebraMap Λ (primePowerQuotient q n) (δ i))).toAlgebra
    letI : Algebra C (primePowerQuotient q n) :=
      ((algebraMap Λ (primePowerQuotient q n)).comp
        (improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel grt)).toAlgebra
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra (MvPolynomial (Fin d)
        (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) T),
      Algebra.Smooth (MvPolynomial (Fin d)
        (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) T ∧
      ∃ (gC : C →+* T) (kk : T →+* primePowerQuotient q n),
        (∀ x : MvPolynomial (Fin d) k, gC (algebraMap (MvPolynomial (Fin d) k) C x) =
          algebraMap (MvPolynomial (Fin d)
              (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) T
            (algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin d)
              (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) x)) ∧
        (∀ x, kk (algebraMap (MvPolynomial (Fin d)
            (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) T x) =
          algebraMap (MvPolynomial (Fin d)
            (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) (primePowerQuotient q n) x) ∧
        ∀ c : C, kk (gC c) = algebraMap C (primePowerQuotient q n) c

/-- **Items (24)-(26) of the proof of Stacks 07FJ** — Stacks 07G8, 07G9 and 07GA — as a standing
hypothesis. This is the telescope of `Stacks.Smoothing.TwistedQuotientLocallyResolvable`
verbatim, up to and including its `hcompat`, with the conclusion replaced by
`Stacks.Smoothing.ExistsTwistedSmoothFactorization` on the same data: the smooth factorization of
`Λ₀[t_1, …, t_d] → C → Λ_𝔮/𝔮ⁿΛ_𝔮`. Nothing about the quotient chain
`R/I → (R ⊗_{k[x]} C)/I → Λ/IΛ`, nor about any localization of it, survives here; that content is
items (22) and (23) and is discharged in
`Stacks.Smoothing.twistedQuotientLocallyResolvable_of_smoothFactorization`.

Every hypothesis of the source telescope is carried, because the proof of items (24)-(26) may use
any of them and carrying one it does not use only weakens this hypothesis.

The data is a field `k`, a `k`-algebra `A` of finite presentation, a Noetherian geometrically
regular `k`-algebra `Λ` with a prime `𝔮`, a family `a : Fin t → A`, a `k[x_1, …, x_d]`-algebra `C`
of finite presentation which is of finite type over `B = parameterPowerAlgebra A d N a` and
carries a `k[x_1, …, x_d]`-algebra map `grt : C → B`, a map `φ : k[y_1, …, y_m] → Λ` with
`𝔭 = φ⁻¹𝔮`, maps `gl : k[y]_𝔭 → Λ_𝔮` and `u : Λ₀ → Λ̄` where `Λ₀ = k[y]_𝔭/𝔭ⁿ` and
`Λ̄ = Λ_𝔮/𝔮ⁿΛ_𝔮`, a subring `D ⊆ Λ̄` with a map `aD : Λ₀ → D`, the parameters
`π : Fin d → k[y_1, …, y_m]`, `δ : Fin d → Λ` and `lam : Fin d → Fin t → Λ`, and a ring `D'` with
maps `cc : D → D'` and `b' : D' → Λ̄`.

The hypotheses, in the order of the telescope: `0 < N`; `0 < c`; `1 ≤ d`; `1 ≤ n`; `N ≤ n`;
`d(8c - 1) < n`; `𝔮` is a minimal prime of the radical of the singular ideal of `A` over `k`
extended to `Λ`; `a` generates that singular ideal; `𝔮^N` lies in it after localizing at `𝔮`;
`dim Λ_𝔮 = d`; `hCalg`, that the `k[x_1, …, x_d]`-algebra structure of `C` is the one it has
through `B`; `hgrt`, that `grt` is a retraction of `B → C`; `hmapφ`, that `𝔭` and `𝔮` generate the
same ideal of `Λ_𝔮`; `hgφ`, that `gl` is `φ` on `k[y_1, …, y_m]`; `gl` is flat; `hu`, that `u` is
the map induced by `gl`; `hDsub`, that `D ⊆ Λ̄` composed with `aD` is `u`; `hAD`, that the image of
`A` in `Λ̄` lies in `D`; `Λ₀`, `Λ̄` and `D` are local Artinian rings; `aD` is essentially smooth;
`D ⊆ Λ̄` is flat; `dim k[y]_𝔭 = d`; `π_i ∈ 𝔭`; the `π_i` generate the maximal ideal of `k[y]_𝔭`;
the `φ(π_i)` generate the maximal ideal of `Λ_𝔮`; `cc` and `b'` are local homomorphisms; `cc` is
essentially smooth; `b'` is flat; `b' ∘ cc` is the inclusion of `D`; `δ_i ∉ 𝔮`; `hrel`, the
relation `(δ_iφ(π_i))^{2N} = Σ_j a_jλ_{ij}`; the `λ_{ij}` and the `δ_i` lift to `D'` along `b'`;
`hstdC`, that the `c`-th power of the image of `x_i` in `C` is strictly standard; and `hcompat`,
the agreement of the two maps `k[x_1, …, x_d] → Λ`, one through `k[y, t]` and one through `C`,
which the conclusion does not use. -/
def TwistedQuotientSmoothFactorization : Prop :=
  ∀ (k A Λ : Type u) [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
      [Algebra A Λ] [IsScalarTower k A Λ] [Algebra.FinitePresentation k A] [IsNoetherianRing Λ]
      [Algebra.IsGeometricallyRegular k Λ] (q : Ideal Λ) [q.IsPrime]
      {t d m N n c : ℕ} (a : Fin t → A)
      (C : Type u) [CommRing C] [Algebra (MvPolynomial (Fin d) k) C]
      [Algebra (parameterPowerAlgebra A d N a) C]
      [Algebra.FiniteType (parameterPowerAlgebra A d N a) C]
      [Algebra.FinitePresentation (MvPolynomial (Fin d) k) C]
      (grt : C →ₐ[MvPolynomial (Fin d) k] parameterPowerAlgebra A d N a)
      (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
      (gl : Localization.AtPrime (Ideal.comap φ.toRingHom q) →+* Localization.AtPrime q)
      (u : primePowerQuotient (Ideal.comap φ.toRingHom q) n →+* primePowerQuotient q n)
      (D : Subring (primePowerQuotient q n))
      (aD : primePowerQuotient (Ideal.comap φ.toRingHom q) n →+* D)
      (π : Fin d → MvPolynomial (Fin m) k) (δ : Fin d → Λ) (lam : Fin d → Fin t → Λ)
      (D' : Type u) [CommRing D'] [IsLocalRing D'] [IsArtinianRing D']
      (cc : D →+* D') (b' : D' →+* primePowerQuotient q n),
    0 < N → 0 < c → 1 ≤ d → 1 ≤ n → N ≤ n → d * (8 * c - 1) + 1 ≤ n →
    q ∈ (Ideal.map (algebraMap A Λ) (singularIdeal k A)).radical.minimalPrimes →
    Ideal.span (Set.range a) = singularIdeal k A →
    Ideal.map (algebraMap Λ (Localization.AtPrime q)) (q ^ N) ≤
      Ideal.map (algebraMap Λ (Localization.AtPrime q))
        (Ideal.map (algebraMap A Λ) (singularIdeal k A)) →
    ringKrullDim (Localization.AtPrime q) = (d : WithBot ℕ∞) →
    (∀ y : MvPolynomial (Fin d) k, algebraMap (MvPolynomial (Fin d) k) C y =
      algebraMap (parameterPowerAlgebra A d N a) C
        (algebraMap (MvPolynomial (Fin d) k) (parameterPowerAlgebra A d N a) y)) →
    (∀ x : parameterPowerAlgebra A d N a,
      grt (algebraMap (parameterPowerAlgebra A d N a) C x) = x) →
    Ideal.map ((algebraMap Λ (Localization.AtPrime q)).comp φ.toRingHom)
        (Ideal.comap φ.toRingHom q) = Ideal.map (algebraMap Λ (Localization.AtPrime q)) q →
    (∀ f, gl (algebraMap (MvPolynomial (Fin m) k)
          (Localization.AtPrime (Ideal.comap φ.toRingHom q)) f)
        = algebraMap Λ (Localization.AtPrime q) (φ f)) →
    gl.Flat →
    (∀ y, u (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) k)
            (Localization.AtPrime (Ideal.comap φ.toRingHom q)))
            (Ideal.comap φ.toRingHom q ^ n)) y)
        = Ideal.Quotient.mk (Ideal.map (algebraMap Λ (Localization.AtPrime q)) (q ^ n))
          (gl y)) →
    D.subtype.comp aD = u →
    (∀ x : A, algebraMap Λ (primePowerQuotient q n) (algebraMap A Λ x) ∈ D) →
    ∀ (_ : IsLocalRing (primePowerQuotient (Ideal.comap φ.toRingHom q) n))
      (_ : IsArtinianRing (primePowerQuotient (Ideal.comap φ.toRingHom q) n))
      (_ : IsLocalRing (primePowerQuotient q n)) (_ : IsArtinianRing (primePowerQuotient q n))
      (_ : IsLocalRing D) (_ : IsArtinianRing D),
    aD.IsEssentiallySmooth → D.subtype.Flat →
    ringKrullDim (Localization.AtPrime (Ideal.comap φ.toRingHom q)) = (d : WithBot ℕ∞) →
    (∀ i, π i ∈ Ideal.comap φ.toRingHom q) →
    Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin m) k)
        (Localization.AtPrime (Ideal.comap φ.toRingHom q)) (π i))
      = IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.comap φ.toRingHom q)) →
    Ideal.span (Set.range fun i => algebraMap Λ (Localization.AtPrime q) (φ (π i)))
      = IsLocalRing.maximalIdeal (Localization.AtPrime q) →
    ∀ (_ : IsLocalHom cc) (_ : IsLocalHom b'),
    cc.IsEssentiallySmooth → b'.Flat → b'.comp cc = D.subtype →
    (∀ i, δ i ∈ q.primeCompl) →
    ∀ hrel : ∀ i, (δ i * φ (π i)) ^ (2 * N) = ∑ j, algebraMap A Λ (a j) * lam i j,
    (∀ i j, ∃ w : D', b' w = algebraMap Λ (primePowerQuotient q n) (lam i j)) →
    (∀ i, ∃ w : D', b' w = algebraMap Λ (primePowerQuotient q n) (δ i)) →
    (∀ i : Fin d, IsStrictlyStandard (R := MvPolynomial (Fin d) k)
      (algebraMap (MvPolynomial (Fin d) k) C (MvPolynomial.X i) ^ c)) →
    letI : Algebra (MvPolynomial (Fin d) k) (MvPolynomial (Fin m ⊕ Fin d) k) :=
      (twistedBaseHom π).toRingHom.toAlgebra
    letI : Algebra (MvPolynomial (Fin m ⊕ Fin d) k) Λ :=
      (twistedBaseToTarget φ δ).toRingHom.toAlgebra
    letI : Algebra (MvPolynomial (Fin d) k) Λ :=
      ((algebraMap (MvPolynomial (Fin m ⊕ Fin d) k) Λ).comp
        (algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin m ⊕ Fin d) k))).toAlgebra
    letI : IsScalarTower (MvPolynomial (Fin d) k) (MvPolynomial (Fin m ⊕ Fin d) k) Λ :=
      IsScalarTower.of_algebraMap_eq' rfl
    ∀ _ : ∀ y : MvPolynomial (Fin d) k,
        algebraMap (MvPolynomial (Fin m ⊕ Fin d) k) Λ
            (algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin m ⊕ Fin d) k) y) =
          improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel grt
            (algebraMap (MvPolynomial (Fin d) k) C y),
    ExistsTwistedSmoothFactorization k A Λ q a C grt φ u π δ lam hrel

/-- **Items (22) and (23) of the proof of Stacks 07FJ at the twisted quotient chain**, with the
chain itself opaque. This is the assembly that reduces resolvability after localizing of a
`Stacks.Smoothing.LocalSmoothingSituation` `Sit` presenting the quotient chain
`R/I → (R ⊗_{k[x]} C)/I → Λ/IΛ` of item (18) to items (24)–(26) alone.

The situation is a variable rather than the structure literal of
`Stacks.Smoothing.TwistedQuotientLocallyResolvable`, and its three rings are identified with the
quotient chain only through ring maps `ν : k[y_1, …, y_m, t_1, …, t_d] → Sit.R` and
`w : Λ → Sit.Λ` and the hypotheses below. That is what keeps the elaboration affordable: every
instance search here is against an opaque `Sit.R`, `Sit.A`, `Sit.Λ` instead of against a
localization of a quotient of a tensor product.

The hypotheses are: `hkxR`, that `k[x_1, …, x_d] → Sit.R` is `ν` after the twisted base map
`x_i ↦ γ_i = π_i t_i`; `hkxΛ`, that `k[x_1, …, x_d] → Λ` sends `x_i` to `δ_iφ(π_i)`; `hνw`, that
the square `k[y, t] → Sit.R → Sit.Λ` equals `k[y, t] → Λ → Sit.Λ`; `hwq`, that `𝔮` is the
preimage of `Sit.q` under `w`; `hνI`, that `ν` kills the twisted parameter powers `γ_i^e`;
`hcompat`, that the two maps `k[x_1, …, x_d] → Λ` agree, one through `k[y, t]` and one through
`C`; `hCA`, that the square `C → Sit.A → Sit.Λ` equals `C → Λ → Sit.Λ`; `hubar`, that `u` is `φ`
on the image of `k[y_1, …, y_m]`; `hδq`, that `δ_i ∉ 𝔮`; `he` and `hn`, the numerical conditions
`1 ≤ e` and `d(e - 1) < n` of `Stacks.Smoothing.exists_primePowerQuotient_lift`; `hπspan` and
`hπΛspan`, that the `π_i` generate the maximal ideal of `k[y]_𝔭` and the `φ(π_i)` that of `Λ_𝔮`;
and `hres`, items (24)–(26) on this data.

The proof produces the auxiliary chain over `R₀ = Λ₀[t_1, …, t_d]` with
`Λ₀ = k[y_1, …, y_m]_𝔭/𝔭ⁿ` and `L₀ = Λ_𝔮/𝔮ⁿΛ_𝔮`, its two structure maps
(`Stacks.Smoothing.exists_twistedLocBaseLift` into `(R/I)_𝔯` and
`Stacks.Smoothing.exists_primePowerQuotient_lift` into `Λ_𝔮/IΛ_𝔮`), the scalar towers joining
them, and the compatibility
`Stacks.Smoothing.algebraMap_locTarget_comp_eq_of_quotient`, and then applies
`Stacks.Smoothing.isResolvableAfterLocalizing_of_hasSmoothFactorization_tensor`. -/
theorem isResolvableAfterLocalizing_twistedQuotient
    (Sit : LocalSmoothingSituation.{u, u, u})
    {k A Λ : Type u} [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [Algebra A Λ] [IsScalarTower k A Λ] (q : Ideal Λ) [q.IsPrime]
    {t d m N n e : ℕ} (a : Fin t → A)
    (C : Type u) [CommRing C] [Algebra (MvPolynomial (Fin d) k) C]
    [Algebra (parameterPowerAlgebra A d N a) C]
    (grt : C →ₐ[MvPolynomial (Fin d) k] parameterPowerAlgebra A d N a)
    (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
    (u : primePowerQuotient (Ideal.comap φ.toRingHom q) n →+* primePowerQuotient q n)
    (π : Fin d → MvPolynomial (Fin m) k) (δ : Fin d → Λ) (lam : Fin d → Fin t → Λ)
    (hrel : ∀ i, (δ i * φ (π i)) ^ (2 * N) = ∑ j, algebraMap A Λ (a j) * lam i j)
    [Algebra (MvPolynomial (Fin d) k) Λ] [IsScalarTower k (MvPolynomial (Fin d) k) Λ]
    [Algebra (MvPolynomial (Fin d) k) Sit.R] [Algebra C Sit.A]
    [Algebra (MvPolynomial (Fin d) k) Sit.A]
    [IsScalarTower (MvPolynomial (Fin d) k) Sit.R Sit.A]
    [IsScalarTower (MvPolynomial (Fin d) k) C Sit.A]
    [Algebra.IsPushout (MvPolynomial (Fin d) k) Sit.R C Sit.A]
    (ν : MvPolynomial (Fin m ⊕ Fin d) k →+* Sit.R) (w : Λ →+* Sit.Λ)
    (hkxR : ∀ x : MvPolynomial (Fin d) k,
      algebraMap (MvPolynomial (Fin d) k) Sit.R x = ν (twistedBaseHom π x))
    (hkxΛ : ∀ i, algebraMap (MvPolynomial (Fin d) k) Λ (MvPolynomial.X i) = δ i * φ (π i))
    (hνw : ∀ x, algebraMap Sit.R Sit.Λ (ν x) = w (twistedBaseToTarget φ δ x))
    (hwq : ∀ y : Λ, w y ∈ Sit.q ↔ y ∈ q)
    (hνI : ∀ i, ν (twistedParameter π i ^ e) = 0)
    (hcompat : ∀ y : MvPolynomial (Fin d) k, algebraMap (MvPolynomial (Fin d) k) Λ y =
      improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel grt
        (algebraMap (MvPolynomial (Fin d) k) C y))
    (hCA : ∀ c : C, algebraMap Sit.A Sit.Λ (algebraMap C Sit.A c) =
      w (improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel grt c))
    (hubar : ∀ f : MvPolynomial (Fin m) k,
      u (algebraMap (MvPolynomial (Fin m) k)
          (primePowerQuotient (Ideal.comap φ.toRingHom q) n) f) =
        algebraMap Λ (primePowerQuotient q n) (φ f))
    (hδq : ∀ i, δ i ∈ q.primeCompl) (he : 1 ≤ e) (hn : d * (e - 1) + 1 ≤ n)
    (hπspan : Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin m) k)
        (Localization.AtPrime (Ideal.comap φ.toRingHom q)) (π i)) =
      maximalIdeal (Localization.AtPrime (Ideal.comap φ.toRingHom q)))
    (hπΛspan : Ideal.span (Set.range fun i => algebraMap Λ (Localization.AtPrime q) (φ (π i))) =
      maximalIdeal (Localization.AtPrime q))
    (hres : ExistsTwistedSmoothFactorization k A Λ q a C grt φ u π δ lam hrel) :
    Sit.IsResolvableAfterLocalizing := by
  -- the composite `Λ → Λ/IΛ → Λ_𝔮/IΛ_𝔮` and the vanishing of the parameter powers on it
  let wb : Λ →+* locTarget Sit := (algebraMap Sit.Λ (locTarget Sit)).comp w
  have hwbunit : ∀ s ∈ q.primeCompl, IsUnit (wb s) := fun s hs =>
    IsLocalization.map_units (locTarget Sit)
      (⟨w s, fun hmem => hs ((hwq s).mp hmem)⟩ : Sit.q.primeCompl)
  have hwpow : ∀ i, wb (φ (π i)) ^ e = 0 := by
    intro i
    have h1 := hνw (twistedParameter π i ^ e)
    rw [hνI i, map_zero, map_pow, twistedBaseToTarget_twistedParameter] at h1
    have h0 : wb ((δ i * φ (π i)) ^ e) = 0 := by
      change algebraMap Sit.Λ (locTarget Sit) (w ((δ i * φ (π i)) ^ e)) = 0
      rw [← h1, map_zero]
    rw [map_pow, map_mul, mul_pow] at h0
    refine ((hwbunit (δ i) (hδq i)).pow e).mul_left_cancel ?_
    rwa [mul_zero]
  -- `Λ₀ = k[y]_𝔭/𝔭ⁿ → (R/I)_𝔯`
  obtain ⟨l0map, hl0⟩ := exists_twistedLocBaseLift q φ π δ Sit ν w hνw hwq hνI hδq he hn hπspan
  have hl0' : ∀ g : MvPolynomial (Fin m) k,
      l0map (algebraMap (MvPolynomial (Fin m) k)
        (primePowerQuotient (Ideal.comap φ.toRingHom q) n) g) =
      algebraMap Sit.R (locBase Sit) (ν (MvPolynomial.rename Sum.inl g)) := hl0
  -- `Λ̄ = Λ_𝔮/𝔮ⁿΛ_𝔮 → Λ_𝔮/IΛ_𝔮`
  obtain ⟨l1map, hl1⟩ := exists_primePowerQuotient_lift q (fun i => φ (π i)) wb
    hwbunit hwpow he hn hπΛspan
  -- the twisted base `R₀ = Λ₀[t_1, …, t_d]` and its two structure maps
  let instkxR₀ : Algebra (MvPolynomial (Fin d) k)
      (MvPolynomial (Fin d) (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) :=
    (MvPolynomial.eval₂Hom
      ((MvPolynomial.C (σ := Fin d)).comp
        (algebraMap k (primePowerQuotient (Ideal.comap φ.toRingHom q) n)))
      (fun i => MvPolynomial.C (algebraMap (MvPolynomial (Fin m) k)
          (primePowerQuotient (Ideal.comap φ.toRingHom q) n) (π i)) *
        MvPolynomial.X i)).toAlgebra
  let moduleKxR₀ : Module (MvPolynomial (Fin d) k) (MvPolynomial (Fin d)
      (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) := Algebra.toModule
  let distribKxR₀ : DistribMulAction (MvPolynomial (Fin d) k) (MvPolynomial (Fin d)
      (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) := Module.toDistribMulAction
  let mulActionKxR₀ : MulAction (MvPolynomial (Fin d) k) (MvPolynomial (Fin d)
      (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) := DistribMulAction.toMulAction
  let moduleKxC : Module (MvPolynomial (Fin d) k) C := Algebra.toModule
  let instR₀LB : Algebra (MvPolynomial (Fin d)
      (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) (locBase Sit) :=
    (MvPolynomial.eval₂Hom l0map (fun i => algebraMap Sit.R (locBase Sit)
      (ν (MvPolynomial.X (Sum.inr i))))).toAlgebra
  let smulR₀LB : SMul (MvPolynomial (Fin d)
      (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) (locBase Sit) := instR₀LB.toSMul
  let smulkxLB : SMul (MvPolynomial (Fin d) k) (locBase Sit) := Algebra.toSMul
  let smulkxR₀ : SMul (MvPolynomial (Fin d) k) (MvPolynomial (Fin d)
      (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) := instkxR₀.toSMul
  have halgkxLB : ∀ x : MvPolynomial (Fin d) k,
      algebraMap (MvPolynomial (Fin d) k) (locBase Sit) x =
        algebraMap Sit.R (locBase Sit) (ν (twistedBaseHom π x)) := by
    intro x
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) k) Sit.R (locBase Sit), hkxR]
  have instTkxR₀LB : IsScalarTower (MvPolynomial (Fin d) k)
      (MvPolynomial (Fin d) (primePowerQuotient (Ideal.comap φ.toRingHom q) n))
      (locBase Sit) :=
    IsScalarTower.of_algebraMap_eq' (eval₂Hom_comp_twistedStructure π l0map
      (fun i => algebraMap Sit.R (locBase Sit) (ν (MvPolynomial.X (Sum.inr i)))) _
      (fun r => by
        rw [halgkxLB, IsScalarTower.algebraMap_apply k (MvPolynomial (Fin m) k)
          (primePowerQuotient (Ideal.comap φ.toRingHom q) n), hl0']
        congr 1
        rw [show twistedBaseHom π (MvPolynomial.C r) =
            algebraMap k (MvPolynomial (Fin m ⊕ Fin d) k) r from (twistedBaseHom π).commutes r,
          show MvPolynomial.rename (R := k) (σ := Fin m) (τ := Fin m ⊕ Fin d) Sum.inl
              (algebraMap k (MvPolynomial (Fin m) k) r) =
            algebraMap k (MvPolynomial (Fin m ⊕ Fin d) k) r from
            (MvPolynomial.rename (R := k) (σ := Fin m) (τ := Fin m ⊕ Fin d) Sum.inl).commutes r])
      fun i => by
        rw [halgkxLB, twistedBaseHom_X, twistedParameter, map_mul, map_mul, hl0'])
  let instR₀LT : Algebra (MvPolynomial (Fin d)
      (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) (locTarget Sit) :=
    ((algebraMap (locBase Sit) (locTarget Sit)).comp
      (algebraMap (MvPolynomial (Fin d)
        (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) (locBase Sit))).toAlgebra
  have instTR₀LBLT : IsScalarTower (MvPolynomial (Fin d)
      (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) (locBase Sit) (locTarget Sit) :=
    IsScalarTower.of_algebraMap_eq' rfl
  -- the structure maps into `Λ̄ = Λ_𝔮/𝔮ⁿΛ_𝔮`
  let instLbarLT : Algebra (primePowerQuotient q n) (locTarget Sit) := l1map.toAlgebra
  have hlbar : ∀ y : Λ, algebraMap (primePowerQuotient q n) (locTarget Sit)
      (algebraMap Λ (primePowerQuotient q n) y) =
      algebraMap Sit.Λ (locTarget Sit) (w y) := hl1
  let instR₀Lbar : Algebra (MvPolynomial (Fin d)
      (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) (primePowerQuotient q n) :=
    (MvPolynomial.eval₂Hom u
      (fun i => algebraMap Λ (primePowerQuotient q n) (δ i))).toAlgebra
  let instCLbar : Algebra C (primePowerQuotient q n) :=
    ((algebraMap Λ (primePowerQuotient q n)).comp
      (improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel grt)).toAlgebra
  let smulR₀Lbar : SMul (MvPolynomial (Fin d)
      (primePowerQuotient (Ideal.comap φ.toRingHom q) n))
      (primePowerQuotient q n) := instR₀Lbar.toSMul
  let smulCLbar : SMul C (primePowerQuotient q n) := instCLbar.toSMul
  let smulkxLbar : SMul (MvPolynomial (Fin d) k) (primePowerQuotient q n) := Algebra.toSMul
  have instTkxCLbar : IsScalarTower (MvPolynomial (Fin d) k) C (primePowerQuotient q n) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap (MvPolynomial (Fin d) k) (primePowerQuotient q n) x =
        algebraMap Λ (primePowerQuotient q n)
          (improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel grt
            (algebraMap (MvPolynomial (Fin d) k) C x))
      rw [← hcompat x,
        IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) k) Λ (primePowerQuotient q n)]
  have instTkxR₀Lbar : IsScalarTower (MvPolynomial (Fin d) k)
      (MvPolynomial (Fin d) (primePowerQuotient (Ideal.comap φ.toRingHom q) n))
      (primePowerQuotient q n) :=
    IsScalarTower.of_algebraMap_eq' (eval₂Hom_comp_twistedStructure π u
      (fun i => algebraMap Λ (primePowerQuotient q n) (δ i)) _
      (fun r => by
        rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) k) Λ (primePowerQuotient q n),
          IsScalarTower.algebraMap_apply k (MvPolynomial (Fin m) k)
            (primePowerQuotient (Ideal.comap φ.toRingHom q) n), hubar]
        congr 1
        rw [φ.commutes r, IsScalarTower.algebraMap_apply k (MvPolynomial (Fin d) k) Λ,
          MvPolynomial.algebraMap_eq])
      fun i => by
        rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) k) Λ (primePowerQuotient q n),
          hkxΛ, map_mul, hubar]
        ring)
  -- the compatibility of the two ways of mapping `C` into `Λ_𝔮/IΛ_𝔮`
  have hCcompat := algebraMap_locTarget_comp_eq_of_quotient Sit C Λ (primePowerQuotient q n)
    w (improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel grt)
    (algebraMap Λ (primePowerQuotient q n)) (fun _ => rfl) hlbar hCA
  have hRLT : ∀ y : Sit.R, algebraMap Sit.R (locTarget Sit) y =
      algebraMap Sit.Λ (locTarget Sit) (algebraMap Sit.R Sit.Λ y) := fun y =>
    IsScalarTower.algebraMap_apply Sit.R Sit.Λ (locTarget Sit) y
  have hLBLT : ∀ y : Sit.R, algebraMap (locBase Sit) (locTarget Sit)
      (algebraMap Sit.R (locBase Sit) y) = algebraMap Sit.R (locTarget Sit) y := fun y =>
    (IsScalarTower.algebraMap_apply Sit.R (locBase Sit) (locTarget Sit) y).symm
  -- the square `Λ₀ → Λ̄ → Λ_𝔮/IΛ_𝔮` equals `Λ₀ → (R/I)_𝔯 → Λ_𝔮/IΛ_𝔮`
  have hkeyΛ₀ : ∀ z : primePowerQuotient (Ideal.comap φ.toRingHom q) n,
      algebraMap (locBase Sit) (locTarget Sit) (l0map z) =
        algebraMap (primePowerQuotient q n) (locTarget Sit) (u z) :=
    RingHom.congr_fun (primePowerQuotient_ringHom_ext (Ideal.comap φ.toRingHom q)
      (f := (algebraMap (locBase Sit) (locTarget Sit)).comp l0map)
      (g := (algebraMap (primePowerQuotient q n) (locTarget Sit)).comp u) fun f => by
        change algebraMap (locBase Sit) (locTarget Sit)
            (l0map (algebraMap (MvPolynomial (Fin m) k)
              (primePowerQuotient (Ideal.comap φ.toRingHom q) n) f)) =
          algebraMap (primePowerQuotient q n) (locTarget Sit)
            (u (algebraMap (MvPolynomial (Fin m) k)
              (primePowerQuotient (Ideal.comap φ.toRingHom q) n) f))
        rw [hl0', hubar, hlbar, hLBLT, hRLT, hνw]
        congr 2
        exact AlgHom.congr_fun (twistedBaseToTarget_comp_rename φ δ) f)
  have instTR₀LbarLT : IsScalarTower (MvPolynomial (Fin d)
      (primePowerQuotient (Ideal.comap φ.toRingHom q) n)) (primePowerQuotient q n)
      (locTarget Sit) := by
    refine IsScalarTower.of_algebraMap_eq' (MvPolynomial.ringHom_ext (fun z => ?_) fun i => ?_)
    · change algebraMap (locBase Sit) (locTarget Sit)
          (MvPolynomial.eval₂Hom l0map _ (MvPolynomial.C z)) = _
      rw [MvPolynomial.eval₂Hom_C]
      change _ = algebraMap (primePowerQuotient q n) (locTarget Sit)
        (MvPolynomial.eval₂Hom u _ (MvPolynomial.C z))
      rw [MvPolynomial.eval₂Hom_C]
      exact hkeyΛ₀ z
    · change algebraMap (locBase Sit) (locTarget Sit)
          (MvPolynomial.eval₂Hom l0map _ (MvPolynomial.X i)) = _
      rw [MvPolynomial.eval₂Hom_X']
      change _ = algebraMap (primePowerQuotient q n) (locTarget Sit)
        (MvPolynomial.eval₂Hom u _ (MvPolynomial.X i))
      rw [MvPolynomial.eval₂Hom_X', hlbar, hLBLT, hRLT, hνw]
      congr 2
      exact twistedBaseToTarget_X_inr φ δ i
  exact isResolvableAfterLocalizing_of_hasSmoothFactorization_tensor Sit
    (MvPolynomial (Fin d) k) C
    (MvPolynomial (Fin d) (primePowerQuotient (Ideal.comap φ.toRingHom q) n))
    (primePowerQuotient q n) hCcompat
    (hasSmoothFactorization_tensor_of_exists (MvPolynomial (Fin d) k) C
      (MvPolynomial (Fin d) (primePowerQuotient (Ideal.comap φ.toRingHom q) n))
      (primePowerQuotient q n) hres)

/-- **Items (22)–(26) of the proof of Stacks 07FJ from items (24)–(26).** Granting
`Stacks.Smoothing.TwistedQuotientSmoothFactorization` — Stacks 07G8, 07G9 and 07GA — the twisted
quotient chain of item (18) is resolvable after localizing at `𝔮`, which is
`Stacks.Smoothing.TwistedQuotientLocallyResolvable`.

The content added here is items (22) and (23), Stacks 07G6 and 07G7: the chain
`R/I → (R ⊗_{k[x]} C)/I → Λ/IΛ` with `R = k[y_1, …, y_m, t_1, …, t_d]`, `γ_i = π_i t_i`,
`e = 8c` and `I = (γ_1^e, …, γ_d^e)` is assembled as a
`Stacks.Smoothing.LocalSmoothingSituation`; its base-change square over `k[x_1, …, x_d]` is
`Stacks.Smoothing.isPushout_quotient_of_isPushout`; the extension `IΛ` of `I` is identified with
`((δ_iφ(π_i))^e)` and shown to lie in `𝔮`, so that `𝔮/IΛ` has `𝔮` as preimage; and the two
structure maps and the remaining compatibilities are handed to
`Stacks.Smoothing.isResolvableAfterLocalizing_twistedQuotient`.

No hypothesis beyond the telescope of `TwistedQuotientLocallyResolvable` is used, and no
hypothesis of it is strengthened: `TwistedQuotientSmoothFactorization` repeats that telescope up
to `hcompat`. -/
theorem twistedQuotientLocallyResolvable_of_smoothFactorization
    (hres : TwistedQuotientSmoothFactorization.{u}) : TwistedQuotientLocallyResolvable.{u} := by
  intro k A Λ _ _ _ _ _ _ _ _ _ _ q _ t d m N n c a C _ _ _ _ _ grt φ gl u D aD π δ lam
    D' _ _ _ cc b' hN hc hd1 hn hNn hnbound hq ha hqN hd hCalg hgrt hmapφ hgφ hgflat hu
    hDsub hAD instP1 instP2 instQ1 instQ2 instD1 instD2 hess hDflat hdimP hπmem hπspan
    hπΛspan instLHcc instLHb' hess' hflat' hcomp' hδq hrel hlamD' hδD' hstdC hcompat
    I ID IL hfp hqb
  -- re-declare the instances that the statement's `letI`s inlined
  let instkxP : Algebra (MvPolynomial (Fin d) k) (MvPolynomial (Fin m ⊕ Fin d) k) :=
    (twistedBaseHom π).toRingHom.toAlgebra
  let instPL : Algebra (MvPolynomial (Fin m ⊕ Fin d) k) Λ :=
    (twistedBaseToTarget φ δ).toRingHom.toAlgebra
  let instkxL : Algebra (MvPolynomial (Fin d) k) Λ :=
    ((algebraMap (MvPolynomial (Fin m ⊕ Fin d) k) Λ).comp
      (algebraMap (MvPolynomial (Fin d) k) (MvPolynomial (Fin m ⊕ Fin d) k))).toAlgebra
  have instTkxPL : IsScalarTower (MvPolynomial (Fin d) k) (MvPolynomial (Fin m ⊕ Fin d) k) Λ :=
    IsScalarTower.of_algebraMap_eq' rfl
  let instTensL : Algebra (MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) Λ :=
    (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom (MvPolynomial (Fin d) k)
        (MvPolynomial (Fin m ⊕ Fin d) k) Λ)
      ({ toRingHom := improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel grt,
          commutes' := fun y => (hcompat y).symm } : C →ₐ[MvPolynomial (Fin d) k] Λ)
      (fun _ _ => Commute.all _ _)).toRingHom.toAlgebra
  let instQuotAlg : Algebra (MvPolynomial (Fin m ⊕ Fin d) k ⧸ I) (Λ ⧸ IL) :=
    ((algebraMap ((MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) ⧸ ID)
      (Λ ⧸ IL)).comp (algebraMap (MvPolynomial (Fin m ⊕ Fin d) k ⧸ I)
        ((MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) ⧸ ID))).toAlgebra
  have instQuotTower : IsScalarTower (MvPolynomial (Fin m ⊕ Fin d) k ⧸ I)
      ((MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) ⧸ ID) (Λ ⧸ IL) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let Sit : LocalSmoothingSituation.{u, u, u} :=
    { R := MvPolynomial (Fin m ⊕ Fin d) k ⧸ I,
      A := (MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) ⧸ ID,
      Λ := Λ ⧸ IL, q := Ideal.map (Ideal.Quotient.mk IL) q,
      finitePresentation := hfp, isPrimeQ := hqb }
  have instSitQ : Sit.q.IsPrime := hqb
  have instSitBP0 : Sit.basePrime.IsPrime := Ideal.comap_isPrime _ _
  change Sit.IsResolvableAfterLocalizing
  -- the chain of the situation is the base change of `C` along `k[x] → R/I`
  have instPushSit : Algebra.IsPushout (MvPolynomial (Fin d) k) Sit.R C Sit.A :=
    isPushout_quotient_of_isPushout (MvPolynomial (Fin d) k) (MvPolynomial (Fin m ⊕ Fin d) k) C
      (MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) I
  -- the extension of `I` to `Λ`
  have instTPTmL : IsScalarTower (MvPolynomial (Fin m ⊕ Fin d) k)
      (MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) Λ := by
    exact IsScalarTower.of_algebraMap_eq fun x =>
      (lift_algebraMap_left (IsScalarTower.toAlgHom (MvPolynomial (Fin d) k)
          (MvPolynomial (Fin m ⊕ Fin d) k) Λ)
        ({ toRingHom := improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel grt,
            commutes' := fun y => (hcompat y).symm } : C →ₐ[MvPolynomial (Fin d) k] Λ)
        (fun _ _ => Commute.all _ _) x).symm
  have hILspan : IL = Ideal.span (Set.range fun i => (δ i * φ (π i)) ^ (8 * c)) := by
    refine map_map_span_pow_eq _ _ (twistedParameter π) δ (fun i => φ (π i)) ?_ rfl rfl rfl
    intro i
    exact mul_map_one_eq (improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel grt)
      (twistedBaseToTarget φ δ (twistedParameter π i))
      (twistedBaseToTarget_twistedParameter φ π δ i)
  have hILq : IL ≤ q :=
    span_mul_pow_le q (fun i => φ (π i)) δ (fun i => Ideal.mem_comap.mp (hπmem i))
      (show 1 ≤ 8 * c by omega) hILspan
  -- the two structure maps of the situation, read off the twisted base
  have hkxR : ∀ x : MvPolynomial (Fin d) k, algebraMap (MvPolynomial (Fin d) k) Sit.R x =
      Ideal.Quotient.mk I (twistedBaseHom π x) := fun _ => rfl
  have hkxΛ : ∀ i, algebraMap (MvPolynomial (Fin d) k) Λ (MvPolynomial.X i) =
      δ i * φ (π i) := by
    intro i
    change twistedBaseToTarget φ δ (twistedBaseHom π (MvPolynomial.X i)) = _
    rw [twistedBaseHom_X, twistedBaseToTarget_twistedParameter]
  have instTkkxΛ : IsScalarTower k (MvPolynomial (Fin d) k) Λ :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap k Λ r = twistedBaseToTarget φ δ
        (twistedBaseHom π (algebraMap k (MvPolynomial (Fin d) k) r))
      rw [(twistedBaseHom π).commutes r, (twistedBaseToTarget φ δ).commutes r]
  have hνw : ∀ x, algebraMap Sit.R Sit.Λ (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk IL (twistedBaseToTarget φ δ x) := by
    intro x
    change algebraMap ((MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) ⧸ ID) (Λ ⧸ IL)
        (algebraMap (MvPolynomial (Fin m ⊕ Fin d) k ⧸ I)
          ((MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) ⧸ ID)
          (Ideal.Quotient.mk I x)) = _
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient,
      Ideal.Quotient.algebraMap_quotient_map_quotient,
      ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin m ⊕ Fin d) k)
        (MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) Λ]
    rfl
  have hwq : ∀ y : Λ, Ideal.Quotient.mk IL y ∈ Sit.q ↔ y ∈ q := by
    intro y
    refine ⟨fun hmem => ?_, fun hmem => Ideal.mem_map_of_mem _ hmem⟩
    have h2 : y ∈ Ideal.comap (Ideal.Quotient.mk IL) (Ideal.map (Ideal.Quotient.mk IL) q) := hmem
    rwa [comap_map_quotient q IL hILq] at h2
  have hνI : ∀ i, Ideal.Quotient.mk I (twistedParameter π i ^ (8 * c)) = 0 := fun i =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  -- the structure map `Λ̄ = Λ_𝔮/𝔮ⁿΛ_𝔮` receives `k[y_1, …, y_m]` through `φ`
  have hubar := primePowerQuotient_map_algebraMap q φ gl u hgφ hu
  -- the compatibility of the two ways of mapping `C` into `Λ/IΛ`
  have hCA : ∀ cc' : C, algebraMap Sit.A Sit.Λ (algebraMap C Sit.A cc') =
      Ideal.Quotient.mk IL
        (improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel grt cc') := by
    intro cc'
    have h2 : algebraMap C Sit.A cc' = Ideal.Quotient.mk ID
        (algebraMap C (MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) cc') :=
      (Ideal.Quotient.mk_algebraMap (R₁ := C)
        (A := MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) ID cc').symm
    have h3 : algebraMap (MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) Λ
        (algebraMap C (MvPolynomial (Fin m ⊕ Fin d) k ⊗[MvPolynomial (Fin d) k] C) cc') =
        improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel grt cc' :=
      lift_algebraMap_right (IsScalarTower.toAlgHom (MvPolynomial (Fin d) k)
          (MvPolynomial (Fin m ⊕ Fin d) k) Λ)
        ({ toRingHom := improvedAlgebraToTarget N a (fun i => δ i * φ (π i)) lam hrel grt,
            commutes' := fun y => (hcompat y).symm } : C →ₐ[MvPolynomial (Fin d) k] Λ)
        (fun _ _ => Commute.all _ _) cc'
    rw [h2, Ideal.Quotient.algebraMap_quotient_map_quotient, h3]
  exact isResolvableAfterLocalizing_twistedQuotient Sit q a C grt φ u π δ lam hrel
    (Ideal.Quotient.mk I) (Ideal.Quotient.mk IL) hkxR hkxΛ hνw hwq hνI hcompat hCA hubar
    hδq (show 1 ≤ 8 * c by omega) hnbound hπspan hπΛspan
    (hres k A Λ q a C grt φ gl u D aD π δ lam D' cc b' hN hc hd1 hn hNn hnbound hq ha hqN hd
      hCalg hgrt hmapφ hgφ hgflat hu hDsub hAD instP1 instP2 instQ1 instQ2 instD1 instD2
      hess hDflat hdimP hπmem hπspan hπΛspan instLHcc instLHb' hess' hflat' hcomp' hδq hrel
      hlamD' hδD' hstdC hcompat)

end Residual

end Stacks.Smoothing

end
