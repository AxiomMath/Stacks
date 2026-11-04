module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-! # The fibre of `Spec S → Spec R` as a quotient of a localisation

Stacks tag 00E7 (Lemma 10.18.6), clause (2) ⇔ clause (3): for a prime `𝔭 ⊂ R` and an
`R`-algebra `S`,

  `κ(𝔭) ⊗_R S ≠ 0`  ↔  `S_𝔭 / 𝔭 S_𝔭 ≠ 0`.

Here `S_𝔭` is the localisation of `S` at `φ(R ∖ 𝔭)` — *not* at a prime of `S`. Mathlib spells
that multiplicative set `Algebra.algebraMapSubmonoid S p.primeCompl`.

The mathematics is entirely Mathlib's: `Ideal.Fiber.algEquivAux₁` already identifies the fibre
`κ(𝔭) ⊗_R S` with `Sₚ ⧸ 𝔭S·Sₚ` for the concrete `Sₚ = Localization …`. What is added here is

* `Ideal.Fiber.ringEquivQuotient`, the same isomorphism for an *arbitrary* localisation `Sₚ`
  of `S` at that multiplicative set, and stated with the ideal in the form `𝔭 · Sₚ` extended
  directly from `R` rather than through `S`;
* `Ideal.nontrivial_fiber_iff`, the clause equivalence the tag actually asserts.

The abstract form is the useful one: it is the hypothesis block Mathlib's own
`IsLocalization.AtPrime` API uses, the concrete `Localization …` satisfies all of it by
instance search, and clause (4) of the same tag — `(S/𝔭S)_𝔭 ≠ 0` — is another localisation of
the same ring at the same submonoid, so it plugs into this statement rather than needing a
separate isomorphism.

Two elaboration hazards, both of which present as timeouts rather than type errors:

* `Ideal.Fiber.algEquivAux₁` cannot be *used* without `Algebra S (p.Fiber S)` in scope, which
  is not a global instance — hence the `attribute [local instance] … in` below, scoped per
  declaration as Mathlib's own `Fiber.lean` does it. Note `#check` on the lemma succeeds
  without it, because the `letI` lives inside its type, so the omission only bites on use.
* Do not chain these through `.trans` in term mode against
  `PrimeSpectrum.nontrivial_iff_mem_rangeComap`; that times out at `whnf`. Use
  `rw [← …]` followed by `exact`. See `StacksCore.RingTheory.Spectrum.Prime.RingHom`.
-/

@[expose] public section

open Algebra

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
variable (Sp : Type*) [CommRing Sp] [Algebra S Sp] [Algebra R Sp] [IsScalarTower R S Sp]
  [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sp]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The fibre `κ(𝔭) ⊗_R S` is isomorphic to `Sₚ ⧸ 𝔭Sₚ`, for *any* localisation `Sₚ` of `S` at
the image of `R ∖ 𝔭`.

This generalises `Ideal.Fiber.algEquivAux₁`, which is the case `Sₚ = Localization …`, and
restates the ideal as `𝔭 · Sₚ` extended from `R` in one step instead of through `S`. The two
spellings agree by `Ideal.map_map` and `IsScalarTower.algebraMap_eq`. -/
noncomputable def Fiber.ringEquivQuotient :
    p.Fiber S ≃+* (Sp ⧸ p.map (algebraMap R Sp)) :=
  (Fiber.algEquivAux₁ p).toRingEquiv.trans <|
    Ideal.quotientEquiv _ _
      (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid S p.primeCompl)
        (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) Sp).toRingEquiv <| by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  ext r
  simp [← IsScalarTower.algebraMap_apply R S Sp]

/-- **Stacks 00E7**, clause (2) ⇔ clause (3): the fibre `κ(𝔭) ⊗_R S` is nonzero if and only if
`S_𝔭 / 𝔭 S_𝔭` is nonzero.

Both are ways of saying the fibre of `Spec S → Spec R` over `𝔭` is nonempty; for the link to
clause (1), that `𝔭` lies in the image, see `PrimeSpectrum.nontrivial_iff_mem_rangeComap`
(tagged in `StacksCore.RingTheory.Spectrum.Prime.RingHom`). -/
@[stacks 00E7 "(2) ⇔ (3)"]
theorem nontrivial_fiber_iff :
    Nontrivial (p.Fiber S) ↔ Nontrivial (Sp ⧸ p.map (algebraMap R Sp)) :=
  (Fiber.ringEquivQuotient p Sp).toEquiv.nontrivial_congr

/-! ### Clause (4): localising the quotient instead of quotienting the localisation

Stacks 00E7 clause (4) is `(S/𝔭S)_𝔭 ≠ 0`, where the subscript again means localisation at the
image of `R ∖ 𝔭`. This is clause (3) with the two operations in the other order, and the two
agree because **localisation commutes with quotients** — which Mathlib provides in the most
convenient possible form, as the instance

  `IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) M) (S ⧸ I.map (algebraMap R S))`

in `Mathlib.RingTheory.Localization.Ideal`. Instantiated at `I = 𝔭S`, it says `Sₚ ⧸ 𝔭Sₚ` *is* a
localisation of `S ⧸ 𝔭S` at the image of `R ∖ 𝔭`, so clauses (3) and (4) are two localisations
of the same ring at the same submonoid and `IsLocalization.algEquiv` identifies them. No
isomorphism has to be built by hand.

The submonoid bookkeeping is one `@[simp]` lemma, `Algebra.algebraMapSubmonoid_map_map`: the
image in `S/𝔭S` of the image in `S` of `R ∖ 𝔭` is the image in `S/𝔭S` of `R ∖ 𝔭`.

`S` is an explicit argument below because it does not appear in the conclusion of
`nontrivial_quotient_localization_iff` — only inside the instance arguments — so it is neither
inferable nor nameable otherwise. That is also why the statement needs `include S`.
-/

-- From here on `S` is explicit: it does not appear in the conclusion of
-- `nontrivial_quotient_localization_iff`, only inside instance arguments, so it is neither
-- inferable at use sites nor nameable in the proof without this.
variable (S)
variable (SpS : Type*) [CommRing SpS] [Algebra (S ⧸ p.map (algebraMap R S)) SpS]
  [IsLocalization (Algebra.algebraMapSubmonoid (S ⧸ p.map (algebraMap R S)) p.primeCompl) SpS]

/-- `(S/𝔭S)_𝔭 ≃+* S_𝔭/𝔭S_𝔭`: localising the quotient agrees with quotienting the localisation.

Both sides are localisations of `S ⧸ 𝔭S` at the image of `R ∖ 𝔭` — the right-hand side by the
`IsLocalization` instance for quotients — so this is uniqueness of localisation, not a
construction. The final `Ideal.quotEquivOfEq` only rewrites `𝔭S` extended through `S` into `𝔭`
extended directly to `Sₚ`; the quotient-algebra instance fires solely for the former spelling. -/
noncomputable def quotientLocalizationRingEquiv :
    SpS ≃+* (Sp ⧸ p.map (algebraMap R Sp)) :=
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (S ⧸ p.map (algebraMap R S)) p.primeCompl)
      (Sp ⧸ (p.map (algebraMap R S)).map (algebraMap S Sp)) := by
    rw [← Algebra.algebraMapSubmonoid_map_map (A := S)]
    infer_instance
  (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid (S ⧸ p.map (algebraMap R S)) p.primeCompl) _
    (Sp ⧸ (p.map (algebraMap R S)).map (algebraMap S Sp))).toRingEquiv.trans <|
    Ideal.quotEquivOfEq (by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq])

include S in
/-- **Stacks 00E7**, clause (3) ⇔ clause (4): `S_𝔭 / 𝔭 S_𝔭` is nonzero if and only if
`(S/𝔭S)_𝔭` is nonzero. -/
@[stacks 00E7 "(3) ⇔ (4)"]
theorem nontrivial_quotient_localization_iff :
    Nontrivial SpS ↔ Nontrivial (Sp ⧸ p.map (algebraMap R Sp)) :=
  (quotientLocalizationRingEquiv S p Sp SpS).toEquiv.nontrivial_congr

end Ideal
