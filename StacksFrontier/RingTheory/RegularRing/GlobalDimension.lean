module

public import StacksFrontier.Data.ENat.WithBotNatCast
public import StacksFrontier.RingTheory.GlobalDimension.Localization
public import StacksFrontier.RingTheory.RegularLocalRing.GlobalDimension
public import StacksFrontier.RingTheory.RegularRing.Defs
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe v

universe u

/-!
# Regular rings of dimension `n` are the rings of global dimension `n`

Let `R` be a Noetherian ring and `n : ℕ`. This file proves Stacks 00OE: the global dimension of
`R` is `n` if and only if `R` is a regular ring of dimension `n`, if and only if the localizations
at the maximal ideals are regular local rings of dimension `≤ n` with the bound attained, if and
only if the same holds at all primes.

Everything is deduced from the bound form of the equivalence,
`gl dim R ≤ m ↔ R is regular and dim R ≤ m`, whose two directions are the two halves of the
source's argument. From left to right, the bound passes to every localization `R_𝔭` (Lemma
00O8 (2)), so Proposition 00OC makes each `R_𝔭` a regular local ring with `dim R_𝔭 ≤ m`; as
`dim R` is the supremum of the `dim R_𝔭`, this is regularity of `R` together with `dim R ≤ m`.
From right to left, `dim R_𝔪 ≤ dim R ≤ m` for a maximal ideal `𝔪`, so Proposition 00OC bounds
`gl dim R_𝔪` and Lemma 00O9 assembles the bounds at the maximal ideals into `gl dim R ≤ m`.

Since an element of `WithBot ℕ∞` other than `⊥` is determined by the natural numbers bounding it,
the bound form says exactly that a regular Noetherian ring satisfies `gl dim R = dim R`, and this
equality is what turns the value `n` of one side into the value `n` of the other.

Items (3) and (4) differ only in the family of primes they quantify over, and neither direction of
their equivalence with item (2) uses anything about that family: what item (2) gives is the `∀` at
all the primes together with the `∃` at a maximal ideal, of which items (3) and (4) are the two
weakenings, and what recovers item (2) is the `∀` at the maximal ideals alone together with any one
prime attaining the bound. So each item is a weakening of
`forall_isRegularLocalRing_atPrime_and_exists_isMaximal` and a strengthening of the hypotheses of
`isRegularRing_and_ringKrullDim_eq_of_forall_isMaximal`. The dimension theory those two need is
that `dim R_𝔭 = ht 𝔭`, so that a bound on all the `dim R_𝔭` is a bound on `dim R`, and that a ring
of finite Krull dimension has a maximal ideal whose height is that dimension
(`Ideal.exists_isMaximal_height`), which is where the attainment of the bound comes from.

## Main results

* `Stacks.RegularRing.GlobalDimension.solution`: the four conditions of Lemma 00OE, for a fixed `n
  : ℕ`, are equivalent.

## Implementation notes

Global dimension appears as the supremum `⨆ M : ModuleCat.{u} R, projectiveDimension M` in
`WithBot ℕ∞`, as in the statement; the bridge to the per-`n` form
`∀ M, HasProjectiveDimensionLE M n`, in which 00O9 and 00O8 bound it, is
`CategoryTheory.projectiveDimension_le_iff`.

Lemma 00O8 (2), that a localization inherits a bound on the global dimension of `R`, has no separate
statement in this tree, so it is proved here as `iSup_projectiveDimension_localization_le`, in the form of
the inequality `gl dim S⁻¹R ≤ gl dim R`, from Mathlib's
`ModuleCat.projectiveDimension_le_projectiveDimension_of_isLocalizedModule`, which localizes the
projective dimension of a single module: an `S⁻¹R`-module `X` is its own localization, restriction
of scalars along `algebraMap R (S⁻¹R)` making `LinearMap.id` an `IsLocalizedModule` for `S`
(`isLocalizedModule_id`), so `S⁻¹X ≅ X` as `S⁻¹R`-modules and the two projective dimensions agree
by `ModuleCat.projectiveDimension_eq_of_linearEquiv`.

The zero ring is separated off first: it has no prime ideal, and both its global dimension and its
Krull dimension are `⊥`, so all four conditions fail and `List.tfae_of_forall` closes the case. Its
exclusion is also what makes the value `n` recoverable from the bounds: `⊥` and `0` satisfy the
same bounds `≤ m`, so nontriviality of `R` is exactly what rules `⊥` out. Which ring `⊥` belongs
to is `iSup_projectiveDimension_eq_bot_iff_subsingleton`, the analogue for global dimension of
Mathlib's `ringKrullDim_eq_bot_iff_subsingleton`.

## References

* [StacksProject 00OE](https://stacks.math.columbia.edu/tag/00OE)
* [StacksProject 00OC](https://stacks.math.columbia.edu/tag/00OC)
* [StacksProject 00O9](https://stacks.math.columbia.edu/tag/00O9)
* [StacksProject 00O8](https://stacks.math.columbia.edu/tag/00O8)
* [StacksProject 00OD](https://stacks.math.columbia.edu/tag/00OD)
-/

@[expose] public section



open CategoryTheory

namespace Stacks.RegularRing.GlobalDimension

/-! ### Bounds in `WithBot ℕ∞` -/

/-- An element of `WithBot ℕ∞` other than `⊥` is determined by the natural numbers bounding it: if
every natural bound of `y ≠ ⊥` bounds `x`, then `x ≤ y`. -/
private lemma le_of_forall_natCast_le {x y : WithBot ℕ∞} (hy : y ≠ ⊥)
    (h : ∀ m : ℕ, y ≤ (m : WithBot ℕ∞) → x ≤ (m : WithBot ℕ∞)) : x ≤ y := by
  induction y with
  | bot => exact absurd rfl hy
  | coe a =>
    induction a with
    | top => exact le_top
    | coe k => exact h k le_rfl

/-! ### The Krull dimensions of the localizations -/

/-- The Krull dimension of the localization of `R` at a prime `𝔭` is the height of `𝔭`. -/
private lemma ringKrullDim_atPrime {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    ringKrullDim (Localization.AtPrime p) = (p.height : WithBot ℕ∞) :=
  IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)

/-- The Krull dimension of `R_𝔭` is at most that of `R`. -/
private lemma ringKrullDim_atPrime_le {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    ringKrullDim (Localization.AtPrime p) ≤ ringKrullDim R :=
  (ringKrullDim_atPrime p).trans_le Ideal.height_le_ringKrullDim_of_isPrime

/-- A bound on the Krull dimensions of all the localizations `R_𝔭` is a bound on the Krull
dimension of `R`. -/
private lemma ringKrullDim_le_of_forall_ringKrullDim_atPrime_le {R : Type u} [CommRing R]
    {x : WithBot ℕ∞}
    (h : ∀ p : Ideal R, ∀ _ : p.IsPrime, ringKrullDim (Localization.AtPrime p) ≤ x) :
    ringKrullDim R ≤ x :=
  (ringKrullDim_le_iff_height_le x).mpr fun p hp =>
    (ringKrullDim_atPrime p).symm.trans_le (h p hp)

/-- A ring of finite Krull dimension has a maximal ideal at which the localization has the same
Krull dimension: `Ideal.exists_isMaximal_height` read through `ringKrullDim_atPrime`. This is where
the attainment of the bound in items (3) and (4) comes from. -/
private lemma exists_isMaximal_ringKrullDim_atPrime_eq (R : Type u) [CommRing R]
    [FiniteRingKrullDim R] :
    ∃ 𝔪 : Ideal R, ∃ _ : 𝔪.IsMaximal,
      ringKrullDim (Localization.AtPrime 𝔪) = ringKrullDim R := by
  obtain ⟨𝔪, h𝔪, hh⟩ := Ideal.exists_isMaximal_height (R := R)
  exact ⟨𝔪, h𝔪, (ringKrullDim_atPrime 𝔪).trans hh⟩

/-! ### The global dimension -/

/-- **A bound on the global dimension, read off the supremum.** The supremum of the projective
dimensions of the objects of an abelian category is `≤ n` exactly when every object has projective
dimension `≤ n`. -/
private lemma iSup_projectiveDimension_le_natCast_iff {C : Type*} [Category C] [Abelian C]
    (n : ℕ) : (⨆ X : C, projectiveDimension X) ≤ (n : WithBot ℕ∞) ↔
      ∀ X : C, HasProjectiveDimensionLE X n :=
  ⟨fun h X => (projectiveDimension_le_iff X n).mp ((le_iSup _ X).trans h),
    fun h => iSup_le fun X => (projectiveDimension_le_iff X n).mpr (h X)⟩

/-- **The global dimension is `⊥` exactly for the zero ring**: over the zero ring every module is
zero, and over a nonzero ring `R` itself is a nonzero module. This is the analogue for global
dimension of `ringKrullDim_eq_bot_iff_subsingleton`. -/
private lemma iSup_projectiveDimension_eq_bot_iff_subsingleton (R : Type u) [CommRing R] :
    (⨆ M : ModuleCat.{u} R, projectiveDimension M) = ⊥ ↔ Subsingleton R := by
  simp only [iSup_eq_bot, projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton]
  exact ⟨fun h => h (ModuleCat.of R R), fun _ M => Module.subsingleton R M⟩

/-- **Stacks 00O8 (2): the global dimension does not grow under localization.** The supremum of
the projective dimensions of the `S⁻¹R`-modules is at most the supremum over the `R`-modules,
because an `S⁻¹R`-module is the localization of itself viewed as an `R`-module. -/
@[ega "0 17.2.10" "partial"]
private lemma iSup_projectiveDimension_localization_le {R : Type u} [CommRing R] [Small.{v} R]
    (S : Submonoid R) :
    (⨆ X : ModuleCat.{v} (Localization S), projectiveDimension X) ≤
      ⨆ M : ModuleCat.{v} R, projectiveDimension M := by
  have : Small.{v} (Localization S) := small_of_surjective Localization.mkHom_surjective
  refine iSup_le fun X => ?_
  let _ : Module R (X : Type v) := Module.compHom (X : Type v) (algebraMap R (Localization S))
  have : IsScalarTower R (Localization S) (X : Type v) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsLocalizedModule S (LinearMap.id : (X : Type v) →ₗ[R] (X : Type v)) :=
    isLocalizedModule_id S (X : Type v) (Localization S)
  set M := ModuleCat.of R (X : Type v)
  calc projectiveDimension X
      = projectiveDimension (M.localizedModule S) :=
        (ModuleCat.projectiveDimension_eq_of_linearEquiv
          (LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
            (IsLocalizedModule.linearEquiv S (M.localizedModuleMkLinearMap S)
              (LinearMap.id : (X : Type v) →ₗ[R] (X : Type v))))).symm
    _ ≤ projectiveDimension M :=
        ModuleCat.projectiveDimension_le_projectiveDimension_of_isLocalizedModule S M
    _ ≤ _ := le_iSup _ M

/-! ### Stacks 00OE -/

/-- **Proposition 00OC with a bound.** A Noetherian local ring has global dimension `≤ m` exactly
when it is a regular local ring of Krull dimension `≤ m`. -/
@[ega "III 6.5.5"]
private lemma iSup_projectiveDimension_le_natCast_iff_isRegularLocalRing (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (m : ℕ) :
    (⨆ M : ModuleCat.{u} A, projectiveDimension M) ≤ (m : WithBot ℕ∞) ↔
      IsRegularLocalRing A ∧ ringKrullDim A ≤ (m : WithBot ℕ∞) := by
  have key := (isRegularLocalRing_tfae (R := A)).out 3 4
  refine ⟨fun h => ?_, fun ⟨hreg, hd⟩ => by rw [key.mp hreg]; exact hd⟩
  have hreg := ((isRegularLocalRing_tfae (R := A)).out 2 3).mp
    (ne_top_of_le_ne_top (natCast_ne_top_withBot m) h)
  exact ⟨hreg, by rw [← key.mp hreg]; exact h⟩

/-- **Stacks 00O9 read through Proposition 00OC.** For a Noetherian ring the global dimension is
`≤ m` exactly when every localization at a maximal ideal is a regular local ring of Krull
dimension `≤ m`. -/
private lemma iSup_projectiveDimension_le_natCast_iff_forall_isMaximal {R : Type u} [CommRing R]
    [IsNoetherianRing R] (m : ℕ) :
    (⨆ M : ModuleCat.{u} R, projectiveDimension M) ≤ (m : WithBot ℕ∞) ↔
      ∀ 𝔪 : Ideal R, ∀ _ : 𝔪.IsMaximal, IsRegularLocalRing (Localization.AtPrime 𝔪) ∧
        ringKrullDim (Localization.AtPrime 𝔪) ≤ (m : WithBot ℕ∞) := by
  rw [iSup_projectiveDimension_le_natCast_iff,
    Ring.forall_hasProjectiveDimensionLE_iff_forall_isLocalization_maximal m
      (fun 𝔪 _ => Localization.AtPrime 𝔪)]
  exact ⟨fun h 𝔪 _ => (iSup_projectiveDimension_le_natCast_iff_isRegularLocalRing _ m).mp
      ((iSup_projectiveDimension_le_natCast_iff m).mpr (h 𝔪)),
    fun h 𝔪 h𝔪 => (iSup_projectiveDimension_le_natCast_iff m).mp
      ((iSup_projectiveDimension_le_natCast_iff_isRegularLocalRing _ m).mpr (h 𝔪 h𝔪))⟩

/-- The localizations of a regular ring at the primes are regular local rings, of Krull dimension
bounded by that of the ring: the `∀` half of items (3) and (4). -/
private lemma isRegularLocalRing_atPrime_and_ringKrullDim_le {R : Type u} [CommRing R]
    {x : WithBot ℕ∞} (hreg : IsRegularRing R) (hdim : ringKrullDim R ≤ x) (p : Ideal R)
    [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) ∧
      ringKrullDim (Localization.AtPrime p) ≤ x :=
  ⟨hreg.isRegularLocalRing_localization p, (ringKrullDim_atPrime_le p).trans hdim⟩

/-- **Stacks 00OE in the form of a bound: a Noetherian ring has global dimension `≤ m` exactly
when it is a regular ring of Krull dimension `≤ m`.** Left to right, the bound passes to each
localization `R_𝔭` (Lemma 00O8 (2)) and Proposition 00OC makes it regular of dimension `≤ m`;
right to left, the bound `dim R_𝔪 ≤ m` at the maximal ideals bounds `gl dim R_𝔪` by Proposition
00OC, and Lemma 00O9 assembles those bounds into a bound for `gl dim R`. -/
@[ega "III 6.5.5" "T = Spec R affine"]
private lemma iSup_projectiveDimension_le_natCast_iff_isRegularRing (R : Type u) [CommRing R]
    [IsNoetherianRing R] (m : ℕ) :
    (⨆ M : ModuleCat.{u} R, projectiveDimension M) ≤ (m : WithBot ℕ∞) ↔
      IsRegularRing R ∧ ringKrullDim R ≤ (m : WithBot ℕ∞) := by
  refine ⟨fun h => ?_, fun ⟨hreg, hdim⟩ =>
    (iSup_projectiveDimension_le_natCast_iff_forall_isMaximal m).mpr fun 𝔪 _ =>
      isRegularLocalRing_atPrime_and_ringKrullDim_le hreg hdim 𝔪⟩
  have hp : ∀ p : Ideal R, ∀ _ : p.IsPrime, IsRegularLocalRing (Localization.AtPrime p) ∧
      ringKrullDim (Localization.AtPrime p) ≤ (m : WithBot ℕ∞) := fun p hp =>
    (iSup_projectiveDimension_le_natCast_iff_isRegularLocalRing _ m).mp
      ((iSup_projectiveDimension_localization_le p.primeCompl).trans h)
  exact ⟨isRegularRing_iff.mpr fun p _ => (hp p ‹_›).1,
    ringKrullDim_le_of_forall_ringKrullDim_atPrime_le fun p h => (hp p h).2⟩

/-- **The global dimension of a regular Noetherian ring is its Krull dimension.** Both are
elements of `WithBot ℕ∞` other than `⊥`, and by
`iSup_projectiveDimension_le_natCast_iff_isRegularRing` they satisfy the same bounds `≤ m`. -/
private lemma iSup_projectiveDimension_eq_ringKrullDim (R : Type u) [CommRing R] [Nontrivial R]
    [IsNoetherianRing R] (hreg : IsRegularRing R) :
    (⨆ M : ModuleCat.{u} R, projectiveDimension M) = ringKrullDim R :=
  le_antisymm
    (le_of_forall_natCast_le
      (fun h => not_subsingleton R (ringKrullDim_eq_bot_iff_subsingleton.mp h))
      fun m hm => (iSup_projectiveDimension_le_natCast_iff_isRegularRing R m).mpr ⟨hreg, hm⟩)
    (le_of_forall_natCast_le
      (fun h => not_subsingleton R ((iSup_projectiveDimension_eq_bot_iff_subsingleton R).mp h))
      fun m hm => ((iSup_projectiveDimension_le_natCast_iff_isRegularRing R m).mp hm).2)

/-- **Items (1) and (2) of Lemma 00OE.** A nonzero Noetherian ring has global dimension `n` exactly
when it is a regular ring of Krull dimension `n`: the bounds of
`iSup_projectiveDimension_le_natCast_iff_isRegularRing` pin the value through
`iSup_projectiveDimension_eq_ringKrullDim`. -/
private lemma iSup_projectiveDimension_eq_natCast_iff_isRegularRing (R : Type u) [CommRing R]
    [Nontrivial R] [IsNoetherianRing R] (n : ℕ) :
    (⨆ M : ModuleCat.{u} R, projectiveDimension M) = (n : WithBot ℕ∞) ↔
      IsRegularRing R ∧ ringKrullDim R = (n : WithBot ℕ∞) := by
  refine ⟨fun h => ?_, fun ⟨hreg, hdim⟩ =>
    (iSup_projectiveDimension_eq_ringKrullDim R hreg).trans hdim⟩
  have hreg := ((iSup_projectiveDimension_le_natCast_iff_isRegularRing R n).mp h.le).1
  exact ⟨hreg, (iSup_projectiveDimension_eq_ringKrullDim R hreg).symm.trans h⟩

/-- **Item (2) of Lemma 00OE implies items (3) and (4).** A regular ring of Krull dimension `n` has
`R_𝔭` a regular local ring with `dim R_𝔭 ≤ n` at every prime — the `∀` of item (4), hence also that
of item (3) — and the bound is attained at a maximal ideal, which is the `∃` of item (3), hence
also that of item (4). So the two items are the two weakenings of this one statement. -/
private lemma forall_isRegularLocalRing_atPrime_and_exists_isMaximal {R : Type u} [CommRing R]
    {n : ℕ} (hreg : IsRegularRing R) (hdim : ringKrullDim R = (n : WithBot ℕ∞)) :
    (∀ 𝔭 : Ideal R, ∀ _ : 𝔭.IsPrime, IsRegularLocalRing (Localization.AtPrime 𝔭) ∧
        ringKrullDim (Localization.AtPrime 𝔭) ≤ (n : WithBot ℕ∞)) ∧
      ∃ 𝔪 : Ideal R, ∃ _ : 𝔪.IsMaximal,
        ringKrullDim (Localization.AtPrime 𝔪) = (n : WithBot ℕ∞) := by
  have : FiniteRingKrullDim R := finiteRingKrullDim_iff_ne_bot_and_top.mpr
    ⟨by rw [hdim]; simp, by rw [hdim]; exact natCast_ne_top_withBot n⟩
  obtain ⟨𝔪, h𝔪, hh⟩ := exists_isMaximal_ringKrullDim_atPrime_eq R
  exact ⟨fun 𝔭 _ => isRegularLocalRing_atPrime_and_ringKrullDim_le hreg hdim.le 𝔭,
    𝔪, h𝔪, hh.trans hdim⟩

/-- **Items (3) and (4) of Lemma 00OE imply item (2).** The `∀` of item (3) — which is what item
(4) says at the maximal ideals — makes `R` a regular ring with `dim R ≤ n` by
`iSup_projectiveDimension_le_natCast_iff_isRegularRing`, and a prime at which the bound is attained
turns that into `dim R = n`. -/
private lemma isRegularRing_and_ringKrullDim_eq_of_forall_isMaximal {R : Type u} [CommRing R]
    [IsNoetherianRing R] {n : ℕ}
    (hall : ∀ 𝔪 : Ideal R, ∀ _ : 𝔪.IsMaximal, IsRegularLocalRing (Localization.AtPrime 𝔪) ∧
      ringKrullDim (Localization.AtPrime 𝔪) ≤ (n : WithBot ℕ∞))
    (𝔭 : Ideal R) [𝔭.IsPrime]
    (hh : ringKrullDim (Localization.AtPrime 𝔭) = (n : WithBot ℕ∞)) :
    IsRegularRing R ∧ ringKrullDim R = (n : WithBot ℕ∞) :=
  have h := (iSup_projectiveDimension_le_natCast_iff_isRegularRing R n).mp
    ((iSup_projectiveDimension_le_natCast_iff_forall_isMaximal n).mpr hall)
  ⟨h.1, le_antisymm h.2 (hh.symm.trans_le (ringKrullDim_atPrime_le 𝔭))⟩

/-- **Stacks 00OE.** For a Noetherian ring `R` and `n : ℕ` the following are equivalent: `R` has
global dimension `n`; `R` is a regular ring of Krull dimension `n`; every localization at a maximal
ideal is a regular local ring of dimension `≤ n`, with equality at some maximal ideal; every
localization at a prime is a regular local ring of dimension `≤ n`, with equality at some prime. -/
public theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    List.TFAE
      [(⨆ M : ModuleCat.{u} R, projectiveDimension M) = (n : WithBot ℕ∞),
       IsRegularRing R ∧ ringKrullDim R = (n : WithBot ℕ∞),
       (∀ 𝔪 : Ideal R, ∀ _ : 𝔪.IsMaximal, IsRegularLocalRing (Localization.AtPrime 𝔪) ∧
            ringKrullDim (Localization.AtPrime 𝔪) ≤ (n : WithBot ℕ∞)) ∧
         ∃ 𝔪 : Ideal R, ∃ _ : 𝔪.IsMaximal,
           ringKrullDim (Localization.AtPrime 𝔪) = (n : WithBot ℕ∞),
       (∀ 𝔭 : Ideal R, ∀ _ : 𝔭.IsPrime, IsRegularLocalRing (Localization.AtPrime 𝔭) ∧
            ringKrullDim (Localization.AtPrime 𝔭) ≤ (n : WithBot ℕ∞)) ∧
         ∃ 𝔭 : Ideal R, ∃ _ : 𝔭.IsPrime,
           ringKrullDim (Localization.AtPrime 𝔭) = (n : WithBot ℕ∞)] := by
  rcases subsingleton_or_nontrivial R with _ | _
  · -- Over the zero ring all four conditions fail: there are no primes and no dimensions.
    have hprime : ∀ 𝔭 : Ideal R, ¬ 𝔭.IsPrime := fun 𝔭 h𝔭 => h𝔭.ne_top (Subsingleton.elim 𝔭 ⊤)
    refine List.tfae_of_forall (b := False) fun a ha => iff_false_intro ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · rw [(iSup_projectiveDimension_eq_bot_iff_subsingleton R).mpr ‹_›]; simp
    · rw [ringKrullDim_eq_bot_iff_subsingleton.mpr ‹_›]; simp
    · exact fun ⟨_, 𝔪, h𝔪, _⟩ => hprime 𝔪 h𝔪.isPrime
    · exact fun ⟨_, 𝔭, h𝔭, _⟩ => hprime 𝔭 h𝔭
  · tfae_have 1 ↔ 2 := iSup_projectiveDimension_eq_natCast_iff_isRegularRing R n
    tfae_have 2 → 3 := fun ⟨hreg, hdim⟩ =>
      have ⟨hall, hex⟩ := forall_isRegularLocalRing_atPrime_and_exists_isMaximal hreg hdim
      ⟨fun 𝔪 h𝔪 => hall 𝔪 h𝔪.isPrime, hex⟩
    tfae_have 2 → 4 := fun ⟨hreg, hdim⟩ =>
      have ⟨hall, 𝔪, h𝔪, hh⟩ := forall_isRegularLocalRing_atPrime_and_exists_isMaximal hreg hdim
      ⟨hall, 𝔪, h𝔪.isPrime, hh⟩
    tfae_have 3 → 2 := fun ⟨hall, 𝔪, h𝔪, hh⟩ =>
      isRegularRing_and_ringKrullDim_eq_of_forall_isMaximal hall 𝔪 hh
    tfae_have 4 → 2 := fun ⟨hall, 𝔭, h𝔭, hh⟩ =>
      isRegularRing_and_ringKrullDim_eq_of_forall_isMaximal (fun 𝔪 h𝔪 => hall 𝔪 h𝔪.isPrime) 𝔭 hh
    tfae_finish

end Stacks.RegularRing.GlobalDimension

end

/-!
# Regular rings of dimension `n` are the rings of global dimension `n`

Let `R` be a Noetherian ring and let `n` be an integer. Then the following are equivalent:

1. `R` has global dimension `n`;
2. `R` is a regular ring of dimension `n`;
3. every localization `R_𝔪` at a maximal ideal is a regular local ring of dimension `≤ n`, and
   `dim R_𝔪 = n` for at least one `𝔪`;
4. every localization `R_𝔭` at a prime is a regular local ring of dimension `≤ n`, and
   `dim R_𝔭 = n` for at least one `𝔭`.

The source's proof. By Lemma 00O9 the bound `gl dim R ≤ n` holds if and only if
`gl dim R_𝔪 ≤ n` for every maximal ideal `𝔪`, and by Proposition 00OC a Noetherian local ring
has finite global dimension exactly when it is regular, in which case its global dimension is its
dimension. So `gl dim R = n` says precisely that each `R_𝔪` is regular of dimension `≤ n` with
the bound attained, which is (3). Regularity at the maximal ideals propagates to all primes
because `R_𝔭` is a localization of any `R_𝔪` containing it and a localization of a regular local
ring is regular (Lemma 0AFS), giving (4); and `dim R` is the supremum of the `dim R_𝔭 = ht 𝔭`
(`Ideal.sup_isPrime_height_eq_ringKrullDim`), so (4) is (2) read through Definition 00OD.

## Main results

* `isRegularRing_tfae`: the four conditions of the source, for a fixed `n`, as one `List.TFAE`.

## Implementation notes

The source writes the integer `n` into items (1) and (2) and re-quantifies it existentially in
items (3) and (4); since "with equality for at least one `𝔪`" pins `n` uniquely, that existential
is the same `n`, and the statement is given here for a fixed `n : ℕ`, which is sharper. The
source's own reading is recovered by `exists_congr` on `n`: `R` has finite global dimension iff
`R` is regular of finite dimension iff the dimensions of the `R_𝔪` are bounded and the bound is
attained.

Mathlib has no name for the global dimension of a ring, so — following Definition 00O6 and the
neighbouring tags 00O7, 00O9, 00OC and 0AFS — it is the supremum
`⨆ M : ModuleCat.{u} R, projectiveDimension M` of the projective dimensions of all `R`-modules,
taken in `WithBot ℕ∞`. Modules are quantified in the universe of `R`, where the cyclic modules
`R ⧸ I` live; by Lemma 065T a bound over those bounds every module, so the choice of universe is
immaterial. Being `= n` for a natural number `n` is in particular being `≠ ⊤`, the spelling of
"finite global dimension" used by 00OC and 0AFS.

"Regular ring" is Mathlib's `IsRegularRing` (Definition 00OD) and "regular local ring" is
`IsRegularLocalRing` (Definition 00KU); dimensions are `ringKrullDim`, so that a single notion of
dimension, valued in `WithBot ℕ∞`, is used for `R` and for its localizations, and the trivial ring
is excluded from every item automatically (`ringKrullDim` of it is `⊥`, and it has no maximal
ideal). The localizations are the concrete `Localization.AtPrime 𝔭`, matching the spelling of the
Mathlib sibling `isRegularRing_iff` and the defining field of `IsRegularRing`; nothing is lost,
regularity transporting along `IsLocalization.algEquiv` by
`IsRegularRing.isRegularLocalRing_of_isLocalization` (Tag 00OD) and `ringKrullDim` along a ring
equivalence, and `IsLocalization.AtPrime.ringKrullDim_eq_height` rewrites
`ringKrullDim (Localization.AtPrime 𝔭)` as `ht 𝔭` for a reader who prefers heights.

Item (2) is a conjunction rather than a hypothesis of the lemma because the source's items are
statements about `R`, and `IsRegularRing R` alone does not bound `dim R`: the source's own remark
after Definition 00OD points at a regular Noetherian ring of infinite dimension, for which no item
holds for any `n`. That remark — regularity is *not* finite global dimension for a Noetherian ring
— is exactly the failure of items (1) and (2) to be separable from the dimension `n`, and is why
`IsRegularRing R ↔ gl dim R ≠ ⊤` is absent from this list.

Faithfulness. (1) No hypothesis is dead: `IsNoetherianRing R` is used by every implication —
Lemma 00O9 and Proposition 00OC both need it, and without it item (1) does not imply item (2), a
rank-one non-discrete valuation ring having global dimension `2` while not being Noetherian — and
`n` occurs in all four items. (2) The scalars and base are the source's: the projective dimensions
in item (1) are those of `R`-modules over `R` itself, `ringKrullDim R` in item (2) is the dimension
of `R`, and items (3) and (4) are about the `R_𝔪`-modules and the Krull dimensions of the rings
`R_𝔪` and `R_𝔭`, over themselves. (3) The rings the source names are pinned, not merely posited:
`R_𝔭` is `Localization.AtPrime 𝔭`, the localization of `R` at `𝔭` along the canonical algebra map,
and `n` is pinned as the *value* of the global dimension and of the dimension, not as some bound.
(4) The instantiation is not degenerate: `R = ℤ`, `n = 1` satisfies all four — `gl dim ℤ = 1`, `ℤ`
is regular of dimension `1`, every `ℤ_(p)` is a discrete valuation ring and `ℤ_(0) = ℚ` has
dimension `0` — while `R = k[x]/(x²)` satisfies none for any `n`, its residue field having infinite
projective dimension, so no item is vacuous.

## References

* [StacksProject 00OE](https://stacks.math.columbia.edu/tag/00OE)

## Tags

regular ring, regular local ring, global dimension, projective dimension, Krull dimension,
localization, Noetherian ring
-/

@[expose] public section



open CategoryTheory in
/-- **A Noetherian ring has global dimension `n` if and only if it is regular of dimension `n`**
(Stacks 00OE). For a Noetherian ring `R` and `n : ℕ` the following are equivalent: (1) the global
dimension of `R` is `n`; (2) `R` is a regular ring and `dim R = n`; (3) every localization `R_𝔪` at
a maximal ideal is a regular local ring of dimension `≤ n`, with `dim R_𝔪 = n` for at least one
`𝔪`; (4) the same for the localizations at all primes. -/
@[stacks 00OE "Stated for a fixed `n : ℕ`: the source re-quantifies `n` existentially in items (3)
and (4), but \"with equality for at least one `𝔪`\" pins it, and `exists_congr` on `n` recovers the
source's reading. Global dimension is the supremum of the projective dimensions of all `R`-modules,
Mathlib having no name for it; \"regular\" is `IsRegularRing` (Definition 00OD) and dimensions are
`ringKrullDim`. See the module docstring."]
public theorem isRegularRing_tfae {R : Type u} [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    List.TFAE
      [(⨆ M : ModuleCat.{u} R, projectiveDimension M) = (n : WithBot ℕ∞),
       IsRegularRing R ∧ ringKrullDim R = (n : WithBot ℕ∞),
       (∀ 𝔪 : Ideal R, ∀ _ : 𝔪.IsMaximal, IsRegularLocalRing (Localization.AtPrime 𝔪) ∧
            ringKrullDim (Localization.AtPrime 𝔪) ≤ (n : WithBot ℕ∞)) ∧
         ∃ 𝔪 : Ideal R, ∃ _ : 𝔪.IsMaximal,
           ringKrullDim (Localization.AtPrime 𝔪) = (n : WithBot ℕ∞),
       (∀ 𝔭 : Ideal R, ∀ _ : 𝔭.IsPrime, IsRegularLocalRing (Localization.AtPrime 𝔭) ∧
            ringKrullDim (Localization.AtPrime 𝔭) ≤ (n : WithBot ℕ∞)) ∧
         ∃ 𝔭 : Ideal R, ∃ _ : 𝔭.IsPrime,
           ringKrullDim (Localization.AtPrime 𝔭) = (n : WithBot ℕ∞)] :=
    by apply Stacks.RegularRing.GlobalDimension.solution

end

/-!
# A regular local ring is a regular ring

Let `R` be a Noetherian local ring. This file proves Stacks 0AFS: `R` is a regular local ring if
and only if it has finite global dimension, and in that case every localization `R_𝔭` at a prime
`𝔭` is again a regular local ring, that is, `R` is a regular ring.

The equivalence of regularity with finiteness of the global dimension is Proposition 00OC, so the
whole content of the second assertion is that the global dimension does not grow under
localization, `gl dim S⁻¹R ≤ gl dim R` (Lemma 00O8 (2)): the Noetherian local ring `R_𝔭` then
also has finite global dimension, and Proposition 00OC applied to it makes it regular. The
reverse implication, that a regular ring which is local is a regular local ring, is
`IsRegularLocalRing.of_isRegularRing_of_isLocalRing`.

## Main results

* `Stacks.RegularRing.FiniteGlobalDimension.solution`: for a Noetherian local ring, being a regular
  local ring, having finite global dimension, and being a regular ring are equivalent.

## Implementation notes

Lemma 00O8 (2) is proved here as
`Stacks.RegularRing.FiniteGlobalDimension.iSup_projectiveDimension_localization_le`, an inequality
of global dimensions rather than a statement about a bound `n`, which is what makes the deduction
of the tagged statement a single step: `≠ ⊤` is inherited downwards along `≤`. Mathlib's
`ModuleCat.projectiveDimension_le_projectiveDimension_of_isLocalizedModule` localizes the
projective dimension of a single `R`-module, so the content left is that every `S⁻¹R`-module `X` is
such a localization: restricting scalars along `algebraMap R (S⁻¹R)` makes `LinearMap.id` an
`IsLocalizedModule` for `S` (`isLocalizedModule_id`), so `S⁻¹X ≅ X` as `S⁻¹R`-modules and the two
projective dimensions agree by `ModuleCat.projectiveDimension_eq_of_linearEquiv`. The localization
is kept at the concrete model `Localization S`, matching the spelling of the Mathlib lemmas it
rests on and of `isRegularRing_iff`.

Global dimension appears as the supremum `⨆ M : ModuleCat.{u} R, projectiveDimension M` in
`WithBot ℕ∞`, as in Proposition 00OC, and "finite" as `≠ ⊤`.

## References

* [StacksProject 0AFS](https://stacks.math.columbia.edu/tag/0AFS)
* [StacksProject 00OC](https://stacks.math.columbia.edu/tag/00OC)
* [StacksProject 00O8](https://stacks.math.columbia.edu/tag/00O8)
-/

@[expose] public section



open CategoryTheory

namespace Stacks.RegularRing.FiniteGlobalDimension

/-- **Stacks 00O8 (2): the global dimension does not grow under localization.** The supremum of
the projective dimensions of the `S⁻¹R`-modules is at most the supremum over the `R`-modules,
because an `S⁻¹R`-module is the localization of itself viewed as an `R`-module. -/
@[ega "0 17.2.10" "partial"]
private lemma iSup_projectiveDimension_localization_le {R : Type u} [CommRing R] [Small.{v} R]
    (S : Submonoid R) :
    (⨆ X : ModuleCat.{v} (Localization S), projectiveDimension X) ≤
      ⨆ M : ModuleCat.{v} R, projectiveDimension M :=
  Stacks.RegularRing.GlobalDimension.iSup_projectiveDimension_localization_le S

/-- **Stacks 0AFS.** For a Noetherian local ring `R` the following are equivalent: `R` is a regular
local ring; `R` has finite global dimension; `R` is a regular ring, that is, every localization of
`R` at a prime is a regular local ring. -/
public theorem solution {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    List.TFAE
      [IsRegularLocalRing R,
       (⨆ M : ModuleCat.{u} R, projectiveDimension M) ≠ ⊤,
       IsRegularRing R] := by
  tfae_have 1 ↔ 2 := (isRegularLocalRing_tfae (R := R)).out 3 2
  tfae_have 2 → 3 := fun h => isRegularRing_iff.mpr fun p _ => by
    have : IsNoetherianRing (Localization.AtPrime p) :=
      IsLocalization.isNoetherianRing p.primeCompl _ ‹_›
    exact ((isRegularLocalRing_tfae (R := Localization.AtPrime p)).out 2 3).mp
      (ne_top_of_le_ne_top h (iSup_projectiveDimension_localization_le p.primeCompl))
  tfae_have 3 → 1 := fun _ => IsRegularLocalRing.of_isRegularRing_of_isLocalRing R
  tfae_finish

end Stacks.RegularRing.FiniteGlobalDimension

end

/-!
# A regular local ring is a regular ring

Let `R` be a Noetherian local ring. Then `R` is a regular local ring if and only if it has finite
global dimension, and in that case the localization `R_𝔭` is a regular local ring for every prime
`𝔭` of `R`, that is, `R` is a regular ring in the sense of Definition 00OD.

The source's proof. The equivalence of regularity and finiteness of the global dimension is
Proposition 00OC (with the upper bound `dim R` coming from Proposition 00O7). For the second
assertion, a localization `R_𝔭` of a ring of global dimension `≤ n` again has global dimension
`≤ n` (Lemma 00O8), and `R_𝔭` is Noetherian local, so Proposition 00OC applied to `R_𝔭` makes it
a regular local ring. Consequently a regular local ring is regular as a ring, which is what makes
Definition 00OD consistent with the notion of a regular local ring.

## Main results

* `IsLocalRing.isRegularRing_tfae`: for a Noetherian local ring, being a regular local ring,
  having finite global dimension, and being a regular ring are equivalent.

## Implementation notes

Both sentences of the source are carried by one `List.TFAE`. Item (1) `↔` item (2) is the first
sentence, and item (1) `→` item (3) is the second: `IsRegularRing R` unfolds, for a Noetherian
`R`, to `∀ 𝔭 [𝔭.IsPrime], IsRegularLocalRing (Localization.AtPrime 𝔭)` by
`isRegularRing_iff`, so item (3) is literally "`R_𝔭` is a regular local ring for all primes
`𝔭`". Mathlib's class is preferred to that unfolding because it *is* the concept the source names
in Definition 00OD, and because it is what fires downstream as an instance; nothing is lost by its
choice of the model `Localization.AtPrime 𝔭`, regularity being invariant under ring isomorphism
(`IsRegularLocalRing.of_ringEquiv`) and any two localizations at `𝔭` being isomorphic. The reverse
implication (3) `→` (1) is Mathlib's `IsRegularLocalRing.of_isRegularRing_of_isLocalRing`, so
closing the cycle costs nothing and makes the statement an `Iff` in every direction a user may want.

Restating the first sentence rather than only the second is not idle duplication of Proposition
00OC: the source's lemma is the conjunction, its point is that the two characterisations of
regularity localize together, and the strengthening `IsRegularLocalRing R → IsRegularRing R` is
the assertion Mathlib records as an open TODO in `Mathlib/RingTheory/RegularLocalRing/Defs.lean`.

Global dimension has no name in Mathlib, so, exactly as in Proposition 00OC (and following
Definition 00O6 and the tags 00O7, 00O9, 00OQ), the global dimension of `R` is the supremum
`⨆ M : ModuleCat.{u} R, projectiveDimension M` of the projective dimensions of all `R`-modules,
taken in `WithBot ℕ∞`, and "finite" is `≠ ⊤`. That supremum being `≠ ⊤` is equivalent to the
existence of a single `n : ℕ` with `∀ M, HasProjectiveDimensionLE M n`, the form in which 00O7 and
00O9 state a bound, an element of `WithBot ℕ∞` other than `⊤` being `⊥` or a natural number.
Modules are quantified in the universe of `R`, where the residue field and the finite free modules
`Rⁿ` live; by Lemma 065T a bound over the cyclic modules `R ⧸ I` bounds every module, so the
choice of universe is immaterial.

The numerical identities `gl dim R = dim R = dim_κ 𝔪/𝔪²` accompanying the equivalence are items
(4) and (5) of Proposition 00OC and are not repeated here.

Faithfulness. (1) No hypothesis is dead: `IsLocalRing R` is what makes finite global dimension
imply regularity at all, and `IsNoetherianRing R` is used by every implication — it is also the
hypothesis of the source's lemma, and it is not implied by item (2) (a non-discrete rank-one
valuation ring has global dimension `2`), while items (1) and (3) both entail it.
(2) The scalars and the base are the source's: the projective dimensions are those of `R`-modules
in `ModuleCat R`, with no localization or completion substituted, and the primes in item (3) are
the primes of `R` itself. (3) No canonical map is at issue; the localization `R_𝔭` is pinned as
the localization of `R` at `𝔭` along the canonical algebra map, through `IsRegularRing`, rather
than being an unspecified local ring with the same residue field. (4) The instantiation is not
degenerate: for `R = k[x, y]` localized at `(x, y)` all three items hold, the global dimension
being `2` (Koszul resolution of `κ`), and the localization at `(x)` is a discrete valuation ring;
for `R = k[x]/(x²)` all three fail, `κ` having infinite projective dimension.

## References

* [StacksProject 0AFS](https://stacks.math.columbia.edu/tag/0AFS)

## Tags

regular local ring, regular ring, global dimension, projective dimension, localization,
Noetherian local ring
-/

@[expose] public section



open CategoryTheory in
/-- **A regular local ring is a regular ring** (Stacks 0AFS). For a Noetherian local ring `R` the
following are equivalent: (1) `R` is a regular local ring; (2) `R` has finite global dimension;
(3) `R` is a regular ring, that is, `R_𝔭` is a regular local ring for every prime `𝔭` of `R`. -/
@[stacks 0AFS "Both sentences of the source as one `List.TFAE`: (1) ↔ (2) is the equivalence of
regularity with finiteness of the global dimension, and (1) → (3) is \"`R_𝔭` is a regular local
ring for all primes `𝔭`\", spelled with Mathlib's `IsRegularRing` (Definition 00OD). Global
dimension is the supremum of the projective dimensions of all `R`-modules, Mathlib having no name
for it, and \"finite\" is `≠ ⊤`. See the module docstring.", ega "0 17.3.1"
  "fin. coh. dim ⇔ regular", ega "0 17.3.1" "fin. coh. dim ⇔ regular"]
public theorem IsLocalRing.isRegularRing_tfae {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    List.TFAE
      [IsRegularLocalRing R,
       (⨆ M : ModuleCat.{u} R, projectiveDimension M) ≠ ⊤,
       IsRegularRing R] := by apply Stacks.RegularRing.FiniteGlobalDimension.solution

end
