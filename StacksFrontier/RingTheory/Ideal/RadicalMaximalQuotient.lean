module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.KrullDimension.Zero
import StacksCore.Tactic.StacksAttribute

/-!
# The quotient by an ideal whose radical is maximal

Let `I` be an ideal of a commutative ring `R` whose radical is a maximal ideal. The ring
`R ⧸ I` is then local, and Artinian as soon as `R` is Noetherian. Neither statement asks `R`
itself to be local: the maximal ideals of `R ⧸ I` are the maximal ideals of `R` containing
`I`, every one of those contains `I.radical`, and `I.radical` is already maximal, so there is
exactly one.

Formally, the nilradical of `R ⧸ I` is the image of `I.radical`
(`Ideal.isMaximal_nilradical_quotient`), and a ring whose nilradical is maximal is local with
Krull dimension zero; both halves of that are in Mathlib, as
`IsLocalRing.of_isMaximal_nilradical` and `Ring.KrullDimLE.of_isMaximal_nilradical`.

The case of interest is `I = 𝔭 ^ n` for a maximal ideal `𝔭` and `n ≠ 0`: the radical of
`𝔭 ^ n` is `𝔭`. This is the ring that [Stacks, Tag 07YM] forms at a closed point in order to
compare a versal object with a lift along a square-zero extension.

## Main results

* `Ideal.isMaximal_nilradical_quotient` — the nilradical of `R ⧸ I` is maximal.
* `isLocalRing_quotient_of_radical_isMaximal` and
  `isArtinianRing_quotient_of_radical_isMaximal` — the quotient is local, and Artinian over a
  Noetherian ring.
* `isLocalRing_quotient_pow_of_isMaximal` and `isArtinianRing_quotient_pow_of_isMaximal` —
  the same for `R ⧸ 𝔭 ^ n` with `𝔭` maximal and `n ≠ 0`, also registered as instances under
  `NeZero n`.
* `Ideal.map_radical_quotient_eq_nilradical` — the image of `I.radical` in `R ⧸ I` is the
  nilradical, for any ideal `I` whatsoever.
* `IsLocalRing.maximalIdeal_quotient_eq_map_radical` and
  `IsLocalRing.maximalIdeal_quotient_pow` — the maximal ideal of `R ⧸ I` is the image of
  `I.radical`, and that of `R ⧸ 𝔭 ^ n` is the image of `𝔭`.
* `Ideal.pow_le_comap_pow_of_map_le` and `Ideal.pow_le_ker_of_map_le` — a ring map carrying
  `𝔭` into `𝔮` carries `𝔭 ^ n` into `𝔮 ^ n`, and kills `𝔭 ^ n` outright when `𝔮 ^ n = 0`.
  Neither ring is asked to be local, Noetherian or Artinian here.
* `IsLocalRing.exists_isLocalHom_comp_mk_pow` — a map `σ : R → S` into a local ring with
  `𝔪_S ^ n = 0` factors through `R ⧸ 𝔭 ^ n` by a local homomorphism, as soon as `σ` carries
  `𝔭` into `𝔪_S`. This is the factorization [Stacks, Tag 07YM] performs at the closed point.
* `IsLocalRing.isLocalHom_of_comp_augmentation` — a map of local rings compatible with
  surjective augmentations onto one field is local. It is collected here rather than with the
  general theory of local homomorphisms because its only consumers are the quotients
  `R ⧸ 𝔭 ^ n` of this file, whose residue fields come from such augmentations.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public section

variable {R : Type*} [CommRing R]

/-- The image of `I.radical` in `R ⧸ I` is the nilradical of `R ⧸ I`: the quotient map is
surjective with kernel `I`, so it carries the radical of `I` to the radical of the zero ideal.
No hypothesis on `I` is needed. -/
public theorem Ideal.map_radical_quotient_eq_nilradical (I : Ideal R) :
    I.radical.map (Ideal.Quotient.mk I) = nilradical (R ⧸ I) := by
  rw [Ideal.map_radical_of_surjective Ideal.Quotient.mk_surjective Ideal.mk_ker.le,
    Ideal.map_quotient_self]
  rfl

/-- If the radical of `I` is maximal, then the nilradical of `R ⧸ I` is maximal: it is the
image of `I.radical` under the quotient map, and that map is surjective with kernel `I`,
which is contained in `I.radical`. -/
public theorem Ideal.isMaximal_nilradical_quotient {I : Ideal R} (hI : I.radical.IsMaximal) :
    (nilradical (R ⧸ I)).IsMaximal := by
  have := hI
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ I.radical := by
    rw [Ideal.mk_ker]
    exact Ideal.le_radical
  exact Ideal.map_radical_quotient_eq_nilradical I ▸
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hker

/-- The quotient of a ring by an ideal whose radical is maximal is a local ring. The ring
itself need not be local. -/
public theorem isLocalRing_quotient_of_radical_isMaximal {I : Ideal R}
    (hI : I.radical.IsMaximal) : IsLocalRing (R ⧸ I) :=
  have := Ideal.isMaximal_nilradical_quotient hI
  IsLocalRing.of_isMaximal_nilradical _

/-- The quotient of a Noetherian ring by an ideal whose radical is maximal is Artinian. The
ring itself need not be local. -/
public theorem isArtinianRing_quotient_of_radical_isMaximal [IsNoetherianRing R] (I : Ideal R)
    (hI : I.radical.IsMaximal) : IsArtinianRing (R ⧸ I) :=
  have := Ideal.isMaximal_nilradical_quotient hI
  isArtinianRing_iff_krullDimLE_zero.mpr (Ring.KrullDimLE.of_isMaximal_nilradical _)

/-- The radical of a nonzero power of a maximal ideal is that ideal again. -/
public theorem Ideal.radical_pow_of_isMaximal (p : Ideal R) [p.IsMaximal] {n : ℕ}
    (hn : n ≠ 0) : (p ^ n).radical = p := by
  rw [Ideal.radical_pow p hn, Ideal.IsPrime.radical ‹p.IsMaximal›.isPrime]

/-- The radical of a nonzero power of a maximal ideal is maximal. -/
public theorem Ideal.radical_pow_isMaximal (p : Ideal R) [p.IsMaximal] {n : ℕ}
    (hn : n ≠ 0) : (p ^ n).radical.IsMaximal := by
  rw [Ideal.radical_pow_of_isMaximal p hn]
  exact ‹p.IsMaximal›

/-- For a maximal ideal `p` of a ring that need not be local and `n ≠ 0`, the ring `R ⧸ p ^ n`
is local. -/
@[stacks 07YM "the local half of `A/𝔭 ^ n`, for `𝔭` the prime of a closed point"]
public theorem isLocalRing_quotient_pow_of_isMaximal (p : Ideal R) [p.IsMaximal] {n : ℕ}
    (hn : n ≠ 0) : IsLocalRing (R ⧸ p ^ n) :=
  isLocalRing_quotient_of_radical_isMaximal (Ideal.radical_pow_isMaximal p hn)

/-- For a maximal ideal `p` of a Noetherian ring that need not be local and `n ≠ 0`, the ring
`R ⧸ p ^ n` is Artinian. -/
@[stacks 07YM "the Artinian half of `A/𝔭 ^ n`, for `𝔭` the prime of a closed point"]
public theorem isArtinianRing_quotient_pow_of_isMaximal [IsNoetherianRing R] (p : Ideal R)
    [p.IsMaximal] {n : ℕ} (hn : n ≠ 0) : IsArtinianRing (R ⧸ p ^ n) :=
  isArtinianRing_quotient_of_radical_isMaximal _ (Ideal.radical_pow_isMaximal p hn)

public instance isLocalRing_quotient_pow_neZero (p : Ideal R) [p.IsMaximal] (n : ℕ)
    [NeZero n] : IsLocalRing (R ⧸ p ^ n) :=
  isLocalRing_quotient_pow_of_isMaximal p (NeZero.ne n)

public instance isArtinianRing_quotient_pow_neZero [IsNoetherianRing R] (p : Ideal R)
    [p.IsMaximal] (n : ℕ) [NeZero n] : IsArtinianRing (R ⧸ p ^ n) :=
  isArtinianRing_quotient_pow_of_isMaximal p (NeZero.ne n)

/-! ### The maximal ideal of the quotient -/

/-- For an ideal whose radical is maximal, the maximal ideal of the local ring `R ⧸ I` is the
image of `I.radical`: that image is the nilradical, which is maximal, and a maximal ideal of a
local ring is its maximal ideal. -/
public theorem IsLocalRing.maximalIdeal_quotient_eq_map_radical {I : Ideal R}
    (hI : I.radical.IsMaximal) [IsLocalRing (R ⧸ I)] :
    IsLocalRing.maximalIdeal (R ⧸ I) = I.radical.map (Ideal.Quotient.mk I) := by
  refine (IsLocalRing.eq_maximalIdeal ?_).symm
  rw [Ideal.map_radical_quotient_eq_nilradical]
  exact Ideal.isMaximal_nilradical_quotient hI

/-- For a maximal ideal `p` and `n ≠ 0`, the maximal ideal of `R ⧸ p ^ n` is the image of
`p`. -/
@[stacks 07YM "the maximal ideal of `A/𝔭 ^ n`, for `𝔭` the prime of a closed point"]
public theorem IsLocalRing.maximalIdeal_quotient_pow (p : Ideal R) [p.IsMaximal] (n : ℕ)
    [NeZero n] :
    IsLocalRing.maximalIdeal (R ⧸ p ^ n) = p.map (Ideal.Quotient.mk (p ^ n)) := by
  rw [IsLocalRing.maximalIdeal_quotient_eq_map_radical
      (Ideal.radical_pow_isMaximal p (NeZero.ne n)),
    Ideal.radical_pow_of_isMaximal p (NeZero.ne n)]

/-- For a maximal ideal `p` and `n ≠ 0`, the `n`-th power of the maximal ideal of `R ⧸ p ^ n`
vanishes: that maximal ideal is the image of `p`, so its `n`-th power is the image of `p ^ n`,
which is the ideal being quotiented out.

This is the hypothesis `𝔪_{B'} ^ n = 0` under which a lift of `R` through a morphism onto
`R ⧸ p ^ n` factors (`IsLocalRing.exists_isLocalHom_comp_mk_pow`), and in [Stacks, Tag 07YM]
it is the sentence "since the maximal ideal of `B'` has `n`th power equal to zero". The ring
`R` is not asked to be local. -/
@[stacks 07YM "the maximal ideal of `A'/(𝔭') ^ n` has vanishing `n`-th power"]
public theorem IsLocalRing.maximalIdeal_quotient_pow_pow_eq_bot (p : Ideal R) [p.IsMaximal]
    (n : ℕ) [NeZero n] : IsLocalRing.maximalIdeal (R ⧸ p ^ n) ^ n = ⊥ := by
  rw [IsLocalRing.maximalIdeal_quotient_pow p n, ← Ideal.map_pow, Ideal.map_quotient_self]

/-! ### Local homomorphisms and `R ⧸ p ^ n` -/

section Factor

variable {S : Type*} [CommRing S]

/-- A ring map between local rings compatible with surjective augmentations onto one field is
a local homomorphism: the maximal ideal of each side is the kernel of its augmentation, and
compatibility carries one kernel into the other. -/
public theorem IsLocalRing.isLocalHom_of_comp_augmentation [IsLocalRing R] [IsLocalRing S]
    {K : Type*} [Field K] (εR : R →+* K) (hεR : Function.Surjective εR) (εS : S →+* K)
    (hεS : Function.Surjective εS) (F : R →+* S) (hF : εS.comp F = εR) : IsLocalHom F := by
  apply ((IsLocalRing.local_hom_TFAE F).out 1 4).mpr
  rw [← IsLocalRing.ker_eq_maximalIdeal εR hεR, ← IsLocalRing.ker_eq_maximalIdeal εS hεS,
    RingHom.comap_ker, hF]

/-- A ring map carrying an ideal `p` into an ideal `q` carries `p ^ n` into `q ^ n`. -/
public theorem Ideal.pow_le_comap_pow_of_map_le (f : R →+* S) {p : Ideal R} {q : Ideal S}
    (hpq : p.map f ≤ q) (n : ℕ) : p ^ n ≤ (q ^ n).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono hpq n

/-- A ring map carrying an ideal `p` into an ideal `q` with `q ^ n = 0` kills `p ^ n`. Nothing
is asked of `f` beyond that: neither ring need be local, Noetherian or Artinian, and `p` and
`q` are arbitrary ideals. -/
public theorem Ideal.pow_le_ker_of_map_le (f : R →+* S) {p : Ideal R} {q : Ideal S}
    (hpq : p.map f ≤ q) {n : ℕ} (hq : q ^ n = ⊥) : p ^ n ≤ RingHom.ker f := by
  have h := Ideal.pow_le_comap_pow_of_map_le f hpq n
  rwa [hq, ← RingHom.ker_eq_comap_bot] at h

/-- **The local factorization of [Stacks, Tag 07YM].** A ring map `σ : R → S` into a local
ring whose maximal ideal satisfies `𝔪_S ^ n = 0` factors through `R ⧸ p ^ n` for every ideal
`p` whose image under `σ` lies in `𝔪_S`, and the factorization is a local homomorphism as soon
as `p` is maximal and `n ≠ 0`.

The ring `R` is not asked to be local: in the source `σ` goes from the finite-type algebra `A`
to an Artinian local ring `B'` and `p` is the prime of the closed point, so the hypothesis
`p.map σ ≤ 𝔪_S` — rather than `IsLocalHom σ` — is what is available. Maximality of `p` and
`n ≠ 0` are used only to make `R ⧸ p ^ n` a local ring, hence only for the `IsLocalHom`
half; the factorization itself is `Ideal.Quotient.lift` applied to
`Ideal.pow_le_ker_of_map_le` and holds for an arbitrary ideal `p` and arbitrary `n`. -/
@[stacks 07YM "σ : A → B' with 𝔪_{B'} ^ n = 0 factors through A/𝔭 ^ n"]
public theorem IsLocalRing.exists_isLocalHom_comp_mk_pow [IsLocalRing S] (f : R →+* S)
    (p : Ideal R) [p.IsMaximal] {n : ℕ} [NeZero n]
    (hp : p.map f ≤ IsLocalRing.maximalIdeal S)
    (hn : IsLocalRing.maximalIdeal S ^ n = ⊥) :
    ∃ F : R ⧸ p ^ n →+* S, IsLocalHom F ∧ F.comp (Ideal.Quotient.mk (p ^ n)) = f := by
  set F := Ideal.Quotient.lift (p ^ n) f (Ideal.pow_le_ker_of_map_le f hp hn) with hFdef
  have hF : F.comp (Ideal.Quotient.mk (p ^ n)) = f := RingHom.ext fun _ ↦ rfl
  refine ⟨F, ?_, hF⟩
  apply ((IsLocalRing.local_hom_TFAE F).out 1 3).mpr
  rwa [IsLocalRing.maximalIdeal_quotient_pow p n, Ideal.map_map, hF]

end Factor
