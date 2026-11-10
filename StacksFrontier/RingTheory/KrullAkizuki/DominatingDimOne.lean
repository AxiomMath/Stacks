module

public import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Around Krull–Akizuki

Stacks Project Tag 00P8 (Lemma 10.119.1, "Around Krull–Akizuki").

Let `R` be a local Noetherian domain with fraction field `K`, and assume `R` is
not a field. Then there exists a ring `R'` with `R ⊆ R' ⊆ K` such that:

1. `R'` is local, Noetherian, and of Krull dimension `1`;
2. the inclusion `R → R'` is a local ring map (i.e. `R'` dominates `R`); and
3. the inclusion `R → R'` is essentially of finite type.

## Formalization notes

- An intermediate ring `R ⊆ R' ⊆ K` is modelled as a `Subring K` containing the
  image of `R` (equivalently a `LocalSubring K`). Containment `R' ⊆ K` is then
  automatic.
- Domination of `R` by `R'` (point 2: the inclusion is a local ring map) is
  exactly the order relation `≤` on `LocalSubring K`: `A ≤ B` unfolds to the
  existence of an inclusion of underlying subrings together with the statement
  that this inclusion is a local homomorphism (`IsLocalHom`). See
  `LocalSubring.le_def`. So `LocalSubring.range (algebraMap R K) ≤ R'` simultaneously
  encodes `R ⊆ R'` and the local-ring-map / domination condition.
- "`R` is not a field" is `¬ IsField R`, equivalently `(0 : Ideal R) ≠ maximalIdeal`.
- Krull dimension is `ringKrullDim`, the supremum of lengths of chains of prime
  ideals, valued in `WithBot ℕ∞`. "`dim R' = 1`" is `ringKrullDim R'.toSubring = 1`.
- "Essentially of finite type" is `Algebra.EssFiniteType`, which is precisely:
  `R'` is (isomorphic as an `R`-algebra to) a localization of a finite-type
  `R`-algebra.
-/

@[expose] public section

/-- The `R`-algebra structure on a subring `R'` of `K` that contains the image
of `R`. The structure map sends `r : R` to `algebraMap R K r`, which lies in
`R'` by the containment hypothesis. This realizes the inclusion `R → R'`. -/
@[reducible]
noncomputable def algebraOfRange {R : Type*} [CommRing R] {K : Type*} [CommRing K] [Algebra R K]
    (R' : Subring K) (h : (algebraMap R K).range ≤ R') : Algebra R R' :=
  ((algebraMap R K).codRestrict R' (fun r => h ⟨r, rfl⟩)).toAlgebra

/-! ## Auxiliary lemmas -/

/-- The `algebraOfRange` structure on a subalgebra (as a subring) carries the same
finite-type property as the subalgebra's own `R`-algebra structure. -/
lemma finiteType_algebraOfRange (R : Type*) [CommRing R]
    (K : Type*) [CommRing K] [Algebra R K]
    (S₀ : Subalgebra R K) (hRS : (algebraMap R K).range ≤ S₀.toSubring)
    (hft : Algebra.FiniteType R S₀) :
    @Algebra.FiniteType R S₀.toSubring _ _ (algebraOfRange S₀.toSubring hRS) := by
  have he : algebraOfRange S₀.toSubring hRS = S₀.algebra := by
    apply Algebra.algebra_ext; intro r; apply Subtype.ext; rfl
  rwa [he]

/-- A finite-type subalgebra of `K` over a Noetherian `R` is a Noetherian ring (with the
`algebraOfRange` structure). -/
lemma isNoetherianRing_toSubring_of_finiteType (R : Type*) [CommRing R] [IsNoetherianRing R]
    (K : Type*) [CommRing K] [Algebra R K]
    (S₀ : Subalgebra R K) (hRS : (algebraMap R K).range ≤ S₀.toSubring)
    (hft : Algebra.FiniteType R S₀) :
    IsNoetherianRing S₀.toSubring := by
  let : Algebra R S₀.toSubring := algebraOfRange S₀.toSubring hRS
  have : Algebra.FiniteType R S₀.toSubring := finiteType_algebraOfRange R K S₀ hRS hft
  exact Algebra.FiniteType.isNoetherianRing R S₀.toSubring

/-- The range-restriction `R → (algebraMap R K).range` reflects units (it is an
isomorphism for a fraction field). -/
lemma isUnit_of_isUnit_range (R : Type*) [CommRing R]
    (K : Type*) [CommRing K] [Algebra R K] [IsFractionRing R K]
    (r : R) (huer : IsUnit (⟨algebraMap R K r, ⟨r, rfl⟩⟩ : (algebraMap R K).range)) : IsUnit r := by
  let e := RingEquiv.ofLeftInverse (Function.leftInverse_invFun (IsFractionRing.injective R K))
  have h1 : (⟨algebraMap R K r, ⟨r, rfl⟩⟩ : (algebraMap R K).range) = e r := rfl
  rw [h1] at huer
  simpa using huer.map e.symm

/-- If a valuation subring `V` dominates `R` (via `LocalSubring.range (algebraMap R K) ≤ V`),
then any element of the
maximal ideal of `R` has valuation `< 1` in `V`. -/
lemma valuation_lt_one_of_mem_maximalIdeal
    (R : Type*) [CommRing R] [IsDomain R] [IsLocalRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (V : ValuationSubring K) (hle : LocalSubring.range (algebraMap R K) ≤ V.toLocalSubring) (r : R)
    (hr : r ∈ IsLocalRing.maximalIdeal R) :
    V.valuation (algebraMap R K r) < 1 := by
  rw [LocalSubring.le_def] at hle
  obtain ⟨hsub, hloc⟩ := hle
  have hmemV : algebraMap R K r ∈ V := hsub ⟨r, rfl⟩
  have hnu : ¬ IsUnit (⟨algebraMap R K r, hmemV⟩ : V) := by
    intro hu
    have huer :
        IsUnit (⟨algebraMap R K r, ⟨r, rfl⟩⟩ : (LocalSubring.range (algebraMap R K)).toSubring) :=
      hloc.map_nonunit _ hu
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (Ideal.eq_top_of_isUnit_mem _ hr (isUnit_of_isUnit_range R K r huer))
  exact (ValuationSubring.valuation_lt_one_iff V _).mp hnu

/-- A quotient `a / b` lies in a valuation subring `V` when `v(a) ≤ v(b)`. -/
lemma div_mem_of_valuation_le (K : Type*) [Field K] (V : ValuationSubring K) (a b : K)
    (hb : b ≠ 0)
    (h : V.valuation a ≤ V.valuation b) : a / b ∈ V := by
  apply V.mem_of_valuation_le_one
  rwa [map_div₀, div_le_one₀ (pos_iff_ne_zero.mpr (by simpa using hb))]

/-- If a Noetherian subring `S ⊇ R` of `K` lies in a valuation subring dominating `R`, and
`𝔪 S` is contained in the principal ideal `x S` for some nonzero `x ∈ 𝔪`, then `S` has a
height one prime lying over `𝔪`. -/
lemma exists_height_one_prime_comap_eq_maximalIdeal
    (R : Type*) [CommRing R] [IsDomain R] [IsLocalRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Subring K) (hRS : (algebraMap R K).range ≤ S) [IsNoetherianRing S]
    (V : ValuationSubring K) (hleV : LocalSubring.range (algebraMap R K) ≤ V.toLocalSubring)
    (hSV : ∀ s ∈ S, s ∈ V)
    (x : R) (hxm : x ∈ IsLocalRing.maximalIdeal R) (hx0 : x ≠ 0)
    (hmx : letI : Algebra R S := algebraOfRange S hRS
      (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ Ideal.span {algebraMap R S x}) :
    ∃ q : Ideal S, q.IsPrime ∧ q.height = 1 ∧
      letI : Algebra R S := algebraOfRange S hRS
      q.comap (algebraMap R S) = IsLocalRing.maximalIdeal R := by
  let : Algebra R S := algebraOfRange S hRS
  let fSV : S →+* V :=
    { toFun := fun s => ⟨s.val, hSV s.val s.property⟩
      map_one' := rfl, map_mul' := fun _ _ => rfl
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have : ((IsLocalRing.maximalIdeal V).comap fSV).IsPrime := Ideal.comap_isPrime _ _
  have hxq₀ : algebraMap R S x ∈ (IsLocalRing.maximalIdeal V).comap fSV := by
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
    exact valuation_lt_one_of_mem_maximalIdeal R K V hleV x hxm
  obtain ⟨q, hqmin, -⟩ :=
    Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).mpr hxq₀)
  have := hqmin.isPrime
  refine ⟨q, this, le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hqmin) ?_,
    le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.comap_isPrime _ q).ne_top)
      (Ideal.map_le_iff_le_comap.mp (hmx.trans hqmin.le))⟩
  refine Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr fun h => hx0 ?_)
  have hx := (Submodule.eq_bot_iff q).mp (Ideal.height_eq_zero_iff_eq_bot.mp h) _
    (hqmin.le (Ideal.mem_span_singleton_self _))
  exact IsFractionRing.injective R K ((congrArg Subtype.val hx).trans (map_zero _).symm)

/-- **(KEY existence step.)** The heart of the Stacks 00P8 construction.

Let `R` be a local Noetherian domain with fraction field `K`, not a field. Then
there is a subring `S` of `K` containing (the image of) `R`, together with a prime
ideal `q` of `S`, such that:

* `R ⊆ S` (the image of `R` lies in `S`): `(algebraMap R K).range ≤ S`;
* `S` is essentially of finite type over `R` -- in fact of finite type -- via the
  `R`-algebra structure induced by the inclusion `R ↪ S ⊆ K`;
* the prime `q` has height `1`;
* `q` lies over the maximal ideal of `R`, i.e. the comap of `q` under `R → S` is
  `maximalIdeal R`; this is exactly the domination condition (`q ∩ R = 𝔪`).

**Informal proof.**
`R` is not a field, so `𝔪 := maximalIdeal R ≠ 0`; pick `0 ≠ x ∈ 𝔪`. Since `R` is
Noetherian, `𝔪` is finitely generated, say `𝔪 = (g₁,…,gₙ)`. Inside `K` form the
finite-type `R`-subalgebra
  `S = R[g₁/x, …, gₙ/x] = Algebra.adjoin R {gᵢ/x}`.
Because `gᵢ = x·(gᵢ/x) ∈ x·S` and `x ∈ 𝔪 ⊆ S`, we get `𝔪·S = x·S`, the *principal*
ideal `(x)` of `S`. Here `x` is a nonzero element of the domain `S` (a subring of the
field `K`), so `x` is a nonzerodivisor; and `x` is not a unit in `S` (if it were,
`𝔪·S = S`, but `q ∩ R = 𝔪` below shows `x·S` is proper -- concretely `x·S` lies in
a prime over `𝔪`). By Krull's principal ideal theorem any prime `q` minimal over
`x·S` has height `≤ 1`, and since `0 ≠ x ∈ q` in a domain, height `= 1`. Finally
`q ∩ R ⊇ 𝔪·S ∩ R ⊇ 𝔪`, and as `q ∩ R` is a prime of the local ring `R` containing
`𝔪`, it equals `𝔪`. So `q` lies over `𝔪`. -/
lemma exists_subring_finiteType_height_one_prime
    (R : Type*) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : ¬ IsField R) :
    ∃ (S : Subring K) (hRS : (algebraMap R K).range ≤ S) (q : Ideal S) (_ : q.IsPrime),
      letI : Algebra R S := algebraOfRange S hRS
      Algebra.FiniteType R S ∧
      q.height = 1 ∧
      q.comap (algebraMap R S) = IsLocalRing.maximalIdeal R := by
  -- 𝔪 ≠ ⊥
  have hm : IsLocalRing.maximalIdeal R ≠ ⊥ := by
    rwa [Ne, ← IsLocalRing.isField_iff_maximalIdeal_eq]
  -- valuation ring dominating R
  obtain ⟨V, hleV⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.range (algebraMap R K))
  -- generating finset of 𝔪
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian (IsLocalRing.maximalIdeal R) :
    (IsLocalRing.maximalIdeal R).FG)
  -- G nonempty
  have hGne : G.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr fun hGe => hm (by simp [← hG, hGe])
  -- argmax
  obtain ⟨x, hxG, hxmax⟩ :=
    Finset.exists_max_image G (fun g => V.valuation (algebraMap R K g)) hGne
  -- x ∈ 𝔪
  have hxm : x ∈ IsLocalRing.maximalIdeal R := hG ▸ Ideal.subset_span hxG
  -- x ≠ 0
  have hx0 : x ≠ 0 := fun hx =>
    hm (by rw [← hG, Ideal.span_eq_bot]; exact fun g hg => by simpa [hx] using hxmax g hg)
  -- the set of fractions gᵢ/x
  set xK : K := algebraMap R K x with hxK
  have hxK0 : xK ≠ 0 := by rw [hxK]; simpa using (IsFractionRing.injective R K).ne hx0
  set Gset : Set K := (fun g => algebraMap R K g / xK) '' (G : Set R) with hGset
  set S₀ : Subalgebra R K := Algebra.adjoin R Gset with hS₀
  set S : Subring K := S₀.toSubring
  have hRS : (algebraMap R K).range ≤ S := by
    rintro y ⟨r, rfl⟩; exact S₀.algebraMap_mem r
  -- S ⊆ V
  have hSV : ∀ s ∈ S, s ∈ V := fun s hs => Algebra.adjoin_induction
    (by rintro _ ⟨g, hg, rfl⟩; exact div_mem_of_valuation_le K V _ _ hxK0 (hxmax g hg))
    (fun r => (LocalSubring.le_def.mp hleV).1 ⟨r, rfl⟩) (fun _ _ _ _ => add_mem)
    (fun _ _ _ _ => mul_mem) hs
  -- FiniteType of the subalgebra (before declaring instA)
  have hFT0 : Algebra.FiniteType R S₀ := by
    classical
    rw [← Subalgebra.fg_iff_finiteType, hS₀, hGset, ← Finset.coe_image]
    exact Subalgebra.fg_adjoin_finset _
  let : Algebra R S := algebraOfRange S hRS
  have : IsNoetherianRing S := isNoetherianRing_toSubring_of_finiteType R K S₀ hRS hFT0
  have hmx : (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤
      Ideal.span {algebraMap R S x} := by
    rw [← hG, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_span_singleton']
    refine ⟨⟨algebraMap R K g / xK, Algebra.subset_adjoin ⟨g, hg, rfl⟩⟩, Subtype.ext ?_⟩
    change algebraMap R K g / xK * xK = algebraMap R K g
    field_simp
  obtain ⟨q, hq, hht, hcomap⟩ :=
    exists_height_one_prime_comap_eq_maximalIdeal R K S hRS V hleV hSV x hxm hx0 hmx
  exact ⟨S, hRS, q, hq, finiteType_algebraOfRange R K S₀ hRS hFT0, hht, hcomap⟩

/-- The localization `S_q = LocalSubring.ofPrime S q` dominates the image of `R`,
provided `q` lies over the maximal ideal of `R`.

**Informal proof.** Write `R' = (ofPrime S q).toSubring`. The inclusion
`R ↪ S ↪ R'` is a ring map `R → R'` whose image is `LocalSubring.range (algebraMap R K)`.
We must show `LocalSubring.range (algebraMap R K) ≤ R'` and that the inclusion is a local
homomorphism. The first is the
chain of inclusions `(algebraMap R K).range ≤ S ≤ R'` (`LocalSubring.le_ofPrime`).
For locality: the maximal ideal of `R' = S_q` contracts to `q` in `S`
(`IsLocalization.AtPrime` makes `qR'` maximal with `qR' ∩ S = q`), and by the
hypothesis `q ∩ R = 𝔪`. Hence the inverse image of the maximal ideal of `R'` in `R`
is `𝔪`, i.e. the map `R → R'` is local. -/
lemma range_le_ofPrime_of_comap_eq_maximalIdeal
    (R : Type*) [CommRing R] [IsDomain R] [IsLocalRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Subring K) (hRS : (algebraMap R K).range ≤ S) (q : Ideal S) [q.IsPrime]
    (hq : letI : Algebra R S := algebraOfRange S hRS
          q.comap (algebraMap R S) = IsLocalRing.maximalIdeal R) :
    LocalSubring.range (algebraMap R K) ≤ LocalSubring.ofPrime S q := by
  let instS : Algebra R S := algebraOfRange S hRS
  have hincl : (LocalSubring.range (algebraMap R K)).toSubring ≤
      (LocalSubring.ofPrime S q).toSubring := le_trans hRS (LocalSubring.le_ofPrime S q)
  set Sq := (LocalSubring.ofPrime S q).toSubring
  let instSq : Algebra R Sq := algebraOfRange Sq hincl
  have : IsScalarTower R S Sq := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsLocalization.AtPrime Sq q := inferInstance
  -- The contraction of the maximal ideal of `S_q` to `R` is `𝔪`:
  -- it contracts to `q` in `S` (localization at a prime), and `q ∩ R = 𝔪` (hq).
  have hcomapSq : Ideal.comap (algebraMap R Sq) (IsLocalRing.maximalIdeal Sq)
      = IsLocalRing.maximalIdeal R := by
    have h := Ideal.under_under (A := R) (B := S) (C := Sq) (IsLocalRing.maximalIdeal Sq)
    rw [IsLocalization.AtPrime.under_maximalIdeal Sq q] at h
    change Ideal.under R (IsLocalRing.maximalIdeal Sq) = _
    rwa [← h]
  -- Hence `R → S_q` is a local ring homomorphism.
  have hlocalg : IsLocalHom (algebraMap R Sq) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap R Sq)).out 4 1).mp hcomapSq.ge
  -- Unfold the domination relation: an inclusion of subrings plus locality.
  rw [LocalSubring.le_def]
  refine ⟨hincl, ⟨fun x hx => ?_⟩⟩
  obtain ⟨_, r, rfl⟩ := x
  exact (hlocalg.map_nonunit r hx).map (algebraMap R K).rangeRestrict

/-! ## Main statement -/

/-- **Stacks Tag 00P8 (Lemma 10.119.1).**
Let `R` be a local Noetherian domain with fraction field `K` that is not a field.
Then there exists a local subring `R'` of `K` (so `R' ⊆ K`) such that:

1. `R'` dominates `R` (`LocalSubring.range (algebraMap R K) ≤ R'`); this encodes both
   `R ⊆ R'` and the fact
   that the inclusion `R → R'` is a local ring map;
2. `R'` is Noetherian;
3. `R'` has Krull dimension `1`;
4. the inclusion `R → R'` is essentially of finite type. -/
@[stacks 00P8]
theorem exists_localSubring_isNoetherian_ringKrullDim_eq_one
    (R : Type*) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : ¬ IsField R) :
    ∃ (R' : LocalSubring K) (hle : LocalSubring.range (algebraMap R K) ≤ R'),
      IsNoetherianRing R'.toSubring ∧
      ringKrullDim R'.toSubring = 1 ∧
      letI : Algebra R R'.toSubring :=
        algebraOfRange R'.toSubring (LocalSubring.le_def.mp hle).choose
      Algebra.EssFiniteType R R'.toSubring := by
  -- Get the blow-up subring `S` and the height-1 prime `q` lying over `𝔪`.
  obtain ⟨S, hRS, q, hqp, hFT, hht, hcomap⟩ := exists_subring_finiteType_height_one_prime R K hR
  let : Algebra R S := algebraOfRange S hRS
  let : Algebra R (LocalSubring.ofPrime S q).toSubring :=
    algebraOfRange (LocalSubring.ofPrime S q).toSubring
      (le_trans hRS (LocalSubring.le_ofPrime S q))
  have : Algebra.EssFiniteType R S := Algebra.EssFiniteType.of_finiteType R S
  have : Algebra.EssFiniteType S (LocalSubring.ofPrime S q).toSubring :=
    Algebra.EssFiniteType.of_isLocalization (LocalSubring.ofPrime S q).toSubring q.primeCompl
  have : IsScalarTower R S (LocalSubring.ofPrime S q).toSubring :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hEFT : Algebra.EssFiniteType R (LocalSubring.ofPrime S q).toSubring :=
    Algebra.EssFiniteType.comp R S (LocalSubring.ofPrime S q).toSubring
  refine ⟨LocalSubring.ofPrime S q, range_le_ofPrime_of_comap_eq_maximalIdeal R K S hRS q hcomap,
    Algebra.EssFiniteType.isNoetherianRing R _, ?_, hEFT⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (LocalSubring.ofPrime S q).toSubring, hht]
  rfl

end
