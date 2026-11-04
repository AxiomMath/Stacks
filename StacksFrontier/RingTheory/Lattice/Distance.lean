module

public import Mathlib.Algebra.Module.Lattice
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Length
import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.QuotSMulTop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lattices in a vector space over a fraction field, and the distance between them

Let `R` be a Noetherian domain with fraction field `K` and let `V` be a `K`-vector space. A
*lattice* in `V` is an `R`-submodule of `V` that is finitely generated over `R` and spans `V` over
`K`; this is Mathlib's `Submodule.IsLattice K M`. When `R` has Krull dimension one, the quotient
of one lattice by a smaller one has finite length, and length measures how far apart two lattices
lie.

Length is additive along a factorisation `ab` of a scalar with `b` acting injectively: writing
`M ⧸ xM` for `QuotSMulTop x M`, `length_R(M ⧸ abM) = length_R(M ⧸ aM) + length_R(M ⧸ bM)`.

Above a lattice `M`, a submodule `M' ⊇ M` is a lattice exactly when `length_R(M'/M) < ∞`, and
exactly when it is finitely generated; below `M`, a submodule `M' ⊆ M` is a lattice exactly when
`length_R(M/M') < ∞`. The lattices are closed under `⊓` and `⊔`.

The signed distance between two submodules is
`d(M, M') = length_R(M/(M ∩ M')) - length_R(M'/(M ∩ M')) ∈ ℤ`.
When `R` has Krull dimension one it is additive on lattices, `d(M, M'') = d(M, M') + d(M', M'')`,
and can be computed through any common sublattice `N` as `length_R(M/N) - length_R(M'/N)`. It is
antisymmetric, and `d(M, M') = length_R(M/M')` when `M' ⊆ M`.

## Main definitions

* `Submodule.lengthDist`: the distance `d(M, M') : ℤ` between two submodules of a module, measured
  by the lengths of `M/(M ∩ M')` and `M'/(M ∩ M')`.

## Main results

* `span_eq_top_of_isBaseChange`: if `K ⊗_R M → V` is an isomorphism then `M` spans `V` over `K`.
* `Module.length_quotient_map_of_injective`: length is additive along an injective linear map.
* `Module.length_quotSMulTop_mul`: `length_R(M ⧸ abM) = length_R(M ⧸ aM) + length_R(M ⧸ bM)` for
  `b` acting injectively on `M`.
* `Module.length_quotient_submoduleOf_eq_add`: additivity of length along a chain of submodules.
* `Submodule.isLattice_tfae_of_le_and_iff_of_ge_and_inf_sup`: the two recognition criteria and
  closure of the lattices under `⊓` and `⊔`.
* `Submodule.lengthDist_of_le`: `d(M, M') = length_R(M/M')` for `M' ≤ M`.
* `Submodule.lengthDist_eq_sub`: the distance measured through a common sublattice.
* `Submodule.lengthDist_additive` and `Submodule.lengthDist_antisymm`: the distance is additive
  and antisymmetric.

## References

* [StacksProject 02MC](https://stacks.math.columbia.edu/tag/02MC)
* [StacksProject 02ME](https://stacks.math.columbia.edu/tag/02ME)
* [StacksProject 02MF](https://stacks.math.columbia.edu/tag/02MF)
* [StacksProject 02MG](https://stacks.math.columbia.edu/tag/02MG)
* [StacksProject 02MH](https://stacks.math.columbia.edu/tag/02MH)
-/

@[expose] public section

/-! ### Lattices -/

/-- If the canonical base-change map `K ⊗[R] M → V` induced by the inclusion `M ↪ V` is an
isomorphism, then the `K`-span of `M` inside `V` is all of `V`. -/
@[stacks 02ME "The definition itself is Mathlib's `Submodule.IsLattice K M`, finite generation
over `R` together with `span_K M = ⊤`; this is the implication from the source's phrasing
`V = K ⊗_R M`, the remark following the definition. Locality of `R`, dimension one and finite
dimensionality of `V` are used by neither."]
lemma span_eq_top_of_isBaseChange (R : Type*) [CommRing R] (K : Type*) [CommRing K] [Algebra R K]
    (V : Type*) [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (M : Submodule R V) (h : IsBaseChange K M.subtype) :
    Submodule.span K (M : Set V) = ⊤ := by
  have hr : LinearMap.range (M.subtype.liftBaseChange K) = ⊤ :=
    LinearMap.range_eq_top.mpr h.equiv.surjective
  rwa [LinearMap.range_liftBaseChange, Submodule.range_subtype] at hr

/-! ### Additivity of length -/

section Length

variable {R M M' : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

/-- For `f : M →ₗ[R] M'` injective and `N ⊆ M` a submodule,
`length(M' ⧸ f(N)) = length(M ⧸ N) + length(M' ⧸ f(M))`. -/
theorem Module.length_quotient_map_of_injective {f : M →ₗ[R] M'}
    (hf : Function.Injective f) (N : Submodule R M) :
    Module.length R (M' ⧸ N.map f) =
      Module.length R (M ⧸ N) + Module.length R (M' ⧸ LinearMap.range f) := by
  refine Module.length_eq_add_of_exact (N.mapQ (N.map f) f (Submodule.le_comap_map f N))
      (Submodule.factor LinearMap.map_le_range) ?_ (Submodule.factor_surjective _) ?_
  · rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ,
      Submodule.comap_map_eq_self ((LinearMap.ker_eq_bot.mpr hf).trans_le bot_le),
      Submodule.mkQ_map_self]
  · rw [LinearMap.exact_iff, Submodule.range_mapQ, Submodule.factor, Submodule.ker_mapQ,
      Submodule.comap_id]

variable {V : Type*} [AddCommGroup V] [Module R V]

/-- For `N ≤ S ≤ A`, the copy of `N` inside `S` is carried onto the copy of `N` inside `A` by the
inclusion `S ↪ A`. -/
private lemma Submodule.map_submoduleOf_inclusion {N S A : Submodule R V} (hNS : N ≤ S)
    (hSA : S ≤ A) : (N.submoduleOf S).map (Submodule.inclusion hSA) = N.submoduleOf A :=
  Submodule.map_comap_eq_self (q := N.submoduleOf A)
    (by rw [Submodule.range_inclusion]; exact Submodule.comap_mono hNS)

/-- For `N ≤ S ≤ A` submodules of `V`, `length_R(A/N) = length_R(S/N) + length_R(A/S)`, an
identity in `ℕ∞`. -/
@[stacks 02MF "(4). Stated for arbitrary submodules `N ≤ S ≤ A` of a module over a ring, and as an
identity in `ℕ∞`, so that no finiteness and none of the source's hypotheses — locality, dimension
one, lattices, finite dimensionality of `V` — are needed. Parts (1)-(3) are
`Submodule.isLattice_tfae_of_le_and_iff_of_ge_and_inf_sup` and part (5) is
`Submodule.lengthDist_eq_sub`."]
theorem Module.length_quotient_submoduleOf_eq_add {N S A : Submodule R V} (hNS : N ≤ S)
    (hSA : S ≤ A) :
    Module.length R (↥A ⧸ N.submoduleOf A) =
      Module.length R (↥S ⧸ N.submoduleOf S) + Module.length R (↥A ⧸ S.submoduleOf A) := by
  rw [← Submodule.map_submoduleOf_inclusion hNS hSA,
    Module.length_quotient_map_of_injective (Submodule.inclusion_injective hSA),
    Submodule.range_inclusion]
  rfl

end Length

/-! ### Additivity of length along a factorisation into a regular element -/

section Factorisation

open Pointwise

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The range of multiplication by `r` on `M` is `rM`. -/
lemma LinearMap.range_lsmul (r : R) :
    LinearMap.range (LinearMap.lsmul R M r) = r • (⊤ : Submodule R M) := by
  rw [LinearMap.range_eq_map]; exact Submodule.pointwise_smul_def

/-- Let `R` be a commutative ring, `M` an `R`-module and `a`, `b ∈ R` with `b` acting injectively
on `M`. Then `length_R(M ⧸ abM) = length_R(M ⧸ aM) + length_R(M ⧸ bM)`, an identity in `ℕ∞`. -/
@[stacks 02MC "Stated for an arbitrary module `M` in place of `R`, of which the source's identity
`length_R(R ⧸ (ab)) = length_R(R ⧸ (a)) + length_R(R ⧸ (b))` is the case `M = R`, and with `b` a
nonzerodivisor weakened to `b` acting injectively on `M`. The equation uses no hypothesis on `R`;
the source's finiteness assertion is `isFiniteLength_quotient_span_singleton`. See the module
docstring."]
theorem Module.length_quotSMulTop_mul {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {a b : R} (hb : IsSMulRegular M b) :
    Module.length R (QuotSMulTop (a * b) M) =
      Module.length R (QuotSMulTop a M) + Module.length R (QuotSMulTop b M) := by
  have h : (a * b) • (⊤ : Submodule R M)
      = (a • (⊤ : Submodule R M)).map (LinearMap.lsmul R M b) := by
    rw [mul_comm, mul_smul]; exact Submodule.pointwise_smul_def
  rw [(Submodule.quotEquivOfEq _ _ h).length_eq,
    Module.length_quotient_map_of_injective (f := LinearMap.lsmul R M b) hb (a • ⊤),
    LinearMap.range_lsmul]

end Factorisation

/-! ### Recognising lattices -/

section Recognition

open scoped nonZeroDivisors

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A finite module over a Noetherian ring of Krull dimension at most one, annihilated by a
non-zerodivisor `f`, has finite length. -/
@[ega "IV 21.10.13" "more general"]
private theorem isFiniteLength_of_isTorsionBy [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [Module.Finite R M] {f : R} (hf : f ∈ R⁰) (h : Module.IsTorsionBy R M f) :
    IsFiniteLength R M := by
  have hset : Module.IsTorsionBySet R M (Ideal.span {f}) := by
    rwa [← Module.isTorsionBySet_iff_is_torsion_by_span, Module.isTorsionBySet_singleton_iff]
  let _ : Module (R ⧸ Ideal.span {f}) M := hset.module
  have : IsScalarTower R (R ⧸ Ideal.span {f}) M := hset.isScalarTower
  have : IsArtinianRing (R ⧸ Ideal.span {f}) :=
    isArtinian_of_tower R (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (isFiniteLength_quotient_span_singleton R hf)).2
  have : Module.Finite (R ⧸ Ideal.span {f}) M := Module.Finite.of_restrictScalars_finite R _ M
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_of_isNoetherianRing_of_finite R M,
      isArtinian_of_surjective_algebraMap (R := R ⧸ Ideal.span {f}) Ideal.Quotient.mk_surjective⟩

/-- A module of finite length over a domain that is not a field is annihilated by a nonzero
element of the ring. -/
private theorem exists_ne_zero_isTorsionBy_of_isFiniteLength [IsDomain R] (hR : ¬ IsField R)
    (h : IsFiniteLength R M) : ∃ f : R, f ≠ 0 ∧ Module.IsTorsionBy R M f := by
  induction h with
  | of_subsingleton => exact ⟨1, one_ne_zero, fun {x} => by rw [Subsingleton.elim x 0, smul_zero]⟩
  | @of_simple_quotient M _ _ N _ _ ih =>
      obtain ⟨f, hf₀, hf⟩ := ih
      have hann : Module.annihilator R (M ⧸ N) ≠ ⊥ := fun h₀ =>
        hR (Ring.isField_iff_maximal_bot.mpr
          (h₀ ▸ IsSimpleModule.annihilator_isMaximal (R := R) (M := M ⧸ N)))
      obtain ⟨g, hg, hg₀⟩ := (Submodule.ne_bot_iff _).mp hann
      refine ⟨f * g, mul_ne_zero hf₀ hg₀, fun {x} => ?_⟩
      have hgx : g • x ∈ N := (Submodule.Quotient.mk_eq_zero N).mp <| by
        rw [← Submodule.mkQ_apply, map_smul]; exact Module.mem_annihilator.mp hg _
      rw [mul_smul]
      simpa using congrArg Subtype.val (hf (x := ⟨g • x, hgx⟩))

section Denominators

variable {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] {V : Type*} [AddCommGroup V] [Module K V] [Module R V]
  [IsScalarTower R K V]

/-- An `R`-submodule of `V` spans `V` over the fraction field `K` exactly when every vector of `V`
has a nonzero `R`-multiple in it. -/
private theorem span_eq_top_iff_forall_exists_ne_zero_smul_mem (M : Submodule R V) :
    Submodule.span K (M : Set V) = ⊤ ↔ ∀ x : V, ∃ r : R, r ≠ 0 ∧ r • x ∈ M := by
  refine ⟨fun hM x => ?_, fun h => eq_top_iff.mpr fun x _ => ?_⟩
  · obtain ⟨n, c, y, hcy⟩ := Submodule.mem_span_set'.mp (hM ▸ Submodule.mem_top (x := x))
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R)
      (Finset.univ : Finset (Fin n)) c
    refine ⟨(b : R), nonZeroDivisors.coe_ne_zero b, ?_⟩
    rw [← hcy, Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨a, ha⟩ := hb i (Finset.mem_univ i)
    have hsmul : (b : R) • (c i • (y i : V)) = a • (y i : V) := by
      rw [← algebraMap_smul (A := K) (b : R) (c i • (y i : V)), smul_smul, ← Algebra.smul_def, ← ha,
        algebraMap_smul]
    exact hsmul ▸ M.smul_mem a (y i).property
  · obtain ⟨r, hr, hrx⟩ := h x
    have hc : algebraMap R K r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr
    have hx : x = (algebraMap R K r)⁻¹ • (r • x) := by
      rw [← algebraMap_smul (A := K) r x, smul_smul, inv_mul_cancel₀ hc, one_smul]
    exact hx ▸ Submodule.smul_mem _ _ (Submodule.subset_span hrx)

/-- A finitely generated submodule is carried into a spanning submodule by a nonzero element of
`R`. -/
private theorem exists_ne_zero_smul_le {M N : Submodule R V}
    (hM : Submodule.span K (M : Set V) = ⊤) (hN : N.FG) :
    ∃ r : R, r ≠ 0 ∧ ∀ x ∈ N, r • x ∈ M := by
  classical
  obtain ⟨s, hs⟩ := hN
  choose c hc₀ hcm using (span_eq_top_iff_forall_exists_ne_zero_smul_mem M).mp hM
  refine ⟨∏ x ∈ s, c x, Finset.prod_ne_zero_iff.mpr fun x _ => hc₀ x,
    show N ≤ Submodule.comap (LinearMap.lsmul R V (∏ x ∈ s, c x)) M from ?_⟩
  rw [← hs, Submodule.span_le]
  intro x hx
  simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.lsmul_apply]
  rw [← Finset.prod_erase_mul s c hx, mul_smul]
  exact M.smul_mem _ (hcm x)

/-- A submodule receiving a nonzero multiple of a spanning submodule spans. -/
private theorem span_eq_top_of_forall_smul_mem {M M' : Submodule R V} {f : R} (hf : f ≠ 0)
    (hfM : ∀ x ∈ M, f • x ∈ M') (hM : Submodule.span K (M : Set V) = ⊤) :
    Submodule.span K (M' : Set V) = ⊤ := by
  rw [span_eq_top_iff_forall_exists_ne_zero_smul_mem] at hM ⊢
  intro x
  obtain ⟨r, hr₀, hrx⟩ := hM x
  exact ⟨f * r, mul_ne_zero hf hr₀, by rw [mul_smul]; exact hfM _ hrx⟩

/-- The intersection of two spanning submodules spans. -/
private theorem span_inf_eq_top {M M' : Submodule R V}
    (hM : Submodule.span K (M : Set V) = ⊤) (hM' : Submodule.span K (M' : Set V) = ⊤) :
    Submodule.span K ((M ⊓ M' : Submodule R V) : Set V) = ⊤ := by
  rw [span_eq_top_iff_forall_exists_ne_zero_smul_mem] at hM hM' ⊢
  intro x
  obtain ⟨r, hr₀, hrx⟩ := hM x
  obtain ⟨r', hr'₀, hr'x⟩ := hM' x
  refine ⟨r * r', mul_ne_zero hr₀ hr'₀, Submodule.mem_inf.mpr ⟨?_, ?_⟩⟩
  · rw [mul_comm, mul_smul]; exact M.smul_mem _ hrx
  · rw [mul_smul]; exact M'.smul_mem _ hr'x

end Denominators

section Quotient

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Being annihilated by `f` on `↥M ⧸ M'.submoduleOf M` is `f M ⊆ M'`. -/
private theorem isTorsionBy_quotient_submoduleOf_iff (M M' : Submodule R V) (f : R) :
    Module.IsTorsionBy R (↥M ⧸ M'.submoduleOf M) f ↔ ∀ x ∈ M, f • x ∈ M' := by
  rw [Module.isTorsionBy_quotient_iff]
  refine ⟨fun h x hx => ?_, fun h x => ?_⟩
  · simpa [Submodule.submoduleOf] using h ⟨x, hx⟩
  · simpa [Submodule.submoduleOf] using h (x : V) x.2

/-- For `M` a finitely generated submodule over a Noetherian domain of Krull dimension one, the
relative quotient `M/(M ∩ M')` has finite length exactly when a single nonzero element of `R`
carries `M` into `M'`. -/
private theorem length_quotient_submoduleOf_ne_top_iff [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] (hR : ¬ IsField R) {M M' : Submodule R V} (hM : M.FG) :
    Module.length R (↥M ⧸ M'.submoduleOf M) ≠ ⊤ ↔ ∃ f : R, f ≠ 0 ∧ ∀ x ∈ M, f • x ∈ M' := by
  have : Module.Finite R ↥M := Module.Finite.iff_fg.mpr hM
  have : Module.Finite R (↥M ⧸ M'.submoduleOf M) := Module.Finite.quotient R _
  simp only [← isTorsionBy_quotient_submoduleOf_iff, Module.length_ne_top_iff]
  exact ⟨exists_ne_zero_isTorsionBy_of_isFiniteLength hR, fun ⟨f, hf₀, hf⟩ =>
    isFiniteLength_of_isTorsionBy (mem_nonZeroDivisors_of_ne_zero hf₀) hf⟩

/-- Over a Noetherian ring, if `M ≤ M'` with `M` finitely generated and `M'/M` of finite length,
then `M'` is finitely generated. -/
private theorem fg_of_le_of_length_quotient_ne_top [IsNoetherianRing R] {M M' : Submodule R V}
    (hM : M.FG) (hle : M ≤ M') (hlen : Module.length R (↥M' ⧸ M.submoduleOf M') ≠ ⊤) : M'.FG := by
  have : Module.Finite R ↥M := Module.Finite.iff_fg.mpr hM
  have : IsNoetherian R ↥M := isNoetherian_of_isNoetherianRing_of_finite R ↥M
  have : IsNoetherian R ↥(M.submoduleOf M') :=
    isNoetherian_of_linearEquiv (Submodule.comapSubtypeEquivOfLe hle).symm
  have : IsNoetherian R (↥M' ⧸ M.submoduleOf M') :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hlen)).1
  have : IsNoetherian R ↥M' :=
    isNoetherian_of_range_eq_ker (M.submoduleOf M').subtype (M.submoduleOf M').mkQ
      (by rw [Submodule.range_subtype, Submodule.ker_mkQ])
  exact (Submodule.fg_top M').mp (IsNoetherian.noetherian ⊤)

end Quotient

section Lattice

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K] {V : Type*} [AddCommGroup V] [Module K V] [Module R V]
  [IsScalarTower R K V]

/-- For lattices `M`, `M'` over a Noetherian domain of Krull dimension one which is not a field,
`length_R(M/(M ∩ M')) < ∞`. -/
theorem Module.length_quotient_submoduleOf_ne_top_of_isLattice [Ring.KrullDimLE 1 R]
    (hR : ¬ IsField R) {M M' : Submodule R V} [Submodule.IsLattice K M]
    [Submodule.IsLattice K M'] : Module.length R (↥M ⧸ M'.submoduleOf M) ≠ ⊤ :=
  (length_quotient_submoduleOf_ne_top_iff hR ‹Submodule.IsLattice K M›.fg).mpr
    (exists_ne_zero_smul_le ‹Submodule.IsLattice K M'›.span_eq_top ‹Submodule.IsLattice K M›.fg)

/-- Let `R` be a Noetherian domain with fraction field `K` and let `V` be a `K`-vector space. If
`R` has Krull dimension `1` then: (1) for `M` a lattice and `M ≤ M'`, the conditions "`M'` is a
lattice", "`length_R(M'/M) < ∞`" and "`M'` is finitely generated" are equivalent; (2) for `M` a
lattice and `M' ≤ M`, `M'` is a lattice if and only if `length_R(M/M') < ∞`. Without any
hypothesis on the dimension: (3) if `M` and `M'` are lattices then so are `M ⊓ M'` and `M ⊔ M'`. -/
@[stacks 02MF "Parts (1)-(3). Locality is dropped, being used by no part, and finite
dimensionality of `V` follows from the existence of a lattice. Dimension one is an antecedent of
parts (1) and (2), over which it is sharp — it is not weakened to `Ring.KrullDimLE 1 R`, which
breaks (2) — and part (3) holds over any Noetherian domain, strengthening Mathlib's
`Submodule.IsLattice.inf`. Parts (4) and (5) hold for arbitrary submodules of a module over a
ring, with none of these hypotheses; they are `Module.length_quotient_submoduleOf_eq_add` and
`Submodule.lengthDist_eq_sub`."]
theorem Submodule.isLattice_tfae_of_le_and_iff_of_ge_and_inf_sup {R : Type*} [CommRing R]
    [IsDomain R] [IsNoetherianRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] :
    (ringKrullDim R = 1 →
      (∀ M M' : Submodule R V, Submodule.IsLattice K M → M ≤ M' →
          [Submodule.IsLattice K M', Module.length R (↥M' ⧸ M.submoduleOf M') ≠ ⊤,
            M'.FG].TFAE) ∧
      (∀ M M' : Submodule R V, Submodule.IsLattice K M → M' ≤ M →
          (Submodule.IsLattice K M' ↔ Module.length R (↥M ⧸ M'.submoduleOf M) ≠ ⊤))) ∧
    (∀ M M' : Submodule R V, Submodule.IsLattice K M → Submodule.IsLattice K M' →
        Submodule.IsLattice K (M ⊓ M') ∧ Submodule.IsLattice K (M ⊔ M')) := by
  refine ⟨fun hdim => ?_, fun M M' hM hM' => ?_⟩
  · have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by simp [hdim])
    have hR : ¬ IsField R := fun hR => by
      rw [ringKrullDim_eq_zero_of_isField hR] at hdim; exact zero_ne_one hdim
    refine ⟨fun M M' hM hle => ?_, fun M M' hM hle => ?_⟩
    · have : Submodule.IsLattice K M := hM
      tfae_have 1 → 2 := fun h => by
        have : Submodule.IsLattice K M' := h
        exact Module.length_quotient_submoduleOf_ne_top_of_isLattice hR
      tfae_have 2 → 3 := fg_of_le_of_length_quotient_ne_top hM.fg hle
      tfae_have 3 → 1 := fun h => Submodule.IsLattice.of_le_of_isLattice_of_fg K hle h
      tfae_finish
    · have : Submodule.IsLattice K M := hM
      refine ⟨fun h => ?_, fun hlen => ?_⟩
      · have : Submodule.IsLattice K M' := h
        exact Module.length_quotient_submoduleOf_ne_top_of_isLattice hR
      · obtain ⟨f, hf₀, hf⟩ := (length_quotient_submoduleOf_ne_top_iff hR hM.fg).mp hlen
        exact ⟨hM.fg.of_le hle, span_eq_top_of_forall_smul_mem hf₀ hf hM.span_eq_top⟩
  · have : Submodule.IsLattice K M := hM
    have : Submodule.IsLattice K M' := hM'
    exact ⟨⟨hM.fg.of_le inf_le_left, span_inf_eq_top hM.span_eq_top hM'.span_eq_top⟩,
      Submodule.IsLattice.sup K M M'⟩

/-- Over a Noetherian domain, the intersection of two lattices is a lattice. -/
instance Submodule.IsLattice.inf_of_isNoetherianRing (M M' : Submodule R V)
    [Submodule.IsLattice K M] [Submodule.IsLattice K M'] : Submodule.IsLattice K (M ⊓ M') :=
  ((Submodule.isLattice_tfae_of_le_and_iff_of_ge_and_inf_sup (K := K)).2 M M' inferInstance
    inferInstance).1

end Lattice

end Recognition

/-! ### The distance between two lattices -/

section Distance

variable {R : Type*} [Ring R] {V : Type*} [AddCommGroup V] [Module R V]

/-- The distance between two submodules `M`, `M'` of a module `V` over a ring `R`: the integer
`d(M, M') = length_R(M/(M ∩ M')) - length_R(M'/(M ∩ M'))`, with both lengths truncated from `ℕ∞`
by `ENat.toNat`. -/
@[stacks 02MG "Stated for arbitrary submodules of a module over a ring, since the formula uses
none of the source's standing hypotheses: those make the two lengths finite, and are carried by
02MF and 02MH rather than left inert here. The difference is taken after `ENat.toNat`, which is
faithful on pairs of lattices by 02MF (1)-(3). See the module docstring."]
noncomputable def Submodule.lengthDist {R : Type*} [Ring R] {V : Type*} [AddCommGroup V]
    [Module R V] (M M' : Submodule R V) : ℤ :=
  ((Module.length R (↥M ⧸ (M ⊓ M').submoduleOf M)).toNat : ℤ) -
    ((Module.length R (↥M' ⧸ (M ⊓ M').submoduleOf M')).toNat : ℤ)

/-- For `M' ≤ M`, `d(M, M') = length_R(M/M')`. -/
@[stacks 02MG "The remark following the definition. Stated for arbitrary submodules of a module
over a ring; on a pair of lattices the length is finite by 02MF (2)."]
theorem Submodule.lengthDist_of_le {M M' : Submodule R V} (h : M' ≤ M) :
    M.lengthDist M' = (Module.length R (↥M ⧸ M'.submoduleOf M)).toNat := by
  rw [Submodule.lengthDist, inf_of_le_right h, Submodule.submoduleOf_self]
  simp

/-- The distance between two submodules is antisymmetric: `d(M, M') = -d(M', M)`. -/
@[stacks 02MH "(2). Stated for arbitrary submodules of a module over a ring: with both quotients
normalised by `M ⊓ M'` the identity is the antisymmetry of a difference."]
theorem Submodule.lengthDist_antisymm (M M' : Submodule R V) :
    M.lengthDist M' = - M'.lengthDist M := by
  rw [Submodule.lengthDist, Submodule.lengthDist, inf_comm]
  ring

end Distance

section LatticeDistance

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {V : Type*} [AddCommGroup V]
  [Module K V] [Module R V] [IsScalarTower R K V]

/-- For a chain of lattices `N ≤ S ≤ A`, `length_R(A/N) = length_R(S/N) + length_R(A/S)` as an
identity of natural numbers. -/
private theorem toNat_length_quotient_submoduleOf_eq_add (hR : ¬ IsField R) {N S A : Submodule R V}
    [Submodule.IsLattice K N] [Submodule.IsLattice K S] [Submodule.IsLattice K A] (hNS : N ≤ S)
    (hSA : S ≤ A) :
    (Module.length R (↥A ⧸ N.submoduleOf A)).toNat
      = (Module.length R (↥S ⧸ N.submoduleOf S)).toNat
        + (Module.length R (↥A ⧸ S.submoduleOf A)).toNat := by
  rw [Module.length_quotient_submoduleOf_eq_add hNS hSA,
    ENat.toNat_add (Module.length_quotient_submoduleOf_ne_top_of_isLattice (K := K) hR)
      (Module.length_quotient_submoduleOf_ne_top_of_isLattice (K := K) hR)]

/-- For lattices `M`, `M'` and a lattice `N` below both,
`d(M, M') = length_R(M/N) - length_R(M'/N)`. -/
@[stacks 02MF "(5), in the form `length_R(M/M ∩ M') - length_R(M'/M ∩ M') =
length_R(M/N) - length_R(M'/N)`; of the source's three expressions for `d(M, M')` this is the one
formalised, the two through `M + M'` and through a lattice `N' ⊇ M + M'` being open. Locality is
dropped and dimension one is spelled as the pair `Ring.KrullDimLE 1 R` and `¬ IsField R`, which
over a Noetherian domain is `ringKrullDim R = 1`."]
theorem Submodule.lengthDist_eq_sub (hR : ¬ IsField R) {M M' N : Submodule R V}
    [Submodule.IsLattice K M] [Submodule.IsLattice K M'] [Submodule.IsLattice K N] (hNM : N ≤ M)
    (hNM' : N ≤ M') :
    M.lengthDist M' = ((Module.length R (↥M ⧸ N.submoduleOf M)).toNat : ℤ)
      - ((Module.length R (↥M' ⧸ N.submoduleOf M')).toNat : ℤ) := by
  rw [Submodule.lengthDist,
    toNat_length_quotient_submoduleOf_eq_add (K := K) hR (le_inf hNM hNM') inf_le_left,
    toNat_length_quotient_submoduleOf_eq_add (K := K) hR (le_inf hNM hNM') inf_le_right]
  push_cast
  ring

/-- For lattices `M`, `M'`, `M''` in `V`, `d(M, M'') = d(M, M') + d(M', M'')`. -/
@[stacks 02MH "(1). Locality is dropped and dimension one is spelled as the pair
`Ring.KrullDimLE 1 R` and `¬ IsField R`, which over a Noetherian domain is `ringKrullDim R = 1`;
finite dimensionality of `V` follows from the existence of a lattice."]
theorem Submodule.lengthDist_additive (hR : ¬ IsField R) (M M' M'' : Submodule R V)
    [Submodule.IsLattice K M] [Submodule.IsLattice K M'] [Submodule.IsLattice K M''] :
    M.lengthDist M'' = M.lengthDist M' + M'.lengthDist M'' := by
  have h₁ : M ⊓ M' ⊓ M'' ≤ M := inf_le_left.trans inf_le_left
  have h₂ : M ⊓ M' ⊓ M'' ≤ M' := inf_le_left.trans inf_le_right
  rw [Submodule.lengthDist_eq_sub (K := K) hR h₁ inf_le_right,
    Submodule.lengthDist_eq_sub (K := K) hR h₁ h₂,
    Submodule.lengthDist_eq_sub (K := K) hR h₂ inf_le_right]
  ring

end LatticeDistance

end
