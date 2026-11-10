module

import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop

public import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence
public import StacksFrontier.RingTheory.CompleteIntersection.Basic
public import StacksFrontier.RingTheory.NaiveCotangent.Localization
public import StacksFrontier.RingTheory.RegularRing.Defs
public import StacksFrontier.RingTheory.Spectrum.Prime.Codimension
import StacksFrontier.RingTheory.KrullDimension.BaseChange
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.CompleteIntersection.AtPrime.LocalCriterion

/-!
# The complete intersection criterion at a prime: from item (2) to item (1)

The local dimension of a spectrum at a point and a standard open attaining it
(`PrimeSpectrum.exists_notMem_topologicalKrullDim_basicOpen_le_localKrullDim`), the codimension
formula for a presented algebra over a field
(`PrimeSpectrum.localKrullDim_add_height_comap_eq_natCard_add_height`), clearing denominators, and
the implications (2) ⇒ (1)
(`Algebra.Generators.exists_isGlobalCompleteIntersection_away_of_spanFinrank_ker_map_le`) and
(5) ⇒ (1) (`Algebra.Generators.exists_isGlobalCompleteIntersection_away_of_exists_isRegular`).

See `StacksFrontier.RingTheory.CompleteIntersection.AtPrime` for the overview and references.
-/

@[expose] public section

universe u v w

open IsLocalRing RingTheory.Sequence

variable {A : Type*} [CommRing A]

/-! ### The local dimension of a spectrum at a point, and where it is attained -/

/-- **A standard open of a spectrum has dimension at least that of the localization it carries.**
`Spec R[g⁻¹] → Spec R` is an embedding with image `D(g)`, so it corestricts to an inducing map
`Spec R[g⁻¹] → D(g)`. -/
@[ega "IV 5.1.1" "partial"]
theorem PrimeSpectrum.ringKrullDim_le_topologicalKrullDim_basicOpen
    {R : Type*} [CommRing R] (g : R) (T : Type*) [CommRing T] [Algebra R T]
    [IsLocalization.Away g T] :
    ringKrullDim T ≤
      topologicalKrullDim (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) := by
  have hrange : Set.range (PrimeSpectrum.comap (algebraMap R T))
      = (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range T g
  set f : PrimeSpectrum T → (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) :=
    fun p => ⟨PrimeSpectrum.comap (algebraMap R T) p, hrange ▸ Set.mem_range_self p⟩
  have hind : Topology.IsInducing f := by
    refine Topology.IsInducing.of_comp ?_ continuous_subtype_val ?_
    · exact Continuous.subtype_mk (PrimeSpectrum.continuous_comap _) _
    · exact (PrimeSpectrum.localization_comap_isEmbedding T (Submonoid.powers g)).isInducing
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact hind.topologicalKrullDim_le

/-- **The infimum defining the dimension of a spectrum at a point is attained on a standard open.**
For a point `x = 𝔮` of `Spec R` there is a `g ∉ 𝔮` with `dim D(g) ≤ dim_x Spec R`; since `D(g)` is
itself an open neighbourhood of `x` this is in fact an equality.

`WithBot ℕ∞` is well ordered, so among the values `dim D(g)` for `g ∉ 𝔮` there is a least one; and
it is below `dim U` for every open `U ∋ x`, because the standard opens are a basis and
`topologicalKrullDim` is monotone. -/
theorem PrimeSpectrum.exists_notMem_topologicalKrullDim_basicOpen_le_localKrullDim
    {R : Type*} [CommRing R] (x : PrimeSpectrum R) :
    ∃ g ∉ x.asIdeal, topologicalKrullDim (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) ≤
      TopologicalSpace.localKrullDim (PrimeSpectrum R) x := by
  classical
  set s : Set (WithBot ℕ∞) :=
    {d | ∃ g : R, g ∉ x.asIdeal ∧
      topologicalKrullDim (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) = d}
  have hne : s.Nonempty :=
    ⟨_, ⟨1, fun h => x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h isUnit_one), rfl⟩⟩
  obtain ⟨d₀, hd₀s, hmin⟩ :=
    (wellFounded_lt (α := WithBot ℕ∞)).has_min s hne
  obtain ⟨g₀, hg₀, hdg₀⟩ := hd₀s
  refine ⟨g₀, hg₀, ?_⟩
  rw [hdg₀, TopologicalSpace.localKrullDim]
  refine le_iInf fun U => le_iInf fun hU => le_iInf fun hxU => ?_
  obtain ⟨_, hvb, hxv, hvU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxU hU
  obtain ⟨g, rfl⟩ := hvb
  calc d₀ ≤ topologicalKrullDim (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) := by
        by_contra hcon
        exact hmin _ ⟨g, hxv, rfl⟩ (lt_of_not_ge hcon)
    _ ≤ topologicalKrullDim U := topologicalKrullDim_le_of_subset hvU

/-- **For a domain of finite type over a field the dimension at a point is the Krull dimension.**
`Spec A` is irreducible and all its maximal chains of primes have the same length, so the infimum
of the heights of the maximal ideals containing a given prime is `dim A`. -/
theorem PrimeSpectrum.localKrullDim_eq_ringKrullDim_of_isDomain
    (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (x : PrimeSpectrum A) :
    TopologicalSpace.localKrullDim (PrimeSpectrum A) x = ringKrullDim A := by
  have key : ∀ m : Ideal A, m.IsMaximal → (m.height : WithBot ℕ∞) = ringKrullDim A := by
    intro m hm
    have := hm
    exact ((Algebra.FiniteType.ringKrullDim_eq_height_of_isMaximal_and_length_eq_ringKrullDim
      k A).1 m).symm
  rw [(PrimeSpectrum.localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height k x).2]
  obtain ⟨m, hm, hle⟩ := x.asIdeal.exists_le_maximal x.isPrime.ne_top
  exact le_antisymm ((iInf₂_le m ⟨hm, hle⟩).trans (key m hm).le)
    (le_iInf₂ fun n hn => (key n hn.1).ge)

/-- **The codimension formula for a presented finite type algebra over a field.** If
`S = k[x_i]/I` with finitely many variables and `x ∈ Spec S` corresponds to `x' ∈ Spec k[x_i]`,
then `dim_x Spec S + height x' = n + height x`, where `n` is the number of variables. -/
theorem PrimeSpectrum.localKrullDim_add_height_comap_eq_natCard_add_height
    (k : Type*) [Field k] {ι : Type*} [Finite ι]
    {S : Type*} [CommRing S] [Algebra k S] (f : MvPolynomial ι k →ₐ[k] S)
    (hf : Function.Surjective f) (x : PrimeSpectrum S) :
    TopologicalSpace.localKrullDim (PrimeSpectrum S) x
        + ((PrimeSpectrum.comap f.toRingHom x).asIdeal.height : WithBot ℕ∞)
      = (Nat.card ι : WithBot ℕ∞) + (x.asIdeal.height : WithBot ℕ∞) := by
  have h := (PrimeSpectrum.localKrullDim_comap_add_height_eq_localKrullDim_add_height_comap
    k f hf x).symm
  rw [PrimeSpectrum.localKrullDim_eq_ringKrullDim_of_isDomain k (MvPolynomial ι k)] at h
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field] at h
  rw [h]
  norm_num

/-- **Cutting `k[x_1, …, x_N]` by `C` elements drops the dimension by at most `C`.** If the
quotient is nonzero it has dimension at least `N - C`: a maximal ideal containing the `C` elements
has height `N` (`mvpoly_maximal_height`), so its image in the quotient has height at least
`N - C` by Krull's height theorem. -/
theorem mvpoly_quotient_span_range_ringKrullDim_ge (k : Type*) [Field k] (N C : ℕ)
    (f : Fin C → MvPolynomial (Fin N) k)
    (hne : Nontrivial (MvPolynomial (Fin N) k ⧸ Ideal.span (Set.range f))) :
    ((N - C : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin N) k ⧸ Ideal.span (Set.range f)) := by
  classical
  set mk := Ideal.Quotient.mk (Ideal.span (Set.range f))
  have hnetop : Ideal.span (Set.range f) ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp hne
  obtain ⟨M, hMmax, hMsub⟩ := Ideal.exists_le_maximal _ hnetop
  have hsub : Set.range f ⊆ (M : Set (MvPolynomial (Fin N) k)) :=
    fun x hx => hMsub (Ideal.subset_span hx)
  have hMh : M.height = (N : ℕ∞) := mvpoly_maximal_height k N M hMmax
  have hkerle : RingHom.ker mk ≤ M := by
    rw [show RingHom.ker mk = Ideal.span (Set.range f) from Ideal.mk_ker]; exact hMsub
  set MT : Ideal (MvPolynomial (Fin N) k ⧸ Ideal.span (Set.range f)) := M.map mk with hMT
  have hcut : ((N - C : ℕ) : ℕ∞) ≤ MT.height := by
    have hk := Ideal.height_le_height_add_encard_of_subset (Set.range f) hsub
    have henc : (Set.range f).encard ≤ (C : ℕ∞) := by
      calc (Set.range f).encard ≤ (Set.univ : Set (Fin C)).encard := by
              rw [← Set.image_univ]; exact Set.encard_image_le f Set.univ
          _ = (C : ℕ∞) := by rw [Set.encard_univ]; simp
    rw [hMh] at hk
    have hnc : (N : ℕ∞) ≤ MT.height + (C : ℕ∞) := le_trans hk (add_le_add_right henc _)
    cases hh : MT.height with
    | top => exact le_top
    | coe m => rw [hh] at hnc; norm_cast at hnc ⊢; omega
  have hMTmax : MT.IsMaximal := by
    rw [hMT]
    exact Ideal.IsMaximal.map_of_surjective_of_ker_le (f := mk) Ideal.Quotient.mk_surjective hkerle
  calc ((N - C : ℕ) : WithBot ℕ∞) = ((((N - C : ℕ) : ℕ∞)) : WithBot ℕ∞) := by norm_cast
    _ ≤ ((MT.height : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hcut
    _ ≤ _ := Ideal.height_le_ringKrullDim_of_ne_top hMTmax.ne_top

/-! ### Clearing denominators -/

/-- Two families of elements differing by units span the same ideal. -/
private theorem span_range_eq_of_unit_mul {A : Type*} [CommRing A] {ν : Type*} {F G : ν → A}
    (h : ∀ i, ∃ w : Aˣ, G i = F i * w) :
    Ideal.span (Set.range G) = Ideal.span (Set.range F) := by
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    obtain ⟨w, hw⟩ := h i
    rw [hw]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    obtain ⟨w, hw⟩ := h i
    have hFi : F i = G i * ((w⁻¹ : Aˣ) : A) := by
      rw [hw, mul_assoc]; simp
    rw [hFi]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- **One denominator clears a finitely generated ideal.** If `I` and `J` become equal in a
localization `A` of a Noetherian ring `R` at `M`, then a single `u ∈ M` satisfies `u·I ⊆ J`: each
generator of `I` is killed into `J` by some element of `M`, and their product works for all of
them at once. -/
private theorem exists_mem_mul_mem_of_map_le {R : Type*} [CommRing R] [IsNoetherianRing R]
    (M : Submonoid R) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization M A]
    {I J : Ideal R} (h : I.map (algebraMap R A) ≤ J.map (algebraMap R A)) :
    ∃ u ∈ M, ∀ y ∈ I, u * y ∈ J := by
  classical
  obtain ⟨t, ht⟩ := IsNoetherian.noetherian I
  have key : ∀ x : R, ∃ mm : R, mm ∈ M ∧ (x ∈ I → mm * x ∈ J) := by
    intro x
    by_cases hx : x ∈ I
    · obtain ⟨mm, hmM, hmJ⟩ :=
        (IsLocalization.algebraMap_mem_map_algebraMap_iff (S := A) M J x).1
          (h (Ideal.mem_map_of_mem _ hx))
      exact ⟨mm, hmM, fun _ => hmJ⟩
    · exact ⟨1, one_mem _, fun hx' => absurd hx' hx⟩
  choose m hmM hmJ using key
  refine ⟨∏ x ∈ t, m x, Submonoid.prod_mem _ fun x _ => hmM x, ?_⟩
  rw [← ht]
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
      have hxI : x ∈ I := ht ▸ Ideal.subset_span hx
      rw [← Finset.mul_prod_erase t m hx, mul_comm (m x), mul_assoc]
      exact Ideal.mul_mem_left _ _ (hmJ x hxI)
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact J.add_mem ha hb
  | smul r a _ ha =>
      have hre : (∏ x ∈ t, m x) * (r • a) = r * ((∏ x ∈ t, m x) * a) := by
        rw [smul_eq_mul]; ring
      rw [hre]
      exact Ideal.mul_mem_left _ _ ha

/-- **Inverting an element commutes with taking a quotient.** For `u : R` and `I : Ideal R`, the
localization of `R/I` away from the class of `u` is the quotient of `R[u⁻¹]` by `I·R[u⁻¹]`. This is
Mathlib's instance `IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) M) (S ⧸ I.map …)` read at
`M = ⟨u⟩`, transported to the canonical model by the uniqueness of localizations. -/
private theorem nonempty_localizationAway_quotient_algEquiv (k : Type*) [Field k]
    (R : Type*) [CommRing R] [Algebra k R] (u : R) (I : Ideal R) :
    Nonempty (Localization.Away (Ideal.Quotient.mk I u) ≃ₐ[k]
      ((Localization.Away u) ⧸ I.map (algebraMap R (Localization.Away u)))) := by
  have hsub : Algebra.algebraMapSubmonoid (R ⧸ I) (Submonoid.powers u)
      = Submonoid.powers (Ideal.Quotient.mk I u) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]; rfl
  have : IsLocalization (Submonoid.powers (Ideal.Quotient.mk I u))
      ((Localization.Away u) ⧸ I.map (algebraMap R (Localization.Away u))) := by
    rw [← hsub]; infer_instance
  have : IsScalarTower k (R ⧸ I)
      ((Localization.Away u) ⧸ I.map (algebraMap R (Localization.Away u))) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨(IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk I u))
    (Localization.Away (Ideal.Quotient.mk I u))
    ((Localization.Away u) ⧸ I.map (algebraMap R (Localization.Away u)))).restrictScalars k⟩

/-- If `J ≤ I` and `u·I ⊆ J`, then `J` and `I` have the same extension to `R[u⁻¹]`. -/
private theorem map_eq_map_of_mul_mem {R : Type*} [CommRing R] {u : R} {I J : Ideal R}
    (hJI : J ≤ I) (hu : ∀ y ∈ I, u * y ∈ J) (Bu : Type*) [CommRing Bu] [Algebra R Bu]
    [IsLocalization.Away u Bu] :
    J.map (algebraMap R Bu) = I.map (algebraMap R Bu) := by
  refine le_antisymm (Ideal.map_mono hJI) ?_
  rw [Ideal.map_le_iff_le_comap]
  intro y hy
  rw [Ideal.mem_comap]
  exact (IsLocalization.algebraMap_mem_map_algebraMap_iff (S := Bu) (Submonoid.powers u) J y).2
    ⟨u, Submonoid.mem_powers u, hu y hy⟩

/-- An algebra isomorphism carrying `r` to `t` induces one of the localizations away from them. -/
private theorem nonempty_localizationAway_algEquiv (k : Type*) [Field k] {R T : Type*}
    [CommRing R] [CommRing T] [Algebra k R] [Algebra k T] (e : R ≃ₐ[k] T) (r : R) (t : T)
    (h : e r = t) : Nonempty (Localization.Away r ≃ₐ[k] Localization.Away t) :=
  ⟨IsLocalization.algEquivOfAlgEquiv (A := k) (R := R) (P := T)
    (S := Localization.Away r) (Q := Localization.Away t)
    (M := Submonoid.powers r) (T := Submonoid.powers t) e
    (by rw [Submonoid.map_powers e r, h])⟩

/-- An ideal needing at most `c` generators is spanned by a family indexed by `Fin c`, padding a
minimal generating set with zeros. -/
private theorem exists_fin_span_eq {A : Type*} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {c : ℕ} (hsp : I.spanFinrank ≤ c) :
    ∃ F : Fin c → A, Ideal.span (Set.range F) = I := by
  classical
  obtain ⟨t, hcard, hspan⟩ :=
    (IsNoetherian.noetherian I).exists_span_finset_card_eq_spanFinrank
  refine ⟨fun i => t.toList.getD (i : ℕ) 0, ?_⟩
  have hlen : t.toList.length ≤ c := by rw [Finset.length_toList]; exact hcard ▸ hsp
  rw [← hspan]
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    change t.toList.getD (i : ℕ) 0 ∈ _
    by_cases h : (i : ℕ) < t.toList.length
    · refine Ideal.subset_span ?_
      rw [List.getD_eq_getElem _ 0 h]
      exact Finset.mem_coe.2 (Finset.mem_toList.1 (List.getElem_mem h))
    · rw [List.getD_eq_default _ _ (by omega)]
      exact Submodule.zero_mem _
  · intro x hx
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem (Finset.mem_toList.2 (Finset.mem_coe.1 hx))
    exact Ideal.subset_span
      ⟨⟨j, by omega⟩, by change t.toList.getD j 0 = x; rw [List.getD_eq_getElem _ 0 hj]; exact hjx⟩

/-- Cancellation of a finite summand in `WithBot ℕ∞`. -/
alias add_right_cancel_coe := Stacks.KrullDimension.LocalBaseChange.add_right_cancel_coe

/-- From `d + c = n` in `WithBot ℕ∞` with `c`, `n` natural numbers: `c ≤ n` and `d = n - c`. -/
theorem natCast_le_and_eq_of_add_eq {d : WithBot ℕ∞} {c n : ℕ}
    (h : d + (c : WithBot ℕ∞) = (n : WithBot ℕ∞)) :
    c ≤ n ∧ d = ((n - c : ℕ) : WithBot ℕ∞) := by
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = (e : WithBot ℕ∞) := by
    cases d with
    | bot => revert h; simp
    | coe e =>
      cases e with
      | top =>
          exfalso
          rw [← WithBot.coe_natCast, ← WithBot.coe_add, ← WithBot.coe_natCast,
            WithBot.coe_inj] at h
          exact (ENat.natCast_ne_top n) h.symm
      | coe m => exact ⟨m, by norm_cast⟩
  have he : e + c = n := by
    have hh : ((e + c : ℕ) : WithBot ℕ∞) = ((n : ℕ) : WithBot ℕ∞) := by push_cast; exact h
    exact_mod_cast hh
  exact ⟨by omega, by congr 1; omega⟩

/-! ### From item (2) to item (1) -/

/-- **The implication (2) ⇒ (1).**

Let `k` be a field, let `S = k[x_i]/I` be a presented `k`-algebra with finitely many variables,
let `q` be a prime of `S`, let `q'` be the corresponding prime of `k[x_i]` and let `c` be the
codimension, `height q' = height q + c`. If the ideal `I_{q'}` of `A = k[x_i]_{q'}` can be
generated by `c` elements, then there is a `g ∈ S`, `g ∉ q`, such that `S_g` is a global complete
intersection over `k`.

Clearing denominators in `c` generators of `I_{q'}` gives `f_1, …, f_c ∈ I` and a `u ∈ k[x_i]` with
`u ∉ q'` and `u·I ⊆ (f_1, …, f_c)`, so that `I` and `(f_1, …, f_c)` agree after inverting `u`;
enlarging `u` by a further factor makes the dimension of `S_g` attain the local dimension
`dim_q Spec S`, which is `n - c`. The localization `S_g` is then `k[x_i]/(f_1, …, f_c)` with `u`
inverted, that is `k[x_1, …, x_{n+1}]/(f_1, …, f_c, x_{n+1}u - 1)`: `n + 1` variables, `c + 1`
relations and dimension `(n + 1) - (c + 1)`. -/
theorem Algebra.Generators.exists_isGlobalCompleteIntersection_away_of_spanFinrank_ker_map_le
    (k : Type u) [Field k] (S : Type v) [CommRing S] [Algebra k S]
    {ι : Type w} [Finite ι] (P : Algebra.Generators k S ι)
    (q : Ideal S) [q.IsPrime] (c : ℕ)
    (hc : (q.comap (algebraMap P.Ring S)).height = q.height + c)
    (A : Type*) [CommRing A] [Algebra P.Ring A]
    [IsLocalization.AtPrime A (q.comap (algebraMap P.Ring S))]
    (hsp : Submodule.spanFinrank (P.ker.map (algebraMap P.Ring A)) ≤ c) :
    ∃ g ∉ q, IsGlobalCompleteIntersection k (Localization.Away g) := by
  classical
  have hsurj : Function.Surjective (algebraMap P.Ring S) := P.algebraMap_surjective
  have hnoethA : IsNoetherianRing A :=
    IsLocalization.isNoetherianRing (q.comap (algebraMap P.Ring S)).primeCompl A inferInstance
  obtain ⟨F, hF⟩ := exists_fin_span_eq (P.ker.map (algebraMap P.Ring A)) hsp
  have hFmem : ∀ i, F i ∈ P.ker.map (algebraMap P.Ring A) :=
    fun i => hF ▸ Ideal.subset_span ⟨i, rfl⟩
  have hclear : ∀ i : Fin c, ∃ y : P.Ring, y ∈ P.ker ∧
      ∃ ww : Aˣ, algebraMap P.Ring A y = F i * ww := by
    intro i
    obtain ⟨⟨y, s⟩, hys⟩ := (IsLocalization.mem_map_algebraMap_iff
      (q.comap (algebraMap P.Ring S)).primeCompl A).1 (hFmem i)
    obtain ⟨ww, hww⟩ :=
      IsLocalization.map_units (M := (q.comap (algebraMap P.Ring S)).primeCompl) A s
    exact ⟨y.1, y.2, ww, by rw [← hys, hww]⟩
  choose xg hxmem ww hxw using hclear
  set J : Ideal P.Ring := Ideal.span (Set.range xg) with hJdef
  have hJI : J ≤ P.ker := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hxmem i)
  have hJmap : J.map (algebraMap P.Ring A) = P.ker.map (algebraMap P.Ring A) := by
    rw [hJdef, Ideal.map_span, ← Set.range_comp,
      show ((algebraMap P.Ring A) ∘ xg) = (fun i => algebraMap P.Ring A (xg i)) from rfl,
      span_range_eq_of_unit_mul (fun i => ⟨ww i, hxw i⟩), hF]
  obtain ⟨u₁, hu₁mem, hu₁⟩ := exists_mem_mul_mem_of_map_le
    (q.comap (algebraMap P.Ring S)).primeCompl A hJmap.ge
  obtain ⟨g₂, hg₂, hdim₂⟩ :=
    PrimeSpectrum.exists_notMem_topologicalKrullDim_basicOpen_le_localKrullDim
      (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum S)
  obtain ⟨w₂, hw₂⟩ := hsurj g₂
  have hu₁q : algebraMap P.Ring S u₁ ∉ q := hu₁mem
  set u : P.Ring := u₁ * w₂ with hudef
  set g : S := algebraMap P.Ring S u with hgdef
  have hgmul : g = algebraMap P.Ring S u₁ * g₂ := by rw [hgdef, hudef, map_mul, hw₂]
  have hgq : g ∉ q := by
    rw [hgmul]
    intro hmem
    rcases (Ideal.IsPrime.mul_mem_iff_mem_or_mem ‹q.IsPrime›).1 hmem with h | h
    · exact hu₁q h
    · exact hg₂ h
  have huI : ∀ y ∈ P.ker, u * y ∈ J := by
    intro y hy
    have hre : u * y = w₂ * (u₁ * y) := by rw [hudef]; ring
    rw [hre]
    exact Ideal.mul_mem_left _ _ (hu₁ y hy)
  have hbo : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆
      (PrimeSpectrum.basicOpen g₂ : Set (PrimeSpectrum S)) := by
    rw [hgmul, PrimeSpectrum.basicOpen_mul]
    intro p hp
    exact hp.2
  have hdimle : ringKrullDim (Localization.Away g) ≤
      TopologicalSpace.localKrullDim (PrimeSpectrum S) (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum S) :=
    le_trans (PrimeSpectrum.ringKrullDim_le_topologicalKrullDim_basicOpen g _)
      (le_trans (topologicalKrullDim_le_of_subset hbo) hdim₂)
  have hD := PrimeSpectrum.localKrullDim_add_height_comap_eq_natCard_add_height k
    (show MvPolynomial ι k →ₐ[k] S from IsScalarTower.toAlgHom k P.Ring S) hsurj
    (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum S)
  have hqq : (PrimeSpectrum.comap
      (IsScalarTower.toAlgHom k P.Ring S).toRingHom (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum S)).asIdeal
      = q.comap (algebraMap P.Ring S) := rfl
  rw [hqq, hc] at hD
  have hq'le : ((q.comap (algebraMap P.Ring S)).height : WithBot ℕ∞) ≤ ringKrullDim P.Ring :=
    Ideal.height_le_ringKrullDim_of_ne_top
      (Ideal.IsPrime.ne_top (Ideal.comap_isPrime _ _))
  have hq'ne : (q.comap (algebraMap P.Ring S)).height ≠ ⊤ := by
    intro htop
    rw [htop, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field] at hq'le
    simp only [zero_add] at hq'le
    have htle : (⊤ : ℕ∞) ≤ (Nat.card ι : ℕ∞) := by exact_mod_cast hq'le
    simp at htle
  have hqne : q.height ≠ ⊤ := by
    intro htop
    rw [hc, htop] at hq'ne
    simp at hq'ne
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 hqne
  rw [← ha] at hD
  have hDD : TopologicalSpace.localKrullDim (PrimeSpectrum S) (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum S)
      + (c : WithBot ℕ∞) = (Nat.card ι : WithBot ℕ∞) := by
    refine add_right_cancel_coe (c := (a : ℕ∞)) (by simp) ?_
    rw [show (((a : ℕ) : ℕ∞) + (c : ℕ∞) : ℕ∞) = (((a + c : ℕ)) : ℕ∞) by push_cast; ring] at hD
    calc TopologicalSpace.localKrullDim (PrimeSpectrum S) (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum S)
          + (c : WithBot ℕ∞) + (((a : ℕ) : ℕ∞) : WithBot ℕ∞)
        = TopologicalSpace.localKrullDim (PrimeSpectrum S) (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum S)
            + ((((a + c : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
          push_cast
          ring
      _ = (Nat.card ι : WithBot ℕ∞) + (((a : ℕ) : ℕ∞) : WithBot ℕ∞) := by
          rw [hD]
  obtain ⟨hcn, hdq⟩ := natCast_le_and_eq_of_add_eq hDD
  set n : ℕ := Nat.card ι with hndef
  set ρ : P.Ring ≃ₐ[k] MvPolynomial (Fin n) k :=
    MvPolynomial.renameEquiv k (Finite.equivFin ι) with hρdef
  set f : Fin c → MvPolynomial (Fin n) k := fun i => ρ (xg i) with hfdef
  have hJρ : Ideal.span (Set.range f)
      = J.map (ρ : P.Ring →+* MvPolynomial (Fin n) k) := by
    rw [hJdef, Ideal.map_span, ← Set.range_comp]
    rfl
  set eρ : (P.Ring ⧸ J) ≃ₐ[k] (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) :=
    Ideal.quotientEquivAlg J (Ideal.span (Set.range f)) ρ hJρ with heρdef
  obtain ⟨he5⟩ := nonempty_localizationAway_algEquiv k eρ _ _ rfl
  obtain ⟨f', ⟨e'⟩⟩ := gci_localization_presentation k
    (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f))
    (Ideal.Quotient.mk (Ideal.span (Set.range f)) (ρ u)) n c f AlgEquiv.refl
  obtain ⟨e1⟩ := nonempty_localizationAway_quotient_algEquiv k P.Ring u J
  obtain ⟨e3⟩ := nonempty_localizationAway_quotient_algEquiv k P.Ring u P.ker
  have heqJ : J.map (algebraMap P.Ring (Localization.Away u))
      = P.ker.map (algebraMap P.Ring (Localization.Away u)) :=
    map_eq_map_of_mul_mem hJI huI (Localization.Away u)
  set εq : (P.Ring ⧸ P.ker) ≃ₐ[k] S :=
    Ideal.quotientKerAlgEquivOfSurjective
      (f := IsScalarTower.toAlgHom k P.Ring S) hsurj with hεqdef
  have hεq : εq (Ideal.Quotient.mk P.ker u) = g := by
    rw [hεqdef, hgdef]
    exact Ideal.quotientKerAlgEquivOfSurjective_mk hsurj u
  obtain ⟨e4⟩ := nonempty_localizationAway_algEquiv k εq _ _ hεq
  have E : Localization.Away (Ideal.Quotient.mk J u) ≃ₐ[k] Localization.Away g :=
    e1.trans ((Ideal.quotientEquivAlgOfEq k heqJ).trans (e3.symm.trans e4))
  have EE : Localization.Away g ≃ₐ[k]
      (MvPolynomial (Fin (n + 1)) k ⧸ Ideal.span (Set.range f')) :=
    E.symm.trans (he5.trans e')
  have hdisj : Disjoint (Submonoid.powers g : Set S) (q : Set S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨m, rfl⟩ hx
    exact hgq (‹q.IsPrime›.mem_of_pow_mem _ hx)
  have hprime : (q.map (algebraMap S (Localization.Away g))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) (Localization.Away g) q
      ‹q.IsPrime› hdisj
  have hnt : Nontrivial (Localization.Away g) := by
    rcases subsingleton_or_nontrivial (Localization.Away g) with hs | hs
    · exfalso
      refine hprime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
      rw [Subsingleton.elim (1 : Localization.Away g) 0]
      exact Submodule.zero_mem _
    · exact hs
  have hntQ : Nontrivial (MvPolynomial (Fin (n + 1)) k ⧸ Ideal.span (Set.range f')) := by
    have := hnt
    exact EE.symm.toEquiv.nontrivial
  have hlow := mvpoly_quotient_span_range_ringKrullDim_ge k (n + 1) (c + 1) f' hntQ
  have hEq : ringKrullDim (Localization.Away g)
      = ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ Ideal.span (Set.range f')) :=
    ringKrullDim_eq_of_ringEquiv EE.toRingEquiv
  refine ⟨g, hgq, Or.inr ⟨n + 1, c + 1, f', EE, by omega, le_antisymm ?_ ?_⟩⟩
  · have hss : (((n + 1) - (c + 1) : ℕ) : WithBot ℕ∞) = ((n - c : ℕ) : WithBot ℕ∞) := by
      congr 1
      omega
    rw [hss, ← hdq]
    exact hdimle
  · rw [hEq]
    exact hlow

/-- **The implication (5) ⇒ (1).** If the ideal `I_{q'}` of `A = k[x_i]_{q'}` is
generated by a regular sequence, then `S_g` is a global complete intersection over `k` for some
`g ∉ q`. This is (5) ⇒ (2) ⇒ (1), the first step being
`Algebra.Generators.spanFinrank_ker_map_le_iff_exists_isRegular`. -/
theorem Algebra.Generators.exists_isGlobalCompleteIntersection_away_of_exists_isRegular
    (k : Type u) [Field k] (S : Type v) [CommRing S] [Algebra k S]
    {ι : Type w} [Finite ι] (P : Algebra.Generators k S ι)
    (q : Ideal S) [q.IsPrime] (c : ℕ)
    (hc : (q.comap (algebraMap P.Ring S)).height = q.height + c)
    (A : Type*) [CommRing A] [Algebra P.Ring A]
    [IsLocalization.AtPrime A (q.comap (algebraMap P.Ring S))]
    (h : ∃ rs : List A, IsRegular A rs ∧ Ideal.ofList rs = P.ker.map (algebraMap P.Ring A)) :
    ∃ g ∉ q, IsGlobalCompleteIntersection k (Localization.Away g) :=
  P.exists_isGlobalCompleteIntersection_away_of_spanFinrank_ker_map_le k S q c hc A
    ((P.spanFinrank_ker_map_le_iff_exists_isRegular k S q c hc A).1.2 h)

end
