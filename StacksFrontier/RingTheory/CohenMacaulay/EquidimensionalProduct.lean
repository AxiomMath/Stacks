module

public import StacksFrontier.RingTheory.CohenMacaulay.Equidimensional
import all StacksFrontier.RingTheory.CohenMacaulay.Equidimensional
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Localization.Away.Lemmas
import StacksFrontier.RingTheory.KrullDimension.FiniteTypeNeTop

/-!
# Stacks 00OV: a Cohen-Macaulay finite type algebra is a product of equidimensional pieces

Let `k` be a field and let `S` be a Cohen-Macaulay `k`-algebra of finite type. Then
`Spec S = \coprod_d T_d` is a finite disjoint union of open and closed subsets `T_d`, with `T_d`
equidimensional of dimension `d`; equivalently `S` is a product of rings `S_d`,
`d = 0, …, dim S`, such that every maximal ideal of `S_d` has height `d`.

The decomposition of `Spec S`, with `T_d` the level set of the local dimension, is
`PrimeSpectrum.isLocallyConstant_localKrullDim_and_equidimensional_fiber_and_finite_range` in
`StacksFrontier.RingTheory.CohenMacaulay.Equidimensional`, whose module docstring explains the
modelling. This file adds the product form and states the whole lemma.

## Main results

* The statement of Stacks 00OV, in namespace `PrimeSpectrum`:
  `isLocallyConstant_localKrullDim_and_equidimensional_fiber_and_exists_algEquiv_pi`.

## Implementation notes

*The equivalent product decomposition.* "`S` is a product of rings `S_d`, `d = 0, …, dim S`,
such that every maximal ideal of `S_d` has height `d`" is the last conjunct of the main
result: an isomorphism of `k`-algebras from `S` onto a product of rings indexed by the natural
numbers `d ≤ dim S`, every maximal ideal of the factor indexed by `d` having height `d`. As in
the source it comes from the clopen decomposition through Lemma 00EM: Mathlib's
`PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen` gives an idempotent `e_d` with
`T_d = D(e_d)`, disjointness and covering of the `T_d` make the `e_d` a complete family of
orthogonal idempotents, and Mathlib's `CompleteOrthogonalIdempotents.bijective_pi` identifies `S`
with `∏_d S ⧸ (1 - e_d)`. The factor `S ⧸ (1 - e_d)` is the localization `S_{e_d}`
(`IsLocalization.Away.quotient_of_isIdempotentElem`), so its maximal ideals have the heights of
the maximal ideals of `S` in `T_d` (`IsLocalization.height_under`), and for a maximal ideal `𝔪`
the local dimension at `𝔪` is `𝔪.height`, because `𝔪` is the only maximal ideal above itself
(Lemma 00OT). A factor may be the zero ring, when `T_d` is empty, exactly as in the source.

## References

* [StacksProject 00OV](https://stacks.math.columbia.edu/tag/00OV)
-/

@[expose] public section

universe v

namespace PrimeSpectrum

open TopologicalSpace

/-- The product half of Stacks 00OV: a Cohen-Macaulay finite type `k`-algebra `S` is, as a
`k`-algebra, the product of the rings `S ⧸ (1 - e_d)` over `d = 0, …, dim S`, where `e_d` is the
idempotent cutting out the level set `T_d` of the local dimension (Lemma 00EM), and every maximal
ideal of the factor indexed by `d` has height `d`. -/
private theorem exists_algEquiv_pi_of_isMaximalCohenMacaulay
    {k : Type*} {S : Type v} [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (hS : ∀ (p : Ideal S) [p.IsPrime],
      Module.IsMaximalCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p)) :
    ∃ (R : {d : ℕ // (d : WithBot ℕ∞) ≤ ringKrullDim S} → Type v)
      (_ : ∀ d, CommRing (R d)) (_ : ∀ d, Algebra k (R d)),
      Nonempty (S ≃ₐ[k] ((d : {d : ℕ // (d : WithBot ℕ∞) ≤ ringKrullDim S}) → R d)) ∧
        ∀ d (𝔪 : Ideal (R d)), 𝔪.IsMaximal → 𝔪.height = d.1 := by
  classical
  have hlc := (Stacks.CohenMacaulay.Equidimensional.solution (k := k) hS).1
  set I := {d : ℕ // (d : WithBot ℕ∞) ≤ ringKrullDim S}
  -- the index set `0, …, dim S` is finite, `dim S` being finite
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim S ≤ n := by
    have htop := ringKrullDim_ne_top_of_finiteType (κ := k) (A := S)
    rcases h : ringKrullDim S with _ | x
    · exact ⟨0, bot_le⟩
    · rcases x with _ | m
      · exact absurd h htop
      · exact ⟨m, le_rfl⟩
  have : Finite I := Finite.of_injective (fun d : I => (⟨d.1, Nat.lt_succ_of_le
    (by exact_mod_cast d.2.trans hn)⟩ : Fin (n + 1))) fun a b h => Subtype.ext (by
      simpa using congrArg Fin.val h)
  have : Fintype I := Fintype.ofFinite I
  -- every point lies in some `T_d` with `d` in the index set
  have hmem : ∀ p : PrimeSpectrum S, ∃ d : I,
      localKrullDim (PrimeSpectrum S) p = (d.1 : WithBot ℕ∞) := by
    intro p
    obtain ⟨q, hq, hqp⟩ := Stacks.CohenMacaulay.Equidimensional.exists_isMin_le p
    have hfp := Stacks.CohenMacaulay.Equidimensional.localKrullDim_eq_coheight k hS hq hqp
    have hle : localKrullDim (PrimeSpectrum S) p ≤ ringKrullDim S := by
      rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
        topologicalKrullDim_eq_iSup_localKrullDim]
      exact le_iSup (localKrullDim (PrimeSpectrum S)) p
    rw [hfp] at hle ⊢
    have hle' := hle.trans hn
    induction hc : Order.coheight q using ENat.recTopCoe with
    | top =>
      rw [hc] at hle'
      have h' : (⊤ : ℕ∞) ≤ n := by exact_mod_cast hle'
      exact absurd h' (by simp)
    | coe m =>
      rw [hc] at hle
      exact ⟨⟨m, by exact_mod_cast hle⟩, rfl⟩
  -- the idempotents cutting out the `T_d`
  have hex : ∀ d : I, ∃ e : S, IsIdempotentElem e ∧
      localKrullDim (PrimeSpectrum S) ⁻¹' {(d.1 : WithBot ℕ∞)} = PrimeSpectrum.basicOpen e :=
    fun d => PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen (hlc.isClopen_fiber _)
  choose e he heT using hex
  have hmemT : ∀ (d : I) (p : PrimeSpectrum S),
      e d ∉ p.asIdeal ↔ localKrullDim (PrimeSpectrum S) p = (d.1 : WithBot ℕ∞) :=
    fun d p => by
      rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← heT d]
      rfl
  have hortho : OrthogonalIdempotents e := by
    refine ⟨he, fun i j hij => (he i).mul (he j) |>.eq_zero_of_isNilpotent ?_⟩
    refine (nilpotent_iff_mem_prime).mpr fun P hP => ?_
    by_contra hne
    have hi : e i ∉ P := fun h => hne (P.mul_mem_right _ h)
    have hj : e j ∉ P := fun h => hne (P.mul_mem_left _ h)
    have h1 := (hmemT i ⟨P, hP⟩).mp hi
    have h2 := (hmemT j ⟨P, hP⟩).mp hj
    exact hij (Subtype.ext (by exact_mod_cast h1.symm.trans h2))
  have hcomplete : CompleteOrthogonalIdempotents e := by
    refine ⟨hortho, ?_⟩
    have hidem : IsIdempotentElem (1 - ∑ d, e d) :=
      (hortho.isIdempotentElem_sum (s := Finset.univ)).one_sub
    refine (sub_eq_zero.mp (hidem.eq_zero_of_isNilpotent ?_)).symm
    refine (nilpotent_iff_mem_prime).mpr fun P hP => ?_
    obtain ⟨d, hd⟩ := hmem ⟨P, hP⟩
    have hed : e d ∉ P := (hmemT d ⟨P, hP⟩).mpr hd
    have hzero : e d * (1 - ∑ d, e d) = 0 := by
      rw [mul_sub, mul_one, hortho.mul_sum_of_mem (Finset.mem_univ d), sub_self]
    exact (hP.mem_or_mem (hzero ▸ P.zero_mem)).resolve_left hed
  refine ⟨fun d => S ⧸ Ideal.span {1 - e d}, fun _ => inferInstance, fun _ => inferInstance,
    ⟨AlgEquiv.ofBijective (AlgHom.pi fun d => Ideal.Quotient.mkₐ k _)
      hcomplete.bijective_pi⟩, fun d 𝔪 h𝔪 => ?_⟩
  -- a maximal ideal of `S ⧸ (1 - e_d)` is a maximal ideal `M` of `S` lying in `T_d`
  have : IsLocalization.Away (e d) (S ⧸ Ideal.span {1 - e d}) :=
    IsLocalization.Away.quotient_of_isIdempotentElem (he d)
  set M := 𝔪.comap (Ideal.Quotient.mk (Ideal.span {1 - e d}))
  have hM : M.IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hheight : M.height = 𝔪.height :=
    IsLocalization.height_under (Submonoid.powers (e d)) 𝔪
  have h1e : 1 - e d ∈ M := by
    simp [M, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)]
  have heM : e d ∉ M := fun h => hM.ne_top ((Ideal.eq_top_iff_one _).mpr
    (by simpa using M.add_mem h1e h))
  have hfM := (hmemT d ⟨M, hM.isPrime⟩).mp heM
  rw [Stacks.CohenMacaulay.EquidimensionalCut.localKrullDim_eq_height_of_isMaximal k M hM,
    hheight] at hfM
  exact_mod_cast hfM


/-- **Stacks 00OV.** Let `k` be a field and let `S` be a Cohen-Macaulay finite type `k`-algebra.
Then `Spec S` is the disjoint union of the level sets `T_d` of its local dimension; these are
open and closed, there are finitely many nonempty ones, and `T_d` is equidimensional of
dimension `d`. Equivalently, `S` is a product of rings `S_d`, `d = 0, …, dim S`, such that every
maximal ideal of `S_d` has height `d`. -/
@[stacks 00OV "The family `T_d` is the family of fibers of `TopologicalSpace.localKrullDim`
(Topology Definition 0055 (4)), indexed by `WithBot ℕ∞`; a nonempty fiber has `d` a natural
number at most `dim S`. Disjointness and covering are definitional, `T_d` open and closed is
`IsLocallyConstant.isClopen_fiber`, and finiteness of the union is finiteness of the range. The
product form is the last conjunct, a `k`-algebra isomorphism `S ≃ₐ[k] ∏_{d ≤ dim S} S_d`; it is
built from Mathlib's `PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen` (Lemma 00EM) and
`CompleteOrthogonalIdempotents.bijective_pi`. Cohen-Macaulayness of the Noetherian ring `S`
(Definition 00NC) is spelled out over its localizations at primes, as in tags 00ND and 00R9. See
the module docstring."]
public theorem
    isLocallyConstant_localKrullDim_and_equidimensional_fiber_and_exists_algEquiv_pi
    {k : Type*} {S : Type v} [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (hS : ∀ (p : Ideal S) [p.IsPrime],
      Module.IsMaximalCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p)) :
    IsLocallyConstant (localKrullDim (PrimeSpectrum S)) ∧
      (∀ d : WithBot ℕ∞,
        Equidimensional ↥(localKrullDim (PrimeSpectrum S) ⁻¹' {d}) ∧
          ((localKrullDim (PrimeSpectrum S) ⁻¹' {d}).Nonempty →
            topologicalKrullDim ↥(localKrullDim (PrimeSpectrum S) ⁻¹' {d}) = d)) ∧
        (Set.range (localKrullDim (PrimeSpectrum S))).Finite ∧
        ∃ (R : {d : ℕ // (d : WithBot ℕ∞) ≤ ringKrullDim S} → Type v)
          (_ : ∀ d, CommRing (R d)) (_ : ∀ d, Algebra k (R d)),
          Nonempty (S ≃ₐ[k] ((d : {d : ℕ // (d : WithBot ℕ∞) ≤ ringKrullDim S}) → R d)) ∧
            ∀ d (𝔪 : Ideal (R d)), 𝔪.IsMaximal → 𝔪.height = d.1 :=
  have h := Stacks.CohenMacaulay.Equidimensional.solution (k := k) hS
  ⟨h.1, h.2.1, h.2.2, exists_algEquiv_pi_of_isMaximalCohenMacaulay hS⟩

end PrimeSpectrum

end
