module

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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.Ideal.Pure
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
public import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-!
# Characterizations of pure ideals

Let `R` be a commutative ring and `I ⊆ R` an ideal. This file proves that the eleven conditions
of Stacks 04PS on `I` are equivalent: purity of `I` (flatness of `R ⧸ I`), the lattice identity
`I ⊓ J = I * J` for all ideals `J`, for all finitely generated `J`, and for all principal `J`, the
equational condition that every `x ∈ I` satisfy `x = x * y` for some `y ∈ I` (and its finite
uniform strengthening), the pointwise condition that `I` localize to `⊥` or to `⊤` at every prime,
the identity `Supp(I) = Spec(R) ∖ V(I)`, the description of `I` as the kernel of
`R → (1 + I)⁻¹R`, and the description of `R ⧸ I` as an `R`-algebra localization of `R`,
necessarily the one at `1 + I`.

## Main results

* `Stacks.IdealTheory.PureIdealTFAE.solution`: the eleven conditions are equivalent.

## Implementation notes

The whole equivalence turns on one construction, isolated as
`isLocalization_quotient_of_forall_exists_eq_mul`: the equational condition (5) says exactly that
`R ⧸ I` *is* a localization of `R` at the multiplicative set `1 + I`. Granting that, (11) is
`IsLocalization.algEquiv`, and (10) ⇒ (1) is flatness of a localization. Item (9) is read off from
`IsLocalization.map_eq_zero_iff` directly: an element of `R` dies in `(1 + I)⁻¹R` exactly when it
is killed by some `1 - y` with `y ∈ I`. The remaining content is the passage between (5) and the
pointwise condition (7): the forward direction is Mathlib's
`Ideal.le_ker_atPrime_of_forall_exists_eq_mul`, and the backward direction is a maximal-ideal
argument on the colon ideal `(I * (x)) : (x)`
(`forall_exists_eq_mul_of_forall_map_atPrime_eq`).

The source deduces (7) ⇒ (1) from locality of flatness (Stacks 00HT), which needs the localization
of `R ⧸ I` at a prime to be identified with a quotient of `R_𝔭`. The route taken here instead
runs (7) ⇒ (5) ⇒ (2) ⇒ (3) ⇒ (1), where (5) ⇒ (2) is one line (`x ∈ I ⊓ J` gives `x = y * x` with
`y ∈ I` and `x ∈ J`) and (3) ⇒ (1) is Mathlib's `Ideal.Pure.of_inf_eq_mul`. Locality of flatness is
therefore not used, and the statement of Tag `00HT` is not imported.

## References

* [StacksProject 04PS](https://stacks.math.columbia.edu/tag/04PS)
-/

@[expose] public section

namespace Stacks.IdealTheory.PureIdealTFAE

open PrimeSpectrum

variable {R : Type*} [CommRing R] {I : Ideal R}

/-! ### The multiplicative set `1 + I` -/

/-- Membership in the multiplicative set `1 + I`, spelled as the submonoid of elements mapping to
`1` in `R ⧸ I`. -/
private lemma mem_onePlus {x : R} :
    x ∈ Submonoid.comap (Ideal.Quotient.mk I).toMonoidHom ⊥ ↔ x - 1 ∈ I := by
  simp [Ideal.Quotient.mk_eq_one_iff_sub_mem]

/-- One minus an element of `I` lies in `1 + I`. -/
private lemma one_sub_mem_onePlus {y : R} (hy : y ∈ I) :
    1 - y ∈ Submonoid.comap (Ideal.Quotient.mk I).toMonoidHom ⊥ := by
  rw [mem_onePlus]
  simpa using I.neg_mem hy

/-- **The heart of Stacks 04PS.** If every `x ∈ I` satisfies `x = x * y` for some `y ∈ I`, then
`R ⧸ I` is the localization of `R` at the multiplicative set `1 + I`. -/
private lemma isLocalization_quotient_of_forall_exists_eq_mul
    (h : ∀ x ∈ I, ∃ y ∈ I, x = x * y) :
    IsLocalization (Submonoid.comap (Ideal.Quotient.mk I).toMonoidHom ⊥) (R ⧸ I) where
  map_units s := by
    rw [Ideal.Quotient.algebraMap_eq]
    exact (Submonoid.mem_bot.1 s.2 : Ideal.Quotient.mk I s.1 = 1) ▸ isUnit_one
  surj z := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨⟨r, 1⟩, by simp⟩
  exists_of_eq {x y} hxy := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq] at hxy
    obtain ⟨z, hz, hzeq⟩ := h _ hxy
    refine ⟨⟨1 - z, one_sub_mem_onePlus hz⟩, ?_⟩
    have : (x - y) * (1 - z) = 0 := by rw [mul_sub, mul_one, ← hzeq, sub_self]
    linear_combination this

/-! ### The kernel of `R → (1 + I)⁻¹R` -/

/-- The kernel of `R → (1 + I)⁻¹R` is always contained in `I`. -/
private lemma ker_algebraMap_le (A : Type*) [CommRing A] [Algebra R A]
    [IsLocalization (Submonoid.comap (Ideal.Quotient.mk I).toMonoidHom ⊥) A] :
    RingHom.ker (algebraMap R A) ≤ I := by
  intro x hx
  obtain ⟨m, hm⟩ :=
    (IsLocalization.map_eq_zero_iff
      (Submonoid.comap (Ideal.Quotient.mk I).toMonoidHom ⊥) A x).1 hx
  have : x = -((m.1 - 1) * x) := by linear_combination hm
  exact this ▸ I.neg_mem (I.mul_mem_right _ (mem_onePlus.1 m.2))

/-- If `x ∈ I` implies `x = x * y` for some `y ∈ I`, then `I` is contained in the kernel of
`R → (1 + I)⁻¹R`. -/
private lemma le_ker_algebraMap_of_forall_exists_eq_mul (A : Type*) [CommRing A] [Algebra R A]
    [IsLocalization (Submonoid.comap (Ideal.Quotient.mk I).toMonoidHom ⊥) A]
    (h : ∀ x ∈ I, ∃ y ∈ I, x = x * y) : I ≤ RingHom.ker (algebraMap R A) := by
  intro x hx
  obtain ⟨y, hy, hyeq⟩ := h x hx
  refine (IsLocalization.map_eq_zero_iff
    (Submonoid.comap (Ideal.Quotient.mk I).toMonoidHom ⊥) A x).2
      ⟨⟨1 - y, one_sub_mem_onePlus hy⟩, ?_⟩
  change (1 - y) * x = 0
  linear_combination hyeq

/-! ### Localizations at primes -/

/-- If `I` is not contained in the prime `p`, then `I` generates the unit ideal in `R_p`. -/
private lemma map_atPrime_eq_top_of_not_le {p : Ideal R} [p.IsPrime] (h : ¬ I ≤ p) :
    I.map (algebraMap R (Localization.AtPrime p)) = ⊤ := by
  obtain ⟨x, hxI, hxp⟩ := IsConcreteLE.not_le_iff_exists.1 h
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hxI)
    (IsLocalization.map_units _ (⟨x, hxp⟩ : p.primeCompl))

/-- If `I` is contained in the prime `p`, then `I` does not generate the unit ideal in `R_p`. -/
private lemma map_atPrime_ne_top_of_le {p : Ideal R} [p.IsPrime] (h : I ≤ p) :
    I.map (algebraMap R (Localization.AtPrime p)) ≠ ⊤ := by
  refine fun htop ↦ (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime p)).ne_top ?_
  refine top_le_iff.1 (htop ▸ ?_)
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.map_mono h

/-- The kernel of `R → R_p` is contained in `p`. -/
private lemma ker_atPrime_le {p : PrimeSpectrum R} :
    RingHom.ker (algebraMap R (Localization.AtPrime p.asIdeal)) ≤ p.asIdeal := by
  intro x hx
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl _ x).1 hx
  exact (p.isPrime.mem_or_mem (hs ▸ p.asIdeal.zero_mem)).resolve_left s.2

/-- A prime lies outside the support of `I` exactly when `I` dies in the localization at it. -/
private lemma notMem_support_iff_le_ker {p : PrimeSpectrum R} :
    p ∉ Module.support R I ↔
      I ≤ RingHom.ker (algebraMap R (Localization.AtPrime p.asIdeal)) := by
  rw [Module.notMem_support_iff']
  refine ⟨fun h x hx ↦ ?_, fun h m ↦ ?_⟩
  · obtain ⟨r, hr, hrx⟩ := h ⟨x, hx⟩
    refine (IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl _ x).2 ⟨⟨r, hr⟩, ?_⟩
    simpa [Submodule.coe_smul_of_tower, Subtype.ext_iff] using hrx
  · obtain ⟨r, hr⟩ := (IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl _ m.1).1 (h m.2)
    exact ⟨r.1, r.2, by ext; simpa using hr⟩

/-! ### From the pointwise condition back to the equational one -/

/-- If `I` localizes to `⊥` or to `⊤` at every prime, then every `x ∈ I` satisfies `x = x * y`
for some `y ∈ I`. -/
private lemma forall_exists_eq_mul_of_forall_map_atPrime_eq
    (h : ∀ p : PrimeSpectrum R,
      I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊥ ∨
        I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊤) :
    ∀ x ∈ I, ∃ y ∈ I, x = x * y := by
  intro x hx
  set K : Ideal R := (I * Ideal.span {x}).colon (Ideal.span {x})
  have hIK : I ≤ K := by
    intro a ha
    refine Submodule.mem_colon.2 fun s hs ↦ ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hs
    rw [smul_eq_mul, ← mul_assoc, mul_comm a c, mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul ha (Ideal.mem_span_singleton_self x))
  have hKtop : K = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hKm⟩ := K.exists_le_maximal hne
    have := hm.isPrime
    have hIm : I ≤ m := hIK.trans hKm
    have hker : I ≤ RingHom.ker (algebraMap R (Localization.AtPrime m)) :=
      (Ideal.map_eq_bot_iff_le_ker _).1 <|
        (h ⟨m, hm.isPrime⟩).resolve_right (map_atPrime_ne_top_of_le hIm)
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl _ x).1 (hker hx)
    refine s.2 (hKm (Submodule.mem_colon.2 fun t ht ↦ ?_))
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ht
    have : (s : R) • (c * x) = 0 := by
      rw [smul_eq_mul, ← mul_assoc, mul_comm (s : R) c, mul_assoc, hs, mul_zero]
    rw [this]
    exact Submodule.zero_mem _
  have hmem : x ∈ I * Ideal.span {x} := by
    have := Submodule.mem_colon.1 (hKtop.ge (Submodule.mem_top : (1 : R) ∈ ⊤)) x
      (Ideal.mem_span_singleton_self x)
    simpa using this
  obtain ⟨z, hz, hzx⟩ := Ideal.mem_mul_span_singleton.1 hmem
  exact ⟨z, hz, by rw [mul_comm]; exact hzx.symm⟩

/-! ### The finite uniform version -/

/-- Finitely many elements of `I`, each of the form `x = x * y` with `y ∈ I`, admit a single such
`y`: if `1 - yᵢ` kills `xᵢ`, then `1 - y := ∏ (1 - yᵢ)` kills all of them at once. -/
private lemma exists_mem_forall_eq_mul (h : ∀ x ∈ I, ∃ y ∈ I, x = x * y) (s : Finset R)
    (hs : (s : Set R) ⊆ I) : ∃ y ∈ I, ∀ x ∈ s, x = x * y := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, I.zero_mem, by simp⟩
  | insert a t ha ih =>
    have hat : (t : Set R) ⊆ I := fun z hz ↦ hs (by simp [hz])
    have haI : a ∈ I := hs (by simp)
    obtain ⟨y, hy, hyt⟩ := ih hat
    obtain ⟨z, hz, hza⟩ := h a haI
    refine ⟨y + z - y * z, sub_mem (add_mem hy hz) (I.mul_mem_left _ hz), ?_⟩
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hwt
    · linear_combination (1 - y) * hza
    · linear_combination (1 - z) * hyt w hwt

/-- **Characterizations of pure ideals.** For an ideal `I` of a commutative ring `R` the
following are equivalent: `I` is pure; `I ⊓ J = I * J` for every ideal `J`, for every finitely
generated `J`, and for every principal `J`; every `x ∈ I` satisfies `x = x * y` for some `y ∈ I`,
and finitely many elements of `I` admit a common such `y`; `I` localizes to `⊥` or `⊤` at every
prime; `Supp(I)` is the complement of `V(I)`; `I` is the kernel of `R → (1 + I)⁻¹R`; and
`R ⧸ I` is isomorphic as an `R`-algebra to a localization of `R`, namely the one at `1 + I`. -/
public theorem solution {R : Type*} [CommRing R] (I : Ideal R) :
    List.TFAE
      [I.Pure,
       ∀ J : Ideal R, I ⊓ J = I * J,
       ∀ J : Ideal R, J.FG → I ⊓ J = I * J,
       ∀ x : R, I ⊓ Ideal.span {x} = I * Ideal.span {x},
       ∀ x ∈ I, ∃ y ∈ I, x = x * y,
       ∀ s : Finset R, (s : Set R) ⊆ I → ∃ y ∈ I, ∀ x ∈ s, x = x * y,
       ∀ p : PrimeSpectrum R,
         I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊥ ∨
           I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊤,
       Module.support R I = (PrimeSpectrum.zeroLocus (I : Set R))ᶜ,
       RingHom.ker (algebraMap R
         (Localization (Submonoid.comap (Ideal.Quotient.mk I).toMonoidHom ⊥))) = I,
       ∃ S : Submonoid R, Nonempty ((R ⧸ I) ≃ₐ[R] Localization S),
       Nonempty ((R ⧸ I) ≃ₐ[R]
         Localization (Submonoid.comap (Ideal.Quotient.mk I).toMonoidHom ⊥))] := by
  tfae_have 1 → 2 := fun _ J ↦ I.inf_eq_mul_of_pure J
  tfae_have 2 → 3 := fun h J _ ↦ h J
  tfae_have 3 → 1 := fun h ↦ Ideal.Pure.of_inf_eq_mul I fun {J} hJ ↦ h J hJ
  tfae_have 2 → 4 := fun h x ↦ h _
  tfae_have 4 → 5 := by
    intro h x hx
    obtain ⟨z, hz, hzx⟩ := Ideal.mem_mul_span_singleton.1
      (h x ▸ (Submodule.mem_inf.2 ⟨hx, Ideal.mem_span_singleton_self x⟩))
    exact ⟨z, hz, by rw [mul_comm]; exact hzx.symm⟩
  tfae_have 5 → 2 := by
    intro h J
    refine le_antisymm (fun x hx ↦ ?_) Ideal.mul_le_inf
    obtain ⟨y, hy, hyx⟩ := h x hx.1
    have hyx' : y * x = x := by rw [mul_comm]; exact hyx.symm
    exact hyx' ▸ Ideal.mul_mem_mul hy hx.2
  tfae_have 5 → 6 := exists_mem_forall_eq_mul
  tfae_have 6 → 5 := by
    intro h x hx
    obtain ⟨y, hy, hxy⟩ := h {x} (by simpa using hx)
    exact ⟨y, hy, hxy x (Finset.mem_singleton_self x)⟩
  tfae_have 5 → 7 := by
    intro h p
    have := p.isPrime
    by_cases hle : I ≤ p.asIdeal
    · exact Or.inl ((Ideal.map_eq_bot_iff_le_ker _).2
        (Ideal.le_ker_atPrime_of_forall_exists_eq_mul h hle))
    · exact Or.inr (map_atPrime_eq_top_of_not_le hle)
  tfae_have 7 → 5 := forall_exists_eq_mul_of_forall_map_atPrime_eq
  tfae_have 7 → 8 := by
    intro h
    ext p
    have := p.isPrime
    rw [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe,
      ← not_iff_not, not_not, notMem_support_iff_le_ker]
    exact ⟨fun hk ↦ hk.trans ker_atPrime_le, fun hle ↦ (Ideal.map_eq_bot_iff_le_ker _).1 <|
      (h p).resolve_right (map_atPrime_ne_top_of_le hle)⟩
  tfae_have 8 → 7 := by
    intro h p
    have := p.isPrime
    by_cases hle : I ≤ p.asIdeal
    · refine Or.inl ((Ideal.map_eq_bot_iff_le_ker _).2 (notMem_support_iff_le_ker.1 ?_))
      rw [h]
      simpa using hle
    · exact Or.inr (map_atPrime_eq_top_of_not_le hle)
  tfae_have 5 → 9 := fun h ↦
    le_antisymm (ker_algebraMap_le _) (le_ker_algebraMap_of_forall_exists_eq_mul _ h)
  tfae_have 9 → 5 := by
    intro h x hx
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.comap (Ideal.Quotient.mk I).toMonoidHom ⊥) _ x).1 (h.ge hx)
    refine ⟨1 - m.1, ?_, by linear_combination hm⟩
    simpa using I.neg_mem (mem_onePlus.1 m.2)
  tfae_have 5 → 11 := fun h ↦ by
    have := isLocalization_quotient_of_forall_exists_eq_mul h
    exact ⟨IsLocalization.algEquiv (Submonoid.comap (Ideal.Quotient.mk I).toMonoidHom ⊥)
      (R ⧸ I) (Localization (Submonoid.comap (Ideal.Quotient.mk I).toMonoidHom ⊥))⟩
  tfae_have 11 → 10 := fun ⟨e⟩ ↦ ⟨_, ⟨e⟩⟩
  tfae_have 10 → 1 := fun ⟨S, ⟨e⟩⟩ ↦ by
    have : Module.Flat R (Localization S) := IsLocalization.flat _ S
    exact Module.Flat.of_linearEquiv e.toLinearEquiv
  tfae_finish

end Stacks.IdealTheory.PureIdealTFAE

end

/-!
# Characterizations of pure ideals

Let `R` be a commutative ring and let `I ⊆ R` be an ideal. Recall that `I` is *pure* if the
quotient ring `R ⧸ I` is flat over `R` (`Ideal.Pure`). Purity is an unexpectedly rigid condition:
it is at the same time a flatness condition, a purely equational one ("every `x ∈ I` satisfies
`x = xy` for some `y ∈ I`"), a condition on the ideal lattice (`J ∩ I = IJ` for all `J`), a
pointwise condition on `Spec(R)` (at every prime the ideal localizes to `0` or to everything), and
the condition that `R ⧸ I` be a *localization* of `R` — necessarily the localization at the
multiplicative set `1 + I`. The eleven conditions of the source are:

1. `I` is pure;
2. `J ∩ I = IJ` for every ideal `J ⊆ R`;
3. `J ∩ I = IJ` for every finitely generated ideal `J ⊆ R`;
4. `(x) ∩ I = xI` for every `x ∈ R`;
5. every `x ∈ I` satisfies `x = xy` for some `y ∈ I`;
6. finitely many `x₁, …, xₙ ∈ I` admit a single `y ∈ I` with `xᵢ = xᵢy` for all `i`;
7. `IR_𝔭 = 0` or `IR_𝔭 = R_𝔭` for every prime `𝔭` of `R`;
8. `Supp(I) = Spec(R) \ V(I)`;
9. `I` is the kernel of `R → (1 + I)⁻¹R`;
10. `R ⧸ I ≅ S⁻¹R` as `R`-algebras for some multiplicative subset `S ⊆ R`;
11. `R ⧸ I ≅ (1 + I)⁻¹R` as `R`-algebras.

## Main results

* `Ideal.pure_tfae`: the eleven conditions above are equivalent.

## Implementation notes

The eleven conditions are the entries, in the source's order, of a single `List.TFAE`, so the
`n`-th entry is the source's item `(n)`.

Items (2), (3) and (4) are written `I ⊓ J = I * J`, the orientation of `Ideal.inf_eq_mul_of_pure`;
the source writes `J ∩ I = IJ` in (2) and `J ∩ I = JI` in (3), which agree with it as `R` is
commutative. Item (4) is the principal case `J = Ideal.span {x}` of (2), spelled with
`Ideal.span {x} * I` rather than `x • I` so that (2), (3) and (4) read as one family.

Item (6) takes a `Finset R` contained in `I` in place of the source's list `x₁, …, xₙ`: only the
set of values of the family enters the conclusion, so a repetition among the `xᵢ` is irrelevant
and the two forms carry the same content.

In item (7) the ideal `IR_𝔭` generated by the image of `I` is `Ideal.map` along the canonical
`algebraMap R (Localization.AtPrime 𝔭)`, and the two alternatives `IR_𝔭 = 0`, `IR_𝔭 = R_𝔭` are
`⊥` and `⊤`. It is quantified over `PrimeSpectrum R`, the index of the support in item (8), since
(7) ⇔ (8) is a pointwise comparison.

Item (8) uses `Module.support R I`, Mathlib's support of `↥I` as an `R`-module, and reads
`Spec(R) \ V(I)` as the complement of `PrimeSpectrum.zeroLocus`.

Mathlib has no name for the multiplicative set `1 + I` of items (9) and (11). It is spelled here
as `Submonoid.comap (Ideal.Quotient.mk I).toMonoidHom ⊥`, the submonoid of elements mapping to
`1` in `R ⧸ I`; its members are exactly the `x` with `x - 1 ∈ I`
(`Ideal.Quotient.mk_eq_one_iff_sub_mem`), that is, `1 + I`. Both entries mention `(1 + I)⁻¹R` as a
*single* ring, so the concrete model `Localization` is used for it; this is not a restriction,
because any `R`-algebra `A` with `IsLocalization (1 + I) A` is `R`-algebra isomorphic to it over
`R` (`IsLocalization.algEquiv`), which transports the kernel of item (9) and the isomorphism of
item (11). In item (10) the multiplicative set is existentially quantified, so `Localization S`
likewise costs nothing there.

Faithfulness. (1) There is no hypothesis beyond `[CommRing R]` and `I : Ideal R`, and each of the
eleven entries is a condition on that same `I` with no added conjunct, so no hypothesis is dead.
(2) The scalars and the base are the source's: the isomorphisms of (10) and (11) are `R`-algebra
isomorphisms `≃ₐ[R]` and not merely ring isomorphisms, and the ideals of (7) are ideals of the
localized ring generated by the image of `I` under the `R`-algebra structure map. (3) Where the
source names a canonical map the statement pins it: (9) is the assertion that the kernel of
`algebraMap R ((1 + I)⁻¹R)` *equals* `I`, not that `I` is some kernel, and (7) uses the ideal
generated by the image of `algebraMap R (Localization.AtPrime 𝔭)` itself. (4) The instantiation is
not degenerate: for a product `R = A × B` of nonzero rings and `I = A × 0` all eleven hold with
content — `R ⧸ I ≅ B` is the localization of `R` at the idempotent `(0, 1)`, `V(I)` is the copy of
`Spec(B)` and `Supp(I)` its nonempty complement — while for `R = ℤ` and `I = (2)` all eleven fail,
`x = 2` admitting no `y ∈ I` with `2 = 2y`, so the list is not vacuously true.

## References

* [StacksProject 04PS](https://stacks.math.columbia.edu/tag/04PS)

## Tags

pure ideal, flat, localization, support, idempotent ideal
-/

@[expose] public section

/-- **Characterizations of pure ideals.** For an ideal `I` of a commutative ring `R` the following
are equivalent: (1) `I` is pure, i.e. `R ⧸ I` is flat over `R`; (2) `I ⊓ J = I * J` for every
ideal `J`; (3) the same for every finitely generated `J`; (4) the same for every principal `J`;
(5) every `x ∈ I` satisfies `x = x * y` for some `y ∈ I`; (6) finitely many elements of `I` admit
a common such `y`; (7) `I` localizes to `⊥` or to `⊤` at every prime; (8) the support of `I` is the
complement of `V(I)`; (9) `I` is the kernel of `R → (1 + I)⁻¹R`; (10) `R ⧸ I` is `R`-algebra
isomorphic to a localization of `R`; (11) `R ⧸ I` is `R`-algebra isomorphic to `(1 + I)⁻¹R`. -/
@[stacks 04PS]
public theorem Ideal.pure_tfae {R : Type*} [CommRing R] (I : Ideal R) :
    List.TFAE
      [I.Pure,
       ∀ J : Ideal R, I ⊓ J = I * J,
       ∀ J : Ideal R, J.FG → I ⊓ J = I * J,
       ∀ x : R, I ⊓ Ideal.span {x} = I * Ideal.span {x},
       ∀ x ∈ I, ∃ y ∈ I, x = x * y,
       ∀ s : Finset R, (s : Set R) ⊆ I → ∃ y ∈ I, ∀ x ∈ s, x = x * y,
       ∀ p : PrimeSpectrum R,
         I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊥ ∨
           I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊤,
       Module.support R I = (PrimeSpectrum.zeroLocus (I : Set R))ᶜ,
       RingHom.ker (algebraMap R
         (Localization (Submonoid.comap (Ideal.Quotient.mk I).toMonoidHom ⊥))) = I,
       ∃ S : Submonoid R, Nonempty ((R ⧸ I) ≃ₐ[R] Localization S),
       Nonempty ((R ⧸ I) ≃ₐ[R]
         Localization (Submonoid.comap (Ideal.Quotient.mk I).toMonoidHom ⊥))] :=
    by apply Stacks.IdealTheory.PureIdealTFAE.solution

end

end

@[expose] public section
set_option linter.unusedVariables false
set_option linter.style.show false


/-- An ideal `I` of a commutative ring `R` is *pure* when the quotient ring `R ⧸ I`
is flat as an `R`-module. -/
def Ideal.IsPure {R : Type*} [CommRing R] (I : Ideal R) : Prop :=
  Module.Flat R (R ⧸ I)

/-- Unfolding lemma: `I` is pure exactly when `R ⧸ I` is a flat `R`-module. -/
theorem Ideal.isPure_iff {R : Type*} [CommRing R] (I : Ideal R) :
    Ideal.IsPure I ↔ Module.Flat R (R ⧸ I) :=
  Iff.rfl

end

@[expose] public section
set_option linter.unusedVariables false
set_option linter.style.show false


/-- An ideal `I` of a commutative ring `R` is *pure* if for every `x ∈ I`
there exists `y ∈ I` with `x * y = x`. -/
def Ideal.IsPure04PT {R : Type*} [CommRing R] (I : Ideal R) : Prop :=
  ∀ x ∈ I, ∃ y ∈ I, x * y = x

/-- If `x * y = x`, then `x * yⁿ = x` for all `n`. -/
private lemma mul_pow_eq_self {R : Type*} [CommRing R] {x y : R} (h : x * y = x) :
    ∀ n : ℕ, x * y ^ n = x
  | 0 => by simp
  | n + 1 => by rw [pow_succ, ← mul_assoc, mul_pow_eq_self h n, h]

/-- If `I` is pure and `radical I ≤ radical J`, then `I ≤ J`. -/
lemma Ideal.IsPure04PT.le_of_radical_le {R : Type*} [CommRing R]
    {I J : Ideal R} (hI : Ideal.IsPure04PT I) (hrad : I.radical ≤ J.radical) :
    I ≤ J := by
  intro x hx
  obtain ⟨y, hyI, hxy⟩ := hI x hx
  obtain ⟨n, hyn⟩ := Ideal.mem_radical_iff.mp (hrad (Ideal.le_radical hyI))
  simpa [mul_pow_eq_self hxy n] using J.mul_mem_left x hyn

/-- Pure ideals are determined by their vanishing locus. -/
theorem Ideal.IsPure04PT.eq_of_zeroLocus_eq {R : Type*} [CommRing R]
    {I J : Ideal R} (hI : Ideal.IsPure04PT I) (hJ : Ideal.IsPure04PT J)
    (h : PrimeSpectrum.zeroLocus (I : Set R) = PrimeSpectrum.zeroLocus (J : Set R)) :
    I = J :=
  have hrad : I.radical = J.radical := by grind only [PrimeSpectrum.zeroLocus_eq_iff]
  le_antisymm (hI.le_of_radical_le hrad.le) (hJ.le_of_radical_le hrad.ge)

end

/-!
# Pure ideals and generalization-stable closed subsets of `Spec R`

Let `R` be a commutative ring and write `Spec R` for its prime spectrum, the set of prime
ideals of `R` with the Zariski topology.

## Definitions

* **Vanishing locus.** For an ideal `I ⊆ R`, `V(I) = { p ∈ Spec R : I ⊆ p }`. As `I` ranges
  over all ideals the sets `V(I)` are exactly the closed subsets of `Spec R`; in Mathlib this
  is `PrimeSpectrum.zeroLocus (I : Set R)`.

* **Pure ideal** (tag 04PR). An ideal `I ⊆ R` is pure when `R / I` is flat as an `R`-module,
  i.e. `Ideal.IsPure I`, definitionally `Module.Flat R (R ⧸ I)`.

* **Closed under generalizations.** A subset `Z ⊆ Spec R` is closed under generalizations
  when `p ∈ Z` and `q ⊆ p` imply `q ∈ Z`, i.e. `StableUnderGeneralization Z`. The
  specialization relation `p ⤳ q` on `PrimeSpectrum R` is inclusion of the underlying ideals
  (`PrimeSpectrum.le_iff_specializes`), so this unfolds to the stated condition on primes.

## Main results

The rule `I ↦ V(I)` is a bijection between the pure ideals of `R` and the closed subsets of
`Spec R` that are closed under generalizations. This splits into three claims:

1. for every pure ideal `I` the closed set `V(I)` is closed under generalizations;
2. for pure ideals `I, J`, `V(I) = V(J)` implies `I = J` (tag 04PT);
3. every closed, generalization-stable subset `Z` equals `V(I)` for some pure ideal `I`.
-/

@[expose] public section

open PrimeSpectrum

-- The vanishing locus `V(I)` of an ideal `I` is `PrimeSpectrum.zeroLocus (I : Set R)`.
-- Purity is `Ideal.IsPure I := Module.Flat R (R ⧸ I)` (Stacks 04PR).
-- Stability under generalization is `StableUnderGeneralization`.

/-- (Well-defined, Stacks 04PU part 1) For a pure ideal `I`, the vanishing locus
`V(I)` is closed under generalizations. (It is automatically closed, as the
vanishing locus of any ideal: see `isClosed_zeroLocus`.) -/
theorem isPure_zeroLocus_stableUnderGeneralization
    {R : Type*} [CommRing R] (I : Ideal R) (hI : I.IsPure) :
    StableUnderGeneralization (zeroLocus (I : Set R)) := by
  -- `I.IsPure` is by definition `Module.Flat R (R ⧸ I)`; register it as an instance.
  have : Module.Flat R (R ⧸ I) := hI
  -- Flatness of the quotient gives the going-down property for `R → R/I`,
  -- which is exactly the statement that `Spec(R/I) → Spec(R)` is a generalizing map.
  have hgd : Algebra.HasGoingDown R (R ⧸ I) := Algebra.HasGoingDown.of_flat
  have hgen : GeneralizingMap (comap (algebraMap R (R ⧸ I))) :=
    Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp hgd
  -- The range of a generalizing map is stable under generalization.
  have hsug := hgen.stableUnderGeneralization_range
  -- Identify the range of `comap (R → R/I)` with the vanishing locus `V(I)`.
  have hrange : Set.range (comap (algebraMap R (R ⧸ I))) = zeroLocus (I : Set R) := by
    rw [Ideal.Quotient.algebraMap_eq,
      range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  rwa [hrange] at hsug

/-! ### Keystone: Stacks 04PS, the equational criterion for purity

The whole problem turns on the equivalence between the *flatness* definition of a
pure ideal (`Ideal.IsPure I := Module.Flat R (R ⧸ I)`, Stacks 04PR) and the
*equational* characterization (Stacks 04PS, criterion (5)):

  `I.IsPure04PT  :=  ∀ x ∈ I, ∃ y ∈ I, x * y = x`.

The `StacksDraft` library already proves the two purely-algebraic consequences of
the equational criterion that we need:
* `Ideal.IsPure04PT.eq_of_zeroLocus_eq` : `I.IsPure04PT → J.IsPure04PT →
    V(I) = V(J) → I = J`   (the reconstruction / injectivity, Stacks 04PT);
* `Ideal.IsPure04PT.le_of_radical_le`  : `I.IsPure04PT → I.radical ≤ J.radical →
    I ≤ J`.

What is *missing* from the library is the bridge `Ideal.IsPure ↔ Ideal.IsPure04PT`.
We isolate the two directions as the keystone helper_04pu lemmas below; both are
instances of Mathlib's equational criterion for flatness
(`Module.Flat.iff_forall_isTrivialRelation`) specialised to `M = R ⧸ I`. -/

/-- (Stacks 04PS, flat ⇒ equational) The flatness definition of purity implies the
equational criterion: if `R ⧸ I` is flat then every `x ∈ I` satisfies `x * y = x`
for some `y ∈ I`.

INFORMAL PROOF. Let `x ∈ I`. In `M := R ⧸ I` we have `mk x = 0`, i.e. the
one-term relation `x • mk 1 = 0` holds (since `x • mk 1 = mk (x * 1) = mk x = 0`,
using `Submodule.Quotient.mk_smul` / `Ideal.Quotient.eq_zero_iff_mem`). Flatness,
via `Module.Flat.isTrivialRelation_of_sum_smul_eq_zero` applied to the single
index `Fin 1` with `f = ![x]`, `m = ![mk 1]`, yields
`Module.IsTrivialRelation ![x] ![mk 1]`: there are `k`, scalars
`a : Fin 1 → Fin k → R` and `m' : Fin k → R ⧸ I` with
`mk 1 = ∑ j, a 0 j • m' j` and `∑ i, f i * a i j = x * a 0 j = 0` for all `j`.
Lift each `m' j = mk (z j)` (`Ideal.Quotient.mk_surjective`). The first equation
says `1 - ∑ j a 0 j * z j ∈ I`; the second says `x * a 0 j = 0` in `R`. Put
`y := ∑ j a 0 j * z j`. Then `x * y = ∑ j (x * a 0 j) * z j = 0`, and
`x - x * y = x * (1 - y)`; since `1 - y ∈ I`... — more directly, set
`y := 1 - (1 - ∑ a0j zj)`. The clean bookkeeping: `1 - y ∈ I` and `x * (1 - y) = 0`
forces, with `y ∈ I` (as `y = 1 - (1-y)` and `x ∈ I` lets us absorb), `x * y = x`.
This is the standard unwinding of `IsTrivialRelation` for a single generator
(Stacks 04PS, 00HK ⇒ (5)); the witness is `y := ∑ j, a 0 j * z j ∈ I` with
`x * y = x`. -/
theorem isPure_imp_isPure04PT
    {R : Type*} [CommRing R] {I : Ideal R} (hI : I.IsPure) :
    I.IsPure04PT := by
  have : Module.Flat R (R ⧸ I) := hI
  intro x hx
  have hrel : ∑ i, ![x] i • ![Ideal.Quotient.mk I 1] i = 0 := by
    simpa [Algebra.smul_def] using Ideal.Quotient.eq_zero_iff_mem.mpr hx
  obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  choose z hz using fun j => Ideal.Quotient.mk_surjective (y j)
  have haj : ∀ j, x * a 0 j = 0 := fun j => by simpa using ha j
  refine ⟨1 - ∑ j, a 0 j * z j, ?_, ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_sum]
    simpa [← hz, Algebra.smul_def] using hy 0
  · simp [mul_sub, Finset.mul_sum, ← mul_assoc, haj]

/-- (Stacks 04PS, equational ⇒ flat) The equational criterion implies the flatness
definition of purity: if every `x ∈ I` satisfies `x * y = x` for some `y ∈ I`,
then `R ⧸ I` is flat.

INFORMAL PROOF. Use `Module.Flat.of_forall_isTrivialRelation` on `M := R ⧸ I`.
Suppose `∑ i, f i • mk (z i) = 0` in `R ⧸ I` for `f : Fin l → R`,
`z : Fin l → R`; this means `s := ∑ i f i * z i ∈ I`
(`Ideal.Quotient.eq_zero_iff_mem`, `Submodule.Quotient.mk_smul`). By the
equational criterion there is `e ∈ I` with `s * e = s`, equivalently
`s * (1 - e) = 0` with `1 - e` acting as a "local idempotent complement".
The element `1 - e` then witnesses triviality: each `mk (z i) = (1-e) • mk (z i)`
because `e • mk (z i) = mk (e * z i) = 0` would require `e * z i ∈ I`, which need
not hold for individual `i`; the correct trivialiser uses the *idempotent up to `I`*
structure. Concretely (Stacks 04PS (5) ⇒ (1), via 00HK): the single relation with
its coefficient `s ∈ I` and witness `e` (with `s e = s`, `e ∈ I`) produces the
trivial-relation data `a`, `m'` by setting `m' = mk ∘ (the z i)` rescaled by the
idempotent, giving `∑ i, f i * a i j = 0`. Hence `IsTrivialRelation f (mk ∘ z)`,
and flatness follows. (The multi-index strengthening of the criterion, 04PS (6),
follows from (5) by the elementary product trick `1 - e = ∏ (1 - eᵢ)`.) -/
theorem isPure04PT_imp_isPure
    {R : Type*} [CommRing R] {I : Ideal R} (hI : I.IsPure04PT) :
    I.IsPure := by
  -- `I.IsPure` is definitionally `Module.Flat R (R ⧸ I)`.
  change Module.Flat R (R ⧸ I)
  -- `I.IsPure04PT` is definitionally `∀ x ∈ I, ∃ y ∈ I, x * y = x`.
  rw [Module.Flat.iff_forall_isTrivialRelation]
  intro l f x hrel
  -- `a • mk b = mk a * mk b = mk (a * b)`.
  have hsmul : ∀ (a b : R), a • (Ideal.Quotient.mk I b)
      = (Ideal.Quotient.mk I a) * (Ideal.Quotient.mk I b) := fun a b => by
    simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  -- Lift each module element `x i` to a representative `z i ∈ R`.
  choose z hz using fun i => Ideal.Quotient.mk_surjective (x i)
  -- The relation `∑ f i • x i = 0` says `s := ∑ f i * z i ∈ I`.
  set s : R := ∑ i, f i * z i with hs
  have hsI : s ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hs, map_sum, ← hrel]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, ← hsmul, hz i]
  -- Equational criterion: `e ∈ I` with `s * e = s`, so `(1 - e) * s = 0`.
  obtain ⟨e, heI, hse⟩ := hI s hsI
  have hez : Ideal.Quotient.mk I e = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr heI
  -- One generator `mk 1`; coefficients `(1 - e) * z i`.  Since `e ∈ I`,
  -- `mk ((1 - e) * z i) = mk (z i) = x i`, and `∑ f i * (1 - e) * z i = (1 - e) * s = 0`.
  refine ⟨1, fun i _ => (1 - e) * z i, fun _ => Ideal.Quotient.mk I 1, ?_, ?_⟩
  · intro i
    rw [Fin.sum_univ_one, hsmul, map_one, mul_one, map_mul, map_sub, map_one, hez,
      sub_zero, one_mul, hz i]
  · intro j
    change ∑ i, f i * ((1 - e) * z i) = 0
    rw [show ∑ i, f i * ((1 - e) * z i) = (1 - e) * s by
      rw [hs, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
      sub_mul, one_mul, mul_comm e s, hse, sub_self]

/-- (Injective, Stacks 04PT) A pure ideal is determined by its vanishing locus:
if `I` and `J` are pure ideals with `V(I) = V(J)`, then `I = J`.

INFORMAL PROOF. Convert both purity hypotheses to the equational criterion via
`isPure_imp_isPure04PT` (Stacks 04PS), then apply the library reconstruction lemma
`Ideal.IsPure04PT.eq_of_zeroLocus_eq`, which says that ideals satisfying the
equational criterion are recovered from their vanishing locus. -/
theorem isPure_injective_zeroLocus
    {R : Type*} [CommRing R] {I J : Ideal R} (hI : I.IsPure) (hJ : J.IsPure)
    (h : zeroLocus (I : Set R) = zeroLocus (J : Set R)) : I = J :=
  -- This is a one-liner once the 04PS bridge `isPure_imp_isPure04PT` is in place.
  Ideal.IsPure04PT.eq_of_zeroLocus_eq (isPure_imp_isPure04PT hI)
    (isPure_imp_isPure04PT hJ) h

/-- The candidate ideal for the surjectivity construction. Given a radical ideal
`J = vanishingIdeal Z`, set `purifyIdeal J := { x | ∃ f ∈ J, x * f = x }`, i.e. the
set of `x` that are "fixed" by some element of `J`. This is the ideal `I` of
Stacks 04PU with `V(I) = V(J)` and `I` pure. -/
def purifyIdeal {R : Type*} [CommRing R] (J : Ideal R) : Ideal R where
  carrier := { x : R | ∃ f ∈ J, x * f = x }
  zero_mem' := ⟨0, J.zero_mem, by ring⟩
  add_mem' := by
    -- For `x = x*f`, `y = y*g` (f,g ∈ J), the common fixer is `h = f + g - f*g ∈ J`,
    -- since `1 - h = (1-f)(1-g)`; then `(x+y)*h = x+y`.
    rintro a b ⟨f, hf, haf⟩ ⟨g, hg, hbg⟩
    refine ⟨f + g - f * g, ?_, ?_⟩
    · rw [show f + g - f * g = f + (1 - f) * g by ring]
      exact J.add_mem hf (J.mul_mem_left _ hg)
    · linear_combination (1 - g) * haf + (1 - f) * hbg
  smul_mem' := by
    -- If `x = x*f` (f ∈ J), then `(r*x)*f = r*(x*f) = r*x`, same fixer.
    rintro r a ⟨f, hf, haf⟩
    exact ⟨f, hf, by rw [smul_eq_mul]; linear_combination r * haf⟩

/-- `purifyIdeal J ⊆ J`: if `x * f = x` with `f ∈ J`, then `x = x * f ∈ J`. -/
theorem purifyIdeal_le {R : Type*} [CommRing R] (J : Ideal R) :
    purifyIdeal J ≤ J := by
  rintro x ⟨f, hf, hxf⟩
  -- `x = x * f` and `x * f ∈ J` (since `f ∈ J`), so `x ∈ J`.
  exact hxf ▸ J.mul_mem_left _ hf

/-- (B) KEYSTONE. For a *radical* ideal `J` whose vanishing locus `V(J)` is stable
under generalization, the hard radical inclusion `J ≤ radical (purifyIdeal J)`.

Combined with `purifyIdeal_le` (which gives `(purifyIdeal J).radical ≤ J.radical = J`),
this yields `(purifyIdeal J).radical = J`, the engine of Stacks 04PU surjectivity.

INFORMAL PROOF. `radical (purifyIdeal J) = sInf {p | purifyIdeal J ≤ p ∧ p prime}`
(`Ideal.radical_eq_sInf`). So it suffices to show `J ≤ p` for every prime
`p ⊇ purifyIdeal J`, i.e. every `p ∈ zeroLocus (purifyIdeal J)`. Fix such `p`.
KEY GEOMETRIC STEP (where gen-stability enters): `p` is a generalization of some
point of `Z = V(J)`. Concretely, `purifyIdeal J ≤ J` gives
`zeroLocus J ⊆ zeroLocus (purifyIdeal J)`, and one shows every prime over
`purifyIdeal J` *specializes from* (is a generalization of) a prime over `J`: the
elements of `purifyIdeal J` are exactly those of `J` that are "units near `Z`", so
on the locus `V(purifyIdeal J)` the extra primes are precisely the generalizations
of `V(J)`. Since `Z = V(J)` is generalization-stable (`hgen` via `hZJ`), these
generalizations lie back in `Z`, forcing `p ∈ V(J)`, i.e. `J ≤ p`. Hence
`J ≤ sInf {…} = radical (purifyIdeal J)`.
LEAN ROUTE: `Ideal.radical_eq_sInf`, `Ideal.mem_sInf`/`Submodule.mem_sInf`;
relate `p ∈ zeroLocus (purifyIdeal J)` to `Z` via `hZJ : zeroLocus J = Z` and
`StableUnderGeneralization` of `Z` (`le_iff_specializes`). The specialization link
`V(purifyIdeal J) ⊆ generalizations of V(J)` is the crux to formalize. -/
theorem purifyIdeal_radical_ge {R : Type*} [CommRing R] (J : Ideal R)
    (hgen : StableUnderGeneralization (zeroLocus (J : Set R))) :
    J ≤ (purifyIdeal J).radical := by
  rw [Ideal.radical_eq_sInf]
  intro a haJ
  rw [Submodule.mem_sInf]
  rintro p ⟨hple, hpprime⟩
  have : Ideal.IsPrime p := hpprime
  -- The submonoid `T = 1 + J = {x | x - 1 ∈ J}`.
  let T : Submonoid R := {
    carrier := { x : R | x - 1 ∈ J }
    one_mem' := by simp
    mul_mem' := by
      intro a b ha hb
      simp only [Set.mem_ofPred_eq] at *
      rw [show a * b - 1 = a * (b - 1) + (a - 1) by ring]
      exact J.add_mem (J.mul_mem_left _ hb) ha }
  -- `S = (R ∖ p) * (1 + J)`.
  let S : Submonoid R := Ideal.primeCompl p ⊔ T
  -- `0 ∉ S`: if `u * z = 0` with `u ∉ p`, `z - 1 ∈ J`, then `u = u * (-(z-1))`
  -- so `u ∈ purifyIdeal J ⊆ p`, contradiction.
  have h0 : (0 : R) ∉ S := by
    rw [Submonoid.mem_sup]
    rintro ⟨u, hu, z, hz, hprod⟩
    exact hu (hple ⟨-(z - 1), J.neg_mem hz, by linear_combination -hprod⟩)
  have hdisj : Disjoint ((⊥ : Ideal R) : Set R) (S : Set R) := by
    simpa [Set.disjoint_left] using h0
  -- A prime `q` disjoint from `S`.
  obtain ⟨q, hqprime, hqle, hqdisj⟩ := Ideal.exists_le_prime_disjoint (⊥ : Ideal R) S hdisj
  have : Ideal.IsPrime q := hqprime
  rw [Set.disjoint_left] at hqdisj
  -- `q ≤ p` since `q` is disjoint from `R ∖ p`.
  have hqsubp : q ≤ p := fun _ hx ↦
    Classical.byContradiction fun hxp ↦ hqdisj hx (Submonoid.mem_sup_left hxp)
  -- `q + J ≠ ⊤`: else `1 = c + j`, `c ∈ q`, `j ∈ J`, so `c ∈ q ∩ T`, contradiction.
  have hproper : q + J ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one]
    intro h1
    rw [Ideal.add_eq_sup, Submodule.mem_sup] at h1
    obtain ⟨c, hc, j, hj, hcj⟩ := h1
    have hcT : c ∈ T := by
      change c - 1 ∈ J
      rw [show c - 1 = -j by linear_combination hcj]
      exact J.neg_mem hj
    exact hqdisj hc (Submonoid.mem_sup_right hcT)
  -- A maximal (hence prime) ideal `m ⊇ q + J`.
  obtain ⟨m, hmmax, hmle⟩ := Ideal.exists_le_maximal (q + J) hproper
  rw [Ideal.add_eq_sup, sup_le_iff] at hmle
  -- `q ⤳ m` since `q ≤ m`.
  have hspec : (⟨q, hqprime⟩ : PrimeSpectrum R) ⤳ (⟨m, hmmax.isPrime⟩ : PrimeSpectrum R) :=
    (PrimeSpectrum.le_iff_specializes _ _).mp hmle.1
  -- Generalization-stability of `V(J)` forces `q ∈ V(J)`, i.e. `J ≤ q ≤ p`.
  exact hqsubp (hgen hspec hmle.2 haJ)

/-- (C) CONDITIONAL equational criterion. If `J ≤ radical (purifyIdeal J)` then
`purifyIdeal J` satisfies the equational criterion (Stacks 04PS (5)). This replaces
the FALSE unconditional `purifyIdeal_isPure04PT` (counterexample R=ℤ[X,F]/(XF−X),
J=(F)) — purity of the purified ideal genuinely needs the radical hypothesis.

INFORMAL PROOF. Let `x ∈ purifyIdeal J`, so `∃ f ∈ J, x * f = x`. By induction
`x * f ^ n = x` for all `n ≥ 1` (`x f^{n+1} = (x f) f^n = x f^n`). Since
`f ∈ J ≤ radical (purifyIdeal J)`, `Ideal.mem_radical_iff` gives `n` with
`f ^ n ∈ purifyIdeal J`. Take `y := f ^ (max n 1)` (guard `n ≥ 1` so the induction
applies and the exponent is positive): `y ∈ purifyIdeal J` (ideal, and `f^n ∈` it
implies `f^{max n 1} = f^n · f^{...} ∈` it, or handle `n=0` via `x·1=x`) and
`x * y = x * f ^ (max n 1) = x`. -/
theorem purifyIdeal_isPure04PT_of_radical_le {R : Type*} [CommRing R] (J : Ideal R)
    (hle : J ≤ (purifyIdeal J).radical) :
    (purifyIdeal J).IsPure04PT := by
  intro x hx
  obtain ⟨f, hf, hxf⟩ := hx
  -- `f ∈ J ≤ radical (purifyIdeal J)`, so some power `f ^ n ∈ purifyIdeal J`.
  have hfrad : f ∈ (purifyIdeal J).radical := hle hf
  rw [Ideal.mem_radical_iff] at hfrad
  obtain ⟨n, hfn⟩ := hfrad
  -- Witness `y := f ^ (max n 1)`.
  refine ⟨f ^ (max n 1), ?_, ?_⟩
  · -- `f ^ (max n 1) = f ^ n * f ^ (max n 1 - n) ∈ purifyIdeal J`.
    rw [← Nat.add_sub_cancel' (le_max_left n 1), pow_add]
    exact (purifyIdeal J).mul_mem_right _ hfn
  · exact mul_pow_eq_self hxf _

/-- (D) For a radical ideal `J = vanishingIdeal Z` whose vanishing locus `Z` is
stable under generalization, the purified ideal has the same vanishing locus as `J`.
Now a COROLLARY of (B): `(purifyIdeal J).radical = J`, so the zeroLoci agree.

INFORMAL PROOF. Let `J := vanishingIdeal Z` (radical). From (B)
`purifyIdeal_radical_ge` we get `J ≤ radical (purifyIdeal J)`; from `purifyIdeal_le`
+ monotonicity of radical + `J` radical we get `radical (purifyIdeal J) ≤ J`. Hence
`radical (purifyIdeal J) = J`, so
`zeroLocus (purifyIdeal J) = zeroLocus (radical (purifyIdeal J)) = zeroLocus J = Z`
(`PrimeSpectrum.zeroLocus_radical`, `hZJ`). -/
theorem purifyIdeal_zeroLocus_eq {R : Type*} [CommRing R] (Z : Set (PrimeSpectrum R))
    (hgen : StableUnderGeneralization Z)
    (hZJ : zeroLocus ((vanishingIdeal Z : Ideal R) : Set R) = Z) :
    zeroLocus ((purifyIdeal (vanishingIdeal Z) : Ideal R) : Set R) = Z := by
  set J : Ideal R := vanishingIdeal Z
  have hJrad : J.IsRadical := isRadical_vanishingIdeal Z
  -- (B): the hard inclusion.
  have hge : J ≤ (purifyIdeal J).radical := purifyIdeal_radical_ge J (hZJ ▸ hgen)
  -- easy inclusion: radical (purifyIdeal J) ≤ radical J = J.
  have hle : (purifyIdeal J).radical ≤ J :=
    (Ideal.radical_mono (purifyIdeal_le J)).trans_eq hJrad.radical
  -- conclude on zeroLoci.
  rw [← zeroLocus_radical, le_antisymm hle hge, hZJ]

/-- (Surjective, Stacks 04PU part 3) Every closed subset of `Spec(R)` that is
closed under generalizations is the vanishing locus of some pure ideal.

INFORMAL PROOF (Stacks 04PU surjectivity), refactored dependency-correct.
1. `Z = V(J)` with `J := vanishingIdeal Z` radical (`zeroLocus_vanishingIdeal_eq_closure`).
2. `I := purifyIdeal J`. From (B) `purifyIdeal_radical_ge`, `J ≤ radical I`.
3. `I.IsPure04PT` from (C) `purifyIdeal_isPure04PT_of_radical_le` applied to step 2;
   hence `I.IsPure` by `isPure04PT_imp_isPure` (PROVEN).
4. `V(I) = Z` by (D) `purifyIdeal_zeroLocus_eq`. -/
theorem exists_isPure_zeroLocus_eq
    {R : Type*} [CommRing R] (Z : Set (PrimeSpectrum R))
    (hclosed : IsClosed Z) (hgen : StableUnderGeneralization Z) :
    ∃ I : Ideal R, I.IsPure ∧ zeroLocus (I : Set R) = Z := by
  -- Step 1: realise `Z` as the vanishing locus of its (radical) vanishing ideal.
  have hZJ : zeroLocus ((vanishingIdeal Z : Ideal R) : Set R) = Z := by
    rw [zeroLocus_vanishingIdeal_eq_closure, hclosed.closure_eq]
  -- Step 2: the keystone radical inclusion (B).
  have hge := purifyIdeal_radical_ge _ (hZJ ▸ hgen)
  -- Step 3 (pure, via (C) + 04PS bridge) and Step 4 (vanishing locus, via (D)).
  exact ⟨_, isPure04PT_imp_isPure (purifyIdeal_isPure04PT_of_radical_le _ hge),
    purifyIdeal_zeroLocus_eq Z hgen hZJ⟩

/-- (Stacks 04PU) The map `I ↦ V(I)` is a bijection between the set of pure
ideals of `R` and the set of closed subsets of `Spec(R)` that are closed under
generalizations. This packages the three claims above as a single `Set.BijOn`
statement. -/
@[stacks 04PU]
theorem bijOn_zeroLocus_isPure {R : Type*} [CommRing R] :
    Set.BijOn (fun I : Ideal R => zeroLocus (I : Set R))
      {I : Ideal R | I.IsPure}
      {Z : Set (PrimeSpectrum R) | IsClosed Z ∧ StableUnderGeneralization Z} := by
  refine ⟨?_, ?_, ?_⟩
  · -- `MapsTo`: the vanishing locus of a pure ideal is closed (automatic) and
    -- stable under generalization (part 1).
    intro I hI
    exact ⟨isClosed_zeroLocus _, isPure_zeroLocus_stableUnderGeneralization I hI⟩
  · -- `InjOn`: injectivity on pure ideals (part 2).
    intro I hI J hJ h
    exact isPure_injective_zeroLocus hI hJ h
  · -- `SurjOn`: surjectivity onto closed generalization-stable subsets (part 3).
    exact fun Z hZ => exists_isPure_zeroLocus_eq Z hZ.1 hZ.2

end

/-!
# Characterizations of pure finitely generated ideals

Let `R` be a commutative ring with unit and `I ⊆ R` an ideal. The four conditions

1. `I` is pure (`Ideal.IsPure I`, i.e. `R ⧸ I` is flat over `R`; tag 04PR) and finitely
   generated (`Ideal.FG I`);
2. `I` is generated by an idempotent: there is `e ∈ R` with `e ^ 2 = e` and
   `I = Ideal.span {e}`;
3. `I` is pure and the vanishing locus `V(I) = PrimeSpectrum.zeroLocus (I : Set R)` is open
   in `Spec R` for the Zariski topology;
4. `R ⧸ I` is a projective `R`-module (`Module.Projective R (R ⧸ I)`)

are all equivalent. The result is stated as a `List.TFAE`, which records the mutual
equivalence of all four at once.
-/

@[expose] public section

/-- The quotient of `R` by the ideal generated by an idempotent is projective. -/
private lemma projective_quotient_span_of_sq_eq_self {R : Type*} [CommRing R] {e : R}
    (he : e ^ 2 = e) : Module.Projective R (R ⧸ Ideal.span {e}) := by
  have hee : e * e = e := by rw [← pow_two]; exact he
  -- multiplication by `(1 - e)` as an `R`-linear map `R →ₗ[R] R`
  set f : R →ₗ[R] R := LinearMap.toSpanSingleton R R (1 - e) with hf
  have hfx : ∀ x : R, f x = x * (1 - e) := by
    intro x; simp [hf, LinearMap.toSpanSingleton_apply, smul_eq_mul]
  -- `span {e}` is contained in the kernel of `f`
  have hker : Ideal.span {e} ≤ LinearMap.ker f := by
    rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hfx]
    have : x * (1 - x) = x - x * x := by ring
    rw [this, hee]; ring
  -- the section map `[x] ↦ (1-e)*x`, with retraction `mkQ`
  refine Module.Projective.of_split (Submodule.liftQ (Ideal.span {e}) f hker)
    (Ideal.span {e}).mkQ ?_
  refine LinearMap.ext fun z => ?_
  obtain ⟨y, rfl⟩ := (Ideal.span {e}).mkQ_surjective z
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq,
    Submodule.liftQ_apply, Submodule.mkQ_apply]
  rw [hfx, ← sub_eq_zero, ← Submodule.Quotient.mk_sub]
  rw [Submodule.Quotient.mk_eq_zero]
  rw [Ideal.mem_span_singleton]
  refine ⟨-y, ?_⟩
  ring

/-- For an ideal `I` of a commutative ring `R`, the following are equivalent: `I` is pure and
finitely generated; `I` is generated by an idempotent; `I` is pure with open vanishing locus;
`R ⧸ I` is a projective `R`-module. -/
@[stacks 05KK]
theorem pure_fg_tfae (R : Type*) [CommRing R] (I : Ideal R) :
    [ -- (1) `I` is pure and finitely generated
      I.IsPure ∧ I.FG,
      -- (2) `I` is generated by an idempotent
      ∃ e : R, e ^ 2 = e ∧ I = Ideal.span {e},
      -- (3) `I` is pure and `V(I)` is open in `Spec(R)`
      I.IsPure ∧ IsOpen (PrimeSpectrum.zeroLocus (I : Set R)),
      -- (4) `R/I` is a projective `R`-module
      Module.Projective R (R ⧸ I) ].TFAE := by
  tfae_have 1 → 2 := by
    -- (1) ⇒ (2): `I` pure and f.g.
    -- Purity means `R ⧸ I` is flat. For a pure ideal one has `I = I²`, i.e. `I`
    -- is an idempotent ideal (`IsIdempotentElem I`). [analytic kernel: purity ⇒
    -- idempotent ideal.] Being also f.g., `Ideal.isIdempotentElem_iff_of_fg`
    -- (Stacks 00EH) produces an idempotent element `e` with
    -- `I = R ∙ e = Ideal.span {e}`.
    rintro ⟨hpure, hfg⟩
    -- Purity: `R ⧸ I` is flat.
    have hflat : Module.Flat R (R ⧸ I) := hpure
    -- Key step: purity ⇒ `I` is idempotent (`I * I = I`).
    have hidem : I * I = I := by
      -- `(R ⧸ I) ⊗ ↥I` is trivial: the map `lTensor (R/I) (I → R)` is injective
      -- (flatness) and zero (its composite with `rid : (R/I) ⊗ R ≅ R/I` vanishes,
      -- since `i • r̄ = 0` for `i ∈ I`).
      have hss : Subsingleton (TensorProduct R (R ⧸ I) ↥I) := by
        have hinj : Function.Injective (LinearMap.lTensor (R ⧸ I) (Submodule.subtype I)) :=
          Module.Flat.lTensor_preserves_injective_linearMap (M := R ⧸ I)
            (Submodule.subtype I) Subtype.coe_injective
        set rid := TensorProduct.rid R (R ⧸ I) with hrid
        have hzero :
            (rid.toLinearMap ∘ₗ LinearMap.lTensor (R ⧸ I) (Submodule.subtype I)) = 0 := by
          apply TensorProduct.ext'
          intro m i
          simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul,
            Submodule.coe_subtype, LinearEquiv.coe_coe, LinearMap.zero_apply, hrid,
            TensorProduct.rid_tmul]
          induction m using Submodule.Quotient.induction_on with
          | H r =>
            rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
            exact Ideal.mul_mem_right r I i.property
        have hf0 : LinearMap.lTensor (R ⧸ I) (Submodule.subtype I) = 0 := by
          refine LinearMap.ext fun x => ?_
          have hx : rid (LinearMap.lTensor (R ⧸ I) (Submodule.subtype I) x) = rid 0 := by
            rw [map_zero]
            exact congrFun (congrArg DFunLike.coe hzero) x
          rw [LinearMap.zero_apply]
          exact rid.injective hx
        refine ⟨fun a b => ?_⟩
        apply hinj
        rw [hf0]; simp
      -- transfer triviality across `(R/I) ⊗ ↥I ≅ ↥I ⧸ (I • ⊤)`
      have hq : Subsingleton (↥I ⧸ (I • (⊤ : Submodule R ↥I))) :=
        (TensorProduct.quotTensorEquivQuotSMul (↥I) I).symm.toEquiv.subsingleton
      have htop : (I • (⊤ : Submodule R ↥I)) = ⊤ :=
        Submodule.Quotient.subsingleton_iff.mp hq
      -- push forward by `I.subtype`: `I • I = I`
      have hmap := congrArg (Submodule.map I.subtype) htop
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at hmap
      rwa [Ideal.smul_eq_mul] at hmap
    -- `I` is idempotent as an element of the monoid of ideals, and f.g.
    have hidemElem : IsIdempotentElem I := hidem
    obtain ⟨e, he, hIe⟩ := (Ideal.isIdempotentElem_iff_of_fg I hfg).mp hidemElem
    -- `e` is an idempotent element with `I = R ∙ e = span {e}`.
    refine ⟨e, ?_, ?_⟩
    · rw [pow_two]; exact he
    · rw [hIe, Ideal.submodule_span_eq]
  tfae_have 2 → 4 := by
    -- (2) ⇒ (4): given `e² = e` with `I = (e)`, `R ⧸ I ≅ (1-e)·R` is a direct
    -- summand of `R` (since `R ≅ eR ⊕ (1-e)R`), hence a projective `R`-module.
    rintro ⟨e, he, rfl⟩
    exact projective_quotient_span_of_sq_eq_self he
  tfae_have 4 → 1 := by
    -- (4) ⇒ (1): `R ⧸ I` projective ⇒ flat (`Module.Flat.of_projective`), which
    -- is exactly `I.IsPure`. Projective + finite ⇒ finitely presented
    -- (`Module.finitePresentation_of_projective`); then the surjection
    -- `Submodule.mkQ I : R →ₗ R ⧸ I` has f.g. kernel
    -- (`Module.FinitePresentation.fg_ker`), and `Submodule.ker_mkQ` identifies
    -- that kernel with `I`, giving `I.FG`.
    intro hproj
    have : Module.Projective R (R ⧸ I) := hproj
    refine ⟨?_, ?_⟩
    · change Module.Flat R (R ⧸ I)
      exact Module.Flat.of_projective
    · have : Module.Finite R (R ⧸ I) :=
        Module.Finite.of_surjective (Submodule.mkQ I) (Submodule.mkQ_surjective I)
      have : Module.FinitePresentation R (R ⧸ I) :=
        Module.finitePresentation_of_projective R (R ⧸ I)
      have hfg : (Submodule.mkQ I).ker.FG :=
        Module.FinitePresentation.fg_ker (Submodule.mkQ I) (Submodule.mkQ_surjective I)
      rwa [Submodule.ker_mkQ] at hfg
  tfae_have 2 → 3 := by
    -- (2) ⇒ (3): `I = (e)`, `e² = e`. Purity: `R ⧸ I ≅ (1-e)R` is flat (direct
    -- summand of `R`), so `I.IsPure`. Openness: by
    -- `PrimeSpectrum.zeroLocus_eq_basicOpen_of_isIdempotentElem` (00EC),
    -- `V(I) = V({e}) = basicOpen (1-e)`, which is open.
    rintro ⟨e, he, rfl⟩
    have hee : e * e = e := by rw [← pow_two]; exact he
    refine ⟨?_, ?_⟩
    · -- Purity: `R ⧸ span{e}` is projective (replicate S2), hence flat.
      change Module.Flat R (R ⧸ Ideal.span {e})
      have := projective_quotient_span_of_sq_eq_self he
      exact Module.Flat.of_projective
    · -- Openness: `V(span{e}) = V({e}) = basicOpen (1-e)`, which is open.
      rw [PrimeSpectrum.zeroLocus_span,
        PrimeSpectrum.zeroLocus_eq_basicOpen_of_isIdempotentElem e hee]
      exact PrimeSpectrum.isOpen_basicOpen
  tfae_have 3 → 2 := by
    -- (3) ⇒ (2): `V(I)` is closed (always) and open, hence clopen. Via
    -- `PrimeSpectrum.isIdempotentElemEquivClopens` (00EE) the clopen `V(I)`
    -- corresponds to an idempotent `e` with `V(I) = V((e))` (and `e` chosen so
    -- `V((e)) = zeroLocus {e}`). Purity of `I` then forces `I = (e)` (two ideals
    -- with the same radical/zero-locus, one pure and idempotent, coincide).
    intro h
    obtain ⟨hpure, hopen⟩ := h
    -- `V(I)` is clopen, so its complement corresponds to an idempotent `e` (Stacks 00EE).
    have hcl : IsClosed (PrimeSpectrum.zeroLocus (I : Set R)) := PrimeSpectrum.isClosed_zeroLocus _
    have hclopen : IsClopen ((PrimeSpectrum.zeroLocus (I : Set R))ᶜ) :=
      isClopen_compl_iff.mpr ⟨hcl, hopen⟩
    set C : TopologicalSpace.Clopens (PrimeSpectrum R) :=
      ⟨(PrimeSpectrum.zeroLocus (I : Set R))ᶜ, hclopen⟩ with hC
    set ee := PrimeSpectrum.isIdempotentElemEquivClopens.symm C with hee
    set e : R := ee.val with hedef
    have heidem : IsIdempotentElem e := ee.property
    -- The chosen `e` satisfies `V({e}) = V(I)`.
    have hZL : PrimeSpectrum.zeroLocus ({e} : Set R) = PrimeSpectrum.zeroLocus (I : Set R) := by
      have key : (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R))
          = (PrimeSpectrum.zeroLocus (I : Set R))ᶜ := by
        have hb : (PrimeSpectrum.isIdempotentElemEquivClopens ee : Set (PrimeSpectrum R))
            = (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) := rfl
        rw [← hb, hee, OrderIso.apply_symm_apply]; rfl
      rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl] at key
      simpa using compl_injective key
    -- Same zero locus ⟹ equal radicals.
    have hrad1 : Ideal.span ({e} : Set R) ≤ I.radical := by
      have hsub : PrimeSpectrum.zeroLocus (I : Set R)
          ⊆ PrimeSpectrum.zeroLocus (Ideal.span ({e} : Set R) : Set R) := by
        rw [PrimeSpectrum.zeroLocus_span, hZL]
      exact (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp hsub
    have hrad2 : I ≤ (Ideal.span ({e} : Set R)).radical := by
      have hsub : PrimeSpectrum.zeroLocus (Ideal.span ({e} : Set R) : Set R)
          ⊆ PrimeSpectrum.zeroLocus (I : Set R) := by
        rw [PrimeSpectrum.zeroLocus_span, hZL]
      exact (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp hsub
    refine ⟨e, by rw [pow_two]; exact heidem, ?_⟩
    -- `e ∈ I`: `e ∈ rad I` and `e` idempotent give `e ∈ I`.
    have heI : e ∈ I := by
      have he_rad : e ∈ I.radical := hrad1 (Ideal.mem_span_singleton_self e)
      obtain ⟨n, hn⟩ := he_rad
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        simp only [pow_zero] at hn
        exact (Ideal.eq_top_iff_one I).mpr hn ▸ Submodule.mem_top
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
        rwa [IsIdempotentElem.pow_succ_eq m heidem] at hn
    apply le_antisymm
    · -- `I ≤ span {e}`: for `x ∈ I`, `x = a*x` with `a ∈ I ⊆ rad(span{e})`, so
      -- `x = aᵐ*x ∈ span{e}`.
      intro x hx
      obtain ⟨a, haI, hxa⟩ := isPure_imp_isPure04PT hpure x hx
      obtain ⟨m, hm⟩ := hrad2 haI
      rw [← mul_pow_eq_self hxa m]
      exact Ideal.mul_mem_left _ x hm
    · rw [Ideal.span_le, Set.singleton_subset_iff]; exact heI
  tfae_finish

end
