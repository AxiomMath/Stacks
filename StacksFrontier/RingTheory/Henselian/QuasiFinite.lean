module

import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Group.Pi.Units

public import StacksFrontier.RingTheory.Henselian.FiniteType.Basic
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v w x

/-!
# Finite and quasi-finite algebras over a henselian local ring

Let `(R, 𝔪, κ)` be a henselian local ring. This file proves Lemma 04GH: a finite `R`-algebra is a
finite product of henselian local rings each finite over `R`; a finite `R`-algebra which is local
is henselian, with `R → S` a local homomorphism; and for `S` of finite type over `R` and `q` a
prime of `S` over `𝔪` at which `R → S` is quasi-finite, the local ring `S_q` is henselian and
finite over `R`.

The source deduces all four items from Lemma 04GG, whose items (10) and (11) say that a finite
`R`-algebra is a finite product of local rings and that a finite type `R`-algebra splits as
`A × B` with `A` finite over `R` and `B` nowhere quasi-finite over `R` above `𝔪`. Both of
those items are available as Stacks 04GJ (`exists_algEquiv_pi_isLocalRing` and
`exists_prod_finite_not_quasiFiniteAt`);
`exists_pi_isLocalRing_of_finite` and `exists_prod_finite_not_quasiFiniteAt'` only restate them in
the spelling 04GG uses, the index type of the product being moved into `Type u` along `ULift`.

## Main results

* `Stacks.Henselian.QuasiFiniteAlgebras.solution`: the statement of the lemma.

## Implementation notes

Item (2) is the substance, and it is the implication 04GG (10) ⟹ (1), the one direction 04GJ does
not supply; `henselianLocalRing_of_finite` proves it in the case at hand. Let `f ∈ S[X]` be monic
with a simple root `a₀` modulo `𝔪_S`. The `S`-algebra `A = S[X]/(f)` is free over `S` and hence
finite over `R`, so 04GG (10) for `R` writes `A` as a finite product of local rings; the map
`A → κ_S` sending the root `x` to `a₀` kills `x - a₀`, so `x - a₀` is not a unit of `A` and
therefore is a non-unit in one of the factors `C`. That factor is both a quotient of `A` and a
direct `S`-summand of it, hence finite and projective over `S`, and it is generated over `S` by the
image `ξ` of `x`; expanding `0 = f(ξ)` around `a₀` with `Polynomial.binomExpansion` and using that
`f'(a₀)` is a unit puts `ξ - a₀` in `𝔪_S · C`, so `C = S + 𝔪_S · C` and `S → C` is onto by
Nakayama. It is then injective: projectivity splits the surjection `S ↠ C`, and the resulting
idempotent of the local ring `S` cannot be `0` because `C` is nonzero, so it is `1`. The preimage of
`ξ` is the required root. Item (1) follows from item (2): 04GG (10) produces a
ring isomorphism `S ≃+* ∀ i, A i` onto a finite product of local rings, and transporting the
`R`-algebra structure along the projections `S → A i` upgrades it to an `R`-algebra isomorphism and
makes each factor a quotient of `S`, hence finite over `R`.

Item (3) rests on `isLocalization_comap_of_surjective`: if `f : S → T` is surjective and some `c`
whose image avoids a prime `p` of `T` annihilates `ker f`, then a localization of `T` at `p` is a
localization of `S` at the contraction of `p` — the kernel dies once `c` is inverted, so the two
localizations agree. Both places where the source localizes are instances of it. Writing
`S = A × B` as in 04GG (11), the surjection `S → A`, with `c` the idempotent cutting out `A`,
identifies `S_q` with a localization of `A` at a prime over `𝔪`; and for a decomposition of the
*finite* algebra `A` as in 04GG (10), the projection onto the factor whose idempotent avoids that
prime, with `c` that idempotent, identifies the localization of `A` with the factor itself
(`surjective_algebraMap_of_liesOver`). So `S_q` is a quotient of `A`, which is what makes it finite
over `R`. The prime of `A` in play is maximal because `A` is integral over the local ring `R`; the
case where `q` comes from `B` is excluded because quasi-finiteness at `q` descends along the
surjection `S → B`.

Both surjections need that the image prime again lies over `𝔪` and that `q` is its contraction;
`map_isPrime_liesOver_comap` supplies both from the annihilator, and is the one place where the
argument for the two factors is carried out. Its `LiesOver` half is the converse of Mathlib's
`Ideal.LiesOver.of_eq_comap`, which transfers `LiesOver` from a prime to its contraction rather
than back; it is proved here by the same computation.

Item (4) is item (3) at every prime over `𝔪`, quasi-finiteness at `q` being inherited from
quasi-finiteness of `S` by `Algebra.QuasiFinite.of_isLocalization`.

## References

* [StacksProject 04GH](https://stacks.math.columbia.edu/tag/04GH)
-/

namespace Stacks.Henselian.QuasiFiniteAlgebras



open IsLocalRing

/-- Multiplication by an element pulled back along a ring equivalence, computed in the target. -/
private lemma symm_mul {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T) (a : T) (x : S) :
    e.symm a * x = e.symm (a * e x) := by
  rw [map_mul, e.symm_apply_apply]

/-- An element pulled back along a ring equivalence annihilates `x` as soon as it does so in the
target. -/
private lemma symm_mul_eq_zero {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T) {a : T}
    {x : S} (h : a * e x = 0) : e.symm a * x = 0 := by
  rw [symm_mul, h, map_zero]

/-- If some `c ∉ q` annihilates the kernel of `f`, that kernel is contained in `q`. -/
private lemma ker_le_of_annihilator_notMem {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T)
    (q : Ideal S) [q.IsPrime] {c : S} (hc : c ∉ q) (hann : ∀ x : S, f x = 0 → c * x = 0) :
    RingHom.ker f ≤ q := by
  intro x hx
  refine (‹q.IsPrime›.mem_or_mem ?_).resolve_left hc
  rw [hann x hx]
  exact q.zero_mem

/-- Converse of `Ideal.LiesOver.of_eq_comap`: if `q = g⁻¹(P)` for an `R`-algebra map `g` and `q`
lies over `𝔭`, then so does `P`. -/
private lemma liesOver_of_eq_comap {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (g : S →ₐ[R] T) {q : Ideal S} {P : Ideal T}
    (hpq : q = Ideal.comap g.toRingHom P) (𝔭 : Ideal R) [q.LiesOver 𝔭] : P.LiesOver 𝔭 := by
  have h : algebraMap R T = g.toRingHom.comp (algebraMap R S) :=
    RingHom.ext fun r => (g.commutes r).symm
  refine ⟨?_⟩
  rw [Ideal.under_def, h, ← Ideal.comap_comap, ← hpq, ← Ideal.under_def]
  exact Ideal.over_def q 𝔭

/-- Along a surjection `g : S →ₐ[R] T` whose kernel is annihilated by some `c ∉ q`, the image
`q.map g` of a prime `q` of `S` lying over `𝔭` is again a prime lying over `𝔭`, and `q` is its
contraction. -/
private lemma map_isPrime_liesOver_comap {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (g : S →ₐ[R] T) (hg : Function.Surjective g) (q : Ideal S)
    [q.IsPrime] (𝔭 : Ideal R) [q.LiesOver 𝔭] {c : S} (hc : c ∉ q)
    (hann : ∀ x : S, g x = 0 → c * x = 0) :
    (q.map g.toRingHom).IsPrime ∧ (q.map g.toRingHom).LiesOver 𝔭 ∧
      q = (q.map g.toRingHom).comap g.toRingHom := by
  have hker : RingHom.ker g.toRingHom ≤ q := ker_le_of_annihilator_notMem _ q hc hann
  have hpq : q = (q.map g.toRingHom).comap g.toRingHom := by
    rw [Ideal.comap_map_of_surjective g.toRingHom hg, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hker]
  exact ⟨Ideal.map_isPrime_of_surjective (f := g.toRingHom) hg hker,
    liesOver_of_eq_comap g hpq 𝔭, hpq⟩

/-- If `f : S → T` is surjective and some `c` whose image avoids a prime `p` of `T` annihilates
`ker f`, then a localization `Tp` of `T` at `p` is a localization of `S` at the contraction of
`p`: the kernel of `f` dies in `Tp`, so inverting `f⁻¹(p)ᶜ` in `S` and `pᶜ` in `T` give the same
ring. -/
private lemma isLocalization_comap_of_surjective {S T Tp : Type*} [CommRing S] [CommRing T]
    [CommRing Tp] [Algebra T Tp] [Algebra S Tp] (f : S →+* T) (hf : Function.Surjective f)
    (q : Ideal S) [q.IsPrime] (p : Ideal T) [p.IsPrime] [IsLocalization.AtPrime Tp p]
    (hpq : q = p.comap f) {c : S} (hc : f c ∉ p) (hann : ∀ x : S, f x = 0 → c * x = 0)
    (hcomp : algebraMap S Tp = (algebraMap T Tp).comp f) :
    IsLocalization q.primeCompl Tp := by
  subst hpq
  have hmem : ∀ x : S, f x ∉ p → x ∈ (p.comap f).primeCompl := fun x hx =>
    Ideal.mem_primeCompl_iff.mpr fun h => hx (Ideal.mem_comap.mp h)
  have hmem' : ∀ x : S, x ∈ (p.comap f).primeCompl → f x ∈ p.primeCompl := fun x hx =>
    Ideal.mem_primeCompl_iff.mpr fun h =>
      Ideal.mem_primeCompl_iff.mp hx (Ideal.mem_comap.mpr h)
  refine ⟨⟨fun y => ?_, fun z => ?_, fun {x y} h => ?_⟩⟩
  · rw [hcomp]
    exact IsLocalization.map_units Tp ⟨f y.1, hmem' y.1 y.2⟩
  · obtain ⟨⟨t, s⟩, hz⟩ := IsLocalization.surj p.primeCompl z
    obtain ⟨x, hx⟩ := hf t
    obtain ⟨y, hy⟩ := hf s.1
    refine ⟨⟨x, y, hmem y (hy ▸ Ideal.mem_primeCompl_iff.mp s.2)⟩, ?_⟩
    rw [hcomp]
    simpa [hx, hy] using hz
  · have h' : algebraMap T Tp (f x) = algebraMap T Tp (f y) := by
      rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← hcomp]; exact h
    obtain ⟨d, hd⟩ := (IsLocalization.eq_iff_exists p.primeCompl Tp).mp h'
    obtain ⟨w, hw⟩ := hf d.1
    refine ⟨⟨c * w, mul_mem (hmem c hc) (hmem w (hw ▸ Ideal.mem_primeCompl_iff.mp d.2))⟩, ?_⟩
    have hzero : c * (w * x - w * y) = 0 :=
      hann _ (by rw [map_sub, map_mul, map_mul, hw, hd, sub_self])
    simpa [mul_sub, sub_eq_zero, mul_assoc] using hzero

/-- The `i`-th projection of a ring isomorphism onto a product is surjective. -/
private lemma surjective_evalRingHom_comp {ι : Type*} {A : Type*} [CommRing A]
    (Aι : ι → Type*) [∀ i, CommRing (Aι i)] (e : A ≃+* ∀ i, Aι i) (i : ι) :
    Function.Surjective ((Pi.evalRingHom Aι i).comp (e : A →+* ∀ i, Aι i)) := by
  classical
  exact fun a => ⟨e.symm (Pi.single i a), by simp⟩

/-- Some idempotent `e.symm (Pi.single i 1)` of a finite product decomposition avoids a given
prime ideal. -/
private lemma exists_symm_single_notMem {ι : Type*} [Finite ι] [DecidableEq ι] {A : Type*}
    [CommRing A] (Aι : ι → Type*) [∀ i, CommRing (Aι i)] (e : A ≃+* ∀ i, Aι i) (p : Ideal A)
    [p.IsPrime] : ∃ i, e.symm (Pi.single i 1) ∉ p := by
  have := Fintype.ofFinite ι
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  refine ‹p.IsPrime›.ne_top ((Ideal.eq_top_iff_one p).mpr ?_)
  have hsum : ∑ j : ι, (Pi.single j 1 : ∀ j, Aι j) = 1 := by
    simpa using Finset.univ_sum_single (1 : ∀ j, Aι j)
  have hone : ∑ j : ι, e.symm (Pi.single j 1) = 1 := by rw [← map_sum e.symm, hsum, map_one]
  rw [← hone]
  exact Ideal.sum_mem _ fun j _ => hcon j

/-- A maximal ideal of a finite product of local rings is the contraction of the maximal ideal of
the factor whose idempotent it avoids. -/
private lemma eq_comap_maximalIdeal_of_symm_single_notMem {ι : Type*} [DecidableEq ι] {A : Type*}
    [CommRing A] (Aι : ι → Type*) [∀ i, CommRing (Aι i)] [∀ i, IsLocalRing (Aι i)]
    (e : A ≃+* ∀ i, Aι i) (p : Ideal A) [p.IsMaximal] (i : ι)
    (hi : e.symm (Pi.single i 1) ∉ p) :
    p = (maximalIdeal (Aι i)).comap ((Pi.evalRingHom Aι i).comp (e : A →+* ∀ i, Aι i)) := by
  set u := (Pi.evalRingHom Aι i).comp (e : A →+* ∀ i, Aι i) with hu_def
  have hu : Function.Surjective u := surjective_evalRingHom_comp Aι e i
  refine ‹p.IsMaximal›.eq_of_le (Ideal.comap_isMaximal_of_surjective u hu).ne_top fun x hx => ?_
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  obtain ⟨w, hw⟩ := hunit.exists_left_inv
  obtain ⟨v, hv⟩ := hu w
  have hvx : (Pi.single i 1 : ∀ j, Aι j) * e (v * x) = Pi.single i 1 := by
    have : u v * u x = 1 := by rw [hv]; exact hw
    funext j
    by_cases hj : j = i
    · subst hj; simpa [hu_def] using this
    · simp [Ne.symm hj]
  refine hi ?_
  rw [← hvx, ← symm_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hx)

/-- **04GG (10)** for a henselian local ring, in the spelling the arguments below use: a finite
algebra over a henselian local ring is a finite product of local rings. This is Stacks 04GJ
(`exists_algEquiv_pi_isLocalRing`), whose decomposition is indexed by a `Fin n` and is an
`AlgEquiv`; the index type is transported into `Type u` along `ULift` and the equivalence is read
as a `RingEquiv`. -/
@[ega "IV 18.5.9" "(ii), necessity", sga "4 VIII 4.1" "(i)"]
private lemma exists_pi_isLocalRing_of_finite (R : Type u) [CommRing R] [HenselianLocalRing R] :
    ∀ (S : Type v) [CommRing S] [Algebra R S], Module.Finite R S →
      ∃ (ι : Type (max u v)) (_ : Finite ι) (A : ι → Type (max u v)) (_ : ∀ i, CommRing (A i))
        (_ : ∀ i, IsLocalRing (A i)), Nonempty (S ≃+* ∀ i, A i) := by
  intro S _ _ _
  let : Module.Finite R (ULift.{u} S) :=
    Module.Finite.equiv (ULift.moduleEquiv (R := R)).symm
  obtain ⟨n, Af, hAfring, hAfalg, hAfloc, hAffin, ⟨e⟩⟩ :=
    exists_algEquiv_pi_isLocalRing R (ULift.{u} S)
  refine ⟨ULift.{max u v} (Fin n), inferInstance, fun j => Af j.down,
    fun j => hAfring j.down, fun j => hAfloc j.down,
    ⟨(ULift.algEquiv (R := R) (A := S)).symm.toRingEquiv.trans
      (e.toRingEquiv.trans ?_)⟩⟩
  exact
    { toFun := fun x j => x j.down
      invFun := fun y i => y (ULift.up i)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }

/-- **04GG (11)** for a henselian local ring, in the spelling the arguments below use: a finite
type algebra over a henselian local ring is `A × B` with `A` finite over `R` and `R → B`
quasi-finite at no prime over `𝔪`. This is Stacks 04GJ
(`exists_prod_finite_not_quasiFiniteAt`), whose two factors
already live in `Type u` when `S` does. -/
private lemma exists_prod_finite_not_quasiFiniteAt' (R : Type u) [CommRing R]
    [HenselianLocalRing R] :
    ∀ (S : Type v) [CommRing S] [Algebra R S], Algebra.FiniteType R S →
      ∃ (A B : Type (max u v)) (_ : CommRing A) (_ : CommRing B)
        (_ : Algebra R A) (_ : Algebra R B)
        (_ : S ≃ₐ[R] A × B), Module.Finite R A ∧
        ∀ q : Ideal B, ∀ [q.IsPrime], q.LiesOver (maximalIdeal R) →
          ¬ Algebra.QuasiFiniteAt R q := by
  intro S _ _ _
  obtain ⟨A, hAring, hAalg, B, hBring, hBalg, hAfin, hBnqf, ⟨e⟩⟩ :=
    exists_prod_finite_not_quasiFiniteAt R S
  exact ⟨A, B, hAring, hBring, hAalg, hBalg, e, hAfin, hBnqf⟩

/-- **Nakayama** for the structure map: if every element of a finite algebra `C` over a local ring
`S` agrees with an element of the image of `S` modulo `𝔪_S · C`, then `S → C` is surjective. -/
private lemma surjective_algebraMap_of_mem_smul_top (S C : Type*) [CommRing S] [IsLocalRing S]
    [CommRing C] [Algebra S C] [Module.Finite S C]
    (h : ∀ c : C, ∃ s : S, c - algebraMap S C s ∈ (maximalIdeal S) • (⊤ : Submodule S C)) :
    Function.Surjective (algebraMap S C) := by
  have hfg : (⊤ : Submodule S C).FG := Module.finite_def.mp inferInstance
  have hle : (⊤ : Submodule S C) ≤ LinearMap.range (Algebra.linearMap S C) ⊔
      (maximalIdeal S) • (⊤ : Submodule S C) := by
    intro c _
    obtain ⟨s, hs⟩ := h c
    exact Submodule.mem_sup.mpr ⟨algebraMap S C s, ⟨s, rfl⟩, c - algebraMap S C s, hs, by ring⟩
  have hsub := Submodule.le_of_le_smul_of_le_jacobson_bot hfg
    (IsLocalRing.maximalIdeal_le_jacobson ⊥) hle
  intro c
  exact hsub (Submodule.mem_top (x := c))

/-- A nonzero algebra `C` over a local ring `S` which is projective as an `S`-module and whose
structure map is surjective: the structure map is bijective. The surjection `S → C` splits by
projectivity, so `S` decomposes as a module into `ker` and a complement; the corresponding
idempotent of `S` is `0` or `1`, and `0` would force `C = 0`. -/
private lemma bijective_algebraMap_of_projective (S C : Type*) [CommRing S] [IsLocalRing S]
    [CommRing C] [Nontrivial C] [Algebra S C] [Module.Projective S C]
    (hsurj : Function.Surjective (algebraMap S C)) :
    Function.Bijective (algebraMap S C) := by
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (Algebra.linearMap S C)
    (LinearMap.id : C →ₗ[S] C)
    (fun c => by obtain ⟨s, hs⟩ := hsurj c; exact ⟨s, by simpa using hs⟩)
  have hσ' : ∀ c : C, algebraMap S C (σ c) = c := fun c => by
    simpa using LinearMap.congr_fun hσ c
  set ε := σ (1 : C) with hε
  have hεmap : algebraMap S C ε = 1 := hσ' 1
  have hpi : ∀ s : S, σ (algebraMap S C s) = s * ε := by
    intro s
    rw [show algebraMap S C s = s • (1 : C) by rw [Algebra.smul_def, mul_one], map_smul,
      smul_eq_mul]
  have hidem : ε = ε * ε := by conv_lhs => rw [hε, ← hεmap, hpi]
  refine ⟨?_, hsurj⟩
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self ε with hu | hu
  · have hε1 : ε = 1 := (hu.mul_left_cancel (by rw [mul_one]; exact hidem)).symm
    intro s t hst
    have h1 := hpi s
    have h2 := hpi t
    rw [hst, hε1, mul_one] at h1
    rw [hε1, mul_one] at h2
    exact h1.symm.trans h2
  · exfalso
    have hz : (1 - ε) * ε = (1 - ε) * 0 := by
      rw [mul_zero, sub_mul, one_mul, ← hidem, sub_self]
    have hz0 : ε = 0 := hu.mul_left_cancel hz
    rw [hz0, map_zero] at hεmap
    exact zero_ne_one hεmap

/-- The local factor carries the root down to `S`. Let `S` be local, `C` a local `S`-algebra which
is finite and projective as an `S`-module and is generated over `S` by an element `ξ` with
`f(ξ) = 0` and `ξ ≡ a₀` modulo `𝔪_C`. Since `a₀` is a simple root of `f` modulo `𝔪_S`, the
expansion `0 = f(ξ) = f(a₀) + f'(a₀)(ξ - a₀) + k(ξ - a₀)²` puts `ξ - a₀` in `𝔪_S · C`, so
`C = S + 𝔪_S · C` and `S → C` is onto by Nakayama, hence bijective by projectivity; the preimage
of `ξ` is the required root. -/
private lemma exists_isRoot_of_eval₂_eq_zero (S C : Type*) [CommRing S] [IsLocalRing S]
    [CommRing C] [IsLocalRing C] [Algebra S C] [Module.Finite S C] [Module.Projective S C]
    (f : Polynomial S) (a₀ : S) (hfa₀ : f.eval a₀ ∈ maximalIdeal S)
    (hder : IsUnit (f.derivative.eval a₀)) (ξ : C)
    (hev : f.eval₂ (algebraMap S C) ξ = 0)
    (hz : ξ - algebraMap S C a₀ ∈ maximalIdeal C)
    (hgen : ∀ c : C, ∃ p : Polynomial S, c = p.eval₂ (algebraMap S C) ξ) :
    ∃ a : S, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal S := by
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (f.map (algebraMap S C))
    (algebraMap S C a₀) (ξ - algebraMap S C a₀)
  rw [add_sub_cancel] at hk
  have e1 : (f.map (algebraMap S C)).eval ξ = 0 := by rwa [Polynomial.eval_map]
  have hmap : ∀ p : Polynomial S, (p.map (algebraMap S C)).eval (algebraMap S C a₀)
      = algebraMap S C (p.eval a₀) := fun p => by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  rw [e1, hmap, Polynomial.derivative_map, hmap] at hk
  -- `f'(a₀) + k(ξ - a₀)` is a unit: `f'(a₀)` is one and `ξ - a₀` lies in `𝔪_C`
  have hvunit : IsUnit (algebraMap S C (f.derivative.eval a₀) + k * (ξ - algebraMap S C a₀)) := by
    by_contra hv
    have hmem := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hv)
    have hkz : k * (ξ - algebraMap S C a₀) ∈ maximalIdeal C := Ideal.mul_mem_left _ _ hz
    have hd : algebraMap S C (f.derivative.eval a₀) ∈ maximalIdeal C := by
      simpa using sub_mem hmem hkz
    exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp hd)) (hder.map (algebraMap S C))
  obtain ⟨vu, hvu⟩ := hvunit
  have hzfac : ξ - algebraMap S C a₀
      = algebraMap S C (f.eval a₀) * (-((vu⁻¹ : Cˣ) : C)) := by
    have h1 : (ξ - algebraMap S C a₀) * ((vu : Cˣ) : C) = - algebraMap S C (f.eval a₀) := by
      rw [hvu]
      linear_combination -hk
    calc ξ - algebraMap S C a₀
        = (ξ - algebraMap S C a₀) * ((vu : Cˣ) : C) * ((vu⁻¹ : Cˣ) : C) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = algebraMap S C (f.eval a₀) * (-((vu⁻¹ : Cˣ) : C)) := by
          rw [h1]
          ring
  have hzmem : ∀ t : C, (ξ - algebraMap S C a₀) * t
      ∈ (maximalIdeal S) • (⊤ : Submodule S C) := by
    intro t
    have ht : (ξ - algebraMap S C a₀) * t = (f.eval a₀) • ((-((vu⁻¹ : Cˣ) : C)) * t) := by
      rw [hzfac, Algebra.smul_def, ← mul_assoc]
    rw [ht]
    exact Submodule.smul_mem_smul hfa₀ Submodule.mem_top
  -- `C = S + 𝔪_S · C`, so `S → C` is onto, hence bijective
  have hsurj : Function.Surjective (algebraMap S C) := by
    refine surjective_algebraMap_of_mem_smul_top S C fun c => ?_
    obtain ⟨p, hp⟩ := hgen c
    refine ⟨p.eval a₀, ?_⟩
    have hpx : c = (p.map (algebraMap S C)).eval ξ := by rw [hp, Polynomial.eval_map]
    obtain ⟨t, ht⟩ := Polynomial.sub_dvd_eval_sub ξ (algebraMap S C a₀)
      (p.map (algebraMap S C))
    rw [hpx, ← hmap, ht]
    exact hzmem t
  have hbij := bijective_algebraMap_of_projective S C hsurj
  obtain ⟨a, ha⟩ := hsurj ξ
  refine ⟨a, ?_, ?_⟩
  · refine hbij.1 ?_
    rwa [map_zero, ← Polynomial.eval₂_at_apply, ha]
  · refine (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr fun hunit => ?_)
    have h2 := hunit.map (algebraMap S C)
    rw [map_sub, ha] at h2
    exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp hz)) h2

/-- **04GG (10) ⟹ (1)** in the case at hand: a local ring `S` finite over a henselian local ring
`R` is henselian. Let `f ∈ S[X]` be monic with a simple root `a₀` modulo `𝔪_S`. The `S`-algebra
`A = S[X]/(f)` is free over `S`, hence finite over `R`, so 04GG (10) for `R` writes it as a finite
product of local rings; the residue map `A → κ_S` sending the root to `a₀` kills `x - a₀`, so
`x - a₀` is not a unit of `A` and therefore is a non-unit in one factor `C`. That factor is a
quotient of `A` and a direct `S`-summand of it, hence finite and projective over `S`, and it is
generated over `S` by the image of `x`, which is a root of `f` congruent to `a₀`; so
`exists_isRoot_of_eval₂_eq_zero` identifies `S` with `C` and produces the root in `S`. -/
private lemma henselianLocalRing_of_finite (R : Type u) (S : Type v)
    [CommRing R] [HenselianLocalRing R]
    [CommRing S] [Algebra R S] [IsLocalRing S] [Module.Finite R S] : HenselianLocalRing S := by
  classical
  refine { is_henselian := fun f hf a₀ hfa₀ hder => ?_ }
  have hAfin : Module.Finite S (AdjoinRoot f) := hf.finite_adjoinRoot
  have hAfree : Module.Free S (AdjoinRoot f) := hf.free_adjoinRoot
  have htow : IsScalarTower R S (AdjoinRoot f) := IsScalarTower.of_algebraMap_eq' rfl
  have hARfin : Module.Finite R (AdjoinRoot f) := Module.Finite.trans S _
  -- `x - a₀` dies in `κ_S`, hence is not a unit of `A`
  have hψroot : f.eval₂ (residue S) (residue S a₀) = 0 := by
    rw [Polynomial.eval₂_at_apply]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr hfa₀
  have hwnu : ¬ IsUnit (AdjoinRoot.root f - algebraMap S (AdjoinRoot f) a₀) := by
    intro hu
    have h2 := hu.map (AdjoinRoot.lift (residue S) (residue S a₀) hψroot)
    rw [map_sub, AdjoinRoot.lift_root hψroot, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.lift_of hψroot, sub_self] at h2
    exact not_isUnit_zero h2
  let : Module.Finite R (ULift.{u} (AdjoinRoot f)) :=
    Module.Finite.equiv (ULift.moduleEquiv (R := R)).symm
  obtain ⟨n, Af, hAfring, hAfalg, hAfloc, hAffin, ⟨e'⟩⟩ :=
    exists_algEquiv_pi_isLocalRing R (ULift.{u} (AdjoinRoot f))
  let e : AdjoinRoot f ≃ₐ[R] (∀ j, Af j) :=
    (ULift.algEquiv (R := R) (A := AdjoinRoot f)).symm.trans e'
  let uj : ∀ j, AdjoinRoot f →+* Af j := fun j =>
    (Pi.evalRingHom Af j).comp (e : AdjoinRoot f →+* ∀ j, Af j)
  let algS : ∀ j, Algebra S (Af j) := fun j =>
    ((uj j).comp (algebraMap S (AdjoinRoot f))).toAlgebra
  have hujalg : ∀ j (s : S), uj j (algebraMap S (AdjoinRoot f) s) = algebraMap S (Af j) s :=
    fun _ _ => rfl
  let E : AdjoinRoot f ≃ₐ[S] (∀ j, Af j) :=
    AlgEquiv.ofRingEquiv (f := (e : AdjoinRoot f ≃+* ∀ j, Af j)) (fun _ => funext fun _ => rfl)
  -- a factor in which `x - a₀` is a non-unit
  have hex : ∃ i, ¬ IsUnit (uj i (AdjoinRoot.root f - algebraMap S (AdjoinRoot f) a₀)) := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    refine hwnu ?_
    have hpi : IsUnit (e (AdjoinRoot.root f - algebraMap S (AdjoinRoot f) a₀)) :=
      Pi.isUnit_iff.mpr fun j => hcon j
    simpa using hpi.map (e.symm : (∀ j, Af j) ≃ₐ[R] AdjoinRoot f)
  obtain ⟨i, hinu⟩ := hex
  have hCloc : IsLocalRing (Af i) := hAfloc i
  let uA : AdjoinRoot f →ₐ[S] Af i := { toRingHom := uj i, commutes' := fun _ => rfl }
  have huA : Function.Surjective uA := surjective_evalRingHom_comp Af e.toRingEquiv i
  have hCfin : Module.Finite S (Af i) := Module.Finite.of_surjective uA.toLinearMap huA
  have hCproj : Module.Projective S (Af i) := by
    refine Module.Projective.of_split (M := AdjoinRoot f)
      ((E.symm.toLinearEquiv.toLinearMap).comp (LinearMap.single S Af i)) uA.toLinearMap ?_
    refine LinearMap.ext fun c => ?_
    simp [uA, uj, E]
  have hofeq : (uj i).comp (AdjoinRoot.of f) = algebraMap S (Af i) := by
    rw [← AdjoinRoot.algebraMap_eq]
    rfl
  have hev : f.eval₂ (algebraMap S (Af i)) (uj i (AdjoinRoot.root f)) = 0 := by
    have h1 := congrArg (uj i) (AdjoinRoot.eval₂_root f)
    rwa [Polynomial.hom_eval₂, hofeq, map_zero] at h1
  have hz : uj i (AdjoinRoot.root f) - algebraMap S (Af i) a₀ ∈ maximalIdeal (Af i) := by
    refine (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr ?_)
    rwa [← hujalg i a₀, ← map_sub]
  have hgen : ∀ c : Af i, ∃ p : Polynomial S,
      c = p.eval₂ (algebraMap S (Af i)) (uj i (AdjoinRoot.root f)) := by
    intro c
    obtain ⟨a, rfl⟩ := huA c
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
    refine ⟨p, ?_⟩
    have h1 : (AdjoinRoot.mk f p)
        = p.eval₂ (algebraMap S (AdjoinRoot f)) (AdjoinRoot.root f) := by
      rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_def]
    show uj i (AdjoinRoot.mk f p) = _
    rw [h1, Polynomial.hom_eval₂]
    rfl
  exact exists_isRoot_of_eval₂_eq_zero S (Af i) f a₀ hfa₀ hder _ hev hz hgen

/-- A finite ring map between local rings is a local homomorphism: the contraction of the maximal
ideal is maximal, hence is the maximal ideal. -/
private lemma isLocalHom_algebraMap (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [Module.Finite R S] : IsLocalHom (algebraMap R S) := by
  refine ⟨fun a ha => notMem_maximalIdeal.mp fun h => notMem_maximalIdeal.mpr ha
    (Ideal.mem_comap.mp ?_)⟩
  rwa [eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (maximalIdeal S))]

/-- **04GH (1)**: a finite algebra over a henselian local ring is a finite product of henselian
local rings, each finite over the base. -/
private lemma exists_pi_henselian_of_finite (R : Type u) [CommRing R] [HenselianLocalRing R]
    (S : Type v) [CommRing S] [Algebra R S] [Module.Finite R S] :
    ∃ (ι : Type (max u v)) (_ : Finite ι) (A : ι → Type (max u v))
      (_ : ∀ i, CommRing (A i))
      (_ : ∀ i, Algebra R (A i)) (_ : ∀ i, HenselianLocalRing (A i)),
      (∀ i, Module.Finite R (A i)) ∧ Nonempty (S ≃ₐ[R] ∀ i, A i) := by
  classical
  obtain ⟨ι, hι, A, hAring, hAlocal, ⟨e⟩⟩ := exists_pi_isLocalRing_of_finite R S inferInstance
  let algA : ∀ i, Algebra R (A i) := fun i =>
    (((Pi.evalRingHom A i).comp (e : S →+* ∀ i, A i)).comp (algebraMap R S)).toAlgebra
  let u : ∀ i, S →ₐ[R] A i := fun i =>
    { toRingHom := (Pi.evalRingHom A i).comp (e : S →+* ∀ i, A i)
      commutes' := fun r => rfl }
  have hfin : ∀ i, Module.Finite R (A i) := fun i =>
    Module.Finite.of_surjective (u i).toLinearMap (surjective_evalRingHom_comp A e i)
  exact ⟨ι, hι, A, hAring, algA,
    fun i => have := hfin i; henselianLocalRing_of_finite R (A i), hfin,
    ⟨AlgEquiv.ofRingEquiv (f := e) fun r => funext fun i => rfl⟩⟩

/-- A localization of a finite algebra over a henselian local ring at a prime over the maximal
ideal is a quotient of it: the algebra is a finite product of local rings by 04GG (10) and the
localization is the factor whose idempotent avoids the prime. -/
private lemma surjective_algebraMap_of_liesOver (R : Type u) (A : Type v) (Ap : Type w) [CommRing R]
    [HenselianLocalRing R] [CommRing A] [Algebra R A] [Module.Finite R A] [CommRing Ap]
    [Algebra A Ap] (p : Ideal A) [p.IsPrime] [p.LiesOver (maximalIdeal R)]
    [IsLocalization.AtPrime Ap p] :
    Function.Surjective (algebraMap A Ap) := by
  classical
  have hpmax : p.IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) p ?_
    rw [← Ideal.under_def, ← Ideal.over_def p (maximalIdeal R)]
    exact maximalIdeal.isMaximal R
  obtain ⟨ι, hι, Aι, hAring, hAlocal, ⟨e⟩⟩ := exists_pi_isLocalRing_of_finite R A inferInstance
  obtain ⟨i, hi⟩ := exists_symm_single_notMem Aι e p
  set u := (Pi.evalRingHom Aι i).comp (e : A →+* ∀ i, Aι i) with hu_def
  have hu : Function.Surjective u := surjective_evalRingHom_comp Aι e i
  -- `Aι i` is its own localization at its maximal ideal, hence a localization of `A` at `p`
  let : Algebra A (Aι i) := u.toAlgebra
  have halg : algebraMap A (Aι i) = u := RingHom.algebraMap_toAlgebra _
  have : IsLocalization.AtPrime (Aι i) (maximalIdeal (Aι i)) :=
    IsLocalization.self fun _ hx => notMem_maximalIdeal.mp (Ideal.mem_primeCompl_iff.mp hx)
  have : IsLocalization p.primeCompl (Aι i) := by
    refine isLocalization_comap_of_surjective u hu p (maximalIdeal (Aι i))
      (by rw [eq_comap_maximalIdeal_of_symm_single_notMem Aι e p i hi, ← hu_def])
      (c := e.symm (Pi.single i 1)) (notMem_maximalIdeal.mpr ?_) (fun x hx => ?_)
      (by rw [halg]; ext x; simp)
    · simp [hu_def]
    · refine symm_mul_eq_zero e ?_
      funext j
      by_cases hj : j = i
      · subst hj; simpa [hu_def] using hx
      · simp [Ne.symm hj]
  have φ : Aι i ≃ₐ[A] Ap := IsLocalization.algEquiv p.primeCompl (Aι i) Ap
  intro z
  obtain ⟨y, rfl⟩ := φ.surjective z
  obtain ⟨x, rfl⟩ := hu y
  exact ⟨x, by rw [← halg]; exact (φ.commutes x).symm⟩

/-- **The finite factor case of 04GH (3)**: if `S` maps onto a finite `R`-algebra `A` by a map
whose kernel is annihilated by some `c` outside a prime `q` of `S` over `𝔪`, then a localization
of `S` at `q` is a quotient of `A`; hence it is finite over `R`, and henselian by 04GH (2). -/
private lemma henselianLocalRing_and_finite_of_surjective
    (R : Type u) (S : Type v) (A : Type w) (Sq : Type x) [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [CommRing A] [Algebra R A]
    [Module.Finite R A] (f : S →ₐ[R] A) (hf : Function.Surjective f) (q : Ideal S) [q.IsPrime]
    [q.LiesOver (maximalIdeal R)] {c : S} (hc : c ∉ q) (hann : ∀ x : S, f x = 0 → c * x = 0)
    [CommRing Sq] [Algebra R Sq] [Algebra S Sq] [IsScalarTower R S Sq]
    [IsLocalization.AtPrime Sq q] :
    HenselianLocalRing Sq ∧ Module.Finite R Sq := by
  obtain ⟨hpprime, hover, hpq⟩ := map_isPrime_liesOver_comap f hf q (maximalIdeal R) hc hann
  set p := q.map f.toRingHom
  let : Algebra S (Localization.AtPrime p) :=
    ((algebraMap A (Localization.AtPrime p)).comp f.toRingHom).toAlgebra
  have hcomp : algebraMap S (Localization.AtPrime p)
      = (algebraMap A (Localization.AtPrime p)).comp f.toRingHom :=
    RingHom.algebraMap_toAlgebra _
  have : IsLocalization q.primeCompl (Localization.AtPrime p) :=
    isLocalization_comap_of_surjective f.toRingHom hf q p hpq
      (fun h => hc (by rw [hpq]; exact h)) hann hcomp
  have hsurjA : Function.Surjective (algebraMap A (Localization.AtPrime p)) :=
    surjective_algebraMap_of_liesOver R A (Localization.AtPrime p) p
  have φ : Localization.AtPrime p ≃ₐ[S] Sq :=
    IsLocalization.algEquiv q.primeCompl (Localization.AtPrime p) Sq
  -- `Sq` is a quotient of `A` as an `R`-algebra, hence finite over `R`
  have hkey : ∀ r : R, φ (algebraMap A (Localization.AtPrime p) (algebraMap R A r))
      = algebraMap R Sq r := fun r => by
    have h1 : algebraMap A (Localization.AtPrime p) (algebraMap R A r)
        = algebraMap S (Localization.AtPrime p) (algebraMap R S r) := by
      rw [hcomp, RingHom.comp_apply]
      exact congrArg _ (f.commutes r).symm
    rw [h1, φ.commutes, ← IsScalarTower.algebraMap_apply]
  let k : A →ₐ[R] Sq :=
    { toRingHom := φ.toRingHom.comp (algebraMap A (Localization.AtPrime p))
      commutes' := hkey }
  have : IsLocalRing Sq := IsLocalization.AtPrime.isLocalRing Sq q
  have : Module.Finite R Sq :=
    Module.Finite.of_surjective k.toLinearMap (φ.surjective.comp hsurjA)
  exact ⟨henselianLocalRing_of_finite R Sq, inferInstance⟩

/-- **04GH (3)**: for `S` of finite type over a henselian local ring `R` and `q` a prime of `S`
over `𝔪` at which `R → S` is quasi-finite, `S_q` is henselian and finite over `R`. Writing
`S = A × B` as in 04GG (11), the prime `q` comes from the finite factor `A` — it cannot come from
`B`, since quasi-finiteness at `q` descends along the surjection `S → B`. -/
private lemma henselianLocalRing_and_finite_localization (R : Type u) [CommRing R]
    [HenselianLocalRing R] (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime] [q.LiesOver (maximalIdeal R)] [Algebra.QuasiFiniteAt R q]
    (Sq : Type w) [CommRing Sq] [Algebra R Sq] [Algebra S Sq] [IsScalarTower R S Sq]
    [IsLocalization.AtPrime Sq q] :
    HenselianLocalRing Sq ∧ Module.Finite R Sq := by
  have h11 := exists_prod_finite_not_quasiFiniteAt' R
  obtain ⟨A, B, hAring, hBring, hAalg, hBalg, e, hA, hB⟩ := h11 S inferInstance
  by_cases hε : e.symm (1, 0) ∈ q
  · -- `q` comes from `B`, which is quasi-finite at no prime over `𝔪`: impossible
    exfalso
    have h1 : e.symm ((1, 0) : A × B) + e.symm ((0, 1) : A × B) = 1 := by rw [← map_add]; simp
    have hone : e.symm ((0, 1) : A × B) ∉ q := fun h =>
      ‹q.IsPrime›.ne_top ((Ideal.eq_top_iff_one q).mpr (h1 ▸ q.add_mem hε h))
    have hgs : Function.Surjective ((AlgHom.snd R A B).comp e.toAlgHom) := fun b =>
      ⟨e.symm (0, b), by simp⟩
    obtain ⟨hp, hover, hpq⟩ := map_isPrime_liesOver_comap ((AlgHom.snd R A B).comp e.toAlgHom)
      hgs q (maximalIdeal R) hone fun x hx =>
        symm_mul_eq_zero e.toRingEquiv (by ext <;> simp [show (e x).2 = 0 from hx])
    exact hB _ hover (Algebra.QuasiFiniteAt.of_surjectiveOnStalks q _
      (RingHom.surjectiveOnStalks_of_surjective hgs) _ hpq)
  · -- `q` comes from the finite factor `A`
    exact henselianLocalRing_and_finite_of_surjective R S A Sq
      ((AlgHom.fst R A B).comp e.toAlgHom) (fun a => ⟨e.symm (a, 0), by simp⟩) q hε
      fun x hx => symm_mul_eq_zero e.toRingEquiv (by ext <;> simp [show (e x).1 = 0 from hx])

public theorem solution (R : Type u) [CommRing R] [HenselianLocalRing R] :
    (∀ (S : Type v) [CommRing S] [Algebra R S], Module.Finite R S →
        ∃ (ι : Type (max u v)) (_ : Finite ι) (A : ι → Type (max u v))
          (_ : ∀ i, CommRing (A i))
          (_ : ∀ i, Algebra R (A i)) (_ : ∀ i, HenselianLocalRing (A i)),
          (∀ i, Module.Finite R (A i)) ∧ Nonempty (S ≃ₐ[R] ∀ i, A i)) ∧
      (∀ (S : Type v) [CommRing S] [Algebra R S] [IsLocalRing S], Module.Finite R S →
        HenselianLocalRing S ∧ IsLocalHom (algebraMap R S)) ∧
      (∀ (S : Type v) [CommRing S] [Algebra R S], Algebra.FiniteType R S →
        ∀ q : Ideal S, ∀ [q.IsPrime] [q.LiesOver (maximalIdeal R)], Algebra.QuasiFiniteAt R q →
        ∀ (Sq : Type w) [CommRing Sq] [Algebra R Sq] [Algebra S Sq] [IsScalarTower R S Sq]
          [IsLocalization.AtPrime Sq q], HenselianLocalRing Sq ∧ Module.Finite R Sq) ∧
      (∀ (S : Type v) [CommRing S] [Algebra R S], Algebra.FiniteType R S →
        Algebra.QuasiFinite R S →
        ∀ q : Ideal S, ∀ [q.IsPrime] [q.LiesOver (maximalIdeal R)],
        ∀ (Sq : Type w) [CommRing Sq] [Algebra R Sq] [Algebra S Sq] [IsScalarTower R S Sq]
          [IsLocalization.AtPrime Sq q], HenselianLocalRing Sq ∧ Module.Finite R Sq) := by
  refine ⟨fun S _ _ _ => exists_pi_henselian_of_finite R S,
    fun S _ _ _ _ => ⟨henselianLocalRing_of_finite R S, isLocalHom_algebraMap R S⟩,
    fun S _ _ _ q _ _ _ Sq _ _ _ _ _ => henselianLocalRing_and_finite_localization R S q Sq,
    fun S _ _ _ _ q _ _ Sq _ _ _ _ _ => ?_⟩
  have : Algebra.QuasiFiniteAt R q := Algebra.QuasiFinite.of_isLocalization q.primeCompl
  exact henselianLocalRing_and_finite_localization R S q Sq

end Stacks.Henselian.QuasiFiniteAlgebras

/-!
# Finite and quasi-finite algebras over a henselian local ring

Let `(R, 𝔪, κ)` be a henselian local ring. Henselianness propagates to the finite and the
quasi-finite algebras over `R`, and it does so together with finiteness over `R`:

* a finite `R`-algebra breaks up as a finite product of henselian local rings, each of them
  again finite over `R`;
* if such an algebra happens to be local, it is henselian and the structure map `R → S` is a
  local homomorphism;
* and for a finite type `R`-algebra `S` and a prime `q` of `S` over `𝔪` at which `R → S` is
  quasi-finite, the local ring `S_q` is henselian and finite over `R` — so the quasi-finite
  case reduces to the finite one after localising.

The source's Lemma 04GH is the conjunction of these, and this file states it as such: the four
items of the source in order, as four conjuncts.

## Main results

* `HenselianLocalRing.henselianLocalRing_and_finite_of_finite_of_quasiFiniteAt`: the four items
  of Lemma 04GH, in the source's order, as one conjunction.

## Implementation notes

*Item (1): products of local rings.* "A finite product of henselian local rings each finite over
`R`" is a family `A : ι → Type u` of henselian local rings over a `Finite` index type, each
`Module.Finite R (A i)`, together with `S ≃ₐ[R] ∀ i, A i`. The index type is an arbitrary
`Finite` type rather than a `Fin n`, matching the spelling of the sibling 04GG item (10) from
which this item is deduced. The equivalence is an `AlgEquiv` and not merely a `RingEquiv` —
unlike 04GG (9), (10) — because the extra assertion "each finite over `R`" is a condition on
`R → A i`, so the decomposition has to be one of `R`-algebras for it to say anything.
`HenselianLocalRing` already extends `IsLocalRing`, so "henselian local ring" is the single
hypothesis `HenselianLocalRing (A i)`.

*Item (2): the local homomorphism clause is genuine content.* Mathlib's
`Algebra.IsIntegral.isLocalHom` gives `IsLocalHom (algebraMap R S)` for an integral extension
only under `FaithfulSMul R S`, i.e. for an *injective* structure map, whereas the source asserts
it for any finite ring map between local rings; `probe` closes neither the general statement by
`inferInstance` nor by `exact?`. Hence the conjunct `IsLocalHom (algebraMap R S)` is kept.
The source's parenthetical "(finite)" is the hypothesis `Module.Finite R S`, not a further claim.

*Items (3), (4): the localisation is abstract.* `S_q` is any `Sq` with
`IsLocalization.AtPrime Sq q`, not the model `Localization.AtPrime q`; the accompanying
`[Algebra S Sq] [IsScalarTower R S Sq]` pin the `R`-algebra structure on `Sq` to the one induced
through `S`, which is what makes `Module.Finite R Sq` the source's "finite over `R`". Without the
tower hypothesis `Module.Finite R Sq` would be a statement about an unrelated algebra structure.

*Quasi-finiteness.* Following 04GG, the source's quasi-finiteness at a prime (Definition 00PM at
`q`, "`q` is isolated in its fibre") is `Algebra.QuasiFiniteAt R q`, and the source's
quasi-finite ring map is `Algebra.FiniteType R S` together with Mathlib's weaker
`Algebra.QuasiFinite R S`; Mathlib's class asks only that every fibre be finite-dimensional over
its residue field, which for a non-finite-type algebra does not imply finite type, so the finite
type hypothesis of item (4) is not redundant.

*Item (4) is item (3) with the prime quantified.* Formally item (4) follows from item (3) by
`Algebra.QuasiFinite.of_isLocalization q.primeCompl`, which upgrades `Algebra.QuasiFinite R S` to
`Algebra.QuasiFiniteAt R q`. It is stated anyway, as the source states it, so that a dependent
citing "04GH (4)" finds it; it does not strengthen the conjunction.

*All algebras are quantified in `R`'s universe*, exactly as in the sibling 04GG whose items
(10), (11) supply the proof: each algebra arising is a quotient or a localisation of a polynomial
ring over `R`, hence has a model in `Type u`.

Faithfulness to [StacksProject 04GH], point by point.

1. No hypothesis is dead. `HenselianLocalRing R` is used by all four conjuncts and is the only
   ambient hypothesis. Inside item (2), `IsLocalRing S` is what the source assumes and cannot be
   dropped — `ℤ_[p] × ℤ_[p]` is finite over the henselian `ℤ_[p]` and is not local. In item (3),
   `Algebra.FiniteType R S` cannot be dropped (Mathlib's `QuasiFinite` is weaker than the
   source's) and `Algebra.QuasiFiniteAt R q` cannot either — for `S = R[Y]` and `q = 𝔪R[Y] + (Y)`
   the ring `S_q` is a two-dimensional local ring, not finite over `R`. `q.LiesOver 𝔪` cannot be
   dropped either: for `R = S = ℤ_[p]` and `q = ⊥` the remaining hypotheses hold, since both
   `Algebra.FiniteType ℤ_[p] ℤ_[p]` and `Algebra.QuasiFiniteAt ℤ_[p] ⊥` are instances (the latter
   because `Algebra.QuasiFinite R (FractionRing R)` is one for a domain `R`), while `S_q = ℚ_[p]`
   is not finite over `ℤ_[p]`.
2. The scalars and the base are the source's. Finiteness, finite type and quasi-finiteness are
   over `R` itself, never over a localisation of it; the decomposition of item (1) is an
   equivalence of `R`-algebras; and `Module.Finite R Sq` is finiteness over `R`, with the
   `IsScalarTower R S Sq` hypothesis fixing which `R`-algebra `Sq` is.
3. Where the source names a canonical map the statement pins it. The map made local in item (2)
   is `algebraMap R S`, the structure map itself. The localisation of items (3), (4) is pinned by
   `IsLocalization.AtPrime Sq q` together with the scalar tower, not by asserting the existence of
   some henselian local ring; and item (1) pins the projections up to a single `R`-algebra
   equivalence rather than only asserting that henselian local factors exist.
4. The instantiation is not degenerate. Take `R = ℤ_[p]`, which is henselian. Item (1) has content
   at `S = ℤ_[p][X]/(X² - 1)` for odd `p`, which splits into two copies of `ℤ_[p]`; item (2) at
   `S = ℤ_[p][X]/(X² - p)`, local and finite over `R`; and items (3), (4) at
   `S = ℤ_[p] × ℤ_[p][Y]` with `q` the maximal ideal of the first factor — `S` is of finite type
   and not finite, `q` lies over `𝔪` and `R → S` is quasi-finite there, and `S_q ≅ ℤ_[p]` is
   henselian and finite over `R`. So item (3) is not item (1) in disguise.

## References

* [StacksProject 04GH](https://stacks.math.columbia.edu/tag/04GH)

## Tags

henselian local ring, finite ring map, quasi-finite, local homomorphism, product of local rings,
localization at a prime
-/



@[expose] public section

open IsLocalRing in
/-- **Finite and quasi-finite algebras over a henselian local ring** (Stacks 04GH). Let
`(R, 𝔪, κ)` be a henselian local ring. (1) A finite `R`-algebra `S` is a finite product of
henselian local rings each finite over `R`. (2) If moreover `S` is local, then `S` is henselian
and `R → S` is a local homomorphism. (3) If `S` is of finite type over `R` and `q` is a prime of
`S` lying over `𝔪` at which `R → S` is quasi-finite, then `S_q` is henselian and finite over `R`.
(4) If `R → S` is quasi-finite, this holds at every prime `q` of `S` lying over `𝔪`. -/
@[stacks 04GH "The four items are the four conjuncts, in the source's order. A finite product of
local rings is an `AlgEquiv` onto a `Pi` type over a `Finite` index type (04GG (10)'s spelling,
upgraded from `RingEquiv` because the factors are required finite over `R`); `S_q` is any
`IsLocalization.AtPrime Sq q` in a scalar tower over `R`; the source's quasi-finiteness at `q` is
`Algebra.QuasiFiniteAt R q` and its quasi-finite ring map is `Algebra.FiniteType` together with
Mathlib's weaker `Algebra.QuasiFinite`. Item (4) is item (3) with `q` quantified. See the module
docstring.",
  ega "IV 18.5.9" "(ii) necessity",
  ega "IV 18.5.10" "R henselian local",
  sga "4 VIII 4.1" "partial"]
public theorem HenselianLocalRing.henselianLocalRing_and_finite_of_finite_of_quasiFiniteAt
    (R : Type u) [CommRing R] [HenselianLocalRing R] :
    (∀ (S : Type v) [CommRing S] [Algebra R S], Module.Finite R S →
        ∃ (ι : Type (max u v)) (_ : Finite ι) (A : ι → Type (max u v))
          (_ : ∀ i, CommRing (A i))
          (_ : ∀ i, Algebra R (A i)) (_ : ∀ i, HenselianLocalRing (A i)),
          (∀ i, Module.Finite R (A i)) ∧ Nonempty (S ≃ₐ[R] ∀ i, A i)) ∧
      (∀ (S : Type v) [CommRing S] [Algebra R S] [IsLocalRing S], Module.Finite R S →
        HenselianLocalRing S ∧ IsLocalHom (algebraMap R S)) ∧
      (∀ (S : Type v) [CommRing S] [Algebra R S], Algebra.FiniteType R S →
        ∀ q : Ideal S, ∀ [q.IsPrime] [q.LiesOver (maximalIdeal R)], Algebra.QuasiFiniteAt R q →
        ∀ (Sq : Type w) [CommRing Sq] [Algebra R Sq] [Algebra S Sq] [IsScalarTower R S Sq]
          [IsLocalization.AtPrime Sq q], HenselianLocalRing Sq ∧ Module.Finite R Sq) ∧
      (∀ (S : Type v) [CommRing S] [Algebra R S], Algebra.FiniteType R S →
        Algebra.QuasiFinite R S →
        ∀ q : Ideal S, ∀ [q.IsPrime] [q.LiesOver (maximalIdeal R)],
        ∀ (Sq : Type w) [CommRing Sq] [Algebra R Sq] [Algebra S Sq] [IsScalarTower R S Sq]
          [IsLocalization.AtPrime Sq q], HenselianLocalRing Sq ∧ Module.Finite R Sq) :=
    Stacks.Henselian.QuasiFiniteAlgebras.solution R

end
