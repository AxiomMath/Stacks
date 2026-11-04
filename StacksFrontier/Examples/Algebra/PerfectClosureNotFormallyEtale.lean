module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.FieldTheory.PerfectClosure
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat and formally unramified is not formally étale

Let `p` be a prime, let `A = 𝔽ₚ[T]` be the polynomial ring in one variable over the prime field,
and let `Aperf = PerfectClosure A p` be its perfect closure, the colimit of `A` along Frobenius.
The structure map `A → Aperf` is flat and formally unramified, but it is not formally étale. So
flatness together with formal unramifiedness does not imply formal étaleness.

Flatness holds because `A` is a Bézout domain and `Aperf` is a torsionfree `A`-module: a nonzero
element of `A` remains a nonzerodivisor in `Aperf`, since `A` is reduced and
`PerfectClosure.eq_iff` turns an equation in `Aperf` into an equation between Frobenius iterates
in `A`.

Formal unramifiedness holds because `Aperf` is a perfect ring: every element is a `p`-th power
`y ^ p`, and the universal derivation kills it, `D (y ^ p) = p • y ^ (p - 1) • D y = 0`, because
`Aperf` has characteristic `p`. Hence `Ω[Aperf⁄A] = 0`.

Formal étaleness fails, and the obstruction is already visible on the square-zero extension
`Aperf[ε] = TrivSqZeroExt Aperf Aperf`, made into an `A`-algebra by `T ↦ T + ε`. Modulo `ε` this
`A`-algebra structure is the standard one, so the inclusion of `Aperf` into `Aperf[ε]/(ε)` is a
map of `A`-algebras; but no `A`-algebra map `Aperf → Aperf[ε]` lifts it. Indeed `T = u ^ p` in
`Aperf` for `u` the `p`-th root of `T`, so a lift `g` would give `T + ε = g T = g u ^ p`, while in
characteristic `p` every `p`-th power in `Aperf[ε]` has vanishing `ε`-component. This is the
elementary shadow of the Stacks Project's computation of the cotangent complex `L_{Aperf/A}` as a
free rank one `Aperf`-module placed in degree `-1`.

## Main results

* `Stacks.Examples.flat_perfectClosure_polynomial`: `𝔽ₚ[T] → 𝔽ₚ[T]perf` is flat.
* `Stacks.Examples.formallyUnramified_perfectClosure_polynomial`: it is formally unramified.
* `Stacks.Examples.not_formallyEtale_perfectClosure_polynomial`: it is not formally étale.

The three conjuncts are specializations of statements proved more generally here:
`Stacks.Examples.flat_perfectClosure` (flatness of the perfect closure of any Bézout domain of
characteristic `p`), `Stacks.Examples.formallyUnramified_perfectClosure` (formal unramifiedness of
the perfect closure of any commutative ring of characteristic `p`), and
`Stacks.Examples.not_formallyEtale_perfectClosure_polynomialRing` (failure of formal étaleness for
the perfect closure of a polynomial ring over any domain of characteristic `p`).

## Implementation notes

`PerfectClosure A p` carries no `Algebra A` instance in Mathlib, so one is provided here, scoped to
the `Stacks.Examples` namespace, as the algebra structure induced by the ring map
`PerfectClosure.of A p`.

The square-zero extension is `TrivSqZeroExt Aperf Aperf` together with the ideal
`TrivSqZeroExt.kerIdeal`, whose square vanishes; the element `ε` is `TrivSqZeroExt.inr 1`. The
twisted `A`-algebra structure is the ring map `Stacks.Examples.perfectClosureDualTwist`, obtained
by evaluating a polynomial at `T + ε`.

## References

* [Stacks Project, Tag 0G65](https://stacks.math.columbia.edu/tag/0G65)
-/

@[expose] public section

namespace Stacks.Examples

universe u

/-- The perfect closure of a ring `K` of characteristic `p`, viewed as a `K`-algebra via the
canonical ring map `PerfectClosure.of K p`. This instance is scoped to `Stacks.Examples`. -/
scoped instance algebraPerfectClosure (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime]
    [CharP K p] : Algebra K (PerfectClosure K p) :=
  (PerfectClosure.of K p).toAlgebra

/-- The structure map of the algebra `PerfectClosure K p` over `K` is `PerfectClosure.of K p`. -/
@[simp]
theorem algebraMap_perfectClosure (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    algebraMap K (PerfectClosure K p) = PerfectClosure.of K p :=
  rfl

section Flat

variable (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- An element `x ^ (p ^ -n)` of the perfect closure of a reduced ring vanishes exactly when `x`
does. -/
theorem perfectClosure_mk_eq_zero_iff [IsReduced K] (n : ℕ) (x : K) :
    PerfectClosure.mk K p (n, x) = 0 ↔ x = 0 := by
  rw [PerfectClosure.zero_def, PerfectClosure.eq_iff, Function.iterate_zero_apply,
    Function.iterate_fixed (map_zero (frobenius K p))]

/-- The canonical map from a reduced ring of characteristic `p` to its perfect closure sends only
`0` to `0`; that is, it is injective. -/
theorem perfectClosure_of_eq_zero_iff [IsReduced K] (x : K) :
    PerfectClosure.of K p x = 0 ↔ x = 0 :=
  perfectClosure_mk_eq_zero_iff K p 0 x

/-- A nonzero element of a domain `K` of characteristic `p` is a nonzerodivisor on the perfect
closure: if `PerfectClosure.of K p a * x = 0` with `a ≠ 0`, then `x = 0`. -/
theorem eq_zero_of_perfectClosure_of_mul_eq_zero [IsDomain K] {a : K} (ha : a ≠ 0)
    {x : PerfectClosure K p} (h : PerfectClosure.of K p a * x = 0) : x = 0 := by
  obtain ⟨⟨n, y⟩, rfl⟩ := PerfectClosure.mk_surjective K p x
  rw [PerfectClosure.of_apply, PerfectClosure.mk_mul_mk,
    perfectClosure_mk_eq_zero_iff] at h
  simp only [Function.iterate_zero_apply, ← coe_iterateFrobenius, iterateFrobenius_def] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd (pow_eq_zero_iff'.mp h').1 ha
  · rw [h']
    exact PerfectClosure.mk_zero_right K p n

/-- The perfect closure of a domain of characteristic `p` is a torsionfree module over that
domain. -/
theorem torsion_perfectClosure_eq_bot [IsDomain K] :
    Submodule.torsion K (PerfectClosure K p) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_torsion_iff] at hx
  obtain ⟨a, hax⟩ := hx
  rw [Submonoid.smul_def, Algebra.smul_def, algebraMap_perfectClosure] at hax
  exact eq_zero_of_perfectClosure_of_mul_eq_zero K p (nonZeroDivisors.coe_ne_zero a) hax

/-- The perfect closure of a Bézout domain of characteristic `p` is flat over it: over a domain
whose finitely generated ideals are principal, flatness is torsionfreeness. -/
theorem flat_perfectClosure [IsDomain K] [IsBezout K] : Module.Flat K (PerfectClosure K p) :=
  Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr (torsion_perfectClosure_eq_bot K p)

/-- The perfect closure of a ring of characteristic `p` is formally unramified over it: every
element of the perfect closure is a `p`-th power, so the universal derivation vanishes on it and
`Ω[PerfectClosure K p⁄K] = 0`. -/
theorem formallyUnramified_perfectClosure :
    Algebra.FormallyUnramified K (PerfectClosure K p) := by
  have htop : (⊤ : Submodule (PerfectClosure K p) (Ω[PerfectClosure K p⁄K])) = ⊥ := by
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
    rintro w ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (PerfectRing.bijective_frobenius (R := PerfectClosure K p) (p := p)).2 x
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul (PerfectClosure K p),
      CharP.cast_eq_zero, zero_smul]
  refine ⟨(subsingleton_iff_forall_eq 0).mpr fun w => ?_⟩
  simpa using htop.le (Submodule.mem_top (R := PerfectClosure K p) (x := w))

end Flat

section SquareZero

variable (R : Type u) [CommRing R] (p : ℕ) [CharP R p]

/-- The trivial square-zero extension `R[ε]` of a ring of characteristic `p` again has
characteristic `p`, because the natural numbers land in the injective image of `inl`. -/
theorem charP_trivSqZeroExt_self : CharP (TrivSqZeroExt R R) p := by
  refine ⟨fun n => ?_⟩
  rw [← CharP.cast_eq_zero_iff R p n]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa using congrArg TrivSqZeroExt.fst h
  · exact TrivSqZeroExt.ext (by simpa using h) (by simp)

/-- In the trivial square-zero extension of a ring of characteristic `p`, every `p`-th power has
vanishing nilpotent component: `(x + m * ε) ^ p = x ^ p`. -/
theorem snd_pow_char_trivSqZeroExt [Fact p.Prime] (c : TrivSqZeroExt R R) : (c ^ p).snd = 0 := by
  have := charP_trivSqZeroExt_self R p
  have hinr : (TrivSqZeroExt.inr c.snd : TrivSqZeroExt R R) ^ p = 0 :=
    pow_eq_zero_of_le (Fact.out : p.Prime).two_le
      (by rw [pow_two, TrivSqZeroExt.inr_mul_inr])
  rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq c, add_pow_char, hinr, TrivSqZeroExt.inl_pow,
    add_zero, TrivSqZeroExt.snd_inl]

end SquareZero

section Twist

variable (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The ring map `k[T] → Aperf[ε]` sending `T` to `T + ε`, where `Aperf` is the perfect closure of
`k[T]` and `Aperf[ε]` is its trivial square-zero extension. It is the twisted `k[T]`-algebra
structure on `Aperf[ε]` that detects the failure of formal smoothness. -/
noncomputable def perfectClosureDualTwist : Polynomial k →+*
    TrivSqZeroExt (PerfectClosure (Polynomial k) p) (PerfectClosure (Polynomial k) p) :=
  Polynomial.eval₂RingHom
    ((TrivSqZeroExt.inlHom _ _).comp ((PerfectClosure.of (Polynomial k) p).comp Polynomial.C))
    (TrivSqZeroExt.inl (PerfectClosure.of (Polynomial k) p Polynomial.X)
      + TrivSqZeroExt.inr 1)

/-- The twisted structure map agrees with the untwisted one on constant polynomials. -/
@[simp]
theorem perfectClosureDualTwist_C (a : k) :
    perfectClosureDualTwist k p (Polynomial.C a)
      = TrivSqZeroExt.inl (PerfectClosure.of (Polynomial k) p (Polynomial.C a)) :=
  Polynomial.eval₂_C _ _

/-- The twisted structure map sends the variable `T` to `T + ε`. -/
@[simp]
theorem perfectClosureDualTwist_X :
    perfectClosureDualTwist k p Polynomial.X
      = TrivSqZeroExt.inl (PerfectClosure.of (Polynomial k) p Polynomial.X)
        + TrivSqZeroExt.inr 1 :=
  Polynomial.eval₂_X _ _

/-- The class of `ε` in the quotient of `Aperf[ε]` by the square-zero ideal vanishes. -/
theorem quotient_mk_inr_one_eq_zero :
    Ideal.Quotient.mk
        (TrivSqZeroExt.kerIdeal (PerfectClosure (Polynomial k) p)
          (PerfectClosure (Polynomial k) p))
        (TrivSqZeroExt.inr 1) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, TrivSqZeroExt.mem_kerIdeal_iff_inr]
  simp

/-- Reducing the twisted structure map modulo the square-zero ideal recovers the untwisted one,
because the two differ exactly by `ε`. -/
theorem quotient_mk_comp_perfectClosureDualTwist :
    (Ideal.Quotient.mk (TrivSqZeroExt.kerIdeal (PerfectClosure (Polynomial k) p)
          (PerfectClosure (Polynomial k) p))).comp
        ((TrivSqZeroExt.inlHom (PerfectClosure (Polynomial k) p)
            (PerfectClosure (Polynomial k) p)).comp (PerfectClosure.of (Polynomial k) p))
      = (Ideal.Quotient.mk (TrivSqZeroExt.kerIdeal (PerfectClosure (Polynomial k) p)
          (PerfectClosure (Polynomial k) p))).comp (perfectClosureDualTwist k p) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp
  · simp [quotient_mk_inr_one_eq_zero k p]

/-- There is no ring map from the perfect closure of `k[T]` to `Aperf[ε]` compatible with the
twisted structure map `T ↦ T + ε`. Indeed `T` is a `p`-th power in the perfect closure, while
`p`-th powers in `Aperf[ε]` have vanishing `ε`-component and `T + ε` does not. -/
theorem not_exists_ringHom_comp_eq_perfectClosureDualTwist [IsDomain k] :
    ¬ ∃ g : PerfectClosure (Polynomial k) p →+*
        TrivSqZeroExt (PerfectClosure (Polynomial k) p) (PerfectClosure (Polynomial k) p),
      g.comp (PerfectClosure.of (Polynomial k) p) = perfectClosureDualTwist k p := by
  rintro ⟨g, hg⟩
  have hu : (PerfectClosure.mk (Polynomial k) p (1, Polynomial.X)) ^ p
      = PerfectClosure.of (Polynomial k) p Polynomial.X := by
    rw [PerfectClosure.mk_pow]
    exact PerfectClosure.mk_succ_pow (Polynomial k) p 0 Polynomial.X
  have hgx : g (PerfectClosure.mk (Polynomial k) p (1, Polynomial.X)) ^ p
      = TrivSqZeroExt.inl (PerfectClosure.of (Polynomial k) p Polynomial.X)
        + TrivSqZeroExt.inr 1 := by
    rw [← map_pow, hu, ← RingHom.comp_apply, hg, perfectClosureDualTwist_X]
  have h1 := snd_pow_char_trivSqZeroExt (PerfectClosure (Polynomial k) p) p
    (g (PerfectClosure.mk (Polynomial k) p (1, Polynomial.X)))
  rw [hgx] at h1
  simp at h1

/-- The perfect closure of a polynomial ring over a domain of characteristic `p` is not formally
étale over that polynomial ring. The square-zero extension `Aperf[ε]`, made a `k[T]`-algebra by
`T ↦ T + ε`, receives the perfect closure modulo `ε` but admits no lift over `ε`. -/
theorem not_formallyEtale_perfectClosure_polynomialRing [IsDomain k] :
    ¬ Algebra.FormallyEtale (Polynomial k) (PerfectClosure (Polynomial k) p) := by
  intro hetale
  let : Algebra (Polynomial k)
      (TrivSqZeroExt (PerfectClosure (Polynomial k) p) (PerfectClosure (Polynomial k) p)) :=
    (perfectClosureDualTwist k p).toAlgebra
  have halg : algebraMap (Polynomial k)
      (TrivSqZeroExt (PerfectClosure (Polynomial k) p) (PerfectClosure (Polynomial k) p))
      = perfectClosureDualTwist k p := RingHom.algebraMap_toAlgebra _
  have hcomm : ∀ a : Polynomial k,
      ((Ideal.Quotient.mk (TrivSqZeroExt.kerIdeal (PerfectClosure (Polynomial k) p)
            (PerfectClosure (Polynomial k) p))).comp
          (TrivSqZeroExt.inlHom (PerfectClosure (Polynomial k) p)
            (PerfectClosure (Polynomial k) p)))
        (algebraMap (Polynomial k) (PerfectClosure (Polynomial k) p) a)
      = algebraMap (Polynomial k)
          (TrivSqZeroExt (PerfectClosure (Polynomial k) p) (PerfectClosure (Polynomial k) p) ⧸
            TrivSqZeroExt.kerIdeal (PerfectClosure (Polynomial k) p)
              (PerfectClosure (Polynomial k) p)) a := by
    intro a
    rw [← (Ideal.Quotient.mkₐ (Polynomial k) (TrivSqZeroExt.kerIdeal
      (PerfectClosure (Polynomial k) p) (PerfectClosure (Polynomial k) p))).commutes a,
      Ideal.Quotient.mkₐ_eq_mk, halg, algebraMap_perfectClosure]
    exact RingHom.congr_fun (quotient_mk_comp_perfectClosureDualTwist k p) a
  have f : PerfectClosure (Polynomial k) p →ₐ[Polynomial k]
      (TrivSqZeroExt (PerfectClosure (Polynomial k) p) (PerfectClosure (Polynomial k) p) ⧸
        TrivSqZeroExt.kerIdeal (PerfectClosure (Polynomial k) p)
          (PerfectClosure (Polynomial k) p)) :=
    AlgHom.mk ((Ideal.Quotient.mk (TrivSqZeroExt.kerIdeal (PerfectClosure (Polynomial k) p)
      (PerfectClosure (Polynomial k) p))).comp
        (TrivSqZeroExt.inlHom (PerfectClosure (Polynomial k) p)
          (PerfectClosure (Polynomial k) p))) hcomm
  obtain ⟨g, -⟩ := (Algebra.FormallyEtale.comp_bijective (Polynomial k)
    (PerfectClosure (Polynomial k) p)
    (TrivSqZeroExt.kerIdeal (PerfectClosure (Polynomial k) p)
      (PerfectClosure (Polynomial k) p))
    (TrivSqZeroExt.kerIdeal_sq _ _)).surjective f
  refine not_exists_ringHom_comp_eq_perfectClosureDualTwist k p ⟨g.toRingHom, ?_⟩
  refine RingHom.ext fun a => ?_
  have h := g.commutes (R := Polynomial k) a
  rw [algebraMap_perfectClosure, halg] at h
  exact h

end Twist

/-- **Flat and formally unramified is not formally étale**, flatness: the perfect closure of
`𝔽ₚ[T]` is flat over `𝔽ₚ[T]`. -/
@[stacks 0G65 "flatness of the example F_p[T] into its perfect closure"]
public theorem flat_perfectClosure_polynomial (p : ℕ) [Fact p.Prime] :
    Module.Flat (Polynomial (ZMod p)) (PerfectClosure (Polynomial (ZMod p)) p) :=
  flat_perfectClosure (Polynomial (ZMod p)) p

/-- **Flat and formally unramified is not formally étale**, formal unramifiedness: the perfect
closure of `𝔽ₚ[T]` is formally unramified over `𝔽ₚ[T]`. -/
@[stacks 0G65 "formal unramifiedness of the example F_p[T] into its perfect closure"]
public theorem formallyUnramified_perfectClosure_polynomial (p : ℕ) [Fact p.Prime] :
    Algebra.FormallyUnramified (Polynomial (ZMod p)) (PerfectClosure (Polynomial (ZMod p)) p) :=
  formallyUnramified_perfectClosure (Polynomial (ZMod p)) p

/-- **Flat and formally unramified is not formally étale**, the negative conjunct: the perfect
closure of `𝔽ₚ[T]` is not formally étale over `𝔽ₚ[T]`. -/
@[stacks 0G65 "the example F_p[T] into its perfect closure is not formally etale"]
public theorem not_formallyEtale_perfectClosure_polynomial (p : ℕ) [Fact p.Prime] :
    ¬ Algebra.FormallyEtale (Polynomial (ZMod p)) (PerfectClosure (Polynomial (ZMod p)) p) :=
  not_formallyEtale_perfectClosure_polynomialRing (ZMod p) p

end Stacks.Examples

end
