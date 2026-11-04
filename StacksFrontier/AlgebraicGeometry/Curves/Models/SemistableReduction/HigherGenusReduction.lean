module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SeparableDegreeFibres
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModel
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.BaseChange
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.Curves

/-!
# Reducing semistable reduction in genus at least two to the local statement

Let `R` be a discrete valuation ring with fraction field `K` and let `C` be a smooth projective
curve over `K` of genus `g ≥ 2` with `H⁰(C, 𝒪_C) = K`. The proof of [Stacks, Tag 0CEI] picks a
prime `ℓ > 768 g` invertible in `R`, passes to a finite separable extension `K'/K` over which `C`
acquires a rational point and its full `ℓ`-torsion in the Picard group, and then works over each
localization `R'_𝔪` of the integral closure `R'` of `R` in `K'`: there the minimal model of
`C_{K'}` is a regular proper model without exceptional curves of the first kind, and the local
statement shows that it is at-worst-nodal of relative dimension one.

## Main results

* `Stacks.Models.exists_hasSemistableReductionAtMaximalIdeals_of_local` — the reduction step,
  with the existence of minimal models ([Stacks, Tag 0C2W]), the torsion statement
  ([Stacks, Tag 0CDU] (2)) and the local statement of [Stacks, Tag 0CEI] as premises. The
  degree of `K'/K` is bounded by `semistableReductionDegreeBound g` ([Stacks, Tag 0CEJ]).

## Implementation notes

Of the first two primes `ℓ₁ < ℓ₂` larger than `768 g`, at most one is the characteristic of the
residue field of `R`, so one of them is a unit in `R`. The bound of [Stacks, Tag 0CEJ] is
computed with `ℓ₂`, which dominates the bound for either choice.

## References

* [Stacks Project, Tag 0CEI](https://stacks.math.columbia.edu/tag/0CEI)
* [Stacks Project, Tag 0CEJ](https://stacks.math.columbia.edu/tag/0CEJ)
* [Stacks Project, Tag 0CDN](https://stacks.math.columbia.edu/tag/0CDN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models

/-- For every `n` and every field `k`, one of the first two primes larger than `n` is nonzero in
`k`. -/
theorem exists_prime_lt_le_nth_ne_zero (k : Type*) [Field k] (n : ℕ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ n < ℓ ∧ ℓ ≤ Nat.nth Nat.Prime (Nat.primeCounting n + 1) ∧
      (ℓ : k) ≠ 0 := by
  set ℓ₁ := Nat.nth Nat.Prime (Nat.primeCounting n)
  set ℓ₂ := Nat.nth Nat.Prime (Nat.primeCounting n + 1)
  have h₁ : n < ℓ₁ := Nat.le_nth_count Nat.infinite_setOfPred_prime (n + 1)
  have h₁₂ : ℓ₁ < ℓ₂ := Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self _)
  have hp₁ : ℓ₁.Prime := Nat.prime_nth_prime _
  have hp₂ : ℓ₂.Prime := Nat.prime_nth_prime _
  by_cases hz : (ℓ₁ : k) = 0
  · refine ⟨ℓ₂, hp₂, h₁.trans h₁₂, le_rfl, fun hz₂ => ?_⟩
    have h := Nat.dvd_gcd ((ringChar.spec k ℓ₁).mp hz) ((ringChar.spec k ℓ₂).mp hz₂)
    rw [((Nat.coprime_primes hp₁ hp₂).mpr h₁₂.ne).gcd_eq_one, Nat.dvd_one] at h
    exact CharP.ringChar_ne_one h
  · exact ⟨ℓ₁, hp₁, h₁, h₁₂.le, hz⟩

/-- **The reduction step of [Stacks, Tag 0CEI].** Let `R` be a discrete valuation ring with
fraction field `K` and `C` a smooth projective curve over `K` of genus `g ≥ 2` with
`H⁰(C, 𝒪_C) = K`. Granting the existence of minimal models over discrete valuation rings
([Stacks, Tag 0C2W]), the visibility of the full `n`-torsion after a bounded separable extension
([Stacks, Tag 0CDU] (2)) and the local statement of [Stacks, Tag 0CEI], there is a finite
separable extension `K'/K` of degree at most `semistableReductionDegreeBound g`
([Stacks, Tag 0CEJ]) such that `C_{K'}` has semistable reduction over the localization of the
integral closure of `R` in `K'` at every maximal ideal. -/
theorem exists_hasSemistableReductionAtMaximalIdeals_of_local
    (h0C2W : ∀ (A L : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field L]
      [Algebra A L] [IsFractionRing A L] {C : Scheme.{u}} (c : C ⟶ Spec (.of L)) [IsCurve L c]
      [Smooth c] (_ : IsProjective c) [IsIso ((Scheme.ΓSpecIso (.of L)).inv ≫ c.appTop)],
      ∃ (X : Scheme.{u}) (p : X ⟶ Spec (.of A))
        (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap A L)))),
        IsMinimalModel c p e)
    (h0CDU : ∀ (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f]
      [Smooth f] [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (n : ℕ),
      IsUnit (n : k) → 2 ≤ genus f →
      ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧
        Algebra.IsSeparable k k' ∧
        Module.finrank k k' ≤ (2 * genus f - 2) * (n ^ (2 * genus f)).factorial ∧
        (∃ x : Spec (.of k') ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))),
          x ≫ pullback.snd _ _ = 𝟙 _) ∧
        Nonempty (AddSubgroup.torsionBy (Stacks.Picard.ofScheme
          (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) (n : ℤ) ≃+
          (Fin (2 * genus f) → ZMod n)))
    (hlocal : ∀ (S : RegularProperModelSituation.{u}), ¬ S.X.HasExceptionalCurveOfFirstKind →
      ∀ (p : Spec (.of S.K) ⟶ S.C), p ≫ S.C_to_K = 𝟙 _ → 2 ≤ genus S.C_to_K →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], 768 * genus S.C_to_K < ℓ → (ℓ : S.k) ≠ 0 →
      Nonempty (AddSubgroup.torsionBy (Stacks.Picard.ofScheme S.C) (ℓ : ℤ) ≃+
        (Fin (2 * genus S.C_to_K) → ZMod ℓ)) →
      IsAtWorstNodalOfRelativeDimensionOne S.X_to_R)
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c]
    (hproj : IsProjective c) [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)]
    (hg : 2 ≤ genus c) :
    haveI : IsProper c := hproj.isProper
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
      (_ : IsScalarTower R K K'), FiniteDimensional K K' ∧ Algebra.IsSeparable K K' ∧
      Module.finrank K K' ≤ AlgebraicGeometry.SemistableReduction.semistableReductionDegreeBound
        (genus c) ∧
      HasSemistableReductionAtMaximalIdeals R K'
        (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
        (hproj.pullback_snd _) := by
  have : IsProper c := hproj.isProper
  -- a prime `ℓ > 768 g` which is a unit in `R`, hence in `K`
  obtain ⟨ℓ, hℓ, hℓg, hℓle, hℓk⟩ :=
    exists_prime_lt_le_nth_ne_zero (IsLocalRing.ResidueField R) (768 * genus c)
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓR : IsUnit (ℓ : R) := by
    rwa [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast]
  have hℓK : IsUnit (ℓ : K) := by simpa using hℓR.map (algebraMap R K)
  -- the extension `K'/K` given by Tag 0CDU (2)
  obtain ⟨K', _, _, hfin, hsep, hdeg, ⟨x, hx⟩, ⟨τ⟩⟩ := h0CDU K c ℓ hℓK hg
  let : Algebra R K' := ((algebraMap K K').comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨K', inferInstance, inferInstance, inferInstance, inferInstance, hfin, hsep,
    hdeg.trans (Nat.mul_le_mul_left _ (Nat.factorial_le (Nat.pow_le_pow_left hℓle _))), ?_⟩
  -- semistable reduction over each localization `A` of the integral closure at a maximal ideal
  intro 𝔪 _ A _ _ _ _ _ _ _ _
  obtain ⟨X, p, e, hmin⟩ := h0C2W A K'
    (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K')))) (hproj.pullback_snd _)
  have := hmin.isProper
  obtain ⟨_, _, _, hover⟩ := hmin.isModel
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  let S : RegularProperModelSituation.{u} :=
    { R := A, K := K', k := IsLocalRing.ResidueField A, residueEquiv := AlgEquiv.refl,
      C := pullback c (Spec.map (CommRingCat.ofHom (algebraMap K K'))),
      C_to_K := pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K'))),
      X := X, X_to_R := p, regular := hmin.regular, genericFiberIso := e,
      genericFiberIso_over_K := hover, π := π, uniformizer := hπ,
      curveProjective := hmin.curveProjective }
  have hgen : genus S.C_to_K = genus c := genus_pullback_snd_eq K K' (algebraMap K K') c
  have hk : (ℓ : S.k) ≠ 0 := by
    have hA : IsUnit (ℓ : A) := by
      simpa using (hℓR.map (algebraMap R (integralClosure R K'))).map
        (algebraMap (integralClosure R K') A)
    show (ℓ : IsLocalRing.ResidueField A) ≠ 0
    rwa [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_ne_zero_iff_isUnit]
  have hτ : Nonempty (AddSubgroup.torsionBy (Stacks.Picard.ofScheme S.C) (ℓ : ℤ) ≃+
      (Fin (2 * genus S.C_to_K) → ZMod ℓ)) := by
    rw [hgen]
    exact ⟨τ⟩
  exact ⟨X, p, e, hmin.isModel, hmin.isProper, hlocal S hmin.not_hasExceptionalCurveOfFirstKind
    x hx (hgen ▸ hg) ℓ (hgen ▸ hℓg) hk hτ⟩

end Stacks.Models

end
