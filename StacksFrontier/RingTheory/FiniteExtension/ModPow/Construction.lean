module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.PicardGroup

/-!
# Finite extensions modulo powers of a nonzerodivisor

Let `A' ⊂ A` be an extension of rings and `f ∈ A'` such that `A` is finite over `A'`, `f` is a
nonzerodivisor on `A`, and `A'_f = A_f`. Then there is `n₀ > 0` such that for all `n ≥ n₀`, every
ring `B'`, every nonzerodivisor `g ∈ B'` and every ring isomorphism `φ' : A'/f^n A' ≃ B'/g^n B'`
with `φ'(f) ≡ g`, there are a finite ring extension `B' ⊂ B` and a ring isomorphism
`φ : A/fA ≃ B/gB` compatible with `φ'`. The ring `B` is `g^{-t} N ⊆ B'_g`, where `f^t A ⊆ A'` and
`N ⊆ B'` is the preimage of `φ'(f^t A / f^n A')`.

This file constructs `B` and shows that it is finite over `B'`; the isomorphism `φ` and the
functoriality of the construction are in the later files of this directory.

## Main definitions

* `LocalizationEq`: every `a ∈ A` satisfies `f^k a ∈ A'` for some `k`.
* `reductionMap`: the reduction map `R'/f^n R' → R/fR`.
* `bSubalg`: the `B'`-subalgebra `g^{-t} N` of `Localization.Away g`.

## Main results

* `exists_pow_mul_mem_range_algebraMap`: there is `t > 0` with `f^t A ⊆ A'`.
* `bSubalg_algebraMap_injective`: `B' → bSubalg` is injective when `g` is a nonzerodivisor.
* `bSubalg_finite`: `bSubalg` is a finite `B'`-module.

## Implementation notes

A ring extension `R' ⊂ R` is an `Algebra R' R` instance with injective `algebraMap`. The quotients
`R'/f^n R'` and `R/fR` are quotients by `Ideal.span {f^n}` and `Ideal.span {algebraMap R' R f}`.

## References

* [Stacks Project, Tag 0GLT](https://stacks.math.columbia.edu/tag/0GLT)
-/

@[expose] public section

universe u v w

/-- Every `a ∈ A` becomes, after multiplying by a sufficiently high power of `f`, the image of an
element of `A'`; equivalently, the natural injection `A'_f → A_f` is an isomorphism. -/
def LocalizationEq (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') : Prop :=
  ∀ a : A, ∃ (k : ℕ) (a' : A'), algebraMap A' A f ^ k * a = algebraMap A' A a'

/-- The canonical reduction ring homomorphism `R'/f^n R' → R/fR`, induced by the
inclusion `R' ↪ R` followed by `R → R/fR`, for `n ≥ 1`. -/
noncomputable def reductionMap (R' : Type u) (R : Type v) [CommRing R'] [CommRing R] [Algebra R' R]
    (f : R') (n : ℕ) (hn : 1 ≤ n) :
    (R' ⧸ Ideal.span {f ^ n}) →+* (R ⧸ Ideal.span {algebraMap R' R f}) :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (algebraMap R' R)) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
      map_mul, map_pow]
    exact Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _)

/-- There is an integer `t > 0` such that `f^t A ⊆ A'`: for every `a ∈ A`, the element `f^t · a`
lies in the image of `A'`. -/
lemma exists_pow_mul_mem_range_algebraMap (A' : Type u) (A : Type v) [CommRing A'] [CommRing A]
  [Algebra A' A]
    [hfin : Module.Finite A' A] (f : A') (hloc : LocalizationEq A' A f) :
    ∃ t : ℕ, 0 < t ∧
      ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a' := by
  obtain ⟨s, hs⟩ := hfin.fg_top
  choose k b hkb using hloc
  set t := max 1 (s.sup k) with ht_def
  have ht0 : 0 < t := by
    have : 1 ≤ t := le_max_left _ _
    omega
  have hkle : ∀ a ∈ s, k a ≤ t := by
    intro a ha
    have : k a ≤ s.sup k := Finset.le_sup ha
    omega
  refine ⟨t, ht0, ?_⟩
  intro a
  have ha : a ∈ Submodule.span A' (s : Set A) := by rw [hs]; exact Submodule.mem_top
  rw [Submodule.mem_span_finset] at ha
  obtain ⟨c, _, rfl⟩ := ha
  refine ⟨∑ x ∈ s, c x * f ^ (t - k x) * b x, ?_⟩
  rw [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Algebra.smul_def]
  rw [map_mul, map_mul, map_pow]
  set F := algebraMap A' A f with hF
  rw [← pow_sub_mul_pow F (hkle x hx)]
  have h := hkb x
  linear_combination (F ^ (t - k x) * algebraMap A' A (c x)) * h

/-- The ideal `M̄ ⊆ A'/f^n A'` of classes of `A'`-representatives `a'` of `f^t · a`, `a ∈ A`. -/
noncomputable def mbarIdeal (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) : Ideal (A' ⧸ Ideal.span {f ^ n}) :=
  Ideal.span { x : A' ⧸ Ideal.span {f ^ n} |
    ∃ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a' ∧
      x = Ideal.Quotient.mk _ a' }

/-- The ideal `N ⊆ B'`: the preimage under `B' → B'/g^n B'` of `φ'(M̄)`. -/
noncomputable def nIdeal (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n})) : Ideal B' :=
  Ideal.comap (Ideal.Quotient.mk (Ideal.span {g ^ n}))
    (Ideal.map (φ' : (A' ⧸ Ideal.span {f ^ n}) →+* _) (mbarIdeal A' A f t n))

/-- The set `g^{-t} N ⊆ Localization.Away g`: those `x` with `g^t · x` the image of some
`b ∈ N`. -/
noncomputable def bCarrier (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n})) :
    Set (Localization.Away g) :=
  { x | ∃ b : B', algebraMap B' (Localization.Away g) b
          = (algebraMap B' (Localization.Away g) g) ^ t * x
        ∧ b ∈ nIdeal A' A f t n B' g φ' }

/-- If `φ'` sends the class of `f` to the class of `g`, then it sends the class of `f ^ t` to the
class of `g ^ t`. -/
lemma map_mk_pow_eq_mk_pow {A' : Type u} {B' : Type w} [CommRing A'] [CommRing B']
    (f : A') (g : B') (t : ℕ) {n : ℕ}
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g) :
    φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) (f ^ t))
      = Ideal.Quotient.mk (Ideal.span {g ^ n}) (g ^ t) := by
  rw [map_pow, map_pow, hφ', ← map_pow]

/-- If `φ'` sends the class of `f` to the class of `g`, then `φ'⁻¹` sends the class of `g` to the
class of `f`. -/
lemma symm_map_mk_eq_mk {A' : Type u} {B' : Type w} [CommRing A'] [CommRing B']
    (f : A') (g : B') {n : ℕ}
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g) :
    φ'.symm (Ideal.Quotient.mk (Ideal.span {g ^ n}) g)
      = Ideal.Quotient.mk (Ideal.span {f ^ n}) f := by
  rw [← hφ', φ'.symm_apply_apply]

/-- If `φ'` sends the class of `f` to the class of `g`, then `φ'⁻¹` sends the class of `g ^ t` to
the class of `f ^ t`. -/
lemma symm_map_mk_pow_eq_mk_pow {A' : Type u} {B' : Type w} [CommRing A'] [CommRing B']
    (f : A') (g : B') (t : ℕ) {n : ℕ}
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g) :
    φ'.symm (Ideal.Quotient.mk (Ideal.span {g ^ n}) (g ^ t))
      = Ideal.Quotient.mk (Ideal.span {f ^ n}) (f ^ t) := by
  rw [← map_mk_pow_eq_mk_pow f g t φ' hφ', φ'.symm_apply_apply]

/-- `g^t ∈ N`, since `φ'(f^t) = g^t` and `f^t ∈ M̄`. -/
lemma gPow_mem_nIdeal (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g) :
    g ^ t ∈ nIdeal A' A f t n B' g φ' := by
  rw [nIdeal, Ideal.mem_comap, ← map_mk_pow_eq_mk_pow f g t φ' hφ']
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨1, f ^ t, by rw [mul_one, map_pow], rfl⟩)

/-- `1 ∈ bCarrier`. -/
lemma one_mem_bCarrier (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g) :
    (1 : Localization.Away g) ∈ bCarrier A' A f t n B' g φ' := by
  refine ⟨g ^ t, ?_, gPow_mem_nIdeal A' A f t n B' g φ' hφ'⟩
  rw [map_pow, mul_one]

/-- `0 ∈ bCarrier`. -/
lemma zero_mem_bCarrier (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n})) :
    (0 : Localization.Away g) ∈ bCarrier A' A f t n B' g φ' := by
  refine ⟨0, ?_, Submodule.zero_mem _⟩
  rw [map_zero, mul_zero]

/-- `bCarrier` is closed under addition. -/
lemma add_mem_bCarrier (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    {x y : Localization.Away g}
    (hx : x ∈ bCarrier A' A f t n B' g φ') (hy : y ∈ bCarrier A' A f t n B' g φ') :
    x + y ∈ bCarrier A' A f t n B' g φ' := by
  obtain ⟨b1, hb1, hb1N⟩ := hx
  obtain ⟨b2, hb2, hb2N⟩ := hy
  refine ⟨b1 + b2, ?_, Ideal.add_mem _ hb1N hb2N⟩
  rw [map_add, hb1, hb2, mul_add]

/-- The image of every `b' ∈ B'` in `Localization.Away g` lies in `bCarrier`. -/
lemma algebraMap_mem_bCarrier (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (b' : B') :
    algebraMap B' (Localization.Away g) b' ∈ bCarrier A' A f t n B' g φ' := by
  refine ⟨g ^ t * b', ?_, Ideal.mul_mem_right b' _ (gPow_mem_nIdeal A' A f t n B' g φ' hφ')⟩
  rw [map_mul, map_pow]

/-- For `b₁, b₂ ∈ N` there is `c ∈ N` with `b₁ b₂ = g^t · c`. -/
lemma exists_mem_nIdeal_mul_eq (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (b₁ b₂ : B') (hb₁ : b₁ ∈ nIdeal A' A f t n B' g φ')
    (hb₂ : b₂ ∈ nIdeal A' A f t n B' g φ') :
    ∃ c, c ∈ nIdeal A' A f t n B' g φ' ∧ b₁ * b₂ = g ^ t * c := by
  have hφft := map_mk_pow_eq_mk_pow f g t φ' hφ'
  have Mbar_mul_dvd : ∀ u ∈ mbarIdeal A' A f t n * mbarIdeal A' A f t n,
      ∃ v ∈ mbarIdeal A' A f t n,
        u = Ideal.Quotient.mk (Ideal.span {f ^ n}) (f ^ t) * v := by
    have hsub : mbarIdeal A' A f t n * mbarIdeal A' A f t n ≤
        Ideal.span {Ideal.Quotient.mk (Ideal.span {f ^ n}) (f ^ t)} * mbarIdeal A' A f t n := by
      apply Ideal.mul_le.mpr
      intro u₁ hu₁ u₂ hu₂
      refine Submodule.span_induction (p := fun u₁ _ =>
          u₁ * u₂ ∈ Ideal.span {Ideal.Quotient.mk (Ideal.span {f ^ n}) (f ^ t)}
            * mbarIdeal A' A f t n) ?_ ?_ ?_ ?_ hu₁
      · rintro x₁ ⟨a₁, a₁', ha₁, rfl⟩
        refine Submodule.span_induction (p := fun u₂ _ =>
            Ideal.Quotient.mk (Ideal.span {f ^ n}) a₁' * u₂ ∈
              Ideal.span {Ideal.Quotient.mk (Ideal.span {f ^ n}) (f ^ t)}
                * mbarIdeal A' A f t n) ?_ ?_ ?_ ?_ hu₂
        · rintro x₂ ⟨a₂, a₂', ha₂, rfl⟩
          obtain ⟨w', hw'⟩ := ht (a₁ * a₂)
          have hAeq : algebraMap A' A (a₁' * a₂') = algebraMap A' A (f ^ t * w') := by
            rw [map_mul, map_mul, map_pow, ← ha₁, ← ha₂, ← hw']; ring
          have hA'eq : a₁' * a₂' = f ^ t * w' := hinj hAeq
          have hw'_mem : Ideal.Quotient.mk (Ideal.span {f ^ n}) w' ∈ mbarIdeal A' A f t n :=
            Ideal.subset_span ⟨a₁ * a₂, w', hw', rfl⟩
          have heq : Ideal.Quotient.mk (Ideal.span {f ^ n}) a₁'
              * Ideal.Quotient.mk (Ideal.span {f ^ n}) a₂'
              = Ideal.Quotient.mk (Ideal.span {f ^ n}) (f ^ t)
                * Ideal.Quotient.mk (Ideal.span {f ^ n}) w' := by
            rw [← map_mul, ← map_mul, hA'eq]
          rw [heq]
          exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton _)) hw'_mem
        · simp
        · intro y z _ _ hy hz; rw [mul_add]; exact Ideal.add_mem _ hy hz
        · intro a y _ hy; rw [mul_smul_comm]; exact Ideal.mul_mem_left _ _ hy
      · simp
      · intro y z _ _ hy hz; rw [add_mul]; exact Ideal.add_mem _ hy hz
      · intro a y _ hy; rw [smul_mul_assoc]; exact Ideal.mul_mem_left _ _ hy
    intro u hu
    have hu' := hsub hu
    rw [Ideal.mem_span_singleton_mul] at hu'
    obtain ⟨v, hvM, hveq⟩ := hu'
    exact ⟨v, hvM, hveq.symm⟩
  rw [nIdeal, Ideal.mem_comap] at hb₁ hb₂
  obtain ⟨u₁, hu₁M, hu₁eq⟩ := (Ideal.mem_map_iff_of_surjective _ φ'.surjective).mp hb₁
  obtain ⟨u₂, hu₂M, hu₂eq⟩ := (Ideal.mem_map_iff_of_surjective _ φ'.surjective).mp hb₂
  obtain ⟨v, hvM, hveq⟩ := Mbar_mul_dvd (u₁ * u₂) (Ideal.mul_mem_mul hu₁M hu₂M)
  obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (φ' v)
  have hdN : d ∈ nIdeal A' A f t n B' g φ' := by
    rw [nIdeal, Ideal.mem_comap, hd]
    exact Ideal.mem_map_of_mem _ hvM
  have hmkeq : Ideal.Quotient.mk (Ideal.span {g ^ n}) (b₁ * b₂)
      = Ideal.Quotient.mk (Ideal.span {g ^ n}) (g ^ t * d) := by
    rw [map_mul, ← hu₁eq, ← hu₂eq, ← map_mul, hveq, map_mul, hφft, map_mul, hd]
  have hsub : b₁ * b₂ - g ^ t * d ∈ Ideal.span {g ^ n} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, hmkeq]
  rw [Ideal.mem_span_singleton] at hsub
  obtain ⟨e, he⟩ := hsub
  have hnt : g ^ n = g ^ t * g ^ (n - t) := (pow_mul_pow_sub g (by omega)).symm
  have hntt : g ^ (n - t) = g ^ t * g ^ (n - t - t) := (pow_mul_pow_sub g (by omega)).symm
  refine ⟨d + g ^ (n - t) * e, ?_, ?_⟩
  · apply Ideal.add_mem _ hdN
    rw [hntt, mul_assoc]
    exact Ideal.mul_mem_right _ _ (gPow_mem_nIdeal A' A f t n B' g φ' hφ')
  · have hbb : b₁ * b₂ = g ^ t * d + g ^ n * e := by rw [← he]; ring
    rw [hbb, hnt]; ring

/-- `bCarrier` is closed under multiplication. -/
lemma mul_mem_bCarrier (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    {x y : Localization.Away g}
    (hx : x ∈ bCarrier A' A f t n B' g φ') (hy : y ∈ bCarrier A' A f t n B' g φ') :
    x * y ∈ bCarrier A' A f t n B' g φ' := by
  obtain ⟨b₁, hb₁eq, hb₁N⟩ := hx
  obtain ⟨b₂, hb₂eq, hb₂N⟩ := hy
  obtain ⟨c, hcN, hbc⟩ :=
    exists_mem_nIdeal_mul_eq A' A f t n B' g φ' hinj ht hn2t hφ' b₁ b₂ hb₁N hb₂N
  refine ⟨c, ?_, hcN⟩
  set G := algebraMap B' (Localization.Away g) g with hGdef
  have hGunit : IsUnit (G ^ t) := (IsLocalization.Away.algebraMap_isUnit g).pow t
  have hmaps : algebraMap B' (Localization.Away g) (b₁ * b₂)
      = G ^ t * algebraMap B' (Localization.Away g) c := by
    rw [hbc, map_mul, map_pow]
  rw [map_mul, hb₁eq, hb₂eq] at hmaps
  have : G ^ t * (G ^ t * (x * y)) = G ^ t * algebraMap B' (Localization.Away g) c := by
    rw [← hmaps]; ring
  have hcancel := hGunit.mul_left_cancel this
  exact hcancel.symm

/-- The `B'`-subalgebra of `Localization.Away g` with carrier `g^{-t} N`. -/
noncomputable def bSubalg (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g) :
    Subalgebra B' (Localization.Away g) where
  carrier := bCarrier A' A f t n B' g φ'
  one_mem' := one_mem_bCarrier A' A f t n B' g φ' hφ'
  mul_mem' := mul_mem_bCarrier A' A f t n B' g φ' hinj ht hn2t hφ'
  zero_mem' := zero_mem_bCarrier A' A f t n B' g φ'
  add_mem' := add_mem_bCarrier A' A f t n B' g φ'
  algebraMap_mem' := algebraMap_mem_bCarrier A' A f t n B' g φ' hφ'

/-- If `g` is a nonzerodivisor, then `B' → bSubalg` is injective. -/
lemma bSubalg_algebraMap_injective (A' : Type u) (A : Type v) [CommRing A'] [CommRing A]
    [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (hg : g ∈ nonZeroDivisors B') :
    Function.Injective (algebraMap B' (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ')) := by
  set S := bSubalg A' A f t n B' g φ' hinj ht hn2t hφ' with hS
  have hcomp : ∀ b, S.val (algebraMap B' S b) = algebraMap B' (Localization.Away g) b := by
    simp
  have hloc : Function.Injective (algebraMap B' (Localization.Away g)) :=
    IsLocalization.injective (M := Submonoid.powers g) (Localization.Away g)
      (Submonoid.powers_le.mpr hg)
  intro x y hxy
  apply hloc
  rw [← hcomp, ← hcomp, hxy]

/-- If `A` is finite over `A'`, then `bSubalg` is a finite `B'`-module. -/
lemma bSubalg_finite (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    [Module.Finite A' A]
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g) :
    Module.Finite B' (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') := by
  set S := bSubalg A' A f t n B' g φ' hinj ht hn2t hφ' with hSdef
  set N := nIdeal A' A f t n B' g φ' with hNdef
  have hNFG : (N : Submodule B' B').FG := by
    set M := mbarIdeal A' A f t n with hMdef
    have hMfin : Module.Finite A' (Submodule.restrictScalars A' M) := by
      set arep : A → A' := fun a => (ht a).choose with hareptodef
      have harep : ∀ a, algebraMap A' A f ^ t * a = algebraMap A' A (arep a) :=
        fun a => (ht a).choose_spec
      have harep_add : ∀ a₁ a₂, arep (a₁ + a₂) = arep a₁ + arep a₂ := by
        intro a₁ a₂
        apply hinj
        rw [map_add, ← harep, ← harep, ← harep, mul_add]
      have harep_smul : ∀ (r : A') (a : A), arep (r • a) = r * arep a := by
        intro r a
        apply hinj
        rw [map_mul, ← harep, ← harep, Algebra.smul_def]; ring
      set θ : A →ₗ[A'] (A' ⧸ Ideal.span {f ^ n}) :=
        { toFun := fun a => Ideal.Quotient.mk (Ideal.span {f ^ n}) (arep a)
          map_add' := by intro a₁ a₂; rw [harep_add, map_add]
          map_smul' := by
            intro r a; rw [RingHom.id_apply, harep_smul, map_mul, Algebra.smul_def]
            rw [Ideal.Quotient.algebraMap_eq] } with hθdef
      have hrange : LinearMap.range θ = Submodule.restrictScalars A' M := by
        apply le_antisymm
        · rw [LinearMap.range_le_iff_comap, eq_top_iff]
          intro a _
          exact Ideal.subset_span ⟨a, arep a, harep a, rfl⟩
        · intro x hx
          have hxM : x ∈ M := hx
          rw [hMdef, mbarIdeal] at hxM
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hxM
          · rintro y ⟨a, a', ha, rfl⟩
            refine ⟨a, ?_⟩
            show Ideal.Quotient.mk (Ideal.span {f ^ n}) (arep a)
                = Ideal.Quotient.mk (Ideal.span {f ^ n}) a'
            rw [Ideal.Quotient.eq]
            have hz : algebraMap A' A (arep a - a') = 0 := by
              rw [map_sub, ← harep, ha, sub_self]
            have h0 : arep a - a' = 0 := hinj (by rw [hz, map_zero])
            rw [sub_eq_zero.mp h0, sub_self]; exact Submodule.zero_mem _
          · exact Submodule.zero_mem _
          · intro y z _ _ hy hz; exact Submodule.add_mem _ hy hz
          · intro c y _ hy
            obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
            obtain ⟨ay, hay⟩ := hy
            refine ⟨c' • ay, ?_⟩
            rw [map_smul, hay, ← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul]
      have hfr : Module.Finite A' (LinearMap.range θ) := Module.Finite.range θ
      rw [hrange] at hfr
      exact hfr
    have hMfin2 : Module.Finite (A' ⧸ Ideal.span {f ^ n}) (Submodule.restrictScalars A' M) :=
      Module.Finite.of_restrictScalars_finite A' (A' ⧸ Ideal.span {f ^ n}) _
    have hMFG : M.FG := Module.Finite.iff_fg.mp hMfin2
    set J : Ideal (B' ⧸ Ideal.span {g ^ n}) :=
      Ideal.map (φ' : (A' ⧸ Ideal.span {f ^ n}) →+* _) M with hJdef
    have hJFG : J.FG := Ideal.FG.map hMFG _
    have hNcomap : ∀ b : B', b ∈ N ↔ Ideal.Quotient.mk (Ideal.span {g ^ n}) b ∈ J := by
      intro b
      rw [hNdef, nIdeal, Ideal.mem_comap]
    have hPN : (Ideal.span {g ^ n} : Ideal B') ≤ N := by
      rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [SetLike.mem_coe, hNcomap]
      have hz : Ideal.Quotient.mk (Ideal.span {g ^ n}) (g ^ n) = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl
      rw [hz]; exact Ideal.zero_mem J
    have hmapeq : Submodule.map ((Ideal.span {g ^ n} : Ideal B').mkQ) (N : Submodule B' B')
        = Submodule.restrictScalars B' J := by
      apply le_antisymm
      · rintro x ⟨b, hbN, rfl⟩
        show (Ideal.span {g ^ n} : Ideal B').mkQ b ∈ J
        exact (hNcomap b).mp hbN
      · intro x hx
        have hxJ : x ∈ J := hx
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact ⟨b, (hNcomap b).mpr hxJ, rfl⟩
    have hBPfin : Module.Finite B' (B' ⧸ Ideal.span {g ^ n}) :=
      Module.Finite.quotient B' (Ideal.span {g ^ n})
    have hJfinBP : Module.Finite (B' ⧸ Ideal.span {g ^ n}) ↥J := Module.Finite.iff_fg.mpr hJFG
    have hJfinB' : Module.Finite B' (Submodule.restrictScalars B' J) := by
      have h : Module.Finite B' ↥J := Module.Finite.trans (B' ⧸ Ideal.span {g ^ n}) ↥J
      exact h
    have hmapFG : (Submodule.map ((Ideal.span {g ^ n} : Ideal B').mkQ)
        (N : Submodule B' B')).FG := by
      rw [hmapeq]
      exact Module.Finite.iff_fg.mp hJfinB'
    have hkerFG : ((N : Submodule B' B') ⊓ ((Ideal.span {g ^ n} : Ideal B').mkQ).ker).FG := by
      rw [Submodule.ker_mkQ, inf_eq_right.mpr hPN]
      exact ⟨{g ^ n}, by rw [Finset.coe_singleton]⟩
    exact Submodule.fg_of_fg_map_of_fg_inf_ker (Ideal.span {g ^ n} : Ideal B').mkQ hmapFG hkerFG
  set Gm := algebraMap B' (Localization.Away g) with hGmdef
  set G := Gm g with hGdef
  have hGunit : IsUnit (G ^ t) := (IsLocalization.Away.algebraMap_isUnit g).pow t
  set ginv : Localization.Away g := ((hGunit.unit⁻¹ : (Localization.Away g)ˣ) : Localization.Away
      g) with hginvdef
  have hGt : G ^ t * ginv = 1 := hGunit.mul_val_inv
  have hmem : ∀ b : B', b ∈ N → ginv * Gm b ∈ bCarrier A' A f t n B' g φ' := by
    intro b hb
    refine ⟨b, ?_, hb⟩
    rw [← hGmdef, ← hGdef, ← mul_assoc, hGt, one_mul]
  let mkBmap : ↥N →ₗ[B'] S :=
    { toFun := fun b => ⟨ginv * Gm b.val, hmem b.val b.property⟩
      map_add' := by
        rintro ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩
        apply Subtype.ext
        show ginv * Gm (b₁ + b₂) = (ginv * Gm b₁) + (ginv * Gm b₂)
        rw [map_add]; ring
      map_smul' := by
        rintro r ⟨b, hb⟩
        apply Subtype.ext
        simp only [RingHom.id_apply, SetLike.val_smul, smul_eq_mul, Algebra.smul_def,
          Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
        rw [map_mul]; ring }
  have hsurj : Function.Surjective mkBmap := by
    rintro ⟨x, hx⟩
    obtain ⟨b, hbeq, hbN⟩ := hx
    refine ⟨⟨b, hbN⟩, ?_⟩
    apply Subtype.ext
    show ginv * Gm b = x
    have hbeq' : Gm b = G ^ t * x := by rw [← hGmdef, ← hGdef] at hbeq; exact hbeq
    rw [hbeq', ← mul_assoc, mul_comm ginv (G ^ t), hGt, one_mul]
  have hNfin : Module.Finite B' ↥N := Module.Finite.iff_fg.mpr hNFG
  exact Module.Finite.of_surjective mkBmap hsurj
