module

public import StacksFrontier.RingTheory.FiniteExtension.ModPow.Construction

/-!
# The forward isomorphism `A/fA → B/gB`

This file continues the construction of
`StacksFrontier.RingTheory.FiniteExtension.ModPow.Construction`. With `B = bSubalg`, the
`B'`-subalgebra `g^{-t} N` of `Localization.Away g`, it defines the elements `g^{-t} · b` of `B`
for `b ∈ N`, chooses for each `a ∈ A` an element `a' ∈ A'` with `f^t a = a'` and a lift `c ∈ N`
of `φ'(a')`, and shows that `a ↦ g^{-t} c` induces a ring homomorphism `φ : A/fA →+* B/gB`.

## Main definitions

* `gPowInv`: a chosen inverse of the image of `g^t` in `Localization.Away g`.
* `mkB`: the element `g^{-t} · b` of `bSubalg` for `b ∈ N`.
* `bSubalg_phiHom`: the ring homomorphism `φ : A/fA →+* B/gB`.
-/

@[expose] public section

universe u v w

/-- A chosen inverse of `G^t = (algebraMap B' (Localization.Away g) g)^t` in
`Localization.Away g` (a unit since `g` is inverted there). -/
noncomputable def gPowInv (B' : Type w) [CommRing B'] (g : B') (t : ℕ) : Localization.Away g :=
  (((IsLocalization.Away.algebraMap_isUnit g).pow t).unit⁻¹ : (Localization.Away g)ˣ)

/-- `(algebraMap B' (Localization.Away g) g) ^ t * gPowInv B' g t = 1`. -/
lemma pow_mul_gPowInv_eq_one (B' : Type w) [CommRing B'] (g : B') (t : ℕ) :
    (algebraMap B' (Localization.Away g) g) ^ t * gPowInv B' g t = 1 := by
  unfold gPowInv
  exact ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).pow t).mul_val_inv

/-- The element `g^{-t}·b` of `B = bSubalg` for `b ∈ N`. -/
noncomputable def mkB (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (b : B') (hb : b ∈ nIdeal A' A f t n B' g φ') :
    bSubalg A' A f t n B' g φ' hinj ht hn2t hφ' :=
  ⟨gPowInv B' g t * algebraMap B' (Localization.Away g) b, by
    change _ ∈ bCarrier A' A f t n B' g φ'
    refine ⟨b, ?_, hb⟩
    rw [← mul_assoc, pow_mul_gPowInv_eq_one B' g t, one_mul]⟩

/-- The underlying element of `mkB b hb` is `gPowInv B' g t * algebraMap b`. -/
lemma mkB_coe (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (b : B') (hb : b ∈ nIdeal A' A f t n B' g φ') :
    ((mkB A' A f t n B' g φ' hinj ht hn2t hφ' b hb :
        bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') : Localization.Away g)
      = gPowInv B' g t * algebraMap B' (Localization.Away g) b := rfl

/-- `g^t · mkB b hb = algebraMap b` in `Localization.Away g`. -/
lemma mkB_spec (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (b : B') (hb : b ∈ nIdeal A' A f t n B' g φ') :
    (algebraMap B' (Localization.Away g) g) ^ t *
      ((mkB A' A f t n B' g φ' hinj ht hn2t hφ' b hb :
          bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') : Localization.Away g)
      = algebraMap B' (Localization.Away g) b := by
  rw [mkB_coe, ← mul_assoc, pow_mul_gPowInv_eq_one B' g t, one_mul]

/-- To check two classes of `B/gB` are equal, it suffices to exhibit `z ∈ B` with
`s - s' = g·z` inside `Localization.Away g`. -/
lemma quotient_mk_eq_of_sub_eq_mul (B' : Type w) [CommRing B'] (g : B')
    (S : Subalgebra B' (Localization.Away g)) (s s' z : S)
    (h : (s : Localization.Away g) - (s' : Localization.Away g)
        = algebraMap B' (Localization.Away g) g * (z : Localization.Away g)) :
    (Ideal.Quotient.mk (Ideal.span {algebraMap B' S g}) s)
      = Ideal.Quotient.mk (Ideal.span {algebraMap B' S g}) s' := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
  refine ⟨z, ?_⟩
  have hcoe : ((z * algebraMap B' S g : S) : Localization.Away g)
      = ((s - s' : S) : Localization.Away g) := by
    push_cast
    rw [h, mul_comm]
  exact Subtype.coe_injective hcoe

/-- If `a'` represents `f^t·a` (`a : A`), then its class lies in `M̄`. -/
lemma mk_arep_mem_mbarIdeal (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (a : A) (a' : A')
    (ha : algebraMap A' A f ^ t * a = algebraMap A' A a') :
    Ideal.Quotient.mk (Ideal.span {f ^ n}) a' ∈ mbarIdeal A' A f t n :=
  Ideal.subset_span ⟨a, a', ha, rfl⟩

/-- Any lift `c` of `φ'(mk a')` (with `mk a' ∈ M̄`) lies in `N`. -/
lemma lift_mem_nIdeal (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (a' : A') (c : B')
    (hM : Ideal.Quotient.mk (Ideal.span {f ^ n}) a' ∈ mbarIdeal A' A f t n)
    (hc : φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) a')
        = Ideal.Quotient.mk (Ideal.span {g ^ n}) c) :
    c ∈ nIdeal A' A f t n B' g φ' := by
  rw [nIdeal, Ideal.mem_comap, ← hc]
  exact Ideal.mem_map_of_mem _ hM

/-- `g^k · m ∈ N` as soon as `t ≤ k`. -/
private lemma pow_mul_mem_nIdeal (A' : Type u) (A : Type v) [CommRing A'] [CommRing A]
    [Algebra A' A] (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g) (m : B') (k : ℕ) (hk : t ≤ k) :
    g ^ k * m ∈ nIdeal A' A f t n B' g φ' := by
  rw [show g ^ k * m = g ^ t * (g ^ (k - t) * m) by
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hk]]
  exact Ideal.mul_mem_right _ _ (gPow_mem_nIdeal A' A f t n B' g φ' hφ')

/-- If `c₁ - c₂ = g · p` with `p ∈ N`, then `mkB c₁` and `mkB c₂` agree in `B/gB`. -/
private lemma mk_mkB_eq_of_sub_eq_mul (A' : Type u) (A : Type v) [CommRing A'] [CommRing A]
    [Algebra A' A] (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (c₁ c₂ p : B') (hN₁ : c₁ ∈ nIdeal A' A f t n B' g φ')
    (hN₂ : c₂ ∈ nIdeal A' A f t n B' g φ') (hp : p ∈ nIdeal A' A f t n B' g φ')
    (h : c₁ - c₂ = g * p) :
    Ideal.Quotient.mk (Ideal.span {(algebraMap B' (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ')
        g)}) (mkB A' A f t n B' g φ' hinj ht hn2t hφ' c₁ hN₁)
      = Ideal.Quotient.mk (Ideal.span {(algebraMap B' (bSubalg A' A f t n B' g φ' hinj ht hn2t
          hφ') g)}) (mkB A' A f t n B' g φ' hinj ht hn2t hφ' c₂ hN₂) := by
  refine quotient_mk_eq_of_sub_eq_mul B' g _ _ _
    (mkB A' A f t n B' g φ' hinj ht hn2t hφ' p hp) ?_
  rw [mkB_coe, mkB_coe, mkB_coe]
  have hG := congrArg (algebraMap B' (Localization.Away g)) h
  simp only [map_sub, map_mul] at hG
  linear_combination gPowInv B' g t * hG

/-- The class of `g^{-t} · c` in `B/gB` depends only on the class of `a` in `A/fA`: for
representatives `a₁, a₂` with the same class and data `(a'ᵢ, cᵢ)` with `f^t · aᵢ = a'ᵢ`,
`φ'(mk a'ᵢ) = mk cᵢ` and `cᵢ ∈ N`, the classes of `mkB cᵢ` in `B/gB` agree. -/
lemma phi_wd (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht0 : 0 < t)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (a₁ a₂ : A) (a'₁ a'₂ : A') (c₁ c₂ : B')
    (ha₁ : algebraMap A' A f ^ t * a₁ = algebraMap A' A a'₁)
    (ha₂ : algebraMap A' A f ^ t * a₂ = algebraMap A' A a'₂)
    (hc₁ : φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) a'₁) = Ideal.Quotient.mk (Ideal.span {g ^ n})
        c₁)
    (hc₂ : φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) a'₂) = Ideal.Quotient.mk (Ideal.span {g ^ n})
        c₂)
    (hN₁ : c₁ ∈ nIdeal A' A f t n B' g φ') (hN₂ : c₂ ∈ nIdeal A' A f t n B' g φ')
    (heq : Ideal.Quotient.mk (Ideal.span {algebraMap A' A f}) a₁
        = Ideal.Quotient.mk (Ideal.span {algebraMap A' A f}) a₂) :
    Ideal.Quotient.mk (Ideal.span {(algebraMap B' (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ')
        g)})
        (mkB A' A f t n B' g φ' hinj ht hn2t hφ' c₁ hN₁)
      = Ideal.Quotient.mk (Ideal.span {(algebraMap B' (bSubalg A' A f t n B' g φ' hinj ht hn2t
          hφ') g)})
        (mkB A' A f t n B' g φ' hinj ht hn2t hφ' c₂ hN₂) := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at heq
  obtain ⟨w, hw⟩ := heq
  obtain ⟨w', hw'⟩ := ht w
  have hA'eq : a'₁ - a'₂ = f * w' := by
    apply hinj
    rw [map_sub, map_mul, ← ha₁, ← ha₂, ← hw']
    have h1 : algebraMap A' A f ^ t * a₁ - algebraMap A' A f ^ t * a₂
        = algebraMap A' A f ^ t * (a₁ - a₂) := by ring
    rw [h1, ← hw]; ring
  obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) w'))
  have hwM : Ideal.Quotient.mk (Ideal.span {f ^ n}) w' ∈ mbarIdeal A' A f t n :=
    mk_arep_mem_mbarIdeal A' A f t n w w' hw'
  have hdN : d ∈ nIdeal A' A f t n B' g φ' :=
    lift_mem_nIdeal A' A f t n B' g φ' w' d hwM hd.symm
  have hmkeq : Ideal.Quotient.mk (Ideal.span {g ^ n}) (c₁ - c₂)
      = Ideal.Quotient.mk (Ideal.span {g ^ n}) (g * d) := by
    have hlhs : Ideal.Quotient.mk (Ideal.span {g ^ n}) (c₁ - c₂)
        = φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) a'₁)
          - φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) a'₂) := by
      rw [map_sub, hc₁, hc₂]
    have hrhs : Ideal.Quotient.mk (Ideal.span {g ^ n}) (g * d)
        = φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) f)
          * φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) w') := by
      rw [map_mul, hφ', ← hd]
    rw [hlhs, hrhs, ← map_mul, ← map_sub]
    congr 1
    rw [← map_mul, ← map_sub, hA'eq]
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hmkeq)
  have hn : g ^ n = g * g ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  exact mk_mkB_eq_of_sub_eq_mul A' A f t n B' g φ' hinj ht hn2t hφ' c₁ c₂ (d + g ^ (n - 1) * e)
    hN₁ hN₂ (Ideal.add_mem _ hdN (pow_mul_mem_nIdeal A' A f t n B' g φ' hφ' e (n - 1) (by omega)))
    (by linear_combination he + e * hn)

/-- A chosen `a' ∈ A'` with `f^t · a = algebraMap a'`. -/
noncomputable def bSubalg_arep (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t : ℕ)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (a : A) : A' := (ht a).choose

/-- `f^t · a = algebraMap (bSubalg_arep a)`. -/
lemma bSubalg_arep_spec (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t : ℕ)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (a : A) :
    algebraMap A' A f ^ t * a = algebraMap A' A (bSubalg_arep A' A f t ht a) :=
  (ht a).choose_spec

/-- A chosen lift `c ∈ B'` of `φ'(mk (bSubalg_arep a))`. -/
noncomputable def bSubalg_crep (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (a : A) : B' :=
  (Ideal.Quotient.mk_surjective
    (φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) (bSubalg_arep A' A f t ht a)))).choose

/-- `mk (bSubalg_crep a) = φ'(mk (bSubalg_arep a))`. -/
lemma bSubalg_crep_spec (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (a : A) :
    Ideal.Quotient.mk (Ideal.span {g ^ n}) (bSubalg_crep A' A f t n B' g φ' ht a)
      = φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) (bSubalg_arep A' A f t ht a)) :=
  (Ideal.Quotient.mk_surjective
    (φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) (bSubalg_arep A' A f t ht a)))).choose_spec

/-- `bSubalg_crep a ∈ N`. -/
lemma bSubalg_crep_mem (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (a : A) :
    bSubalg_crep A' A f t n B' g φ' ht a ∈ nIdeal A' A f t n B' g φ' :=
  lift_mem_nIdeal A' A f t n B' g φ' (bSubalg_arep A' A f t ht a)
    (bSubalg_crep A' A f t n B' g φ' ht a)
    (mk_arep_mem_mbarIdeal A' A f t n a (bSubalg_arep A' A f t ht a)
      (bSubalg_arep_spec A' A f t ht a))
    (bSubalg_crep_spec A' A f t n B' g φ' ht a).symm

/-- The function `A → B/gB`, `a ↦ mk (g^{-t} · bSubalg_crep a)`. -/
noncomputable def bSubalg_phiFun
    (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (a : A) :
    (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') ⧸
      Ideal.span {algebraMap B' (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') g} :=
  Ideal.Quotient.mk _
    (mkB A' A f t n B' g φ' hinj ht hn2t hφ'
      (bSubalg_crep A' A f t n B' g φ' ht a) (bSubalg_crep_mem A' A f t n B' g φ' ht a))

/-- For any `(a', c)` with `f^t · a = algebraMap a'`, `φ'(mk a') = mk c` and `c ∈ N`,
`bSubalg_phiFun a = mk (mkB c)`. -/
lemma bSubalg_phiFun_eq (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht0 : 0 < t)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (a : A) (a' : A') (c : B')
    (ha : algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hc : φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) a') = Ideal.Quotient.mk (Ideal.span {g ^ n}) c)
    (hN : c ∈ nIdeal A' A f t n B' g φ') :
    bSubalg_phiFun A' A f t n B' g φ' hinj ht hn2t hφ' a
      = Ideal.Quotient.mk _ (mkB A' A f t n B' g φ' hinj ht hn2t hφ' c hN) :=
  phi_wd A' A f t n B' g φ' hinj ht0 ht hn2t hφ' a a
    (bSubalg_arep A' A f t ht a) a' (bSubalg_crep A' A f t n B' g φ' ht a) c
    (bSubalg_arep_spec A' A f t ht a) ha
    (bSubalg_crep_spec A' A f t n B' g φ' ht a).symm hc
    (bSubalg_crep_mem A' A f t n B' g φ' ht a) hN rfl

/-- `bSubalg_phiFun` is constant on the cosets of `f · A`. -/
lemma bSubalg_phiFun_wd (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht0 : 0 < t)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (a₁ a₂ : A)
    (heq : Ideal.Quotient.mk (Ideal.span {algebraMap A' A f}) a₁
        = Ideal.Quotient.mk (Ideal.span {algebraMap A' A f}) a₂) :
    bSubalg_phiFun A' A f t n B' g φ' hinj ht hn2t hφ' a₁
      = bSubalg_phiFun A' A f t n B' g φ' hinj ht hn2t hφ' a₂ :=
  phi_wd A' A f t n B' g φ' hinj ht0 ht hn2t hφ' a₁ a₂
    (bSubalg_arep A' A f t ht a₁) (bSubalg_arep A' A f t ht a₂)
    (bSubalg_crep A' A f t n B' g φ' ht a₁) (bSubalg_crep A' A f t n B' g φ' ht a₂)
    (bSubalg_arep_spec A' A f t ht a₁) (bSubalg_arep_spec A' A f t ht a₂)
    (bSubalg_crep_spec A' A f t n B' g φ' ht a₁).symm
    (bSubalg_crep_spec A' A f t n B' g φ' ht a₂).symm
    (bSubalg_crep_mem A' A f t n B' g φ' ht a₁)
    (bSubalg_crep_mem A' A f t n B' g φ' ht a₂) heq

/-- `bSubalg_phiFun (a₁ * a₂) = bSubalg_phiFun a₁ * bSubalg_phiFun a₂`. -/
lemma bSubalg_phiFun_mul (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht0 : 0 < t)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n) (hn2t1 : 2 * t < n) (hg : g ∈ nonZeroDivisors B')
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (a₁ a₂ : A) :
    bSubalg_phiFun A' A f t n B' g φ' hinj ht hn2t hφ' (a₁ * a₂)
      = bSubalg_phiFun A' A f t n B' g φ' hinj ht hn2t hφ' a₁
        * bSubalg_phiFun A' A f t n B' g φ' hinj ht hn2t hφ' a₂ := by
  set S := bSubalg A' A f t n B' g φ' hinj ht hn2t hφ' with hSdef
  set c₁ := bSubalg_crep A' A f t n B' g φ' ht a₁ with hc₁def
  set c₂ := bSubalg_crep A' A f t n B' g φ' ht a₂ with hc₂def
  have hN₁ : c₁ ∈ nIdeal A' A f t n B' g φ' := bSubalg_crep_mem A' A f t n B' g φ' ht a₁
  have hN₂ : c₂ ∈ nIdeal A' A f t n B' g φ' := bSubalg_crep_mem A' A f t n B' g φ' ht a₂
  obtain ⟨c'', hN'', hmul⟩ :=
    exists_mem_nIdeal_mul_eq A' A f t n B' g φ' hinj ht hn2t hφ' c₁ c₂ hN₁ hN₂
  set Gm := algebraMap B' (Localization.Away g) with hGmdef
  set G := Gm g with hGdef
  have hGt : G ^ t * gPowInv B' g t = 1 := pow_mul_gPowInv_eq_one B' g t
  have hmkB_mul : mkB A' A f t n B' g φ' hinj ht hn2t hφ' c₁ hN₁
        * mkB A' A f t n B' g φ' hinj ht hn2t hφ' c₂ hN₂
      = mkB A' A f t n B' g φ' hinj ht hn2t hφ' c'' hN'' := by
    apply Subtype.ext
    have e1 := mkB_coe A' A f t n B' g φ' hinj ht hn2t hφ' c₁ hN₁
    have e2 := mkB_coe A' A f t n B' g φ' hinj ht hn2t hφ' c₂ hN₂
    have e3 := mkB_coe A' A f t n B' g φ' hinj ht hn2t hφ' c'' hN''
    rw [Subalgebra.coe_mul, e1, e2, e3]
    have hmm : Gm c₁ * Gm c₂ = G ^ t * Gm c'' := by
      rw [← map_mul, hmul, map_mul, map_pow]
    change gPowInv B' g t * Gm c₁ * (gPowInv B' g t * Gm c₂) = gPowInv B' g t * Gm c''
    linear_combination (gPowInv B' g t * gPowInv B' g t) * hmm + (gPowInv B' g t * Gm c'') * hGt
  have hRHS : bSubalg_phiFun A' A f t n B' g φ' hinj ht hn2t hφ' a₁
        * bSubalg_phiFun A' A f t n B' g φ' hinj ht hn2t hφ' a₂
      = Ideal.Quotient.mk _ (mkB A' A f t n B' g φ' hinj ht hn2t hφ' c'' hN'') := by
    change Ideal.Quotient.mk _ _ * Ideal.Quotient.mk _ _ = _
    rw [← map_mul, hmkB_mul]
  rw [hRHS]
  change Ideal.Quotient.mk _ (mkB A' A f t n B' g φ' hinj ht hn2t hφ'
        (bSubalg_crep A' A f t n B' g φ' ht (a₁ * a₂))
        (bSubalg_crep_mem A' A f t n B' g φ' ht (a₁ * a₂))) = _
  set crep := bSubalg_crep A' A f t n B' g φ' ht (a₁ * a₂) with hcrepdef
  set hNcrep := bSubalg_crep_mem A' A f t n B' g φ' ht (a₁ * a₂)
  set ar1 := bSubalg_arep A' A f t ht a₁ with har1def
  set ar2 := bSubalg_arep A' A f t ht a₂ with har2def
  set ar12 := bSubalg_arep A' A f t ht (a₁ * a₂) with har12def
  have hs1 := bSubalg_arep_spec A' A f t ht a₁
  have hs2 := bSubalg_arep_spec A' A f t ht a₂
  have hs12 := bSubalg_arep_spec A' A f t ht (a₁ * a₂)
  have hAeq : algebraMap A' A (ar1 * ar2) = algebraMap A' A (f ^ t * ar12) := by
    rw [map_mul, map_mul, map_pow, ← hs1, ← hs2, ← hs12]
    ring
  have hA'eq : ar1 * ar2 = f ^ t * ar12 := hinj hAeq
  have hcs1 := bSubalg_crep_spec A' A f t n B' g φ' ht a₁
  have hcs2 := bSubalg_crep_spec A' A f t n B' g φ' ht a₂
  have hcs12 := bSubalg_crep_spec A' A f t n B' g φ' ht (a₁ * a₂)
  have hφft := map_mk_pow_eq_mk_pow f g t φ' hφ'
  have hquot : Ideal.Quotient.mk (Ideal.span {g ^ n}) (g ^ t * c'')
      = Ideal.Quotient.mk (Ideal.span {g ^ n}) (g ^ t * crep) := by
    rw [← hmul]
    calc Ideal.Quotient.mk (Ideal.span {g ^ n}) (c₁ * c₂)
        = φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) ar1)
          * φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) ar2) := by
          rw [map_mul, hcs1, hcs2]
      _ = φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) (f ^ t * ar12)) := by
          rw [← map_mul, ← map_mul, hA'eq]
      _ = φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) (f ^ t))
          * φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) ar12) := by
          rw [map_mul, map_mul]
      _ = Ideal.Quotient.mk (Ideal.span {g ^ n}) (g ^ t)
          * Ideal.Quotient.mk (Ideal.span {g ^ n}) crep := by
          rw [hφft, ← hcs12]
      _ = Ideal.Quotient.mk (Ideal.span {g ^ n}) (g ^ t * crep) := by rw [map_mul]
  obtain ⟨m, hm⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hquot)
  have hnt : g ^ n = g ^ t * g ^ (n - t) := by rw [← pow_add]; congr 1; omega
  have hdiff : c'' - crep = g ^ (n - t) * m := by
    have hz : ((c'' - crep) - g ^ (n - t) * m) * g ^ t = 0 := by
      linear_combination hm + m * hnt
    linear_combination (mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hg t)).mp hz
  have hgp : c'' - crep = g * (g ^ (n - t - 1) * m) := by
    rw [hdiff, ← mul_assoc, ← pow_succ']; congr 2; omega
  exact (mk_mkB_eq_of_sub_eq_mul A' A f t n B' g φ' hinj ht hn2t hφ' c'' crep _ hN'' hNcrep
    (pow_mul_mem_nIdeal A' A f t n B' g φ' hφ' m _ (by omega)) hgp).symm

/-- `bSubalg_phiFun (a₁ + a₂) = bSubalg_phiFun a₁ + bSubalg_phiFun a₂`. -/
lemma bSubalg_phiFun_add (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht0 : 0 < t)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (a₁ a₂ : A) :
    bSubalg_phiFun A' A f t n B' g φ' hinj ht hn2t hφ' (a₁ + a₂)
      = bSubalg_phiFun A' A f t n B' g φ' hinj ht hn2t hφ' a₁
        + bSubalg_phiFun A' A f t n B' g φ' hinj ht hn2t hφ' a₂ := by
  set S := bSubalg A' A f t n B' g φ' hinj ht hn2t hφ' with hSdef
  set c₁ := bSubalg_crep A' A f t n B' g φ' ht a₁ with hc₁def
  set c₂ := bSubalg_crep A' A f t n B' g φ' ht a₂ with hc₂def
  have hN₁ : c₁ ∈ nIdeal A' A f t n B' g φ' := bSubalg_crep_mem A' A f t n B' g φ' ht a₁
  have hN₂ : c₂ ∈ nIdeal A' A f t n B' g φ' := bSubalg_crep_mem A' A f t n B' g φ' ht a₂
  set ar1 := bSubalg_arep A' A f t ht a₁ with har1def
  set ar2 := bSubalg_arep A' A f t ht a₂ with har2def
  have hs1 := bSubalg_arep_spec A' A f t ht a₁
  have hs2 := bSubalg_arep_spec A' A f t ht a₂
  have hcs1 := bSubalg_crep_spec A' A f t n B' g φ' ht a₁
  have hcs2 := bSubalg_crep_spec A' A f t n B' g φ' ht a₂
  have hNsum : c₁ + c₂ ∈ nIdeal A' A f t n B' g φ' := Ideal.add_mem _ hN₁ hN₂
  have hasum : algebraMap A' A f ^ t * (a₁ + a₂) = algebraMap A' A (ar1 + ar2) := by
    rw [mul_add, hs1, hs2, map_add]
  have hcsum : φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) (ar1 + ar2))
      = Ideal.Quotient.mk (Ideal.span {g ^ n}) (c₁ + c₂) := by
    rw [map_add, map_add, map_add, ← hcs1, ← hcs2]
  have hmkB_add : mkB A' A f t n B' g φ' hinj ht hn2t hφ' (c₁ + c₂) hNsum
      = mkB A' A f t n B' g φ' hinj ht hn2t hφ' c₁ hN₁
        + mkB A' A f t n B' g φ' hinj ht hn2t hφ' c₂ hN₂ := by
    apply Subtype.ext
    rw [Subalgebra.coe_add, mkB_coe, mkB_coe, mkB_coe, map_add, mul_add]
  rw [bSubalg_phiFun_eq A' A f t n B' g φ' hinj ht0 ht hn2t hφ' (a₁ + a₂) (ar1 + ar2) (c₁ + c₂)
      hasum hcsum hNsum,
    bSubalg_phiFun_eq A' A f t n B' g φ' hinj ht0 ht hn2t hφ' a₁ ar1 c₁ hs1 hcs1.symm hN₁,
    bSubalg_phiFun_eq A' A f t n B' g φ' hinj ht0 ht hn2t hφ' a₂ ar2 c₂ hs2 hcs2.symm hN₂]
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _ + Ideal.Quotient.mk _ _
  rw [← map_add, hmkB_add]

/-- `bSubalg_phiFun 1 = 1`. -/
lemma bSubalg_phiFun_one (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht0 : 0 < t)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g) :
    bSubalg_phiFun A' A f t n B' g φ' hinj ht hn2t hφ' 1 = 1 := by
  have hφft0 := map_mk_pow_eq_mk_pow f g t φ' hφ'
  have hgtN := gPow_mem_nIdeal A' A f t n B' g φ' hφ'
  rw [bSubalg_phiFun_eq A' A f t n B' g φ' hinj ht0 ht hn2t hφ' 1
    (f ^ t) (g ^ t)
    (by rw [mul_one, map_pow])
    hφft0
    hgtN]
  have hone : mkB A' A f t n B' g φ' hinj ht hn2t hφ' (g ^ t)
      hgtN = 1 := by
    apply Subtype.ext
    rw [mkB_coe, OneMemClass.coe_one, map_pow, mul_comm, pow_mul_gPowInv_eq_one]
  rw [hone, map_one]

/-- `bSubalg_phiFun 0 = 0`. -/
lemma bSubalg_phiFun_zero (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht0 : 0 < t)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g) :
    bSubalg_phiFun A' A f t n B' g φ' hinj ht hn2t hφ' 0 = 0 := by
  have hφ0 : φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) 0)
      = Ideal.Quotient.mk (Ideal.span {g ^ n}) 0 := by
    rw [map_zero, map_zero, map_zero]
  have hzN : (0 : B') ∈ nIdeal A' A f t n B' g φ' := Submodule.zero_mem _
  rw [bSubalg_phiFun_eq A' A f t n B' g φ' hinj ht0 ht hn2t hφ' 0
    0 0
    (by rw [mul_zero, map_zero])
    hφ0
    hzN]
  have hzero : mkB A' A f t n B' g φ' hinj ht hn2t hφ' (0 : B')
      hzN = 0 := by
    apply Subtype.ext
    rw [mkB_coe, ZeroMemClass.coe_zero, map_zero, mul_zero]
  rw [hzero, map_zero]

/-- The ring homomorphism `φ : A/fA →+* B/gB` given on a representative `a : A` by
`φ(ā) = (g^{-t} · c) mod gB`, where `c ∈ N` is any lift of `φ'` of the class of `f^t · a` in
`A'/f^n A'`. -/
noncomputable def bSubalg_phiHom
    (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht0 : 0 < t)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n) (hn2t1 : 2 * t < n) (hg : g ∈ nonZeroDivisors B')
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g) :
    (A ⧸ Ideal.span {algebraMap A' A f}) →+*
      ((bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') ⧸
        Ideal.span {algebraMap B' (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') g}) :=
  { toFun := Quotient.lift
      (bSubalg_phiFun A' A f t n B' g φ' hinj ht hn2t hφ')
      (fun a₁ a₂ h => bSubalg_phiFun_wd A' A f t n B' g φ' hinj ht0 ht hn2t hφ' a₁ a₂
        (Quotient.sound h))
    map_one' := bSubalg_phiFun_one A' A f t n B' g φ' hinj ht0 ht hn2t hφ'
    map_mul' := by
      refine Quotient.ind₂ (fun a₁ a₂ => ?_)
      exact bSubalg_phiFun_mul A' A f t n B' g φ' hinj ht0 ht hn2t hn2t1 hg hφ' a₁ a₂
    map_zero' := bSubalg_phiFun_zero A' A f t n B' g φ' hinj ht0 ht hn2t hφ'
    map_add' := by
      refine Quotient.ind₂ (fun a₁ a₂ => ?_)
      exact bSubalg_phiFun_add A' A f t n B' g φ' hinj ht0 ht hn2t hφ' a₁ a₂ }
