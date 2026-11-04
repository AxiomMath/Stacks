module

public import StacksFrontier.RingTheory.FiniteExtension.ModPow.ForwardMap

/-!
# The inverse map `B/gB → A/fA`

This file constructs the inverse of the ring homomorphism `bSubalg_phiHom`. For `x ∈ B = bSubalg`
it chooses `c ∈ N` with `c = g^t x`, an element `a' ∈ A'` lifting `φ'⁻¹(c)` and `a ∈ A` with
`a' = f^t a`, and shows that `x ↦ a` induces a ring homomorphism `ψ : B/gB →+* A/fA`.

## Main definitions

* `bSubalg_psiHom`: the ring homomorphism `ψ : B/gB →+* A/fA`.
-/

@[expose] public section

universe u v w

/-- If `mk a' ∈ M̄` and `t ≤ n`, there is `a : A` with `algebraMap a' = f^t · a`. -/
lemma exists_pow_mul_eq_of_mk_mem_mbarIdeal (A' : Type u) (A : Type v) [CommRing A']
    [CommRing A] [Algebra A' A] (f : A') (t n : ℕ)
    (hn : t ≤ n)
    (a' : A')
    (hM : Ideal.Quotient.mk (Ideal.span {f ^ n}) a' ∈ mbarIdeal A' A f t n) :
    ∃ a : A, algebraMap A' A a' = algebraMap A' A f ^ t * a := by
  rw [mbarIdeal] at hM
  have key : ∀ y ∈ Ideal.span { x : A' ⧸ Ideal.span {f ^ n} |
        ∃ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a' ∧
          x = Ideal.Quotient.mk _ a' },
      ∃ a : A, ∃ a'' : A', algebraMap A' A a'' = algebraMap A' A f ^ t * a ∧
        y = Ideal.Quotient.mk (Ideal.span {f ^ n}) a'' := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro x ⟨a, a'', ha, rfl⟩
      exact ⟨a, a'', ha.symm, rfl⟩
    · exact ⟨0, 0, by rw [map_zero, mul_zero], by rw [map_zero]⟩
    · rintro y z _ _ ⟨ay, a'y, hay, rfl⟩ ⟨az, a'z, haz, rfl⟩
      refine ⟨ay + az, a'y + a'z, ?_, by rw [map_add]⟩
      rw [map_add, hay, haz, mul_add]
    · rintro c y _ ⟨ay, a'y, hay, rfl⟩
      obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
      refine ⟨algebraMap A' A c' • ay, c' * a'y, ?_, ?_⟩
      · rw [map_mul, hay, smul_eq_mul]; ring
      · rw [map_mul]; rfl
  obtain ⟨a, a'', ha, hy⟩ := key _ hM
  rw [eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hy
  obtain ⟨d, hd⟩ := hy
  refine ⟨a + algebraMap A' A (f ^ (n - t) * (-d)), ?_⟩
  have hfn : algebraMap A' A f ^ t * algebraMap A' A (f ^ (n - t) * (-d))
      = algebraMap A' A (f ^ n * (-d)) := by
    rw [← map_pow, ← map_mul]
    congr 1
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  have hgoal : algebraMap A' A a'
      = algebraMap A' A a'' + algebraMap A' A (f ^ n * (-d)) := by
    rw [← map_add]
    congr 1
    linear_combination -hd
  rw [mul_add, ← ha, hfn, hgoal]

/-- For `c ∈ N`, `φ'⁻¹(mk c) ∈ M̄`. -/
lemma symm_mk_mem_mbarIdeal (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (c : B') (hc : c ∈ nIdeal A' A f t n B' g φ') :
    φ'.symm (Ideal.Quotient.mk (Ideal.span {g ^ n}) c) ∈ mbarIdeal A' A f t n := by
  rw [nIdeal, Ideal.mem_comap] at hc
  have hmem : φ'.symm (Ideal.Quotient.mk (Ideal.span {g ^ n}) c)
      ∈ Ideal.map (φ'.symm : (B' ⧸ Ideal.span {g ^ n}) →+* _)
          (Ideal.map (φ' : (A' ⧸ Ideal.span {f ^ n}) →+* _) (mbarIdeal A' A f t n)) :=
    Ideal.mem_map_of_mem _ hc
  have hcomp : ((φ'.symm : (B' ⧸ Ideal.span {g ^ n}) →+* _).comp
      (φ' : (A' ⧸ Ideal.span {f ^ n}) →+* _)) = RingHom.id _ := by
    ext z; exact φ'.symm_apply_apply z
  rwa [Ideal.map_map, hcomp, Ideal.map_id] at hmem

/-- For `x ∈ bSubalg`, a chosen `c ∈ N` with `algebraMap c = g^t · x`. -/
noncomputable def bSubalg_crepB (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (x : bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') : B' :=
  x.property.choose

/-- `algebraMap (bSubalg_crepB x) = g^t · x` in `Localization.Away g`. -/
lemma bSubalg_crepB_spec (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (x : bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') :
    algebraMap B' (Localization.Away g) (bSubalg_crepB A' A f t n B' g φ' hinj ht hn2t hφ' x)
      = (algebraMap B' (Localization.Away g) g) ^ t * (x : Localization.Away g) :=
  x.property.choose_spec.left

/-- `bSubalg_crepB x ∈ N`. -/
lemma bSubalg_crepB_mem (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (x : bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') :
    bSubalg_crepB A' A f t n B' g φ' hinj ht hn2t hφ' x ∈ nIdeal A' A f t n B' g φ' :=
  x.property.choose_spec.right

/-- A chosen `a' ∈ A'` lifting `φ'⁻¹(mk (bSubalg_crepB x))`. -/
noncomputable def bSubalg_arepB (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (x : bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') : A' :=
  (Ideal.Quotient.mk_surjective
    (φ'.symm (Ideal.Quotient.mk (Ideal.span {g ^ n})
      (bSubalg_crepB A' A f t n B' g φ' hinj ht hn2t hφ' x)))).choose

/-- `mk (bSubalg_arepB x) = φ'⁻¹(mk (bSubalg_crepB x))`. -/
lemma bSubalg_arepB_spec (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (x : bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') :
    Ideal.Quotient.mk (Ideal.span {f ^ n})
        (bSubalg_arepB A' A f t n B' g φ' hinj ht hn2t hφ' x)
      = φ'.symm (Ideal.Quotient.mk (Ideal.span {g ^ n})
          (bSubalg_crepB A' A f t n B' g φ' hinj ht hn2t hφ' x)) :=
  (Ideal.Quotient.mk_surjective
     (φ'.symm (Ideal.Quotient.mk (Ideal.span {g ^ n})
       (bSubalg_crepB A' A f t n B' g φ' hinj ht hn2t hφ' x)))).choose_spec

/-- `mk (bSubalg_arepB x) ∈ M̄`. -/
lemma bSubalg_arepB_mem (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (x : bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') :
    Ideal.Quotient.mk (Ideal.span {f ^ n})
        (bSubalg_arepB A' A f t n B' g φ' hinj ht hn2t hφ' x) ∈ mbarIdeal A' A f t n := by
  rw [bSubalg_arepB_spec]
  exact symm_mk_mem_mbarIdeal A' A f t n B' g φ'
    (bSubalg_crepB A' A f t n B' g φ' hinj ht hn2t hφ' x)
    (bSubalg_crepB_mem A' A f t n B' g φ' hinj ht hn2t hφ' x)

/-- A chosen `a : A` with `algebraMap (bSubalg_arepB x) = f^t · a`. -/
noncomputable def bSubalg_aA (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (x : bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') : A :=
  (exists_pow_mul_eq_of_mk_mem_mbarIdeal A' A f t n (by omega)
    (bSubalg_arepB A' A f t n B' g φ' hinj ht hn2t hφ' x)
    (bSubalg_arepB_mem A' A f t n B' g φ' hinj ht hn2t hφ' x)).choose

/-- `algebraMap (bSubalg_arepB x) = f^t · bSubalg_aA x`. -/
lemma bSubalg_aA_spec (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (x : bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') :
    algebraMap A' A (bSubalg_arepB A' A f t n B' g φ' hinj ht hn2t hφ' x)
      = algebraMap A' A f ^ t * (bSubalg_aA A' A f t n B' g φ' hinj ht hn2t hφ' x) :=
  (exists_pow_mul_eq_of_mk_mem_mbarIdeal A' A f t n (by omega)
     (bSubalg_arepB A' A f t n B' g φ' hinj ht hn2t hφ' x)
     (bSubalg_arepB_mem A' A f t n B' g φ' hinj ht hn2t hφ' x)).choose_spec

/-- If `mk a = mk b` modulo `f ^ n`, then `a = b + f ^ n * e` for some `e`. -/
private lemma exists_eq_add_pow_mul_of_mk_eq {R : Type*} [CommRing R] (f : R) (n : ℕ) {a b : R}
    (h : Ideal.Quotient.mk (Ideal.span {f ^ n}) a = Ideal.Quotient.mk (Ideal.span {f ^ n}) b) :
    ∃ e, a = b + f ^ n * e := by
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  exact ⟨e, by linear_combination he⟩

/-- The chosen `c`, `a'`, `a` for `x` satisfy all their defining relations. -/
private lemma bSubalg_exists_rep (A' : Type u) (A : Type v) [CommRing A'] [CommRing A]
    [Algebra A' A] (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (x : bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') :
    ∃ (c : B') (a' : A') (a : A),
      algebraMap B' (Localization.Away g) c
        = (algebraMap B' (Localization.Away g) g) ^ t * (x : Localization.Away g) ∧
      Ideal.Quotient.mk (Ideal.span {f ^ n}) a'
        = φ'.symm (Ideal.Quotient.mk (Ideal.span {g ^ n}) c) ∧
      algebraMap A' A a' = algebraMap A' A f ^ t * a ∧ c ∈ nIdeal A' A f t n B' g φ' :=
  ⟨_, _, _, bSubalg_crepB_spec A' A f t n B' g φ' hinj ht hn2t hφ' x,
    bSubalg_arepB_spec A' A f t n B' g φ' hinj ht hn2t hφ' x,
    bSubalg_aA_spec A' A f t n B' g φ' hinj ht hn2t hφ' x,
    bSubalg_crepB_mem A' A f t n B' g φ' hinj ht hn2t hφ' x⟩

/-- The class `mk a ∈ A/fA`, where `f^t · a = algebraMap a'`, `mk a' = φ'⁻¹(mk c)`,
`algebraMap c = g^t · x` and `c ∈ N`, depends only on the class of `x` in `B/gB`. -/
lemma psi_wd (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (hnzd : algebraMap A' A f ∈ nonZeroDivisors A)
    (ht0 : 0 < t)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n) (hg : g ∈ nonZeroDivisors B')
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (x₁ x₂ : bSubalg A' A f t n B' g φ' hinj ht hn2t hφ')
    (c₁ c₂ : B') (a'₁ a'₂ : A') (a₁ a₂ : A)
    (hc₁ : algebraMap B' (Localization.Away g) c₁
        = (algebraMap B' (Localization.Away g) g) ^ t * (x₁ : Localization.Away g))
    (hc₂ : algebraMap B' (Localization.Away g) c₂
        = (algebraMap B' (Localization.Away g) g) ^ t * (x₂ : Localization.Away g))
    (ha'₁ : Ideal.Quotient.mk (Ideal.span {f ^ n}) a'₁
        = φ'.symm (Ideal.Quotient.mk (Ideal.span {g ^ n}) c₁))
    (ha'₂ : Ideal.Quotient.mk (Ideal.span {f ^ n}) a'₂
        = φ'.symm (Ideal.Quotient.mk (Ideal.span {g ^ n}) c₂))
    (ha₁ : algebraMap A' A a'₁ = algebraMap A' A f ^ t * a₁)
    (ha₂ : algebraMap A' A a'₂ = algebraMap A' A f ^ t * a₂)
    (heq : Ideal.Quotient.mk
        (Ideal.span {algebraMap B' (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') g}) x₁
      = Ideal.Quotient.mk
        (Ideal.span {algebraMap B' (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') g}) x₂) :
    Ideal.Quotient.mk (Ideal.span {algebraMap A' A f}) a₁
      = Ideal.Quotient.mk (Ideal.span {algebraMap A' A f}) a₂ := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at heq
  obtain ⟨z, hz⟩ := heq
  obtain ⟨cz, w', aw, hcz, hw', haw, -⟩ :=
    bSubalg_exists_rep A' A f t n B' g φ' hinj ht hn2t hφ' z
  set Gm := algebraMap B' (Localization.Away g) with hGmdef
  set G := Gm g with hGdef
  have hxdiff : (x₁ : Localization.Away g) - (x₂ : Localization.Away g)
      = G * (z : Localization.Away g) := by
    have hzc := congrArg
      (fun s : (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') => (s : Localization.Away g)) hz
    simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Subalgebra.coe_sub] at hzc
    rw [← hGmdef, ← hGdef] at hzc
    linear_combination -hzc
  have hLoc : Gm (c₁ - c₂) = Gm (g * cz) := by
    rw [map_sub, hc₁, hc₂, map_mul, hcz, ← hGdef]
    linear_combination (G ^ t) * hxdiff
  have hinjLoc : Function.Injective (algebraMap B' (Localization.Away g)) :=
    IsLocalization.injective (Localization.Away g) (Submonoid.powers_le.mpr hg)
  have hc12 : c₁ - c₂ = g * cz := hinjLoc hLoc
  have hmkdiff : Ideal.Quotient.mk (Ideal.span {f ^ n}) (a'₁ - a'₂)
      = Ideal.Quotient.mk (Ideal.span {f ^ n}) (f * w') := by
    rw [map_sub, ha'₁, ha'₂, ← map_sub]
    rw [show Ideal.Quotient.mk (Ideal.span {g ^ n}) c₁ - Ideal.Quotient.mk (Ideal.span {g ^ n}) c₂
          = Ideal.Quotient.mk (Ideal.span {g ^ n}) (c₁ - c₂) from (map_sub _ _ _).symm]
    rw [hc12, map_mul, map_mul, symm_map_mk_eq_mk f g φ' hφ', ← hw', ← map_mul]
  obtain ⟨e, he⟩ := exists_eq_add_pow_mul_of_mk_eq f n hmkdiff
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
  refine ⟨aw + algebraMap A' A f ^ (n - t - 1) * algebraMap A' A e,
    (mul_cancel_left_mem_nonZeroDivisors (pow_mem hnzd t)).mp ?_⟩
  have hn : algebraMap A' A f ^ n
      = algebraMap A' A f ^ t * (algebraMap A' A f * algebraMap A' A f ^ (n - t - 1)) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  have hae : algebraMap A' A a'₁ - algebraMap A' A a'₂
      = algebraMap A' A f * algebraMap A' A w' + algebraMap A' A f ^ n * algebraMap A' A e := by
    rw [← map_sub, he, map_add, map_mul, map_mul, map_pow]
  linear_combination ha₁ - ha₂ - hae - algebraMap A' A f * haw - algebraMap A' A e * hn

/-- The function `bSubalg → A/fA`, `x ↦ mk (bSubalg_aA x)`. -/
noncomputable def bSubalg_psiFun
    (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (x : bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') :
    A ⧸ Ideal.span {algebraMap A' A f} :=
  Ideal.Quotient.mk _ (bSubalg_aA A' A f t n B' g φ' hinj ht hn2t hφ' x)

/-- For any `(c, a', a)` with `algebraMap c = g^t · x`, `mk a' = φ'⁻¹(mk c)` and
`algebraMap a' = f^t · a`, `bSubalg_psiFun x = mk a`. -/
lemma bSubalg_psiFun_eq (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (hnzd : algebraMap A' A f ∈ nonZeroDivisors A)
    (ht0 : 0 < t)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n) (hg : g ∈ nonZeroDivisors B')
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (x : bSubalg A' A f t n B' g φ' hinj ht hn2t hφ')
    (c : B') (a' : A') (a : A)
    (hc : algebraMap B' (Localization.Away g) c
        = (algebraMap B' (Localization.Away g) g) ^ t * (x : Localization.Away g))
    (ha' : Ideal.Quotient.mk (Ideal.span {f ^ n}) a'
        = φ'.symm (Ideal.Quotient.mk (Ideal.span {g ^ n}) c))
    (ha : algebraMap A' A a' = algebraMap A' A f ^ t * a) :
    bSubalg_psiFun A' A f t n B' g φ' hinj ht hn2t hφ' x
      = Ideal.Quotient.mk _ a :=
  psi_wd A' A f t n B' g φ' hinj hnzd ht0 ht hn2t hg hφ' x x
    (bSubalg_crepB A' A f t n B' g φ' hinj ht hn2t hφ' x) c
    (bSubalg_arepB A' A f t n B' g φ' hinj ht hn2t hφ' x) a'
    (bSubalg_aA A' A f t n B' g φ' hinj ht hn2t hφ' x) a
    (bSubalg_crepB_spec A' A f t n B' g φ' hinj ht hn2t hφ' x) hc
    (bSubalg_arepB_spec A' A f t n B' g φ' hinj ht hn2t hφ' x) ha'
    (bSubalg_aA_spec A' A f t n B' g φ' hinj ht hn2t hφ' x) ha rfl

/-- `bSubalg_psiFun` is constant on the cosets of `g · bSubalg`. -/
lemma bSubalg_psiFun_wd (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (hnzd : algebraMap A' A f ∈ nonZeroDivisors A)
    (ht0 : 0 < t)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n) (hg : g ∈ nonZeroDivisors B')
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (x₁ x₂ : bSubalg A' A f t n B' g φ' hinj ht hn2t hφ')
    (heq : Ideal.Quotient.mk
        (Ideal.span {algebraMap B' (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') g}) x₁
      = Ideal.Quotient.mk
        (Ideal.span {algebraMap B' (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') g}) x₂) :
    bSubalg_psiFun A' A f t n B' g φ' hinj ht hn2t hφ' x₁
      = bSubalg_psiFun A' A f t n B' g φ' hinj ht hn2t hφ' x₂ :=
  psi_wd A' A f t n B' g φ' hinj hnzd ht0 ht hn2t hg hφ' x₁ x₂
    (bSubalg_crepB A' A f t n B' g φ' hinj ht hn2t hφ' x₁)
    (bSubalg_crepB A' A f t n B' g φ' hinj ht hn2t hφ' x₂)
    (bSubalg_arepB A' A f t n B' g φ' hinj ht hn2t hφ' x₁)
    (bSubalg_arepB A' A f t n B' g φ' hinj ht hn2t hφ' x₂)
    (bSubalg_aA A' A f t n B' g φ' hinj ht hn2t hφ' x₁)
    (bSubalg_aA A' A f t n B' g φ' hinj ht hn2t hφ' x₂)
    (bSubalg_crepB_spec A' A f t n B' g φ' hinj ht hn2t hφ' x₁)
    (bSubalg_crepB_spec A' A f t n B' g φ' hinj ht hn2t hφ' x₂)
    (bSubalg_arepB_spec A' A f t n B' g φ' hinj ht hn2t hφ' x₁)
    (bSubalg_arepB_spec A' A f t n B' g φ' hinj ht hn2t hφ' x₂)
    (bSubalg_aA_spec A' A f t n B' g φ' hinj ht hn2t hφ' x₁)
    (bSubalg_aA_spec A' A f t n B' g φ' hinj ht hn2t hφ' x₂) heq

/-- `bSubalg_psiFun 0 = 0`. -/
lemma bSubalg_psiFun_zero (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (hnzd : algebraMap A' A f ∈ nonZeroDivisors A)
    (ht0 : 0 < t)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n) (hg : g ∈ nonZeroDivisors B')
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g) :
    bSubalg_psiFun A' A f t n B' g φ' hinj ht hn2t hφ' 0 = 0 := by
  rw [bSubalg_psiFun_eq A' A f t n B' g φ' hinj hnzd ht0 ht hn2t hg hφ' 0
    0 0 0 (by rw [map_zero, ZeroMemClass.coe_zero, mul_zero])
    (by rw [map_zero, map_zero, map_zero]) (by rw [map_zero, mul_zero])]
  rw [map_zero]

/-- `bSubalg_psiFun 1 = 1`. -/
lemma bSubalg_psiFun_one (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (hnzd : algebraMap A' A f ∈ nonZeroDivisors A)
    (ht0 : 0 < t)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n) (hg : g ∈ nonZeroDivisors B')
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g) :
    bSubalg_psiFun A' A f t n B' g φ' hinj ht hn2t hφ' 1 = 1 := by
  have hφft := symm_map_mk_pow_eq_mk_pow f g t φ' hφ'
  rw [bSubalg_psiFun_eq A' A f t n B' g φ' hinj hnzd ht0 ht hn2t hg hφ' 1
    (g ^ t) (f ^ t) 1
    (by rw [map_pow, OneMemClass.coe_one, mul_one])
    (by rw [hφft])
    (by rw [map_pow, mul_one])]
  rw [map_one]

/-- `bSubalg_psiFun (x₁ + x₂) = bSubalg_psiFun x₁ + bSubalg_psiFun x₂`. -/
lemma bSubalg_psiFun_add (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (hnzd : algebraMap A' A f ∈ nonZeroDivisors A)
    (ht0 : 0 < t)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n) (hg : g ∈ nonZeroDivisors B')
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (x₁ x₂ : bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') :
    bSubalg_psiFun A' A f t n B' g φ' hinj ht hn2t hφ' (x₁ + x₂)
      = bSubalg_psiFun A' A f t n B' g φ' hinj ht hn2t hφ' x₁
        + bSubalg_psiFun A' A f t n B' g φ' hinj ht hn2t hφ' x₂ := by
  obtain ⟨c₁, a'₁, a₁, hc₁, ha'₁, ha₁, hN₁⟩ :=
    bSubalg_exists_rep A' A f t n B' g φ' hinj ht hn2t hφ' x₁
  obtain ⟨c₂, a'₂, a₂, hc₂, ha'₂, ha₂, hN₂⟩ :=
    bSubalg_exists_rep A' A f t n B' g φ' hinj ht hn2t hφ' x₂
  have hx1 := bSubalg_psiFun_eq A' A f t n B' g φ' hinj hnzd ht0 ht hn2t hg hφ' x₁ c₁ a'₁ a₁
    hc₁ ha'₁ ha₁
  have hx2 := bSubalg_psiFun_eq A' A f t n B' g φ' hinj hnzd ht0 ht hn2t hg hφ' x₂ c₂ a'₂ a₂
    hc₂ ha'₂ ha₂
  have hsum : bSubalg_psiFun A' A f t n B' g φ' hinj ht hn2t hφ' (x₁ + x₂)
      = Ideal.Quotient.mk _ (a₁ + a₂) := by
    refine bSubalg_psiFun_eq A' A f t n B' g φ' hinj hnzd ht0 ht hn2t hg hφ' (x₁ + x₂)
      (c₁ + c₂) (a'₁ + a'₂) (a₁ + a₂) ?_ ?_ ?_
    · rw [map_add, hc₁, hc₂, AddMemClass.coe_add, mul_add]
    · rw [map_add, ha'₁, ha'₂, map_add, map_add]
    · rw [map_add, ha₁, ha₂]; ring
  rw [hsum, hx1, hx2, map_add]

/-- `bSubalg_psiFun (x₁ * x₂) = bSubalg_psiFun x₁ * bSubalg_psiFun x₂`. -/
lemma bSubalg_psiFun_mul (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (hnzd : algebraMap A' A f ∈ nonZeroDivisors A)
    (ht0 : 0 < t)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n) (hn2t1 : 2 * t < n) (hg : g ∈ nonZeroDivisors B')
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (x₁ x₂ : bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') :
    bSubalg_psiFun A' A f t n B' g φ' hinj ht hn2t hφ' (x₁ * x₂)
      = bSubalg_psiFun A' A f t n B' g φ' hinj ht hn2t hφ' x₁
        * bSubalg_psiFun A' A f t n B' g φ' hinj ht hn2t hφ' x₂ := by
  obtain ⟨c₁, a'₁, a₁, hc₁, ha'₁, ha₁, hN₁⟩ :=
    bSubalg_exists_rep A' A f t n B' g φ' hinj ht hn2t hφ' x₁
  obtain ⟨c₂, a'₂, a₂, hc₂, ha'₂, ha₂, hN₂⟩ :=
    bSubalg_exists_rep A' A f t n B' g φ' hinj ht hn2t hφ' x₂
  have hx1 := bSubalg_psiFun_eq A' A f t n B' g φ' hinj hnzd ht0 ht hn2t hg hφ' x₁ c₁ a'₁ a₁
    hc₁ ha'₁ ha₁
  have hx2 := bSubalg_psiFun_eq A' A f t n B' g φ' hinj hnzd ht0 ht hn2t hg hφ' x₂ c₂ a'₂ a₂
    hc₂ ha'₂ ha₂
  set Gm := algebraMap B' (Localization.Away g) with hGmdef
  set G := Gm g with hGdef
  obtain ⟨c'', hN'', hmul⟩ :=
    exists_mem_nIdeal_mul_eq A' A f t n B' g φ' hinj ht hn2t hφ' c₁ c₂ hN₁ hN₂
  have hGunit : IsUnit (G ^ t) := (IsLocalization.Away.algebraMap_isUnit g).pow t
  have hcc'' : Gm c'' = G ^ t * ((x₁ * x₂ : bSubalg A' A f t n B' g φ' hinj ht hn2t hφ')
      : Localization.Away g) := by
    have hlhs : Gm (c₁ * c₂) = G ^ t * Gm c'' := by rw [hmul, map_mul, map_pow, ← hGdef]
    have hprod : Gm (c₁ * c₂) = G ^ t * (G ^ t * ((x₁ * x₂ :
        bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') : Localization.Away g)) := by
      rw [map_mul, hc₁, hc₂, Subalgebra.coe_mul]; ring
    have : G ^ t * Gm c'' = G ^ t * (G ^ t * ((x₁ * x₂ :
        bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') : Localization.Away g)) := by
      rw [← hlhs, hprod]
    exact hGunit.mul_left_cancel this
  obtain ⟨a'', ha''⟩ := Ideal.Quotient.mk_surjective
    (φ'.symm (Ideal.Quotient.mk (Ideal.span {g ^ n}) c''))
  have hφft := symm_map_mk_pow_eq_mk_pow f g t φ' hφ'
  have hmkprod : Ideal.Quotient.mk (Ideal.span {f ^ n}) (a'₁ * a'₂)
      = Ideal.Quotient.mk (Ideal.span {f ^ n}) (f ^ t * a'') := by
    rw [map_mul, ha'₁, ha'₂, ← map_mul]
    rw [show Ideal.Quotient.mk (Ideal.span {g ^ n}) c₁
          * Ideal.Quotient.mk (Ideal.span {g ^ n}) c₂
        = Ideal.Quotient.mk (Ideal.span {g ^ n}) (c₁ * c₂) from (map_mul _ _ _).symm]
    rw [hmul, map_mul, map_mul, hφft, ← ha'', ← map_mul]
  obtain ⟨e, he⟩ := exists_eq_add_pow_mul_of_mk_eq f n hmkprod
  have hnt : algebraMap A' A f ^ n
      = algebraMap A' A f ^ t * algebraMap A' A f ^ t * algebraMap A' A f ^ (n - 2 * t) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have haa : algebraMap A' A a''
      = algebraMap A' A f ^ t
        * (a₁ * a₂ - algebraMap A' A f ^ (n - 2 * t) * algebraMap A' A e) := by
    refine (mul_cancel_left_mem_nonZeroDivisors (pow_mem hnzd t)).mp ?_
    have hLA : algebraMap A' A (a'₁ * a'₂)
        = algebraMap A' A f ^ t * algebraMap A' A f ^ t * (a₁ * a₂) := by
      rw [map_mul, ha₁, ha₂]; ring
    have hRA : algebraMap A' A (a'₁ * a'₂)
        = algebraMap A' A f ^ t * algebraMap A' A a'' + algebraMap A' A f ^ n * algebraMap A' A e :=
      by rw [he, map_add, map_mul, map_mul, map_pow, map_pow]
    linear_combination hLA - hRA - algebraMap A' A e * hnt
  have hprodval : bSubalg_psiFun A' A f t n B' g φ' hinj ht hn2t hφ' (x₁ * x₂)
      = Ideal.Quotient.mk _ (a₁ * a₂ - algebraMap A' A f ^ (n - 2 * t) * algebraMap A' A e) :=
    bSubalg_psiFun_eq A' A f t n B' g φ' hinj hnzd ht0 ht hn2t hg hφ' (x₁ * x₂)
      c'' a'' (a₁ * a₂ - algebraMap A' A f ^ (n - 2 * t) * algebraMap A' A e)
      hcc'' ha'' haa
  rw [hprodval, hx1, hx2, ← map_mul]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [Ideal.mem_span_singleton]
  refine ⟨- (algebraMap A' A f ^ (n - 2 * t - 1) * algebraMap A' A e), ?_⟩
  have hsplit : algebraMap A' A f ^ (n - 2 * t)
      = algebraMap A' A f * algebraMap A' A f ^ (n - 2 * t - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hsplit]; ring

/-- The ring homomorphism `ψ : B/gB →+* A/fA` sending the class of `x` to the class of `a`,
where `algebraMap c = g^t · x` with `c ∈ N`, `mk a' = φ'⁻¹(mk c)` and
`algebraMap a' = f^t · a`. -/
noncomputable def bSubalg_psiHom
    (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (hnzd : algebraMap A' A f ∈ nonZeroDivisors A)
    (ht0 : 0 < t)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n) (hn2t1 : 2 * t < n) (hg : g ∈ nonZeroDivisors B')
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g) :
    ((bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') ⧸
        Ideal.span {algebraMap B' (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') g}) →+*
      (A ⧸ Ideal.span {algebraMap A' A f}) :=
  { toFun := Quotient.lift
      (bSubalg_psiFun A' A f t n B' g φ' hinj ht hn2t hφ')
      (fun x₁ x₂ h => bSubalg_psiFun_wd A' A f t n B' g φ' hinj hnzd ht0 ht hn2t hg hφ' x₁ x₂
        (Quotient.sound h))
    map_one' := bSubalg_psiFun_one A' A f t n B' g φ' hinj hnzd ht0 ht hn2t hg hφ'
    map_mul' := by
      refine Quotient.ind₂ (fun x₁ x₂ => ?_)
      exact bSubalg_psiFun_mul A' A f t n B' g φ' hinj hnzd ht0 ht hn2t hn2t1 hg hφ' x₁ x₂
    map_zero' := bSubalg_psiFun_zero A' A f t n B' g φ' hinj hnzd ht0 ht hn2t hg hφ'
    map_add' := by
      refine Quotient.ind₂ (fun x₁ x₂ => ?_)
      exact bSubalg_psiFun_add A' A f t n B' g φ' hinj hnzd ht0 ht hn2t hg hφ' x₁ x₂ }
