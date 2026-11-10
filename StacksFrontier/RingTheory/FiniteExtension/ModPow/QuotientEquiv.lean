module

public import StacksFrontier.RingTheory.FiniteExtension.ModPow.InverseMap

/-!
# The isomorphism `A/fA ≃ B/gB` and its functoriality

This file shows that `bSubalg_phiHom` and `bSubalg_psiHom` are mutually inverse and compatible
with the reduction maps. This proves Stacks Tag 0GLT: for `n` large enough, every ring
isomorphism `φ' : A'/f^n A' ≃ B'/g^n B'` with `φ'(f) ≡ g` comes with a finite ring extension
`B' ⊂ B` and a ring isomorphism `φ : A/fA ≃ B/gB` compatible with `φ'`. It then proves the
functoriality of that construction in a commutative square of the given finite extensions
(Stacks Tag 0GLU).

## Main results

* `bSubalg_iso`: the ring isomorphism `A/fA ≃+* B/gB` compatible with `φ'`.
* `exists_bound_finite_extension_ringEquiv_mod`: Stacks Tag 0GLT (Lemma 15.118.3).
* `exists_compatible_finite_extensions_of_quotient_equiv`: Stacks Tag 0GLU, the functoriality of
  that construction in a commutative square of the given finite extensions.

## Implementation notes

For the functoriality statement, the two displayed output diagrams are equalities of ring
homomorphisms, and the source's references to `g` in the second rings mean its image under the
relevant structural map.

## References

* [Stacks Project, Tag 0GLT](https://stacks.math.columbia.edu/tag/0GLT)
* [Stacks Project, Tag 0GLU](https://stacks.math.columbia.edu/tag/0GLU)
-/

@[expose] public section

universe u v w

/-- `ψ ∘ φ = id` on `A/fA`. -/
lemma bSubalg_psi_phi (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (hnzd : algebraMap A' A f ∈ nonZeroDivisors A)
    (ht0 : 0 < t)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n) (hn2t1 : 2 * t < n) (hg : g ∈ nonZeroDivisors B')
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g) :
    (bSubalg_psiHom A' A f t n B' g φ' hinj hnzd ht0 ht hn2t hn2t1 hg hφ').comp
        (bSubalg_phiHom A' A f t n B' g φ' hinj ht0 ht hn2t hn2t1 hg hφ')
      = RingHom.id _ := by
  refine RingHom.ext (fun x => ?_)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.comp_apply, RingHom.id_apply]
  set c := bSubalg_crep A' A f t n B' g φ' ht a with hcdef
  set a' := bSubalg_arep A' A f t ht a with ha'def
  have ha : algebraMap A' A f ^ t * a = algebraMap A' A a' := bSubalg_arep_spec A' A f t ht a
  have hc : φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) a')
      = Ideal.Quotient.mk (Ideal.span {g ^ n}) c :=
    (bSubalg_crep_spec A' A f t n B' g φ' ht a).symm
  have hN : c ∈ nIdeal A' A f t n B' g φ' := bSubalg_crep_mem A' A f t n B' g φ' ht a
  have hphi : (bSubalg_phiHom A' A f t n B' g φ' hinj ht0 ht hn2t hn2t1 hg hφ')
      (Ideal.Quotient.mk (Ideal.span {algebraMap A' A f}) a)
      = Ideal.Quotient.mk _ (mkB A' A f t n B' g φ' hinj ht hn2t hφ' c hN) := by
    change bSubalg_phiFun A' A f t n B' g φ' hinj ht hn2t hφ' a = _
    exact bSubalg_phiFun_eq A' A f t n B' g φ' hinj ht0 ht hn2t hφ' a a' c ha hc hN
  rw [hphi]
  change bSubalg_psiFun A' A f t n B' g φ' hinj ht hn2t hφ'
      (mkB A' A f t n B' g φ' hinj ht hn2t hφ' c hN) = _
  refine bSubalg_psiFun_eq A' A f t n B' g φ' hinj hnzd ht0 ht hn2t hg hφ'
    (mkB A' A f t n B' g φ' hinj ht hn2t hφ' c hN) c a' a ?_ ?_ ha.symm
  · exact (mkB_spec A' A f t n B' g φ' hinj ht hn2t hφ' c hN).symm
  · rw [← hc, RingEquiv.symm_apply_apply]

/-- An element `y` of `Localization.Away g` with `g ^ t * y = c` is the underlying element of
`mkB c`. -/
private lemma coe_mkB_eq_of_pow_mul_eq (A' : Type u) (A : Type v) [CommRing A'] [CommRing A]
    [Algebra A' A] (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    {c : B'} {hN : c ∈ nIdeal A' A f t n B' g φ'} {y : Localization.Away g}
    (h : algebraMap B' (Localization.Away g) g ^ t * y = algebraMap B' (Localization.Away g) c) :
    ((mkB A' A f t n B' g φ' hinj ht hn2t hφ' c hN : bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') :
      Localization.Away g) = y :=
  ((IsLocalization.Away.algebraMap_isUnit g).pow t).mul_right_injective
    ((mkB_spec A' A f t n B' g φ' hinj ht hn2t hφ' c hN).trans h.symm)

/-- `φ ∘ ψ = id` on `B/gB`. -/
lemma bSubalg_phi_psi (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (hnzd : algebraMap A' A f ∈ nonZeroDivisors A)
    (ht0 : 0 < t)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n) (hn2t1 : 2 * t < n) (hg : g ∈ nonZeroDivisors B')
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g) :
    (bSubalg_phiHom A' A f t n B' g φ' hinj ht0 ht hn2t hn2t1 hg hφ').comp
        (bSubalg_psiHom A' A f t n B' g φ' hinj hnzd ht0 ht hn2t hn2t1 hg hφ')
      = RingHom.id _ := by
  refine RingHom.ext (fun y => ?_)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [RingHom.comp_apply, RingHom.id_apply]
  set aAx := bSubalg_aA A' A f t n B' g φ' hinj ht hn2t hφ' x with haAxdef
  set a'' := bSubalg_arepB A' A f t n B' g φ' hinj ht hn2t hφ' x with ha''def
  set c' := bSubalg_crepB A' A f t n B' g φ' hinj ht hn2t hφ' x with hc'def
  have haaspec : algebraMap A' A a'' = algebraMap A' A f ^ t * aAx :=
    bSubalg_aA_spec A' A f t n B' g φ' hinj ht hn2t hφ' x
  have haA : algebraMap A' A f ^ t * aAx = algebraMap A' A a'' := haaspec.symm
  have hc'N : c' ∈ nIdeal A' A f t n B' g φ' :=
    bSubalg_crepB_mem A' A f t n B' g φ' hinj ht hn2t hφ' x
  have ha''spec : Ideal.Quotient.mk (Ideal.span {f ^ n}) a''
      = φ'.symm (Ideal.Quotient.mk (Ideal.span {g ^ n}) c') :=
    bSubalg_arepB_spec A' A f t n B' g φ' hinj ht hn2t hφ' x
  have hc' : φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) a'')
      = Ideal.Quotient.mk (Ideal.span {g ^ n}) c' := by
    rw [ha''spec, RingEquiv.apply_symm_apply]
  have hpsi : (bSubalg_psiHom A' A f t n B' g φ' hinj hnzd ht0 ht hn2t hn2t1 hg hφ')
      (Ideal.Quotient.mk _ x)
      = Ideal.Quotient.mk (Ideal.span {algebraMap A' A f}) aAx := rfl
  rw [hpsi]
  change bSubalg_phiFun A' A f t n B' g φ' hinj ht hn2t hφ' aAx = _
  rw [bSubalg_phiFun_eq A' A f t n B' g φ' hinj ht0 ht hn2t hφ' aAx a'' c'
    haA hc' hc'N]
  congr 1
  apply Subtype.coe_injective
  refine coe_mkB_eq_of_pow_mul_eq A' A f t n B' g φ' hinj ht hn2t hφ' ?_
  exact (bSubalg_crepB_spec A' A f t n B' g φ' hinj ht hn2t hφ' x).symm

/-- The reduction square commutes: `φ ∘ reductionMap A' A f n = reductionMap B' B g n ∘ φ'`. -/
lemma bSubalg_square (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht0 : 0 < t)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n) (hn2t1 : 2 * t < n) (hg : g ∈ nonZeroDivisors B') (hn : 1 ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g) :
    (bSubalg_phiHom A' A f t n B' g φ' hinj ht0 ht hn2t hn2t1 hg hφ').comp
        (reductionMap A' A f n hn)
      = (reductionMap B' (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') g n hn).comp
        (φ' : (A' ⧸ Ideal.span {f ^ n}) →+* _) := by
  refine RingHom.ext (fun x => ?_)
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.comp_apply, RingHom.comp_apply]
  have hred : reductionMap A' A f n hn (Ideal.Quotient.mk (Ideal.span {f ^ n}) a')
      = Ideal.Quotient.mk (Ideal.span {algebraMap A' A f}) (algebraMap A' A a') := rfl
  rw [hred]
  obtain ⟨c0, hc0⟩ := Ideal.Quotient.mk_surjective
    (φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) a'))
  have hredB : reductionMap B' (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') g n hn
        ((φ' : (A' ⧸ Ideal.span {f ^ n}) →+* _) (Ideal.Quotient.mk (Ideal.span {f ^ n}) a'))
      = Ideal.Quotient.mk
          (Ideal.span {algebraMap B' (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') g})
          (algebraMap B' (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') c0) := by
    change reductionMap B' (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') g n hn
        (φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) a')) = _
    rw [← hc0]; rfl
  rw [hredB]
  change bSubalg_phiFun A' A f t n B' g φ' hinj ht hn2t hφ' (algebraMap A' A a') = _
  have ha : algebraMap A' A f ^ t * algebraMap A' A a'
      = algebraMap A' A (f ^ t * a') := by rw [map_mul, map_pow]
  have hc : φ' (Ideal.Quotient.mk (Ideal.span {f ^ n}) (f ^ t * a'))
      = Ideal.Quotient.mk (Ideal.span {g ^ n}) (g ^ t * c0) := by
    rw [map_mul, map_mul, map_pow, map_pow, hφ', ← hc0, map_mul, map_pow]
  have hgtN : g ^ t ∈ nIdeal A' A f t n B' g φ' :=
    gPow_mem_nIdeal A' A f t n B' g φ' hφ'
  have hN : g ^ t * c0 ∈ nIdeal A' A f t n B' g φ' :=
    Ideal.mul_mem_right c0 _ hgtN
  rw [bSubalg_phiFun_eq A' A f t n B' g φ' hinj ht0 ht hn2t hφ'
    (algebraMap A' A a') (f ^ t * a') (g ^ t * c0) ha hc hN]
  congr 1
  refine Subtype.ext (coe_mkB_eq_of_pow_mul_eq A' A f t n B' g φ' hinj ht hn2t hφ' ?_)
  rw [Subalgebra.coe_algebraMap, map_mul, map_pow]

/-- There is a ring isomorphism `φ : A/fA ≃+* B/gB` with
`φ ∘ reductionMap A' A f n = reductionMap B' B g n ∘ φ'`. -/
lemma bSubalg_iso (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (hnzd : algebraMap A' A f ∈ nonZeroDivisors A)
    (ht0 : 0 < t)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n) (hn2t1 : 2 * t < n) (hg : g ∈ nonZeroDivisors B') (hn : 1 ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g) :
    ∃ φ : (A ⧸ Ideal.span {algebraMap A' A f}) ≃+*
        ((bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') ⧸
          Ideal.span {algebraMap B' (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') g}),
      (φ : (A ⧸ Ideal.span {algebraMap A' A f}) →+* _).comp
          (reductionMap A' A f n hn)
        = (reductionMap B' (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') g n hn).comp
          (φ' : (A' ⧸ Ideal.span {f ^ n}) →+* _) := by
  refine ⟨RingEquiv.ofRingHom
      (bSubalg_phiHom A' A f t n B' g φ' hinj ht0 ht hn2t hn2t1 hg hφ')
      (bSubalg_psiHom A' A f t n B' g φ' hinj hnzd ht0 ht hn2t hn2t1 hg hφ')
      (bSubalg_phi_psi A' A f t n B' g φ' hinj hnzd ht0 ht hn2t hn2t1 hg hφ')
      (bSubalg_psi_phi A' A f t n B' g φ' hinj hnzd ht0 ht hn2t hn2t1 hg hφ'), ?_⟩
  exact bSubalg_square A' A f t n B' g φ' hinj ht0 ht hn2t hn2t1 hg hn hφ'

/-- Given `t > 0` with `f^t A ⊆ A'`, an exponent `n` with `2t < n`, a nonzerodivisor `g ∈ B'`
and a ring isomorphism `φ' : A'/f^n A' ≃+* B'/g^n B'` with `φ'(f̄) = ḡ`, there are a finite ring
extension `B' ⊂ B` and a ring isomorphism `φ : A/fA ≃+* B/gB` compatible with `φ'`. -/
lemma exists_finite_extension_quotient_ringEquiv
    (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (hinj : Function.Injective (algebraMap A' A))
    (f : A')
    [Module.Finite A' A]
    (hnzd : algebraMap A' A f ∈ nonZeroDivisors A)
    (t : ℕ) (ht0 : 0 < t)
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (n : ℕ) (hn2t1 : 2 * t < n)
    (B' : Type w) [CommRing B'] (g : B') (hg : g ∈ nonZeroDivisors B')
    (hn : 1 ≤ n)
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g) :
    ∃ (B : Type w) (_ : CommRing B) (_ : Algebra B' B),
      Function.Injective (algebraMap B' B) ∧
      Module.Finite B' B ∧
      ∃ φ : (A ⧸ Ideal.span {algebraMap A' A f}) ≃+*
          (B ⧸ Ideal.span {algebraMap B' B g}),
        (φ : (A ⧸ Ideal.span {algebraMap A' A f}) →+* _).comp
            (reductionMap A' A f n hn)
          = (reductionMap B' B g n hn).comp
            (φ' : (A' ⧸ Ideal.span {f ^ n}) →+* _) :=
  ⟨bSubalg A' A f t n B' g φ' hinj ht hn2t1.le hφ', inferInstance, inferInstance,
    bSubalg_algebraMap_injective A' A f t n B' g φ' hinj ht hn2t1.le hφ' hg,
    bSubalg_finite A' A f t n B' g φ' hinj ht hn2t1.le hφ',
    bSubalg_iso A' A f t n B' g φ' hinj hnzd ht0 ht hn2t1.le hn2t1 hg hn hφ'⟩

/-- **Stacks 0GLT**.
Let `A' ⊂ A` be an extension of rings and `f ∈ A'`, with `A` finite over `A'`, `f` a nonzerodivisor
on `A`, and `A'_f = A_f`. Then there is `n₀ > 0` such that for all `n ≥ n₀`: for every ring `B'`,
every nonzerodivisor `g ∈ B'`, and every ring isomorphism `φ' : A'/f^n A' ≃ B'/g^n B'` sending
the class of `f` to the class of `g`, there exist a finite ring extension `B' ⊂ B` and a ring
isomorphism `φ : A/fA ≃ B/gB` compatible with `φ'`, i.e. making the square of reduction maps
commute. -/
@[stacks 0GLT]
theorem exists_bound_finite_extension_ringEquiv_mod
    (A' : Type u) (A : Type v) [CommRing A'] [CommRing A] [Algebra A' A]
    (hinj : Function.Injective (algebraMap A' A))
    (f : A')
    [Module.Finite A' A]
    (hnzd : algebraMap A' A f ∈ nonZeroDivisors A)
    (hloc : LocalizationEq A' A f) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∀ (B' : Type w) [CommRing B'] (g : B') (_ : g ∈ nonZeroDivisors B')
        (hn : 1 ≤ n)
        (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n})),
        φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g →
        ∃ (B : Type w) (_ : CommRing B) (_ : Algebra B' B),
          Function.Injective (algebraMap B' B) ∧
          Module.Finite B' B ∧
          ∃ φ : (A ⧸ Ideal.span {algebraMap A' A f}) ≃+*
              (B ⧸ Ideal.span {algebraMap B' B g}),
            (φ : (A ⧸ Ideal.span {algebraMap A' A f}) →+* _).comp
                (reductionMap A' A f n hn)
              = (reductionMap B' B g n hn).comp
                (φ' : (A' ⧸ Ideal.span {f ^ n}) →+* _) := by
  obtain ⟨t, ht0, ht⟩ := exists_pow_mul_mem_range_algebraMap A' A f hloc
  refine ⟨2 * t + 1, by omega, ?_⟩
  intro n hn₀ B' _ g hg hn φ' hφ'
  exact exists_finite_extension_quotient_ringEquiv A' A hinj f hnzd t ht0 ht n (by omega) B' g hg hn
      φ' hφ'

/-! ### Functoriality of the construction -/

universe u₁ v₁ u₂ v₂ w₁ w₂

/-- If `f ^ r * x` is the image of an element of `R` for every `x : S`, then so is `f ^ t * x`
for every exponent `t ≥ r`. -/
private lemma exists_pow_mul_eq_of_le
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (f : R)
    {r t : ℕ} (hrt : r ≤ t)
    (h : ∀ x : S, ∃ y : R, algebraMap R S f ^ r * x = algebraMap R S y) :
    ∀ x : S, ∃ y : R, algebraMap R S f ^ t * x = algebraMap R S y := by
  intro x
  obtain ⟨y, hy⟩ := h x
  refine ⟨f ^ (t - r) * y, ?_⟩
  rw [map_mul, map_pow, ← hy, ← mul_assoc, ← pow_add]
  congr 2
  omega

/-- If `φ x = y`, then `φ` maps the ideal `(x)` into the ideal `(y)`. -/
private lemma span_singleton_le_comap_span_singleton {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) {x : R} {y : S} (h : φ x = y) :
    Ideal.span {x} ≤ (Ideal.span {y}).comap φ := by
  refine Ideal.span_le.2 ?_
  rintro _ rfl
  rw [SetLike.mem_coe, Ideal.mem_comap, h]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- A commutative square of ring maps carries `f ^ t * x = c` to `a' f ^ t * a x = a' c`. -/
private lemma pow_mul_map_eq_algebraMap {A₁' A₁ A₂' A₂ : Type*}
    [CommRing A₁'] [CommRing A₁] [CommRing A₂'] [CommRing A₂]
    [Algebra A₁' A₁] [Algebra A₂' A₂] {a' : A₁' →+* A₂'} {a : A₁ →+* A₂}
    (ha : a.comp (algebraMap A₁' A₁) = (algebraMap A₂' A₂).comp a') {f c : A₁'} {t : ℕ}
    {x : A₁} (hc : algebraMap A₁' A₁ f ^ t * x = algebraMap A₁' A₁ c) :
    algebraMap A₂' A₂ (a' f) ^ t * a x = algebraMap A₂' A₂ (a' c) := by
  have haf : a (algebraMap A₁' A₁ f) = algebraMap A₂' A₂ (a' f) := DFunLike.congr_fun ha f
  rw [← haf, ← map_pow, ← map_mul, hc]
  exact DFunLike.congr_fun ha c

/-- Every element of `bSubalg` becomes an element of `B'` after multiplying by `g ^ t`. -/
private lemma bSubalg_localizationEq (A' : Type u) (A : Type v) [CommRing A'] [CommRing A]
    [Algebra A' A] (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g) :
    LocalizationEq B' (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') g := by
  intro x
  obtain ⟨c, hc, _⟩ := x.2
  exact ⟨t, c, Subtype.ext hc.symm⟩

/-- The image of `g` in `bSubalg` is a nonzerodivisor. -/
private lemma bSubalg_algebraMap_mem_nonZeroDivisors (A' : Type u) (A : Type v) [CommRing A']
    [CommRing A] [Algebra A' A] (f : A') (t n : ℕ) (B' : Type w) [CommRing B'] (g : B')
    (φ' : (A' ⧸ Ideal.span {f ^ n}) ≃+* (B' ⧸ Ideal.span {g ^ n}))
    (hinj : Function.Injective (algebraMap A' A))
    (ht : ∀ a : A, ∃ a' : A', algebraMap A' A f ^ t * a = algebraMap A' A a')
    (hn2t : 2 * t ≤ n)
    (hφ' : φ' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g) :
    algebraMap B' (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') g ∈
      nonZeroDivisors (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ') := by
  apply mem_nonZeroDivisors_of_injective
    (f := (bSubalg A' A f t n B' g φ' hinj ht hn2t hφ').val) Subtype.val_injective
  exact (IsLocalization.Away.algebraMap_isUnit g).mem_nonZeroDivisors

/-- A ring map `B₁'_g → B₂'_{b' g}` extending `b'` carries `bSubalg` into `bSubalg`, given a
commutative square of extensions and a compatible square of isomorphisms modulo `f ^ n`. -/
private lemma bSubalg_map_mem
    {A₁' : Type u₁} {A₁ : Type v₁} {A₂' : Type u₂} {A₂ : Type v₂}
    [CommRing A₁'] [CommRing A₁] [CommRing A₂'] [CommRing A₂]
    [Algebra A₁' A₁] [Algebra A₂' A₂]
    (iA₁ : Function.Injective (algebraMap A₁' A₁))
    (iA₂ : Function.Injective (algebraMap A₂' A₂))
    {a' : A₁' →+* A₂'} {a : A₁ →+* A₂}
    (ha : a.comp (algebraMap A₁' A₁) = (algebraMap A₂' A₂).comp a') {f : A₁'} {t n : ℕ}
    (hT₁ : ∀ x : A₁, ∃ y : A₁', algebraMap A₁' A₁ f ^ t * x = algebraMap A₁' A₁ y)
    (hT₂ : ∀ x : A₂, ∃ y : A₂', algebraMap A₂' A₂ (a' f) ^ t * x = algebraMap A₂' A₂ y)
    (hn2t : 2 * t ≤ n) {B₁' : Type w₁} {B₂' : Type w₂} [CommRing B₁'] [CommRing B₂']
    {b' : B₁' →+* B₂'} {g : B₁'}
    {φ₁' : (A₁' ⧸ Ideal.span {f ^ n}) ≃+* (B₁' ⧸ Ideal.span {g ^ n})}
    {φ₂' : (A₂' ⧸ Ideal.span {(a' f) ^ n}) ≃+* (B₂' ⧸ Ideal.span {(b' g) ^ n})}
    (hφsq : φ₂'.toRingHom.comp
        (Ideal.quotientMap _ a' (span_singleton_le_comap_span_singleton a' (map_pow a' f n))) =
      (Ideal.quotientMap _ b' (span_singleton_le_comap_span_singleton b' (map_pow b' g n))).comp
        φ₁'.toRingHom)
    (hφg₁ : φ₁' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (hφg₂ : φ₂' (Ideal.Quotient.mk _ (a' f)) = Ideal.Quotient.mk _ (b' g))
    (L : Localization.Away g →+* Localization.Away (b' g))
    (hL : ∀ x : B₁', L (algebraMap B₁' (Localization.Away g) x) =
      algebraMap B₂' (Localization.Away (b' g)) (b' x))
    (x : bSubalg A₁' A₁ f t n B₁' g φ₁' iA₁ hT₁ hn2t hφg₁) :
    L x.1 ∈ bSubalg A₂' A₂ (a' f) t n B₂' (b' g) φ₂' iA₂ hT₂ hn2t hφg₂ := by
  let qA : (A₁' ⧸ Ideal.span {f ^ n}) →+* (A₂' ⧸ Ideal.span {(a' f) ^ n}) :=
    Ideal.quotientMap _ a' (span_singleton_le_comap_span_singleton a' (map_pow a' f n))
  let qB : (B₁' ⧸ Ideal.span {g ^ n}) →+* (B₂' ⧸ Ideal.span {(b' g) ^ n}) :=
    Ideal.quotientMap _ b' (span_singleton_le_comap_span_singleton b' (map_pow b' g n))
  obtain ⟨c, hc, hcN⟩ := x.2
  refine ⟨b' c, ?_, ?_⟩
  · rw [← hL c, ← hL g, ← map_pow, ← map_mul, hc]
  rw [nIdeal, Ideal.mem_comap]
  rw [nIdeal, Ideal.mem_comap] at hcN
  obtain ⟨z, hz, hzeq⟩ := (Ideal.mem_map_iff_of_surjective _ φ₁'.surjective).1 hcN
  have hzmap : qA z ∈ mbarIdeal A₂' A₂ (a' f) t n := by
    refine Submodule.span_induction (p := fun z _ ↦
      qA z ∈ mbarIdeal A₂' A₂ (a' f) t n) ?_ ?_ ?_ ?_ hz
    · rintro z ⟨x₁, c₁, hc₁, rfl⟩
      apply Ideal.subset_span
      exact ⟨a x₁, a' c₁, pow_mul_map_eq_algebraMap ha hc₁, rfl⟩
    · simp
    · intro y z _ _ hy hz
      simpa using Ideal.add_mem _ hy hz
    · intro r y _ hy
      change qA (r * y) ∈ _
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ hy
  have hs : φ₂' (qA z) = qB (φ₁' z) := DFunLike.congr_fun hφsq z
  rw [show Ideal.Quotient.mk (Ideal.span {(b' g) ^ n}) (b' c) = φ₂' (qA z) from
    (congrArg qB hzeq.symm).trans hs.symm]
  exact Ideal.mem_map_of_mem _ hzmap

/-- The isomorphisms `bSubalg_phiHom` of a commutative square of extensions commute with the
maps induced on the quotients by `a` and by any map `b` of the `bSubalg`s extending `L`. -/
private lemma bSubalg_phiHom_comp_quotientMap
    {A₁' : Type u₁} {A₁ : Type v₁} {A₂' : Type u₂} {A₂ : Type v₂}
    [CommRing A₁'] [CommRing A₁] [CommRing A₂'] [CommRing A₂]
    [Algebra A₁' A₁] [Algebra A₂' A₂]
    (iA₁ : Function.Injective (algebraMap A₁' A₁))
    (iA₂ : Function.Injective (algebraMap A₂' A₂))
    {a' : A₁' →+* A₂'} {a : A₁ →+* A₂}
    (ha : a.comp (algebraMap A₁' A₁) = (algebraMap A₂' A₂).comp a') {f : A₁'} {t n : ℕ}
    (ht0 : 0 < t)
    (hT₁ : ∀ x : A₁, ∃ y : A₁', algebraMap A₁' A₁ f ^ t * x = algebraMap A₁' A₁ y)
    (hT₂ : ∀ x : A₂, ∃ y : A₂', algebraMap A₂' A₂ (a' f) ^ t * x = algebraMap A₂' A₂ y)
    (hn2t : 2 * t ≤ n) (hn2t1 : 2 * t < n)
    {B₁' : Type w₁} {B₂' : Type w₂} [CommRing B₁'] [CommRing B₂']
    {b' : B₁' →+* B₂'} {g : B₁'} (hg₁ : g ∈ nonZeroDivisors B₁')
    (hg₂ : b' g ∈ nonZeroDivisors B₂')
    {φ₁' : (A₁' ⧸ Ideal.span {f ^ n}) ≃+* (B₁' ⧸ Ideal.span {g ^ n})}
    {φ₂' : (A₂' ⧸ Ideal.span {(a' f) ^ n}) ≃+* (B₂' ⧸ Ideal.span {(b' g) ^ n})}
    (hφsq : φ₂'.toRingHom.comp
        (Ideal.quotientMap _ a' (span_singleton_le_comap_span_singleton a' (map_pow a' f n))) =
      (Ideal.quotientMap _ b' (span_singleton_le_comap_span_singleton b' (map_pow b' g n))).comp
        φ₁'.toRingHom)
    (hφg₁ : φ₁' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g)
    (hφg₂ : φ₂' (Ideal.Quotient.mk _ (a' f)) = Ideal.Quotient.mk _ (b' g))
    (L : Localization.Away g →+* Localization.Away (b' g))
    (hL : ∀ x : B₁', L (algebraMap B₁' (Localization.Away g) x) =
      algebraMap B₂' (Localization.Away (b' g)) (b' x))
    (b : bSubalg A₁' A₁ f t n B₁' g φ₁' iA₁ hT₁ hn2t hφg₁ →+*
      bSubalg A₂' A₂ (a' f) t n B₂' (b' g) φ₂' iA₂ hT₂ hn2t hφg₂)
    (hbL : ∀ x, (b x).1 = L x.1)
    (hIa : Ideal.span {algebraMap A₁' A₁ f} ≤
      (Ideal.span {algebraMap A₂' A₂ (a' f)}).comap a)
    (hIb : Ideal.span {algebraMap B₁' (bSubalg A₁' A₁ f t n B₁' g φ₁' iA₁ hT₁ hn2t hφg₁) g} ≤
      (Ideal.span {(algebraMap B₂'
        (bSubalg A₂' A₂ (a' f) t n B₂' (b' g) φ₂' iA₂ hT₂ hn2t hφg₂) (b' g))}).comap b) :
    (bSubalg_phiHom A₂' A₂ (a' f) t n B₂' (b' g) φ₂' iA₂ ht0 hT₂ hn2t hn2t1 hg₂ hφg₂).comp
        (Ideal.quotientMap _ a hIa) =
      (Ideal.quotientMap _ b hIb).comp
        (bSubalg_phiHom A₁' A₁ f t n B₁' g φ₁' iA₁ ht0 hT₁ hn2t hn2t1 hg₁ hφg₁) := by
  let qB : (B₁' ⧸ Ideal.span {g ^ n}) →+* (B₂' ⧸ Ideal.span {(b' g) ^ n}) :=
    Ideal.quotientMap _ b' (span_singleton_le_comap_span_singleton b' (map_pow b' g n))
  refine RingHom.ext fun z ↦ ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  change bSubalg_phiFun A₂' A₂ (a' f) t n B₂' (b' g) φ₂' iA₂ hT₂ hn2t hφg₂
      (a x) = Ideal.quotientMap _ b hIb
        (bSubalg_phiFun A₁' A₁ f t n B₁' g φ₁' iA₁ hT₁ hn2t hφg₁ x)
  obtain ⟨c, hc⟩ := hT₁ x
  obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective
    (φ₁' (Ideal.Quotient.mk (Ideal.span {f ^ n}) c))
  have hdN₁ : d ∈ nIdeal A₁' A₁ f t n B₁' g φ₁' :=
    lift_mem_nIdeal A₁' A₁ f t n B₁' g φ₁' c d
      (mk_arep_mem_mbarIdeal A₁' A₁ f t n x c hc) hd.symm
  have hac := pow_mul_map_eq_algebraMap ha hc
  have hs : φ₂' (Ideal.Quotient.mk _ (a' c)) = qB (φ₁' (Ideal.Quotient.mk _ c)) :=
    DFunLike.congr_fun hφsq (Ideal.Quotient.mk _ c)
  have hd₂ : φ₂' (Ideal.Quotient.mk (Ideal.span {(a' f) ^ n}) (a' c)) =
      Ideal.Quotient.mk (Ideal.span {(b' g) ^ n}) (b' d) :=
    hs.trans (congrArg qB hd.symm)
  have hdN₂ : b' d ∈ nIdeal A₂' A₂ (a' f) t n B₂' (b' g) φ₂' :=
    lift_mem_nIdeal A₂' A₂ (a' f) t n B₂' (b' g) φ₂' (a' c) (b' d)
      (mk_arep_mem_mbarIdeal A₂' A₂ (a' f) t n (a x) (a' c) hac) hd₂
  rw [bSubalg_phiFun_eq A₂' A₂ (a' f) t n B₂' (b' g) φ₂' iA₂ ht0 hT₂
    hn2t hφg₂ (a x) (a' c) (b' d) hac hd₂ hdN₂,
    bSubalg_phiFun_eq A₁' A₁ f t n B₁' g φ₁' iA₁ ht0 hT₁ hn2t hφg₁ x c d hc hd.symm hdN₁]
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ (b _)
  congr 1
  apply Subtype.ext
  rw [hbL]
  refine coe_mkB_eq_of_pow_mul_eq A₂' A₂ (a' f) t n B₂' (b' g) φ₂' iA₂ hT₂ hn2t hφg₂ ?_
  rw [← hL g, ← map_pow, ← map_mul, mkB_spec, hL]

/-- **Stacks 0GLU**. The construction of `exists_bound_finite_extension_ringEquiv_mod` is
  functorial. Given a commutative square
of finite injective ring extensions satisfying its hypotheses, and a compatible square of
isomorphisms modulo a sufficiently large common power, the two constructed finite extensions
admit a map extending the given map of base rings. Both the square of extensions and the square
of the resulting isomorphisms modulo the nonzerodivisors commute. As in the construction
`B = g^{-t} N ⊆ B'_g` of `bSubalg`, each extension becomes an isomorphism after inverting the
corresponding image of `g`, and this image is a nonzerodivisor in the constructed ring. -/
@[stacks 0GLU]
theorem exists_compatible_finite_extensions_of_quotient_equiv
    (A₁' : Type u₁) (A₁ : Type v₁) (A₂' : Type u₂) (A₂ : Type v₂)
    [CommRing A₁'] [CommRing A₁] [CommRing A₂'] [CommRing A₂]
    [Algebra A₁' A₁] [Algebra A₂' A₂]
    (iA₁ : Function.Injective (algebraMap A₁' A₁))
    (iA₂ : Function.Injective (algebraMap A₂' A₂))
    (a' : A₁' →+* A₂') (a : A₁ →+* A₂)
    (ha : a.comp (algebraMap A₁' A₁) = (algebraMap A₂' A₂).comp a')
    (f : A₁')
    (hfin₁ : Module.Finite A₁' A₁) (hfin₂ : Module.Finite A₂' A₂)
    (hnzd₁ : algebraMap A₁' A₁ f ∈ nonZeroDivisors A₁)
    (hnzd₂ : algebraMap A₂' A₂ (a' f) ∈ nonZeroDivisors A₂)
    (hloc₁ : LocalizationEq A₁' A₁ f)
    (hloc₂ : LocalizationEq A₂' A₂ (a' f)) :
    ∃ (n₀₁ : ℕ) (_ : 0 < n₀₁) (n₀₂ : ℕ) (_ : 0 < n₀₂),
      ∀ (n : ℕ) (hnmax : max n₀₁ n₀₂ ≤ n),
      ∀ (B₁' : Type w₁) (B₂' : Type w₂) [CommRing B₁'] [CommRing B₂']
        (b' : B₁' →+* B₂') (g : B₁')
        (_ : g ∈ nonZeroDivisors B₁') (_ : b' g ∈ nonZeroDivisors B₂')
        (φ₁' : (A₁' ⧸ Ideal.span {f ^ n}) ≃+* (B₁' ⧸ Ideal.span {g ^ n}))
        (φ₂' : (A₂' ⧸ Ideal.span {(a' f) ^ n}) ≃+*
          (B₂' ⧸ Ideal.span {(b' g) ^ n})),
        φ₂'.toRingHom.comp
            (Ideal.quotientMap (Ideal.span {(a' f) ^ n}) a' (by
              apply Ideal.span_le.2
              rintro _ rfl
              change a' (f ^ n) ∈ Ideal.span {(a' f) ^ n}
              rw [map_pow]
              exact Ideal.subset_span (Set.mem_singleton _))) =
          (Ideal.quotientMap (Ideal.span {(b' g) ^ n}) b' (by
            apply Ideal.span_le.2
            rintro _ rfl
            change b' (g ^ n) ∈ Ideal.span {(b' g) ^ n}
            rw [map_pow]
            exact Ideal.subset_span (Set.mem_singleton _))).comp φ₁'.toRingHom →
        φ₁' (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ g →
        ∃ (B₁ : Type w₁) (_ : CommRing B₁) (_ : Algebra B₁' B₁)
          (B₂ : Type w₂) (_ : CommRing B₂) (_ : Algebra B₂' B₂),
          Function.Injective (algebraMap B₁' B₁) ∧ Module.Finite B₁' B₁ ∧
          Function.Injective (algebraMap B₂' B₂) ∧ Module.Finite B₂' B₂ ∧
          LocalizationEq B₁' B₁ g ∧ LocalizationEq B₂' B₂ (b' g) ∧
          algebraMap B₁' B₁ g ∈ nonZeroDivisors B₁ ∧
          algebraMap B₂' B₂ (b' g) ∈ nonZeroDivisors B₂ ∧
          ∃ (b : B₁ →+* B₂)
            (hb : b.comp (algebraMap B₁' B₁) = (algebraMap B₂' B₂).comp b')
            (φ₁ : (A₁ ⧸ Ideal.span {algebraMap A₁' A₁ f}) ≃+*
              (B₁ ⧸ Ideal.span {algebraMap B₁' B₁ g}))
            (φ₂ : (A₂ ⧸ Ideal.span {algebraMap A₂' A₂ (a' f)}) ≃+*
              (B₂ ⧸ Ideal.span {algebraMap B₂' B₂ (b' g)})),
            φ₂.toRingHom.comp
                (Ideal.quotientMap (Ideal.span {algebraMap A₂' A₂ (a' f)}) a (by
                  apply Ideal.span_le.2
                  rintro _ rfl
                  change a (algebraMap A₁' A₁ f) ∈
                    Ideal.span {algebraMap A₂' A₂ (a' f)}
                  rw [show a (algebraMap A₁' A₁ f) =
                    algebraMap A₂' A₂ (a' f) from DFunLike.congr_fun ha f]
                  exact Ideal.subset_span (Set.mem_singleton _))) =
              (Ideal.quotientMap (Ideal.span {algebraMap B₂' B₂ (b' g)}) b (by
                apply Ideal.span_le.2
                rintro _ rfl
                change b (algebraMap B₁' B₁ g) ∈
                  Ideal.span {algebraMap B₂' B₂ (b' g)}
                rw [show b (algebraMap B₁' B₁ g) =
                  algebraMap B₂' B₂ (b' g) from DFunLike.congr_fun hb g]
                exact Ideal.subset_span (Set.mem_singleton _))).comp
                φ₁.toRingHom ∧
            φ₁.toRingHom.comp (reductionMap A₁' A₁ f n (by omega)) =
              (reductionMap B₁' B₁ g n (by omega)).comp φ₁'.toRingHom ∧
            φ₂.toRingHom.comp (reductionMap A₂' A₂ (a' f) n (by omega)) =
              (reductionMap B₂' B₂ (b' g) n (by omega)).comp φ₂'.toRingHom := by
  obtain ⟨t₁, ht₁0, ht₁⟩ := exists_pow_mul_mem_range_algebraMap A₁' A₁ f hloc₁
  obtain ⟨t₂, ht₂0, ht₂⟩ := exists_pow_mul_mem_range_algebraMap A₂' A₂ (a' f) hloc₂
  let t := max t₁ t₂
  have ht0 : 0 < t := lt_of_lt_of_le ht₁0 (le_max_left _ _)
  have hT₁ := exists_pow_mul_eq_of_le A₁' A₁ f (le_max_left t₁ t₂) ht₁
  have hT₂ := exists_pow_mul_eq_of_le A₂' A₂ (a' f) (le_max_right t₁ t₂) ht₂
  refine ⟨2 * t + 1, by omega, 2 * t + 1, by omega, ?_⟩
  intro n hn B₁' B₂' _ _ b' g hg₁ hg₂ φ₁' φ₂' hφsq hφg
  have hn2t : 2 * t ≤ n := by omega
  have hn2t1 : 2 * t < n := by omega
  have hn1 : 1 ≤ n := by omega
  have hφg₂ : φ₂' (Ideal.Quotient.mk _ (a' f)) = Ideal.Quotient.mk _ (b' g) := by
    simpa [hφg] using DFunLike.congr_fun hφsq (Ideal.Quotient.mk _ f)
  let B₁ := bSubalg A₁' A₁ f t n B₁' g φ₁' iA₁ hT₁ hn2t hφg
  let B₂ := bSubalg A₂' A₂ (a' f) t n B₂' (b' g) φ₂' iA₂ hT₂ hn2t hφg₂
  let L : Localization.Away g →+* Localization.Away (b' g) :=
    IsLocalization.Away.map _ _ b' g
  have hLbase (x : B₁') : L (algebraMap B₁' (Localization.Away g) x) =
      algebraMap B₂' (Localization.Away (b' g)) (b' x) := by
    simp [L, IsLocalization.Away.map]
  let b : B₁ →+* B₂ :=
    { toFun := fun x ↦ ⟨L x.1, bSubalg_map_mem iA₁ iA₂ ha hT₁ hT₂ hn2t hφsq hφg hφg₂ L hLbase x⟩
      map_one' := Subtype.ext L.map_one
      map_mul' := fun x y ↦ Subtype.ext (L.map_mul x.1 y.1)
      map_zero' := Subtype.ext L.map_zero
      map_add' := fun x y ↦ Subtype.ext (L.map_add x.1 y.1) }
  have hb : b.comp (algebraMap B₁' B₁) = (algebraMap B₂' B₂).comp b' := by
    ext x
    exact hLbase x
  let φ₁ := RingEquiv.ofRingHom
    (bSubalg_phiHom A₁' A₁ f t n B₁' g φ₁' iA₁ ht0 hT₁ hn2t hn2t1 hg₁ hφg)
    (bSubalg_psiHom A₁' A₁ f t n B₁' g φ₁' iA₁ hnzd₁ ht0 hT₁ hn2t hn2t1 hg₁ hφg)
    (bSubalg_phi_psi A₁' A₁ f t n B₁' g φ₁' iA₁ hnzd₁ ht0 hT₁ hn2t hn2t1 hg₁ hφg)
    (bSubalg_psi_phi A₁' A₁ f t n B₁' g φ₁' iA₁ hnzd₁ ht0 hT₁ hn2t hn2t1 hg₁ hφg)
  let φ₂ := RingEquiv.ofRingHom
    (bSubalg_phiHom A₂' A₂ (a' f) t n B₂' (b' g) φ₂' iA₂ ht0 hT₂ hn2t hn2t1 hg₂ hφg₂)
    (bSubalg_psiHom A₂' A₂ (a' f) t n B₂' (b' g) φ₂' iA₂ hnzd₂ ht0 hT₂ hn2t hn2t1 hg₂ hφg₂)
    (bSubalg_phi_psi A₂' A₂ (a' f) t n B₂' (b' g) φ₂' iA₂ hnzd₂ ht0 hT₂ hn2t hn2t1 hg₂ hφg₂)
    (bSubalg_psi_phi A₂' A₂ (a' f) t n B₂' (b' g) φ₂' iA₂ hnzd₂ ht0 hT₂ hn2t hn2t1 hg₂ hφg₂)
  have hsq₁ := bSubalg_square A₁' A₁ f t n B₁' g φ₁' iA₁ ht0 hT₁ hn2t hn2t1 hg₁ hn1 hφg
  have hsq₂ :=
    bSubalg_square A₂' A₂ (a' f) t n B₂' (b' g) φ₂' iA₂ ht0 hT₂ hn2t hn2t1 hg₂ hn1 hφg₂
  refine ⟨B₁, inferInstance, inferInstance, B₂, inferInstance, inferInstance,
    bSubalg_algebraMap_injective A₁' A₁ f t n B₁' g φ₁' iA₁ hT₁ hn2t hφg hg₁,
    bSubalg_finite A₁' A₁ f t n B₁' g φ₁' iA₁ hT₁ hn2t hφg,
    bSubalg_algebraMap_injective A₂' A₂ (a' f) t n B₂' (b' g) φ₂' iA₂ hT₂ hn2t hφg₂ hg₂,
    bSubalg_finite A₂' A₂ (a' f) t n B₂' (b' g) φ₂' iA₂ hT₂ hn2t hφg₂,
    bSubalg_localizationEq A₁' A₁ f t n B₁' g φ₁' iA₁ hT₁ hn2t hφg,
    bSubalg_localizationEq A₂' A₂ (a' f) t n B₂' (b' g) φ₂' iA₂ hT₂ hn2t hφg₂,
    bSubalg_algebraMap_mem_nonZeroDivisors A₁' A₁ f t n B₁' g φ₁' iA₁ hT₁ hn2t hφg,
    bSubalg_algebraMap_mem_nonZeroDivisors A₂' A₂ (a' f) t n B₂' (b' g) φ₂' iA₂ hT₂ hn2t hφg₂,
    b, hb, φ₁, φ₂, ?_, hsq₁, hsq₂⟩
  exact bSubalg_phiHom_comp_quotientMap iA₁ iA₂ ha ht0 hT₁ hT₂ hn2t hn2t1 hg₁ hg₂ hφsq hφg hφg₂
    L hLbase b (fun _ ↦ rfl) _ _
