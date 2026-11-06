module

public import StacksFrontier.RingTheory.Sequence.QuasiRegular.Defs

/-!
# The quasi-regularity map with polynomial source

Let `R` be a commutative ring, let `f : Fin c → R` and let `J = (f₀, ..., f_{c-1})`.  The canonical
map of Stacks tag 061N, `quasiRegularCanonicalMap`, is defined on the tensor product
`(R/J)[T] ⊗_{R/J} (R/JR)`.  This file records the version whose source is literally the polynomial
algebra `(R/J)[T₀, ..., T_{c-1}]`, obtained by inserting the class of `1` in the second factor,
together with the facts needed to build the sheaf-theoretic version of the map (Stacks tag 063B):

* it is a homomorphism of `(R/J)[T]`-modules, so its kernel is an ideal;
* it is surjective, so the quotient of `(R/J)[T]` by that ideal is additively the associated
  graded ring `⨁_d J^d/J^{d+1}`;
* it vanishes on a polynomial exactly when, for every `d`, the degree-`d` part
  `∑_{|e| = d} f^e a_e` of (a lift of) the polynomial lies in `J^{d+1}`.

The last item is what makes the vanishing locus of a polynomial relation open on a ringed space:
it expresses the relation by finitely many membership conditions in powers of `J`.

## Main definitions

* `associatedGradedMap f`: the map `(R/J)[T] → ⨁_d J^d/J^{d+1}`, `T^e ↦ f^e mod J^{|e|+1}`.
* `associatedGradedIdeal f`: its kernel, an ideal of `(R/J)[T]`.
* `gradedQuotEquiv f`: the resulting additive identification
  `(R/J)[T] / associatedGradedIdeal f ≃+ ⨁_d J^d/J^{d+1}`.
* `gradedPartOn f p S d`: the degree-`d` part `∑_{e ∈ S, |e| = d} f^e · (coeff e p)`.

## Main results

* `associatedGradedMap_monomial`, `associatedGradedMap_X`: the values on monomials.
* `associatedGradedMap_surjective`.
* `associatedGradedMap_map_eq_zero_iff`: the degreewise vanishing criterion.
-/

@[expose] public section

namespace Stacks.RingTheory.QuasiRegular

variable {R : Type*} [CommRing R] {c : ℕ}

section Map

/-- The class of `1` in `R/JR`, the element inserted in the second tensor factor to turn the
source of `quasiRegularCanonicalMap` into a polynomial algebra. -/
noncomputable def quotOne (f : Fin c → R) : qrMbar R f := Submodule.Quotient.mk 1

/-- The canonical map of Stacks tag 061N with its source written literally as the polynomial
algebra `(R/J)[T₀, ..., T_{c-1}]`: the `R/J`-linear map sending `a T^e` to the class of `a f^e`
in degree `|e|` of `⨁_d J^d/J^{d+1}`. -/
noncomputable def associatedGradedMap (f : Fin c → R) :
    MvPolynomial (Fin c) (qrRbar f) →ₗ[qrRbar f] Target R f :=
  (quasiRegularCanonicalMap (M := R) f).comp
    ((TensorProduct.mk (qrRbar f) _ _).flip
      ((Submodule.quotEquivOfEq (Jid f : Submodule R R)
        (Jid f • (⊤ : Submodule R R)) (by simp) : qrRbar f →ₗ[R] qrMbar R f) 1))

/-- The map `associatedGradedMap f` sends `q` to the image of `q ⊗ 1` under
`quasiRegularCanonicalMap f`. -/
theorem associatedGradedMap_apply (f : Fin c → R) (q : MvPolynomial (Fin c) (qrRbar f)) :
    associatedGradedMap f q
      = quasiRegularCanonicalMap f (q ⊗ₜ[qrRbar f] quotOne f) := by
  have h : ((Submodule.quotEquivOfEq (Jid f : Submodule R R)
      (Jid f • (⊤ : Submodule R R)) (by simp) : qrRbar f →ₗ[R] qrMbar R f) 1) = quotOne f := by
    show (Submodule.quotEquivOfEq (Jid f : Submodule R R)
      (Jid f • (⊤ : Submodule R R)) (by simp)) (Submodule.Quotient.mk (1 : R)) = quotOne f
    rw [Submodule.quotEquivOfEq_mk]
    rfl
  rw [associatedGradedMap]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
    TensorProduct.mk_apply, h]

/-- The scalar `a mod J` acts on the class of `1` in `R/JR` as the class of `a`. -/
theorem smul_quotOne (f : Fin c → R) (a : R) :
    (Ideal.Quotient.mk (Jid f) a) • (quotOne f) = (Submodule.Quotient.mk a : qrMbar R f) := by
  have h1 : (Ideal.Quotient.mk (Jid f) a) = a • (1 : qrRbar f) := by
    simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  rw [quotOne, h1, smul_assoc, one_smul]
  exact (Submodule.Quotient.mk_smul (Jid f • (⊤ : Submodule R R)) a (1 : R)).symm.trans
    (congrArg Submodule.Quotient.mk (by simp))

/-- The monomial `a T^e` goes to the class of `a f^e` in degree `|e|`. -/
theorem associatedGradedMap_monomial (f : Fin c → R) (e : Fin c →₀ ℕ) (a : R) :
    associatedGradedMap f (MvPolynomial.monomial e (Ideal.Quotient.mk (Jid f) a))
      = imgTargetLin f e a := by
  have hmono : (MvPolynomial.monomial e) ((Ideal.Quotient.mk (Jid f)) a)
      = ((Ideal.Quotient.mk (Jid f)) a) • (MvPolynomial.monomial e) (1 : qrRbar f) := by
    rw [MvPolynomial.smul_monomial]
    exact congrArg (MvPolynomial.monomial e) (by simp)
  rw [associatedGradedMap_apply, hmono, TensorProduct.smul_tmul, smul_quotOne,
    show (MvPolynomial.monomial e) (1 : qrRbar f) ⊗ₜ[qrRbar f]
      (Submodule.Quotient.mk a : qrMbar R f) = srcMono f e a from rfl,
    canonicalMap_srcMono]

/-- The variable `T i` goes to the class of `f i` in degree one. -/
theorem associatedGradedMap_X (f : Fin c → R) (i : Fin c) :
    associatedGradedMap f (MvPolynomial.X i)
      = imgTargetLin f (Finsupp.single i 1) (1 : R) := by
  rw [show (MvPolynomial.X i : MvPolynomial (Fin c) (qrRbar f))
      = MvPolynomial.monomial (Finsupp.single i 1) (Ideal.Quotient.mk (Jid f) (1 : R)) by
    rw [map_one]; rfl, associatedGradedMap_monomial]

/-- The map is a homomorphism of `(R/J)[T]`-modules: multiplying the polynomial acts by the
polynomial action on the associated graded module. -/
theorem associatedGradedMap_mul (f : Fin c → R) (p q : MvPolynomial (Fin c) (qrRbar f)) :
    associatedGradedMap f (p * q) = p • associatedGradedMap f q := by
  have hpq : (p * q) ⊗ₜ[qrRbar f] quotOne f = p • (q ⊗ₜ[qrRbar f] quotOne f) :=
    (TensorProduct.smul_tmul' p q (quotOne f)).symm
  rw [associatedGradedMap_apply, associatedGradedMap_apply, hpq,
    canonicalMap_MvPolynomial_linear]

/-- The map `(R/J)[T] → ⨁_d J^d/J^{d+1}`, as a homomorphism of `(R/J)[T]`-modules. -/
noncomputable def associatedGradedLin (f : Fin c → R) :
    MvPolynomial (Fin c) (qrRbar f) →ₗ[MvPolynomial (Fin c) (qrRbar f)] Target R f where
  toFun := associatedGradedMap f
  map_add' := map_add _
  map_smul' p q := by rw [smul_eq_mul, associatedGradedMap_mul]; rfl

/-- The underlying function of `associatedGradedLin f` is `associatedGradedMap f`. -/
@[simp]
theorem associatedGradedLin_apply (f : Fin c → R) (q : MvPolynomial (Fin c) (qrRbar f)) :
    associatedGradedLin f q = associatedGradedMap f q := rfl

/-- The kernel of the quasi-regularity map, an ideal of `(R/J)[T]`. -/
noncomputable def associatedGradedIdeal (f : Fin c → R) :
    Ideal (MvPolynomial (Fin c) (qrRbar f)) :=
  LinearMap.ker (associatedGradedLin f)

/-- A polynomial lies in `associatedGradedIdeal f` exactly when `associatedGradedMap f` vanishes
on it. -/
theorem mem_associatedGradedIdeal {f : Fin c → R} {q : MvPolynomial (Fin c) (qrRbar f)} :
    q ∈ associatedGradedIdeal f ↔ associatedGradedMap f q = 0 := Iff.rfl

/-- Tensoring with the class of `1` is surjective onto the source of the canonical map: the second
tensor factor `R/JR` is generated by the class of `1`. -/
theorem exists_tmul_quotOne (f : Fin c → R) (s : Source R f) :
    ∃ q : MvPolynomial (Fin c) (qrRbar f), q ⊗ₜ[qrRbar f] quotOne f = s := by
  induction s using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.zero_tmul _ _⟩
  | tmul q m =>
    induction m using Submodule.Quotient.induction_on with
    | H a =>
      exact ⟨(Ideal.Quotient.mk (Jid f) a) • q, by
        rw [TensorProduct.smul_tmul, smul_quotOne]⟩
  | add s₁ s₂ h₁ h₂ =>
    obtain ⟨q₁, hq₁⟩ := h₁
    obtain ⟨q₂, hq₂⟩ := h₂
    exact ⟨q₁ + q₂, by rw [TensorProduct.add_tmul, hq₁, hq₂]⟩

/-- The map `(R/J)[T] → ⨁_d J^d/J^{d+1}` is surjective. -/
theorem associatedGradedMap_surjective (f : Fin c → R) :
    Function.Surjective (associatedGradedMap f) := by
  intro t
  obtain ⟨s, hs⟩ := quasiRegularCanonicalMap_surjective (M := R) f t
  obtain ⟨q, hq⟩ := exists_tmul_quotOne f s
  exact ⟨q, by rw [associatedGradedMap_apply, hq, hs]⟩

/-- The associated graded module is additively the quotient of `(R/J)[T]` by the kernel of the
quasi-regularity map. -/
noncomputable def gradedQuotEquiv (f : Fin c → R) :
    (MvPolynomial (Fin c) (qrRbar f) ⧸ associatedGradedIdeal f) ≃+ Target R f :=
  (LinearMap.quotKerEquivOfSurjective (associatedGradedLin f)
    (associatedGradedMap_surjective f)).toAddEquiv

/-- The class of `q` goes under `gradedQuotEquiv f` to `associatedGradedMap f q`. -/
@[simp]
theorem gradedQuotEquiv_mk (f : Fin c → R) (q : MvPolynomial (Fin c) (qrRbar f)) :
    gradedQuotEquiv f (Ideal.Quotient.mk (associatedGradedIdeal f) q)
      = associatedGradedMap f q := rfl

end Map

section Graded

/-- The class in degree `d` of an element of `J^d`. -/
noncomputable def gradedClass (f : Fin c → R) (d : ℕ) (a : JpowM R f d) : Target R f :=
  DirectSum.lof R ℕ (fun n => Tcomp R f n) d (Submodule.Quotient.mk a)

/-- The submodule `JpowM R f n` of `R` is the ideal `J^n`. -/
theorem JpowM_self (f : Fin c → R) (n : ℕ) : JpowM R f n = (Jid f ^ n : Ideal R) := by
  unfold JpowM; simp

/-- An element of `R` lies in `JpowM R f n` exactly when it lies in `J^n`. -/
theorem mem_JpowM_iff {f : Fin c → R} {n : ℕ} {a : R} :
    a ∈ JpowM R f n ↔ a ∈ (Jid f ^ n : Ideal R) := by rw [JpowM_self]

/-- The degree-`d` class is additive. -/
theorem gradedClass_add (f : Fin c → R) (d : ℕ) (a b : JpowM R f d) :
    gradedClass f d (a + b) = gradedClass f d a + gradedClass f d b := by
  rw [gradedClass, gradedClass, gradedClass, Submodule.Quotient.mk_add, map_add]

/-- The degree-`d` class of `a` vanishes exactly when `a` is zero in `Tcomp R f d`. -/
private theorem gradedClass_eq_zero_iff_mk (f : Fin c → R) (d : ℕ) (a : JpowM R f d) :
    gradedClass f d a = 0 ↔ (Submodule.Quotient.mk a : Tcomp R f d) = 0 := by
  rw [gradedClass, ← map_zero (DirectSum.lof R ℕ (fun n => Tcomp R f n) d)]
  exact (DirectSum.of_injective (β := fun n => Tcomp R f n) d).eq_iff

/-- The degree-`d` class of `a ∈ J^d` vanishes exactly when `a ∈ J^{d+1}`. -/
theorem gradedClass_eq_zero_iff {f : Fin c → R} {d : ℕ} {a : JpowM R f d} :
    gradedClass f d a = 0 ↔ (a : R) ∈ (Jid f ^ (d + 1) : Ideal R) := by
  rw [gradedClass_eq_zero_iff_mk, Submodule.Quotient.mk_eq_zero]
  show a ∈ Tsub R f d ↔ _
  rw [Tsub, Submodule.mem_comap, Submodule.coe_subtype, mem_JpowM_iff]

/-- The degree-`d` class of a finite sum is the sum of the degree-`d` classes. -/
theorem gradedClass_sum {f : Fin c → R} {d : ℕ} {ι : Type*} (S : Finset ι)
    (a : ι → JpowM R f d) :
    gradedClass f d (∑ i ∈ S, a i) = ∑ i ∈ S, gradedClass f d (a i) := by
  classical
  induction S using Finset.induction with
  | empty => simp [gradedClass]
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, gradedClass_add, ih]

/-- Graded classes in distinct degrees are independent: if a finite sum of classes in pairwise
distinct degrees vanishes, each summand vanishes. -/
theorem gradedClass_eq_zero_of_sum_eq_zero {f : Fin c → R} {T : Finset ℕ}
    (w : (d : ℕ) → JpowM R f d) (h : ∑ d ∈ T, gradedClass f d (w d) = 0)
    {d : ℕ} (hd : d ∈ T) : gradedClass f d (w d) = 0 := by
  classical
  have h0 := congrArg (DirectSum.component R ℕ (fun n => Tcomp R f n) d) h
  rw [map_sum, map_zero, Finset.sum_eq_single_of_mem d hd (fun d' _ hne => by
    simp only [gradedClass, DirectSum.component.of, hne, dite_false]), gradedClass,
    DirectSum.component.lof_self] at h0
  exact (gradedClass_eq_zero_iff_mk f d _).mpr h0

/-- The element `imgTargetLin f e a` is the class of `f^e a` in degree `|e|`. -/
theorem imgTargetLin_eq_gradedClass (f : Fin c → R) (e : Fin c →₀ ℕ) (a : R) :
    imgTargetLin f e a
      = gradedClass f (qrMdeg e) ⟨fpow f e * a, by
          rw [← smul_eq_mul]; exact fpow_smul_mem f e a⟩ := by
  rw [imgTargetLin, gradedClass]
  rfl

/-- The degree-`d` contribution of the monomial indexed by `e`, as an element of `J^d`: it is
`f^e · (coeff e p)` when `|e| = d` and zero otherwise. -/
noncomputable def gradedTerm (f : Fin c → R) (p : MvPolynomial (Fin c) R) (d : ℕ)
    (e : Fin c →₀ ℕ) : JpowM R f d :=
  if h : qrMdeg e = d then
    ⟨fpow f e * p.coeff e, by
      rw [← h, ← smul_eq_mul]; exact fpow_smul_mem f e _⟩
  else 0

/-- In degree `|e|`, the contribution of the monomial indexed by `e` is `f^e · (coeff e p)`. -/
theorem gradedTerm_of_eq (f : Fin c → R) (p : MvPolynomial (Fin c) R) (e : Fin c →₀ ℕ) :
    gradedTerm f p (qrMdeg e) e
      = ⟨fpow f e * p.coeff e, by rw [← smul_eq_mul]; exact fpow_smul_mem f e _⟩ := by
  rw [gradedTerm, dite_eq_left rfl]

/-- The degree-`d` part of a polynomial `p` with coefficients in `R`, evaluated at `f`, as an
element of `J^d`.  The index set `S` is any finite set containing the support of `p`. -/
noncomputable def gradedPartSub (f : Fin c → R) (p : MvPolynomial (Fin c) R)
    (S : Finset (Fin c →₀ ℕ)) (d : ℕ) : JpowM R f d :=
  ∑ e ∈ S with qrMdeg e = d, gradedTerm f p d e

/-- The degree-`d` part of a polynomial `p` with coefficients in `R`, evaluated at `f`:
`∑_{e ∈ S, |e| = d} f^e · (coeff e p)`. -/
noncomputable def gradedPartOn (f : Fin c → R) (p : MvPolynomial (Fin c) R)
    (S : Finset (Fin c →₀ ℕ)) (d : ℕ) : R := (gradedPartSub f p S d : R)

/-- The degree-`d` part is the sum `∑_{e ∈ S, |e| = d} f^e · (coeff e p)`. -/
theorem gradedPartOn_eq_sum (f : Fin c → R) (p : MvPolynomial (Fin c) R)
    (S : Finset (Fin c →₀ ℕ)) (d : ℕ) :
    gradedPartOn f p S d = ∑ e ∈ S with qrMdeg e = d, fpow f e * p.coeff e := by
  rw [gradedPartOn, gradedPartSub, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [gradedTerm, dite_eq_left (Finset.mem_filter.mp he).2]

/-- The degree-`d` part of `p` evaluated at `f` lies in `J^d`. -/
theorem gradedPartOn_mem (f : Fin c → R) (p : MvPolynomial (Fin c) R)
    (S : Finset (Fin c →₀ ℕ)) (d : ℕ) : gradedPartOn f p S d ∈ JpowM R f d :=
  (gradedPartSub f p S d).2

/-- **The degreewise vanishing criterion.**  For a polynomial `p` with coefficients in `R`, the
reduction of `p` modulo `J` is killed by the quasi-regularity map exactly when every degree-`d`
part `∑_{|e| = d} f^e · (coeff e p)` lies in `J^{d+1}`. -/
theorem associatedGradedMap_map_eq_zero_iff (f : Fin c → R) (p : MvPolynomial (Fin c) R)
    (S : Finset (Fin c →₀ ℕ)) (hS : p.support ⊆ S) :
    associatedGradedMap f (MvPolynomial.map (Ideal.Quotient.mk (Jid f)) p) = 0
      ↔ ∀ d, gradedPartOn f p S d ∈ (Jid f ^ (d + 1) : Ideal R) := by
  classical
  set T : Finset ℕ := S.image qrMdeg with hT
  have hmapsto : ∀ e ∈ S, qrMdeg e ∈ T := fun e he => Finset.mem_image_of_mem _ he
  have hval : associatedGradedMap f (MvPolynomial.map (Ideal.Quotient.mk (Jid f)) p)
      = ∑ d ∈ T, gradedClass f d (gradedPartSub f p S d) := by
    have hsum : MvPolynomial.map (Ideal.Quotient.mk (Jid f)) p
        = ∑ e ∈ S, MvPolynomial.monomial e
            (Ideal.Quotient.mk (Jid f) (p.coeff e)) := by
      conv_lhs => rw [MvPolynomial.as_sum p]
      rw [map_sum, Finset.sum_subset hS]
      · exact Finset.sum_congr rfl fun e _ => MvPolynomial.map_monomial _ _ _
      · intro e _ he
        rw [MvPolynomial.notMem_support_iff] at he
        rw [MvPolynomial.map_monomial, he, map_zero, MvPolynomial.monomial_zero]
    rw [hsum, map_sum,
      Finset.sum_congr rfl (fun e _ => associatedGradedMap_monomial f e _),
      Finset.sum_congr rfl (fun e (_ : e ∈ S) => by
        rw [imgTargetLin_eq_gradedClass f e (p.coeff e), ← gradedTerm_of_eq f p e]),
      ← Finset.sum_fiberwise_of_maps_to hmapsto]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [gradedPartSub, gradedClass_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    obtain ⟨-, hd⟩ := Finset.mem_filter.mp he
    subst hd
    rfl
  rw [hval]
  refine ⟨fun h d => ?_, fun h => Finset.sum_eq_zero fun d _ =>
    gradedClass_eq_zero_iff.mpr (h d)⟩
  by_cases hdT : d ∈ T
  · exact gradedClass_eq_zero_iff.mp
      (gradedClass_eq_zero_of_sum_eq_zero (gradedPartSub f p S) h hdT)
  · have hzero : gradedPartOn f p S d = 0 := by
      rw [gradedPartOn_eq_sum, Finset.sum_eq_zero]
      intro e he
      obtain ⟨heS, hd⟩ := Finset.mem_filter.mp he
      exact absurd (hd ▸ hmapsto e heS) hdT
    rw [hzero]
    exact Submodule.zero_mem _

end Graded

end Stacks.RingTheory.QuasiRegular
