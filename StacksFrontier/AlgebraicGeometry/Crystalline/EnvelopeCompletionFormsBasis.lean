module

public import Mathlib.RingTheory.Kaehler.Polynomial
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedEnvelopeFactorizationForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedTensorFreeFinite
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionLevelIndependence
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionTowerComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Envelope

/-!
# The completed one-forms of a completed envelope are free on the `d x_i`

Let `(A, I, γ)` be a divided power ring, `P = A[x_i : i ∈ ι]` a polynomial algebra in finitely
many variables, `J ⊆ P` an ideal containing `I P`, `E = D_{P,γ}(J)` the divided power envelope
and `D` its `p`-adic completion, with `p` a prime nilpotent modulo the divided power ideal of
`E`.  The `p`-adically completed divided power one-forms `Ω̂¹_D` of the ring `D` itself are free
over `D` on the differentials `d x_i`.

A ring carrying divided powers on an ideal modulo which `p` is nilpotent is canonically a
`ℤ_(p)`-algebra, so no `ℤ_(p)`-structure is assumed.

## Main definitions

* `Crystalline.algebraIntegersAtPrimeOfIsNilpotent` — the `ℤ_(p)`-algebra structure of a divided
  power ring in which `p` is nilpotent modulo the divided power ideal, and
  `Crystalline.dividedPowerDifferentialsCompletionComparisonOfIsNilpotent`, the comparison of
  [Stacks, Tag 07KK] with no `ℤ_(p)`-structure assumed.
* `Crystalline.adicCompletionPiSelfEquiv` — `(R^ι)^∧ ≃ (R^∧)^ι`, with the standard module
  structure on the right.
* `Crystalline.completedDifferentialsCompletionEquiv` — the completions of `Ω_{B̂/A,γ̂}` and of
  `Ω̂_{B/A,δ}` agree.
* `Crystalline.completedDividedPowerFormsAlgebraCongr` — the completed forms for two equal
  algebra structures agree.
* `Crystalline.completedDividedPowerFormsBasisOfBasis` — for a divided power ring whose divided
  power differentials have a finite basis, the basis of the completed one-forms of its
  completion.
* `Crystalline.envelopeDifferentialsBasis` — the basis of `Ω_{E/A,δ}` on the `d y_i`.
* `Crystalline.envelopeCompletionFormsEquivPi` and `Crystalline.envelopeCompletionFormsBasis` —
  **`Ω̂¹_D ≃ D^ι`, and the basis of `Ω̂¹_D` on the `d x_i`**.

## Main results

* `Crystalline.envelopeCompletionFormsBasis_apply` — the basis vector of index `i` is
  `d x_i`.
* `Crystalline.completedMapDifferentialForms_id` and
  `Crystalline.completedMapDifferentialForms_comp` — the comparison of completed forms along a
  divided power morphism is functorial.
* `Crystalline.completedMapDifferentialForms_differentialOnRing` — the comparison carries `d b`
  to `d (f b)`.

## References

* [Stacks Project, Tag 07HW](https://stacks.math.columbia.edu/tag/07HW)
* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
-/

@[expose] public noncomputable section

namespace Crystalline

open DividedPowers

universe u v w

/-! ### The `ℤ_(p)`-algebra structure of a divided power ring -/

section IntegersAtPrime

variable {B : Type v} [CommRing B] {J : Ideal B} {p : ℕ}

/-- **An integer prime to `p` is a unit in a divided power ring in which `p` is nilpotent modulo
the divided power ideal.** -/
public theorem isUnit_natCast_of_coprime_of_isNilpotent (delta : _root_.DividedPowers J)
    (hp : IsNilpotent (Ideal.Quotient.mk J (p : B))) {m : ℕ} (hm0 : m ≠ 0)
    (hm : Nat.Coprime m p) : IsUnit (m : B) := by
  obtain ⟨N, hN⟩ := hp
  have hpN : (p : B) ^ N ∈ J := by
    rwa [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hN
  have hdvd : (m : B) ∣ ((p : B) ^ N) ^ m := by
    rw [← delta.factorial_mul_dpow_eq_pow (n := m) hpN]
    exact Dvd.dvd.mul_right
      (Nat.cast_dvd_cast (Nat.dvd_factorial (Nat.pos_of_ne_zero hm0) le_rfl)) _
  have h1 : IsCoprime (m : ℤ) ((p : ℤ) ^ (N * m)) :=
    (Nat.isCoprime_iff_coprime.mpr hm).pow_right
  have h2 : IsCoprime (m : B) ((p : B) ^ (N * m)) := by
    simpa only [map_pow, map_natCast] using h1.map (Int.castRingHom B)
  exact h2.isUnit_of_dvd (by rwa [pow_mul])

/-- An integer outside `(p)` is a unit in a divided power ring in which the prime `p` is nilpotent
modulo the divided power ideal. -/
public theorem isUnit_intCast_of_not_mem_span [Fact p.Prime] (delta : _root_.DividedPowers J)
    (hp : IsNilpotent (Ideal.Quotient.mk J (p : B))) {y : ℤ}
    (hy : y ∉ Ideal.span ({(p : ℤ)} : Set ℤ)) : IsUnit (y : B) := by
  have hm0 : y.natAbs ≠ 0 := fun h ↦ hy (by rw [Int.natAbs_eq_zero.mp h]; exact zero_mem _)
  have hcop : Nat.Coprime y.natAbs p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
    intro hd
    exact hy (Ideal.mem_span_singleton.mpr (Int.natCast_dvd.mpr hd))
  have hu := isUnit_natCast_of_coprime_of_isNilpotent delta hp hm0 hcop
  rcases Int.natAbs_eq y with h | h
  · rwa [h, Int.cast_natCast]
  · rw [h, Int.cast_neg, Int.cast_natCast]
    exact hu.neg

/-- **The `ℤ_(p)`-algebra structure of a divided power ring in which `p` is nilpotent modulo the
divided power ideal**: the extension to the localization `ℤ_(p)` of the ring map from `ℤ`, every
integer prime to `p` being a unit in the ring. -/
@[instance_reducible]
public def algebraIntegersAtPrimeOfIsNilpotent [Fact p.Prime] (delta : _root_.DividedPowers J)
    (hp : IsNilpotent (Ideal.Quotient.mk J (p : B))) : Algebra (IntegersAtPrime p) B :=
  letI : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime :=
    (Ideal.span_singleton_prime (Int.ofNat_ne_zero.mpr (Fact.out : p.Prime).ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp Fact.out)
  (IsLocalization.lift (M := (Ideal.span ({(p : ℤ)} : Set ℤ)).primeCompl)
    (S := IntegersAtPrime p) (g := Int.castRingHom B)
    (fun y ↦ by simpa using isUnit_intCast_of_not_mem_span delta hp y.2)).toAlgebra

end IntegersAtPrime

/-! ### Two equal algebra structures give the same completed forms -/

section AlgebraCongr

variable (p : ℕ) (A : Type u) [CommRing A] {B : Type v} [CommRing B] {J : Ideal B}
  (hJ : _root_.DividedPowers J)

/-- **The completed divided power forms for two equal `A`-algebra structures on `B` are the
same**, as a `B`-linear equivalence. -/
public def completedDividedPowerFormsAlgebraCongr (i : ℕ) (inst inst' : Algebra A B)
    (h : inst = inst') :
    @completedDividedPowerForms p A _ B _ inst J hJ i ≃ₗ[B]
      @completedDividedPowerForms p A _ B _ inst' J hJ i := by
  subst h
  exact LinearEquiv.refl B _

/-- The identification of `Crystalline.completedDividedPowerFormsAlgebraCongr` carries the
universal differential to the universal differential. -/
public theorem completedDividedPowerFormsAlgebraCongr_differentialOnRing (inst inst' : Algebra A B)
    (h : inst = inst') (b : B) :
    completedDividedPowerFormsAlgebraCongr p A hJ 1 inst inst' h
        (@completedDividedPowerDifferentialOnRing p A _ B _ inst J hJ b) =
      @completedDividedPowerDifferentialOnRing p A _ B _ inst' J hJ b := by
  subst h
  rfl

end AlgebraCongr

/-! ### Functoriality of the comparison of completed forms -/

section Functoriality

variable (p : ℕ) (A : Type u) [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
  {J : Ideal B} (hJ : _root_.DividedPowers J)
  {C : Type*} [CommRing C] [Algebra A C] {K : Ideal C} (epsilon : _root_.DividedPowers K)
  (f : B →ₐ[A] C) (hf : IsDPMorphism hJ epsilon f.toRingHom)

/-- **The comparison of completed forms along the identity is the identity**, in every degree. -/
public theorem completedMapDifferentialForms_id (i : ℕ)
    (hid : IsDPMorphism hJ hJ (AlgHom.id A B).toRingHom)
    (x : completedDividedPowerForms p A hJ i) :
    completedMapDifferentialForms p A hJ hJ (AlgHom.id A B) hid i x = x := by
  refine AdicCompletion.ext fun n ↦ ?_
  obtain ⟨omega, homega⟩ := Submodule.Quotient.mk_surjective
    (pAdicIdeal (A := B) p ^ n • ⊤ : Submodule B (dividedPowerDifferentialForms (A := A) hJ i))
    (x.val n)
  rw [completedMapDifferentialForms_val p A hJ hJ _ hid i n x omega homega.symm,
    mapDifferentialFormsOfDPMorphism_id, homega]

/-- **The comparisons of completed forms along two composable divided power morphisms
compose**, in every degree. -/
public theorem completedMapDifferentialForms_comp {D : Type*} [CommRing D] [Algebra A D]
    {L : Ideal D} (zeta : _root_.DividedPowers L) (g : C →ₐ[A] D)
    (hg : IsDPMorphism epsilon zeta g.toRingHom)
    (hgf : IsDPMorphism hJ zeta (g.comp f).toRingHom) (i : ℕ)
    (x : completedDividedPowerForms p A hJ i) :
    completedMapDifferentialForms p A hJ zeta (g.comp f) hgf i x =
      completedMapDifferentialForms p A epsilon zeta g hg i
        (completedMapDifferentialForms p A hJ epsilon f hf i x) := by
  refine AdicCompletion.ext fun n ↦ ?_
  obtain ⟨omega, homega⟩ := Submodule.Quotient.mk_surjective
    (pAdicIdeal (A := B) p ^ n • ⊤ : Submodule B (dividedPowerDifferentialForms (A := A) hJ i))
    (x.val n)
  rw [completedMapDifferentialForms_val p A hJ zeta (g.comp f) hgf i n x omega homega.symm,
    completedMapDifferentialForms_val p A epsilon zeta g hg i n _ _
      (completedMapDifferentialForms_val p A hJ epsilon f hf i n x omega homega.symm),
    mapDifferentialFormsOfDPMorphism_comp]

/-- **The comparison of completed forms carries `d b` to `d (f b)`**, for `b` in the ring `B`
itself. -/
public theorem completedMapDifferentialForms_differentialOnRing (b : B) :
    completedMapDifferentialForms p A hJ epsilon f hf 1
        (completedDividedPowerDifferentialOnRing p A hJ b) =
      completedDividedPowerDifferentialOnRing p A epsilon (f b) :=
  completedMapDifferentialForms_completedFormsDifferential_of p A hJ epsilon f hf b

end Functoriality

/-! ### A finite basis of the differentials gives a basis of the completed one-forms -/

section Generic

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal B)
  (delta : _root_.DividedPowers J) (p : ℕ) [Fact p.Prime]
  (hp : IsNilpotent (Ideal.Quotient.mk J (p : B))) {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- **The comparison of [Stacks, Lemma 60.20.1, Tag 07KK] with no `ℤ_(p)`-structure assumed**:
`Crystalline.dividedPowerDifferentialsCompletionComparisonOfAlgebra` at the `ℤ_(p)`-structure of
`Crystalline.algebraIntegersAtPrimeOfIsNilpotent`. -/
public def dividedPowerDifferentialsCompletionComparisonOfIsNilpotent :
    DifferentialsCompletionComparison (A := A) J delta p hp :=
  letI := algebraIntegersAtPrimeOfIsNilpotent delta hp
  dividedPowerDifferentialsCompletionComparisonOfAlgebra J delta p hp

/-- **The completion of a linear equivalence, read as linear over the base ring**: the
restriction of scalars of `AdicCompletion.congr` to the ring itself. -/
public def adicCompletionCongrBase {S : Type*} [CommRing S] (I : Ideal S)
    {M N : Type*} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N] (f : M ≃ₗ[S] N) :
    AdicCompletion I M ≃ₗ[S] AdicCompletion I N :=
  (AdicCompletion.congr I f).restrictScalars S

/-- The completion of a linear equivalence on the image of the uncompleted module. -/
public theorem adicCompletionCongrBase_of {S : Type*} [CommRing S] (I : Ideal S)
    {M N : Type*} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N] (f : M ≃ₗ[S] N)
    (x : M) :
    adicCompletionCongrBase I f (AdicCompletion.of I M x) = AdicCompletion.of I N (f x) := by
  rw [adicCompletionCongrBase, LinearEquiv.restrictScalars_apply, AdicCompletion.congr_apply,
    AdicCompletion.map_of]
  rfl

/-- **On the completion of a ring, its action on itself as a completed module is its
multiplication.** -/
public theorem adicCompletion_smul_self_eq_mul {R : Type*} [CommRing R] (I : Ideal R)
    (r x : AdicCompletion I R) :
    @HSMul.hSMul _ _ _ (@instHSMul _ _ (AdicCompletion.smul I (M := R))) r x = r * x := by
  refine AdicCompletion.ext fun n ↦ ?_
  rw [AdicCompletion.smul_eval, AdicCompletion.val_mul]
  generalize r.val n = a
  generalize x.val n = c
  induction a using Quotient.inductionOn' with | _ a
  induction c using Quotient.inductionOn' with | _ c
  rfl

/-- **The completion of `R^ι` is `(R^∧)^ι`**, for a finite `ι`, with the product carrying its
standard module structure over `R^∧`. -/
public def adicCompletionPiSelfEquiv {R : Type*} [CommRing R] (I : Ideal R) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :
    AdicCompletion I (ι → R) ≃ₗ[AdicCompletion I R] (ι → AdicCompletion I R) :=
  { (AdicCompletion.piEquivOfFintype I (fun _ : ι ↦ R)).toAddEquiv with
    map_smul' := fun r x ↦ by
      funext j
      rw [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, ← adicCompletion_smul_self_eq_mul]
      exact congrFun ((AdicCompletion.piEquivOfFintype I (fun _ : ι ↦ R)).map_smul r x) j }

/-- The identification `(R^ι)^∧ ≃ (R^∧)^ι` on the image of `R^ι`. -/
public theorem adicCompletionPiSelfEquiv_of {R : Type*} [CommRing R] (I : Ideal R) (ι : Type*)
    [Fintype ι] [DecidableEq ι] (v : ι → R) :
    adicCompletionPiSelfEquiv I ι (AdicCompletion.of I _ v) =
      fun j ↦ AdicCompletion.of I R (v j) := by
  funext j
  change AdicCompletion.piEquivOfFintype I (fun _ : ι ↦ R) (AdicCompletion.of I _ v) j = _
  simp only [AdicCompletion.piEquivOfFintype_apply, AdicCompletion.pi, LinearMap.pi_apply,
    AdicCompletion.map_of, LinearMap.proj_apply]

/-- The completion `Ω̂_{B/A,δ}` of the differentials is `B̂^ι` for a basis of `Ω_{B/A,δ}` indexed
by the finite type `ι`. -/
public def completionDifferentialsEquivPi
    (b : Module.Basis ι B (dividedPowerDifferentials (A := A) delta)) :
    AdicCompletion (pAdicIdeal (A := B) p) (dividedPowerDifferentials (A := A) delta) ≃ₗ[
        AdicCompletion (pAdicIdeal (A := B) p) B]
      (ι → AdicCompletion (pAdicIdeal (A := B) p) B) :=
  (AdicCompletion.congr (pAdicIdeal (A := B) p) b.equivFun).trans
    (adicCompletionPiSelfEquiv (pAdicIdeal (A := B) p) ι)

omit [Fact p.Prime] in
/-- The identification `Ω̂_{B/A,δ} ≃ B̂^ι` sends the image of a basis vector to the corresponding
standard basis vector. -/
public theorem completionDifferentialsEquivPi_of_basis
    (b : Module.Basis ι B (dividedPowerDifferentials (A := A) delta)) (i : ι) :
    completionDifferentialsEquivPi J delta p b
        (AdicCompletion.of (pAdicIdeal (A := B) p) _ (b i)) = Pi.single i 1 := by
  rw [completionDifferentialsEquivPi, LinearEquiv.trans_apply, AdicCompletion.congr_apply,
    AdicCompletion.map_of, adicCompletionPiSelfEquiv_of]
  funext j
  rw [LinearEquiv.coe_coe, Module.Basis.equivFun_self]
  rcases eq_or_ne j i with rfl | hji
  · rw [ite_eq_left rfl, Pi.single_eq_same]
    exact (AdicCompletion.algebraMap_apply _ (1 : B)).symm.trans (map_one _)
  · rw [ite_eq_right hji.symm, Pi.single_eq_of_ne hji, map_zero]

/-- **A `B̂`-linear isomorphism of the completions of `Ω_{B̂/A,γ̂}` and of `Ω̂_{B/A,δ}`**, whose
value at every level beyond the cutoff of [Stacks, Lemma 60.20.1, Tag 07KK] is the level
identification `Crystalline.completedDifferentialsLevelLinearEquiv`. -/
public def completedDifferentialsCompletionEquivSpec :=
  let cmp := dividedPowerDifferentialsCompletionComparisonOfIsNilpotent (A := A) J delta p hp
  adicCompletionLinearEquivOfQuotEquiv
    (pAdicIdeal (A := AdicCompletion (pAdicIdeal (A := B) p) B) p) cmp.quotientSystem.cutoff
    (fun e ↦ completedDifferentialsLevelLinearEquiv (A := A) J delta p hp cmp e)
    (fun h x ↦ LinearMap.congr_fun
      (completedDifferentialsLevelEquiv_transition (A := A) J delta p hp cmp h) x)

/-- **The completions of `Ω_{B̂/A,γ̂}` and of `Ω̂_{B/A,δ}` are isomorphic**, `B̂`-linearly: the
equivalence of `Crystalline.completedDifferentialsCompletionEquivSpec`. -/
public def completedDifferentialsCompletionEquiv :
    AdicCompletion (pAdicIdeal (A := AdicCompletion (pAdicIdeal (A := B) p) B) p)
        (dividedPowerDifferentials (A := A) (completedDividedPowers J delta p hp).1) ≃ₗ[
        AdicCompletion (pAdicIdeal (A := B) p) B]
      AdicCompletion (pAdicIdeal (A := AdicCompletion (pAdicIdeal (A := B) p) B) p)
        (AdicCompletion (pAdicIdeal (A := B) p) (dividedPowerDifferentials (A := A) delta)) :=
  (completedDifferentialsCompletionEquivSpec J delta p hp).1

/-- The comparison of the completions carries the image of `d b`, for `b` in the uncompleted
`B`, to the image of `d b`. -/
public theorem completedDifferentialsCompletionEquiv_of (x : B) :
    completedDifferentialsCompletionEquiv J delta p hp
        (AdicCompletion.of _ _ (dividedPowerDifferential (A := A)
          (completedDividedPowers J delta p hp).1
          (AdicCompletion.of (pAdicIdeal (A := B) p) B x))) =
      AdicCompletion.of _ _ (AdicCompletion.of (pAdicIdeal (A := B) p) _
        (dividedPowerDifferential (A := A) delta x)) := by
  refine adicCompletion_ext_of_eval_shift _
    (dividedPowerDifferentialsCompletionComparisonOfIsNilpotent (A := A) J delta p
      hp).quotientSystem.cutoff fun e ↦ ?_
  refine ((completedDifferentialsCompletionEquivSpec J delta p hp).2 e _).trans ?_
  rw [AdicCompletion.eval_of, AdicCompletion.eval_of, Submodule.mkQ_apply, Submodule.mkQ_apply]
  exact completedDifferentialsLevelEquiv_d (A := A) J delta p hp _ e x

/-- **The completed one-forms `Ω̂¹_{B̂/A,γ̂}` are `B̂^ι`**, for a finite basis of `Ω_{B/A,δ}`
indexed by `ι`. -/
public def completedDividedPowerFormsEquivPi
    (b : Module.Basis ι B (dividedPowerDifferentials (A := A) delta)) :
    completedDividedPowerForms p A (completedDividedPowers J delta p hp).1 1 ≃ₗ[
        AdicCompletion (pAdicIdeal (A := B) p) B]
      (ι → AdicCompletion (pAdicIdeal (A := B) p) B) :=
  letI : IsAdicComplete (pAdicIdeal (A := AdicCompletion (pAdicIdeal (A := B) p) B) p)
      (ι → AdicCompletion (pAdicIdeal (A := B) p) B) :=
    isAdicComplete_pi _ (fun _ : ι ↦ AdicCompletion (pAdicIdeal (A := B) p) B)
      fun _ ↦ inferInstance
  (adicCompletionCongrBase _ (exteriorPower.oneEquiv _ _)).trans
    ((completedDifferentialsCompletionEquiv J delta p hp).trans
      ((adicCompletionCongrBase _ (completionDifferentialsEquivPi J delta p b)).trans
        (AdicCompletion.ofLinearEquiv _ _).symm))

/-- **The basis of the completed one-forms of the completion**, for a divided power ring whose
divided power differentials have a finite basis. -/
public def completedDividedPowerFormsBasisOfBasis
    (b : Module.Basis ι B (dividedPowerDifferentials (A := A) delta)) :
    Module.Basis ι (AdicCompletion (pAdicIdeal (A := B) p) B)
      (completedDividedPowerForms p A (completedDividedPowers J delta p hp).1 1) :=
  .ofEquivFun (completedDividedPowerFormsEquivPi J delta p hp b)

/-- **The identification `Ω̂¹_{B̂/A,γ̂} ≃ B̂^ι` sends `d (y i)` to the `i`-th standard basis
vector**, when the basis vector `b i` of `Ω_{B/A,δ}` is `d (y i)`. -/
public theorem completedDividedPowerFormsEquivPi_differential
    (b : Module.Basis ι B (dividedPowerDifferentials (A := A) delta)) (y : ι → B)
    (hy : ∀ i, b i = dividedPowerDifferential (A := A) delta (y i)) (i : ι) :
    completedDividedPowerFormsEquivPi J delta p hp b
        (completedDividedPowerDifferentialOnRing p A (completedDividedPowers J delta p hp).1
          (AdicCompletion.of (pAdicIdeal (A := B) p) B (y i))) = Pi.single i 1 := by
  rw [completedDividedPowerDifferentialOnRing_eq, dividedPowerOneForm_apply,
    completedDividedPowerFormsEquivPi, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply]
  simp only [adicCompletionCongrBase_of, LinearEquiv.apply_symm_apply,
    completedDifferentialsCompletionEquiv_of, ← hy, completionDifferentialsEquivPi_of_basis,
    AdicCompletion.ofLinearEquiv_symm_of]

/-- **The basis vectors of `Crystalline.completedDividedPowerFormsBasisOfBasis` are the
differentials of the completed ring**: if the basis vector `b i` of `Ω_{B/A,δ}` is `d (y i)`,
the basis vector of index `i` of the completed one-forms is `d (y i)` read in the completion. -/
public theorem completedDividedPowerFormsBasisOfBasis_apply
    (b : Module.Basis ι B (dividedPowerDifferentials (A := A) delta)) (y : ι → B)
    (hy : ∀ i, b i = dividedPowerDifferential (A := A) delta (y i)) (i : ι) :
    completedDividedPowerFormsBasisOfBasis J delta p hp b i =
      completedDividedPowerDifferentialOnRing p A (completedDividedPowers J delta p hp).1
        (AdicCompletion.of (pAdicIdeal (A := B) p) B (y i)) := by
  rw [completedDividedPowerFormsBasisOfBasis, Module.Basis.coe_ofEquivFun,
    LinearEquiv.symm_apply_eq, completedDividedPowerFormsEquivPi_differential J delta p hp b y hy]

end Generic

/-! ### The completed envelope of a polynomial presentation -/

section Envelope

variable {A : DividedPowerRing.{u}} {ι : Type u} [Fintype ι] [DecidableEq ι]
  {J : Ideal (MvPolynomial ι A)} {hJ : A.ideal.map (algebraMap A (MvPolynomial ι A)) ≤ J}
  (E : DividedPowerEnvelope A (algebraMap A (MvPolynomial ι A)) J hJ)

/-- The base change to the envelope of the basis `d x_i` of the Kähler differentials of the
polynomial algebra. -/
public def envelopeKaehlerBasis :
    letI : Algebra (MvPolynomial ι A) E.object := E.algebraMap.toRingHom.toAlgebra
    { c : Module.Basis ι E.object (TensorProduct (MvPolynomial ι A) E.object
        (KaehlerDifferential (A : Type u) (MvPolynomial ι A))) //
      ∀ i, c i = (1 : E.object) ⊗ₜ[MvPolynomial ι A]
        KaehlerDifferential.D (A : Type u) (MvPolynomial ι A) (MvPolynomial.X i) } :=
  letI : Algebra (MvPolynomial ι A) E.object := E.algebraMap.toRingHom.toAlgebra
  ⟨(KaehlerDifferential.mvPolynomialBasis (A : Type u) ι).baseChange E.object, fun i ↦ by
    rw [Module.Basis.baseChange_apply, KaehlerDifferential.mvPolynomialBasis_apply]⟩

/-- A basis of `E ⊗_P Ω_{P/A}` of the shape of `Crystalline.envelopeKaehlerBasis`, carried across
an equality of `A`-algebra structures on `P`. -/
public def envelopeKaehlerBasisCongr (inst inst' : Algebra (A : Type u) (MvPolynomial ι A))
    (h : inst = inst')
    (c : letI := inst
      letI : Algebra (MvPolynomial ι A) E.object := E.algebraMap.toRingHom.toAlgebra
      { c : Module.Basis ι E.object (TensorProduct (MvPolynomial ι A) E.object
          (KaehlerDifferential (A : Type u) (MvPolynomial ι A))) //
        ∀ i, c i = (1 : E.object) ⊗ₜ[MvPolynomial ι A]
          KaehlerDifferential.D (A : Type u) (MvPolynomial ι A) (MvPolynomial.X i) }) :
    letI := inst'
    letI : Algebra (MvPolynomial ι A) E.object := E.algebraMap.toRingHom.toAlgebra
    { c : Module.Basis ι E.object (TensorProduct (MvPolynomial ι A) E.object
        (KaehlerDifferential (A : Type u) (MvPolynomial ι A))) //
      ∀ i, c i = (1 : E.object) ⊗ₜ[MvPolynomial ι A]
        KaehlerDifferential.D (A : Type u) (MvPolynomial ι A) (MvPolynomial.X i) } := by
  subst h
  exact c

/-- **The divided power differentials `Ω_{E/A,δ}` of the envelope are free on the `d y_i`**, `y_i`
the image of the variable `x_i`. -/
public def envelopeDifferentialsBasis :
    letI : Algebra (A : Type u) E.object := E.structureMap.toRingHom.toAlgebra
    Module.Basis ι E.object (dividedPowerDifferentials (A := (A : Type u))
      E.object.dividedPowers) :=
  letI : Algebra (A : Type u) E.object := E.structureMap.toRingHom.toAlgebra
  (envelopeKaehlerBasisCongr E inferInstance (algebraMap (A : Type u) (MvPolynomial ι A)).toAlgebra
      (Algebra.algebra_ext _ _ fun _ ↦ rfl) (envelopeKaehlerBasis E)).1.map
    (dividedPowerEnvelopeDifferentialsEquiv A (algebraMap A (MvPolynomial ι A)) J hJ E).1.symm

omit [Fintype ι] [DecidableEq ι] in
/-- The basis vector of index `i` of `Crystalline.envelopeDifferentialsBasis` is `d y_i`. -/
public theorem envelopeDifferentialsBasis_apply (i : ι) :
    letI : Algebra (A : Type u) E.object := E.structureMap.toRingHom.toAlgebra
    envelopeDifferentialsBasis E i =
      dividedPowerDifferential (A := (A : Type u)) E.object.dividedPowers
        (E.algebraMap.toRingHom (MvPolynomial.X i)) := by
  let : Algebra (A : Type u) E.object := E.structureMap.toRingHom.toAlgebra
  rw [envelopeDifferentialsBasis, Module.Basis.map_apply, LinearEquiv.symm_apply_eq,
    (dividedPowerEnvelopeDifferentialsEquiv A (algebraMap A (MvPolynomial ι A)) J hJ E).2]
  exact (envelopeKaehlerBasisCongr E inferInstance
    (algebraMap (A : Type u) (MvPolynomial ι A)).toAlgebra (Algebra.algebra_ext _ _ fun _ ↦ rfl)
    (envelopeKaehlerBasis E)).2 i

variable (p : ℕ) [Fact p.Prime] (hp : IsNilpotent (Ideal.Quotient.mk E.object.ideal (p : E.object)))

/-- **`Ω̂¹_D ≃ D^ι`**: `Crystalline.completedDividedPowerFormsEquivPi` at the basis
`Crystalline.envelopeDifferentialsBasis` of `Ω_{E/A,δ}`, read for the `A`-algebra structure
`Crystalline.algebraBaseEnvelopeCompletion` of `D`. -/
public def envelopeCompletionFormsEquivPi :
    envelopeCompletionForms E p hp 1 ≃ₗ[envelopeCompletion E p hp]
      (ι → envelopeCompletion E p hp) :=
  letI : Algebra (A : Type u) E.object := E.structureMap.toRingHom.toAlgebra
  ((completedDividedPowerFormsAlgebraCongr p (A : Type u)
      (B := AdicCompletion (pAdicIdeal (A := (E.object : Type u)) p) E.object)
      (completedDividedPowers E.object.ideal E.object.dividedPowers p hp).1 1 inferInstance
      (algebraBaseEnvelopeCompletion E p hp) (Algebra.algebra_ext _ _ fun _ ↦ rfl)).symm.trans
    (completedDividedPowerFormsEquivPi E.object.ideal E.object.dividedPowers p hp
      (envelopeDifferentialsBasis E)) :
    _ ≃ₗ[AdicCompletion (pAdicIdeal (A := (E.object : Type u)) p) E.object] _)

/-- **The completed one-forms of the completed envelope are free on the `d x_i`.**

`Ω̂¹_D`, the `p`-adic completion of the degree-one divided power forms of the ring
`D = Crystalline.envelopeCompletion E p hp` itself, has a basis over `D` indexed by the
variables, whose vectors are the differentials of the coordinates. -/
public def envelopeCompletionFormsBasis :
    Module.Basis ι (envelopeCompletion E p hp) (envelopeCompletionForms E p hp 1) :=
  .ofEquivFun (envelopeCompletionFormsEquivPi E p hp)

/-- **The basis vector of index `i` of `Ω̂¹_D` is `d x_i`**, the universal differential of the
coordinate `x_i` of `D`. -/
public theorem envelopeCompletionFormsBasis_apply (i : ι) :
    envelopeCompletionFormsBasis E p hp i =
      envelopeCompletionFormsDifferential E p hp (envelopeCompletionCoord E p hp i) := by
  rw [envelopeCompletionFormsBasis, Module.Basis.coe_ofEquivFun, LinearEquiv.symm_apply_eq]
  symm
  let : Algebra (A : Type u) E.object := E.structureMap.toRingHom.toAlgebra
  have h1 := completedDividedPowerFormsAlgebraCongr_differentialOnRing p (A : Type u)
    (B := AdicCompletion (pAdicIdeal (A := (E.object : Type u)) p) E.object)
    (completedDividedPowers E.object.ideal E.object.dividedPowers p hp).1 inferInstance
    (algebraBaseEnvelopeCompletion E p hp) (Algebra.algebra_ext _ _ fun _ ↦ rfl)
    (AdicCompletion.of (pAdicIdeal (A := (E.object : Type u)) p) _
      (E.algebraMap.toRingHom (MvPolynomial.X i)))
  have h2 := completedDividedPowerFormsEquivPi_differential E.object.ideal E.object.dividedPowers
    p hp (envelopeDifferentialsBasis E) (fun i ↦ E.algebraMap.toRingHom (MvPolynomial.X i))
    (envelopeDifferentialsBasis_apply E) i
  exact (congrArg _ ((LinearEquiv.symm_apply_eq _).mpr h1.symm)).trans h2

end Envelope

end Crystalline

end
