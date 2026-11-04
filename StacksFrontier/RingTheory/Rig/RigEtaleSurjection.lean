module

public import StacksFrontier.RingTheory.Rig.NaiveCotangent.BaseChangeKer
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.SmulIdModule
public import StacksFrontier.RingTheory.Rig.PresentationGenerators
public import StacksFrontier.RingTheory.Rig.RigSmooth
public import StacksFrontier.RingTheory.Restricted.RigEtale
public import StacksFrontier.RingTheory.Restricted.RigSmoothCriteria

/-!
# Rig-smoothness and rig-étaleness of an adic quotient

Let `A` be a Noetherian ring which is `I`-adically complete for an ideal `I`, and let `B` be an
object of the category of Stacks 0AL4 over `(A, I)` for which the structure map `A → B` is
*surjective*, say with kernel `J`.  Then `B = A / J` is presented by the completed polynomial
algebra in **zero** variables, so its completed naive cotangent complex is the conormal module
`J / J²` placed in degree `-1` with nothing in degree `0`.  Consequently both rigidity
conditions over `(A, I)` collapse to a single statement about `J`:

`B` is rig-smooth over `(A, I)` ⟺ `B` is rig-étale over `(A, I)` ⟺ `Iᶜ · J ⊆ J²` for some `c`.

This is the algebraic content of Stacks 0GD4, which deduces from it that a closed immersion of
locally Noetherian formal algebraic spaces is rig-smooth exactly when it is rig-étale.

## Main definitions

* `Rig.zeroVariableEquiv` — the identification of an `I`-adically complete ring with the
  `I`-adic completion of the polynomial algebra in zero variables over it.
* `Rig.quotientPresentation` — the presentation of a surjective quotient by zero variables,
  and `Rig.quotientPresentationEquiv` the identification of its presenting ring with `A`.

## Main results

* `Rig.isRigSmooth_iff_exists_pow_mul_ker_le_sq` and
  `Rig.isRigEtale_iff_exists_pow_mul_ker_le_sq` — each rigidity condition is the annihilation
  of the conormal module `J / J²` by a power of `I`.
* `Rig.isRigSmooth_iff_isRigEtale_of_surjective` — the two conditions agree for a quotient.

## References

* [Stacks Project, Tag 0GAJ](https://stacks.math.columbia.edu/tag/0GAJ)
* [Stacks Project, Tag 0GAY](https://stacks.math.columbia.edu/tag/0GAY)
* [Stacks Project, Tag 0GB1](https://stacks.math.columbia.edu/tag/0GB1)
* [Stacks Project, Tag 0GD4](https://stacks.math.columbia.edu/tag/0GD4)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Rig

universe u v

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {I : Ideal A}

section Equiv

variable (I)

/-- The polynomial algebra in zero variables over an `I`-adically complete ring is adically
complete for the extension of `I`. -/
public theorem isAdicComplete_mvPolynomial_isEmpty [IsAdicComplete I A] :
    IsAdicComplete (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin 0) A))
      (MvPolynomial (Fin 0) A) :=
  (IsAdicComplete.congr_ringEquiv I
    ((MvPolynomial.isEmptyAlgEquiv A (Fin 0)).symm.toRingEquiv :
      A ≃+* MvPolynomial (Fin 0) A)).mpr ‹IsAdicComplete I A›

/-- The identification of an `I`-adically complete ring with the completed polynomial algebra
in zero variables over it. -/
public def zeroVariableEquiv [IsAdicComplete I A] : A ≃+* completedPolynomialAlgebra I 0 :=
  let := isAdicComplete_mvPolynomial_isEmpty I
  ((MvPolynomial.isEmptyAlgEquiv A (Fin 0)).symm.toRingEquiv).trans
    (AdicCompletion.ofAlgEquiv
      (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin 0) A))).toRingEquiv

/-- `Rig.zeroVariableEquiv` is the structure map of the completed polynomial algebra. -/
public theorem zeroVariableEquiv_apply [IsAdicComplete I A] (a : A) :
    zeroVariableEquiv I a = algebraMap A (completedPolynomialAlgebra I 0) a := rfl

end Equiv

section Presentation

variable [IsNoetherianRing A] (B : AdicFiniteTypeAlgebra.{u, v} A I)

omit [IsNoetherianRing A] in
/-- The empty family generates the reduction of a surjective quotient. -/
public theorem surjective_aeval_isEmpty
    (hsurj : Function.Surjective (algebraMap A B.carrier)) :
    Function.Surjective (MvPolynomial.aeval
      (fun i : Fin 0 ↦ Ideal.Quotient.mk B.adicIdeal ((Fin.elim0 i : B.carrier))) :
        MvPolynomial (Fin 0) (A ⧸ I) →ₐ[A ⧸ I] B.reduction) := by
  intro x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, rfl⟩ := hsurj b
  exact ⟨MvPolynomial.C (Ideal.Quotient.mk I a), by rw [MvPolynomial.aeval_C]; rfl⟩

/-- The presentation of a surjective quotient by zero variables. -/
public def quotientPresentation (hsurj : Function.Surjective (algebraMap A B.carrier)) :
    CompletedPolynomialPresentation I B :=
  CompletedPolynomialPresentation.ofGenerators B 0 Fin.elim0
    (Ideal.fg_of_isNoetherianRing I) (surjective_aeval_isEmpty B hsurj)

/-- `Rig.quotientPresentation` has zero variables. -/
@[simp] public theorem quotientPresentation_variableCount
    (hsurj : Function.Surjective (algebraMap A B.carrier)) :
    (quotientPresentation B hsurj).variableCount = 0 := rfl

variable [IsAdicComplete I A] (hsurj : Function.Surjective (algebraMap A B.carrier))

/-- `Rig.zeroVariableEquiv`, read as an identification of `A` with the ring presenting a
surjective quotient. -/
public def quotientPresentationEquiv :
    A ≃+* (quotientPresentation B hsurj).extension.Ring :=
  zeroVariableEquiv I

/-- The identification `Rig.quotientPresentationEquiv` is compatible with the structure maps
to `B`. -/
public theorem algebraMap_quotientPresentationEquiv (a : A) :
    algebraMap (quotientPresentation B hsurj).extension.Ring B.carrier
        (quotientPresentationEquiv B hsurj a) = algebraMap A B.carrier a :=
  (quotientPresentation B hsurj).toAlgHom.commutes a

/-- The kernel of `Rig.quotientPresentation` is the kernel `J` of `A → B`, transported along
`Rig.quotientPresentationEquiv`. -/
public theorem ker_quotientPresentation :
    (quotientPresentation B hsurj).extension.ker =
      (RingHom.ker (algebraMap A B.carrier)).map (quotientPresentationEquiv B hsurj) := by
  ext x
  have h2 : x ∈ (RingHom.ker (algebraMap A B.carrier)).map
      (quotientPresentationEquiv B hsurj) ↔
      algebraMap A B.carrier ((quotientPresentationEquiv B hsurj).symm x) = 0 := by
    rw [← Ideal.symm_apply_mem_of_equiv_iff]
    exact RingHom.mem_ker
  rw [h2, ← algebraMap_quotientPresentationEquiv B hsurj
    ((quotientPresentationEquiv B hsurj).symm x), RingEquiv.apply_symm_apply]
  exact RingHom.mem_ker.symm

end Presentation

section Collapse

variable [IsNoetherianRing A] [IsAdicComplete I A] (B : AdicFiniteTypeAlgebra.{u, v} A I)
  (hsurj : Function.Surjective (algebraMap A B.carrier))

/-- A scalar of the presenting ring acts on the conormal module through its image in the
presented algebra. -/
public alias cotangent_ring_smul := extension_cotangent_ring_smul_eq_algebraMap

/-- Annihilation of the conormal module of `Rig.quotientPresentation` by a scalar of `A` is
the inclusion `a · J ⊆ J²`. -/
public theorem smul_cotangent_quotientPresentation_eq_zero_iff (a : A) :
    (∀ x : (quotientPresentation B hsurj).extension.Cotangent,
        (algebraMap A B.carrier a) • x = 0) ↔
      ∀ y ∈ RingHom.ker (algebraMap A B.carrier),
        a * y ∈ RingHom.ker (algebraMap A B.carrier) ^ 2 := by
  set E := (quotientPresentation B hsurj).extension
  set e := quotientPresentationEquiv B hsurj
  set J : Ideal A := RingHom.ker (algebraMap A B.carrier)
  have hkerP : E.ker = J.map e := ker_quotientPresentation B hsurj
  have hsmul : ∀ x : E.Cotangent, (algebraMap A B.carrier a) • x = (e a) • x := fun x ↦ by
    rw [cotangent_ring_smul E (e a) x,
      show algebraMap E.Ring B.carrier (e a) = algebraMap A B.carrier a from
        algebraMap_quotientPresentationEquiv B hsurj a]
  have hpow : (J ^ 2).map e = E.ker ^ 2 := by rw [hkerP, Ideal.map_pow]
  refine ⟨fun h y hy ↦ ?_, fun h x ↦ ?_⟩
  · have hyP : e y ∈ E.ker := hkerP ▸ Ideal.mem_map_of_mem _ hy
    have hzero : Algebra.Extension.Cotangent.mk (P := E) ((e a) • (⟨e y, hyP⟩ : E.ker)) = 0 := by
      rw [map_smul, ← hsmul]
      exact h _
    have hmem : (((e a) • (⟨e y, hyP⟩ : E.ker) : E.ker) : E.Ring) ∈ E.ker ^ 2 :=
      (Algebra.Extension.Cotangent.mk_eq_zero_iff (P := E) _).mp hzero
    have hval : (((e a) • (⟨e y, hyP⟩ : E.ker) : E.ker) : E.Ring) = e (a * y) := by
      simp [map_mul]
    rwa [hval, ← hpow, Ideal.apply_mem_of_equiv_iff] at hmem
  · obtain ⟨y, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective (P := E) x
    rw [hsmul, ← map_smul]
    refine (Algebra.Extension.Cotangent.mk_eq_zero_iff (P := E) _).mpr ?_
    have hyJ : e.symm (y : E.Ring) ∈ J :=
      Ideal.symm_apply_mem_of_equiv_iff.mpr (hkerP ▸ y.2)
    have hval : (((e a) • y : E.ker) : E.Ring) = e (a * e.symm (y : E.Ring)) := by
      simp [map_mul]
    rw [hval, ← hpow]
    exact Ideal.mem_map_of_mem _ (h _ hyJ)

omit [IsAdicComplete I A] in
/-- With zero variables the degree-zero term of the complex is trivial. -/
private theorem eq_zero_of_variableCount
    (w : Fin (quotientPresentation B hsurj).variableCount → B.carrier) : w = 0 :=
  funext fun i ↦ i.elim0

include hsurj in
/-- **Stacks 0GD4**, the algebraic half, for rig-smoothness.  A surjective quotient `B = A / J`
is rig-smooth over `(A, I)` exactly when some power of `I` carries `J` into `J²`. -/
public theorem isRigSmooth_iff_exists_pow_mul_ker_le_sq :
    IsRigSmooth B ↔ ∃ c : ℕ, ∀ a ∈ I ^ c, ∀ y ∈ RingHom.ker (algebraMap A B.carrier),
      a * y ∈ RingHom.ker (algebraMap A B.carrier) ^ 2 := by
  rw [isRigSmooth_iff_cotangentFactorization B (quotientPresentation B hsurj)]
  refine ⟨fun ⟨c, hc⟩ ↦ ⟨c, fun a ha ↦ ?_⟩, fun ⟨c, hc⟩ ↦ ⟨c, fun a ha ↦ ⟨0, ?_⟩⟩⟩
  · rw [← smul_cotangent_quotientPresentation_eq_zero_iff B hsurj a]
    obtain ⟨h, hh⟩ := hc a ha
    intro x
    have hx := LinearMap.congr_fun hh x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
      LinearMap.id_coe, id_eq] at hx
    rw [eq_zero_of_variableCount B hsurj
      ((completedNaiveCotangentComplex B (quotientPresentation B hsurj)).differential x),
      map_zero] at hx
    exact hx.symm
  · have hann := (smul_cotangent_quotientPresentation_eq_zero_iff B hsurj a).mpr (hc a ha)
    refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply,
      LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    exact (hann x).symm

include hsurj in
/-- **Stacks 0GD4**, the algebraic half, for rig-étaleness.  A surjective quotient `B = A / J`
is rig-étale over `(A, I)` exactly when some power of `I` carries `J` into `J²`. -/
public theorem isRigEtale_iff_exists_pow_mul_ker_le_sq :
    IsRigEtale B ↔ ∃ c : ℕ, ∀ a ∈ I ^ c, ∀ y ∈ RingHom.ker (algebraMap A B.carrier),
      a * y ∈ RingHom.ker (algebraMap A B.carrier) ^ 2 := by
  refine ⟨fun h ↦ (isRigSmooth_iff_exists_pow_mul_ker_le_sq B hsurj).mp
    (isRigSmooth_of_isRigEtale B h), fun ⟨c, hc⟩ ↦ ?_⟩
  rw [isRigEtale_iff B (quotientPresentation B hsurj)]
  refine ⟨c, fun a ha ↦ ?_⟩
  have hann := (smul_cotangent_quotientPresentation_eq_zero_iff B hsurj a).mpr (hc a ha)
  exact smul_id_eq_zero_of_differential_section B (quotientPresentation B hsurj)
    (algebraMap A B.carrier a) 0
    (fun y ↦ by rw [LinearMap.zero_apply, hann y])
    fun _ ↦ (eq_zero_of_variableCount B hsurj _).trans (eq_zero_of_variableCount B hsurj _).symm

include hsurj in
/-- **Stacks 0GD4**, the algebraic half.  A surjective quotient is rig-smooth over `(A, I)`
exactly when it is rig-étale over `(A, I)`. -/
public theorem isRigSmooth_iff_isRigEtale_of_surjective :
    IsRigSmooth B ↔ IsRigEtale B :=
  (isRigSmooth_iff_exists_pow_mul_ker_le_sq B hsurj).trans
    (isRigEtale_iff_exists_pow_mul_ker_le_sq B hsurj).symm

end Collapse

section Over

/-- Rig-étaleness of the algebra attached to a homomorphism and an ideal of definition is
rig-étaleness over that ideal in the sense of `Rig.IsRigEtaleOver`. -/
public theorem isRigEtaleOver_of_isRigEtale_adicFiniteTypeAlgebra
    {A : Type u} {C : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [IsNoetherianRing A]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (φ : A →+* C) (hft : FiniteTypeAdicAlgebraForEveryIdeal φ) (I : Ideal A)
    (hI : TopologicalRing.IsIdealOfDefinition I)
    (h : IsRigEtale (adicFiniteTypeAlgebra φ hft I hI)) : IsRigEtaleOver φ I := by
  have p := isAdicFiniteType_of_finiteTypeAdicAlgebraForEveryIdeal φ hft I hI
  let _ : Algebra A C := φ.toAlgebra
  refine ⟨p.1, p.2, ?_⟩
  have _ : Algebra.FiniteType (A ⧸ I) (C ⧸ I.map (algebraMap A C)) := p.2
  have heq : adicFiniteTypeAlgebra φ hft I hI = AdicFiniteTypeAlgebra.of (I := I) C p.1 :=
    ObjectProperty.FullSubcategory.ext rfl
  exact heq ▸ h

end Over

end Rig

end
