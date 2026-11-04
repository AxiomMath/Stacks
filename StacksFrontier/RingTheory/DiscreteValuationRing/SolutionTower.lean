module

public import Mathlib
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar
public import StacksFrontier.RingTheory.DiscreteValuationRing.BaseChangeClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.IntegralClosureBaseChangeConstruction
public import StacksFrontier.RingTheory.DiscreteValuationRing.ReducedTensorTower
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
public import StacksFrontier.RingTheory.FormallySmooth.Topological

/-!
# Solutions persist under finite field extensions

Let `A → B` be an extension of discrete valuation rings with fraction fields `K ⊆ L`. If a
finite extension `K₁ / K` is a solution for `A → B`, then every finite extension `K₂ / K₁`,
regarded as an extension of `K`, is again a solution for `A → B`.

## Main results

* `IsDiscreteValuationRing.exists_isSolution_of_tower`: solutions persist under finite
  extensions.

## Implementation notes

The reduced composita and integral closures associated to the two finite extensions are
represented by `IsDiscreteValuationRing.IntegralClosureBaseChange`, and the algebra and
scalar-tower instances record the compatibility of the field inclusions. The input carriers
have independent universes; the integral closures use the universes of the extension field and
its reduced compositum, and each solution is tested in the maximum of its two
localization-carrier universes, as in the formal-smoothness criterion of Tag 09E7.

The auxiliary `ReducedTensorTower` namespace collects the canonical functoriality maps for
reductions of tensor products that are needed to compare the two reduced composita. No
assertion is made that reduction commutes with a further tensor product: that assertion is
false without additional hypotheses in the inseparable, nonexcellent case.

## References

* [The Stacks Project, Tag 0GLR](https://stacks.math.columbia.edu/tag/0GLR)
-/

@[expose] public section

namespace IsDiscreteValuationRing

universe uA uB uK uL uK₁ uK₂ uR uC uS uR' uS' uT uX

open scoped TensorProduct

namespace ReducedTensorTower

end ReducedTensorTower

open ReducedTensorTower in
private theorem reductionMap_bijective_of_surjective_of_ker_le
    {R : Type uR} {A : Type uA} {B : Type uB}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (hf : Function.Surjective f)
    (hker : RingHom.ker f ≤ nilradical A) :
    Function.Bijective (reductionMap f) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [reductionMap_mk, Ideal.Quotient.eq_zero_iff_mem, mem_nilradical] at hx
    obtain ⟨n, hn⟩ := hx
    have : x ^ n ∈ RingHom.ker f := by simpa [RingHom.mem_ker] using hn
    obtain ⟨m, hm⟩ := mem_nilradical.mp (hker this)
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_nilradical]
    exact ⟨n * m, by rw [pow_mul, hm]⟩
  · intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩

open ReducedTensorTower in
private theorem ker_rTensor_mk_nilradical_le
    {R : Type uR} {A : Type uA} {C : Type uC}
    [CommRing R] [CommRing A] [CommRing C] [Algebra R A] [Algebra R C] :
    RingHom.ker (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (nilradical A))
      (AlgHom.id R C)) ≤ nilradical (A ⊗[R] C) := by
  rw [Algebra.TensorProduct.rTensor_ker _ (Ideal.Quotient.mkₐ_surjective R _),
    Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, mem_nilradical]
  rw [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
  exact (mem_nilradical.mp hx).map _

open ReducedTensorTower in
/-- Reducing before or after a base change gives the same reduced ring. -/
private noncomputable def reductionTensorReductionEquiv
    (R : Type uR) (A : Type uA) (C : Type uC)
    [CommRing R] [CommRing A] [CommRing C] [Algebra R A] [Algebra R C] :
    Reduction (A ⊗[R] C) ≃ₐ[R] Reduction (Reduction A ⊗[R] C) :=
  AlgEquiv.ofBijective (reducedTensorMap (Ideal.Quotient.mkₐ R (nilradical A)) (AlgHom.id R C))
    (reductionMap_bijective_of_surjective_of_ker_le _
      (Algebra.TensorProduct.map_surjective _ _ (Ideal.Quotient.mkₐ_surjective R _)
        (fun c => ⟨c, rfl⟩)) ker_rTensor_mk_nilradical_le)

open ReducedTensorTower

section Tower
variable (R : Type uR) (S : Type uS) (A : Type uA) (T : Type uT) (X : Type uX)
    [CommRing R] [CommRing S] [CommRing A] [CommRing T] [CommRing X]
    [Algebra R S] [Algebra R A] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [Algebra R X] [Algebra S X] [IsScalarTower R S X]
    (e : X ≃ₐ[R] Reduction (A ⊗[R] S))
    (he : ∀ s : S, e (algebraMap S X s) = Ideal.Quotient.mk _ (1 ⊗ₜ[R] s))

private noncomputable def swappedReductionEquiv : X ≃ₐ[S] Reduction (S ⊗[R] A) where
  __ := e.trans (reductionEquiv (Algebra.TensorProduct.comm R A S))
  commutes' s := by
    change reductionEquiv (Algebra.TensorProduct.comm R A S)
      (e (algebraMap S X s)) = Ideal.Quotient.mk _ (s ⊗ₜ[R] 1)
    rw [he, reductionEquiv_mk, Algebra.TensorProduct.comm_tmul]

private noncomputable def reducedTensorTowerEquiv :
    Reduction (A ⊗[R] T) ≃ₐ[R] Reduction (X ⊗[S] T) :=
  (reductionEquiv (Algebra.TensorProduct.comm R A T)).trans <|
    ((reductionEquiv (Algebra.TensorProduct.cancelBaseChange R S T T A).symm).restrictScalars
      R).trans <|
    ((reductionEquiv (Algebra.TensorProduct.comm S T (S ⊗[R] A))).restrictScalars R).trans <|
    ((reductionTensorReductionEquiv S (S ⊗[R] A) T).restrictScalars R).trans <|
    (reductionEquiv (Algebra.TensorProduct.congr (swappedReductionEquiv R S A X e he).symm
      (AlgEquiv.refl (R := S) (A₁ := T)))).restrictScalars R

private theorem reducedTensorTowerEquiv_tmul (a : A) (t : T) :
    reducedTensorTowerEquiv R S A T X e he (Ideal.Quotient.mk _ (a ⊗ₜ[R] t)) =
      Ideal.Quotient.mk _ (e.symm (Ideal.Quotient.mk _ (a ⊗ₜ[R] 1)) ⊗ₜ[S] t) := by
  simp only [reducedTensorTowerEquiv, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    reductionEquiv_mk, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.cancelBaseChange_symm_tmul]
  show Ideal.Quotient.mk _
    ((swappedReductionEquiv R S A X e he).symm (Ideal.Quotient.mk _ (1 ⊗ₜ[R] a)) ⊗ₜ[S] t) = _
  congr 2

private theorem reducedTensorTowerEquiv_includeLeft
    (f : A →ₐ[R] X)
    (hf : ∀ a : A, e (f a) = Ideal.Quotient.mk _ (a ⊗ₜ[R] 1)) (a : A) :
    reducedTensorTowerEquiv R S A T X e he
        (Ideal.Quotient.mk _ ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] T) a)) =
      Ideal.Quotient.mk _ ((Algebra.TensorProduct.includeLeft : X →ₐ[S] X ⊗[S] T) (f a)) := by
  show reducedTensorTowerEquiv R S A T X e he (Ideal.Quotient.mk _ (a ⊗ₜ[R] 1)) = _
  rw [reducedTensorTowerEquiv_tmul, ← hf, e.symm_apply_apply]
  rfl

private theorem reducedTensorTowerEquiv_includeRight (t : T) :
    reducedTensorTowerEquiv R S A T X e he
        (Ideal.Quotient.mk _ ((Algebra.TensorProduct.includeRight : T →ₐ[R] A ⊗[R] T) t)) =
      Ideal.Quotient.mk _ ((Algebra.TensorProduct.includeRight : T →ₐ[S] X ⊗[S] T) t) := by
  show reducedTensorTowerEquiv R S A T X e he (Ideal.Quotient.mk _ (1 ⊗ₜ[R] t)) = _
  rw [reducedTensorTowerEquiv_tmul]
  simp only [← Algebra.TensorProduct.one_def, map_one, Algebra.TensorProduct.includeRight_apply]
end Tower

/-- Formal smoothness for an adic topology is invariant under ring isomorphisms of source and
target. -/
private theorem formallySmoothNAdic_ringEquiv
    {R : Type uR} {S : Type uS} {R' : Type uR'} {S' : Type uS'}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (φ : R →+* S) (n : Ideal S) (eR : R' ≃+* R) (eS : S ≃+* S')
    (h : RingHom.FormallySmoothNAdic.{uT} φ n) :
    RingHom.FormallySmoothNAdic.{uT} ((eS.toRingHom.comp φ).comp eR.toRingHom)
      (n.map eS.toRingHom) := by
  rintro T _ J hJ f ψ hcomm ⟨k, hk1, hkle⟩
  obtain ⟨g, hg1, hg2⟩ := h T J hJ (f.comp eR.symm.toRingHom) (ψ.comp eS.toRingHom)
    (by
      ext x
      simpa using congrArg (fun F : R' →+* T ⧸ J => F (eR.symm x)) hcomm)
    ⟨k, hk1, by
      intro x hx
      have : eS x ∈ n.map eS.toRingHom ^ k := by
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hx
      simpa using hkle this⟩
  refine ⟨g.comp eS.symm.toRingHom, ?_, ?_⟩
  · ext x
    simpa using congrArg (fun F : S →+* T ⧸ J => F (eS.symm x)) hg1
  · ext x
    simpa using congrArg (fun F : R →+* T => F (eR x)) hg2

/-- Reduction carries a localization to the corresponding localization of the reduction: if `S`
is the localization of `R` at `M`, then `Reduction S` is the localization of `Reduction R` at the
image of `M`, for any algebra structure on the reductions induced by the one on `R → S`. -/
theorem isLocalization_reduction
    (R : Type uR) (S : Type uS) [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S]
    [Algebra (Reduction R) (Reduction S)]
    (h : ∀ r : R, algebraMap (Reduction R) (Reduction S) (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (algebraMap R S r)) :
    IsLocalization (Algebra.algebraMapSubmonoid (Reduction R) M) (Reduction S) := by
  apply IsLocalization.of_surjective M S
    (Ideal.Quotient.mk (nilradical R)) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (nilradical S)) Ideal.Quotient.mk_surjective
  · ext r
    exact (h r).symm
  · simp only [Ideal.mk_ker]
    show (⊥ : Ideal S).radical ≤ Ideal.map (algebraMap R S) (⊥ : Ideal R).radical
    rw [IsLocalization.map_radical M S, Ideal.map_bot]

/-- Non-zero-divisors of `R` stay non-zero-divisors in the localization at a prime. -/
private theorem algebraMapSubmonoid_atPrime_le_nonZeroDivisors
    {R : Type uR} [CommRing R] (M : Submonoid R) (hM : M ≤ nonZeroDivisors R)
    (q : Ideal R) [q.IsPrime] :
    Algebra.algebraMapSubmonoid (Localization.AtPrime q) M ≤
      nonZeroDivisors (Localization.AtPrime q) := by
  rintro x ⟨r, hr, rfl⟩
  exact IsLocalization.map_nonZeroDivisors_le q.primeCompl _ ⟨r, hM hr, rfl⟩

private theorem isField_localization_genericFiber
    (R : Type uR) (S : Type uS) [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] [IsArtinianRing S]
    (hM : M ≤ nonZeroDivisors R) (q : Ideal R) [q.IsPrime]
    [IsDomain (Localization.AtPrime q)] :
    IsField (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)) := by
  let Q := Localization.AtPrime q
  let E := Localization (Algebra.algebraMapSubmonoid S q.primeCompl)
  let : IsLocalization (Algebra.algebraMapSubmonoid Q M) E :=
    IsLocalization.commutes Q S E q.primeCompl M
  let : IsDomain E := IsLocalization.isDomain_of_le_nonZeroDivisors E
    (algebraMapSubmonoid_atPrime_le_nonZeroDivisors M hM q)
  let : IsArtinianRing E := IsArtinianRing.localization_artinian
    (Algebra.algebraMapSubmonoid S q.primeCompl) E
  exact IsArtinianRing.isField_of_isDomain E

private theorem isFractionRing_of_isLocalization_of_field
    (R : Type uR) (S : Type uS) [CommRing R] [IsDomain R] [Field S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (hM : M ≤ nonZeroDivisors R) :
    IsFractionRing R S where
  map_units m := IsUnit.mk0 _ (IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors S hM m.property)
  surj s := by
    obtain ⟨⟨r, m⟩, hm⟩ := IsLocalization.surj M s
    exact ⟨⟨r, ⟨m, hM m.property⟩⟩, hm⟩
  exists_of_eq h := ⟨1, by simpa using IsLocalization.injective S hM h⟩

private theorem formallySmoothNAdic_localRingHom_of_isLocalization
    {R : Type uR} {S : Type uS} {R' : Type uR'} {S' : Type uS'}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R R'] [Algebra S S']
    (M : Submonoid R) (N : Submonoid S) [IsLocalization M R'] [IsLocalization N S']
    (f : R →+* S) (f' : R' →+* S')
    (hcomm : f'.comp (algebraMap R R') = (algebraMap S S').comp f)
    (p : Ideal R) (q : Ideal S) (p' : Ideal R') (q' : Ideal S')
    [p.IsPrime] [q.IsPrime] [p'.IsPrime] [q'.IsPrime]
    (hpq : p = q.comap f) (hpq' : p' = q'.comap f')
    (hqq' : q = q'.comap (algebraMap S S'))
    (hformal : RingHom.FormallySmoothNAdic.{uT}
      (Localization.localRingHom p' q' f' hpq')
      (IsLocalRing.maximalIdeal (Localization.AtPrime q'))) :
    RingHom.FormallySmoothNAdic.{uT} (Localization.localRingHom p q f hpq)
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) := by
  have hpp' : p = p'.comap (algebraMap R R') := by
    rw [hpq, hpq', hqq', Ideal.comap_comap, Ideal.comap_comap, hcomm]
  let : IsLocalization.AtPrime (Localization.AtPrime p') p := by
    have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime p') p'
    clear hpq
    subst p
    exact h
  let : IsLocalization.AtPrime (Localization.AtPrime q') q := by
    have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization N
      (Localization.AtPrime q') q'
    subst q
    exact h
  let eR := IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) (Localization.AtPrime p')
  let eS := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q') (Localization.AtPrime q)
  have he : ((eS.toRingEquiv.toRingHom.comp (Localization.localRingHom p' q' f' hpq')).comp
      eR.toRingEquiv.toRingHom) = Localization.localRingHom p q f hpq := by
    symm
    apply Localization.localRingHom_unique
    intro r
    show eS (Localization.localRingHom p' q' f' hpq' (eR (algebraMap R _ r))) = _
    rw [eR.commutes, IsScalarTower.algebraMap_apply R R' (Localization.AtPrime p'),
      Localization.localRingHom_to_map,
      show f' (algebraMap R R' r) = algebraMap S S' (f r) from DFunLike.congr_fun hcomm r,
      ← IsScalarTower.algebraMap_apply S S' (Localization.AtPrime q'), eS.commutes]
  have h := formallySmoothNAdic_ringEquiv _ _ eR.toRingEquiv eS.toRingEquiv hformal
  rw [he] at h
  have hm : (IsLocalRing.maximalIdeal (Localization.AtPrime q')).map eS.toRingEquiv.toRingHom =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) :=
    IsLocalRing.map_ringEquiv_maximalIdeal eS.toRingEquiv
  rwa [hm] at h

/-- The map on integral closures induced by an `R`-algebra map `f : A →ₐ[R] B` whose target is
also an `S`-algebra: the image of an element integral over `R` is integral over `R`, hence
integral over `S`. -/
def integralClosureMapOfScalarTower
    {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    (f : A →ₐ[R] B) : integralClosure R A →ₐ[R] integralClosure S B where
  __ := (f.toRingHom.comp (integralClosure R A).subtype).codRestrict
    (integralClosure S B) fun a => (a.property.map f).tower_top
  commutes' r := by
    apply Subtype.ext
    exact f.commutes r

/-- The induced map on integral closures acts as `f` on underlying elements. -/
theorem integralClosureMapOfScalarTower_apply
    {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    (f : A →ₐ[R] B) (a : integralClosure R A) :
    (integralClosureMapOfScalarTower (S := S) f a : B) = f (a : A) := rfl

private theorem isLocalization_reducedTensor
    (R : Type uR) (A : Type uA) (B : Type uB) (C : Type uC)
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra A B] [IsScalarTower R A B]
    (M : Submonoid A) [IsLocalization M B] :
    letI : Algebra (Reduction (A ⊗[R] C)) (Reduction (B ⊗[R] C)) :=
      (reducedTensorMap (IsScalarTower.toAlgHom R A B) (AlgHom.id R C)).toRingHom.toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (Reduction (A ⊗[R] C)) M)
      (Reduction (B ⊗[R] C)) := by
  let f : A ⊗[R] C →ₐ[R] B ⊗[R] C :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A B) (AlgHom.id R C)
  let : Algebra (A ⊗[R] C) (B ⊗[R] C) := f.toRingHom.toAlgebra
  let : IsScalarTower A (A ⊗[R] C) (B ⊗[R] C) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap A B a ⊗ₜ[R] (1 : C) = f (a ⊗ₜ[R] (1 : C))
      simp [f]
  let : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[R] C) M) (B ⊗[R] C) :=
    IsLocalization.tensorProduct_tensorProduct R C M B (by
      ext c
      show f (1 ⊗ₜ[R] c) = 1 ⊗ₜ[R] c
      simp [f])
  let : Algebra (Reduction (A ⊗[R] C)) (Reduction (B ⊗[R] C)) :=
    (reducedTensorMap (IsScalarTower.toAlgHom R A B) (AlgHom.id R C)).toRingHom.toAlgebra
  have h := isLocalization_reduction (A ⊗[R] C) (B ⊗[R] C)
    (Algebra.algebraMapSubmonoid (A ⊗[R] C) M) (fun _ => rfl)
  convert h using 1
  show M.map (algebraMap A _) = (M.map (algebraMap A (A ⊗[R] C))).map
    (algebraMap (A ⊗[R] C) _)
  exact (Submonoid.map_map _ _ _).symm

universe uD uD'
private theorem exists_reducedTensorLocalizationEquiv
    (R : Type uR) (A : Type uA) (B : Type uB) (C : Type uC)
    (D : Type uD) (D' : Type uD')
    [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D] [CommRing D']
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D] [Algebra R D']
    [Algebra A B] [IsScalarTower R A B]
    [Algebra A D] [IsScalarTower R A D] [Algebra C D]
    [Algebra D D'] [IsScalarTower R D D']
    [Algebra A D'] [IsScalarTower A D D'] [Algebra B D'] [IsScalarTower A B D']
    [Algebra C D'] [IsScalarTower C D D']
    (M : Submonoid A) [IsLocalization M B]
    [IsLocalization (Algebra.algebraMapSubmonoid D M) D']
    (e : D ≃ₐ[R] Reduction (A ⊗[R] C))
    (heA : ∀ a : A, e (algebraMap A D a) = Ideal.Quotient.mk _ (a ⊗ₜ[R] 1))
    (heC : ∀ c : C, e (algebraMap C D c) = Ideal.Quotient.mk _ (1 ⊗ₜ[R] c)) :
    ∃ e' : D' ≃ₐ[R] Reduction (B ⊗[R] C),
      (∀ b : B, e' (algebraMap B D' b) = Ideal.Quotient.mk _ (b ⊗ₜ[R] 1)) ∧
      (∀ c : C, e' (algebraMap C D' c) = Ideal.Quotient.mk _ (1 ⊗ₜ[R] c)) := by
  let P := Reduction (A ⊗[R] C)
  let Q := Reduction (B ⊗[R] C)
  let g : P →ₐ[R] Q := reducedTensorMap (IsScalarTower.toAlgHom R A B) (AlgHom.id R C)
  let : Algebra P Q := g.toRingHom.toAlgebra
  let : IsLocalization (Algebra.algebraMapSubmonoid P M) Q :=
    isLocalization_reducedTensor R A B C M
  let : Algebra D Q := (g.comp e.toAlgHom).toRingHom.toAlgebra
  let : IsScalarTower R D Q := IsScalarTower.of_algebraMap_eq fun r =>
    ((g.comp e.toAlgHom).commutes r).symm
  have hM : (Algebra.algebraMapSubmonoid D M).map e.toRingEquiv.toMonoidHom =
      Algebra.algebraMapSubmonoid P M := by
    show (M.map (algebraMap A D)).map e.toRingEquiv.toMonoidHom = M.map (algebraMap A P)
    trans M.map (e.toRingEquiv.toMonoidHom.comp (algebraMap A D).toMonoidHom)
    · exact Submonoid.map_map _ _ _
    · congr 1
      ext a
      exact heA a
  let : IsLocalization (Algebra.algebraMapSubmonoid D M) Q :=
    IsLocalization.of_ringEquiv_left e.toRingEquiv hM (fun _ => rfl)
  let e' := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid D M) D' Q
  have heD (d : D) : e' (algebraMap D D' d) = g (e d) := e'.commutes d
  refine ⟨e'.restrictScalars R, ?_, ?_⟩
  · have hB : e'.toRingEquiv.toRingHom.comp (algebraMap B D') =
        (Ideal.Quotient.mk (nilradical (B ⊗[R] C))).comp
          (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] C).toRingHom := by
      apply IsLocalization.ringHom_ext M
      ext a
      show e' (algebraMap B D' (algebraMap A B a)) =
        Ideal.Quotient.mk _ (algebraMap A B a ⊗ₜ[R] 1)
      rw [← IsScalarTower.algebraMap_apply A B D', IsScalarTower.algebraMap_apply A D D',
        heD, heA]
      exact reducedTensorMap_tmul _ _ a 1
    exact DFunLike.congr_fun hB
  · intro c
    show e' (algebraMap C D' c) = _
    rw [IsScalarTower.algebraMap_apply C D D', heD, heC]
    show Ideal.Quotient.mk _ (algebraMap A B 1 ⊗ₜ[R] c) = _
    rw [map_one]

private theorem isLocalization_integralClosure_of_scalarTower
    (R : Type uR) (S : Type uS) (A : Type uA) (B : Type uB)
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [Algebra A B]
    [IsScalarTower R S B] [IsScalarTower R A B]
    (M : Submonoid R) [IsLocalization M S]
    [IsLocalization (Algebra.algebraMapSubmonoid A M) B] :
    letI : Algebra (integralClosure R A) (integralClosure S B) :=
      (integralClosureMapOfScalarTower (S := S)
        (IsScalarTower.toAlgHom R A B)).toRingHom.toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R A) M)
      (integralClosure S B) := by
  let f := integralClosureMapOfScalarTower (S := S) (IsScalarTower.toAlgHom R A B)
  let : Algebra (integralClosure R A) (integralClosure S B) := f.toRingHom.toAlgebra
  let : Algebra (integralClosure R A) B :=
    ((algebraMap A B).comp (integralClosure R A).subtype).toAlgebra
  let : IsScalarTower (integralClosure R A) (integralClosure S B) B :=
    ⟨fun a x y => by
      simp only [Subalgebra.smul_def, Algebra.smul_def]
      show (algebraMap A B (a : A) * (x : B)) * y =
        algebraMap A B (a : A) * ((x : B) * y)
      exact mul_assoc _ _ _⟩
  let : IsScalarTower R (integralClosure R A) (integralClosure S B) :=
    IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  exact IsLocalization.integralClosure M

universe uF
private theorem formallySmooth_integralClosure_localRingHom
    (R : Type uR) (S : Type uS) (K : Type uK) (F : Type uF)
    (C : Type uC) (T : Type uT)
    [CommRing R] [IsDomain R] [CommRing S] [Field K] [CommRing F] [Field C] [CommRing T]
    [Algebra R S] [Algebra R K] [Algebra K F] [Algebra S F] [Algebra R F]
    [IsScalarTower R S F] [IsScalarTower R K F] [IsFractionRing R K]
    [Algebra K C] [Algebra R C] [IsScalarTower R K C] [Module.Finite K C]
    [Algebra K T] [Algebra F T] [Algebra C T] [Algebra S T] [Algebra R T]
    [IsScalarTower K F T] [IsScalarTower K C T] [IsScalarTower S F T]
    [IsScalarTower R S T] [IsScalarTower R K T] [IsScalarTower R C T]
    (M : Submonoid S) [IsLocalization M F] [IsArtinianRing F]
    (hM : M ≤ nonZeroDivisors S)
    (e : T ≃ₐ[K] Reduction (F ⊗[K] C))
    (heF : ∀ x : F, e (algebraMap F T x) = Ideal.Quotient.mk _ (x ⊗ₜ[K] 1))
    (heC : ∀ x : C, e (algebraMap C T x) = Ideal.Quotient.mk _ (1 ⊗ₜ[K] x))
    (f₂ : integralClosure R C →+* integralClosure S T)
    (hf₂ : ∀ x : integralClosure R C, (f₂ x : T) = algebraMap C T (x : C))
    (q₂ : Ideal (integralClosure S T)) [q₂.IsMaximal]
    (q : Ideal S) [q.IsPrime]
    (hqq₂ : q = q₂.comap (algebraMap S (integralClosure S T)))
    (p : Ideal R) [p.IsPrime] (hpq : p = q.comap (algebraMap R S))
    [IsDiscreteValuationRing (Localization.AtPrime p)]
    [IsDomain (Localization.AtPrime q)] [IsDiscreteValuationRing (Localization.AtPrime q)]
    (hinj : Function.Injective (Localization.localRingHom p q (algebraMap R S) hpq))
    (hformal : RingHom.FormallySmoothNAdic.{max uR uS}
      (Localization.localRingHom p q (algebraMap R S) hpq)
      (IsLocalRing.maximalIdeal (Localization.AtPrime q))) :
    letI : (q₂.comap f₂).IsPrime := Ideal.IsPrime.comap f₂
    RingHom.FormallySmoothNAdic.{max uC uT}
      (Localization.localRingHom (q₂.comap f₂) q₂ f₂ rfl)
      (IsLocalRing.maximalIdeal (Localization.AtPrime q₂)) := by
  classical
  let Rq := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let E := Localization (Algebra.algebraMapSubmonoid F q.primeCompl)
  let Tq := Localization (Algebra.algebraMapSubmonoid T q.primeCompl)
  let : Algebra Rq Sq := (Localization.localRingHom p q (algebraMap R S) hpq).toAlgebra
  let : FaithfulSMul Rq Sq := (faithfulSMul_iff_algebraMap_injective Rq Sq).mpr hinj
  let : IsLocalHom (algebraMap Rq Sq) :=
    inferInstanceAs (IsLocalHom (Localization.localRingHom p q (algebraMap R S) hpq))
  let : IsExtension Rq Sq := {}
  let : IsScalarTower R Rq Sq := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap S Sq (algebraMap R S r) =
      Localization.localRingHom p q (algebraMap R S) hpq (algebraMap R Rq r)
    exact (Localization.localRingHom_to_map p q _ hpq r).symm
  have hK : ∀ m : p.primeCompl, IsUnit (algebraMap R K m) := fun m =>
    IsUnit.mk0 _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (show (m : R) ∈ nonZeroDivisors R from mem_nonZeroDivisors_iff_ne_zero.mpr
        (fun hz => m.property (hz ▸ p.zero_mem))))
  let : Algebra Rq K := (IsLocalization.lift (S := Rq) hK).toAlgebra
  let : IsScalarTower R Rq K := IsScalarTower.of_algebraMap_eq fun r =>
    (IsLocalization.lift_eq hK r).symm
  let : IsFractionRing Rq K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl Rq K
  let : Algebra Rq C := ((algebraMap K C).comp (algebraMap Rq K)).toAlgebra
  let : IsScalarTower Rq K C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower R Rq C := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R K C, IsScalarTower.algebraMap_apply R Rq K,
      ← IsScalarTower.algebraMap_apply Rq K C]
  let : Field E := (isField_localization_genericFiber S F M hM q).toField
  let : IsLocalization (Algebra.algebraMapSubmonoid Sq M) E :=
    IsLocalization.commutes Sq F E q.primeCompl M
  let : IsFractionRing Sq E := isFractionRing_of_isLocalization_of_field Sq E _
    (algebraMapSubmonoid_atPrime_le_nonZeroDivisors M hM q)
  let : Algebra Rq E := ((algebraMap Sq E).comp (algebraMap Rq Sq)).toAlgebra
  let : IsScalarTower Rq Sq E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower R Rq E := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R S E, IsScalarTower.algebraMap_apply S Sq E,
      ← IsScalarTower.algebraMap_apply R S Sq, IsScalarTower.algebraMap_apply R Rq Sq, ←
        IsScalarTower.algebraMap_apply Rq Sq E]
  let : IsScalarTower Rq K E := IsScalarTower.of_algebraMap_eq' (by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext r
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply])
  let : IsLocalization
      (Algebra.algebraMapSubmonoid T (Algebra.algebraMapSubmonoid F q.primeCompl)) Tq := by
    rw [Algebra.algebraMapSubmonoid_map_map]
    infer_instance
  let : Algebra E Tq :=
    localizationAlgebra (Algebra.algebraMapSubmonoid F q.primeCompl) T
  let : IsScalarTower F E Tq :=
    isScalarTower_localizationAlgebra _ _
  let : IsScalarTower K E Tq := IsScalarTower.of_algebraMap_eq fun k => by
    rw [IsScalarTower.algebraMap_apply K F E, ← IsScalarTower.algebraMap_apply F E Tq,
      ← IsScalarTower.algebraMap_apply K F Tq]
  obtain ⟨eTq, heTqE, heTqC⟩ := exists_reducedTensorLocalizationEquiv K F E C T Tq
    (Algebra.algebraMapSubmonoid F q.primeCompl) e heF heC
  let : Algebra Rq Tq := ((algebraMap Sq Tq).comp (algebraMap Rq Sq)).toAlgebra
  let : IsScalarTower Rq Sq Tq := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower S Sq Tq := inferInstance
  let : IsScalarTower R Rq Tq := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R S Tq, IsScalarTower.algebraMap_apply S Sq Tq,
      ← IsScalarTower.algebraMap_apply R S Sq, IsScalarTower.algebraMap_apply R Rq Sq,
      ← IsScalarTower.algebraMap_apply Rq Sq Tq]
  let : IsScalarTower S E Tq := IsScalarTower.of_algebraMap_eq fun s => by
    rw [IsScalarTower.algebraMap_apply S F E, ← IsScalarTower.algebraMap_apply F E Tq,
      ← IsScalarTower.algebraMap_apply S F Tq]
  let : IsScalarTower Sq E Tq := IsScalarTower.of_algebraMap_eq' (by
    apply IsLocalization.ringHom_ext q.primeCompl
    ext s
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply])
  let : IsScalarTower Rq K Tq := IsScalarTower.of_algebraMap_eq' (by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext r
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply])
  let : IsScalarTower Rq C Tq := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply Rq K C, ← IsScalarTower.algebraMap_apply K C Tq,
      ← IsScalarTower.algebraMap_apply Rq K Tq]
  let R₂ := integralClosure R C
  let S₂ := integralClosure S T
  let R₂q := integralClosure Rq C
  let S₂q := integralClosure Sq Tq
  let f₂q : R₂q →+* S₂q :=
    (integralClosureMapOfScalarTower (S := Sq) (IsScalarTower.toAlgHom Rq C Tq)).toRingHom
  let : Algebra R₂q S₂q := f₂q.toAlgebra
  let : IsScalarTower Rq R₂q S₂q := IsScalarTower.of_algebraMap_eq fun r =>
    ((integralClosureMapOfScalarTower (S := Sq) (IsScalarTower.toAlgHom Rq C Tq)).commutes r).symm
  let : IsScalarTower Sq S₂q Tq := ⟨fun s x y => by
    simp only [Algebra.smul_def]
    exact mul_assoc _ _ _⟩
  have hbase := formallySmooth_localizations_after_finite_fraction_field_extension
    Rq Sq K E C Tq R₂q S₂q eTq (AlgEquiv.refl) (AlgEquiv.refl)
    heTqE heTqC (fun _ => rfl)
    (fun k => by rw [← IsScalarTower.algebraMap_apply K E Tq,
      ← IsScalarTower.algebraMap_apply K C Tq])
    (fun _ => rfl) hformal
  let gR : R₂ →ₐ[R] R₂q := integralClosureMapOfScalarTower (S := Rq)
    (IsScalarTower.toAlgHom R C C)
  let gS : S₂ →ₐ[S] S₂q := integralClosureMapOfScalarTower (S := Sq)
    (IsScalarTower.toAlgHom S T Tq)
  let : Algebra R₂ R₂q := gR.toRingHom.toAlgebra
  let : Algebra S₂ S₂q := gS.toRingHom.toAlgebra
  let : IsLocalization (Algebra.algebraMapSubmonoid C p.primeCompl) C :=
    IsLocalization.of_le_isUnit (by
      rintro x ⟨r, hr, rfl⟩
      show IsUnit (algebraMap R C r)
      rw [IsScalarTower.algebraMap_apply R K C]
      exact (hK ⟨r, hr⟩).map (algebraMap K C))
  let : IsLocalization (Algebra.algebraMapSubmonoid R₂ p.primeCompl) R₂q :=
    isLocalization_integralClosure_of_scalarTower R Rq C C p.primeCompl
  let : IsLocalization (Algebra.algebraMapSubmonoid S₂ q.primeCompl) S₂q :=
    isLocalization_integralClosure_of_scalarTower S Sq T Tq q.primeCompl
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid S₂ q.primeCompl : Set S₂) (q₂ : Set S₂) := by
    rw [Set.disjoint_left]
    rintro x ⟨s, hs, rfl⟩ hx
    exact hs (show s ∈ q from hqq₂ ▸ hx)
  let Q₂ := q₂.map (algebraMap S₂ S₂q)
  let : Q₂.IsMaximal := IsLocalization.isMaximal_of_isMaximal_disjoint
    (Algebra.algebraMapSubmonoid S₂ q.primeCompl) S₂q q₂ hdisj
  have hQ₂ : q₂ = Q₂.comap (algebraMap S₂ S₂q) :=
    (IsLocalization.under_map_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid S₂ q.primeCompl) S₂q (inferInstance : q₂.IsPrime) hdisj).symm
  obtain ⟨_, hQprime, hPprime, _, _, φ, _, _, hφ, hφsmooth⟩ := hbase.2.2 Q₂ inferInstance
  let P₂ := Q₂.comap f₂q
  let : P₂.IsPrime := Ideal.IsPrime.comap f₂q
  rw [← Localization.localRingHom_unique P₂ Q₂ f₂q rfl hφ] at hφsmooth
  apply formallySmoothNAdic_localRingHom_of_isLocalization
    (Algebra.algebraMapSubmonoid R₂ p.primeCompl)
    (Algebra.algebraMapSubmonoid S₂ q.primeCompl) f₂ f₂q ?_
    (q₂.comap f₂) q₂ P₂ Q₂ rfl rfl hQ₂ hφsmooth
  ext a
  show algebraMap C Tq (a : C) = algebraMap T Tq (f₂ a : T)
  rw [hf₂, ← IsScalarTower.algebraMap_apply C T Tq]

/-- A finite extension of a solution for an extension of discrete valuation rings is again a
solution. -/
@[stacks 0GLR]
theorem exists_isSolution_of_tower
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    (K₁ : Type uK₁) (K₂ : Type uK₂)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁] [Field K₂]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [Algebra K₁ K₂] [Algebra K K₂]
    [Algebra A K₁] [Algebra A K₂]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower A K K₁] [IsScalarTower A K K₂]
    [IsScalarTower K K₁ K₂] [IsScalarTower A K₁ K₂]
    [IsExtension A B]
    [IsFractionRing A K] [IsFractionRing B L]
    [Module.Finite K K₁] [Module.Finite K₁ K₂]
    (hsolution :
      ∃ D₁ : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁,
          max uL uK₁, uK₁, max uL uK₁} A B K L K₁,
        D₁.IsSolution.{uA, uB, uK, uL, uK₁, max uL uK₁, uK₁, max uL uK₁,
          max uL uK₁}) :
    letI : Module.Finite K K₂ := Module.Finite.trans K₁ K₂
    ∃ D₂ : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₂,
        max uL uK₂, uK₂, max uL uK₂} A B K L K₂,
      D₂.IsSolution.{uA, uB, uK, uL, uK₂, max uL uK₂, uK₂, max uL uK₂,
        max uL uK₂} := by
  classical
  let : Module.Finite K K₂ := Module.Finite.trans K₁ K₂
  obtain ⟨D₁, hD₁⟩ := hsolution
  let := D₁.commRingL₁
  let := D₁.commRingA₁
  let := D₁.commRingB₁
  let := D₁.algebraKL₁
  let := D₁.algebraLL₁
  let := D₁.algebraK₁L₁
  let := D₁.algebraBL₁
  let := D₁.algebraAA₁
  let := D₁.algebraA₁K₁
  let := D₁.algebraBB₁
  let := D₁.algebraB₁L₁
  let := D₁.algebraAB₁
  let := D₁.algebraA₁B₁
  let := D₁.isScalarTowerKLL₁
  let := D₁.isScalarTowerKK₁L₁
  let := D₁.isScalarTowerBLL₁
  let := D₁.isScalarTowerAA₁K₁
  let := D₁.isScalarTowerBB₁L₁
  let := D₁.isScalarTowerABB₁
  let := D₁.isScalarTowerAA₁B₁
  let := D₁.isIntegralClosureA₁
  let := D₁.isIntegralClosureB₁
  let R := D₁.A₁
  let S := D₁.B₁
  let F := D₁.L₁
  have hdata := integralClosures_after_finite_fraction_field_extension
    A B K L K₁ F R S D₁.eL₁
    (IsIntegralClosure.equiv A R K₁ (integralClosure A K₁))
    (IsIntegralClosure.equiv B S F (integralClosure B F))
    D₁.eL₁_left D₁.eL₁_right
    (fun x => IsIntegralClosure.algebraMap_equiv B S F (integralClosure B F) x)
    (fun k => by rw [← IsScalarTower.algebraMap_apply K L F,
      ← IsScalarTower.algebraMap_apply K K₁ F])
    (fun r => by
      rw [show ((IsIntegralClosure.equiv A R K₁ (integralClosure A K₁) r :
        integralClosure A K₁) : K₁) = algebraMap R K₁ r from
          IsIntegralClosure.algebraMap_equiv A R K₁ (integralClosure A K₁) r]
      exact D₁.ringSquare r)
  obtain ⟨_, hR, _, _, _, _, _, _, _, hlocal, _⟩ := hdata
  let : IsDedekindDomain R := hR
  let : IsFractionRing R K₁ := IsIntegralClosure.isFractionRing_of_finite_extension A K K₁ R
  let : Algebra.IsIntegral A R := IsIntegralClosure.isIntegral_algebra A K₁
  let : Algebra.IsIntegral B S := IsIntegralClosure.isIntegral_algebra B F
  let eLF : F ≃ₐ[L] Reduction (L ⊗[K] K₁) :=
    { __ := D₁.eL₁
      commutes' := D₁.eL₁_left }
  let : Module.Finite L F := Module.Finite.equiv eLF.symm.toLinearEquiv
  let : IsArtinianRing F := IsArtinianRing.of_finite L F
  let M := Algebra.algebraMapSubmonoid S (nonZeroDivisors B)
  let : IsLocalization M F :=
    Stacks.DiscreteValuationRing.Ramification.isLocalization_integralClosure_of_isIntegral
      B L F S (nonZeroDivisors B)
  have hM : M ≤ nonZeroDivisors S := by
    rintro x ⟨b, hb, rfl⟩
    apply mem_nonZeroDivisors_of_injective (IsIntegralClosure.algebraMap_injective S B F)
    rw [← IsScalarTower.algebraMap_apply B S F, IsScalarTower.algebraMap_apply B L F]
    exact ((IsLocalization.map_units L (⟨b, hb⟩ : nonZeroDivisors B)).map
      (algebraMap L F)).mem_nonZeroDivisors
  let D₀ := canonicalBaseChange A B K L K₂
  let := D₀.commRingL₁
  let := D₀.algebraKL₁
  let := D₀.algebraLL₁
  let := D₀.algebraK₁L₁
  let := D₀.algebraBL₁
  let := D₀.isScalarTowerKLL₁
  let := D₀.isScalarTowerKK₁L₁
  let := D₀.isScalarTowerBLL₁
  let T := D₀.L₁
  let eTower := reducedTensorTowerEquiv K K₁ L K₂ F D₁.eL₁ D₁.eL₁_right
  let eT₀ : T ≃ₐ[K] Reduction (F ⊗[K₁] K₂) := D₀.eL₁.trans eTower
  let : Algebra K₁ T :=
    (eT₀.symm.toRingHom.comp (algebraMap K₁ (Reduction (F ⊗[K₁] K₂)))).toAlgebra
  let : Algebra F T :=
    (eT₀.symm.toRingHom.comp (algebraMap F (Reduction (F ⊗[K₁] K₂)))).toAlgebra
  let eT : T ≃ₐ[K₁] Reduction (F ⊗[K₁] K₂) :=
    { __ := eT₀
      commutes' k := eT₀.apply_symm_apply _ }
  have heF (x : F) : eT (algebraMap F T x) = Ideal.Quotient.mk _ (x ⊗ₜ[K₁] 1) :=
    eT₀.apply_symm_apply _
  have heC (x : K₂) : eT (algebraMap K₂ T x) = Ideal.Quotient.mk _ (1 ⊗ₜ[K₁] x) := by
    show eTower (D₀.eL₁ (algebraMap K₂ T x)) = _
    rw [D₀.eL₁_right]
    exact reducedTensorTowerEquiv_includeRight K K₁ L K₂ F D₁.eL₁ D₁.eL₁_right x
  have heL (x : L) : eT₀ (algebraMap L T x) =
      Ideal.Quotient.mk _ (algebraMap L F x ⊗ₜ[K₁] 1) := by
    show eTower (D₀.eL₁ (algebraMap L T x)) = _
    rw [D₀.eL₁_left]
    exact reducedTensorTowerEquiv_includeLeft K K₁ L K₂ F D₁.eL₁ D₁.eL₁_right
      (IsScalarTower.toAlgHom K L F) D₁.eL₁_left x
  let : IsScalarTower K₁ F T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower L F T := IsScalarTower.of_algebraMap_eq fun l =>
    eT₀.injective ((heL l).trans (heF (algebraMap L F l)).symm)
  let : IsScalarTower K₁ K₂ T := IsScalarTower.of_algebraMap_eq fun k => by
    apply eT.injective
    rw [eT.commutes, heC]
    show Ideal.Quotient.mk _ (algebraMap K₁ F k ⊗ₜ[K₁] 1) =
      Ideal.Quotient.mk _ (1 ⊗ₜ[K₁] algebraMap K₁ K₂ k)
    exact congrArg (Ideal.Quotient.mk _) (DFunLike.congr_fun
      Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap k)
  let : Algebra R F := ((algebraMap K₁ F).comp (algebraMap R K₁)).toAlgebra
  let : IsScalarTower R K₁ F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower R S F := IsScalarTower.of_algebraMap_eq fun r => (D₁.ringSquare r).symm
  let : Algebra R K₂ := ((algebraMap K₁ K₂).comp (algebraMap R K₁)).toAlgebra
  let : IsScalarTower R K₁ K₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra S T := ((algebraMap F T).comp (algebraMap S F)).toAlgebra
  let : IsScalarTower S F T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra R T := ((algebraMap K₁ T).comp (algebraMap R K₁)).toAlgebra
  let : IsScalarTower R K₁ T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R K₁ T, IsScalarTower.algebraMap_apply K₁ F T,
      ← D₁.ringSquare, ← IsScalarTower.algebraMap_apply S F T]
  let : IsScalarTower R K₂ T := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R K₁ K₂, ← IsScalarTower.algebraMap_apply K₁ K₂ T,
      ← IsScalarTower.algebraMap_apply R K₁ T]
  let : IsScalarTower B S T := IsScalarTower.of_algebraMap_eq fun b => by
    rw [IsScalarTower.algebraMap_apply B L T, IsScalarTower.algebraMap_apply L F T,
      ← IsScalarTower.algebraMap_apply B L F, IsScalarTower.algebraMap_apply B S F,
      ← IsScalarTower.algebraMap_apply S F T]
  let : IsScalarTower A R K₂ := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A K₁ K₂, IsScalarTower.algebraMap_apply A R K₁,
      ← IsScalarTower.algebraMap_apply R K₁ K₂]
  let : Algebra A T := ((algebraMap B T).comp (algebraMap A B)).toAlgebra
  let : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower A L T := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A B T, IsScalarTower.algebraMap_apply B L T,
      ← IsScalarTower.algebraMap_apply A B L]
  let : IsScalarTower A K T := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A L T, IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply K L T]
  let : IsScalarTower A K₂ T := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A K K₂, ← IsScalarTower.algebraMap_apply K K₂ T,
      ← IsScalarTower.algebraMap_apply A K T]
  let : IsScalarTower A S T := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A B T, IsScalarTower.algebraMap_apply B S T,
      ← IsScalarTower.algebraMap_apply A B S]
  let : IsScalarTower A R T := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A K₂ T, IsScalarTower.algebraMap_apply A R K₂,
      ← IsScalarTower.algebraMap_apply R K₂ T]
  let R₂ := integralClosure R K₂
  let S₂ := integralClosure S T
  let f₂ : R₂ →+* S₂ :=
    (integralClosureMapOfScalarTower (S := S) (IsScalarTower.toAlgHom R K₂ T)).toRingHom
  let : Algebra R₂ S₂ := f₂.toAlgebra
  let : IsScalarTower A R₂ S₂ := IsScalarTower.of_algebraMap_eq fun a => by
    apply Subtype.ext
    show algebraMap S₂ T (algebraMap A S₂ a) =
      algebraMap K₂ T (algebraMap R₂ K₂ (algebraMap A R₂ a))
    rw [← IsScalarTower.algebraMap_apply A S₂ T, ← IsScalarTower.algebraMap_apply A R₂ K₂,
      ← IsScalarTower.algebraMap_apply A K₂ T]
  let : Algebra.IsIntegral A R₂ := Algebra.IsIntegral.trans R
  let : Algebra.IsIntegral B S₂ := Algebra.IsIntegral.trans S
  let : IsIntegralClosure R₂ A K₂ := IsIntegralClosure.of_isIntegrallyClosedIn
  let : IsIntegralClosure S₂ B T := IsIntegralClosure.of_isIntegrallyClosedIn
  let D₂ : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₂,
      max uL uK₂, uK₂, max uL uK₂} A B K L K₂ := {
    L₁ := T
    A₁ := R₂
    B₁ := S₂
    eL₁ := D₀.eL₁
    eL₁_left := D₀.eL₁_left
    eL₁_right := D₀.eL₁_right
    ringSquare := fun _ => rfl }
  refine ⟨D₂, fun q₂ hq₂ => ?_⟩
  let : q₂.IsMaximal := hq₂
  let q := q₂.comap (algebraMap S S₂)
  let : q.IsMaximal := Ideal.IsMaximal.under S q₂
  let p := q.comap (algebraMap R S)
  let : p.IsPrime := Ideal.IsPrime.comap (algebraMap R S)
  obtain ⟨_, _, _, ⟨hRp, hDVRp⟩, ⟨hSq, hDVRq⟩, φ, hφinj, _, hφ⟩ :=
    hlocal q inferInstance
  let := hSq
  let := hDVRq
  let := hDVRp
  rw [← Localization.localRingHom_unique p q (algebraMap R S) rfl hφ] at hφinj
  exact formallySmooth_integralClosure_localRingHom R S K₁ F K₂ T M hM eT heF heC
    f₂ (fun _ => rfl) q₂ q rfl p rfl hφinj (hD₁ q inferInstance)
end IsDiscreteValuationRing
