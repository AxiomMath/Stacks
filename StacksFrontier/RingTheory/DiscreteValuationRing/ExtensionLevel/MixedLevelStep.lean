module

public import StacksFrontier.NumberTheory.Cyclotomic.OneAddPow
public import StacksFrontier.RingTheory.DiscreteValuationRing.PurelyInseparable
public import StacksFrontier.RingTheory.LocalRing.ResidueSection
public import StacksFrontier.RingTheory.DiscreteValuationRing.ExtensionLevel.ArtinSchreierShift

open Stacks.DiscreteValuationRing.AdjoinPthRoot

/-!
# One step of the level induction

Weak solutions from tensor products and unramified normalizations, and the outcome of one step
of lowering the level of a degree-`p` extension.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u uA uK uL

open Polynomial

namespace Stacks.DiscreteValuationRing.EppLevelInduction

private theorem exists_isWeakSolution_of_tensor_closure
    {A C K M E : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Field K] [Field M] [Field E]
    [Algebra A C] [Algebra A K] [Algebra C M] [Algebra A M]
    [Algebra K M] [Algebra K E] [Algebra A E]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower A K E]
    [IsDiscreteValuationRing.IsExtension A C] [IsFractionRing A K] [IsFractionRing C M]
    [Module.Finite K E] [IsReduced (M ⊗[K] E)]
    (g : integralClosure A E →+* integralClosure C (M ⊗[K] E))
    (hg : ∀ a : integralClosure A E,
      (g a : M ⊗[K] E) = (Algebra.TensorProduct.includeRight : E →ₐ[K] M ⊗[K] E) a)
    (hweak : letI := g.toAlgebra
      ∀ q : Ideal (integralClosure C (M ⊗[K] E)), q.IsMaximal →
        q.ramificationIdx (integralClosure A E) = 1) :
    ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A C K M E,
      D.IsWeakSolution := by
  let T := M ⊗[K] E
  let A₁ := integralClosure A E
  let C₁ := integralClosure C T
  let : Algebra E T := Algebra.TensorProduct.rightAlgebra
  let : Algebra A₁ C₁ := g.toAlgebra
  have : IsScalarTower A A₁ C₁ := IsScalarTower.of_algebraMap_eq fun a => by
    apply Subtype.ext
    change algebraMap A T a = (g (algebraMap A A₁ a) : T)
    rw [hg]
    exact ((Algebra.TensorProduct.includeRight : E →ₐ[K] T).restrictScalars A).commutes a |>.symm
  let eT : T ≃ₐ[K] (T ⧸ nilradical T) :=
    (AlgEquiv.quotientBot K T).symm.trans
      (Ideal.quotientEquivAlg ⊥ (nilradical T) (AlgEquiv.refl : T ≃ₐ[K] T) (by simp))
  let D : IsDiscreteValuationRing.IntegralClosureBaseChange A C K M E :=
    { L₁ := T
      A₁ := A₁
      B₁ := C₁
      eL₁ := eT
      eL₁_left := by
        intro m
        simp only [eT, AlgEquiv.trans_apply, AlgEquiv.quotientBot_symm_mk,
          Ideal.quotientEquivAlg]
        rfl
      eL₁_right := by
        intro a
        simp only [eT, AlgEquiv.trans_apply, AlgEquiv.quotientBot_symm_mk,
          Ideal.quotientEquivAlg]
        rfl
      ringSquare := hg }
  exact ⟨D, hweak⟩

private theorem exists_integralClosure_pi_algEquiv
    {B C R F T I : Type*} [CommRing B] [CommRing C] [CommRing R]
    [CommRing F] [CommRing T] [Finite I]
    [Algebra B C] [Algebra C T] [Algebra B T] [IsScalarTower B C T]
    [Algebra B R] [Algebra R F] [Algebra B F] [IsScalarTower B R F]
    [IsIntegralClosure R B F] [Module.Finite B R] [Algebra.IsIntegral B C]
    (e : T ≃ₐ[B] (I → F)) :
    ∃ eC : (I → R) ≃ₐ[B] integralClosure C T,
      ∀ x : I → R, (eC x : T) = e.symm (fun i => algebraMap R F (x i)) := by
  let h : (I → R) →ₐ[B] T := e.symm.toAlgHom.comp
    (AlgHom.pi fun i => (IsScalarTower.toAlgHom B R F).comp (Pi.evalAlgHom B (fun _ : I => R) i))
  let hC : (I → R) →ₐ[B] integralClosure C T :=
    h.codRestrict ((integralClosure C T).restrictScalars B)
      (fun x => ((IsIntegral.of_finite B x).map h).tower_top)
  have hinj : Function.Injective hC := by
    intro x y hxy
    have hxy' : h x = h y := congrArg Subtype.val hxy
    have hcoord := e.symm.injective hxy'
    funext i
    exact IsIntegralClosure.algebraMap_injective R B F (congrFun hcoord i)
  have hsurj : Function.Surjective hC := by
    intro x
    have hx : IsIntegral B (x : T) := isIntegral_trans (x : T) x.2
    have hxi (i : I) : IsIntegral B (e (x : T) i) :=
      (hx.map e.toAlgHom).map (Pi.evalAlgHom B (fun _ : I => F) i)
    let y : I → R := fun i => IsIntegralClosure.mk' R (e (x : T) i) (hxi i)
    refine ⟨y, ?_⟩
    apply Subtype.ext
    change e.symm (fun i => algebraMap R F (y i)) = (x : T)
    have hy : (fun i => algebraMap R F (y i)) = e (x : T) := by
      funext i
      exact IsIntegralClosure.algebraMap_mk' R _ _
    rw [hy, e.symm_apply_apply]
  exact ⟨AlgEquiv.ofBijective hC ⟨hinj, hsurj⟩, fun _ => rfl⟩

private theorem ramificationIdx_eq_one_of_map_maximalIdeal
    {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    (hmap : (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S) :
    (IsLocalRing.maximalIdeal S).ramificationIdx R = 1 := by
  have : IsLocalHom (algebraMap R S) := ⟨fun r hr => by
    by_contra hnot
    have hmem := Ideal.mem_map_of_mem (algebraMap R S) (show r ∈ IsLocalRing.maximalIdeal R from
      hnot)
    rw [hmap] at hmem
    exact hmem hr⟩
  have : (IsLocalRing.maximalIdeal S).LiesOver (IsLocalRing.maximalIdeal R) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm⟩
  have : Module.IsTorsionFree R S := Module.isTorsionFree_iff_algebraMap_injective.mpr (by
    apply (injective_iff_map_eq_zero (algebraMap R S)).mpr
    intro r hr
    by_contra h0
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hπ
    have hπmap : algebraMap R S π ≠ 0 := by
      intro hz
      have hm0 : (IsLocalRing.maximalIdeal R).map (algebraMap R S) = ⊥ := by
        rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hz, Ideal.span_singleton_zero]
      exact IsDiscreteValuationRing.not_a_field S (hmap.symm.trans hm0)
    have hnonzero : algebraMap R S r ≠ 0 := by
      rw [hu, map_mul, map_pow]
      exact mul_ne_zero (u.isUnit.map _).ne_zero (pow_ne_zero _ hπmap)
    exact hnonzero hr)
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (IsLocalRing.maximalIdeal R)
    (IsLocalRing.maximalIdeal S) (IsDiscreteValuationRing.not_a_field R), ← hmap]
  exact Ideal.ramificationIdx'_map_self_eq_one
    (by rw [hmap]; exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top)
    (by rw [hmap]; exact IsDiscreteValuationRing.not_a_field S)

theorem exists_isWeakSolution_of_tensor_embedding
    {A B C K L M E : Type u}
    [CommRing A] [CommRing B] [CommRing C] [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M] [Field E] [CharZero K]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra A M] [Algebra B M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower B C M]
    [IsScalarTower B L M] [IsScalarTower A C M]
    [IsScalarTower A K L] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsDiscreteValuationRing.IsExtension A B] [IsDiscreteValuationRing.IsExtension B C]
      [IsDiscreteValuationRing.IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [Module.Finite K E] [Algebra.IsSeparable K E] [Module.Finite L M] [IsGalois L M]
    (z : M) (hz : Algebra.adjoin L {z} = ⊤) (hL : IsField (L ⊗[K] E)) :
    letI := hL.toField
    ∀ (hA : IsDiscreteValuationRing (integralClosure A E))
      (hB : IsDiscreteValuationRing (integralClosure B (L ⊗[K] E)))
      (hfrac : IsFractionRing (integralClosure B (L ⊗[K] E)) (L ⊗[K] E)),
    letI := hA
    letI := hB
    letI := hfrac
    ∀ f' : integralClosure A E →+* integralClosure B (L ⊗[K] E),
      (IsLocalRing.maximalIdeal (integralClosure A E)).map f' =
        IsLocalRing.maximalIdeal (integralClosure B (L ⊗[K] E)) →
      (∀ a : integralClosure A E,
        (f' a : L ⊗[K] E) = (Algebra.TensorProduct.includeRight : E →ₐ[K] L ⊗[K] E) a) →
      (M →ₐ[L] L ⊗[K] E) →
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A C K M E,
        D.IsWeakSolution := by
  classical
  let := hL.toField
  intro hA hB hfrac
  let := hA
  let := hB
  let := hfrac
  intro f' hf' hfsquare φ
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let F := L ⊗[K] E
  let T := M ⊗[K] E
  let A₁ := integralClosure A E
  let B₁ := integralClosure B F
  let C₁ := integralClosure C T
  let I := M ≃ₐ[L] M
  let ι : F →ₐ[K] T :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M) (AlgHom.id K E)
  have hι (l : L) (a : E) : ι (l ⊗ₜ[K] a) = algebraMap L M l ⊗ₜ[K] a :=
    Algebra.TensorProduct.map_tmul (IsScalarTower.toAlgHom K L M) (AlgHom.id K E) l a
  let : Algebra F T := ι.toRingHom.toAlgebra
  have : IsScalarTower K F T := IsScalarTower.of_algHom ι
  have : IsScalarTower B F T := IsScalarTower.of_algebraMap_eq fun b => by
    change algebraMap B M b ⊗ₜ[K] (1 : E) = ι (algebraMap B L b ⊗ₜ[K] (1 : E))
    rw [hι, ← IsScalarTower.algebraMap_apply B L M]
  have : Algebra.IsIntegral B C := by
    let : Algebra M F := φ.toAlgebra
    let : Algebra C F := ((algebraMap M F).comp (algebraMap C M)).toAlgebra
    have : IsScalarTower C M F := IsScalarTower.of_algebraMap_eq' rfl
    have : IsScalarTower B C F := IsScalarTower.of_algebraMap_eq fun b => by
      change algebraMap B L b ⊗ₜ[K] (1 : E) = φ (algebraMap C M (algebraMap B C b))
      rw [← IsScalarTower.algebraMap_apply B C M,
        IsScalarTower.algebraMap_apply B L M, φ.commutes]
      rfl
    exact isIntegral_of_isDiscreteValuationRing_integralClosure (M := M) (E := F)
  have : Module.Finite B B₁ := IsIntegralClosure.finite B L F B₁
  obtain ⟨e, he⟩ := exists_tensorProduct_pi_algEquiv_of_embedding z hz hL φ
  obtain ⟨eC, heC⟩ := exists_integralClosure_pi_algEquiv
    (C := C) (R := B₁) (e.restrictScalars B)
  let g : A₁ →+* C₁ := eC.toRingHom.comp (RingHom.pi fun _ : I => f')
  have hg (a : A₁) : (g a : T) =
      (Algebra.TensorProduct.includeRight : E →ₐ[K] T) a := by
    change (eC (fun _ : I => f' a) : T) = _
    rw [heC]
    change e.symm (fun _ : I => (f' a : F)) = _
    simp_rw [hfsquare a]
    change e.symm (algebraMap F (I → F) (Algebra.TensorProduct.includeRight (a : E))) = _
    rw [e.symm.commutes]
    change ι ((1 : L) ⊗ₜ[K] (a : E)) = (1 : M) ⊗ₜ[K] (a : E)
    rw [hι, map_one]
  let : Algebra A₁ B₁ := f'.toAlgebra
  let : Algebra A₁ C₁ := g.toAlgebra
  let eA : (I → B₁) ≃ₐ[A₁] C₁ :=
    { eC.toRingEquiv with commutes' := fun _ => rfl }
  have hweak : ∀ q : Ideal C₁, q.IsMaximal → q.ramificationIdx A₁ = 1 := by
    intro q hq
    let := hq
    obtain ⟨i, eLocal, _⟩ := Stacks.ProductLocalizations.exists_component_algEquiv_atMaximal
      A₁ C₁ (fun _ : I => B₁) eA.symm q
    rw [SplitFactors.ramificationIdx_eq_of_localComponentEquiv A₁ C₁ B₁ q eLocal]
    exact ramificationIdx_eq_one_of_map_maximalIdeal hf'
  have : IsReduced T := isReduced_of_injective e e.injective
  exact exists_isWeakSolution_of_tensor_closure g hg hweak

theorem nonempty_algHom_of_cyclotomic_tensor_not_isField
    {B K L M E : Type u} [CommRing B] [IsDomain B]
    [Field K] [Field L] [Field M] [Field E]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] [Algebra K E]
    [Algebra B L] [IsFractionRing B L] [Algebra B M] [IsScalarTower B L M]
    [Module.Finite L M]
    (p : ℕ) [Fact p.Prime] (f : CyclotomicRing p ℤ ℚ →+* B) (P : Polynomial B)
    (hP : intProp f P) (hw : wElt f ≠ 0) (hdeg : Module.finrank L M = p)
    (ξ : L) (z : M) (hz : Algebra.adjoin L {z} = ⊤)
    (hPz : Polynomial.aeval z P = algebraMap L M ξ)
    (hL : IsField (L ⊗[K] E)) (hM : ¬IsField (M ⊗[K] E)) :
    letI := hL.toField
    Nonempty (M →ₐ[L] L ⊗[K] E) := by
  let := hL.toField
  let w := algebraMap B L (wElt f)
  let α := 1 + algebraMap B M (wElt f) * z
  let a := 1 + w ^ p * ξ
  have hw' : w ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hw
  have hαgen : Algebra.adjoin L {α} = ⊤ := by
    simpa only [α, w, map_one, ← IsScalarTower.algebraMap_apply B L M, add_comm]
      using adjoin_affine_eq_top w 1 hw' z hz
  have hα : α ^ p = algebraMap L M a := by
    have h := congrArg (Polynomial.aeval z) hP.1
    simp only [map_mul, map_pow, map_sub, map_add, map_one, Polynomial.aeval_C,
      Polynomial.aeval_X, hPz] at h
    dsimp [α, a, w]
    simp only [map_add, map_one, map_mul, map_pow, ← IsScalarTower.algebraMap_apply B L M]
    linear_combination -h
  let pres := PrimeKummer.presentationOfGenerator L M p (Fact.out : p.Prime).pos
    a α hα hαgen hdeg
  have hsmall : ¬IsField (M ⊗[L] (L ⊗[K] E)) :=
    fun hfield ↦ hM (MulEquiv.isField hfield
      (Algebra.TensorProduct.cancelBaseChange K L M M E).symm.toMulEquiv)
  exact PrimeKummer.nonempty_algHom_of_tensor_not_isField L (L ⊗[K] E) M p
    (Fact.out : p.Prime) a pres hsmall

theorem isExtension_integralClosure
    {R E : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field E] [Algebra R E] [IsDiscreteValuationRing (integralClosure R E)]
    (hinj : Function.Injective (algebraMap R E)) :
    IsDiscreteValuationRing.IsExtension R (integralClosure R E) := by
  let : FaithfulSMul R (integralClosure R E) :=
    (faithfulSMul_iff_algebraMap_injective R (integralClosure R E)).mpr
      (fun _ _ h => hinj (congrArg Subtype.val h))
  let : Algebra.IsIntegral R (integralClosure R E) := IsIntegralClosure.isIntegral_algebra R E
  exact {}

theorem irreducible_root_of_totallyRamified
    {A K E : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field E] [Algebra A K] [IsFractionRing A K]
    [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [Module.Finite K E] [Algebra.IsSeparable K E]
    [IsDiscreteValuationRing (integralClosure A E)]
    (htot : IsDiscreteValuationRing.IsTotallyRamifiedWithRespectTo A K E)
    (q : ℕ) (hq : 0 < q) (hd : Module.finrank K E = q)
    (π : A) (hπ : Irreducible π) (t : E) (ht : t ^ q = algebraMap A E π)
    (hint : IsIntegral A t) : Irreducible (⟨t, hint⟩ : integralClosure A E) := by
  let R := integralClosure A E
  have hinj : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A K E]
    exact (algebraMap K E).injective.comp (IsFractionRing.injective A K)
  let : IsDiscreteValuationRing.IsExtension A R := isExtension_integralClosure hinj
  have : Module.IsTorsionFree A R := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (FaithfulSMul.algebraMap_injective A R)
  have : (IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A R)).symm⟩
  have heq : IsDiscreteValuationRing.ramificationIndex A R = q :=
    (IsDiscreteValuationRing.ramificationIdx_eq_finrank_of_totallyRamified A K E htot
      (IsLocalRing.maximalIdeal R) inferInstance inferInstance).trans hd
  exact irreducible_of_pow_eq_uniformizer_of_ramificationIndex A R π hπ ⟨t, hint⟩ q hq
    (Subtype.ext ht) heq

/-- **The four cyclotomic hypotheses on `(f, P)` are carried along any ring map.**

`intProp`, `quotChar`, `shapeProp` and `funcEq` all transport from `(f, P)` over `A` to
`(q.comp f, P.map q)` over `B`, for an arbitrary `q : A →+* B`. -/
theorem cyclotomic_properties_map
    {A B : Type*} [CommRing A] [CommRing B] {p : ℕ} [Fact p.Prime]
    (f : CyclotomicRing p ℤ ℚ →+* A) (P : Polynomial A)
    (hP : intProp f P ∧ quotChar f P ∧ shapeProp f P ∧ funcEq f P)
    (q : A →+* B) :
    intProp (q.comp f) (P.map q) ∧ quotChar (q.comp f) (P.map q) ∧
      shapeProp (q.comp f) (P.map q) ∧ funcEq (q.comp f) (P.map q) := by
  have hint := intProp_map f P hP.1 q
  refine ⟨hint, ?_, ?_, ?_⟩
  · have h := congrArg (Polynomial.map (algebraMap B (Localization.Away (wElt (q.comp f))))) hint.1
    simpa only [quotChar, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_add, Polynomial.map_one, Polynomial.map_C, Polynomial.map_X] using h
  · obtain ⟨a, ha, heq⟩ := hP.2.2.1
    refine ⟨fun i => q (a i), ?_, ?_⟩
    · intro i hi hip
      rw [wElt_comp, Ideal.mem_span_singleton]
      exact map_dvd q (Ideal.mem_span_singleton.mp (ha i hi hip))
    · rw [heq]
      simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
  · let : Algebra A B := q.toAlgebra
    let R := MvPolynomial (Fin 2) B
    have h := aeval_cyclotomic_add f P hP.2.2.2
      (MvPolynomial.X 0 : R) (MvPolynomial.X 1 : R)
    change funcEq ((algebraMap A B).comp f) (P.map (algebraMap A B))
    simpa only [funcEq, wElt_comp, Polynomial.aeval_map_algebraMap, map_pow,
      ← IsScalarTower.algebraMap_apply A B (MvPolynomial (Fin 2) B)] using h

private theorem ramificationIdx_eq_one_atMaximal_of_map_maximalIdeal
    {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (f : R →+* S)
    (hf : (IsLocalRing.maximalIdeal R).map f = IsLocalRing.maximalIdeal S) :
    letI := f.toAlgebra
    ∀ q : Ideal S, q.IsMaximal → q.ramificationIdx R = 1 := by
  let := f.toAlgebra
  intro q hq
  rw [IsLocalRing.eq_maximalIdeal hq]
  exact ramificationIdx_eq_one_of_map_maximalIdeal (R := R) (S := S) hf

theorem exists_isWeakSolution_of_unramified_normalization
    {A B C K L M E : Type u}
    [CommRing A] [CommRing B] [CommRing C] [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M] [Field E] [CharZero K]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra A M] [Algebra B M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower B C M]
    [IsScalarTower B L M] [IsScalarTower A C M]
    [IsScalarTower A K L] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsDiscreteValuationRing.IsExtension A B] [IsDiscreteValuationRing.IsExtension B C]
      [IsDiscreteValuationRing.IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [Module.Finite K E] [Algebra.IsSeparable K E] [Module.Finite L M]
    (z : M) (hz : Algebra.adjoin L {z} = ⊤)
    (hL : IsField (L ⊗[K] E)) (hM : IsField (M ⊗[K] E)) :
    letI := hL.toField
    letI := hM.toField
    let ι : L ⊗[K] E →ₐ[K] M ⊗[K] E :=
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M) (AlgHom.id K E)
    letI : Algebra (L ⊗[K] E) (M ⊗[K] E) := ι.toRingHom.toAlgebra
    let A₁ := integralClosure A E
    let B₁ := integralClosure B (L ⊗[K] E)
    ∀ (hA : IsDiscreteValuationRing A₁) (hB : IsDiscreteValuationRing B₁)
      (hfrac : IsFractionRing B₁ (L ⊗[K] E)),
    letI := hA
    letI := hB
    letI := hfrac
    ∀ f' : A₁ →+* B₁,
      (IsLocalRing.maximalIdeal A₁).map f' = IsLocalRing.maximalIdeal B₁ →
      (∀ a : A₁, (f' a : L ⊗[K] E) =
        (Algebra.TensorProduct.includeRight : E →ₐ[K] L ⊗[K] E) a) →
      let R := integralClosure B₁ (M ⊗[K] E)
      ∀ hR : IsDiscreteValuationRing R,
      letI : IsLocalRing R := hR.toIsLocalRing
      (IsLocalRing.maximalIdeal B₁).map (algebraMap B₁ R) =
        IsLocalRing.maximalIdeal R →
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A C K M E,
        D.IsWeakSolution := by
  classical
  let := hL.toField
  let := hM.toField
  intro ι
  let : Algebra (L ⊗[K] E) (M ⊗[K] E) := ι.toRingHom.toAlgebra
  intro A₁ B₁ hA hB hfrac
  let : CommRing A₁ := inferInstance
  let : CommRing B₁ := inferInstance
  let := hA
  let := hB
  let := hfrac
  intro f' hf' hfsquare R hR
  let : CommRing R := inferInstance
  let := hR
  let : IsLocalRing R := hR.toIsLocalRing
  intro hBR
  let F := L ⊗[K] E
  let T := M ⊗[K] E
  let C₁ := integralClosure C T
  let : CommRing C₁ := inferInstance
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have hι (l : L) (a : E) : ι (l ⊗ₜ[K] a) = algebraMap L M l ⊗ₜ[K] a :=
    Algebra.TensorProduct.map_tmul (IsScalarTower.toAlgHom K L M) (AlgHom.id K E) l a
  have : IsScalarTower L F T := IsScalarTower.of_algebraMap_eq fun l => by
    change algebraMap L M l ⊗ₜ[K] (1 : E) = ι (l ⊗ₜ[K] (1 : E))
    exact (hι l 1).symm
  have : IsScalarTower B F T := IsScalarTower.of_algebraMap_eq fun b => by
    rw [IsScalarTower.algebraMap_apply B L T, IsScalarTower.algebraMap_apply L F T,
      ← IsScalarTower.algebraMap_apply B L F]
  obtain ⟨hfin, _, _⟩ := finite_finrank_adjoin_tensorProduct_of_isField hL z hz
  let := hfin
  have : Module.Finite L T := Module.Finite.trans F T
  have : Algebra.IsIntegral B B₁ := IsIntegralClosure.isIntegral_algebra B F
  let eR : R ≃+* integralClosure B T :=
    (Stacks.DiscreteValuationRing.AdjoinPthRoot.integralClosureEquivOfIsIntegral (R := B) (S := B₁)
      (T := T)).toRingEquiv
  let : IsDiscreteValuationRing (integralClosure B T) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eR
  let : IsFractionRing (integralClosure B T) T :=
    IsIntegralClosure.isFractionRing_of_finite_extension B L T (integralClosure B T)
  let : Algebra.IsIntegral B C :=
    isIntegral_of_isDiscreteValuationRing_integralClosure (M := M) (E := T)
  let eC : R ≃+* C₁ := eR.trans
    (Stacks.DiscreteValuationRing.AdjoinPthRoot.integralClosureEquivOfIsIntegral (R := B) (S := C)
      (T := T)).toRingEquiv.symm
  let : IsDiscreteValuationRing C₁ :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eC
  let g : A₁ →+* C₁ := eC.toRingHom.comp ((algebraMap B₁ R).comp f')
  have hg (a : A₁) : (g a : T) =
      (Algebra.TensorProduct.includeRight : E →ₐ[K] T) a := by
    change algebraMap F T (f' a : F) = _
    rw [hfsquare a]
    change ι ((1 : L) ⊗ₜ[K] (a : E)) = (1 : M) ⊗ₜ[K] (a : E)
    rw [hι, map_one]
  have hmapR : (IsLocalRing.maximalIdeal A₁).map ((algebraMap B₁ R).comp f') =
      IsLocalRing.maximalIdeal R := by
    rw [← Ideal.map_map, hf', hBR]
  have hmap := IsDiscreteValuationRing.map_maximalIdeal_comp_ringEquiv
    ((algebraMap B₁ R).comp f') eC hmapR
  have hweak := ramificationIdx_eq_one_atMaximal_of_map_maximalIdeal
    (R := A₁) (S := C₁) g hmap
  exact exists_isWeakSolution_of_tensor_closure (A := A) (C := C) (K := K) (M := M) (E := E) g hg
    hweak

theorem exists_scaled_laurent_parameter
    {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (π : A) (hπ : algebraMap A K π ≠ 0) (P : Polynomial A)
    (n m k : ℕ) (hm : m ≤ n) (hkd : P.natDegree ≤ k) (hk : n - m ≤ k)
    (ξ : K) (b : A)
    (hξ : algebraMap A K π ^ n * (ξ - Polynomial.aeval (algebraMap A K π)⁻¹ P) =
      algebraMap A K (π ^ m * b)) :
    ∃ a : A, algebraMap A K a = algebraMap A K π ^ k * ξ ∧
      a = π ^ (k - P.natDegree) * (P.scaleRoots π).eval 1 + π ^ (k - (n - m)) * b := by
  obtain ⟨a₀, ha₀⟩ := exists_mul_pow_aeval_inv_eq π hπ P k hkd
  let a := π ^ (k - P.natDegree) * (P.scaleRoots π).eval 1 + π ^ (k - (n - m)) * b
  refine ⟨a, ?_, rfl⟩
  have hcalc : algebraMap A K (π ^ (k - P.natDegree) * (P.scaleRoots π).eval 1) =
      algebraMap A K π ^ k * Polynomial.aeval (algebraMap A K π)⁻¹ P := by
    rw [map_mul, map_eval_scaleRoots_inv_mul P π 1 hπ, map_one, mul_one,
      map_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hkd]
  apply mul_left_cancel₀ (pow_ne_zero n hπ)
  dsimp only [a]
  rw [map_add, hcalc, map_mul, map_pow, mul_add]
  have hexp : n + (k - (n - m)) = k + m := by omega
  have hb : algebraMap A K π ^ n * (algebraMap A K π ^ (k - (n - m)) * algebraMap A K b) =
      algebraMap A K π ^ k * algebraMap A K (π ^ m * b) := by
    rw [← mul_assoc, ← pow_add, hexp, pow_add, map_mul, map_pow]
    ring
  rw [hb, ← hξ]
  ring

theorem residue_eval_scaleRoots_one
    {A : Type*} [CommRing A] [IsLocalRing A] (P : Polynomial A) (π : A)
    (hπ : IsLocalRing.residue A π = 0)
    (hlc : IsLocalRing.residue A P.leadingCoeff ≠ 0) :
    IsLocalRing.residue A ((P.scaleRoots π).eval 1) = IsLocalRing.residue A P.leadingCoeff := by
  rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map,
    Polynomial.map_scaleRoots P π (IsLocalRing.residue A) hlc, hπ,
    Polynomial.scaleRoots_zero]
  simp [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hlc]

/-- The successful output of one positive mixed-characteristic level step: a finite separable
totally ramified base extension which either already solves the tower or carries the finite-level
presentation at the prescribed smaller bound. -/
abbrev MixedLevelStepOutcome
    (A B C K L M : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra A M] [Algebra B M]
    [IsScalarTower A B C] [IsScalarTower A B L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K L]
    [IsScalarTower A K M] [IsScalarTower K L M]
    [IsDiscreteValuationRing.IsExtension A B] [IsDiscreteValuationRing.IsExtension B C]
    [IsDiscreteValuationRing.IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    (p : ℕ) [Fact p.Prime]
    (f : CyclotomicRing p ℤ ℚ →+* B) (P : Polynomial B) (l : ℚ) : Prop :=
  ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
    (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁)
    (_ : Algebra.IsSeparable K K₁),
    IsDiscreteValuationRing.IsTotallyRamifiedWithRespectTo A K K₁ ∧
      ((∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u, u, u, u, u, u, u, u}
          A C K M K₁, D.IsWeakSolution) ∨
        let L₁ := L ⊗[K] K₁
        let M₁ := M ⊗[K] K₁
        ∃ (hL₁ : IsField L₁) (hM₁ : IsField M₁),
          letI := hL₁.toField
          letI := hM₁.toField
          let ι : L₁ →ₐ[K] M₁ :=
            Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M) (AlgHom.id K K₁)
          letI : Algebra L₁ M₁ := ι.toRingHom.toAlgebra
          let B₁ := integralClosure B L₁
          ∃ (hB₁ : IsDiscreteValuationRing B₁) (hfrac : IsFractionRing B₁ L₁)
            (hfin : Module.Finite L₁ M₁),
            letI := hB₁
            letI := hfrac
            letI := hfin
            let f₁ := (algebraMap B B₁).comp f
            let P₁ := P.map (algebraMap B B₁)
            Stacks.DegreePExtensionLevel.IsDegreePExtensionOfFiniteLevel B₁ L₁ M₁ p f₁ P₁ ∧
              ∃ (π₁ : B₁) (e₁ : ℕ) (he₁ : 0 < e₁)
                (hne : (Stacks.DegreePExtensionLevel.extensionLevelNumerators B₁ L₁ M₁ P₁
                  π₁).Nonempty),
                Irreducible π₁ ∧ Associated (wElt f₁) (π₁ ^ e₁) ∧
                  Stacks.DegreePExtensionLevel.extensionLevel B₁ L₁ M₁ P₁ π₁ e₁ he₁ hne ≤
                    max 0 (max (l - 1) (2 * l - (p : ℚ))))

/-- Re-entry data for the finite-support branch of a mixed-characteristic level step.  Once the
displayed finite residue support has been absorbed by any compatible weakly-unramified base
inside `B`, the *same prepared polynomial* completes the level step over that base. -/
abbrev MixedLevelStepReentry
    (B C L M : Type u)
    [CommRing B] [CommRing C] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    [Field L] [Field M]
    [Algebra B C] [Algebra B L] [Algebra C M] [Algebra L M] [Algebra B M]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsDiscreteValuationRing.IsExtension B C]
    [IsFractionRing B L] [IsFractionRing C M]
    (p : ℕ) [Fact p.Prime]
    (f : CyclotomicRing p ℤ ℚ →+* B) (P : Polynomial B) (l : ℚ)
    (π : B) (s : Finset (IsLocalRing.ResidueField B)) : Prop :=
  ∀ (A K : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
    [Algebra A B] [Algebra A C] [Algebra A K] [Algebra K L] [Algebra K M]
    [Algebra A L] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A C M]
    [IsScalarTower A K L] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsDiscreteValuationRing.IsExtension A B]
    [IsDiscreteValuationRing.IsExtension A C] [IsFractionRing A K]
    [CharZero K] [CharP (IsLocalRing.ResidueField A) p]
    [PerfectField (IsLocalRing.ResidueField A)],
    IsDiscreteValuationRing.IsWeaklyUnramified A B →
      ∀ (πA : A), Irreducible πA → algebraMap A B πA = π →
        (∀ x ∈ s, x ∈ (algebraMap (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField B)).fieldRange) →
          MixedLevelStepOutcome A B C K L M p f P l

/-- **The prepared data retained by the finite-support branch of the mixed level step.**

It asserts that `pi` is a uniformizer with `wElt f` associated to `pi ^ e` and `l` the level, and
provides a generator `z` with parameter `xi`, the least admissible numerator `n` and a decrement
`m` with their bounds, a polynomial `H` over `B` whose image in `B ⧸ 𝔪 ^ m` is the image of a
residue polynomial `H0` under a section `sigma0` of the reduction `r0`, with `s` the set of
coefficients of `H0` and these lying in the perfect core, and the scaled parameter relation. -/
abbrev MixedLevelPreparation
    (B L M : Type u)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field L] [Field M] [Algebra B L] [Algebra L M] [Algebra B M]
    [IsScalarTower B L M] [IsFractionRing B L]
    (p : ℕ) [Fact p.Prime]
    [ExpChar (IsLocalRing.ResidueField B) p]
    (f : CyclotomicRing p ℤ ℚ →+* B) (P : Polynomial B)
    (l : ℚ) (pi : B) (s : Finset (IsLocalRing.ResidueField B)) : Prop :=
  ∃ (e : ℕ) (he : 0 < e)
      (hne : (Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P pi).Nonempty),
    Irreducible pi ∧ Associated (wElt f) (pi ^ e) ∧
      l = Stacks.DegreePExtensionLevel.extensionLevel B L M P pi e he hne ∧
      ∃ (n m : ℕ) (xi : L) (z : M) (H : Polynomial B)
        (H0 : Polynomial (IsLocalRing.ResidueField B))
        (sigma0 : IsLocalRing.ResidueField B →+*
          B ⧸ IsLocalRing.maximalIdeal B ^ m)
        (r0 : (B ⧸ IsLocalRing.maximalIdeal B ^ m) →+*
          IsLocalRing.ResidueField B),
        n = sInf (Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P pi) ∧
        n ∈ Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P pi ∧
        (∀ k, k ∈ Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P pi → n ≤ k) ∧
        0 < n ∧ n < p * e ∧
        m = min n (min e (p * e - n)) ∧ 0 < m ∧ m ≤ n ∧ m ≤ e ∧
        n + m ≤ p * e ∧
        (p : B) ∈ IsLocalRing.maximalIdeal B ^ m ∧
        ((n - m : ℕ) : ℚ) / e = max 0 (max (l - 1) (2 * l - (p : ℚ))) ∧
        Algebra.adjoin L {z} = ⊤ ∧ Polynomial.aeval z P = algebraMap L M xi ∧
        H.natDegree ≤ n ∧ H0.natDegree ≤ n ∧
        H.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B ^ m)) =
          H0.map sigma0 ∧
        (∀ x, r0 (sigma0 x) = x) ∧
        (∀ b, r0 (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B ^ m) b) =
          IsLocalRing.residue B b) ∧
        s = @Finset.image ℕ (IsLocalRing.ResidueField B) (Classical.decEq _)
          (fun i => H0.coeff i) H0.support ∧
        (∀ i, H0.coeff i ∈ perfectCore (IsLocalRing.ResidueField B) p) ∧
        ∃ b : B, algebraMap B L pi ^ n *
            (xi - Polynomial.aeval (algebraMap B L pi)⁻¹ H) =
          algebraMap B L (pi ^ m * b)

/-- A weakly unramified extension of discrete valuation rings maps the maximal ideal onto the
maximal ideal. -/
private theorem map_maximalIdeal_eq_of_isWeaklyUnramified
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [IsDiscreteValuationRing.IsExtension A B]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B) :
    (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B := by
  simpa only [show IsDiscreteValuationRing.ramificationIndex A B = 1 from hweak, pow_one] using
    (IsDiscreteValuationRing.ramificationIndex_characterization A B).2.1

/-- **The factor-stable endgame of the positive mixed-characteristic level step.**

If `n` is the least admissible numerator and `piA ^ n * xi = aA + pi ^ m * bA` in `L`, then
`MixedLevelStepOutcome` holds: a totally ramified base extension either gives a weak solution or
lowers the finite level by the prescribed amount. -/
theorem mixedLevelStepOutcome_of_scaled_parameter_eq
    (A B C K L M : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra A M] [Algebra B M]
    [IsScalarTower A B C] [IsScalarTower A B L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K L]
    [IsScalarTower A K M] [IsScalarTower K L M]
    [IsDiscreteValuationRing.IsExtension A B] [IsDiscreteValuationRing.IsExtension B C]
    [IsDiscreteValuationRing.IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    (p : ℕ) [Fact p.Prime] [CharZero K]
    [CharP (IsLocalRing.ResidueField A) p]
    [ExpChar (IsLocalRing.ResidueField B) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    (piA : A) (hpiA : Irreducible piA) (pi : B) (hpi : Irreducible pi)
    (hpieq : algebraMap A B piA = pi)
    (f : CyclotomicRing p ℤ ℚ →+* B) (P : Polynomial B)
    (hP : intProp f P ∧ quotChar f P ∧ shapeProp f P ∧ funcEq f P)
    [Module.Finite L M]
    (hfinite : Stacks.DegreePExtensionLevel.IsDegreePExtensionOfFiniteLevel B L M p f P)
    (l : ℚ) (e : ℕ) (he : 0 < e) (n : ℕ)
    (_hne : (Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P pi).Nonempty)
    (hnmem : n ∈ Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P pi)
    (hnleast : ∀ k, k ∈ Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P pi → n ≤ k)
    (hnpos : 0 < n) (hnbound : n < p * e)
    (m : ℕ) (hmpos : 0 < m) (hmle : m ≤ n) (hme : m ≤ e)
    (hnm : n + m ≤ p * e)
    (hbound : ((n - m : ℕ) : ℚ) / e = max 0 (max (l - 1) (2 * l - (p : ℚ))))
    (hw : Associated (wElt f) (pi ^ e))
    (xi : L) (z : M) (hz : Algebra.adjoin L {z} = ⊤)
    (hPz : Polynomial.aeval z P = algebraMap L M xi)
    (aA : A) (bA : B)
    (haA : algebraMap A L piA ^ n * xi =
      algebraMap A L aA + algebraMap B L (pi ^ m * bA)) :
    MixedLevelStepOutcome A B C K L M p f P l := by
  have hmapmax := map_maximalIdeal_eq_of_isWeaklyUnramified A B hweak
  let rho := algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)
  let : CharP (IsLocalRing.ResidueField B) p :=
    CharP.of_ringHom_of_ne_zero rho p (Fact.out : p.Prime).ne_zero
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  obtain ⟨_hfinGal, hgal, _⟩ :=
    isGalois_and_ramification_cases_of_adjoin_root_cyclotomic_quotient B L M p f P hP
      xi z (by
        simpa only [Polynomial.aeval_def, IsScalarTower.algebraMap_eq B L M] using hPz)
      hz pi hpi
  let : IsGalois L M := hgal
  have hwne : wElt f ≠ 0 := hw.ne_zero_iff.mpr (pow_ne_zero _ hpi.ne_zero)
  let a' : B := algebraMap A B aA + pi ^ m * bA
  have ha' : algebraMap B L a' = algebraMap B L (pi ^ n) * xi := by
    simpa only [a', map_add, map_mul, map_pow, IsScalarTower.algebraMap_apply A B L,
      hpieq] using haA.symm
  have hau' : IsUnit a' := isUnit_of_isLeast_extensionLevelNumerator
    P pi hpi n hnpos ⟨hnmem, hnleast⟩ xi z a' hz
    (by simpa only [Polynomial.aeval_def, IsScalarTower.algebraMap_eq B L M] using hPz) ha'
  have hres' : IsLocalRing.residue B a' = rho (IsLocalRing.residue A aA) := by
    have hpires : IsLocalRing.residue B pi = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, hpi.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self pi
    dsimp only [a']
    rw [map_add, map_mul, map_pow, hpires, zero_pow hmpos.ne', zero_mul, add_zero,
      ← IsLocalRing.ResidueField.map_residue]
    rfl
  have haAu : IsUnit aA := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    intro hzA
    have hzB := (IsLocalRing.residue_ne_zero_iff_isUnit a').mpr hau'
    exact hzB (by rw [hres', hzA, map_zero])
  have hpn : ¬p ∣ n := by
    intro hpdiv
    apply not_isPow_residue_of_isLeast_extensionLevelNumerator
      p f P hP.1 hP.2.2.2 pi hpi e n hw hnpos hnbound
      ⟨hnmem, hnleast⟩ hpdiv xi z a' hz hPz
      (by simpa only [map_pow] using ha')
    obtain ⟨c, hc⟩ :=
      (PerfectRing.bijective_frobenius (R := IsLocalRing.ResidueField A) (p := p)).2
        (IsLocalRing.residue A aA)
    refine ⟨rho c, ?_⟩
    rw [hres', ← map_pow]
    exact congrArg rho hc.symm
  obtain ⟨K1, hK1, hKK1, hAK1, htower, hfinK1, hsepK1, htot, _hdeg,
      y, _hygen, hy⟩ :=
    exists_totallyRamified_root_pow_sub A K p (Fact.out : p.Prime).one_lt piA (-aA)
      hpiA haAu.neg n hnpos ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpn)
  refine ⟨K1, hK1, hKK1, hAK1, htower, hfinK1, hsepK1, htot, ?_⟩
  obtain ⟨hL1, hA1, _hBdom, _hB1, _hinj, _hmap, _hCdom, hC1, hfrac,
      eB, heB, _hinj', hmap'⟩ :=
    IsDiscreteValuationRing.isField_tensorProduct_and_isDVR_baseChange_of_totallyRamified
      A B K L K1 hmapmax htot
  by_cases hM1 : IsField (M ⊗[K] K1)
  · right
    let := hL1.toField
    let := hM1.toField
    have hxiA : algebraMap B L pi ^ n * xi - algebraMap B L (algebraMap A B aA) =
        algebraMap B L pi ^ m * algebraMap B L bA := by
      have haA' := haA
      simp only [map_mul, map_pow, IsScalarTower.algebraMap_apply A B L, hpieq] at haA'
      linear_combination haA'
    have hyT := artinSchreier_eq_tensor_includeRight piA aA
      ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hpiA.ne_zero)
      n p y hy hL1
    have hyB : algebraMap B (L ⊗[K] K1) pi ^ n *
        (((1 : L) ⊗ₜ[K] y) ^ p - (1 : L) ⊗ₜ[K] y) =
          -algebraMap B (L ⊗[K] K1) (algebraMap A B aA) := by
      rw [← hpieq]
      simpa only [← IsScalarTower.algebraMap_apply A B (L ⊗[K] K1)] using hyT
    obtain ⟨hfin, hfl, pi1, e1, he1, hne1, hpi1, hw1, hle⟩ :=
      finiteLevel_tensorProduct_of_artinSchreier_shift p f P hP hfinite.1 pi hpi e n m
        he hw hnbound hme hmle hnm z hz xi hPz (algebraMap A B aA) bA hxiA
        hL1 hM1 hC1 hfrac (1 ⊗ₜ[K] y) hyB
    exact ⟨hL1, hM1, hC1, hfrac, hfin, hfl, pi1, e1, he1, hne1, hpi1, hw1,
      hle.trans_eq hbound⟩
  · left
    let := hL1.toField
    obtain ⟨phi⟩ := nonempty_algHom_of_cyclotomic_tensor_not_isField p f P hP.1 hwne
      hfinite.1 xi z hz hPz hL1 hM1
    exact exists_isWeakSolution_of_tensor_embedding (A := A) (B := B) (C := C) z hz
      hL1 hA1 hC1 hfrac (eB.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
      hmap' heB phi

/-- **A mapped mixed preparation either performs the level step or reveals a smaller least
numerator.**

Either `MixedLevelStepOutcome` holds, or the set of admissible numerators for the mapped
uniformizer is nonempty with infimum strictly less than `n`. -/
theorem mixedLevelStepOutcome_or_numerator_lt_of_mapped_preparation
    (A B0 B C K L M : Type u)
    [CommRing A] [CommRing B0] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B0] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B0]
    [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra B0 B]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra A M] [Algebra B M]
    [IsScalarTower A B C] [IsScalarTower A B L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K L]
    [IsScalarTower A K M] [IsScalarTower K L M]
    [IsDiscreteValuationRing.IsExtension B0 B]
    [IsDiscreteValuationRing.IsExtension A B]
    [IsDiscreteValuationRing.IsExtension B C]
    [IsDiscreteValuationRing.IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    (p : ℕ) [Fact p.Prime] [CharZero K]
    [CharP (IsLocalRing.ResidueField A) p]
    [ExpChar (IsLocalRing.ResidueField B0) p]
    [ExpChar (IsLocalRing.ResidueField B) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    (hweak0 : IsDiscreteValuationRing.IsWeaklyUnramified B0 B)
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    (piA : A) (hpiA : Irreducible piA) (pi0 : B0)
    (hpieq : algebraMap B0 B pi0 = algebraMap A B piA)
    (f : CyclotomicRing p ℤ ℚ →+* B) (P : Polynomial B)
    (hP : intProp f P ∧ quotChar f P ∧ shapeProp f P ∧ funcEq f P)
    [Module.Finite L M]
    (hfinite : Stacks.DegreePExtensionLevel.IsDegreePExtensionOfFiniteLevel B L M p f P)
    (l : ℚ) (e : ℕ) (he : 0 < e) (n m : ℕ)
    (hnpos : 0 < n) (hnbound : n < p * e)
    (hmpos : 0 < m) (hmle : m ≤ n) (hme : m ≤ e)
    (hnm : n + m ≤ p * e)
    (hpm0 : (p : B0) ∈ IsLocalRing.maximalIdeal B0 ^ m)
    (hbound : ((n - m : ℕ) : ℚ) / e =
      max 0 (max (l - 1) (2 * l - (p : ℚ))))
    (hw : Associated (wElt f) ((algebraMap B0 B pi0) ^ e))
    (xi : L) (z : M) (hz : Algebra.adjoin L {z} = ⊤)
    (hPz : Polynomial.aeval z P = algebraMap L M xi)
    (H : Polynomial B0) (H0 : Polynomial (IsLocalRing.ResidueField B0))
    (sigma0 : IsLocalRing.ResidueField B0 →+*
      B0 ⧸ IsLocalRing.maximalIdeal B0 ^ m)
    (r0 : (B0 ⧸ IsLocalRing.maximalIdeal B0 ^ m) →+*
      IsLocalRing.ResidueField B0)
    (hr0sigma : ∀ x, r0 (sigma0 x) = x)
    (hr0q : ∀ b, r0 (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B0 ^ m) b) =
      IsLocalRing.residue B0 b)
    (hH : H.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B0 ^ m)) =
      H0.map sigma0)
    (hHd : H.natDegree ≤ n)
    (hcore : ∀ i, H0.coeff i ∈ perfectCore (IsLocalRing.ResidueField B0) p)
    (habs : ∀ x ∈ @Finset.image ℕ (IsLocalRing.ResidueField B0) (Classical.decEq _)
      (fun i => H0.coeff i) H0.support,
      IsLocalRing.ResidueField.map (algebraMap B0 B) x ∈
        (algebraMap (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField B)).fieldRange)
    (hxi : ∃ b : B, algebraMap B L (algebraMap B0 B pi0) ^ n *
        (xi - Polynomial.aeval (algebraMap B L (algebraMap B0 B pi0))⁻¹
          (H.map (algebraMap B0 B))) =
      algebraMap B L ((algebraMap B0 B pi0) ^ m * b)) :
    MixedLevelStepOutcome A B C K L M p f P l ∨
      ∃ _hne : (Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P
        (algebraMap B0 B pi0)).Nonempty,
        sInf (Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P
          (algebraMap B0 B pi0)) < n := by
  classical
  have hpimap : Irreducible (algebraMap B0 B pi0) := by
    rw [hpieq]
    apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    rw [← map_maximalIdeal_eq_of_isWeaklyUnramified A B hweak, hpiA.maximalIdeal_eq,
      Ideal.map_span, Set.image_singleton]
  obtain ⟨aA, bB, ha⟩ := exists_scaled_parameter_eq_of_mapped_dvr_preparation
    A B0 B L p hweak0 hweak piA hpiA m n hmpos hpm0 H H0 sigma0 r0
      hr0sigma hr0q hH hHd hcore habs xi (by simpa only [hpieq] using hxi)
  let aB : B := algebraMap A B aA + (algebraMap B0 B pi0) ^ m * bB
  have haB : algebraMap B L aB = algebraMap B L ((algebraMap B0 B pi0) ^ n) * xi := by
    simpa only [aB, map_add, map_mul, map_pow, IsScalarTower.algebraMap_apply A B L,
      hpieq] using ha.symm
  have hnmem : n ∈ Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P
      (algebraMap B0 B pi0) := by
    refine ⟨xi, z, hz, ?_, aB, haB⟩
    simpa only [Polynomial.aeval_def, IsScalarTower.algebraMap_eq B L M] using hPz
  let hne : (Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P
      (algebraMap B0 B pi0)).Nonempty := ⟨n, hnmem⟩
  let n0 := sInf (Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P
    (algebraMap B0 B pi0))
  have hn0le : n0 ≤ n := Nat.sInf_le hnmem
  rcases eq_or_lt_of_le hn0le with hn0eq | hn0lt
  · left
    apply mixedLevelStepOutcome_of_scaled_parameter_eq
      A B C K L M p hweak piA hpiA (algebraMap B0 B pi0) hpimap hpieq.symm
      f P hP hfinite l e he n hne hnmem
      (fun k hk => hn0eq ▸ Nat.sInf_le hk) hnpos hnbound m hmpos hmle hme hnm
      hbound hw xi z hz hPz aA bB
    simpa only [hpieq] using ha
  · exact Or.inr ⟨hne, hn0lt⟩

end Stacks.DiscreteValuationRing.EppLevelInduction
