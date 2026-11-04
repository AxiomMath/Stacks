module

public import StacksFrontier.RingTheory.DiscreteValuationRing.SeparableSolution.AdjoinRootOrders

/-!
# Finite base change and linear perturbation for solutions

Finiteness of the integral closures of a base change of a solution, and compatible
finite extensions obtained from a linear perturbation of a polynomial modulo a power of
the uniformiser.
-/

@[expose] public section

namespace IsDiscreteValuationRing

open Polynomial IntermediateField
open scoped TensorProduct

private theorem finite_integralClosure_of_finite_tensor_integralClosure
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]
    [IsExtension A B] [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L] [Algebra A L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (K₁ : Type*) [Field K₁] [Algebra A K₁] [Algebra K K₁] [IsScalarTower A K K₁]
    [FiniteDimensional K K₁]
    (hfinite :
      letI : Algebra L (K₁ ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
      letI : Algebra B (K₁ ⊗[K] L) := ((algebraMap L (K₁ ⊗[K] L)).comp (algebraMap B L)).toAlgebra
      Module.Finite B (integralClosure B (K₁ ⊗[K] L))) :
    Module.Finite A (integralClosure A K₁) := by
  let : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let T := K₁ ⊗[K] L
  let ψ₀ : B ⊗[A] K →ₐ[B] L :=
    Algebra.TensorProduct.lift (Algebra.ofId B L) (IsScalarTower.toAlgHom A K L)
      fun _ _ => Commute.all _ _
  have hψ₀ : Function.Injective ψ₀ :=
    injective_of_isLocalization_of_injective
      (M := Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) ψ₀.toRingHom
      (fun x => ψ₀.commutes x) (IsLocalization.injective L le_rfl)
  let φ : K ⊗[A] B →ₐ[K] L :=
    Algebra.TensorProduct.lift (Algebra.ofId K L)
      (IsScalarTower.toAlgHom A B L) fun _ _ => Commute.all _ _
  have hφ : Function.Injective φ := by
    have heq : ∀ x, ψ₀ (Algebra.TensorProduct.comm A K B x) = φ x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul k b => simp [φ, ψ₀, mul_comm]
      | add x y hx hy => simp [hx, hy]
    intro x y hxy
    apply (Algebra.TensorProduct.comm A K B).injective
    apply hψ₀
    simpa only [heq] using hxy
  let e : K₁ ⊗[A] B ≃ₐ[K₁] K₁ ⊗[K] (K ⊗[A] B) :=
    (Algebra.TensorProduct.cancelBaseChange A K K₁ K₁ B).symm
  let μ : K₁ ⊗[K] (K ⊗[A] B) →ₗ[K₁] T :=
    LinearMap.baseChange K₁ φ.toLinearMap
  have hμ : Function.Injective μ := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap φ.toLinearMap hφ
  let : Algebra L T := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower A L T := IsScalarTower.to₁₃₄ A K L T
  let : Algebra B T :=
    RingHom.toAlgebra
      ((algebraMap L T).comp (algebraMap B L))
  have : IsScalarTower B L T := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A B T := IsScalarTower.to₁₂₄ A B L T
  have : IsScalarTower A K₁ T := .of_algebraMap_eq fun a => by
    simp [T, IsScalarTower.algebraMap_apply A K K₁]
  let θ₀ : B ⊗[A] K₁ →ₐ[B] T :=
    Algebra.TensorProduct.lift (Algebra.ofId B T) (IsScalarTower.toAlgHom A K₁ T)
      fun _ _ => Commute.all _ _
  have hθ₀ : Function.Injective θ₀ := by
    have heq : ∀ x, θ₀ x = μ (e (Algebra.TensorProduct.comm A B K₁ x)) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul b k =>
          simp [θ₀, μ, e, φ, T, IsScalarTower.algebraMap_apply B L T,
            Algebra.TensorProduct.right_algebraMap_apply, mul_comm]
      | add x y hx hy => simp [hx, hy]
    intro x y hxy
    apply (Algebra.TensorProduct.comm A B K₁).injective
    apply e.injective
    apply hμ
    simpa only [← heq] using hxy
  let A₁ := integralClosure A K₁
  let ν : B ⊗[A] A₁ →ₗ[B] B ⊗[A] K₁ :=
    LinearMap.baseChange B (Subalgebra.val A₁).toLinearMap
  have hν : Function.Injective ν := by
    simp [ν, LinearMap.baseChange_eq_ltensor]
  have hmem : ∀ z : B ⊗[A] A₁, θ₀ (ν z) ∈ integralClosure B T := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b a =>
        have ha : IsIntegral B
            (Algebra.TensorProduct.includeLeft (R := K) (A := K₁) (B := L) (a : K₁)) :=
          (a.2.map (IsScalarTower.toAlgHom A K₁ T)).tower_top
        simpa [ν, θ₀, T] using
          Subalgebra.mul_mem (integralClosure B T) (Subalgebra.algebraMap_mem _ b) ha
    | add x y hx hy => simpa only [map_add] using Subalgebra.add_mem _ hx hy
  have : Module.Finite B (integralClosure B T) := hfinite
  let θ : B ⊗[A] A₁ →ₗ[B] integralClosure B T :=
    { toFun := fun z => ⟨θ₀ (ν z), hmem z⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun b x => Subtype.ext (by simp) }
  have : Module.Finite B (B ⊗[A] A₁) :=
    Module.Finite.of_injective θ fun x y hxy => hν (hθ₀ (Subtype.ext_iff.mp hxy))
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B

theorem exists_injective_finite_adjoinRoot_baseChange
    (A B K L : Type*)
    (K₁ K₂ : Type*)
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
    [Module.Finite K K₂]
    (D₁ : IntegralClosureBaseChange A B K L K₁)
    (D₂ : IntegralClosureBaseChange A B K L K₂)
    (p : ℕ) (hp : p.Prime)
    (hsep : Algebra.IsSeparableExtension K L) (hB : IsNagataRing B) :
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
    let := D₂.commRingL₁
    let := D₂.commRingA₁
    let := D₂.commRingB₁
    let := D₂.algebraKL₁
    let := D₂.algebraLL₁
    let := D₂.algebraK₁L₁
    let := D₂.algebraBL₁
    let := D₂.algebraAA₁
    let := D₂.algebraA₁K₁
    let := D₂.algebraBB₁
    let := D₂.algebraB₁L₁
    let := D₂.algebraAB₁
    let := D₂.algebraA₁B₁
    let := D₂.isScalarTowerKLL₁
    let := D₂.isScalarTowerKK₁L₁
    let := D₂.isScalarTowerBLL₁
    let := D₂.isScalarTowerAA₁K₁
    let := D₂.isScalarTowerBB₁L₁
    let := D₂.isScalarTowerABB₁
    let := D₂.isScalarTowerAA₁B₁
    let := D₂.isIntegralClosureA₁
    let := D₂.isIntegralClosureB₁
    ∀ (c : D₁.A₁) (x : D₂.A₁),
      minpoly K₁ (algebraMap D₂.A₁ K₂ x) = X ^ p - C (algebraMap D₁.A₁ K₁ c) →
      K₁⟮algebraMap D₂.A₁ K₂ x⟯ = ⊤ →
      ∃ (b : D₁.B₁ →ₐ[B] D₂.B₁)
        (h : AdjoinRoot ((X ^ p - C c).map (algebraMap D₁.A₁ D₁.B₁)) →+* D₂.B₁),
        h.comp (AdjoinRoot.of _) = b.toRingHom ∧
        (∀ (y : D₁.A₁) (z : D₂.A₁),
          algebraMap D₂.A₁ K₂ z = algebraMap K₁ K₂ (algebraMap D₁.A₁ K₁ y) →
          b (algebraMap D₁.A₁ D₁.B₁ y) = algebraMap D₂.A₁ D₂.B₁ z) ∧
        h (AdjoinRoot.root _) = algebraMap D₂.A₁ D₂.B₁ x ∧ Function.Injective h ∧
        (letI := h.toAlgebra;
          Module.Finite (AdjoinRoot ((X ^ p - C c).map (algebraMap D₁.A₁ D₁.B₁))) D₂.B₁) ∧
        ∀ r : B, IsLocalization.Away r L →
          letI := h.toAlgebra
          LocalizationEq (AdjoinRoot ((X ^ p - C c).map (algebraMap D₁.A₁ D₁.B₁))) D₂.B₁
            (AdjoinRoot.of _ (algebraMap B D₁.B₁ r)) := by
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
  let := D₂.commRingL₁
  let := D₂.commRingA₁
  let := D₂.commRingB₁
  let := D₂.algebraKL₁
  let := D₂.algebraLL₁
  let := D₂.algebraK₁L₁
  let := D₂.algebraBL₁
  let := D₂.algebraAA₁
  let := D₂.algebraA₁K₁
  let := D₂.algebraBB₁
  let := D₂.algebraB₁L₁
  let := D₂.algebraAB₁
  let := D₂.algebraA₁B₁
  let := D₂.isScalarTowerKLL₁
  let := D₂.isScalarTowerKK₁L₁
  let := D₂.isScalarTowerBLL₁
  let := D₂.isScalarTowerAA₁K₁
  let := D₂.isScalarTowerBB₁L₁
  let := D₂.isScalarTowerABB₁
  let := D₂.isScalarTowerAA₁B₁
  let := D₂.isIntegralClosureA₁
  let := D₂.isIntegralClosureB₁
  dsimp only
  intro c x hmin hgen
  have hred₁ : IsReduced (L ⊗[K] K₁) :=
    Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated (.inl hsep)
  have hred₂ : IsReduced (L ⊗[K] K₂) :=
    Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated (.inl hsep)
  let e₁ := integralClosureBaseChangeRightEquiv A B K L K₁ D₁ hred₁
  let e₂ := integralClosureBaseChangeRightEquiv A B K L K₂ D₂ hred₂
  have he₁ (a : D₁.A₁) :
      (e₁ (algebraMap D₁.A₁ D₁.B₁ a) : L ⊗[K] K₁) =
        (Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁)
          (algebraMap D₁.A₁ K₁ a) := by
    rw [integralClosureBaseChangeRightEquiv_apply, D₁.ringSquare,
      integralClosureBaseChangeTensorEquiv_right]
  have he₂ (z : D₂.A₁) : (e₂ (algebraMap D₂.A₁ D₂.B₁ z) : L ⊗[K] K₂) =
      1 ⊗ₜ[K] algebraMap D₂.A₁ K₂ z := by
    rw [integralClosureBaseChangeRightEquiv_apply, D₂.ringSquare,
      integralClosureBaseChangeTensorEquiv_right]
    rfl
  have hβB : IsIntegral B (1 ⊗ₜ[K] algebraMap D₂.A₁ K₂ x : L ⊗[K] K₂) := by
    rw [← he₂ x]
    exact (e₂ (algebraMap D₂.A₁ D₂.B₁ x)).property
  have : Module.Finite B D₂.B₁ := integralClosureBaseChange_finite_right A B K L K₂ D₂ hB
  let P : D₁.B₁[X] := (X ^ p - C c).map (algebraMap D₁.A₁ D₁.B₁)
  have hP : P.Monic := (monic_X_pow_sub_C c hp.ne_zero).map _
  have hPmap : P.map ((integralClosure B (L ⊗[K] K₁)).val.toRingHom.comp e₁.toRingHom) =
      (minpoly K₁ (algebraMap D₂.A₁ K₂ x)).map
        (Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁).toRingHom := by
    rw [hmin]
    simp only [P, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      RingHom.comp_apply]
    congr 1
    exact congrArg C (he₁ c)
  obtain ⟨b, h, hc, hb, hr, hi, hfin, hloc⟩ :=
    exists_injective_finite_adjoinRoot_of_integralClosure_equiv B K L K₁ K₂ D₁.B₁ D₂.B₁
      e₁ e₂ (IsIntegral.of_finite K₁ _) hgen P hP hPmap hβB
  refine ⟨b, h, hc, ?_, ?_, hi, hfin, hloc⟩
  · intro y z hz
    apply e₂.injective
    apply Subtype.val_injective
    rw [hb, he₁, he₂ z, hz]
    rfl
  · apply e₂.injective
    apply Subtype.val_injective
    exact hr.trans (he₂ x).symm

theorem integralClosureBaseChange_finite_left
    (A B K L F : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field F]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K F] [Algebra A F]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K F]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [Module.Finite K F] (D : IntegralClosureBaseChange A B K L F)
    (hsep : Algebra.IsSeparableExtension K L) (hB : IsNagataRing B) :
    let := D.commRingA₁
    let := D.algebraAA₁
    Module.Finite A D.A₁ := by
  let := D.commRingL₁
  let := D.commRingA₁
  let := D.commRingB₁
  let := D.algebraAA₁
  let := D.algebraA₁K₁
  let := D.algebraBB₁
  let := D.isScalarTowerAA₁K₁
  let := D.isIntegralClosureA₁
  have hred : IsReduced (L ⊗[K] F) :=
    Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated (.inl hsep)
  have : Module.Finite B D.B₁ := integralClosureBaseChange_finite_right A B K L F D hB
  have : Module.Finite B (integralClosure B (L ⊗[K] F)) :=
    Module.Finite.equiv (integralClosureBaseChangeRightEquiv A B K L F D hred).toLinearEquiv
  let : Algebra L (F ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
  let : Algebra B (F ⊗[K] L) :=
    ((algebraMap L (F ⊗[K] L)).comp (algebraMap B L)).toAlgebra
  have : IsScalarTower B L (F ⊗[K] L) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfin : Module.Finite B (integralClosure B (F ⊗[K] L)) :=
    Module.Finite.equiv ((Algebra.TensorProduct.commRight K L F).restrictScalars
      B).mapIntegralClosure.toLinearEquiv
  have : Module.Finite A (integralClosure A F) :=
    finite_integralClosure_of_finite_tensor_integralClosure A B K L F hfin
  exact Module.Finite.equiv (IsIntegralClosure.equiv A D.A₁ F (integralClosure A
    F)).symm.toLinearEquiv

universe uF
theorem exists_finite_isSeparable_quotient_adjoinRoot
    (F : Type uF) [Field F] (P : F[X]) (hP : P.Separable) (hdeg : 0 < P.natDegree) :
    ∃ (E : Type uF) (_ : Field E) (_ : Algebra F E) (_ : Module.Finite F E),
      Algebra.IsSeparable F E ∧ ∃ φ : AdjoinRoot P →ₐ[F] E, Function.Surjective φ := by
  obtain ⟨q, hq, hqP⟩ := exists_irreducible_of_natDegree_pos hdeg
  let : Fact (Irreducible q) := ⟨hq⟩
  have : Module.Finite F (AdjoinRoot q) := (AdjoinRoot.powerBasis hq.ne_zero).finite
  have hroot : aeval (AdjoinRoot.root q) P = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
    exact hqP
  have hs : IsSeparable F (AdjoinRoot.root q) := hP.of_dvd (minpoly.dvd F (AdjoinRoot.root q) hroot)
  have ht : Algebra.IsSeparable F F⟮AdjoinRoot.root q⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F (AdjoinRoot q)).mpr hs
  rw [IntermediateField.adjoin_root_eq_top q] at ht
  have hsep : Algebra.IsSeparable F (AdjoinRoot q) :=
    (IntermediateField.isSeparable_top F (AdjoinRoot q)).mp ht
  let φ : AdjoinRoot P →ₐ[F] AdjoinRoot q :=
    AdjoinRoot.mapAlgHom (AlgHom.id F F) P q (by simpa using hqP)
  refine ⟨AdjoinRoot q, inferInstance, inferInstance, inferInstance, hsep, φ, ?_⟩
  intro x
  obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective x
  refine ⟨AdjoinRoot.mk P r, ?_⟩
  show AdjoinRoot.map (RingHom.id F) P q (by simpa using hqP) (AdjoinRoot.mk P r) = AdjoinRoot.mk
    q r
  rw [AdjoinRoot.map, AdjoinRoot.lift_mk]
  exact AdjoinRoot.aeval_eq r

noncomputable def quotAdjoinRootPowEquiv
    {R : Type*} [CommRing R] (r : R) (n : ℕ) (P Q : R[X])
    (hPQ : P.map (Ideal.Quotient.mk (Ideal.span {r ^ n})) =
      Q.map (Ideal.Quotient.mk (Ideal.span {r ^ n}))) :
    (AdjoinRoot P ⧸ Ideal.span {AdjoinRoot.of P r ^ n}) ≃ₐ[R]
      (AdjoinRoot Q ⧸ Ideal.span {AdjoinRoot.of Q r ^ n}) :=
  (Ideal.quotientEquivAlgOfEq R (show Ideal.span {AdjoinRoot.of P r ^ n} =
    (Ideal.span {r ^ n}).map (AdjoinRoot.of P) by simp [Ideal.map_span])).trans
    ((quotAdjoinRootEquivOfMapEq (Ideal.span {r ^ n}) P Q hPQ).trans
      (Ideal.quotientEquivAlgOfEq R (by simp [Ideal.map_span])))

private theorem quotAdjoinRootPowEquiv_mk
    {R : Type*} [CommRing R] (r : R) (n : ℕ) (P Q : R[X])
    (hPQ : P.map (Ideal.Quotient.mk (Ideal.span {r ^ n})) =
      Q.map (Ideal.Quotient.mk (Ideal.span {r ^ n}))) (p : R[X]) :
    quotAdjoinRootPowEquiv r n P Q hPQ (Ideal.Quotient.mk _ (AdjoinRoot.mk P p)) =
      Ideal.Quotient.mk _ (AdjoinRoot.mk Q p) := by
  simp only [quotAdjoinRootPowEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk, quotAdjoinRootEquivOfMapEq_apply_mk]

private theorem adjoinRoot_map_mk
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (P : R[X]) (Q : S[X]) (h : Q ∣ P.map f) (p : R[X]) :
    AdjoinRoot.map f P Q h (AdjoinRoot.mk P p) = AdjoinRoot.mk Q (p.map f) := by
  rw [AdjoinRoot.map, AdjoinRoot.lift_mk, ← AdjoinRoot.aeval_eq, aeval_def,
    ← eval₂_map, eval₂_map, AdjoinRoot.algebraMap_eq, eval₂_map]

private noncomputable def quotAdjoinRootPowMap
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (r : R) (n : ℕ) (P : R[X]) :
    (AdjoinRoot P ⧸ Ideal.span {AdjoinRoot.of P r ^ n}) →+*
      (AdjoinRoot (P.map f) ⧸ Ideal.span {AdjoinRoot.of (P.map f) (f r) ^ n}) :=
  Ideal.quotientMap (Ideal.span {AdjoinRoot.of (P.map f) (f r) ^ n})
    (AdjoinRoot.map f P (P.map f) dvd_rfl) (by
    apply Ideal.span_le.mpr
    rintro _ rfl
    change AdjoinRoot.map f P (P.map f) dvd_rfl (AdjoinRoot.of P r ^ n) ∈
      Ideal.span {AdjoinRoot.of (P.map f) (f r) ^ n}
    rw [map_pow, AdjoinRoot.map_of]
    exact Ideal.subset_span (Set.mem_singleton _))

private theorem quotAdjoinRootPowMap_mk
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (r : R) (n : ℕ) (P p : R[X]) :
    quotAdjoinRootPowMap f r n P (Ideal.Quotient.mk _ (AdjoinRoot.mk P p)) =
      Ideal.Quotient.mk _ (AdjoinRoot.mk (P.map f) (p.map f)) := by
  show Ideal.Quotient.mk _ (AdjoinRoot.map f P (P.map f) dvd_rfl (AdjoinRoot.mk P p)) = _
  rw [adjoinRoot_map_mk]

private theorem quotAdjoinRootPowEquiv_naturality
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (r : R) (n : ℕ) (P Q : R[X])
    (hPQ : P.map (Ideal.Quotient.mk (Ideal.span {r ^ n})) =
      Q.map (Ideal.Quotient.mk (Ideal.span {r ^ n})))
    (hPQS : (P.map f).map (Ideal.Quotient.mk (Ideal.span {f r ^ n})) =
      (Q.map f).map (Ideal.Quotient.mk (Ideal.span {f r ^ n}))) :
    (quotAdjoinRootPowEquiv (f r) n (P.map f) (Q.map f) hPQS).toRingHom.comp
        (quotAdjoinRootPowMap f r n P) =
      (quotAdjoinRootPowMap f r n Q).comp (quotAdjoinRootPowEquiv r n P Q hPQ).toRingHom := by
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  show quotAdjoinRootPowEquiv (f r) n (P.map f) (Q.map f) hPQS
      (quotAdjoinRootPowMap f r n P (Ideal.Quotient.mk _ (AdjoinRoot.mk P p))) =
    quotAdjoinRootPowMap f r n Q
      (quotAdjoinRootPowEquiv r n P Q hPQ (Ideal.Quotient.mk _ (AdjoinRoot.mk P p)))
  rw [quotAdjoinRootPowMap_mk, quotAdjoinRootPowEquiv_mk,
    quotAdjoinRootPowEquiv_mk, quotAdjoinRootPowMap_mk]

theorem map_linear_perturbation_quotient
    {R : Type*} [CommRing R] (r : R) (n : ℕ) (P : R[X]) :
    (P - Polynomial.C (r ^ n) * X).map (Ideal.Quotient.mk (Ideal.span {r ^ n})) =
      P.map (Ideal.Quotient.mk (Ideal.span {r ^ n})) := by
  have hz : Ideal.Quotient.mk (Ideal.span {r ^ n}) (r ^ n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_X, hz, Polynomial.C_0, zero_mul, sub_zero]

theorem map_map_linear_perturbation_quotient
    {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (r : R) (n : ℕ) (P : R[X]) :
    ((P - Polynomial.C (r ^ n) * X).map φ).map (Ideal.Quotient.mk (Ideal.span {φ r ^ n})) =
      (P.map φ).map (Ideal.Quotient.mk (Ideal.span {φ r ^ n})) := by
  simpa using map_linear_perturbation_quotient (φ r) n (P.map φ)

noncomputable def quotAdjoinRootPowEquivOfEq
    {R : Type*} [CommRing R] (r : R) (n : ℕ) (P Q : R[X])
    (hPQ : P.map (Ideal.Quotient.mk (Ideal.span {r ^ n})) =
      Q.map (Ideal.Quotient.mk (Ideal.span {r ^ n})))
    (s : AdjoinRoot P) (t : AdjoinRoot Q) (hs : s = AdjoinRoot.of P r)
    (ht : t = AdjoinRoot.of Q r) :
    (AdjoinRoot P ⧸ Ideal.span {s ^ n}) ≃ₐ[R] (AdjoinRoot Q ⧸ Ideal.span {t ^ n}) :=
  (Ideal.quotientEquivAlgOfEq R (show Ideal.span {s ^ n} = Ideal.span {AdjoinRoot.of P r ^ n} by rw
    [hs])).trans
    ((quotAdjoinRootPowEquiv r n P Q hPQ).trans
      (Ideal.quotientEquivAlgOfEq R (by rw [ht])))

private theorem quotAdjoinRootPowEquivOfEq_mk
    {R : Type*} [CommRing R] (r : R) (n : ℕ) (P Q : R[X])
    (hPQ : P.map (Ideal.Quotient.mk (Ideal.span {r ^ n})) =
      Q.map (Ideal.Quotient.mk (Ideal.span {r ^ n})))
    (s : AdjoinRoot P) (t : AdjoinRoot Q) (hs : s = AdjoinRoot.of P r)
    (ht : t = AdjoinRoot.of Q r) (p : R[X]) :
    quotAdjoinRootPowEquivOfEq r n P Q hPQ s t hs ht (Ideal.Quotient.mk _ (AdjoinRoot.mk P p)) =
      Ideal.Quotient.mk _ (AdjoinRoot.mk Q p) := by
  simp only [quotAdjoinRootPowEquivOfEq, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk, quotAdjoinRootPowEquiv_mk]

universe uR uS uC uD

theorem exists_compatible_finite_extensions_of_linear_perturbation
    (R : Type uR) (S : Type uS) (C : Type uC) (D : Type uD)
    [CommRing R] [Nontrivial R] [CommRing S] [CommRing C] [CommRing D]
    (φ : R →+* S) (P : R[X]) (hP : P.Monic) (hdeg : 1 < P.natDegree) (r : R)
    [Algebra (AdjoinRoot P) C] [Algebra (AdjoinRoot (P.map φ)) D]
    (iC : Function.Injective (algebraMap (AdjoinRoot P) C))
    (iD : Function.Injective (algebraMap (AdjoinRoot (P.map φ)) D))
    (a : C →+* D)
    (ha : a.comp (algebraMap (AdjoinRoot P) C) =
      (algebraMap (AdjoinRoot (P.map φ)) D).comp (AdjoinRoot.map φ P (P.map φ) dvd_rfl))
    (hfinC : Module.Finite (AdjoinRoot P) C) (hfinD : Module.Finite (AdjoinRoot (P.map φ)) D)
    (hr : r ∈ nonZeroDivisors R) (hφr : φ r ∈ nonZeroDivisors S)
    (hnzdC : algebraMap (AdjoinRoot P) C (AdjoinRoot.of P r) ∈ nonZeroDivisors C)
    (hnzdD : algebraMap (AdjoinRoot (P.map φ)) D (AdjoinRoot.of (P.map φ) (φ r)) ∈ nonZeroDivisors
      D)
    (hlocC : LocalizationEq (AdjoinRoot P) C (AdjoinRoot.of P r))
    (hlocD : LocalizationEq (AdjoinRoot (P.map φ)) D (AdjoinRoot.of (P.map φ) (φ r))) :
    let A₁' := AdjoinRoot P
    let A₂' := AdjoinRoot (P.map φ)
    let A₁ := C
    let A₂ := D
    let a' := AdjoinRoot.map φ P (P.map φ) dvd_rfl
    let f := AdjoinRoot.of P r
    ∃ (n : ℕ) (_ : 0 < n),
      let Q := P - Polynomial.C (r ^ n) * X
      let B₁' := AdjoinRoot Q
      let B₂' := AdjoinRoot (Q.map φ)
      let b' := AdjoinRoot.map φ Q (Q.map φ) dvd_rfl
      let g := AdjoinRoot.of Q r
      let φ₁' := (quotAdjoinRootPowEquiv r n P Q (map_linear_perturbation_quotient r n
        P).symm).toRingEquiv
      let φ₂' := (quotAdjoinRootPowEquivOfEq (φ r) n (P.map φ) (Q.map φ)
        (map_map_linear_perturbation_quotient φ r n P).symm (a' f) (b' g)
        (AdjoinRoot.map_of φ P (P.map φ) dvd_rfl r)
        (AdjoinRoot.map_of φ Q (Q.map φ) dvd_rfl r)).toRingEquiv
      ∃ (B₁ : Type uR) (_ : CommRing B₁) (_ : Algebra B₁' B₁)
        (B₂ : Type uS) (_ : CommRing B₂) (_ : Algebra B₂' B₂),
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
  let a' := AdjoinRoot.map φ P (P.map φ) dvd_rfl
  let f := AdjoinRoot.of P r
  obtain ⟨n₁, hn₁, n₂, hn₂, H⟩ :=
    exists_compatible_finite_extensions_of_quotient_equiv
      (AdjoinRoot P) C (AdjoinRoot (P.map φ)) D iC iD a' a ha f hfinC hfinD hnzdC
      (by simpa only [a', f, AdjoinRoot.map_of] using hnzdD) hlocC
      (by simpa only [a', f, AdjoinRoot.map_of] using hlocD)
  let n := max n₁ n₂
  have hn : 0 < n := lt_of_lt_of_le hn₁ (le_max_left _ _)
  let Q := P - Polynomial.C (r ^ n) * X
  have hQ : Q.Monic := hP.sub_of_left
    ((degree_C_mul_X_le (r ^ n)).trans_lt (by
      rw [degree_eq_natDegree hP.ne_zero]
      exact_mod_cast hdeg))
  have : Module.Free R (AdjoinRoot Q) := Module.Free.of_basis (AdjoinRoot.powerBasis' hQ).basis
  have : Module.Free S (AdjoinRoot (Q.map φ)) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' (hQ.map φ)).basis
  let b' := AdjoinRoot.map φ Q (Q.map φ) dvd_rfl
  let g := AdjoinRoot.of Q r
  have hg : g ∈ nonZeroDivisors (AdjoinRoot Q) :=
    algebraMap_mem_nonZeroDivisors_of_isTorsionFree hr
  have hbg : b' g ∈ nonZeroDivisors (AdjoinRoot (Q.map φ)) := by
    rw [AdjoinRoot.map_of]
    exact algebraMap_mem_nonZeroDivisors_of_isTorsionFree hφr
  have hPQ : P.map (Ideal.Quotient.mk (Ideal.span {r ^ n})) =
      Q.map (Ideal.Quotient.mk (Ideal.span {r ^ n})) :=
    (map_linear_perturbation_quotient r n P).symm
  have hPQS : (P.map φ).map (Ideal.Quotient.mk (Ideal.span {φ r ^ n})) =
      (Q.map φ).map (Ideal.Quotient.mk (Ideal.span {φ r ^ n})) :=
    (map_map_linear_perturbation_quotient φ r n P).symm
  let eR := (quotAdjoinRootPowEquiv r n P Q hPQ).toRingEquiv
  let eS := (quotAdjoinRootPowEquivOfEq (φ r) n (P.map φ) (Q.map φ)
    hPQS (a' f) (b' g) (AdjoinRoot.map_of φ P (P.map φ) dvd_rfl r)
    (AdjoinRoot.map_of φ Q (Q.map φ) dvd_rfl r)).toRingEquiv
  dsimp only
  refine ⟨n, hn, ?_⟩
  apply H n (le_refl _) (AdjoinRoot Q) (AdjoinRoot (Q.map φ)) b' g hg hbg eR eS
  · apply RingHom.ext
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    simp only [RingHom.comp_apply, Ideal.quotientMap_mk]
    show eS (Ideal.Quotient.mk _ (a' (AdjoinRoot.mk P p))) = _
    rw [adjoinRoot_map_mk]
    show quotAdjoinRootPowEquivOfEq (φ r) n (P.map φ) (Q.map φ) hPQS (a' f) (b' g)
      (AdjoinRoot.map_of φ P (P.map φ) dvd_rfl r)
      (AdjoinRoot.map_of φ Q (Q.map φ) dvd_rfl r)
      (Ideal.Quotient.mk _ (AdjoinRoot.mk (P.map φ) (p.map φ))) = _
    rw [quotAdjoinRootPowEquivOfEq_mk]
    have heR : eR.toRingHom (Ideal.Quotient.mk (Ideal.span {f ^ n}) (AdjoinRoot.mk P p)) =
        Ideal.Quotient.mk (Ideal.span {g ^ n}) (AdjoinRoot.mk Q p) :=
      quotAdjoinRootPowEquiv_mk r n P Q hPQ p
    rw [heR]
    show _ = Ideal.Quotient.mk _ (b' (AdjoinRoot.mk Q p))
    rw [adjoinRoot_map_mk]
  · show quotAdjoinRootPowEquiv r n P Q hPQ (Ideal.Quotient.mk _ (AdjoinRoot.mk P (Polynomial.C
    r))) =
      Ideal.Quotient.mk _ (AdjoinRoot.mk Q (Polynomial.C r))
    rw [quotAdjoinRootPowEquiv_mk]

end IsDiscreteValuationRing
