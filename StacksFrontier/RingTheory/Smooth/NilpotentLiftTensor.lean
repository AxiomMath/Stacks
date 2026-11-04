module

public import StacksFrontier.RingTheory.Smooth.NilpotentLiftAtPrime
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Smooth.Basic

/-!
# The Jacobian lifting at a point of a base change

Let `B'` be a ring with an ideal `J` inside its nilradical, `M` a formally smooth `B'`-algebra of
finite presentation and `f'₁, …, f'ᵣ ∈ M`, with `S₁ = M / (f')`. Let `C` be a `B'`-algebra
through a ring map `s` (its algebra structure) which is also smooth over `B'` through a second
ring map `t`, with `J C` the same for both. This file shows that `C ⊗_{B'} S₁` (base change along
`s`) is smooth over `B'` through `t` at a point, from the data Stacks 0CJV produces there.
-/

@[expose] public section

open TensorProduct

namespace Algebra

universe u

variable {B' : Type u} [CommRing B'] (J : Ideal B')
  {C : Type u} [CommRing C] [Algebra B' C] (t : B' →+* C)

/-- The `B' ⧸ J`-algebra structure on `N ⊗_{B'} C`, for `N` killed by `J`, through `t`, when
`t (J) C = J C`. -/
noncomputable def tensorQuotientViaT (hE0 : J.map (algebraMap B' C) = J.map t)
    (N : Type u) [CommRing N] [Algebra B' N] (hN : ∀ j ∈ J, algebraMap B' N j = 0) :
    B' ⧸ J →+* N ⊗[B'] C :=
  Ideal.Quotient.lift J (Algebra.TensorProduct.includeRight.toRingHom.comp t) (by
    intro j hj
    have hjC : t j ∈ J.map (algebraMap B' C) := hE0 ▸ Ideal.mem_map_of_mem t hj
    have hker : J.map (algebraMap B' C) ≤ RingHom.ker
        (Algebra.TensorProduct.includeRight (R := B') (A := N) (B := C)).toRingHom := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.includeRight_apply]
      rw [Algebra.algebraMap_eq_smul_one, ← smul_tmul, ← Algebra.algebraMap_eq_smul_one, hN x hx,
        zero_tmul]
    exact hker hjC)

/-- `J` kills the reduction `S ⧸ J S` of a `B'`-algebra `S`. -/
theorem algebraMap_quotient_map_eq_zero (S : Type u) [CommRing S] [Algebra B' S] :
    ∀ j ∈ J, algebraMap B' (S ⧸ J.map (algebraMap B' S)) j = 0 := by
  intro j hj
  rw [IsScalarTower.algebraMap_apply B' S, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ hj

/-- `M ⊗_{B'} C` is formally smooth over `B'` through `t`. -/
theorem formallySmooth_tensor_viaT (ht : @Algebra.Smooth B' _ C _ t.toAlgebra)
    (M : Type u) [CommRing M] [Algebra B' M] [FormallySmooth B' M] :
    @FormallySmooth B' (M ⊗[B'] C) _ _
      ((Algebra.TensorProduct.includeRight.toRingHom).comp t).toAlgebra := by
  let T := M ⊗[B'] C
  let algCT : Algebra C T := Algebra.TensorProduct.rightAlgebra
  have hTC : FormallySmooth C T :=
    FormallySmooth.of_equiv
      { (Algebra.TensorProduct.comm B' C M) with
        commutes' := fun c => rfl }
  let tT : Algebra B' T := ((Algebra.TensorProduct.includeRight.toRingHom).comp t).toAlgebra
  have htower : @IsScalarTower B' C T t.toAlgebra.toSMul algCT.toSMul tT.toSMul :=
    @IsScalarTower.of_algebraMap_eq B' C T _ _ _ t.toAlgebra algCT tT fun _ => rfl
  exact @FormallySmooth.comp B' _ C _ t.toAlgebra T _ tT algCT htower ht.formallySmooth hTC

/-- **Smoothness through `t` at a point of the base change `(M / (f')) ⊗_{B'} C`.** -/
theorem isSmoothAt_tensor_quotient_span (hJ : J ≤ nilradical B')
    (ht : @Algebra.Smooth B' _ C _ t.toAlgebra)
    [Module.Flat B' C] (hE0 : J.map (algebraMap B' C) = J.map t)
    {M : Type u} [CommRing M] [Algebra B' M] [FormallySmooth B' M] {r : ℕ} (f' : Fin r → M)
    {Q : Type u} [CommRing Q] (φ₀ : Q →+* M ⧸ J.map (algebraMap B' M)) (hφ₀ : φ₀.Flat)
    (f₀ : Fin r → Q) (hf₀ : ∀ i, φ₀ (f₀ i) = Ideal.Quotient.mk _ (f' i)) (q₀ : Ideal Q)
    (hrel : ∀ a : Fin r → Q, ∑ i, a i * f₀ i = 0 → ∀ i, a i ∈ q₀)
    (hZ : @FormallySmooth (B' ⧸ J) (((M ⧸ Ideal.span (Set.range f')) ⧸
        J.map (algebraMap B' (M ⧸ Ideal.span (Set.range f')))) ⊗[B'] C) _ _
      (tensorQuotientViaT J t hE0 _
        (algebraMap_quotient_map_eq_zero J (M ⧸ Ideal.span (Set.range f')))).toAlgebra)
    (𝔷 : Ideal ((M ⧸ Ideal.span (Set.range f')) ⊗[B'] C)) [𝔷.IsPrime]
    (hq₀ : q₀ ≤ ((((𝔷.comap (Algebra.TensorProduct.includeLeftRingHom)).comap
      (algebraMap M (M ⧸ Ideal.span (Set.range f')))).map
        (Ideal.Quotient.mk (J.map (algebraMap B' M)))).comap φ₀)) :
    @IsSmoothAt B' ((M ⧸ Ideal.span (Set.range f')) ⊗[B'] C) _ _
      ((Algebra.TensorProduct.includeRight.toRingHom).comp t).toAlgebra 𝔷 _ := by
  classical
  -- objects built from the algebra structure `s` of `C`
  let F' : Ideal M := Ideal.span (Set.range f')
  let JM : Ideal M := J.map (algebraMap B' M)
  let JS : Ideal (M ⧸ F') := J.map (algebraMap B' (M ⧸ F'))
  let mk₁ : M →ₐ[B'] M ⧸ F' := Ideal.Quotient.mkₐ B' F'
  let mkX : M →ₐ[B'] (M ⧸ F') ⧸ JS := (Ideal.Quotient.mkₐ B' JS).comp mk₁
  let Θ₁ := Algebra.TensorProduct.map mk₁ (AlgHom.id B' C)
  let Θ₂ := Algebra.TensorProduct.map mkX (AlgHom.id B' C)
  let Θ₃ := Algebra.TensorProduct.map (Ideal.Quotient.mkₐ B' JM) (AlgHom.id B' C)
  have hsurjC : Function.Surjective (AlgHom.id B' C) := fun c => ⟨c, rfl⟩
  have hs₁ : Function.Surjective Θ₁ :=
    Algebra.TensorProduct.map_surjective _ _ Ideal.Quotient.mk_surjective hsurjC
  have hmkX : Function.Surjective mkX :=
    (Ideal.Quotient.mk_surjective).comp (Ideal.Quotient.mk_surjective (I := F'))
  have hs₂ : Function.Surjective Θ₂ := Algebra.TensorProduct.map_surjective _ _ hmkX hsurjC
  have hs₃ : Function.Surjective Θ₃ :=
    Algebra.TensorProduct.map_surjective _ _ Ideal.Quotient.mk_surjective hsurjC
  let f : Fin r → M ⊗[B'] C := fun i => f' i ⊗ₜ (1 : C)
  let inclL := (Algebra.TensorProduct.includeLeft (R := B') (S := B') (A := M) (B := C))
  have hspanf : F'.map inclL = Ideal.span (Set.range f) := by
    rw [Ideal.map_span, ← Set.range_comp]; rfl
  have hker₁ : RingHom.ker Θ₁ = Ideal.span (Set.range f) := by
    simp only [Θ₁]
    rw [Algebra.TensorProduct.rTensor_ker _ (Ideal.Quotient.mkₐ_surjective B' F'),
      show RingHom.ker (Ideal.Quotient.mkₐ B' F') = F' from Ideal.Quotient.mkₐ_ker B' F', hspanf]
  -- the ideal `J (M ⊗ C)`, read through either structure
  let JT : Ideal (M ⊗[B'] C) := J.map (algebraMap B' (M ⊗[B'] C))
  let tT : B' →+* M ⊗[B'] C := (Algebra.TensorProduct.includeRight.toRingHom).comp t
  have hJl : JM.map inclL = JT := by
    show Ideal.map inclL.toRingHom (Ideal.map (algebraMap B' M) J) =
      Ideal.map (algebraMap B' (M ⊗[B'] C)) J
    rw [Ideal.map_map]
    congr 1
  have hJt : J.map tT = JT := by
    have : J.map tT = (J.map t).map (Algebra.TensorProduct.includeRight.toRingHom) := by
      rw [Ideal.map_map]
    rw [this, ← hE0, Ideal.map_map]
    congr 1
    ext b
    simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_one_eq_one_tmul]
  have hker₃ : RingHom.ker Θ₃ = J.map tT := by
    simp only [Θ₃]
    rw [Algebra.TensorProduct.rTensor_ker _ (Ideal.Quotient.mkₐ_surjective B' JM),
      show RingHom.ker (Ideal.Quotient.mkₐ B' JM) = JM from Ideal.Quotient.mkₐ_ker B' JM, hJl, hJt]
  have hkerX : RingHom.ker mkX = JM ⊔ F' := by
    have hJS : JS = JM.map mk₁ := by
      show Ideal.map (algebraMap B' (M ⧸ F')) J =
        Ideal.map mk₁.toRingHom (Ideal.map (algebraMap B' M) J)
      rw [Ideal.map_map]
      congr 1
    show RingHom.ker ((Ideal.Quotient.mk JS).comp (Ideal.Quotient.mk F')) = _
    rw [← RingHom.comap_ker, Ideal.mk_ker, hJS]
    show Ideal.comap (Ideal.Quotient.mk F') (JM.map (Ideal.Quotient.mk F')) = _
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker]
  have hker₂ : RingHom.ker Θ₂ = J.map tT ⊔ Ideal.span (Set.range f) := by
    simp only [Θ₂]
    rw [Algebra.TensorProduct.rTensor_ker _ hmkX, hkerX, Ideal.map_sup, hJl, hspanf, hJt]
  -- the reductions, as ring isomorphisms
  let e₁ : (M ⊗[B'] C) ⧸ Ideal.span (Set.range f) ≃+* (M ⧸ F') ⊗[B'] C :=
    (Ideal.quotEquivOfEq hker₁.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hs₁).toRingEquiv
  have he₁ : ∀ z, e₁ (Ideal.Quotient.mk _ z) = Θ₁ z := fun _ => rfl
  have hspan₂ : Ideal.span (Set.range (Ideal.Quotient.mk (J.map tT) ∘ f)) =
      (Ideal.span (Set.range f)).map (Ideal.Quotient.mk (J.map tT)) := by
    rw [Ideal.map_span, ← Set.range_comp]
  let e₂ : ((M ⊗[B'] C) ⧸ J.map tT) ⧸ Ideal.span (Set.range (Ideal.Quotient.mk (J.map tT) ∘ f))
      ≃+* ((M ⧸ F') ⧸ JS) ⊗[B'] C :=
    (Ideal.quotEquivOfEq hspan₂).trans ((DoubleQuot.quotQuotEquivQuotSup _ _).trans
      ((Ideal.quotEquivOfEq hker₂.symm).trans
        (Ideal.quotientKerAlgEquivOfSurjective hs₂).toRingEquiv))
  have he₂ : ∀ z, e₂ (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ z)) = Θ₂ z := fun _ => rfl
  let e₃ : (M ⊗[B'] C) ⧸ J.map tT ≃+* (M ⧸ JM) ⊗[B'] C :=
    (Ideal.quotEquivOfEq hker₃.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hs₃).toRingEquiv
  have he₃ : ∀ z, e₃ (Ideal.Quotient.mk _ z) = Θ₃ z := fun _ => rfl
  -- the map `M ⧸ JM ⟶ (M ⊗ C) ⧸ J (M ⊗ C)` and its flatness
  have hle : JM ≤ (J.map tT).comap (inclL : M →+* M ⊗[B'] C) := by
    have : JM.map (inclL : M →+* M ⊗[B'] C) = J.map tT := by rw [hJt]; exact hJl
    rw [← this]; exact Ideal.le_comap_map
  let ψ : M ⧸ JM →+* (M ⊗[B'] C) ⧸ J.map tT := Ideal.quotientMap _ (inclL : M →+* M ⊗[B'] C) hle
  have hψe :
      (e₃.symm : (M ⧸ JM) ⊗[B'] C →+* _).comp Algebra.TensorProduct.includeLeftRingHom = ψ := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun m => ?_)
    apply e₃.injective
    simp only [RingHom.comp_apply, RingHom.coe_coe, RingEquiv.apply_symm_apply]
    rfl
  have hψflat : ψ.Flat := by
    rw [← hψe]
    refine RingHom.Flat.comp ?_ (RingHom.Flat.of_bijective e₃.symm.bijective)
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  -- switch to the structure through `t`
  let tA : Algebra B' (M ⊗[B'] C) := tT.toAlgebra
  have : FormallySmooth B' (M ⊗[B'] C) := formallySmooth_tensor_viaT t ht M
  have hFS0 : FormallySmooth (B' ⧸ J) (((M ⊗[B'] C) ⧸ J.map (algebraMap B' (M ⊗[B'] C))) ⧸
      Ideal.span (Set.range (Ideal.Quotient.mk (J.map (algebraMap B' (M ⊗[B'] C))) ∘ f))) := by
    let : Algebra (B' ⧸ J) (((M ⧸ F') ⧸ JS) ⊗[B'] C) :=
      (tensorQuotientViaT J t hE0 _ (algebraMap_quotient_map_eq_zero J (M ⧸ F'))).toAlgebra
    have := hZ
    refine FormallySmooth.of_equiv (AlgEquiv.ofRingEquiv (f := e₂.symm) fun x => ?_)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply e₂.injective
    rw [RingEquiv.apply_symm_apply]
    show _ = e₂ (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (tT b)))
    rw [he₂]
    rfl
  let φ : Q →+* (M ⊗[B'] C) ⧸ J.map (algebraMap B' (M ⊗[B'] C)) := ψ.comp φ₀
  have hφ : φ.Flat := RingHom.Flat.comp hφ₀ hψflat
  have hf₀' : ∀ i, φ (f₀ i) = Ideal.Quotient.mk _ (f i) := by
    intro i
    show ψ (φ₀ (f₀ i)) = _
    rw [hf₀]
    rfl
  let 𝔷' : Ideal ((M ⊗[B'] C) ⧸ Ideal.span (Set.range f)) := 𝔷.comap (e₁ : _ →+* _)
  have : 𝔷'.IsPrime := Ideal.comap_isPrime _ _
  have hq₀' : q₀ ≤ ((𝔷'.comap (algebraMap (M ⊗[B'] C) ((M ⊗[B'] C) ⧸ Ideal.span (Set.range f)))).map
      (Ideal.Quotient.mk (J.map (algebraMap B' (M ⊗[B'] C))))).comap φ := by
    intro a ha
    obtain ⟨m, hm, hma⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1
      (hq₀ ha)
    rw [Ideal.mem_comap]
    show ψ (φ₀ a) ∈ _
    rw [← hma]
    refine Ideal.mem_map_of_mem _ ?_
    show e₁ (Ideal.Quotient.mk _ (inclL m)) ∈ 𝔷
    rw [he₁]
    exact hm
  have hsm := Algebra.isSmoothAt_quotient_span_of_reduction J hJ f φ hφ f₀ hf₀' q₀ hrel 𝔷' hq₀'
  -- transport to `(M ⧸ F') ⊗ C`
  let tS : Algebra B' ((M ⧸ F') ⊗[B'] C) :=
    ((Algebra.TensorProduct.includeRight.toRingHom).comp t).toAlgebra
  let E₁ : ((M ⊗[B'] C) ⧸ Ideal.span (Set.range f)) ≃ₐ[B'] (M ⧸ F') ⊗[B'] C :=
    AlgEquiv.ofRingEquiv (f := e₁) fun b => rfl
  have H : Submonoid.map E₁ 𝔷'.primeCompl = 𝔷.primeCompl := by
    ext x
    refine ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun hx => ⟨E₁.symm x, ?_, by simp⟩⟩
    show E₁ (E₁.symm x) ∉ 𝔷
    simpa using hx
  exact FormallySmooth.of_equiv (IsLocalization.algEquivOfAlgEquiv
    (Localization.AtPrime 𝔷') (Localization.AtPrime 𝔷) (h := E₁) H)

end Algebra
