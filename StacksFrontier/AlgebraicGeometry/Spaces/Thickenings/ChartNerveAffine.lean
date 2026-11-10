module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.MorphismDescent
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFieldAtlas
public import StacksFrontier.RingTheory.Descent.CechNerveClimb

/-!
# An algebraic space whose chart is the Čech nerve of a ring map is affine

Let `F` be an algebraic space over `S` with a surjective étale chart `f : U → F` from an object
of the site with affine underlying scheme, whose kernel pair `t, s : R ⇉ U` has affine underlying
scheme too. Suppose there is a faithfully flat étale ring map `A₁ → Γ(U)` with
`Γ(U) ⊗[A₁] Γ(U) ≅ Γ(R)`, the isomorphism carrying the two inclusions to `t^*` and `s^*`. Then
`F` is represented by `Spec A₁`, so it is an affine algebraic space
(`AlgebraicGeometry.Space.isAffineSpace_of_chart_tensor`).

`Spec Γ(U) → Spec A₁` is faithfully flat, of finite presentation, and its kernel pair is
`Spec Γ(R)` (`AlgebraicGeometry.isPullback_of_tensor_equiv`). The structure morphism `U → S`
coequalizes `t, s`, so descends to `Spec A₁ → S` (Stacks 023Q,
`AlgebraicGeometry.exists_desc_of_surjective_flat_quasiCompact'`), making `Spec A₁` an object of
the site over `S`; then `AlgebraicGeometry.Space.exists_iso_yoneda_of_isPullback` identifies `F`
with it.

`AlgebraicGeometry.Space.isAffineSpace_of_isNerveReduction_bot` reads the hypothesis off a
Čech nerve modulo `0` (`Module.Descent.IsNerveReduction`), the output of the ring-level climb.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace AlgebraicGeometry

/-- **The quotient of an affine chart by a tensor relation.** Let `t, s : R ⟶ U` be morphisms of
affine schemes over `S`, and let `A₁ → Γ(U)` be faithfully flat and étale with an isomorphism
`Γ(U) ⊗[A₁] Γ(U) ≅ Γ(R)` carrying the two inclusions to `t^*` and `s^*`. Then `Spec A₁` is a
scheme over `S` receiving from `U` a faithfully flat morphism of finite presentation with kernel
pair `t, s`. -/
theorem exists_quotient_of_tensor_equiv (S : Scheme.{u}) {R U : Over S} (t s : R ⟶ U)
    [IsAffine U.left] [IsAffine R.left] (A₁ : Type u) [CommRing A₁] [Algebra A₁ Γ(U.left, ⊤)]
    [Algebra.Etale A₁ Γ(U.left, ⊤)] [Module.FaithfullyFlat A₁ Γ(U.left, ⊤)]
    (e : Γ(U.left, ⊤) ⊗[A₁] Γ(U.left, ⊤) ≃+* Γ(R.left, ⊤))
    (he₁ : ∀ b, e (b ⊗ₜ 1) = t.left.appTop.hom b) (he₂ : ∀ b, e (1 ⊗ₜ b) = s.left.appTop.hom b) :
    ∃ (g : Spec (.of A₁) ⟶ S) (π : U ⟶ Over.mk g),
      Flat π.left ∧ LocallyOfFinitePresentation π.left ∧ Surjective π.left ∧
        IsPullback t s π π := by
  let φ : CommRingCat.of A₁ ⟶ Γ(U.left, ⊤) := CommRingCat.ofHom (algebraMap A₁ Γ(U.left, ⊤))
  -- the pushout square of rings
  have hpo : IsPushout φ φ t.left.appTop s.left.appTop := by
    refine (CommRingCat.isPushout_tensorProduct A₁ Γ(U.left, ⊤) Γ(U.left, ⊤)).of_iso (Iso.refl _)
      (Iso.refl _) (Iso.refl _) e.toCommRingCatIso (by simp [φ]) (by simp [φ]) ?_ ?_
    · ext b; simpa using he₁ b
    · ext b; simpa using he₂ b
  have hspec := isPullback_SpecMap_of_isPushout _ _ _ _ hpo
  -- the quotient map `X ⟶ Spec A₁`
  let π₀ : U.left ⟶ Spec (.of A₁) := U.left.isoSpec.hom ≫ Spec.map φ
  have hP : IsPullback t.left s.left π₀ π₀ := by
    refine hspec.of_iso R.left.isoSpec.symm U.left.isoSpec.symm U.left.isoSpec.symm (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp [Scheme.isoSpec_inv_naturality]
    · simp [Scheme.isoSpec_inv_naturality]
    · simp [π₀]
    · simp [π₀]
  have hφff : φ.hom.FaithfullyFlat := by
    rw [CommRingCat.hom_ofHom, RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  obtain ⟨hφflat, hφsurj⟩ := (flat_and_surjective_SpecMap_iff φ).2 hφff
  have hφet : Etale (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom]
    exact RingHom.etale_algebraMap.2 inferInstance
  have := hφflat
  have := hφsurj
  have := hφet
  have : Flat π₀ := inferInstance
  have : Surjective π₀ := inferInstance
  have : LocallyOfFinitePresentation π₀ := inferInstance
  have : QuasiCompact π₀ := inferInstance
  -- the structure morphism descends
  obtain ⟨g, hg⟩ := exists_desc_of_surjective_flat_quasiCompact' π₀ U.hom (by
    rw [← cancel_epi hP.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc,
      IsPullback.isoPullback_hom_snd_assoc, Over.w t, Over.w s])
  let π : U ⟶ Over.mk g := Over.homMk π₀ hg
  refine ⟨g, π, inferInstanceAs (Flat π₀), inferInstanceAs (LocallyOfFinitePresentation π₀),
    inferInstanceAs (Surjective π₀), ?_⟩
  exact IsPullback.of_map (Over.forget S) (by ext; exact hP.w) hP

/-- **A Čech nerve modulo `0` is the nerve of a faithfully flat étale ring map.** If the diagram
`p₁, p₂ : B → C`, `e₁₂, e₁₃, e₂₃ : C → D` is a nerve modulo `0`, then `B` is a faithfully flat
étale algebra over some ring `A₁` with `B ⊗[A₁] B ≅ C`, the isomorphism carrying the two
inclusions to `p₁` and `p₂`. -/
theorem _root_.Module.Descent.IsNerveReduction.exists_tensor_equiv {R' B C D : Type u} [CommRing R']
    [CommRing B] [CommRing C] [CommRing D] [Algebra R' B] [Algebra R' C] [Algebra R' D]
    {p₁ p₂ : B →ₐ[R'] C} {e₁₂ e₁₃ e₂₃ : C →ₐ[R'] D}
    (h : Module.Descent.IsNerveReduction p₁ p₂ e₁₂ e₁₃ e₂₃ ⊥) :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : Algebra A₁ B), Algebra.Etale A₁ B ∧
      Module.FaithfullyFlat A₁ B ∧ ∃ e : B ⊗[A₁] B ≃+* C,
        (∀ b, e (b ⊗ₜ 1) = p₁ b) ∧ ∀ b, e (1 ⊗ₜ b) = p₂ b := by
  obtain ⟨A₁, B₁, _, _, _, hEt, hFF, πB, πC, -, hsB, hsC, -, hkB, hkC, -, hC₁, hC₂, -⟩ := h
  rw [Ideal.map_bot] at hkC
  let eB : B ≃+* B₁ := RingEquiv.ofBijective πB ⟨(RingHom.injective_iff_ker_eq_bot _).2 hkB, hsB⟩
  let eC : C ≃+* B₁ ⊗[A₁] B₁ :=
    RingEquiv.ofBijective πC ⟨(RingHom.injective_iff_ker_eq_bot _).2 hkC, hsC⟩
  let : Algebra A₁ B := ((eB.symm : B₁ →+* B).comp (algebraMap A₁ B₁)).toAlgebra
  let eBA : B ≃ₐ[A₁] B₁ := AlgEquiv.ofRingEquiv (f := eB) fun a => by
    change eB (eB.symm (algebraMap A₁ B₁ a)) = _
    rw [RingEquiv.apply_symm_apply]
  have : Algebra.Etale A₁ B := Algebra.Etale.of_equiv eBA.symm
  have : Module.FaithfullyFlat A₁ B := Module.FaithfullyFlat.of_linearEquiv A₁ B₁ eBA.toLinearEquiv
  refine ⟨A₁, inferInstance, inferInstance, inferInstance, inferInstance,
    (Algebra.TensorProduct.congr eBA eBA).toRingEquiv.trans eC.symm, fun b => ?_, fun b => ?_⟩
  · rw [RingEquiv.trans_apply, RingEquiv.symm_apply_eq]
    change _ = πC (p₁ b)
    rw [show πC (p₁ b) = πB b ⊗ₜ 1 from RingHom.congr_fun hC₁ b]
    change (Algebra.TensorProduct.congr eBA eBA) (b ⊗ₜ 1) = _
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
    rfl
  · rw [RingEquiv.trans_apply, RingEquiv.symm_apply_eq]
    change _ = πC (p₂ b)
    rw [show πC (p₂ b) = 1 ⊗ₜ πB b from RingHom.congr_fun hC₂ b]
    change (Algebra.TensorProduct.congr eBA eBA) (1 ⊗ₜ b) = _
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
    rfl

/-- **The rings of functions of a Čech nerve of affine schemes (G1).** Let `t, s : R ⟶ U`,
`δ : U ⟶ R` and `e₁₂, e₁₃, e₂₃ : W ⟶ R` be morphisms of affine schemes satisfying the simplicial
identities of the first terms of a Čech nerve, with `s`, `e₂₃` and `t`, `e₁₂` étale, and let
`p₁, p₂ : Γ(U) → Γ(R)`, `δ' : Γ(R) → Γ(U)`, `e₁₂', e₁₃', e₂₃' : Γ(R) → Γ(W)` be algebra maps over
some ring `R'` acting as the pullbacks of functions along them. Then they satisfy the identities
and étaleness consumed by `Module.Descent.isNerveReduction_bot_of_span_singleton` and its
relatives. -/
theorem nerve_identities_of_schemes {U R W : Scheme.{u}} [IsAffine U] [IsAffine R] [IsAffine W]
    (t s : R ⟶ U) (δ : U ⟶ R) (e₁₂ e₁₃ e₂₃ : W ⟶ R)
    (hδt : δ ≫ t = 𝟙 U) (hδs : δ ≫ s = 𝟙 U) (h₁₂₁₃ : e₁₂ ≫ t = e₁₃ ≫ t)
    (h₁₂₂₃ : e₁₂ ≫ s = e₂₃ ≫ t) (h₁₃₂₃ : e₁₃ ≫ s = e₂₃ ≫ s)
    [Etale t] [Etale s] [Etale e₁₂] [Etale e₂₃]
    {R' : Type u} [CommRing R'] [Algebra R' Γ(U, ⊤)] [Algebra R' Γ(R, ⊤)] [Algebra R' Γ(W, ⊤)]
    (p₁ p₂ : Γ(U, ⊤) →ₐ[R'] Γ(R, ⊤)) (δ' : Γ(R, ⊤) →ₐ[R'] Γ(U, ⊤))
    (e₁₂' e₁₃' e₂₃' : Γ(R, ⊤) →ₐ[R'] Γ(W, ⊤))
    (hp₁ : ∀ b, p₁ b = t.appTop.hom b) (hp₂ : ∀ b, p₂ b = s.appTop.hom b)
    (hδ : ∀ c, δ' c = δ.appTop.hom c) (he₁₂ : ∀ c, e₁₂' c = e₁₂.appTop.hom c)
    (he₁₃ : ∀ c, e₁₃' c = e₁₃.appTop.hom c) (he₂₃ : ∀ c, e₂₃' c = e₂₃.appTop.hom c) :
    δ'.comp p₁ = AlgHom.id R' Γ(U, ⊤) ∧ δ'.comp p₂ = AlgHom.id R' Γ(U, ⊤) ∧
      e₁₂'.comp p₁ = e₁₃'.comp p₁ ∧ e₁₂'.comp p₂ = e₂₃'.comp p₁ ∧
      e₁₃'.comp p₂ = e₂₃'.comp p₂ ∧
      (p₁ : Γ(U, ⊤) →+* Γ(R, ⊤)).Etale ∧ (p₂ : Γ(U, ⊤) →+* Γ(R, ⊤)).Etale ∧
      (e₁₂' : Γ(R, ⊤) →+* Γ(W, ⊤)).Etale ∧ (e₂₃' : Γ(R, ⊤) →+* Γ(W, ⊤)).Etale := by
  have key : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (z : Γ(Z, ⊤)),
      f.appTop.hom (g.appTop.hom z) = (f ≫ g).appTop.hom z := fun f g z => by
    rw [Scheme.Hom.comp_appTop]; rfl
  have hid : ∀ (b : Γ(U, ⊤)), (𝟙 U : U ⟶ U).appTop.hom b = b := fun b => by
    rw [Scheme.Hom.id_appTop]; rfl
  have hRet : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) [Etale f]
      (φ : Γ(Y, ⊤) →+* Γ(X, ⊤)), (∀ y, φ y = f.appTop.hom y) → φ.Etale := by
    intro X Y _ _ f _ φ hφ
    have : φ = f.appTop.hom := RingHom.ext hφ
    rw [this]
    exact HasRingHomProperty.appTop (P := @Etale) f inferInstance
  refine ⟨?_, ?_, ?_, ?_, ?_, hRet t _ hp₁, hRet s _ hp₂, hRet e₁₂ _ he₁₂, hRet e₂₃ _ he₂₃⟩
  · ext b; simp only [AlgHom.comp_apply, AlgHom.id_apply, hp₁, hδ, key, hδt, hid]
  · ext b; simp only [AlgHom.comp_apply, AlgHom.id_apply, hp₂, hδ, key, hδs, hid]
  · ext b; simp only [AlgHom.comp_apply, hp₁, he₁₂, he₁₃, key, h₁₂₁₃]
  · ext b; simp only [AlgHom.comp_apply, hp₁, hp₂, he₁₂, he₂₃, key, h₁₂₂₃]
  · ext b; simp only [AlgHom.comp_apply, hp₂, he₁₃, he₂₃, key, h₁₃₂₃]

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An algebraic space whose affine chart is the Čech nerve of a faithfully flat étale ring
map is affine.** Let `f : U → F` be a surjective étale chart of an algebraic space with kernel
pair `t, s : R ⇉ U`, `U` and `R` affine, and let `A₁ → Γ(U)` be faithfully flat and étale with
`Γ(U) ⊗[A₁] Γ(U) ≅ Γ(R)` carrying the two inclusions to `t^*` and `s^*`. Then `F` is
represented by `Spec A₁`. -/
theorem isAffineSpace_of_chart_tensor {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {U R : BigFppfOver B S hS} (f : yoneda.obj U ⟶ F)
    (t s : R ⟶ U) (hR : IsPullback (yoneda.map t) (yoneda.map s) f f)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hRa : IsAffine ((BigFppfOver.toScheme B S hS).obj R))
    (A₁ : Type u) [CommRing A₁] [Algebra A₁ Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)]
    [Algebra.Etale A₁ Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)]
    [Module.FaithfullyFlat A₁ Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)]
    (e : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ⊗[A₁]
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ≃+* Γ((BigFppfOver.toScheme B S hS).obj R, ⊤))
    (he₁ : ∀ b, e (b ⊗ₜ 1) = ((BigFppfOver.toScheme B S hS).map t).appTop.hom b)
    (he₂ : ∀ b, e (1 ⊗ₜ b) = ((BigFppfOver.toScheme B S hS).map s).appTop.hom b) :
    IsAffineSpace B S hS F := by
  have _ : IsAffine ((Over.post B.inclusion).obj U).left := hU
  have _ : IsAffine ((Over.post B.inclusion).obj R).left := hRa
  let : Algebra A₁ Γ(((Over.post B.inclusion).obj U).left, ⊤) := ‹_›
  have : Algebra.Etale A₁ Γ(((Over.post B.inclusion).obj U).left, ⊤) := ‹_›
  have : Module.FaithfullyFlat A₁ Γ(((Over.post B.inclusion).obj U).left, ⊤) := ‹_›
  obtain ⟨g, π, hfl, hlfp, hsu, hpb⟩ := exists_quotient_of_tensor_equiv S
    ((Over.post B.inclusion).map t) ((Over.post B.inclusion).map s) A₁ e he₁ he₂
  have := hfl
  have := hsu
  have hAcontains : B.Contains (Spec (CommRingCat.of A₁)) :=
    Scheme.size_lt_of_flat_of_surjective_of_isStrongPrelimit B.cutoff_isStrongPrelimit π.left
      U.left.2
  obtain ⟨m, e', -, -⟩ := exists_iso_yoneda_of_isPullback B S hS hF f t s hR hsurj hetale
    (U' := Over.mk (⟨g⟩ : B.obj hAcontains ⟶ B.obj hS)) π hfl hlfp hsu hpb
  exact ⟨_, inferInstanceAs (IsAffine (Spec (CommRingCat.of A₁))), ⟨e'⟩⟩

/-- **An algebraic space whose affine chart is a Čech nerve modulo `0` is affine.** The
geometric reading of `Module.Descent.IsNerveReduction … ⊥`: if the rings of functions
`Γ(U) ⇉ Γ(R) ⇉ D` of a surjective étale affine chart and its kernel pair, with `p₁ = t^*` and
`p₂ = s^*`, form a nerve modulo `0`, the space is affine. -/
theorem isAffineSpace_of_isNerveReduction_bot {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {U R : BigFppfOver B S hS} (f : yoneda.obj U ⟶ F)
    (t s : R ⟶ U) (hR : IsPullback (yoneda.map t) (yoneda.map s) f f)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hRa : IsAffine ((BigFppfOver.toScheme B S hS).obj R))
    {R' D : Type u} [CommRing R'] [CommRing D]
    [Algebra R' Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)]
    [Algebra R' Γ((BigFppfOver.toScheme B S hS).obj R, ⊤)] [Algebra R' D]
    (p₁ p₂ : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) →ₐ[R']
      Γ((BigFppfOver.toScheme B S hS).obj R, ⊤))
    (hp₁ : ∀ b, p₁ b = ((BigFppfOver.toScheme B S hS).map t).appTop.hom b)
    (hp₂ : ∀ b, p₂ b = ((BigFppfOver.toScheme B S hS).map s).appTop.hom b)
    {e₁₂ e₁₃ e₂₃ : Γ((BigFppfOver.toScheme B S hS).obj R, ⊤) →ₐ[R'] D}
    (h : Module.Descent.IsNerveReduction p₁ p₂ e₁₂ e₁₃ e₂₃ ⊥) :
    IsAffineSpace B S hS F := by
  obtain ⟨A₁, _, _, _, _, e, he₁, he₂⟩ := Module.Descent.IsNerveReduction.exists_tensor_equiv h
  exact isAffineSpace_of_chart_tensor B S hS hF f t s hR hsurj hetale hU hRa A₁ e
    (fun b => (he₁ b).trans (hp₁ b)) (fun b => (he₂ b).trans (hp₂ b))

end Space

end AlgebraicGeometry
