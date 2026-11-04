module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ChartNerveAffine

/-!
# The Čech nerve of an affine chart modulo a closed subspace

Let `U → W` be a surjective étale chart of an algebraic space with affine kernel pair
`t, s : R ⇉ U` and affine triple product `R ×_U R`, and let `Q → W` be a closed immersion from an
affine scheme. Then the rings of functions `Γ(U) ⇉ Γ(R) ⇉ Γ(R ×_U R)` form a Čech nerve modulo the
ideal `K_Q` of `U ×_W Q` in `Γ(U)` (`Module.Descent.IsNerveReduction`): reducing modulo `K_Q` gives
the rings of the chart `U ×_W Q → Q` of the affine scheme `Q`, which is the Čech nerve of the
faithfully flat étale ring map `Γ(Q) → Γ(U ×_W Q)`.

* `CommRingCat.surjective_and_ker_of_isPushout`: a pushout of a surjection of rings is a
  surjection, with kernel the extension of the kernel.
* `AlgebraicGeometry.surjective_and_ker_appTop_of_isPullback`: the restriction of functions to the
  base change of a closed immersion of affine schemes.
* `Module.Descent.isNerveReduction_of_surjections`: a diagram with compatible surjections onto a
  nerve modulo `0` is a nerve modulo the kernel.
* `AlgebraicGeometry.isNerveReduction_bot_of_isPullback`: the chart of an affine scheme (G2 at
  `Q = W`).
* `AlgebraicGeometry.isNerveReduction_of_isClosedImmersion`: the scheme-level form of G2.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace CommRingCat

/-- **A pushout of a surjection of rings is a surjection.** In a pushout square
`f : A → B`, `g : A → C`, `inl : B → P`, `inr : C → P` of commutative rings with `g` surjective,
`inl` is surjective with kernel the extension along `f` of the kernel of `g`. -/
theorem surjective_and_ker_of_isPushout {A B C P : CommRingCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P} (H : IsPushout f g inl inr) (hg : Function.Surjective g.hom) :
    Function.Surjective inl.hom ∧ RingHom.ker inl.hom = (RingHom.ker g.hom).map f.hom := by
  have hw : ∀ a, inl.hom (f.hom a) = inr.hom (g.hom a) := fun a => by
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← hom_comp, ← hom_comp, H.w]
  refine ⟨fun x => ?_, le_antisymm ?_ ?_⟩
  · have hle : Subring.closure (Set.range inl ∪ Set.range inr) ≤ inl.hom.range := by
      refine Subring.closure_le.2 (Set.union_subset ?_ ?_)
      · rintro _ ⟨y, rfl⟩
        exact ⟨y, rfl⟩
      · rintro _ ⟨c, rfl⟩
        obtain ⟨a, rfl⟩ := hg c
        exact ⟨f.hom a, hw a⟩
    rw [closure_range_union_range_eq_top_of_isPushout H] at hle
    exact hle (Subring.mem_top x)
  · let J := (RingHom.ker g.hom).map f.hom
    let ψ : C →+* B ⧸ J := (Ideal.Quotient.lift (RingHom.ker g.hom) ((Ideal.Quotient.mk J).comp
      f.hom) fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)).comp
      (RingHom.quotientKerEquivOfSurjective hg).symm.toRingHom
    have hψ : ∀ a, ψ (g.hom a) = Ideal.Quotient.mk J (f.hom a) := fun a => by
      have : (RingHom.quotientKerEquivOfSurjective hg).symm (g.hom a) =
          Ideal.Quotient.mk (RingHom.ker g.hom) a :=
        (RingEquiv.symm_apply_eq _).2 rfl
      simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this,
        Ideal.Quotient.lift_mk]
    let φ : P ⟶ of (B ⧸ J) := H.desc (ofHom (Ideal.Quotient.mk J)) (ofHom ψ) (by
      ext a; exact (hψ a).symm)
    intro x hx
    have h1 : φ.hom (inl.hom x) = Ideal.Quotient.mk J x := by
      rw [← RingHom.comp_apply, ← hom_comp, H.inl_desc]; rfl
    rw [RingHom.mem_ker.1 hx, map_zero] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 h1.symm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    show inl.hom (f.hom a) = 0
    rw [hw a, RingHom.mem_ker.1 ha, map_zero]

/-- **The tensor product of a pushout square is its corner.** If `fB : A → B`, `fC : A → C`,
`u : B → P`, `v : C → P` is a pushout square of rings and `B`, `C` are `A`-algebras through `fB`,
`fC`, then a ring map `B ⊗[A] C → P` with `b ⊗ c ↦ u b · v c` is bijective. -/
theorem bijective_of_isPushout {A B C P : CommRingCat.{u}} [Algebra A B] [Algebra A C]
    {fB : A ⟶ B} {fC : A ⟶ C} {u : B ⟶ P} {v : C ⟶ P} (H : IsPushout fB fC u v)
    (hB : algebraMap A B = fB.hom) (hC : algebraMap A C = fC.hom) (φ : B ⊗[A] C →+* P)
    (hφ : ∀ b c, φ (b ⊗ₜ c) = u b * v c) : Function.Bijective φ := by
  have H' : IsPushout (ofHom (algebraMap A B)) (ofHom (algebraMap A C)) u v := by
    rw [hB, hC]; exact H
  let e := (isPushout_tensorProduct A B C).isoIsPushout _ _ H'
  have heq : ∀ x, φ x = e.hom x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
      have h1 : e.hom (b ⊗ₜ 1) = u b :=
        congr($((isPushout_tensorProduct A B C).inl_isoIsPushout_hom _ _ H').hom b)
      have h2 : e.hom (1 ⊗ₜ c) = v c :=
        congr($((isPushout_tensorProduct A B C).inr_isoIsPushout_hom _ _ H').hom c)
      rw [hφ, ← h1, ← h2, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have : (φ : B ⊗[A] C → P) = e.commRingCatIsoToRingEquiv := funext heq
  rw [this]
  exact e.commRingCatIsoToRingEquiv.bijective

end CommRingCat

namespace Module.Descent

/-- **A diagram with compatible surjections onto a nerve modulo `0` is a nerve modulo the
kernel.** Let `qB : B → B'`, `qC : C → C'`, `qD : D → D'` be surjective with kernels `K`,
`p₁ K` and `e₁₂ p₁ K`, commuting with the two diagrams. If the primed diagram is a nerve modulo
`0`, the unprimed one is a nerve modulo `K`. -/
theorem isNerveReduction_of_surjections {R R'' : Type u} [CommRing R] [CommRing R'']
    {B C D B' C' D' : Type u} [CommRing B] [CommRing C] [CommRing D] [CommRing B'] [CommRing C']
    [CommRing D'] [Algebra R B] [Algebra R C] [Algebra R D] [Algebra R'' B'] [Algebra R'' C']
    [Algebra R'' D'] {p₁ p₂ : B →ₐ[R] C} {e₁₂ e₁₃ e₂₃ : C →ₐ[R] D}
    {p₁' p₂' : B' →ₐ[R''] C'} {e₁₂' e₁₃' e₂₃' : C' →ₐ[R''] D'}
    (qB : B →+* B') (qC : C →+* C') (qD : D →+* D') (hqB : Function.Surjective qB)
    (hqC : Function.Surjective qC) (hqD : Function.Surjective qD) (K : Ideal B)
    (hkB : RingHom.ker qB = K) (hkC : RingHom.ker qC = K.map (p₁ : B →+* C))
    (hkD : RingHom.ker qD = K.map ((e₁₂ : C →+* D).comp (p₁ : B →+* C)))
    (h₁ : ∀ b, qC (p₁ b) = p₁' (qB b)) (h₂ : ∀ b, qC (p₂ b) = p₂' (qB b))
    (h₁₂ : ∀ c, qD (e₁₂ c) = e₁₂' (qC c)) (h₁₃ : ∀ c, qD (e₁₃ c) = e₁₃' (qC c))
    (h₂₃ : ∀ c, qD (e₂₃ c) = e₂₃' (qC c))
    (h : IsNerveReduction p₁' p₂' e₁₂' e₁₃' e₂₃' ⊥) :
    IsNerveReduction p₁ p₂ e₁₂ e₁₃ e₂₃ K := by
  obtain ⟨A₁, B₁, _, _, _, hEt, hFF, πB, πC, πD, hsB, hsC, hsD, hkB', hkC', hkD',
    hC₁, hC₂, hD₁₂, hD₁₃, hD₂₃⟩ := h
  rw [Ideal.map_bot] at hkC' hkD'
  have hker : ∀ {X Y Z : Type u} [CommRing X] [CommRing Y] [CommRing Z] (q : X →+* Y)
      (π : Y →+* Z), RingHom.ker π = ⊥ → RingHom.ker (π.comp q) = RingHom.ker q := by
    intro X Y Z _ _ _ q π hπ
    rw [← RingHom.comap_ker, hπ, ← RingHom.ker_eq_comap_bot]
  refine ⟨A₁, B₁, inferInstance, inferInstance, inferInstance, hEt, hFF,
    πB.comp qB, πC.comp qC, πD.comp qD, hsB.comp hqB, hsC.comp hqC, hsD.comp hqD,
    (hker _ _ hkB').trans hkB, (hker _ _ hkC').trans hkC, (hker _ _ hkD').trans hkD,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact RingHom.ext fun b => by
      simpa only [RingHom.comp_apply, AlgHom.coe_toRingHom, h₁] using RingHom.congr_fun hC₁ (qB b)
  · exact RingHom.ext fun b => by
      simpa only [RingHom.comp_apply, AlgHom.coe_toRingHom, h₂] using RingHom.congr_fun hC₂ (qB b)
  · exact RingHom.ext fun c => by
      simpa only [RingHom.comp_apply, AlgHom.coe_toRingHom, h₁₂] using RingHom.congr_fun hD₁₂ (qC c)
  · exact RingHom.ext fun c => by
      simpa only [RingHom.comp_apply, AlgHom.coe_toRingHom, h₁₃] using RingHom.congr_fun hD₁₃ (qC c)
  · exact RingHom.ext fun c => by
      simpa only [RingHom.comp_apply, AlgHom.coe_toRingHom, h₂₃] using RingHom.congr_fun hD₂₃ (qC c)

end Module.Descent

namespace AlgebraicGeometry

/-- **Functions on the base change of a closed immersion of affine schemes.** In a pullback
square `X' = X ×_Y Y'` of schemes with `X`, `Y`, `Y'` affine and `i : Y' → Y` a closed
immersion, the restriction `Γ(X) → Γ(X')` is surjective with kernel the extension of the kernel
of `Γ(Y) → Γ(Y')`. -/
theorem surjective_and_ker_appTop_of_isPullback {X Y X' Y' : Scheme.{u}} [IsAffine X]
    [IsAffine Y] [IsAffine Y'] {i' : X' ⟶ X} {g' : X' ⟶ Y'} {g : X ⟶ Y} {i : Y' ⟶ Y}
    (h : IsPullback i' g' g i) [IsClosedImmersion i] :
    Function.Surjective i'.appTop.hom ∧
      RingHom.ker i'.appTop.hom = (RingHom.ker i.appTop.hom).map g.appTop.hom :=
  CommRingCat.surjective_and_ker_of_isPushout (isPushout_appTop_of_isPullback h)
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2

/-- Pulling functions back along `g` then `f` is pulling back along `f ≫ g`. -/
theorem appTop_appTop {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (z : Γ(Z, ⊤)) :
    f.appTop.hom (g.appTop.hom z) = (f ≫ g).appTop.hom z := by
  rw [Scheme.Hom.comp_appTop]; rfl

/-- Two composites of pullbacks of functions agree when the composites of morphisms agree. -/
private theorem appTop_appTop_eq {X Y Y' Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X ⟶ Y'}
    {g' : Y' ⟶ Z} (h : f ≫ g = f' ≫ g') (z : Γ(Z, ⊤)) :
    f.appTop.hom (g.appTop.hom z) = f'.appTop.hom (g'.appTop.hom z) := by
  rw [appTop_appTop, appTop_appTop, h]

/-- **The chart of an affine scheme is a Čech nerve modulo `0` (G2 for `Q = W`).** Let
`g : U₀ → T` be a surjective étale morphism of affine schemes, `tQ, sQ : R₀ ⇉ U₀` its kernel
pair and `e₁₂, e₂₃ : W₀ ⇉ R₀` the fibre product `R₀ ×_{sQ, U₀, tQ} R₀`, with `e₁₃ : W₀ → R₀`
satisfying the coface identities. Then the rings of functions form a nerve modulo `0`. -/
theorem isNerveReduction_bot_of_isPullback {T U₀ R₀ W₀ : Scheme.{u}} [IsAffine T] [IsAffine U₀]
    [IsAffine R₀] [IsAffine W₀] (g : U₀ ⟶ T) [Etale g] [Surjective g] {tQ sQ : R₀ ⟶ U₀}
    (hR : IsPullback tQ sQ g g) {e₁₂ e₁₃ e₂₃ : W₀ ⟶ R₀} (hW : IsPullback e₁₂ e₂₃ sQ tQ)
    (h₁₂₁₃ : e₁₂ ≫ tQ = e₁₃ ≫ tQ) (h₁₃₂₃ : e₁₃ ≫ sQ = e₂₃ ≫ sQ)
    {R'' : Type u} [CommRing R''] [Algebra R'' Γ(U₀, ⊤)] [Algebra R'' Γ(R₀, ⊤)]
    [Algebra R'' Γ(W₀, ⊤)] (p₁ p₂ : Γ(U₀, ⊤) →ₐ[R''] Γ(R₀, ⊤))
    (f₁₂ f₁₃ f₂₃ : Γ(R₀, ⊤) →ₐ[R''] Γ(W₀, ⊤))
    (hp₁ : ∀ b, p₁ b = tQ.appTop.hom b) (hp₂ : ∀ b, p₂ b = sQ.appTop.hom b)
    (hf₁₂ : ∀ c, f₁₂ c = e₁₂.appTop.hom c) (hf₁₃ : ∀ c, f₁₃ c = e₁₃.appTop.hom c)
    (hf₂₃ : ∀ c, f₂₃ c = e₂₃.appTop.hom c) :
    Module.Descent.IsNerveReduction p₁ p₂ f₁₂ f₁₃ f₂₃ ⊥ := by
  let : Algebra Γ(T, ⊤) Γ(U₀, ⊤) := g.appTop.hom.toAlgebra
  let : Algebra Γ(T, ⊤) Γ(R₀, ⊤) := (tQ ≫ g).appTop.hom.toAlgebra
  let : Algebra Γ(T, ⊤) Γ(W₀, ⊤) := (e₁₂ ≫ tQ ≫ g).appTop.hom.toAlgebra
  have hsg : sQ ≫ g = tQ ≫ g := hR.w.symm
  have h13 : e₁₃ ≫ tQ ≫ g = e₁₂ ≫ tQ ≫ g := by
    rw [← Category.assoc, ← h₁₂₁₃, Category.assoc]
  have h23 : e₂₃ ≫ tQ ≫ g = e₁₂ ≫ tQ ≫ g := by
    rw [← Category.assoc, ← hW.w, Category.assoc, hsg]
  have c₂ : ∀ a, sQ.appTop.hom (g.appTop.hom a) = (tQ ≫ g).appTop.hom a := fun a => by
    rw [appTop_appTop, hsg]
  have c₁₃ : ∀ a, e₁₃.appTop.hom ((tQ ≫ g).appTop.hom a) = (e₁₂ ≫ tQ ≫ g).appTop.hom a :=
    fun a => by rw [appTop_appTop, h13]
  have c₂₃ : ∀ a, e₂₃.appTop.hom ((tQ ≫ g).appTop.hom a) = (e₁₂ ≫ tQ ≫ g).appTop.hom a :=
    fun a => by rw [appTop_appTop, h23]
  let p₁' : Γ(U₀, ⊤) →ₐ[Γ(T, ⊤)] Γ(R₀, ⊤) :=
    { tQ.appTop.hom with commutes' := fun a => appTop_appTop tQ g a }
  let p₂' : Γ(U₀, ⊤) →ₐ[Γ(T, ⊤)] Γ(R₀, ⊤) := { sQ.appTop.hom with commutes' := c₂ }
  let e₁₂' : Γ(R₀, ⊤) →ₐ[Γ(T, ⊤)] Γ(W₀, ⊤) :=
    { e₁₂.appTop.hom with commutes' := fun a => appTop_appTop e₁₂ (tQ ≫ g) a }
  let e₁₃' : Γ(R₀, ⊤) →ₐ[Γ(T, ⊤)] Γ(W₀, ⊤) := { e₁₃.appTop.hom with commutes' := c₁₃ }
  let e₂₃' : Γ(R₀, ⊤) →ₐ[Γ(T, ⊤)] Γ(W₀, ⊤) := { e₂₃.appTop.hom with commutes' := c₂₃ }
  have : Algebra.Etale Γ(T, ⊤) Γ(U₀, ⊤) :=
    RingHom.etale_algebraMap.1 (HasRingHomProperty.appTop (P := @Etale) g inferInstance)
  have : Module.FaithfullyFlat Γ(T, ⊤) Γ(U₀, ⊤) :=
    RingHom.faithfullyFlat_algebraMap_iff.1
      ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).1 ⟨inferInstance, inferInstance⟩)
  refine Module.Descent.isNerveReduction_bot_of_bijective _ _ _ _ _ p₁' p₂' e₁₂' e₁₃' e₂₃'
    (fun b => (hp₁ b).symm) (fun b => (hp₂ b).symm) (fun c => (hf₁₂ c).symm)
    (fun c => (hf₁₃ c).symm) (fun c => (hf₂₃ c).symm) ?_ ?_ ?_ ?_ ?_
  · refine AlgHom.ext fun b => ?_
    exact appTop_appTop_eq h₁₂₁₃ b
  · refine AlgHom.ext fun b => ?_
    exact appTop_appTop_eq hW.w b
  · refine AlgHom.ext fun b => ?_
    exact appTop_appTop_eq h₁₃₂₃ b
  · exact CommRingCat.bijective_of_isPushout (isPushout_appTop_of_isPullback hR) rfl rfl
      (Module.Descent.chartMap p₁' p₂' (AlgHom.id _ _)).toRingHom fun b c => by
        simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Module.Descent.chartMap_tmul,
          AlgHom.id_apply]
        rfl
  · have hP : IsPullback (e₁₂ ≫ tQ) e₂₃ g (tQ ≫ g) := (hW.flip.paste_vert hR.flip).flip
    exact CommRingCat.bijective_of_isPushout (isPushout_appTop_of_isPullback hP) rfl rfl
      (Module.Descent.tripleMap p₁' e₁₂' e₂₃' (AlgHom.id _ _)).toRingHom fun b c => by
        simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Module.Descent.tripleMap_tmul,
          AlgHom.id_apply]
        show e₁₂.appTop.hom (tQ.appTop.hom b) * _ = _
        rw [appTop_appTop]
        rfl

/-- **The Čech nerve of an affine chart modulo a closed subscheme of the chart (G2, scheme
level).** Let `t, s : R ⇉ U` and `e₁₂, e₁₃, e₂₃ : W ⇉ R` be morphisms of affine schemes, let
`i : U₀ → U` be a closed immersion and `g : U₀ → T` a surjective étale morphism to an affine
scheme. Suppose `R₀ = R ×_{t, U} U₀` (with projections `r`, `tQ`), that `sQ : R₀ → U₀` lifts
`r ≫ s` and makes `tQ, sQ` the kernel pair of `g`, that `W₀ = W ×_{e₁₂, R} R₀` (with projections
`w`, `e₁₂Q`), and that `e₁₃Q, e₂₃Q : W₀ → R₀` lift `w ≫ e₁₃`, `w ≫ e₂₃` with `W₀` the fibre
product `R₀ ×_{sQ, U₀, tQ} R₀` and the coface identities. Then the rings of functions of `U`,
`R`, `W` form a nerve modulo the kernel of `Γ(U) → Γ(U₀)`. -/
theorem isNerveReduction_of_isClosedImmersion {U R W U₀ R₀ W₀ T : Scheme.{u}} [IsAffine U]
    [IsAffine R] [IsAffine W] [IsAffine U₀] [IsAffine R₀] [IsAffine W₀] [IsAffine T]
    {t s : R ⟶ U} {e₁₂ e₁₃ e₂₃ : W ⟶ R} (i : U₀ ⟶ U) [IsClosedImmersion i] (g : U₀ ⟶ T)
    [Etale g] [Surjective g] {r : R₀ ⟶ R} {tQ sQ : R₀ ⟶ U₀} {w : W₀ ⟶ W}
    {e₁₂Q e₁₃Q e₂₃Q : W₀ ⟶ R₀} (hr : IsPullback r tQ t i) (hsQ : sQ ≫ i = r ≫ s)
    (hRQ : IsPullback tQ sQ g g) (hw : IsPullback w e₁₂Q e₁₂ r)
    (hWQ : IsPullback e₁₂Q e₂₃Q sQ tQ) (h₁₃ : e₁₃Q ≫ r = w ≫ e₁₃) (h₂₃ : e₂₃Q ≫ r = w ≫ e₂₃)
    (h₁₂₁₃Q : e₁₂Q ≫ tQ = e₁₃Q ≫ tQ) (h₁₃₂₃Q : e₁₃Q ≫ sQ = e₂₃Q ≫ sQ)
    {R' : Type u} [CommRing R'] [Algebra R' Γ(U, ⊤)] [Algebra R' Γ(R, ⊤)] [Algebra R' Γ(W, ⊤)]
    (p₁ p₂ : Γ(U, ⊤) →ₐ[R'] Γ(R, ⊤)) (e₁₂' e₁₃' e₂₃' : Γ(R, ⊤) →ₐ[R'] Γ(W, ⊤))
    (hp₁ : ∀ b, p₁ b = t.appTop.hom b) (hp₂ : ∀ b, p₂ b = s.appTop.hom b)
    (he₁₂ : ∀ c, e₁₂' c = e₁₂.appTop.hom c) (he₁₃ : ∀ c, e₁₃' c = e₁₃.appTop.hom c)
    (he₂₃ : ∀ c, e₂₃' c = e₂₃.appTop.hom c) :
    Module.Descent.IsNerveReduction p₁ p₂ e₁₂' e₁₃' e₂₃' (RingHom.ker i.appTop.hom) := by
  obtain ⟨hsC, hkC⟩ := surjective_and_ker_appTop_of_isPullback hr
  obtain ⟨hsD, hkD⟩ := surjective_and_ker_appTop_of_isPullback (hw.paste_vert hr)
  have hp₁' : (p₁ : Γ(U, ⊤) →+* Γ(R, ⊤)) = t.appTop.hom := RingHom.ext hp₁
  have hpe : ((e₁₂' : Γ(R, ⊤) →+* Γ(W, ⊤)).comp (p₁ : Γ(U, ⊤) →+* Γ(R, ⊤))) =
      (e₁₂ ≫ t).appTop.hom := RingHom.ext fun b => by
    simp only [RingHom.comp_apply, AlgHom.coe_toRingHom, hp₁, he₁₂, appTop_appTop]
  have c₁ : ∀ b, r.appTop.hom (p₁ b) = tQ.appTop.hom (i.appTop.hom b) := fun b => by
    rw [hp₁]; exact appTop_appTop_eq hr.w b
  have c₂ : ∀ b, r.appTop.hom (p₂ b) = sQ.appTop.hom (i.appTop.hom b) := fun b => by
    rw [hp₂]; exact (appTop_appTop_eq hsQ b).symm
  have c₁₂ : ∀ c, w.appTop.hom (e₁₂' c) = e₁₂Q.appTop.hom (r.appTop.hom c) := fun c => by
    rw [he₁₂]; exact appTop_appTop_eq hw.w c
  have c₁₃ : ∀ c, w.appTop.hom (e₁₃' c) = e₁₃Q.appTop.hom (r.appTop.hom c) := fun c => by
    rw [he₁₃]; exact (appTop_appTop_eq h₁₃ c).symm
  have c₂₃ : ∀ c, w.appTop.hom (e₂₃' c) = e₂₃Q.appTop.hom (r.appTop.hom c) := fun c => by
    rw [he₂₃]; exact (appTop_appTop_eq h₂₃ c).symm
  let : Algebra R' Γ(U₀, ⊤) := (i.appTop.hom.comp (algebraMap R' Γ(U, ⊤))).toAlgebra
  let : Algebra R' Γ(R₀, ⊤) := (r.appTop.hom.comp (algebraMap R' Γ(R, ⊤))).toAlgebra
  let : Algebra R' Γ(W₀, ⊤) := (w.appTop.hom.comp (algebraMap R' Γ(W, ⊤))).toAlgebra
  let q₁ : Γ(U₀, ⊤) →ₐ[R'] Γ(R₀, ⊤) :=
    { tQ.appTop.hom with commutes' := fun a => (c₁ _).symm.trans (congrArg _ (p₁.commutes a)) }
  let q₂ : Γ(U₀, ⊤) →ₐ[R'] Γ(R₀, ⊤) :=
    { sQ.appTop.hom with commutes' := fun a => (c₂ _).symm.trans (congrArg _ (p₂.commutes a)) }
  let f₁₂ : Γ(R₀, ⊤) →ₐ[R'] Γ(W₀, ⊤) :=
    { e₁₂Q.appTop.hom with
      commutes' := fun a => (c₁₂ _).symm.trans (congrArg _ (e₁₂'.commutes a)) }
  let f₁₃ : Γ(R₀, ⊤) →ₐ[R'] Γ(W₀, ⊤) :=
    { e₁₃Q.appTop.hom with
      commutes' := fun a => (c₁₃ _).symm.trans (congrArg _ (e₁₃'.commutes a)) }
  let f₂₃ : Γ(R₀, ⊤) →ₐ[R'] Γ(W₀, ⊤) :=
    { e₂₃Q.appTop.hom with
      commutes' := fun a => (c₂₃ _).symm.trans (congrArg _ (e₂₃'.commutes a)) }
  exact Module.Descent.isNerveReduction_of_surjections (p₁' := q₁) (p₂' := q₂) (e₁₂' := f₁₂)
    (e₁₃' := f₁₃) (e₂₃' := f₂₃) i.appTop.hom r.appTop.hom w.appTop.hom
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2 hsC hsD _ rfl (by rw [hkC, hp₁'])
    (by rw [hkD, hpe]) c₁ c₂ c₁₂ c₁₃ c₂₃
    (isNerveReduction_bot_of_isPullback g hRQ hWQ h₁₂₁₃Q h₁₃₂₃Q q₁ q₂ f₁₂ f₁₃ f₂₃
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))

end AlgebraicGeometry
