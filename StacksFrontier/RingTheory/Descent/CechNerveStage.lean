module

public import StacksFrontier.RingTheory.Descent.CechNerveModel

/-!
# A Čech nerve modulo a nil ideal is a nerve modulo some stage of a directed family

Let `p₁, p₂ : B → C`, `δ`, `e₁₂, e₁₃, e₂₃ : C → D` be the first terms of the Čech nerve of a
surjective étale chart `U → P` of an algebraic space, let `(K i)` be a directed family of
invariant ideals of `B` whose union `I` is nil. If the diagram is a nerve modulo `I` (the closed
subspace of `P` cut out by `I` is affine) then it is a nerve modulo some `K i`
(`Module.Descent.exists_isNerveReduction_of_iSup`).

## The argument

Write `A_i` for the ring of invariant functions on the reduction of `U` modulo `K i`
(`Module.Descent.stageEq`) and `A₁ → B₁` for the faithfully flat étale cover of the closed
subspace cut out by `I`. The rings `A_i` form a directed system with colimit `A₁`: every function
on the closed subspace is an invariant function modulo `I`, hence modulo some `K i`, and an
invariant function vanishing modulo `I` vanishes modulo some `K i`. A standard étale presentation
of `B₁` over `A₁` descends to a faithfully flat étale `A_i`-algebra `S` with `A₁ ⊗[A_i] S ≅ B₁`
(`Algebra.Etale.exists_model_of_directed`, from Stacks 00U9 and the limit lemmas of
`StacksFrontier.RingTheory.Etale.DirectedColimitPresentation`). The reduction of the diagram modulo
`K i` is then a nerve modulo the nil ideal `I` with the étale model `S`, hence a nerve
(`Module.Descent.isNerveReduction_bot_of_model`).
-/

@[expose] public section

universe u v w

open TensorProduct

/-- **An étale cover of a directed colimit descends to a stage.** Let `A` be the colimit of a
directed system of rings `(G i)` and `B` a faithfully flat étale `A`-algebra. Then for some `i`
there is a faithfully flat étale `G i`-algebra `S` with `A ⊗[G i] S ≅ B`. -/
theorem Algebra.Etale.exists_model_of_directed {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    [Nonempty ι] {G : ι → Type v} [∀ i, CommRing (G i)] {f : ∀ i j, i ≤ j → G i →+* G j}
    [DirectedSystem G fun i j h ↦ f i j h] {A : Type w} [CommRing A] {φ : ∀ i, G i →+* A}
    (hφ : ∀ i j (h : i ≤ j) (x : G i), φ j (f i j h x) = φ i x)
    (hsurj : ∀ a : A, ∃ (i : ι) (x : G i), φ i x = a)
    (hzero : ∀ (i : ι) (x : G i), φ i x = 0 → ∃ (j : ι) (h : i ≤ j), f i j h x = 0)
    (B : Type*) [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.FaithfullyFlat A B] :
    ∃ (i : ι) (S : Type v) (_ : CommRing S) (_ : Algebra (G i) S),
      Algebra.Etale (G i) S ∧ Module.FaithfullyFlat (G i) S ∧
      letI := (φ i).toAlgebra
      Nonempty (A ⊗[G i] S ≃ₐ[A] B) := by
  classical
  obtain ⟨κ, _, _, g, hg, ⟨E⟩⟩ := Algebra.Etale.exists_square_presentation A B
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨i, -, q, hq⟩ := MvPolynomial.exists_ge_forall_map_eq_square_of_directed hφ hsurj g i₀
  have hφc : ∀ i j (h : i ≤ j), (φ j).comp (f i j h) = φ i := fun i j h =>
    RingHom.ext (hφ i j h)
  have hq' : (fun k => MvPolynomial.map (φ i) (q k)) = g := funext hq
  obtain ⟨j, hij, hj⟩ := MvPolynomial.exists_ge_etale_quotient_of_directed hφ hsurj hzero q
    (by rw [hq']; exact hg)
  set q₁ : κ → MvPolynomial κ (G j) := fun k => MvPolynomial.map (f i j hij) (q k) with hq₁def
  have hq₁ : ∀ k, MvPolynomial.map (φ j) (q₁ k) = g k := fun k => by
    rw [hq₁def, MvPolynomial.map_map, hφc, hq]
  have hle : Ideal.span (Set.range q₁) ≤
      (Ideal.span (Set.range g)).comap (MvPolynomial.map (φ j)) := by
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, hq₁]
    exact Ideal.subset_span ⟨k, rfl⟩
  let θ : (MvPolynomial κ (G j) ⧸ Ideal.span (Set.range q₁)) →+* B :=
    (E : _ →+* B).comp (Ideal.quotientMap _ (MvPolynomial.map (φ j)) hle)
  have hcomm : (algebraMap A B).comp (φ j) =
      θ.comp (algebraMap (G j) (MvPolynomial κ (G j) ⧸ Ideal.span (Set.range q₁))) := by
    refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply, θ, RingHom.coe_coe]
    rw [IsScalarTower.algebraMap_apply (G j) (MvPolynomial κ (G j))
      (MvPolynomial κ (G j) ⧸ Ideal.span (Set.range q₁)) x, Ideal.Quotient.algebraMap_eq,
      MvPolynomial.algebraMap_eq, Ideal.quotientMap_mk, MvPolynomial.map_C,
      ← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap, E.commutes]
  obtain ⟨k, hjk, hk⟩ := MvPolynomial.exists_ge_surjective_comap_quotient_of_directed hφ hsurj
    hzero q₁ (algebraMap A B) θ hcomm (PrimeSpectrum.comap_surjective_of_faithfullyFlat)
  set q₂ : κ → MvPolynomial κ (G k) := fun l => MvPolynomial.map (f j k hjk) (q₁ l) with hq₂def
  have hq₂ : ∀ l, MvPolynomial.map (φ k) (q₂ l) = g l := fun l => by
    rw [hq₂def, MvPolynomial.map_map, hφc, hq₁]
  let S := MvPolynomial κ (G k) ⧸ Ideal.span (Set.range q₂)
  have hSet : Algebra.Etale (G k) S := by
    let := (f j k hjk).toAlgebra
    obtain ⟨e⟩ := MvPolynomial.nonempty_quotientSpanEquiv_tensor_of_le hjk q₁
    exact Algebra.Etale.of_equiv e
  refine ⟨k, S, inferInstance, inferInstance, hSet,
    Module.FaithfullyFlat.of_comap_surjective hk, ?_⟩
  let := (φ k).toAlgebra
  obtain ⟨e⟩ := MvPolynomial.nonempty_quotientSpanEquiv_tensor_of_directed (φ := φ) q₂
  exact ⟨e.trans ((Ideal.quotientEquivAlgOfEq A (by rw [funext hq₂])).trans E)⟩

namespace Module.Descent

/-- A ring map onto the image of an injective ring map factors through it. -/
noncomputable def liftOfRange {X A₁ B₁ : Type*} [CommRing X] [CommRing A₁] [CommRing B₁]
    (j : A₁ →+* B₁) (hj : Function.Injective j) (π : X →+* B₁) (h : ∀ x, π x ∈ j.range) :
    X →+* A₁ :=
  ((RingEquiv.ofBijective j.rangeRestrict
    ⟨fun _ _ hxy => hj (congrArg Subtype.val hxy), j.rangeRestrict_surjective⟩).symm :
      j.range →+* A₁).comp (π.codRestrict j.range h)

/-- Composing `liftOfRange j hj π h` with `j` recovers `π`. -/
theorem liftOfRange_spec {X A₁ B₁ : Type*} [CommRing X] [CommRing A₁] [CommRing B₁]
    (j : A₁ →+* B₁) (hj : Function.Injective j) (π : X →+* B₁) (h : ∀ x, π x ∈ j.range)
    (x : X) : j (liftOfRange j hj π h x) = π x := by
  have := congrArg Subtype.val ((RingEquiv.ofBijective j.rangeRestrict
    ⟨fun _ _ hxy => hj (congrArg Subtype.val hxy), j.rangeRestrict_surjective⟩).apply_symm_apply
      (π.codRestrict j.range h x))
  exact this

section Nerve

variable {R : Type u} [CommRing R] {B C D : Type u} [CommRing B] [CommRing C] [CommRing D]
  [Algebra R B] [Algebra R C] [Algebra R D] (p₁ p₂ : B →ₐ[R] C)

/-- The ring of invariant functions on the reduction of the chart modulo an invariant ideal `K`:
the equalizer of the two reduced projections. -/
noncomputable def stageEq (K : Ideal B) (hK : K.map (p₁ : B →+* C) = K.map (p₂ : B →+* C)) :
    Subalgebra R (B ⧸ K) :=
  AlgHom.equalizer (nerveQuotP₁ p₁ K) (nerveQuotP₂ p₁ p₂ K hK)

variable {p₁ p₂}

/-- The class of `b` modulo `K` is an invariant function exactly when `p₁ b - p₂ b` lies in the
extension of `K` along `p₁`. -/
theorem mem_stageEq_mk {K : Ideal B} (hK : K.map (p₁ : B →+* C) = K.map (p₂ : B →+* C))
    (b : B) : Ideal.Quotient.mk K b ∈ stageEq p₁ p₂ K hK ↔ p₁ b - p₂ b ∈ K.map (p₁ : B →+* C) := by
  rw [stageEq, AlgHom.mem_equalizer, nerveQuotP₁_mk, nerveQuotP₂_mk, Ideal.Quotient.eq]

/-- The transition map between rings of invariant functions for `K ≤ K'`. -/
noncomputable def stageMap {K K' : Ideal B} (hK : K.map (p₁ : B →+* C) = K.map (p₂ : B →+* C))
    (hK' : K'.map (p₁ : B →+* C) = K'.map (p₂ : B →+* C)) (h : K ≤ K') :
    stageEq p₁ p₂ K hK →+* stageEq p₁ p₂ K' hK' :=
  ((Ideal.Quotient.factor h).comp (stageEq p₁ p₂ K hK).val.toRingHom).codRestrict _
    (fun ⟨x, hx⟩ => by
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.factor h (Ideal.Quotient.mk K b) ∈ _
      rw [Ideal.Quotient.factor_mk, mem_stageEq_mk]
      exact Ideal.map_mono h ((mem_stageEq_mk hK b).1 hx))

/-- The transition map `stageMap` is the factor map `B ⧸ K → B ⧸ K'` on underlying elements. -/
theorem stageMap_coe {K K' : Ideal B} (hK : K.map (p₁ : B →+* C) = K.map (p₂ : B →+* C))
    (hK' : K'.map (p₁ : B →+* C) = K'.map (p₂ : B →+* C)) (h : K ≤ K')
    (x : stageEq p₁ p₂ K hK) :
    (stageMap hK hK' h x : B ⧸ K') = Ideal.Quotient.factor h x := rfl

variable {e₁₂ : C →ₐ[R] D}

/-- **A model at a stage gives a nerve at that stage.** Let the diagram be a nerve modulo an
invariant nil ideal `I`, witnessed by `πB`, `πC`, `πD` over `A₁`, and let `K' ≤ I` be invariant.
If the ring `A'` of invariant functions modulo `K'` maps to `A₁` compatibly with `πB` and
`B₁ ≅ A₁ ⊗[A'] S` for a faithfully flat étale `A'`-algebra `S`, the diagram is a nerve modulo
`K'`. -/
theorem isNerveReduction_of_stage_model (δ : C →ₐ[R] B) (e₁₃ e₂₃ : C →ₐ[R] D)
    (hδ₁ : δ.comp p₁ = AlgHom.id R B) (hδ₂ : δ.comp p₂ = AlgHom.id R B)
    (h₁₂₁₃ : e₁₂.comp p₁ = e₁₃.comp p₁) (h₁₂₂₃ : e₁₂.comp p₂ = e₂₃.comp p₁)
    (h₁₃₂₃ : e₁₃.comp p₂ = e₂₃.comp p₂)
    (hp₁ : (p₁ : B →+* C).Etale) (hp₂ : (p₂ : B →+* C).Etale)
    (he₁₂ : (e₁₂ : C →+* D).Etale) (he₂₃ : (e₂₃ : C →+* D).Etale)
    (I : Ideal B) (hI : I.map (p₁ : B →+* C) = I.map (p₂ : B →+* C)) (hIn : I ≤ nilradical B)
    (K' : Ideal B) (hK' : K'.map (p₁ : B →+* C) = K'.map (p₂ : B →+* C)) (hK'I : K' ≤ I)
    {A₁ B₁ : Type*} [CommRing A₁] [CommRing B₁] [Algebra A₁ B₁]
    (πB : B →+* B₁) (πC : C →+* B₁ ⊗[A₁] B₁) (πD : D →+* B₁ ⊗[A₁] (B₁ ⊗[A₁] B₁))
    (hsB : Function.Surjective πB) (hsC : Function.Surjective πC)
    (hkB : RingHom.ker πB = I) (hkC : RingHom.ker πC = I.map (p₁ : B →+* C))
    (hkD : RingHom.ker πD = I.map ((e₁₂ : C →+* D).comp (p₁ : B →+* C)))
    (hC₁ : πC.comp (p₁ : B →+* C) =
        (Algebra.TensorProduct.includeLeft : B₁ →ₐ[A₁] B₁ ⊗[A₁] B₁).toRingHom.comp πB)
    (hC₂ : πC.comp (p₂ : B →+* C) =
        (Algebra.TensorProduct.includeRight : B₁ →ₐ[A₁] B₁ ⊗[A₁] B₁).toRingHom.comp πB)
    (hD₁₂ : πD.comp (e₁₂ : C →+* D) = (Algebra.TensorProduct.map (AlgHom.id A₁ B₁)
        (Algebra.TensorProduct.includeLeft : B₁ →ₐ[A₁] B₁ ⊗[A₁] B₁)).toRingHom.comp πC)
    (hD₂₃ : πD.comp (e₂₃ : C →+* D) = (Algebra.TensorProduct.includeRight :
        B₁ ⊗[A₁] B₁ →ₐ[A₁] B₁ ⊗[A₁] (B₁ ⊗[A₁] B₁)).toRingHom.comp πC)
    [Algebra (stageEq p₁ p₂ K' hK') A₁]
    (hρ : ∀ a : stageEq p₁ p₂ K' hK', algebraMap A₁ B₁ (algebraMap _ A₁ a) =
      Ideal.Quotient.lift K' πB (fun x hx => by rw [← RingHom.mem_ker, hkB]; exact hK'I hx) a)
    (S : Type u) [CommRing S] [Algebra (stageEq p₁ p₂ K' hK') S]
    [Algebra.Etale (stageEq p₁ p₂ K' hK') S] [Module.FaithfullyFlat (stageEq p₁ p₂ K' hK') S]
    (e : A₁ ⊗[stageEq p₁ p₂ K' hK'] S ≃ₐ[A₁] B₁) :
    IsNerveReduction p₁ p₂ e₁₂ e₁₃ e₂₃ K' := by
  obtain ⟨hq₁, hq₂, hq₃, hq₄, hq₅, -, hqp₂, -, hqe₂₃⟩ :=
    nerveQuot_identities hδ₁ hδ₂ h₁₂₁₃ h₁₂₂₃ h₁₃₂₃ hp₁ hp₂ he₁₂ he₂₃ hK'
  refine isNerveReduction_of_quot_bot h₁₂₁₃ h₁₂₂₃ hK' ?_
  have HC : ∀ a ∈ K'.map (p₁ : B →+* C), πC a = 0 := fun _ ha =>
    hkC.ge (Ideal.map_mono hK'I ha)
  have HD : ∀ a ∈ K'.map ((e₁₂ : C →+* D).comp (p₁ : B →+* C)), πD a = 0 := fun _ ha =>
    hkD.ge (Ideal.map_mono hK'I ha)
  have hmapC : ∀ (J : Ideal B) (f : B →ₐ[R] C) (g : B ⧸ K' →+* C ⧸ K'.map (p₁ : B →+* C)),
      (∀ b, g (Ideal.Quotient.mk K' b) = Ideal.Quotient.mk _ (f b)) →
      (J.map (Ideal.Quotient.mk K')).map g =
        (J.map (f : B →+* C)).map (Ideal.Quotient.mk (K'.map (p₁ : B →+* C))) := by
    intro J f g hg
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    exact RingHom.ext hg
  refine isNerveReduction_bot_of_model _ _ (nerveQuotδ p₁ K' δ hδ₁) _ _ _ hq₁ hq₂ hq₃ hq₄ hq₅
    hqp₂ hqe₂₃ (I.map (Ideal.Quotient.mk K')) ?_
    (Ideal.map_le_nilradical_of_le_nilradical _ hIn)
    (Ideal.Quotient.lift K' πB fun x hx => by rw [← RingHom.mem_ker, hkB]; exact hK'I hx)
    (Ideal.Quotient.lift _ πC HC) (Ideal.Quotient.lift _ πD HD)
    (Ideal.Quotient.lift_surjective_of_surjective _ _ hsB)
    (Ideal.Quotient.lift_surjective_of_surjective _ _ hsC) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (stageEq p₁ p₂ K' hK') (fun _ => Iff.rfl) hρ S e
  · rw [hmapC I p₁ _ (fun _ => rfl), hmapC I p₂ _ (fun _ => rfl), hI]
  · rw [ker_lift_eq, hkB]
  · rw [ker_lift_eq, hkC, hmapC I p₁ _ (fun _ => rfl)]
  · rw [ker_lift_eq, hkD, Ideal.map_map, Ideal.map_map]
    exact le_of_eq (congrArg (I.map ·) (RingHom.ext fun _ => rfl))
  · exact Ideal.Quotient.ringHom_ext (RingHom.ext (RingHom.congr_fun hC₁))
  · exact Ideal.Quotient.ringHom_ext (RingHom.ext (RingHom.congr_fun hC₂))
  · exact Ideal.Quotient.ringHom_ext (RingHom.ext (RingHom.congr_fun hD₁₂))
  · exact Ideal.Quotient.ringHom_ext (RingHom.ext (RingHom.congr_fun hD₂₃))

/-- **A Čech nerve modulo a nil ideal is a nerve modulo a stage of a directed family.** Let
`(K i)` be a directed family of invariant ideals of `B` whose supremum `I` is nil. If the Čech
nerve is a nerve modulo `I`, it is a nerve modulo some `K i`. Geometrically: if the closed
subspace of `P` cut out by `I` is affine, so is the one cut out by some `K i`. -/
theorem exists_isNerveReduction_of_iSup (δ : C →ₐ[R] B) (e₁₃ e₂₃ : C →ₐ[R] D)
    (hδ₁ : δ.comp p₁ = AlgHom.id R B) (hδ₂ : δ.comp p₂ = AlgHom.id R B)
    (h₁₂₁₃ : e₁₂.comp p₁ = e₁₃.comp p₁) (h₁₂₂₃ : e₁₂.comp p₂ = e₂₃.comp p₁)
    (h₁₃₂₃ : e₁₃.comp p₂ = e₂₃.comp p₂)
    (hp₁ : (p₁ : B →+* C).Etale) (hp₂ : (p₂ : B →+* C).Etale)
    (he₁₂ : (e₁₂ : C →+* D).Etale) (he₂₃ : (e₂₃ : C →+* D).Etale)
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (K : ι → Ideal B)
    (hKm : Monotone K) (hKinv : ∀ i, (K i).map (p₁ : B →+* C) = (K i).map (p₂ : B →+* C))
    (I : Ideal B) (hIn : I ≤ nilradical B) (hKI : ⨆ i, K i = I)
    (h : IsNerveReduction p₁ p₂ e₁₂ e₁₃ e₂₃ I) :
    ∃ i, IsNerveReduction p₁ p₂ e₁₂ e₁₃ e₂₃ (K i) := by
  classical
  obtain ⟨A₁, B₁, _, _, _, hEt, hFF, πB, πC, πD, hsB, hsC, hsD, hkB, hkC, hkD,
    hC₁, hC₂, hD₁₂, -, hD₂₃⟩ := h
  have hKI' : ∀ i, K i ≤ I := fun i => hKI ▸ le_iSup K i
  have hI : I.map (p₁ : B →+* C) = I.map (p₂ : B →+* C) := by
    rw [← hKI, Ideal.map_iSup, Ideal.map_iSup]; exact iSup_congr hKinv
  have hinj : Function.Injective (algebraMap A₁ B₁) := FaithfulSMul.algebraMap_injective A₁ B₁
  have hπC : ∀ b, πC (p₁ b) = πB b ⊗ₜ[A₁] 1 ∧ πC (p₂ b) = 1 ⊗ₜ[A₁] πB b := fun b =>
    ⟨by simpa using RingHom.congr_fun hC₁ b, by simpa using RingHom.congr_fun hC₂ b⟩
  have hrange : ∀ b, p₁ b - p₂ b ∈ I.map (p₁ : B →+* C) → πB b ∈ (algebraMap A₁ B₁).range := by
    intro b hb
    have heff := Algebra.IsEffective.of_faithfullyFlat A₁ B₁
    obtain ⟨a, ha⟩ := (heff (πB b)).1 (by
      rw [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero, ← (hπC b).1,
        ← (hπC b).2, ← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, hkC]
      exact hb)
    exact ⟨a, ha⟩
  have hlift : ∀ i, ∀ x ∈ K i, πB x = 0 := fun i x hx => by
    rw [← RingHom.mem_ker, hkB]; exact hKI' i hx
  obtain ⟨φ, hφspec⟩ : ∃ φ : ∀ i, stageEq p₁ p₂ (K i) (hKinv i) →+* A₁,
      ∀ i x, algebraMap A₁ B₁ (φ i x) = Ideal.Quotient.lift (K i) πB (hlift i) x := by
    refine ⟨fun i => liftOfRange (algebraMap A₁ B₁) hinj
      ((Ideal.Quotient.lift (K i) πB (hlift i)).comp
        (stageEq p₁ p₂ (K i) (hKinv i)).val.toRingHom) (fun ⟨x, hx⟩ => ?_),
      fun i x => liftOfRange_spec _ _ _ _ x⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact hrange b (Ideal.map_mono (hKI' i) ((mem_stageEq_mk (hKinv i) b).1 hx))
  have : DirectedSystem (fun i => ↥(stageEq p₁ p₂ (K i) (hKinv i)))
      fun i j h => ⇑(stageMap (hKinv i) (hKinv j) (hKm h)) := by
    constructor
    · intro i x
      refine Subtype.ext ?_
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (x : B ⧸ K i)
      rw [stageMap_coe, ← hb, Ideal.Quotient.factor_mk]
    · intro k j i hij hjk x
      refine Subtype.ext ?_
      rw [stageMap_coe, stageMap_coe, stageMap_coe, Ideal.Quotient.factor_comp_apply]
  have hφ : ∀ i j (h : i ≤ j) (x : stageEq p₁ p₂ (K i) (hKinv i)),
      φ j (stageMap (hKinv i) (hKinv j) (hKm h) x) = φ i x := by
    intro i j h x
    refine hinj ?_
    rw [hφspec, hφspec, stageMap_coe]
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (x : B ⧸ K i)
    rw [← hb, Ideal.Quotient.factor_mk, Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk]
  have hdirC : Directed (· ≤ ·) fun i => (K i).map (p₁ : B →+* C) :=
    Monotone.directed_le fun _ _ h => Ideal.map_mono (hKm h)
  have hsurj : ∀ a : A₁, ∃ (i : ι) (x : stageEq p₁ p₂ (K i) (hKinv i)), φ i x = a := by
    intro a
    obtain ⟨b, hb⟩ := hsB (algebraMap A₁ B₁ a)
    have hmem : p₁ b - p₂ b ∈ I.map (p₁ : B →+* C) := by
      rw [← hkC, RingHom.mem_ker, map_sub, sub_eq_zero]
      show πC (p₁ b) = πC (p₂ b)
      rw [(hπC b).1, (hπC b).2, hb, Algebra.TensorProduct.tmul_one_eq_one_tmul]
    rw [← hKI, Ideal.map_iSup, Submodule.mem_iSup_of_directed _ hdirC] at hmem
    obtain ⟨i, hi⟩ := hmem
    refine ⟨i, ⟨Ideal.Quotient.mk (K i) b, (mem_stageEq_mk (hKinv i) b).2 hi⟩, hinj ?_⟩
    rw [hφspec, ← hb]
    exact Ideal.Quotient.lift_mk (K i) πB (hlift i)
  have hzero : ∀ (i : ι) (x : stageEq p₁ p₂ (K i) (hKinv i)), φ i x = 0 →
      ∃ (j : ι) (h : i ≤ j), stageMap (hKinv i) (hKinv j) (hKm h) x = 0 := by
    intro i x hx
    have hx' := hφspec i x
    rw [hx, map_zero] at hx'
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (x : B ⧸ K i)
    rw [← hb, Ideal.Quotient.lift_mk] at hx'
    have hbI : b ∈ ⨆ i, K i := by rw [hKI, ← hkB, RingHom.mem_ker]; exact hx'.symm
    rw [Submodule.mem_iSup_of_directed _ hKm.directed_le] at hbI
    obtain ⟨j, hj⟩ := hbI
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨k, hik, Subtype.ext ?_⟩
    rw [stageMap_coe, ← hb, Ideal.Quotient.factor_mk, ZeroMemClass.coe_zero,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hKm hjk hj
  have : Algebra.Etale A₁ B₁ := hEt
  have : Module.FaithfullyFlat A₁ B₁ := hFF
  obtain ⟨i, S, _, _, hSE, hSF, ⟨e⟩⟩ := Algebra.Etale.exists_model_of_directed
    (G := fun i => ↥(stageEq p₁ p₂ (K i) (hKinv i)))
    (f := fun i j h => stageMap (hKinv i) (hKinv j) (hKm h)) hφ hsurj hzero B₁
  let := (φ i).toAlgebra
  exact ⟨i, isNerveReduction_of_stage_model δ e₁₃ e₂₃ hδ₁ hδ₂ h₁₂₁₃ h₁₂₂₃ h₁₃₂₃ hp₁ hp₂ he₁₂ he₂₃
    I hI hIn (K i) (hKinv i) (hKI' i) πB πC πD hsB hsC hkB hkC hkD hC₁ hC₂ hD₁₂ hD₂₃
    (fun a => hφspec i a) S e⟩

/-- **A Čech nerve modulo a nil ideal of the base is a Čech nerve.** If the closed subspace of
`P` cut out by a nil ideal `I` of the base `R` is affine, so is `P`: a nerve modulo `I B` is a
nerve modulo `0`. The ideal `I` is the directed union of its finitely generated subideals `J`;
by `Module.Descent.exists_isNerveReduction_of_iSup` the diagram is a nerve modulo some `J B`, and
`Module.Descent.isNerveReduction_bot_of_fg_of_le_nilradical` climbs down the nilpotent `J`. -/
theorem isNerveReduction_bot_of_le_nilradical (δ : C →ₐ[R] B) (e₁₃ e₂₃ : C →ₐ[R] D)
    (hδ₁ : δ.comp p₁ = AlgHom.id R B) (hδ₂ : δ.comp p₂ = AlgHom.id R B)
    (h₁₂₁₃ : e₁₂.comp p₁ = e₁₃.comp p₁) (h₁₂₂₃ : e₁₂.comp p₂ = e₂₃.comp p₁)
    (h₁₃₂₃ : e₁₃.comp p₂ = e₂₃.comp p₂)
    (hp₁ : (p₁ : B →+* C).Etale) (hp₂ : (p₂ : B →+* C).Etale)
    (he₁₂ : (e₁₂ : C →+* D).Etale) (he₂₃ : (e₂₃ : C →+* D).Etale)
    (I : Ideal R) (hI : I ≤ nilradical R)
    (h : IsNerveReduction p₁ p₂ e₁₂ e₁₃ e₂₃ (I.map (algebraMap R B))) :
    IsNerveReduction p₁ p₂ e₁₂ e₁₃ e₂₃ ⊥ := by
  let ι := {J : Ideal R // J.FG ∧ J ≤ I}
  have : IsDirected ι (· ≤ ·) := ⟨fun a b =>
    ⟨⟨a.1 ⊔ b.1, Submodule.FG.sup a.2.1 b.2.1, sup_le a.2.2 b.2.2⟩, le_sup_left (a := a.1),
      le_sup_right (a := a.1)⟩⟩
  have : Nonempty ι := ⟨⟨⊥, Submodule.fg_bot, bot_le⟩⟩
  have hsup : ⨆ J : ι, J.1.map (algebraMap R B) = I.map (algebraMap R B) := by
    rw [← Ideal.map_iSup]
    congr 1
    refine le_antisymm (iSup_le fun J => J.2.2) fun x hx => ?_
    exact Ideal.mem_iSup_of_mem (⟨Ideal.span {x}, Submodule.fg_span_singleton x,
      (Ideal.span_singleton_le_iff_mem I).2 hx⟩ : ι) (Ideal.subset_span rfl)
  obtain ⟨J, hJ⟩ := exists_isNerveReduction_of_iSup δ e₁₃ e₂₃ hδ₁ hδ₂ h₁₂₁₃ h₁₂₂₃ h₁₃₂₃ hp₁ hp₂
    he₁₂ he₂₃ (fun J : ι => J.1.map (algebraMap R B)) (fun _ _ h => Ideal.map_mono h)
    (fun J => map_algebraMap_invariant J.1) _
    (Ideal.map_le_nilradical_of_le_nilradical _ hI) hsup h
  exact isNerveReduction_bot_of_fg_of_le_nilradical δ e₁₃ e₂₃ hδ₁ hδ₂ h₁₂₁₃ h₁₂₂₃ h₁₃₂₃ hp₁ hp₂
    he₁₂ he₂₃ J.1 J.2.1 (J.2.2.trans hI) hJ

end Nerve

end Module.Descent
