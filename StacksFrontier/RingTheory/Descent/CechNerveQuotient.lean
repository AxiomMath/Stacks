module

public import StacksFrontier.RingTheory.Descent.CechNerveClimb
public import StacksFrontier.Topology.Algebra.AdicTopology.EtaleModWeakIdeal

/-!
# Čech nerves modulo invariant ideals, and the climb down a nilpotent ideal of the base

Let `p₁, p₂ : B → C`, `δ : C → B` and `e₁₂, e₁₃, e₂₃ : C → D` be the first terms of the Čech
nerve of a surjective étale chart `U → P` of an algebraic space over `Spec R`. An ideal `K` of
`B` is *invariant* when `p₁ K` and `p₂ K` generate the same ideal of `C`; for instance `K = J B`
for an ideal `J` of `R`. Reducing the diagram modulo `K`, `p₁ K` and `e₁₂ p₁ K` gives the Čech
nerve of the closed subspace of `P` cut out by `K`
(`Module.Descent.nerveQuotP₁`, `Module.Descent.nerveQuotP₂`, `Module.Descent.nerveQuotE`,
`Module.Descent.nerveQuotδ`).

## Main results

* `Module.Descent.isNerveReduction_of_sup_span_singleton`: for an invariant ideal `K` and an
  element `μ` with `μ² ∈ K` which is invariant modulo `K`, a nerve modulo `K + (μ)` is a nerve
  modulo `K`. Geometrically: if the closed subspace cut out by `K + (μ)` is affine, so is the one
  cut out by `K`.
* `Module.Descent.isNerveReduction_bot_of_fg_of_le_nilradical`: for a finitely generated nil
  ideal `J` of the base `R`, a nerve modulo `J B` is a nerve modulo `0`: if the closed subspace of
  `P` cut out by `J` is affine, so is `P`.

The first is `Module.Descent.isNerveReduction_bot_of_span_singleton` applied to the diagram
reduced modulo `K`; the second walks down `J ⊇ J² ⊇ J⁴ ⊇ ⋯ ⊇ 0`, each step adding one generator
at a time.
-/

@[expose] public section

universe u

open TensorProduct

namespace Module.Descent

/-- The reduction of an étale ring map modulo an ideal and its extension is étale
(`RingHom.Etale.quotientMap`), for an ideal given up to equality. -/
private theorem etale_quotientMap_of_eq {X Y : Type*} [CommRing X] [CommRing Y] {f : X →+* Y}
    (hf : f.Etale) (I : Ideal X) {J : Ideal Y} (hJ : J = I.map f) (h : I ≤ J.comap f) :
    (Ideal.quotientMap J f h).Etale := by
  subst hJ
  exact RingHom.Etale.quotientMap f hf I

section Nerve

variable {R : Type u} [CommRing R] {B C D : Type u} [CommRing B] [CommRing C] [CommRing D]
  [Algebra R B] [Algebra R C] [Algebra R D]
  (p₁ p₂ : B →ₐ[R] C) (e₁₂ : C →ₐ[R] D) (K : Ideal B)

/-- The first projection of the Čech nerve reduced modulo an ideal `K` of `B`. -/
noncomputable def nerveQuotP₁ : B ⧸ K →ₐ[R] C ⧸ K.map (p₁ : B →+* C) :=
  Ideal.quotientMapₐ _ p₁ Ideal.le_comap_map

/-- The second projection of the Čech nerve reduced modulo an invariant ideal `K` of `B`. -/
noncomputable def nerveQuotP₂ (hK : K.map (p₁ : B →+* C) = K.map (p₂ : B →+* C)) :
    B ⧸ K →ₐ[R] C ⧸ K.map (p₁ : B →+* C) :=
  Ideal.quotientMapₐ _ p₂ (by rw [hK]; exact Ideal.le_comap_map)

/-- A partial projection `e : C → D` of the Čech nerve reduced modulo an ideal `K` of `B`, when
it carries `p₁ K` into `e₁₂ p₁ K`. -/
noncomputable def nerveQuotE (e : C →ₐ[R] D)
    (he : (K.map (p₁ : B →+* C)).map (e : C →+* D) =
      K.map ((e₁₂ : C →+* D).comp (p₁ : B →+* C))) :
    C ⧸ K.map (p₁ : B →+* C) →ₐ[R] D ⧸ K.map ((e₁₂ : C →+* D).comp (p₁ : B →+* C)) :=
  Ideal.quotientMapₐ _ e (by rw [← he]; exact Ideal.le_comap_map)

/-- The diagonal of the Čech nerve reduced modulo an ideal `K` of `B`. -/
noncomputable def nerveQuotδ (δ : C →ₐ[R] B) (hδ₁ : δ.comp p₁ = AlgHom.id R B) :
    C ⧸ K.map (p₁ : B →+* C) →ₐ[R] B ⧸ K :=
  Ideal.quotientMapₐ _ δ (by
    rw [← Ideal.map_le_iff_le_comap]
    change Ideal.map (δ : C →+* B) (Ideal.map (p₁ : B →+* C) K) ≤ K
    rw [Ideal.map_map]
    rw [show (δ : C →+* B).comp (p₁ : B →+* C) = RingHom.id B from
      congrArg AlgHom.toRingHom hδ₁, Ideal.map_id])

variable {p₁ p₂ e₁₂ K}

/-- `Module.Descent.nerveQuotP₁` sends the class of `b` to the class of `p₁ b`. -/
@[simp]
theorem nerveQuotP₁_mk (b : B) :
    nerveQuotP₁ p₁ K (Ideal.Quotient.mk K b) = Ideal.Quotient.mk _ (p₁ b) := rfl

/-- `Module.Descent.nerveQuotP₂` sends the class of `b` to the class of `p₂ b`. -/
@[simp]
theorem nerveQuotP₂_mk (hK : K.map (p₁ : B →+* C) = K.map (p₂ : B →+* C)) (b : B) :
    nerveQuotP₂ p₁ p₂ K hK (Ideal.Quotient.mk K b) = Ideal.Quotient.mk _ (p₂ b) := rfl

/-- `Module.Descent.nerveQuotE` sends the class of `c` to the class of `e c`. -/
@[simp]
theorem nerveQuotE_mk (e : C →ₐ[R] D)
    (he : (K.map (p₁ : B →+* C)).map (e : C →+* D) =
      K.map ((e₁₂ : C →+* D).comp (p₁ : B →+* C))) (c : C) :
    nerveQuotE p₁ e₁₂ K e he (Ideal.Quotient.mk _ c) = Ideal.Quotient.mk _ (e c) := rfl

/-- `Module.Descent.nerveQuotδ` sends the class of `c` to the class of `δ c`. -/
@[simp]
theorem nerveQuotδ_mk (δ : C →ₐ[R] B) (hδ₁ : δ.comp p₁ = AlgHom.id R B) (c : C) :
    nerveQuotδ p₁ K δ hδ₁ (Ideal.Quotient.mk _ c) = Ideal.Quotient.mk _ (δ c) := rfl

/-- `e₁₂` carries `p₁ K` onto `e₁₂ p₁ K`. -/
theorem map_e₁₂_eq : (K.map (p₁ : B →+* C)).map (e₁₂ : C →+* D) =
    K.map ((e₁₂ : C →+* D).comp (p₁ : B →+* C)) := Ideal.map_map _ _

/-- `e₁₃` carries `p₁ K` onto `e₁₂ p₁ K`. -/
theorem map_e₁₃_eq {e₁₃ : C →ₐ[R] D} (h₁₂₁₃ : e₁₂.comp p₁ = e₁₃.comp p₁) :
    (K.map (p₁ : B →+* C)).map (e₁₃ : C →+* D) =
      K.map ((e₁₂ : C →+* D).comp (p₁ : B →+* C)) := by
  rw [Ideal.map_map]
  exact congrArg (K.map ·) (congrArg AlgHom.toRingHom h₁₂₁₃).symm

/-- For an invariant `K`, `e₂₃` carries `p₁ K` onto `e₁₂ p₁ K`. -/
theorem map_e₂₃_eq {e₂₃ : C →ₐ[R] D} (h₁₂₂₃ : e₁₂.comp p₂ = e₂₃.comp p₁)
    (hK : K.map (p₁ : B →+* C) = K.map (p₂ : B →+* C)) :
    (K.map (p₁ : B →+* C)).map (e₂₃ : C →+* D) =
      K.map ((e₁₂ : C →+* D).comp (p₁ : B →+* C)) := by
  have h : (e₂₃ : C →+* D).comp (p₁ : B →+* C) = (e₁₂ : C →+* D).comp (p₂ : B →+* C) :=
    RingHom.ext fun x => (AlgHom.congr_fun h₁₂₂₃ x).symm
  rw [Ideal.map_map, h, ← Ideal.map_map, ← hK, Ideal.map_map]

/-- The kernel of a map out of a quotient, read off from the map it lifts. -/
theorem ker_lift_eq {X Y : Type*} [CommRing X] [CommRing Y] (I : Ideal X) (f : X →+* Y)
    (H : ∀ a ∈ I, f a = 0) : RingHom.ker (Ideal.Quotient.lift I f H) = (RingHom.ker f).map
      (Ideal.Quotient.mk I) :=
  Ideal.ker_quotient_lift f fun a ha => H a ha

/-- **A nerve modulo `L ⊇ K` is a nerve of the reduction modulo `K`.** -/
theorem isNerveReduction_quot_of_le {e₁₃ e₂₃ : C →ₐ[R] D}
    (h₁₂₁₃ : e₁₂.comp p₁ = e₁₃.comp p₁) (h₁₂₂₃ : e₁₂.comp p₂ = e₂₃.comp p₁)
    (hK : K.map (p₁ : B →+* C) = K.map (p₂ : B →+* C)) {L : Ideal B} (hKL : K ≤ L)
    (h : IsNerveReduction p₁ p₂ e₁₂ e₁₃ e₂₃ L) :
    IsNerveReduction (nerveQuotP₁ p₁ K) (nerveQuotP₂ p₁ p₂ K hK)
      (nerveQuotE p₁ e₁₂ K e₁₂ map_e₁₂_eq) (nerveQuotE p₁ e₁₂ K e₁₃ (map_e₁₃_eq h₁₂₁₃))
      (nerveQuotE p₁ e₁₂ K e₂₃ (map_e₂₃_eq h₁₂₂₃ hK)) (L.map (Ideal.Quotient.mk K)) := by
  obtain ⟨A₁, B₁, _, _, _, hEt, hFF, πB, πC, πD, hsB, hsC, hsD, hkB, hkC, hkD,
    hC₁, hC₂, hD₁₂, hD₁₃, hD₂₃⟩ := h
  have HB : ∀ a ∈ K, πB a = 0 := fun a ha => by
    rw [← RingHom.mem_ker, hkB]; exact hKL ha
  have HC : ∀ a ∈ K.map (p₁ : B →+* C), πC a = 0 := fun a ha => by
    rw [← RingHom.mem_ker, hkC]; exact Ideal.map_mono hKL ha
  have HD : ∀ a ∈ K.map ((e₁₂ : C →+* D).comp (p₁ : B →+* C)), πD a = 0 := fun a ha => by
    rw [← RingHom.mem_ker, hkD]; exact Ideal.map_mono hKL ha
  refine ⟨A₁, B₁, inferInstance, inferInstance, inferInstance, hEt, hFF,
    Ideal.Quotient.lift _ πB HB, Ideal.Quotient.lift _ πC HC, Ideal.Quotient.lift _ πD HD,
    Ideal.Quotient.lift_surjective_of_surjective _ _ hsB,
    Ideal.Quotient.lift_surjective_of_surjective _ _ hsC,
    Ideal.Quotient.lift_surjective_of_surjective _ _ hsD, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ker_lift_eq, hkB]
  · rw [ker_lift_eq, hkC, Ideal.map_map, Ideal.map_map]
    rfl
  · rw [ker_lift_eq, hkD, Ideal.map_map, Ideal.map_map]
    rfl
  · exact Ideal.Quotient.ringHom_ext (RingHom.ext (RingHom.congr_fun hC₁))
  · exact Ideal.Quotient.ringHom_ext (RingHom.ext (RingHom.congr_fun hC₂))
  · exact Ideal.Quotient.ringHom_ext (RingHom.ext (RingHom.congr_fun hD₁₂))
  · exact Ideal.Quotient.ringHom_ext (RingHom.ext (RingHom.congr_fun hD₁₃))
  · exact Ideal.Quotient.ringHom_ext (RingHom.ext (RingHom.congr_fun hD₂₃))

/-- **A nerve of the reduction modulo `K` is a nerve modulo `K`.** -/
theorem isNerveReduction_of_quot_bot {e₁₃ e₂₃ : C →ₐ[R] D}
    (h₁₂₁₃ : e₁₂.comp p₁ = e₁₃.comp p₁) (h₁₂₂₃ : e₁₂.comp p₂ = e₂₃.comp p₁)
    (hK : K.map (p₁ : B →+* C) = K.map (p₂ : B →+* C))
    (h : IsNerveReduction (nerveQuotP₁ p₁ K) (nerveQuotP₂ p₁ p₂ K hK)
      (nerveQuotE p₁ e₁₂ K e₁₂ map_e₁₂_eq) (nerveQuotE p₁ e₁₂ K e₁₃ (map_e₁₃_eq h₁₂₁₃))
      (nerveQuotE p₁ e₁₂ K e₂₃ (map_e₂₃_eq h₁₂₂₃ hK)) ⊥) :
    IsNerveReduction p₁ p₂ e₁₂ e₁₃ e₂₃ K := by
  obtain ⟨A₁, B₁, _, _, _, hEt, hFF, πB, πC, πD, hsB, hsC, hsD, hkB, hkC, hkD,
    hC₁, hC₂, hD₁₂, hD₁₃, hD₂₃⟩ := h
  have hker : ∀ {X Y : Type u} [CommRing X] [CommRing Y] (I : Ideal X) (π : X ⧸ I →+* Y),
      RingHom.ker π = ⊥ → RingHom.ker (π.comp (Ideal.Quotient.mk I)) = I := by
    intro X Y _ _ I π hπ
    rw [← RingHom.comap_ker, hπ, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  refine ⟨A₁, B₁, inferInstance, inferInstance, inferInstance, hEt, hFF,
    πB.comp (Ideal.Quotient.mk _), πC.comp (Ideal.Quotient.mk _), πD.comp (Ideal.Quotient.mk _),
    hsB.comp Ideal.Quotient.mk_surjective, hsC.comp Ideal.Quotient.mk_surjective,
    hsD.comp Ideal.Quotient.mk_surjective, hker _ _ hkB,
    hker _ _ (by rw [hkC, Ideal.map_bot]), hker _ _ (by rw [hkD, Ideal.map_bot]),
    ?_, ?_, ?_, ?_, ?_⟩
  · exact RingHom.ext fun b => RingHom.congr_fun hC₁ (Ideal.Quotient.mk _ b)
  · exact RingHom.ext fun b => RingHom.congr_fun hC₂ (Ideal.Quotient.mk _ b)
  · exact RingHom.ext fun b => RingHom.congr_fun hD₁₂ (Ideal.Quotient.mk _ b)
  · exact RingHom.ext fun b => RingHom.congr_fun hD₁₃ (Ideal.Quotient.mk _ b)
  · exact RingHom.ext fun b => RingHom.congr_fun hD₂₃ (Ideal.Quotient.mk _ b)

/-- The coface identities and étaleness of the Čech nerve pass to its reduction modulo an
invariant ideal. -/
theorem nerveQuot_identities {δ : C →ₐ[R] B} {e₁₃ e₂₃ : C →ₐ[R] D}
    (hδ₁ : δ.comp p₁ = AlgHom.id R B) (hδ₂ : δ.comp p₂ = AlgHom.id R B)
    (h₁₂₁₃ : e₁₂.comp p₁ = e₁₃.comp p₁) (h₁₂₂₃ : e₁₂.comp p₂ = e₂₃.comp p₁)
    (h₁₃₂₃ : e₁₃.comp p₂ = e₂₃.comp p₂)
    (hp₁ : (p₁ : B →+* C).Etale) (hp₂ : (p₂ : B →+* C).Etale)
    (he₁₂ : (e₁₂ : C →+* D).Etale) (he₂₃ : (e₂₃ : C →+* D).Etale)
    (hK : K.map (p₁ : B →+* C) = K.map (p₂ : B →+* C)) :
    (nerveQuotδ p₁ K δ hδ₁).comp (nerveQuotP₁ p₁ K) = AlgHom.id R (B ⧸ K) ∧
    (nerveQuotδ p₁ K δ hδ₁).comp (nerveQuotP₂ p₁ p₂ K hK) = AlgHom.id R (B ⧸ K) ∧
    (nerveQuotE p₁ e₁₂ K e₁₂ map_e₁₂_eq).comp (nerveQuotP₁ p₁ K) =
      (nerveQuotE p₁ e₁₂ K e₁₃ (map_e₁₃_eq h₁₂₁₃)).comp (nerveQuotP₁ p₁ K) ∧
    (nerveQuotE p₁ e₁₂ K e₁₂ map_e₁₂_eq).comp (nerveQuotP₂ p₁ p₂ K hK) =
      (nerveQuotE p₁ e₁₂ K e₂₃ (map_e₂₃_eq h₁₂₂₃ hK)).comp (nerveQuotP₁ p₁ K) ∧
    (nerveQuotE p₁ e₁₂ K e₁₃ (map_e₁₃_eq h₁₂₁₃)).comp (nerveQuotP₂ p₁ p₂ K hK) =
      (nerveQuotE p₁ e₁₂ K e₂₃ (map_e₂₃_eq h₁₂₂₃ hK)).comp (nerveQuotP₂ p₁ p₂ K hK) ∧
    (nerveQuotP₁ p₁ K : B ⧸ K →+* C ⧸ K.map (p₁ : B →+* C)).Etale ∧
    (nerveQuotP₂ p₁ p₂ K hK : B ⧸ K →+* C ⧸ K.map (p₁ : B →+* C)).Etale ∧
    (nerveQuotE p₁ e₁₂ K e₁₂ map_e₁₂_eq : C ⧸ K.map (p₁ : B →+* C) →+*
      D ⧸ K.map ((e₁₂ : C →+* D).comp (p₁ : B →+* C))).Etale ∧
    (nerveQuotE p₁ e₁₂ K e₂₃ (map_e₂₃_eq h₁₂₂₃ hK) : C ⧸ K.map (p₁ : B →+* C) →+*
      D ⧸ K.map ((e₁₂ : C →+* D).comp (p₁ : B →+* C))).Etale := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Ideal.Quotient.algHom_ext R (AlgHom.ext fun b =>
      congrArg (Ideal.Quotient.mk _) (AlgHom.congr_fun hδ₁ b))
  · exact Ideal.Quotient.algHom_ext R (AlgHom.ext fun b =>
      congrArg (Ideal.Quotient.mk _) (AlgHom.congr_fun hδ₂ b))
  · exact Ideal.Quotient.algHom_ext R (AlgHom.ext fun b =>
      congrArg (Ideal.Quotient.mk _) (AlgHom.congr_fun h₁₂₁₃ b))
  · exact Ideal.Quotient.algHom_ext R (AlgHom.ext fun b =>
      congrArg (Ideal.Quotient.mk _) (AlgHom.congr_fun h₁₂₂₃ b))
  · exact Ideal.Quotient.algHom_ext R (AlgHom.ext fun b =>
      congrArg (Ideal.Quotient.mk _) (AlgHom.congr_fun h₁₃₂₃ b))
  · exact etale_quotientMap_of_eq hp₁ K rfl Ideal.le_comap_map
  · exact etale_quotientMap_of_eq hp₂ K hK (by rw [hK]; exact Ideal.le_comap_map)
  · exact etale_quotientMap_of_eq he₁₂ _ map_e₁₂_eq.symm
      (by rw [← map_e₁₂_eq]; exact Ideal.le_comap_map)
  · exact etale_quotientMap_of_eq he₂₃ _ (map_e₂₃_eq h₁₂₂₃ hK).symm
      (by rw [← map_e₂₃_eq h₁₂₂₃ hK]; exact Ideal.le_comap_map)

/-- **Climbing one square-zero step.** Let `K` be an invariant ideal of `B` and `μ ∈ B` with
`μ² ∈ K` and `p₁ μ ≡ p₂ μ` modulo `p₁ K`. If the Čech nerve is a nerve modulo `K + (μ)`, it is a
nerve modulo `K`. -/
theorem isNerveReduction_of_sup_span_singleton (p₁ p₂ : B →ₐ[R] C) (δ : C →ₐ[R] B)
    (e₁₂ e₁₃ e₂₃ : C →ₐ[R] D)
    (hδ₁ : δ.comp p₁ = AlgHom.id R B) (hδ₂ : δ.comp p₂ = AlgHom.id R B)
    (h₁₂₁₃ : e₁₂.comp p₁ = e₁₃.comp p₁) (h₁₂₂₃ : e₁₂.comp p₂ = e₂₃.comp p₁)
    (h₁₃₂₃ : e₁₃.comp p₂ = e₂₃.comp p₂)
    (hp₁ : (p₁ : B →+* C).Etale) (hp₂ : (p₂ : B →+* C).Etale)
    (he₁₂ : (e₁₂ : C →+* D).Etale) (he₂₃ : (e₂₃ : C →+* D).Etale)
    (K : Ideal B) (hK : K.map (p₁ : B →+* C) = K.map (p₂ : B →+* C))
    (μ : B) (hμ : μ * μ ∈ K) (hμp : p₁ μ - p₂ μ ∈ K.map (p₁ : B →+* C))
    (h : IsNerveReduction p₁ p₂ e₁₂ e₁₃ e₂₃ (K ⊔ Ideal.span {μ})) :
    IsNerveReduction p₁ p₂ e₁₂ e₁₃ e₂₃ K := by
  obtain ⟨hq₁, hq₂, hq₃, hq₄, hq₅, hqp₁, hqp₂, hqe₁₂, hqe₂₃⟩ :=
    nerveQuot_identities hδ₁ hδ₂ h₁₂₁₃ h₁₂₂₃ h₁₃₂₃ hp₁ hp₂ he₁₂ he₂₃ hK
  refine isNerveReduction_of_quot_bot h₁₂₁₃ h₁₂₂₃ hK ?_
  have h' := isNerveReduction_quot_of_le h₁₂₁₃ h₁₂₂₃ hK le_sup_left h
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton,
    show K.map (Ideal.Quotient.mk K) = ⊥ from Ideal.map_quotient_self K, bot_sup_eq] at h'
  refine isNerveReduction_bot_of_span_singleton _ _ (nerveQuotδ p₁ K δ hδ₁) _ _ _ hq₁ hq₂ hq₃ hq₄
    hq₅ hqp₁ hqp₂ hqe₁₂ hqe₂₃ (Ideal.Quotient.mk K μ) ?_ ?_ h'
  · rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]; exact hμ
  · rw [nerveQuotP₁_mk, nerveQuotP₂_mk, Ideal.Quotient.eq]; exact hμp

/-- An ideal extended from the base is invariant. -/
theorem map_algebraMap_invariant (J : Ideal R) :
    (J.map (algebraMap R B)).map (p₁ : B →+* C) = (J.map (algebraMap R B)).map (p₂ : B →+* C) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  exact RingHom.ext fun r => by simp

/-- **Climbing a finite set of square-zero generators from the base.** -/
theorem isNerveReduction_of_sup_span_finset (δ : C →ₐ[R] B)
    (e₁₃ e₂₃ : C →ₐ[R] D)
    (hδ₁ : δ.comp p₁ = AlgHom.id R B) (hδ₂ : δ.comp p₂ = AlgHom.id R B)
    (h₁₂₁₃ : e₁₂.comp p₁ = e₁₃.comp p₁) (h₁₂₂₃ : e₁₂.comp p₂ = e₂₃.comp p₁)
    (h₁₃₂₃ : e₁₃.comp p₂ = e₂₃.comp p₂)
    (hp₁ : (p₁ : B →+* C).Etale) (hp₂ : (p₂ : B →+* C).Etale)
    (he₁₂ : (e₁₂ : C →+* D).Etale) (he₂₃ : (e₂₃ : C →+* D).Etale)
    (J : Ideal R) (s : Finset R) (hs : ∀ f ∈ s, f * f ∈ J)
    (h : IsNerveReduction p₁ p₂ e₁₂ e₁₃ e₂₃ ((J ⊔ Ideal.span (s : Set R)).map (algebraMap R B))) :
    IsNerveReduction p₁ p₂ e₁₂ e₁₃ e₂₃ (J.map (algebraMap R B)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h
  | insert a s ha ih =>
    refine ih (fun f hf => hs f (Finset.mem_insert_of_mem hf)) ?_
    refine isNerveReduction_of_sup_span_singleton p₁ p₂ δ e₁₂ e₁₃ e₂₃ hδ₁ hδ₂ h₁₂₁₃ h₁₂₂₃ h₁₃₂₃
      hp₁ hp₂ he₁₂ he₂₃ _ (map_algebraMap_invariant _) (algebraMap R B a) ?_ ?_ ?_
    · rw [← map_mul]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_left (hs a (Finset.mem_insert_self a s)))
    · rw [AlgHom.commutes, AlgHom.commutes, sub_self]; exact Submodule.zero_mem _
    · have e : J ⊔ Ideal.span ((insert a s : Finset R) : Set R) =
          (J ⊔ Ideal.span (s : Set R)) ⊔ Ideal.span {a} := by
        rw [Finset.coe_insert, Ideal.span_insert, ← sup_assoc, sup_comm J, sup_assoc, sup_comm]
      rwa [e, Ideal.map_sup, Ideal.map_span, Set.image_singleton] at h

/-- **A Čech nerve modulo a finitely generated nil ideal of the base is a Čech nerve.** If the
closed subspace of `P` cut out by a finitely generated nil ideal `J` of `R` is affine, so is `P`:
a nerve modulo `J B` is a nerve modulo `0`. -/
theorem isNerveReduction_bot_of_fg_of_le_nilradical (δ : C →ₐ[R] B)
    (e₁₃ e₂₃ : C →ₐ[R] D)
    (hδ₁ : δ.comp p₁ = AlgHom.id R B) (hδ₂ : δ.comp p₂ = AlgHom.id R B)
    (h₁₂₁₃ : e₁₂.comp p₁ = e₁₃.comp p₁) (h₁₂₂₃ : e₁₂.comp p₂ = e₂₃.comp p₁)
    (h₁₃₂₃ : e₁₃.comp p₂ = e₂₃.comp p₂)
    (hp₁ : (p₁ : B →+* C).Etale) (hp₂ : (p₂ : B →+* C).Etale)
    (he₁₂ : (e₁₂ : C →+* D).Etale) (he₂₃ : (e₂₃ : C →+* D).Etale)
    (J : Ideal R) (hJ : J.FG) (hJn : J ≤ nilradical R)
    (h : IsNerveReduction p₁ p₂ e₁₂ e₁₃ e₂₃ (J.map (algebraMap R B))) :
    IsNerveReduction p₁ p₂ e₁₂ e₁₃ e₂₃ ⊥ := by
  classical
  -- one squaring step: `J' ⊇ J'²`, for any finitely generated `J'`
  have step : ∀ J' : Ideal R, J'.FG → IsNerveReduction p₁ p₂ e₁₂ e₁₃ e₂₃ (J'.map (algebraMap R B))
      → IsNerveReduction p₁ p₂ e₁₂ e₁₃ e₂₃ ((J' ^ 2).map (algebraMap R B)) := by
    rintro J' ⟨s, hs⟩ hJ'
    refine isNerveReduction_of_sup_span_finset δ e₁₃ e₂₃ hδ₁ hδ₂ h₁₂₁₃ h₁₂₂₃ h₁₃₂₃ hp₁ hp₂ he₁₂
      he₂₃ _ s (fun f hf => ?_) ?_
    · have hf' : f ∈ J' := hs ▸ Ideal.subset_span hf
      rw [pow_two]; exact Ideal.mul_mem_mul hf' hf'
    · rwa [hs, sup_eq_right.2 (Ideal.pow_le_self two_ne_zero)]
  have hpow : ∀ k : ℕ, (J ^ (2 ^ k)).FG ∧
      IsNerveReduction p₁ p₂ e₁₂ e₁₃ e₂₃ ((J ^ (2 ^ k)).map (algebraMap R B)) := by
    intro k
    induction k with
    | zero => simpa using ⟨hJ, h⟩
    | succ k ih =>
      rw [pow_succ, pow_mul]
      exact ⟨Ideal.FG.pow ih.1, step _ ih.1 ih.2⟩
  obtain ⟨N, hN⟩ := Ideal.FG.isNilpotent_of_le_nilradical hJ hJn
  have hle : J ^ (2 ^ N) = ⊥ := by
    rw [← le_bot_iff, ← Ideal.zero_eq_bot, ← hN]
    exact Ideal.pow_le_pow_right (Nat.lt_two_pow_self).le
  simpa [hle] using (hpow N).2

end Nerve

end Module.Descent
