module

public import StacksFrontier.RingTheory.Etale.PushoutLiftSquareZero.Thickening

/-!
# The glued ring of the square-zero case of Stacks 0ALT

Let `J ⊆ A` be a square-zero ideal, `f_1, …, f_r ∈ A`, `B₀` an `A ⧸ J`-algebra and `C` an
`A`-algebra with a map `B₀ → C ⧸ JC`. Under the standing hypotheses `SquareZero.Setup`, each
localization `B₀[1/g_s]` at a product of generators has a chosen étale lift over `A`, with
restriction maps between these lifts and comparison maps to the localizations of `C`.

## Main results

* `SquareZero.Setup`: the standing hypotheses of the construction.
* `SquareZero.liftE`, `SquareZero.resE`: the étale lifts of the `B₀[1/g_s]` and their
  restrictions.
* `SquareZero.psi`: the comparison maps from the étale lifts to the localizations of `C`.
* `SquareZero.glueRing`: the ring glued from `C` and the étale lifts of the `B₀[1/f_i]`.
* `SquareZero.exists_reduction`, `SquareZero.glueReduction`: the reduction map from the glued
  ring to `B₀`, by formal glueing (Stacks 05EK).
-/

@[expose] public noncomputable section

open TensorProduct

universe u v

namespace SquareZero

variable {A : Type u} [CommRing A] (J : Ideal A) (T : Type v) [CommRing T] [Algebra A T]

section Core

variable {A : Type u} [CommRing A] (J : Ideal A) {r : ℕ} (f : Fin r → A)
  (B₀ : Type u) [CommRing B₀] [Algebra A B₀] [Algebra (A ⧸ J) B₀] [IsScalarTower A (A ⧸ J) B₀]

/-- The product of the generators indexed by `s`. -/
def prodGen (s : Finset (Fin r)) : A := ∏ k ∈ s, f k

/-- The localization of `B₀` at the product of the generators indexed by `s`. -/
abbrev locB (s : Finset (Fin r)) : Type u :=
  Localization.Away (algebraMap (A ⧸ J) B₀ (Ideal.Quotient.mk J (prodGen f s)))

/-- The product of the generators indexed by a nonempty `s` lies in any ideal containing them. -/
private theorem prodGen_mem_of_nonempty {I : Ideal A} (hf : ∀ k, f k ∈ I) {s : Finset (Fin r)}
    (hs : s.Nonempty) : prodGen f s ∈ I := by
  obtain ⟨k, hk⟩ := hs
  rw [prodGen, ← Finset.mul_prod_erase s f hk]
  exact Ideal.mul_mem_right _ _ (hf k)

omit [Algebra A B₀] [IsScalarTower A (A ⧸ J) B₀] in
/-- For a nonempty index set, the localization of `B₀` at the product of the corresponding
generators of `I` is étale over `A ⧸ J`, `B₀` being étale over the complement of `V(I)`. -/
theorem etale_locB [Algebra.FinitePresentation (A ⧸ J) B₀] (I : Ideal A)
    (hf : ∀ k, f k ∈ I)
    (hB₀ : ∀ q : Ideal B₀, ∀ _ : q.IsPrime,
      ¬ I.map (Ideal.Quotient.mk J) ≤ q.comap (algebraMap (A ⧸ J) B₀) →
        Algebra.IsEtaleAt (A ⧸ J) q)
    {s : Finset (Fin r)} (hs : s.Nonempty) : Algebra.Etale (A ⧸ J) (locB J f B₀ s) := by
  exact etale_localizationAway_of_isEtaleAt _ hB₀
    (Ideal.mem_map_of_mem _ (prodGen_mem_of_nonempty f hf hs))

omit [Algebra A B₀] [IsScalarTower A (A ⧸ J) B₀] in
/-- For `t ⊆ s`, the product of the generators indexed by `t` is a unit in `B₀[1/g_s]`. -/
theorem isUnit_locB {t s : Finset (Fin r)} (h : t ⊆ s) :
    IsUnit (algebraMap B₀ (locB J f B₀ s)
      (algebraMap (A ⧸ J) B₀ (Ideal.Quotient.mk J (prodGen f t)))) := by
  have hdvd : algebraMap (A ⧸ J) B₀ (Ideal.Quotient.mk J (prodGen f t)) ∣
      algebraMap (A ⧸ J) B₀ (Ideal.Quotient.mk J (prodGen f s)) :=
    map_dvd _ (map_dvd _ (Finset.prod_dvd_prod_of_subset t s f h))
  exact isUnit_of_dvd_unit (map_dvd _ hdvd) (IsLocalization.Away.algebraMap_isUnit _)

/-- The restriction `B₀[1/g_t] → B₀[1/g_s]` between localizations, for `t ⊆ s`. -/
noncomputable def locBRes {t s : Finset (Fin r)} (h : t ⊆ s) : locB J f B₀ t →ₐ[A] locB J f B₀ s :=
  { IsLocalization.Away.lift (S := locB J f B₀ t)
      (algebraMap (A ⧸ J) B₀ (Ideal.Quotient.mk J (prodGen f t))) (isUnit_locB J f B₀ h) with
    commutes' := fun a ↦ by
      change IsLocalization.Away.lift _ _ (algebraMap A (locB J f B₀ t) a) = _
      rw [IsScalarTower.algebraMap_apply A B₀ (locB J f B₀ t), IsLocalization.Away.lift_eq,
        ← IsScalarTower.algebraMap_apply] }

omit [IsScalarTower A (A ⧸ J) B₀] in
/-- `locBRes` restricts to the identity on `B₀`. -/
@[simp]
theorem locBRes_algebraMap {t s : Finset (Fin r)} (h : t ⊆ s) (b : B₀) :
    locBRes J f B₀ h (algebraMap B₀ (locB J f B₀ t) b) = algebraMap B₀ (locB J f B₀ s) b :=
  IsLocalization.Away.lift_eq _ (isUnit_locB J f B₀ h) b

/-- The standing hypotheses of the square-zero construction: `J² = 0`, and each localization of
`B₀` at a nonempty product of generators is étale over `A ⧸ J`. -/
structure Setup : Prop where
  /-- The ideal `J` has square zero. -/
  sq_eq_bot : J ^ 2 = ⊥
  /-- Each localization `B₀[1/g_s]` with `s` nonempty is étale over `A ⧸ J`. -/
  etale : ∀ s : Finset (Fin r), s.Nonempty → Algebra.Etale (A ⧸ J) (locB J f B₀ s)

variable {J f B₀}

/-- The étale lift over `A` of `B₀[1/g_s]`, for `s` nonempty. -/
abbrev liftE (σ : Setup J f B₀) (s : Finset (Fin r)) (hs : s.Nonempty) : Type u :=
  haveI := σ.etale s hs
  etaleLift J (locB J f B₀ s)

/-- The reduction of `liftE` onto `B₀[1/g_s]`. -/
abbrev liftEπ (σ : Setup J f B₀) (s : Finset (Fin r)) (hs : s.Nonempty) :
    liftE σ s hs →ₐ[A] locB J f B₀ s :=
  haveI := σ.etale s hs
  etaleLiftπ J (locB J f B₀ s)

/-- The kernel of the reduction of `liftE` onto `B₀[1/g_s]` is nilpotent. -/
theorem isNilpotent_ker_liftEπ (σ : Setup J f B₀) (s : Finset (Fin r)) (hs : s.Nonempty) :
    IsNilpotent (RingHom.ker (liftEπ σ s hs : liftE σ s hs →+* locB J f B₀ s)) := by
  have := σ.etale s hs
  change IsNilpotent (RingHom.ker (etaleLiftπ J (locB J f B₀ s) :
    etaleLift J (locB J f B₀ s) →+* locB J f B₀ s))
  rw [ker_etaleLiftπ]
  exact isNilpotent_map J _ σ.sq_eq_bot

/-- The reduction of `liftE` onto `B₀[1/g_s]` is surjective. -/
theorem surjective_liftEπ (σ : Setup J f B₀) (s : Finset (Fin r)) (hs : s.Nonempty) :
    Function.Surjective (liftEπ σ s hs) := by
  have := σ.etale s hs
  exact surjective_etaleLiftπ J (locB J f B₀ s)

/-- The lift `liftE` is étale over `A`. -/
instance (σ : Setup J f B₀) (s : Finset (Fin r)) (hs : s.Nonempty) :
    Algebra.Etale A (liftE σ s hs) := by
  have := σ.etale s hs
  exact inferInstanceAs (Algebra.Etale A (etaleLift J (locB J f B₀ s)))

/-- The restriction `liftE t → liftE s` for `t ⊆ s`, lifting `B₀[1/g_t] → B₀[1/g_s]`. -/
noncomputable def resE (σ : Setup J f B₀) {t s : Finset (Fin r)} (ht : t.Nonempty)
    (hs : s.Nonempty) (h : t ⊆ s) : liftE σ t ht →ₐ[A] liftE σ s hs :=
  Algebra.FormallySmooth.liftOfSurjective ((locBRes J f B₀ h).comp (liftEπ σ t ht))
    (liftEπ σ s hs) (surjective_liftEπ σ s hs) (isNilpotent_ker_liftEπ σ s hs)

/-- The restriction `resE` lifts the restriction `locBRes` of localizations of `B₀`. -/
theorem liftEπ_resE (σ : Setup J f B₀) {t s : Finset (Fin r)} (ht : t.Nonempty)
    (hs : s.Nonempty) (h : t ⊆ s) (x : liftE σ t ht) :
    liftEπ σ s hs (resE σ ht hs h x) = locBRes J f B₀ h (liftEπ σ t ht x) :=
  Algebra.FormallySmooth.liftOfSurjective_apply _ _ _ _ x

omit [IsScalarTower A (A ⧸ J) B₀] in
/-- The restrictions `locBRes` compose. -/
theorem locBRes_comp {t s u : Finset (Fin r)} (h : t ⊆ s) (h' : s ⊆ u) :
    (locBRes J f B₀ h').comp (locBRes J f B₀ h) = locBRes J f B₀ (h.trans h') := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers
    (algebraMap (A ⧸ J) B₀ (Ideal.Quotient.mk J (prodGen f t))))
  ext b
  simp

/-- Two `A`-algebra maps out of `liftE t` which agree after reduction onto `B₀[1/g_s]` agree. -/
theorem resE_ext (σ : Setup J f B₀) {t s : Finset (Fin r)} (ht : t.Nonempty) (hs : s.Nonempty)
    {φ₁ φ₂ : liftE σ t ht →ₐ[A] liftE σ s hs}
    (h : (liftEπ σ s hs).comp φ₁ = (liftEπ σ s hs).comp φ₂) : φ₁ = φ₂ :=
  Algebra.FormallyUnramified.lift_unique' _ (isNilpotent_ker_liftEπ σ s hs) _ _ h

/-- The restrictions between étale lifts are functorial. -/
theorem resE_comp (σ : Setup J f B₀) {t s u : Finset (Fin r)} (ht : t.Nonempty)
    (hs : s.Nonempty) (hu : u.Nonempty) (h : t ⊆ s) (h' : s ⊆ u) :
    (resE σ hs hu h').comp (resE σ ht hs h) = resE σ ht hu (h.trans h') := by
  apply resE_ext σ ht hu
  ext x
  simp only [AlgHom.comp_apply, liftEπ_resE]
  rw [← AlgHom.comp_apply (locBRes J f B₀ h'), locBRes_comp]

/-- The restrictions `resE` compose. -/
theorem resE_comp_apply (σ : Setup J f B₀) {t s u : Finset (Fin r)} (ht : t.Nonempty)
    (hs : s.Nonempty) (hu : u.Nonempty) (h : t ⊆ s) (h' : s ⊆ u) (x : liftE σ t ht) :
    resE σ hs hu h' (resE σ ht hs h x) = resE σ ht hu (h.trans h') x :=
  AlgHom.congr_fun (resE_comp σ ht hs hu h h') x

/-- The restriction `resE` from `s` to itself is the identity. -/
theorem resE_self (σ : Setup J f B₀) {s : Finset (Fin r)} (hs : s.Nonempty) (h : s ⊆ s) :
    resE σ hs hs h = AlgHom.id A _ := by
  apply resE_ext σ hs hs
  ext x
  simp only [AlgHom.comp_apply, liftEπ_resE, AlgHom.id_apply]
  have : locBRes J f B₀ h = AlgHom.id A _ := by
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers
      (algebraMap (A ⧸ J) B₀ (Ideal.Quotient.mk J (prodGen f s))))
    ext b
    simp
  rw [this, AlgHom.id_apply]

end Core

section CSide

variable {A : Type u} [CommRing A] (J : Ideal A) {r : ℕ} (f : Fin r → A)
  (C : Type u) [CommRing C] [Algebra A C]

/-- The localization of `C` at the product of the generators indexed by `s`. -/
abbrev locC (s : Finset (Fin r)) : Type u := Localization.Away (algebraMap A C (prodGen f s))

/-- The localization of `C ⧸ JC` at the product of the generators indexed by `s`. -/
abbrev locC₀ (s : Finset (Fin r)) : Type u :=
  Localization.Away (Ideal.Quotient.mk (J.map (algebraMap A C)) (algebraMap A C (prodGen f s)))

/-- The reduction `C[1/g_s] → (C ⧸ JC)[1/g_s]`, as a ring map. -/
noncomputable def redCRingHom (s : Finset (Fin r)) : locC f C s →+* locC₀ J f C s :=
  IsLocalization.Away.map (locC f C s) (locC₀ J f C s)
    (Ideal.Quotient.mk (J.map (algebraMap A C))) (algebraMap A C (prodGen f s))

/-- `redCRingHom` sends the image of `c ∈ C` to the image of its class in `C ⧸ JC`. -/
theorem redCRingHom_algebraMap (s : Finset (Fin r)) (c : C) :
    redCRingHom J f C s (algebraMap C (locC f C s) c) =
      algebraMap (C ⧸ J.map (algebraMap A C)) (locC₀ J f C s)
        (Ideal.Quotient.mk (J.map (algebraMap A C)) c) := by
  simp only [redCRingHom, IsLocalization.Away.map, IsLocalization.map_eq]

/-- The reduction `C[1/g_s] → (C ⧸ JC)[1/g_s]`. -/
noncomputable def redC (s : Finset (Fin r)) : locC f C s →ₐ[A] locC₀ J f C s :=
  { redCRingHom J f C s with
    commutes' := fun a ↦ by
      change redCRingHom J f C s (algebraMap A (locC f C s) a) = _
      rw [IsScalarTower.algebraMap_apply A C (locC f C s), redCRingHom_algebraMap]
      exact (IsScalarTower.algebraMap_apply A (C ⧸ J.map (algebraMap A C)) _ a).symm }

/-- `redC` sends the image of `c ∈ C` to the image of its class in `C ⧸ JC`. -/
theorem redC_algebraMap (s : Finset (Fin r)) (c : C) :
    redC J f C s (algebraMap C (locC f C s) c) =
      algebraMap (C ⧸ J.map (algebraMap A C)) (locC₀ J f C s)
        (Ideal.Quotient.mk (J.map (algebraMap A C)) c) :=
  redCRingHom_algebraMap J f C s c

/-- The reduction `C[1/g_s] → (C ⧸ JC)[1/g_s]` is surjective. -/
theorem surjective_redC (s : Finset (Fin r)) : Function.Surjective (redC J f C s) := by
  intro y
  obtain ⟨⟨c₀, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Submonoid.powers (Ideal.Quotient.mk (J.map (algebraMap A C)) (algebraMap A C (prodGen f s))))
    y
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c₀
  refine ⟨IsLocalization.mk' (locC f C s) c
    (⟨(algebraMap A C (prodGen f s)) ^ n, n, rfl⟩ : Submonoid.powers _), ?_⟩
  change redCRingHom J f C s _ = _
  simp only [redCRingHom, IsLocalization.Away.map, IsLocalization.map_mk']
  congr 1

/-- For `J² = 0`, the kernel of the reduction `C[1/g_s] → (C ⧸ JC)[1/g_s]` is nilpotent. -/
theorem isNilpotent_ker_redC (hJ : J ^ 2 = ⊥) (s : Finset (Fin r)) :
    IsNilpotent (RingHom.ker (redC J f C s : locC f C s →+* locC₀ J f C s)) :=
  isNilpotent_ker_localization_map J C hJ (algebraMap A C (prodGen f s)) (locC f C s)
    (locC₀ J f C s)

end CSide

section Psi

variable {A : Type u} [CommRing A] {J : Ideal A} {r : ℕ} {f : Fin r → A}
  {B₀ : Type u} [CommRing B₀] [Algebra A B₀] [Algebra (A ⧸ J) B₀] [IsScalarTower A (A ⧸ J) B₀]
  (C : Type u) [CommRing C] [Algebra A C]
  [Algebra B₀ (C ⧸ J.map (algebraMap A C))] [IsScalarTower A B₀ (C ⧸ J.map (algebraMap A C))]

/-- The product of the generators indexed by `s` becomes a unit in `(C ⧸ JC)[1/g_s]`. -/
theorem isUnit_locBC (s : Finset (Fin r)) :
    IsUnit ((algebraMap (C ⧸ J.map (algebraMap A C)) (locC₀ J f C s)).comp
      (algebraMap B₀ (C ⧸ J.map (algebraMap A C)))
        (algebraMap (A ⧸ J) B₀ (Ideal.Quotient.mk J (prodGen f s)))) := by
  have h : algebraMap B₀ (C ⧸ J.map (algebraMap A C))
      (algebraMap (A ⧸ J) B₀ (Ideal.Quotient.mk J (prodGen f s))) =
      Ideal.Quotient.mk (J.map (algebraMap A C)) (algebraMap A C (prodGen f s)) := by
    rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply A (A ⧸ J) B₀,
      ← IsScalarTower.algebraMap_apply A B₀]
    rfl
  rw [RingHom.comp_apply, h]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The comparison `B₀[1/g_s] → (C ⧸ JC)[1/g_s]` induced by `B₀ → C ⧸ JC`. -/
noncomputable def locBC (s : Finset (Fin r)) : locB J f B₀ s →ₐ[A] locC₀ J f C s :=
  { IsLocalization.Away.lift (S := locB J f B₀ s)
      (algebraMap (A ⧸ J) B₀ (Ideal.Quotient.mk J (prodGen f s))) (isUnit_locBC C s) with
    commutes' := fun a ↦ by
      change IsLocalization.Away.lift _ _ (algebraMap A (locB J f B₀ s) a) = _
      rw [IsScalarTower.algebraMap_apply A B₀ (locB J f B₀ s), IsLocalization.Away.lift_eq,
        RingHom.comp_apply, ← IsScalarTower.algebraMap_apply A B₀,
        ← IsScalarTower.algebraMap_apply] }

/-- `locBC` restricts to the structure map `B₀ → C ⧸ JC` on `B₀`. -/
theorem locBC_algebraMap (s : Finset (Fin r)) (b : B₀) :
    locBC C s (algebraMap B₀ (locB J f B₀ s) b) =
      algebraMap (C ⧸ J.map (algebraMap A C)) (locC₀ J f C s)
        (algebraMap B₀ (C ⧸ J.map (algebraMap A C)) b) :=
  IsLocalization.Away.lift_eq _ (isUnit_locBC C s) b

/-- The map `ψ_s : liftE s → C[1/g_s]` lifting `B₀[1/g_s] → (C ⧸ JC)[1/g_s]` through the reduction
of `C[1/g_s]`. -/
noncomputable def psi (σ : Setup J f B₀) (s : Finset (Fin r)) (hs : s.Nonempty) :
    liftE σ s hs →ₐ[A] locC f C s :=
  Algebra.FormallySmooth.liftOfSurjective ((locBC C s).comp (liftEπ σ s hs)) (redC J f C s)
    (surjective_redC J f C s) (isNilpotent_ker_redC J f C σ.sq_eq_bot s)

/-- `ψ_s` lifts `locBC` through the reductions of `liftE` and of `C[1/g_s]`. -/
theorem redC_psi (σ : Setup J f B₀) (s : Finset (Fin r)) (hs : s.Nonempty) (x : liftE σ s hs) :
    redC J f C s (psi C σ s hs x) = locBC C s (liftEπ σ s hs x) :=
  Algebra.FormallySmooth.liftOfSurjective_apply _ _ _ _ x

end Psi

section Restrictions

variable {A : Type u} [CommRing A] (J : Ideal A) {r : ℕ} (f : Fin r → A)
  (C : Type u) [CommRing C] [Algebra A C]

/-- For `t ⊆ s`, the product of the generators indexed by `t` divides the one indexed by `s`. -/
theorem prodGen_dvd {t s : Finset (Fin r)} (h : t ⊆ s) : prodGen f t ∣ prodGen f s :=
  Finset.prod_dvd_prod_of_subset t s f h

/-- For `t ⊆ s`, the product of the generators indexed by `t` is a unit in `C[1/g_s]`. -/
theorem isUnit_locC {t s : Finset (Fin r)} (h : t ⊆ s) :
    IsUnit (algebraMap C (locC f C s) (algebraMap A C (prodGen f t))) :=
  isUnit_of_dvd_unit (map_dvd _ (map_dvd _ (prodGen_dvd f h)))
    (IsLocalization.Away.algebraMap_isUnit _)

/-- For `t ⊆ s`, the product of the generators indexed by `t` is a unit in `(C ⧸ JC)[1/g_s]`. -/
theorem isUnit_locC₀ {t s : Finset (Fin r)} (h : t ⊆ s) :
    IsUnit (algebraMap (C ⧸ J.map (algebraMap A C)) (locC₀ J f C s)
      (Ideal.Quotient.mk (J.map (algebraMap A C)) (algebraMap A C (prodGen f t)))) :=
  isUnit_of_dvd_unit (map_dvd _ (map_dvd _ (map_dvd _ (prodGen_dvd f h))))
    (IsLocalization.Away.algebraMap_isUnit _)

/-- The restriction `C[1/g_t] → C[1/g_s]` for `t ⊆ s`. -/
noncomputable def locCRes {t s : Finset (Fin r)} (h : t ⊆ s) : locC f C t →ₐ[A] locC f C s :=
  { IsLocalization.Away.lift (S := locC f C t) (algebraMap A C (prodGen f t))
      (g := algebraMap C (locC f C s)) (isUnit_locC f C h) with
    commutes' := fun a ↦ by
      change IsLocalization.Away.lift _ _ (algebraMap A (locC f C t) a) = _
      rw [IsScalarTower.algebraMap_apply A C (locC f C t), IsLocalization.Away.lift_eq,
        ← IsScalarTower.algebraMap_apply] }

/-- `locCRes` restricts to the identity on `C`. -/
theorem locCRes_algebraMap {t s : Finset (Fin r)} (h : t ⊆ s) (c : C) :
    locCRes f C h (algebraMap C (locC f C t) c) = algebraMap C (locC f C s) c :=
  IsLocalization.Away.lift_eq _ (isUnit_locC f C h) c

/-- The restriction `(C ⧸ JC)[1/g_t] → (C ⧸ JC)[1/g_s]` for `t ⊆ s`. -/
noncomputable def locC₀Res {t s : Finset (Fin r)} (h : t ⊆ s) :
    locC₀ J f C t →ₐ[A] locC₀ J f C s :=
  { IsLocalization.Away.lift (S := locC₀ J f C t)
      (Ideal.Quotient.mk (J.map (algebraMap A C)) (algebraMap A C (prodGen f t)))
      (g := algebraMap (C ⧸ J.map (algebraMap A C)) (locC₀ J f C s)) (isUnit_locC₀ J f C h) with
    commutes' := fun a ↦ by
      change IsLocalization.Away.lift _ _ (algebraMap A (locC₀ J f C t) a) = _
      rw [IsScalarTower.algebraMap_apply A (C ⧸ J.map (algebraMap A C)) (locC₀ J f C t),
        IsLocalization.Away.lift_eq, ← IsScalarTower.algebraMap_apply] }

/-- `locC₀Res` restricts to the identity on `C ⧸ JC`. -/
theorem locC₀Res_algebraMap {t s : Finset (Fin r)} (h : t ⊆ s) (c : C ⧸ J.map (algebraMap A C)) :
    locC₀Res J f C h (algebraMap _ (locC₀ J f C t) c) = algebraMap _ (locC₀ J f C s) c :=
  IsLocalization.Away.lift_eq _ (isUnit_locC₀ J f C h) c

/-- The reductions `redC` commute with the restrictions of localizations of `C` and `C ⧸ JC`. -/
theorem redC_locCRes {t s : Finset (Fin r)} (h : t ⊆ s) :
    (redC J f C s).comp (locCRes f C h) = (locC₀Res J f C h).comp (redC J f C t) := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap A C (prodGen f t)))
  ext c
  simp [locCRes_algebraMap, redC_algebraMap, locC₀Res_algebraMap]

/-- The kernel of the reduction `C[1/g_s] → (C ⧸ JC)[1/g_s]` is `J C[1/g_s]`. -/
theorem ker_redC (s : Finset (Fin r)) :
    RingHom.ker (redC J f C s : locC f C s →+* locC₀ J f C s) =
      J.map (algebraMap A (locC f C s)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨c, ⟨_, n, rfl⟩, rfl⟩ : ∃ (c : C) (t : Submonoid.powers (algebraMap A C (prodGen f s))),
        IsLocalization.mk' (locC f C s) c t = x :=
      Prod.exists.mp (IsLocalization.mk'_surjective _ x)
    rw [RingHom.mem_ker] at hx
    change redCRingHom J f C s _ = 0 at hx
    simp only [redCRingHom, IsLocalization.Away.map, IsLocalization.map_mk'] at hx
    rw [IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := hx
    have hmem : (algebraMap A C (prodGen f s)) ^ m * c ∈ J.map (algebraMap A C) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow]
      simpa using hm
    have hx' : IsLocalization.mk' (locC f C s) c
        (⟨(algebraMap A C (prodGen f s)) ^ n, n, rfl⟩ :
          Submonoid.powers (algebraMap A C (prodGen f s))) =
        algebraMap C (locC f C s) ((algebraMap A C (prodGen f s)) ^ m * c) *
          IsLocalization.mk' (locC f C s) (1 : C)
            (⟨(algebraMap A C (prodGen f s)) ^ (m + n), m + n, rfl⟩ :
              Submonoid.powers (algebraMap A C (prodGen f s))) := by
      rw [← IsLocalization.mk'_one (M := Submonoid.powers (algebraMap A C (prodGen f s)))
        (locC f C s), ← IsLocalization.mk'_mul, mul_one, IsLocalization.mk'_eq_iff_eq]
      simp only [pow_add, one_mul]
      ring_nf
    rw [hx']
    have hmap : J.map (algebraMap A (locC f C s)) =
        (J.map (algebraMap A C)).map (algebraMap C (locC f C s)) := by
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    rw [hmap]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hmem)
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change redC J f C s (algebraMap A (locC f C s) a) = 0
    rw [AlgHom.commutes,
      IsScalarTower.algebraMap_apply A (C ⧸ J.map (algebraMap A C)) (locC₀ J f C s)]
    have : algebraMap A (C ⧸ J.map (algebraMap A C)) a = 0 := by
      change Ideal.Quotient.mk (J.map (algebraMap A C)) (algebraMap A C a) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ ha
    rw [this, map_zero]

/-- For a nonempty index set, the localization of `C` at the product of the corresponding
generators of `I` is étale over `A`, `C` being étale over the complement of `V(I)`. -/
theorem etale_locC [Algebra.FinitePresentation A C] (I : Ideal A) (hf : ∀ k, f k ∈ I)
    (hC : ∀ q : Ideal C, ∀ _ : q.IsPrime, ¬ I ≤ q.comap (algebraMap A C) → Algebra.IsEtaleAt A q)
    {s : Finset (Fin r)} (hs : s.Nonempty) : Algebra.Etale A (locC f C s) := by
  exact etale_localizationAway_of_isEtaleAt I hC (prodGen_mem_of_nonempty f hf hs)

end Restrictions

section PsiRes

variable {A : Type u} [CommRing A] {J : Ideal A} {r : ℕ} {f : Fin r → A}
  {B₀ : Type u} [CommRing B₀] [Algebra A B₀] [Algebra (A ⧸ J) B₀] [IsScalarTower A (A ⧸ J) B₀]
  (C : Type u) [CommRing C] [Algebra A C]
  [Algebra B₀ (C ⧸ J.map (algebraMap A C))] [IsScalarTower A B₀ (C ⧸ J.map (algebraMap A C))]

/-- The comparisons `locBC` commute with the restrictions of localizations of `B₀` and `C ⧸ JC`. -/
theorem locBC_locBRes {t s : Finset (Fin r)} (h : t ⊆ s) :
    (locBC C s).comp (locBRes J f B₀ h) = (locC₀Res J f C h).comp (locBC C t) := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers
    (algebraMap (A ⧸ J) B₀ (Ideal.Quotient.mk J (prodGen f t))))
  ext b
  simp [locBC_algebraMap, locC₀Res_algebraMap]

/-- The comparison maps commute with restriction. -/
theorem psi_resE (σ : Setup J f B₀) {t s : Finset (Fin r)} (ht : t.Nonempty) (hs : s.Nonempty)
    (h : t ⊆ s) :
    (psi C σ s hs).comp (resE σ ht hs h) = (locCRes f C h).comp (psi C σ t ht) := by
  apply Algebra.FormallyUnramified.lift_unique' (redC J f C s)
    (isNilpotent_ker_redC J f C σ.sq_eq_bot s)
  ext x
  simp only [AlgHom.comp_apply, redC_psi, liftEπ_resE]
  rw [← AlgHom.comp_apply (redC J f C s), redC_locCRes, AlgHom.comp_apply, redC_psi,
    ← AlgHom.comp_apply (locBC C s), locBC_locBRes, AlgHom.comp_apply]

/-- The maps `ψ_s` commute with the restrictions `resE` and `locCRes`. -/
theorem psi_resE_apply (σ : Setup J f B₀) {t s : Finset (Fin r)} (ht : t.Nonempty)
    (hs : s.Nonempty) (h : t ⊆ s) (x : liftE σ t ht) :
    psi C σ s hs (resE σ ht hs h x) = locCRes f C h (psi C σ t ht x) :=
  AlgHom.congr_fun (psi_resE C σ ht hs h) x

end PsiRes

section GlueRing

variable {A : Type u} [CommRing A] {J : Ideal A} {r : ℕ} {f : Fin r → A}
  {B₀ : Type u} [CommRing B₀] [Algebra A B₀] [Algebra (A ⧸ J) B₀] [IsScalarTower A (A ⧸ J) B₀]
  (C : Type u) [CommRing C] [Algebra A C]
  [Algebra B₀ (C ⧸ J.map (algebraMap A C))] [IsScalarTower A B₀ (C ⧸ J.map (algebraMap A C))]
  (σ : Setup J f B₀)

/-- `{i}` is contained in `{i, j}`. -/
theorem singleton_subset_pair_left (i j : Fin r) : ({i} : Finset (Fin r)) ⊆ {i, j} := by simp
/-- `{j}` is contained in `{i, j}`. -/
theorem singleton_subset_pair_right (i j : Fin r) : ({j} : Finset (Fin r)) ⊆ {i, j} := by simp

/-- **The glued ring.** The `A`-algebra of pairs `(c, (e_i)_i)` with `c ∈ C` and `e_i` in the
étale lift of `B₀[1/f_i]`, such that each `e_i` maps to the image of `c` in `C[1/f_i]` and any
two `e_i, e_j` agree in the étale lift of `B₀[1/f_i f_j]`. -/
def glueRing : Subalgebra A (C × ∀ i : Fin r, liftE σ {i} (Finset.singleton_nonempty i)) where
  carrier := {x | (∀ i, psi C σ {i} (Finset.singleton_nonempty i) (x.2 i) =
      algebraMap C (locC f C {i}) x.1) ∧
    ∀ i j, resE σ (Finset.singleton_nonempty i) (Finset.insert_nonempty i {j})
        (singleton_subset_pair_left i j) (x.2 i) =
      resE σ (Finset.singleton_nonempty j) (Finset.insert_nonempty i {j})
        (singleton_subset_pair_right i j) (x.2 j)}
  mul_mem' := by
    rintro x y ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩
    exact ⟨fun i ↦ by simp [hx₁ i, hy₁ i], fun i j ↦ by simp [hx₂ i j, hy₂ i j]⟩
  add_mem' := by
    rintro x y ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩
    exact ⟨fun i ↦ by simp [hx₁ i, hy₁ i], fun i j ↦ by simp [hx₂ i j, hy₂ i j]⟩
  algebraMap_mem' := by
    intro a
    refine ⟨fun i ↦ ?_, fun i j ↦ ?_⟩
    · change psi C σ {i} _ (algebraMap A _ a) = algebraMap C (locC f C {i})
        (algebraMap A C a)
      rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
    · change resE σ _ _ _ (algebraMap A _ a) = resE σ _ _ _ (algebraMap A _ a)
      rw [AlgHom.commutes, AlgHom.commutes]

end GlueRing

section Reduction

variable {A : Type u} [CommRing A] {J : Ideal A} {r : ℕ} {f : Fin r → A}
  {B₀ : Type u} [CommRing B₀] [Algebra A B₀] [Algebra (A ⧸ J) B₀] [IsScalarTower A (A ⧸ J) B₀]
  (C : Type u) [CommRing C] [Algebra A C]
  [Algebra B₀ (C ⧸ J.map (algebraMap A C))] [IsScalarTower A B₀ (C ⧸ J.map (algebraMap A C))]

variable (J f B₀) in
/-- The images in `B₀` of the generators of `I`. -/
abbrev genB (k : Fin r) : B₀ := algebraMap (A ⧸ J) B₀ (Ideal.Quotient.mk J (f k))

variable (J f B₀) in
omit [Algebra A B₀] [IsScalarTower A (A ⧸ J) B₀] in
/-- The image in `B₀` of the product of the generators indexed by `s` is the product of the
`genB`. -/
theorem genB_prod (s : Finset (Fin r)) :
    algebraMap (A ⧸ J) B₀ (Ideal.Quotient.mk J (prodGen f s)) = ∏ k ∈ s, genB J f B₀ k := by
  simp [prodGen, map_prod]

omit [Algebra A B₀] [IsScalarTower A (A ⧸ J) B₀] in
/-- Being a localization only depends on the submonoid, not on how it is written. -/
theorem _root_.IsLocalization.of_submonoid_eq {R S : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] {M M' : Submonoid R} (h : M = M') [IsLocalization M S] : IsLocalization M' S :=
  h ▸ inferInstance

variable (J f B₀) in
omit [Algebra A B₀] [IsScalarTower A (A ⧸ J) B₀] in
/-- `B₀[1/g_i]` is the localization of `B₀` at the powers of `genB i`. -/
theorem isLocalization_locB_singleton (i : Fin r) :
    IsLocalization (Submonoid.powers (genB J f B₀ i)) (locB J f B₀ {i}) := by
  have h : IsLocalization (Submonoid.powers
      (algebraMap (A ⧸ J) B₀ (Ideal.Quotient.mk J (prodGen f {i})))) (locB J f B₀ {i}) :=
    inferInstance
  exact IsLocalization.of_submonoid_eq (S := locB J f B₀ {i})
    (M := Submonoid.powers (algebraMap (A ⧸ J) B₀ (Ideal.Quotient.mk J (prodGen f {i}))))
    (by rw [genB_prod, Finset.prod_singleton])

variable (J f B₀) in
omit [Algebra A B₀] [IsScalarTower A (A ⧸ J) B₀] in
/-- For `i ≠ j`, `locB {i, j}` is the localization of `B₀` at the powers of
`genB i * genB j`. -/
theorem isLocalization_locB_pair {i j : Fin r} (hij : i ≠ j) :
    IsLocalization (Submonoid.powers (genB J f B₀ i * genB J f B₀ j)) (locB J f B₀ {i, j}) := by
  have h : IsLocalization (Submonoid.powers
      (algebraMap (A ⧸ J) B₀ (Ideal.Quotient.mk J (prodGen f {i, j})))) (locB J f B₀ {i, j}) :=
    inferInstance
  exact IsLocalization.of_submonoid_eq (S := locB J f B₀ {i, j})
    (M := Submonoid.powers (algebraMap (A ⧸ J) B₀ (Ideal.Quotient.mk J (prodGen f {i, j}))))
    (by rw [genB_prod, Finset.prod_pair hij])

/-- The image of `genB k` in `C ⧸ JC` is the class of `f k`. -/
theorem algebraMap_genB (k : Fin r) :
    algebraMap B₀ (C ⧸ J.map (algebraMap A C)) (genB J f B₀ k) =
      Ideal.Quotient.mk (J.map (algebraMap A C)) (algebraMap A C (f k)) := by
  rw [genB, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply A (A ⧸ J) B₀,
    ← IsScalarTower.algebraMap_apply A B₀]
  rfl

/-- `(C ⧸ JC)[1/g_i]` is the localization of the `B₀`-module `C ⧸ JC` at the powers of `genB i`. -/
theorem isLocalizedModule_locC₀_singleton (i : Fin r) :
    IsLocalizedModule (Submonoid.powers (genB J f B₀ i))
      (IsScalarTower.toAlgHom B₀ (C ⧸ J.map (algebraMap A C)) (locC₀ J f C {i})).toLinearMap := by
  rw [isLocalizedModule_iff_isLocalization, Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  have h : IsLocalization (Submonoid.powers (Ideal.Quotient.mk (J.map (algebraMap A C))
      (algebraMap A C (prodGen f {i})))) (locC₀ J f C {i}) := inferInstance
  exact IsLocalization.of_submonoid_eq (S := locC₀ J f C {i})
    (M := Submonoid.powers (Ideal.Quotient.mk (J.map (algebraMap A C))
      (algebraMap A C (prodGen f {i}))))
    (by rw [algebraMap_genB, prodGen, Finset.prod_singleton])

/-- `locBRes` as a `B₀`-linear map. -/
def locBResLin {t s : Finset (Fin r)} (h : t ⊆ s) : locB J f B₀ t →ₗ[B₀] locB J f B₀ s where
  toFun := locBRes J f B₀ h
  map_add' := map_add _
  map_smul' := fun b x ↦ by
    simp only [Algebra.smul_def, map_mul, locBRes_algebraMap, RingHom.id_apply]

/-- `locBC` as a `B₀`-linear map. -/
def locBCLin (s : Finset (Fin r)) : locB J f B₀ s →ₗ[B₀] locC₀ J f C s where
  toFun := locBC C s
  map_add' := map_add _
  map_smul' := fun b x ↦ by
    simp only [Algebra.smul_def, map_mul, locBC_algebraMap, RingHom.id_apply]
    rfl

/-- **The reduction of a glued element.** Every element `(c, e)` of the glued ring has a unique
reduction `b ∈ B₀`: an element whose image in `C ⧸ JC` is the class of `c` and whose image in each
`B₀[1/f_i]` is the reduction of `e_i`. Existence is formal glueing (Stacks 05EK) for the flat map
`B₀ → C ⧸ JC`, an isomorphism modulo `I`. -/
theorem exists_reduction (σ : Setup J f B₀)
    (hflat : Module.Flat B₀ (C ⧸ J.map (algebraMap A C)))
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range (genB J f B₀))).map (algebraMap B₀ (C ⧸ J.map (algebraMap A C))))
      (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) Ideal.le_comap_map))
    (x : glueRing C σ) :
    ∃ b : B₀, algebraMap B₀ (C ⧸ J.map (algebraMap A C)) b =
        Ideal.Quotient.mk (J.map (algebraMap A C)) x.1.1 ∧
      ∀ i, algebraMap B₀ (locB J f B₀ {i}) b =
        liftEπ σ {i} (Finset.singleton_nonempty i) (x.1.2 i) := by
  have h₁ : ∀ i, IsLocalization (Submonoid.powers (genB J f B₀ i)) (locB J f B₀ {i}) :=
    fun i ↦ isLocalization_locB_singleton J f B₀ i
  have h₂ : ∀ i, IsLocalizedModule (Submonoid.powers (genB J f B₀ i))
      (IsScalarTower.toAlgHom B₀ (C ⧸ J.map (algebraMap A C)) (locC₀ J f C {i})).toLinearMap :=
    fun i ↦ isLocalizedModule_locC₀_singleton C i
  obtain ⟨b, hb₁, hb₂⟩ := FormalGlueing.glueing_exact_middle_of_models B₀
    (C ⧸ J.map (algebraMap A C)) (genB J f B₀) B₀ hflat hq
    (Algebra.linearMap B₀ (C ⧸ J.map (algebraMap A C)))
    (IsBaseChange.linearMap B₀ (C ⧸ J.map (algebraMap A C)))
    (fun i ↦ Algebra.linearMap B₀ (locB J f B₀ {i}))
    (fun i j ↦ Algebra.linearMap B₀ (locB J f B₀ {i, j}))
    (fun i j hij ↦ by have := isLocalization_locB_pair J f B₀ hij; infer_instance)
    (fun i ↦ (IsScalarTower.toAlgHom B₀ (C ⧸ J.map (algebraMap A C)) (locC₀ J f C {i})).toLinearMap)
    (fun i j ↦ locBResLin (singleton_subset_pair_left i j))
    (fun i j ↦ LinearMap.ext fun b ↦ locBRes_algebraMap J f B₀ (singleton_subset_pair_left i j) b)
    (fun i j ↦ locBResLin (singleton_subset_pair_right i j))
    (fun i j ↦ LinearMap.ext fun b ↦ locBRes_algebraMap J f B₀ (singleton_subset_pair_right i j) b)
    (fun i ↦ locBCLin C {i})
    (fun i ↦ LinearMap.ext fun b ↦ locBC_algebraMap C {i} b)
    (Ideal.Quotient.mk _ x.1.1) (fun i ↦ liftEπ σ {i} (Finset.singleton_nonempty i) (x.1.2 i))
    (fun i ↦ by
      change algebraMap (C ⧸ J.map (algebraMap A C)) (locC₀ J f C {i})
          (Ideal.Quotient.mk (J.map (algebraMap A C)) x.1.1) =
        locBC C {i} (liftEπ σ {i} (Finset.singleton_nonempty i) (x.1.2 i))
      rw [← redC_psi, x.2.1 i, redC_algebraMap])
    (fun i j _ ↦ by
      change locBRes J f B₀ (singleton_subset_pair_left i j)
          (liftEπ σ {i} (Finset.singleton_nonempty i) (x.1.2 i)) =
        locBRes J f B₀ (singleton_subset_pair_right i j)
          (liftEπ σ {j} (Finset.singleton_nonempty j) (x.1.2 j))
      rw [← liftEπ_resE, ← liftEπ_resE, x.2.2 i j])
  exact ⟨b, hb₁, hb₂⟩

omit [Algebra A B₀] [IsScalarTower A (A ⧸ J) B₀]
    [IsScalarTower A B₀ (C ⧸ J.map (algebraMap A C))] in
/-- An element of `B₀` is determined by its images in `C ⧸ JC` and in the `B₀[1/f_i]`. -/
theorem eq_of_reductions (hflat : Module.Flat B₀ (C ⧸ J.map (algebraMap A C)))
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range (genB J f B₀))).map (algebraMap B₀ (C ⧸ J.map (algebraMap A C))))
      (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) Ideal.le_comap_map))
    {b b' : B₀} (h₀ : algebraMap B₀ (C ⧸ J.map (algebraMap A C)) b =
      algebraMap B₀ (C ⧸ J.map (algebraMap A C)) b')
    (h₁ : ∀ i, algebraMap B₀ (locB J f B₀ {i}) b = algebraMap B₀ (locB J f B₀ {i}) b') :
    b = b' := by
  have h₁' : ∀ i, IsLocalization (Submonoid.powers (genB J f B₀ i)) (locB J f B₀ {i}) :=
    fun i ↦ isLocalization_locB_singleton J f B₀ i
  rw [← sub_eq_zero]
  exact FormalGlueing.glueing_injective_of_models B₀ (C ⧸ J.map (algebraMap A C)) (genB J f B₀)
    B₀ hflat hq (Algebra.linearMap B₀ (C ⧸ J.map (algebraMap A C)))
    (IsBaseChange.linearMap B₀ (C ⧸ J.map (algebraMap A C)))
    (fun i ↦ Algebra.linearMap B₀ (locB J f B₀ {i})) (b - b')
    (by simp [h₀]) (fun i ↦ by simp [h₁ i])

variable {C} in
/-- **The reduction map** from the glued ring to `B₀`. -/
noncomputable def glueReduction (σ : Setup J f B₀)
    (hflat : Module.Flat B₀ (C ⧸ J.map (algebraMap A C)))
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range (genB J f B₀))).map (algebraMap B₀ (C ⧸ J.map (algebraMap A C))))
      (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) Ideal.le_comap_map)) :
    glueRing C σ →ₐ[A] B₀ where
  toFun x := (exists_reduction C σ hflat hq x).choose
  map_one' := by
    refine eq_of_reductions C hflat hq ?_ fun i ↦ ?_
    · rw [(exists_reduction C σ hflat hq 1).choose_spec.1, map_one]; rfl
    · rw [(exists_reduction C σ hflat hq 1).choose_spec.2 i, map_one]
      exact map_one _
  map_mul' x y := by
    refine eq_of_reductions C hflat hq ?_ fun i ↦ ?_
    · rw [(exists_reduction C σ hflat hq (x * y)).choose_spec.1, map_mul,
        (exists_reduction C σ hflat hq x).choose_spec.1,
        (exists_reduction C σ hflat hq y).choose_spec.1, ← map_mul]
      rfl
    · rw [(exists_reduction C σ hflat hq (x * y)).choose_spec.2 i, map_mul,
        (exists_reduction C σ hflat hq x).choose_spec.2 i,
        (exists_reduction C σ hflat hq y).choose_spec.2 i, ← map_mul]
      rfl
  map_zero' := by
    refine eq_of_reductions C hflat hq ?_ fun i ↦ ?_
    · rw [(exists_reduction C σ hflat hq 0).choose_spec.1, map_zero]; rfl
    · rw [(exists_reduction C σ hflat hq 0).choose_spec.2 i, map_zero]
      exact map_zero _
  map_add' x y := by
    refine eq_of_reductions C hflat hq ?_ fun i ↦ ?_
    · rw [(exists_reduction C σ hflat hq (x + y)).choose_spec.1, map_add,
        (exists_reduction C σ hflat hq x).choose_spec.1,
        (exists_reduction C σ hflat hq y).choose_spec.1, ← map_add]
      rfl
    · rw [(exists_reduction C σ hflat hq (x + y)).choose_spec.2 i, map_add,
        (exists_reduction C σ hflat hq x).choose_spec.2 i,
        (exists_reduction C σ hflat hq y).choose_spec.2 i, ← map_add]
      rfl
  commutes' a := by
    refine eq_of_reductions C hflat hq ?_ fun i ↦ ?_
    · rw [(exists_reduction C σ hflat hq (algebraMap A _ a)).choose_spec.1,
        ← IsScalarTower.algebraMap_apply]
      rfl
    · rw [(exists_reduction C σ hflat hq (algebraMap A _ a)).choose_spec.2 i,
        ← IsScalarTower.algebraMap_apply]
      exact (liftEπ σ {i} _).commutes a

end Reduction

end SquareZero
