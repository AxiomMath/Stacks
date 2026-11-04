module

public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.ValuationCenter
public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.Residue
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegreeClosedSubscheme

/-!
# Moving the places of a curve by an automorphism of its function field

Let `X` be a proper curve over a field `F` whose local rings at the places are discrete valuation
rings, and let `τ` be an automorphism of the function field `R(X)` fixing `F`. Since the places of
`X` are the proper valuation subrings of `R(X)` containing `F`
(`Stacks.BombieriStepanov.exists_curvePlace_mem_iff`), `τ` permutes them: the image `τ(𝒪_{X,P})`
is the local ring at a place `τ(P)`, and `ord_{τ(P)}(τ f) = ord_P(f)`. Two normalized discrete
valuations with the same valuation ring are equal, which is how the orders are compared.

This gives the hypothesis `hσ` of the twisted Stepanov bound
`Stacks.BombieriStepanov.exists_sum_curveDeg_add_one_le_twisted` for any `F`-automorphism of the
function field, without realizing it as an automorphism of the curve.

## Main results

* `Stacks.BombieriStepanov.zero_le_curveVal_iff`: `ord_P f ≥ 0` exactly on `𝒪_{X,P}`.
* `Stacks.BombieriStepanov.addValuation_eq_of_forall_zero_le_iff`: normalized `ℤ`-valuations with
  the same valuation ring are equal.
* `Stacks.BombieriStepanov.exists_curveVal_ringEquiv`: the place `τ(P)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace Stacks.BombieriStepanov

section Valuation

variable {K : Type*} [Field K]

/-- Two `ℤ`-valuations with the same nonnegative locus order any two nonzero elements the same
way: the comparison of `a` and `b` is the sign of the order of `b / a`. -/
private theorem ordZ_le_iff_of_forall_zero_le_iff {v w : AddValuation K (WithTop ℤ)}
    (hvw : ∀ f, 0 ≤ v f ↔ 0 ≤ w f) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    ordZ v a ≤ ordZ v b ↔ ordZ w a ≤ ordZ w b := by
  have hba : b / a ≠ 0 := div_ne_zero hb ha
  have hv' : ordZ v b = ordZ v (b / a) + ordZ v a := by
    rw [← ordZ_mul hba ha, div_mul_cancel₀ b ha]
  have hw' : ordZ w b = ordZ w (b / a) + ordZ w a := by
    rw [← ordZ_mul hba ha, div_mul_cancel₀ b ha]
  have h0 : 0 ≤ ordZ v (b / a) ↔ 0 ≤ ordZ w (b / a) := by
    rw [le_ordZ_iff hba, le_ordZ_iff hba]
    exact hvw _
  omega

/-- **Normalized discrete valuations with the same valuation ring are equal.** -/
theorem addValuation_eq_of_forall_zero_le_iff {v w : AddValuation K (WithTop ℤ)}
    (hvw : ∀ f, 0 ≤ v f ↔ 0 ≤ w f) (hv : ∃ π, v π = ((1 : ℤ) : WithTop ℤ))
    (hw : ∃ π, w π = ((1 : ℤ) : WithTop ℤ)) (f : K) : v f = w f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hcmp : ∀ a b : K, a ≠ 0 → b ≠ 0 → (ordZ v a ≤ ordZ v b ↔ ordZ w a ≤ ordZ w b) :=
    ordZ_le_iff_of_forall_zero_le_iff hvw
  have huni : ∀ (u : AddValuation K (WithTop ℤ)) (x : K), u x = ((1 : ℤ) : WithTop ℤ) →
      x ≠ 0 ∧ ordZ u x = 1 := by
    intro u x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    refine ⟨hx0, ?_⟩
    have := coe_ordZ (w := u) hx0
    rw [hx] at this
    exact_mod_cast this
  have h1 : ∀ u : AddValuation K (WithTop ℤ), ordZ u (1 : K) = 0 := by simp [ordZ]
  have hsign : ∀ x : K, x ≠ 0 → (0 < ordZ v x ↔ 0 < ordZ w x) := fun x hx => by
    have := (hcmp x 1 hx one_ne_zero).not
    rw [h1, h1] at this
    omega
  obtain ⟨π, hπ⟩ := hv
  obtain ⟨π', hπ'⟩ := hw
  obtain ⟨hπ0, hvπ⟩ := huni v π hπ
  obtain ⟨hπ'0, hwπ'⟩ := huni w π' hπ'
  have hwπ : ordZ w π = 1 := by
    have hpos := (hsign π hπ0).1 (by omega)
    have hpos' := (hsign π' hπ'0).2 (by omega)
    have hle := (hcmp π π' hπ0 hπ'0).1 (by omega)
    omega
  -- compare `f` with a power of `π`
  have key : ordZ v f = ordZ w f := by
    set n := ordZ v f with hn
    rcases le_or_gt 0 n with h | h
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h
      have hpm : π ^ m ≠ 0 := pow_ne_zero m hπ0
      have hv1 : ordZ v (π ^ m) = n := by rw [ordZ_pow hπ0, hvπ, hm]; ring
      have hw1 : ordZ w (π ^ m) = m := by rw [ordZ_pow hπ0, hwπ]; ring
      have ha := (hcmp f (π ^ m) hf hpm).1 (by omega)
      have hb := (hcmp (π ^ m) f hpm hf).1 (by omega)
      omega
    · obtain ⟨m, hm⟩ := Int.exists_eq_neg_ofNat h.le
      have hpm : π ^ m ≠ 0 := pow_ne_zero m hπ0
      have hfm : f * π ^ m ≠ 0 := mul_ne_zero hf hpm
      have hv1 : ordZ v (f * π ^ m) = 0 := by
        rw [ordZ_mul hf hpm, ordZ_pow hπ0, hvπ, ← hn, hm]; ring
      have := h1 v
      have := h1 w
      have ha := (hcmp (f * π ^ m) 1 hfm one_ne_zero).1 (by omega)
      have hb := (hcmp 1 (f * π ^ m) one_ne_zero hfm).1 (by omega)
      rw [ordZ_mul hf hpm, ordZ_pow hπ0, hwπ] at ha hb
      omega
  rw [← coe_ordZ hf, ← coe_ordZ hf, key]

end Valuation

section Curve

variable {F : Type u} [Field F] {X : Scheme.{u}} (p : X ⟶ Spec (.of F)) [IsIntegral X]
  [IsLocallyNoetherian X]
  (hdvr : ∀ x : X, coheight x = 1 → IsDiscreteValuationRing (X.presheaf.stalk x))

include hdvr in
/-- `ord_P f ≥ 0` exactly when `f` comes from the local ring at `P`. -/
theorem zero_le_curveVal_iff (P : CurvePlace X) (f : X.functionField) :
    0 ≤ curveVal hdvr P f ↔ ∃ a : X.presheaf.stalk P.1, algebraMap _ X.functionField a = f := by
  have := hdvr P.1 P.2
  rcases eq_or_ne f 0 with rfl | hf
  · simp only [AddValuation.map_zero, le_top, true_iff]
    exact ⟨0, map_zero _⟩
  rw [← coe_ordZ hf, ordZ_curveVal]
  show (((0 : ℤ) : WithTop ℤ)) ≤ _ ↔ _
  rw [WithTop.coe_le_coe]
  constructor
  · exact exists_algebraMap_eq_of_ord_nonneg P.2
  · rintro ⟨a, rfl⟩
    have ha : a ≠ 0 := by
      rintro rfl
      exact hf (map_zero _)
    exact ord_algebraMap_nonneg P.2 ha

include hdvr in
/-- A place has a uniformizer. -/
theorem exists_curveVal_eq_one (P : CurvePlace X) :
    ∃ π : X.functionField, curveVal hdvr P π = ((1 : ℤ) : WithTop ℤ) := by
  have := hdvr P.1 P.2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk P.1)
  have hπ0 : algebraMap (X.presheaf.stalk P.1) X.functionField π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hπ.ne_zero
  refine ⟨algebraMap (X.presheaf.stalk P.1) X.functionField π, ?_⟩
  rw [← coe_ordZ hπ0, ordZ_curveVal, ord_algebraMap_irreducible P.2 hπ]

include hdvr in
/-- An element of the local ring has `ord_P ≥ 1` exactly when it lies in the maximal ideal. -/
theorem one_le_curveVal_algebraMap_iff (P : CurvePlace X) (a : X.presheaf.stalk P.1) :
    ((1 : ℤ) : WithTop ℤ) ≤ curveVal hdvr P (algebraMap _ X.functionField a) ↔
      a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk P.1) := by
  have := hdvr P.1 P.2
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have ha' : algebraMap (X.presheaf.stalk P.1) X.functionField a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha
  rw [← coe_ordZ ha', ordZ_curveVal, WithTop.coe_le_coe]
  constructor
  · intro h hu
    obtain ⟨u, rfl⟩ := hu
    have h1 := ord_algebraMap_nonneg P.2 (u⁻¹ : (X.presheaf.stalk P.1)ˣ).ne_zero
    have h2 : X.ord (algebraMap _ X.functionField (u : X.presheaf.stalk P.1) *
        algebraMap _ X.functionField ((u⁻¹ : (X.presheaf.stalk P.1)ˣ) :
          X.presheaf.stalk P.1)) P.1 = 0 := by
      rw [← map_mul, Units.mul_inv, map_one, scheme_ord_one]
    rw [Scheme.ord_mul ha' ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
      (u⁻¹ : (X.presheaf.stalk P.1)ˣ).ne_zero)] at h2
    omega
  · exact one_le_ord_algebraMap P.2 ha

include hdvr in
/-- **Places with the same valuation are equal**, on a separated scheme. -/
theorem eq_of_forall_curveVal_eq [IsSeparated p] {P P' : CurvePlace X}
    (h : ∀ f, curveVal hdvr P f = curveVal hdvr P' f) : P = P' := by
  have := hdvr P.1 P.2
  have := hdvr P'.1 P'.2
  refine Subtype.ext (eq_of_forall_algebraMap_iff p fun f => ?_)
  rw [← zero_le_curveVal_iff hdvr P, ← zero_le_curveVal_iff hdvr P', h]

include hdvr in
/-- **An automorphism of the function field moves the places.** For an automorphism `τ` of
`R(X)` fixing `F` and a place `P` there is a place `P'` with `ord_{P'}(τ f) = ord_P(f)`. -/
theorem exists_curveVal_ringEquiv [UniversallyClosed p] [IsCurve F p]
    (τ : X.functionField ≃+* X.functionField)
    (hτ : ∀ c : F, τ ((fieldToStalk p (genericPoint X)).hom c) =
      (fieldToStalk p (genericPoint X)).hom c) (P : CurvePlace X) :
    ∃ P' : CurvePlace X, ∀ f, curveVal hdvr P' (τ f) = curveVal hdvr P f := by
  have := hdvr P.1 P.2
  set V := (stalkValuationSubring P.1).comap (τ.symm : X.functionField →+* X.functionField)
  have hV : ∀ g, g ∈ V ↔ 0 ≤ curveVal hdvr P (τ.symm g) := by
    intro g
    rw [ValuationSubring.mem_comap, zero_le_curveVal_iff hdvr P]
    rfl
  have hk : ∀ c : F, (fieldToStalk p (genericPoint X)).hom c ∈ V := by
    intro c
    rw [hV, zero_le_curveVal_iff hdvr P, τ.symm_apply_eq.2 (hτ c).symm]
    exact ⟨(fieldToStalk p P.1).hom c, (algebraMap_functionFieldAlgebra p P.1 c).symm⟩
  have hVtop : V ≠ ⊤ := by
    obtain ⟨π, hπ⟩ := exists_curveVal_eq_one hdvr P
    intro htop
    have hmem : τ π⁻¹ ∈ V := htop ▸ ValuationSubring.mem_top _
    rw [hV, RingEquiv.symm_apply_apply, AddValuation.map_inv, hπ] at hmem
    exact absurd hmem (by decide)
  obtain ⟨P', hP'⟩ := exists_curvePlace_mem_iff p hdvr V hk hVtop
  refine ⟨P', fun f => ?_⟩
  refine (addValuation_eq_of_forall_zero_le_iff (v := (curveVal hdvr P').comap
    (τ : X.functionField →+* X.functionField)) (w := curveVal hdvr P) (fun g => ?_) ?_
    (exists_curveVal_eq_one hdvr P) f)
  · show 0 ≤ curveVal hdvr P' (τ g) ↔ _
    rw [zero_le_curveVal_iff hdvr P', ← hP', hV, RingEquiv.symm_apply_apply]
  · obtain ⟨π, hπ⟩ := exists_curveVal_eq_one hdvr P'
    exact ⟨τ.symm π, by
      show curveVal hdvr P' (τ (τ.symm π)) = _
      rw [RingEquiv.apply_symm_apply, hπ]⟩

include hdvr in
/-- **An automorphism of the function field moves Riemann–Roch spaces.** For an automorphism
`τ` of `R(X)` fixing `F` and a place `P₀`, the place `P₁ = τ(P₀)` has `τ(L(n P₀)) ⊆ L(n P₁)`. -/
theorem exists_mapsTo_poleSpace [IsProper p] [IsCurve F p]
    (τ : X.functionField ≃+* X.functionField)
    (hτ : ∀ c : F, τ ((fieldToStalk p (genericPoint X)).hom c) =
      (fieldToStalk p (genericPoint X)).hom c) (P₀ : CurvePlace X) :
    ∃ P₁ : CurvePlace X, (∀ f, curveVal hdvr P₁ (τ f) = curveVal hdvr P₀ f) ∧
      ∀ n, ∀ y ∈ poleSpace (curveVal hdvr) P₀ n, τ y ∈ poleSpace (curveVal hdvr) P₁ n := by
  obtain ⟨P₁, hP₁⟩ := exists_curveVal_ringEquiv p hdvr τ hτ P₀
  have hτ' : ∀ c : F, τ.symm ((fieldToStalk p (genericPoint X)).hom c) =
      (fieldToStalk p (genericPoint X)).hom c := fun c => τ.symm_apply_eq.2 (hτ c).symm
  refine ⟨P₁, hP₁, fun n y hy => ⟨?_, fun P hP => ?_⟩⟩
  · rw [hP₁]
    exact hy.1
  · obtain ⟨Q, hQ⟩ := exists_curveVal_ringEquiv p hdvr τ.symm hτ' P
    have hQP₀ : Q ≠ P₀ := by
      rintro rfl
      refine hP (eq_of_forall_curveVal_eq p hdvr fun g => ?_)
      rw [← hQ g, ← hP₁ (τ.symm g), RingEquiv.apply_symm_apply]
    have := hQ (τ y)
    rw [RingEquiv.symm_apply_apply] at this
    rw [← this]
    exact hy.2 Q hQP₀

include hdvr in
/-- The residue field at `P` is `F` exactly when every regular function is congruent to a
constant modulo the maximal ideal. -/
theorem surjective_residue_iff (P : CurvePlace X) :
    Function.Surjective (fun c : F =>
      IsLocalRing.residue (X.presheaf.stalk P.1) ((fieldToStalk p P.1).hom c)) ↔
      ∀ y, 0 ≤ curveVal hdvr P y → ∃ c : F,
        ((1 : ℤ) : WithTop ℤ) ≤ curveVal hdvr P (y - (fieldToStalk p (genericPoint X)).hom c) := by
  have hc' : ∀ c : F, (fieldToStalk p (genericPoint X)).hom c =
      algebraMap _ X.functionField ((fieldToStalk p P.1).hom c) :=
    algebraMap_functionFieldAlgebra p P.1
  constructor
  · intro hs y hy
    obtain ⟨a, rfl⟩ := (zero_le_curveVal_iff hdvr P y).1 hy
    obtain ⟨c, hc⟩ := hs (IsLocalRing.residue _ a)
    refine ⟨c, ?_⟩
    rw [hc' c, ← map_sub, one_le_curveVal_algebraMap_iff hdvr P,
      ← IsLocalRing.residue_eq_zero_iff, map_sub]
    simp only at hc
    rw [hc, sub_self]
  · intro h z
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨c, hc⟩ := h (algebraMap _ X.functionField a)
      ((zero_le_curveVal_iff hdvr P _).2 ⟨a, rfl⟩)
    refine ⟨c, ?_⟩
    rw [hc' c, ← map_sub, one_le_curveVal_algebraMap_iff hdvr P,
      ← IsLocalRing.residue_eq_zero_iff, map_sub] at hc
    exact (sub_eq_zero.1 hc).symm

/-- A place whose residue map from `F` is onto has degree one. -/
theorem curveDeg_eq_one_of_surjective (P : CurvePlace X)
    (hs : Function.Surjective (fun c : F =>
      IsLocalRing.residue (X.presheaf.stalk P.1) ((fieldToStalk p P.1).hom c))) :
    curveDeg F p P = 1 := by
  let : Algebra F (X.presheaf.stalk P.1) :=
    ((X.presheaf.germ ⊤ P.1 (by simp)).hom.comp
      ((Scheme.ΓSpecIso (.of F)).inv ≫ p.appTop).hom).toAlgebra
  unfold curveDeg
  rw [Stacks.Chow.residueDegree_eq_finrank_residueField F p P.1]
  have hbij : Function.Bijective (algebraMap F (IsLocalRing.ResidueField
      (X.presheaf.stalk P.1))) :=
    ⟨(algebraMap F _).injective, hs⟩
  rw [← (LinearEquiv.ofBijective (Algebra.linearMap F _) hbij).finrank_eq, Module.finrank_self]

include hdvr in
/-- A rational place moves to a rational place. -/
theorem surjective_residue_of_curveVal_ringEquiv (τ : X.functionField ≃+* X.functionField)
    (hτ : ∀ c : F, τ ((fieldToStalk p (genericPoint X)).hom c) =
      (fieldToStalk p (genericPoint X)).hom c) {P₀ P₁ : CurvePlace X}
    (hP₁ : ∀ f, curveVal hdvr P₁ (τ f) = curveVal hdvr P₀ f)
    (hs : Function.Surjective (fun c : F =>
      IsLocalRing.residue (X.presheaf.stalk P₀.1) ((fieldToStalk p P₀.1).hom c))) :
    Function.Surjective (fun c : F =>
      IsLocalRing.residue (X.presheaf.stalk P₁.1) ((fieldToStalk p P₁.1).hom c)) := by
  rw [surjective_residue_iff p hdvr] at hs ⊢
  intro y hy
  obtain ⟨c, hc⟩ := hs (τ.symm y) (by rw [← hP₁, RingEquiv.apply_symm_apply]; exact hy)
  refine ⟨c, ?_⟩
  rw [← hP₁, map_sub, RingEquiv.apply_symm_apply, hτ] at hc
  exact hc

end Curve

end Stacks.BombieriStepanov

end
