module

public import StacksFrontier.AlgebraicGeometry.Examples.HironakaLocalModel.FirstBlowupPoints
public import StacksFrontier.AlgebraicGeometry.CartierQuotientChart.AffineSubscheme

/-!
# The strict transform of the second curve in the first blow-up is an affine line

Let `A = k[x, y, z]`, `I = (x, y)`, `J = (x - y², z)` on `Spec A` and
`J' = AlgebraicGeometry.TwoStepTower.strictCentre I J` the ideal on `Bl_I Spec A` of the strict
transform of `V(J)`. This file shows that `V(J')` lies in the chart `U₂ = Spec k[x₁, y, z]`
(`x = x₁·y`), where it is `V(x₁ - y, z)`, and so `V(J') ≅ 𝔸¹_k = Spec k[t]` (parameter `y`).

## Main results

* `Stacks.Examples.HironakaLocalModel.support_strictCentre_subset_range_chartι_one`: every point
  of `V(J')` lies in the chart `U₂`.
* `Stacks.Examples.HironakaLocalModel.nonempty_strictCentre_subscheme_iso`: `V(J') ≅ Spec k[t]`.
* `Stacks.Examples.HironakaLocalModel.isIntegral_strictCentre_subscheme`: `V(J')` is integral, so
  in particular irreducible and connected.

## Implementation notes

A point of `V(J')` in the other chart `U₁ = Spec k[x, y₁, z]` satisfies `x·y₁² = 1`, so lies off
the exceptional divisor; the point of `U₂` with coordinates `(1/y₁, x·y₁, z)` has the same image
in `Spec A`, off `V(I)`, and the blow-up is injective there
(`Stacks.Examples.HironakaLocalModel.eq_of_blowUpToBase_eq`). Hence `V(J') ⟶ Bl_I Spec A`
factors through the open immersion `U₂ ⟶ Bl_I Spec A`, so its base change along it
(`Scheme.IdealSheafData.comapIso`) is an isomorphism, and on `U₂` the ideal is `(x₁ - y, z)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AlgebraicGeometry.TwoStepTower

universe u

namespace Stacks.Examples.HironakaLocalModel

variable (k : Type u) [Field k]

/-! ### `V(J')` lies in the chart `U₂` -/

/-- The chart transition `U₂ ⇢ U₁` on rings: `x₁ ↦ 1/y₁`, `y ↦ x·y₁`, `z ↦ z`, into
`k[x, y₁, z][1/y₁]`. -/
def chartTransition : Ring3 k →ₐ[k] Localization.Away (X 1 : Ring3 k) :=
  aeval ![IsLocalization.Away.invSelf (X 1 : Ring3 k),
    algebraMap (Ring3 k) _ (X 0 * X 1), algebraMap (Ring3 k) _ (X 2)]

/-- The chart transition is compatible with the two chart maps. -/
theorem chartTransition_comp_chartHom_one :
    (chartTransition k).comp (chartHom k 1) =
      (IsScalarTower.toAlgHom k (Ring3 k) (Localization.Away (X 1 : Ring3 k))).comp
        (chartHom k 0) := by
  have hinv := IsLocalization.Away.mul_invSelf (S := Localization.Away (X 1 : Ring3 k))
    (X 1 : Ring3 k)
  refine MvPolynomial.algHom_ext fun j ↦ ?_
  fin_cases j
  · simp only [chartHom_one_eq, chartHom_zero_eq, AlgHom.comp_apply, aeval_X, chartTransition,
      map_mul, IsScalarTower.coe_toAlgHom', Fin.zero_eta, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [mul_comm (algebraMap _ _ (X 0)), ← mul_assoc, mul_comm _ (algebraMap _ _ (X 1)), hinv,
      one_mul]
  all_goals simp [chartHom_one_eq, chartHom_zero_eq, chartTransition]

/-- A point of the chart `U₁` on `V(J')` is a point of the chart `U₂`. -/
theorem exists_chartι_one_eq_chartι_zero (q : ambient k)
    (hq : Ideal.span {1 - X 0 * X 1 ^ 2, (X 2 : Ring3 k)} ≤ (primeOf k q).asIdeal) :
    ∃ q' : ambient k, chartι k 1 q' = chartι k 0 q := by
  set P := (primeOf k q).asIdeal
  have h1 : (1 - X 0 * X 1 ^ 2 : Ring3 k) ∈ P := hq (Ideal.subset_span (Set.mem_insert _ _))
  have hunit : ∀ g : Ring3 k, g ∣ X 0 * X 1 ^ 2 → g ∉ P := by
    rintro g ⟨c, hc⟩ hg
    have : (1 : Ring3 k) ∈ P := by
      rw [show (1 : Ring3 k) = (1 - X 0 * X 1 ^ 2) + c * g by linear_combination hc]
      exact add_mem h1 (P.mul_mem_left _ hg)
    exact (primeOf k q).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  have hX1 : (X 1 : Ring3 k) ∉ P := hunit _ ⟨X 0 * X 1, by ring⟩
  have hX0 : (X 0 : Ring3 k) ∉ P := hunit _ ⟨X 1 ^ 2, by ring⟩
  let L := Localization.Away (X 1 : Ring3 k)
  have hdisj : Disjoint (Submonoid.powers (X 1 : Ring3 k) : Set (Ring3 k)) P := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hX1 ((primeOf k q).isPrime.mem_of_pow_mem n hn)
  have hQ : (P.map (algebraMap (Ring3 k) L)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (X 1 : Ring3 k)) L P
      (primeOf k q).isPrime hdisj
  have hQc : (P.map (algebraMap (Ring3 k) L)).comap (algebraMap (Ring3 k) L) = P :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers (X 1 : Ring3 k)) L
      (primeOf k q).isPrime hdisj
  let q' : ambient k :=
    (⟨(P.map (algebraMap (Ring3 k) L)).comap (chartTransition k : Ring3 k →+* L),
      Ideal.comap_isPrime _ _⟩ : PrimeSpectrum (Ring3 k))
  have himage : Spec.map (CommRingCat.ofHom (chartHom k 1 : Ring3 k →+* Ring3 k)) q' =
      Spec.map (CommRingCat.ofHom (chartHom k 0 : Ring3 k →+* Ring3 k)) q := by
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (chartHom k 1 : Ring3 k →+* Ring3 k)
        (Ideal.comap (chartTransition k : Ring3 k →+* L) (P.map (algebraMap (Ring3 k) L))) =
      Ideal.comap (chartHom k 0 : Ring3 k →+* Ring3 k) P
    conv_rhs => rw [← hQc]
    rw [Ideal.comap_comap, Ideal.comap_comap]
    congr 1
    exact congrArg AlgHom.toRingHom (chartTransition_comp_chartHom_one k)
  refine ⟨q', eq_of_blowUpToBase_eq (centreIdeal k) ?_ ?_⟩
  · rw [blowUpToBase_chartι, blowUpToBase_chartι, himage]
  · rw [blowUpToBase_chartι, himage, mem_support_idealSheafOf_iff]
    intro hle
    apply hX0
    have : (X 0 : Ring3 k) ∈ Ideal.comap (chartHom k 0 : Ring3 k →+* Ring3 k) P :=
      hle (Ideal.subset_span (Set.mem_insert _ _))
    simpa [chartHom_zero_eq] using this

/-- **`V(J')` lies in the chart `U₂ = Spec k[x₁, y, z]`.** -/
theorem support_strictCentre_subset_range_chartι_one :
    ((strictCentre (centreIdeal k) (curveIdeal k)).support : Set (blowUp (centreIdeal k))) ⊆
      Set.range (chartι k 1) := by
  intro p hp
  obtain ⟨i, q, rfl⟩ := exists_chartι_eq k p
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · have hq := (chartι_mem_support_strictCentre_iff k 0 q).mp hp
    rw [comap_chartι_zero_strictCentre, mem_support_idealSheafOf_iff] at hq
    exact exists_chartι_one_eq_chartι_zero k q hq
  · exact ⟨q, rfl⟩

/-! ### `V(J') ≅ 𝔸¹` -/

/-- The parametrization `x₁ ↦ t, y ↦ t, z ↦ 0` of `V(x₁ - y, z)`. -/
def lineParam : Ring3 k →ₐ[k] Polynomial k := aeval ![Polynomial.X, Polynomial.X, 0]

/-- The parametrization is surjective. -/
theorem lineParam_surjective : Function.Surjective (lineParam k) := by
  have h : (lineParam k).comp (Polynomial.aeval (X 0 : Ring3 k)) = AlgHom.id k (Polynomial k) :=
    Polynomial.algHom_ext (by simp [lineParam])
  exact fun f ↦ ⟨Polynomial.aeval (X 0 : Ring3 k) f, DFunLike.congr_fun h f⟩

/-- The kernel of the parametrization is `(x₁ - y, z)`. -/
theorem ker_lineParam :
    RingHom.ker (lineParam k) = Ideal.span {X 0 - X 1, (X 2 : Ring3 k)} := by
  set P : Ideal (Ring3 k) := Ideal.span {X 0 - X 1, X 2}
  refine le_antisymm (fun f hf ↦ ?_) ?_
  · have hσ : (Polynomial.aeval (X 1 : Ring3 k)).comp (lineParam k) =
        aeval ![X 1, X 1, (0 : Ring3 k)] := by
      refine MvPolynomial.algHom_ext fun j ↦ ?_
      fin_cases j <;> simp [lineParam]
    have hsub : f - aeval ![X 1, X 1, (0 : Ring3 k)] f ∈ P := sub_aeval_mem P ![X 1, X 1, 0]
      (fun j ↦ by
        fin_cases j
        · change X 0 - X 1 ∈ P
          exact Ideal.subset_span (Set.mem_insert _ _)
        · change X 1 - X 1 ∈ P
          simp
        · change X 2 - 0 ∈ P
          rw [sub_zero]
          exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)) f
    have h0 : aeval ![X 1, X 1, (0 : Ring3 k)] f = 0 := by
      rw [← hσ, AlgHom.comp_apply, show lineParam k f = 0 from hf, map_zero]
    rwa [h0, sub_zero] at hsub
  · rw [Ideal.span_le]
    rintro _ (rfl | rfl) <;> simp [lineParam]

/-- `k[x₁, y, z]/(x₁ - y, z) ≅ k[t]`. -/
def lineQuotientEquiv : Ring3 k ⧸ Ideal.span {X 0 - X 1, (X 2 : Ring3 k)} ≃+* Polynomial k :=
  (Ideal.quotientEquivAlgOfEq k (ker_lineParam k).symm).toRingEquiv.trans
    (Ideal.quotientKerAlgEquivOfSurjective (lineParam_surjective k)).toRingEquiv

/-- **`V(J') ≅ 𝔸¹_k`.** The strict transform of `V(x - y², z)` in the blow-up of `(x, y)` is
isomorphic to the affine line `Spec k[t]`. -/
theorem nonempty_strictCentre_subscheme_iso :
    Nonempty ((strictCentre (centreIdeal k) (curveIdeal k)).subscheme ≅
      Spec (.of (Polynomial k))) := by
  set K := strictCentre (centreIdeal k) (curveIdeal k)
  have hsurj : Function.Surjective (pullback.snd (chartι k 1) K.subschemeι) := by
    intro x
    have hx : K.subschemeι x ∈ (K.support : Set (blowUp (centreIdeal k))) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := support_strictCentre_subset_range_chartι_one k hx
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback y x hy
    exact ⟨z, hz⟩
  have : Surjective (pullback.snd (chartι k 1) K.subschemeι) := ⟨hsurj⟩
  have : IsIso (pullback.snd (chartι k 1) K.subschemeι) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  have hK : (K.comap (chartι k 1)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (Ideal.span {X 0 - X 1, (X 2 : Ring3 k)}).map
        (gammaEquiv k : Ring3 k →+* Γ(ambient k, ⊤)) := by
    rw [comap_chartι_one_strictCentre, idealSheafOf_ideal_top]
  obtain ⟨e, -⟩ := Stacks.CartierQuotientChart.exists_subschemeIsoSpec_of_ideal_eq _ hK
  let r : Polynomial k ≃+* Γ(ambient k, ⊤) ⧸ (Ideal.span {X 0 - X 1, (X 2 : Ring3 k)}).map
      (gammaEquiv k : Ring3 k →+* Γ(ambient k, ⊤)) :=
    (lineQuotientEquiv k).symm.trans (Ideal.quotientEquiv _ _ (gammaEquiv k) rfl)
  exact ⟨(asIso (pullback.snd (chartι k 1) K.subschemeι)).symm ≪≫ (K.comapIso (chartι k 1)).symm ≪≫
    e ≪≫ Scheme.Spec.mapIso r.toCommRingCatIso.op⟩

/-- **`V(J')` is integral**: it is isomorphic to the affine line. In particular it is irreducible
and connected. -/
theorem isIntegral_strictCentre_subscheme :
    IsIntegral (strictCentre (centreIdeal k) (curveIdeal k)).subscheme := by
  obtain ⟨e⟩ := nonempty_strictCentre_subscheme_iso k
  have : Nonempty (strictCentre (centreIdeal k) (curveIdeal k)).subscheme :=
    ⟨e.inv (Classical.arbitrary _)⟩
  exact isIntegral_of_isOpenImmersion e.hom

/-- `V(J')` is irreducible. -/
theorem irreducibleSpace_strictCentre_subscheme :
    IrreducibleSpace (strictCentre (centreIdeal k) (curveIdeal k)).subscheme := by
  have := isIntegral_strictCentre_subscheme k
  infer_instance

/-- `V(J')` is connected. -/
theorem connectedSpace_strictCentre_subscheme :
    ConnectedSpace (strictCentre (centreIdeal k) (curveIdeal k)).subscheme := by
  have := irreducibleSpace_strictCentre_subscheme k
  infer_instance

end Stacks.Examples.HironakaLocalModel
