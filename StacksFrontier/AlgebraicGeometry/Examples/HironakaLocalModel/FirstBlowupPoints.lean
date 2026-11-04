module

public import StacksFrontier.AlgebraicGeometry.Examples.HironakaLocalModel.FirstBlowupStrictCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.IsoOffCentre

/-!
# Points of the first blow-up of the local model of Hironaka's example

Let `A = k[x, y, z]`, `I = (x, y)`, `J = (x - y², z)` on `Spec A`, `b : Bl_I Spec A ⟶ Spec A` the
blow-up and `J' = AlgebraicGeometry.TwoStepTower.strictCentre I J` the ideal of the strict
transform of `V(J)`. This file records the points of `Bl_I Spec A` that the analysis of
Hironaka's example uses.

## Main definitions

* `Stacks.Examples.HironakaLocalModel.kPoint`: the `k`-point of `Spec k[x, y, z]` with given
  coordinates, the prime `ker (eval v)`.
* `Stacks.Examples.HironakaLocalModel.originIdealSheaf`: the ideal sheaf `(x, y, z)` of the
  origin.

## Main results

* `Stacks.Examples.HironakaLocalModel.comap_chartι_zero_fibreIdeal`,
  `Stacks.Examples.HironakaLocalModel.comap_chartι_one_fibreIdeal`: the fibre `b⁻¹(O)` of the
  blow-up over the origin is cut out by `(x, z)` on `U₁` and by `(y, z)` on `U₂`.
* `Stacks.Examples.HironakaLocalModel.mem_support_strictCentre_and_eq_origin_iff`: the unique
  point `o'` of `V(J')` over the origin is the `k`-point `x₁ = y = z = 0` of `U₂`.
* `Stacks.Examples.HironakaLocalModel.existsUnique_mem_support_strictCentre_and_eq_d`: the point
  `d = (1, 1, 0)` of `V(J) ∖ V(I)` has exactly one preimage in `V(J')`, the `k`-point
  `x₁ = y = 1, z = 0` of `U₂`.
* `Stacks.Examples.HironakaLocalModel.eq_of_blowUpToBase_eq`: the blow-up is injective over the
  complement of `V(I)` ([Stacks, Tag 02OS], first assertion, read on points).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AlgebraicGeometry.TwoStepTower

universe u

namespace Stacks.Examples.HironakaLocalModel

variable (k : Type u) [Field k]

/-! ### `k`-points of affine `3`-space -/

/-- The `k`-point of `Spec k[x, y, z]` with coordinates `v`: the prime ideal `ker (eval v)`. -/
def kPoint (v : Fin 3 → k) : ambient k :=
  (⟨RingHom.ker (MvPolynomial.eval v), RingHom.ker_isPrime _⟩ : PrimeSpectrum (Ring3 k))

/-- A point of `Spec k[x, y, z]`, read as a prime ideal of `k[x, y, z]`. -/
abbrev primeOf (q : ambient k) : PrimeSpectrum (Ring3 k) := q

/-- The prime of the `k`-point `v` is `ker (eval v)`. -/
theorem kPoint_asIdeal (v : Fin 3 → k) :
    (primeOf k (kPoint k v)).asIdeal = RingHom.ker (MvPolynomial.eval v) := rfl

/-- `Spec` of a substitution sends a `k`-point to the `k`-point of the substituted values. -/
theorem specMap_aeval_kPoint (w : Fin 3 → Ring3 k) (v : Fin 3 → k) :
    Spec.map (CommRingCat.ofHom (aeval w : Ring3 k →ₐ[k] Ring3 k).toRingHom) (kPoint k v) =
      kPoint k (fun j ↦ MvPolynomial.eval v (w j)) := by
  have h : (MvPolynomial.eval v).comp (aeval w : Ring3 k →ₐ[k] Ring3 k).toRingHom =
      MvPolynomial.eval (fun j ↦ MvPolynomial.eval v (w j)) :=
    MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun j ↦ by simp)
  refine PrimeSpectrum.ext ?_
  change Ideal.comap (aeval w : Ring3 k →ₐ[k] Ring3 k).toRingHom
      (RingHom.ker (MvPolynomial.eval v)) =
    RingHom.ker (MvPolynomial.eval (fun j ↦ MvPolynomial.eval v (w j)))
  rw [RingHom.comap_ker, h]

/-- The ideal of a `k`-point is contained in any prime containing the `X j - v j`. -/
theorem ker_eval_le (v : Fin 3 → k) (K : Ideal (Ring3 k))
    (hK : ∀ j, X j - C (v j) ∈ K) : RingHom.ker (MvPolynomial.eval v) ≤ K := by
  intro f hf
  have h := sub_aeval_mem K (fun j ↦ C (v j)) hK f
  have hc : aeval (fun j ↦ C (v j)) f = (C (MvPolynomial.eval v f) : Ring3 k) := by
    have : ((aeval fun j ↦ C (v j) : Ring3 k →ₐ[k] Ring3 k) : Ring3 k →+* Ring3 k) =
        C.comp (MvPolynomial.eval v) :=
      MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun j ↦ by simp)
    exact congrArg (fun φ : Ring3 k →+* Ring3 k ↦ φ f) this
  rw [hc, RingHom.mem_ker.mp hf, map_zero, sub_zero] at h
  exact h

/-- A prime containing the `X j - v j` is the `k`-point `v`. -/
theorem eq_kPoint_of_mem (v : Fin 3 → k) (q : ambient k)
    (hq : ∀ j, X j - C (v j) ∈ (primeOf k q).asIdeal) : q = kPoint k v := by
  have hmax : (RingHom.ker (MvPolynomial.eval v)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun a ↦ ⟨C a, eval_C a⟩
  exact PrimeSpectrum.ext (hmax.eq_of_le (primeOf k q).isPrime.ne_top (ker_eval_le k v _ hq)).symm

/-- A point of `Spec k[x, y, z]` lies on the support of the ideal sheaf of `K` exactly when its
prime contains `K`. -/
theorem mem_support_idealSheafOf_iff (K : Ideal (Ring3 k)) (q : ambient k) :
    q ∈ (idealSheafOf k K).support ↔ K ≤ (primeOf k q).asIdeal := by
  change (q : ambient k) ∈ (((idealSheafOf k K).support : TopologicalSpace.Closeds (ambient k)) :
    Set (ambient k)) ↔ _
  rw [Scheme.IdealSheafData.coe_support_ofIdealTop, Spec_zeroLocus]
  change (_ : Set (Ring3 k)) ⊆ (primeOf k q).asIdeal ↔ _
  constructor
  · intro h f hf
    exact h (show gammaEquiv k f ∈ K.map (gammaEquiv k : Ring3 k →+* Γ(ambient k, ⊤)) from
      Ideal.mem_map_of_mem _ hf)
  · intro h f hf
    exact h ((gammaEquiv_mem_map_iff k K f).mp hf)

/-! ### Injectivity off the centre -/

/-- **The blow-up is injective over the complement of the centre.** Two points of the blow-up of
`W` in `I` with the same image off `V(I)` are equal ([Stacks, Tag 02OS], first assertion). -/
theorem eq_of_blowUpToBase_eq {W : Scheme.{u}} (I : W.IdealSheafData) {p p' : blowUp I}
    (h : blowUpToBase I p = blowUpToBase I p') (hp : blowUpToBase I p ∉ I.support) : p = p' := by
  have hpU : p ∈ blowUpToBase I ⁻¹ᵁ I.support.compl := hp
  have hpU' : p' ∈ blowUpToBase I ⁻¹ᵁ I.support.compl := show _ ∉ I.support from h ▸ hp
  have hinj : Function.Injective (blowUpToBase I ∣_ I.support.compl) := by
    intro a a' haa
    have h1 := congrArg (fun z ↦ (inv (blowUpToBase I ∣_ I.support.compl)) z) haa
    simp only at h1
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id] at h1
  have key : ∀ a : (blowUpToBase I ⁻¹ᵁ I.support.compl).toScheme,
      Scheme.Opens.ι (I.support.compl : W.Opens) ((blowUpToBase I ∣_ I.support.compl) a) =
        blowUpToBase I ((blowUpToBase I ⁻¹ᵁ I.support.compl).ι a) := fun a ↦ by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have := @hinj ⟨p, hpU⟩ ⟨p', hpU'⟩
    ((Scheme.Opens.ι (I.support.compl : W.Opens)).isOpenEmbedding.injective
      ((key ⟨p, hpU⟩).trans (h.trans (key ⟨p', hpU'⟩).symm)))
  exact congrArg Subtype.val this

/-! ### The fibre over the origin -/

/-- The ideal sheaf `(x, y, z)` of the origin of `Spec k[x, y, z]`. -/
abbrev originIdealSheaf : (ambient k).IdealSheafData :=
  idealSheafOf k (Ideal.span {X 0, X 1, X 2})

/-- The fibre of the blow-up over the origin, pulled back to a chart, is cut out by the image of
`(x, y, z)` under the chart map. -/
private theorem comap_chartι_fibreIdeal (i : Fin 2) :
    ((originIdealSheaf k).comap (blowUpToBase (centreIdeal k))).comap (chartι k i) =
      idealSheafOf k (Ideal.map (chartHom k i : Ring3 k →+* Ring3 k)
        (Ideal.span {X 0, X 1, X 2})) := by
  rw [← Scheme.IdealSheafData.comap_comp, chartι_comp_blowUpToBase, comap_specMap_idealSheafOf]

/-- On `U₁ = Spec k[x, y₁, z]` the fibre of the blow-up over the origin is cut out by `(x, z)`. -/
theorem comap_chartι_zero_fibreIdeal :
    ((originIdealSheaf k).comap (blowUpToBase (centreIdeal k))).comap (chartι k 0) =
      idealSheafOf k (Ideal.span {X 0, X 2}) := by
  rw [comap_chartι_fibreIdeal]
  congr 1
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  simp only [chartHom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    AlgHom.coe_toRingHom, aeval_X, Matrix.tail_cons, Matrix.head_cons]
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · rintro _ (rfl | rfl | rfl)
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
    · exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  · rintro _ (rfl | rfl)
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

/-- On `U₂ = Spec k[x₁, y, z]` the fibre of the blow-up over the origin is cut out by `(y, z)`. -/
theorem comap_chartι_one_fibreIdeal :
    ((originIdealSheaf k).comap (blowUpToBase (centreIdeal k))).comap (chartι k 1) =
      idealSheafOf k (Ideal.span {X 1, X 2}) := by
  rw [comap_chartι_fibreIdeal]
  congr 1
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  simp only [chartHom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    AlgHom.coe_toRingHom, aeval_X, Matrix.tail_cons, Matrix.head_cons]
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · rintro _ (rfl | rfl | rfl)
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  · rintro _ (rfl | rfl)
    · exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

/-! ### The points of the strict transform over the origin and over `d = (1, 1, 0)` -/

/-- The chart map of the pivot `x`. -/
theorem chartHom_zero_eq : chartHom k 0 = aeval ![X 0, X 0 * X 1, X 2] := rfl

/-- The chart map of the pivot `y`. -/
theorem chartHom_one_eq : chartHom k 1 = aeval ![X 0 * X 1, X 1, X 2] := rfl

/-- A point of a chart lies on `V(J')` exactly when its image under the chart does. -/
theorem chartι_mem_support_strictCentre_iff (i : Fin 2) (q : ambient k) :
    chartι k i q ∈ (strictCentre (centreIdeal k) (curveIdeal k)).support ↔
      q ∈ ((strictCentre (centreIdeal k) (curveIdeal k)).comap (chartι k i)).support := by
  rw [Scheme.IdealSheafData.support_comap]
  rfl

/-- The image in `Spec A` of a point of a chart. -/
theorem blowUpToBase_chartι (i : Fin 2) (q : ambient k) :
    blowUpToBase (centreIdeal k) (chartι k i q) =
      Spec.map (CommRingCat.ofHom (chartHom k i : Ring3 k →+* Ring3 k)) q := by
  rw [← Scheme.Hom.comp_apply, chartι_comp_blowUpToBase]

/-- A `k`-point of the chart `U₂` with `x₁ = y` and `z = 0` lies on `V(J')`. -/
private theorem chartι_one_kPoint_mem_support_strictCentre (v : Fin 3 → k) (h0 : v 0 = v 1)
    (h2 : v 2 = 0) :
    chartι k 1 (kPoint k v) ∈ (strictCentre (centreIdeal k) (curveIdeal k)).support := by
  rw [chartι_mem_support_strictCentre_iff, comap_chartι_one_strictCentre]
  refine (mem_support_idealSheafOf_iff k _ (kPoint k v)).mpr ?_
  rw [Ideal.span_le]
  rintro _ (rfl | rfl) <;> simp [kPoint_asIdeal, h0, h2]

/-- The image in `Spec A` of the `k`-point `v` of the chart `U₂` is the `k`-point `(v₀v₁, v₁, v₂)`
(for `w` equal to it). -/
private theorem blowUpToBase_chartι_one_kPoint (v w : Fin 3 → k)
    (hw : w = ![v 0 * v 1, v 1, v 2]) :
    blowUpToBase (centreIdeal k) (chartι k 1 (kPoint k v)) = kPoint k w := by
  rw [blowUpToBase_chartι, chartHom_one_eq]
  refine (specMap_aeval_kPoint k _ _).trans ?_
  congr 1
  funext j
  fin_cases j <;> simp [hw]

/-- **The point `o'` of `V(J')` over the origin.** A point of the blow-up lies on the strict
transform of `V(J)` and over the origin exactly when it is the `k`-point `x₁ = y = z = 0` of the
chart `U₂ = Spec k[x₁, y, z]`. -/
theorem mem_support_strictCentre_and_eq_origin_iff (p : blowUp (centreIdeal k)) :
    (p ∈ (strictCentre (centreIdeal k) (curveIdeal k)).support ∧
        blowUpToBase (centreIdeal k) p = kPoint k 0) ↔
      p = chartι k 1 (kPoint k 0) := by
  constructor
  · rintro ⟨hJ, hb⟩
    obtain ⟨i, q, rfl⟩ := exists_chartι_eq k p
    rw [chartι_mem_support_strictCentre_iff] at hJ
    rw [blowUpToBase_chartι] at hb
    have hb' := congrArg PrimeSpectrum.asIdeal hb
    change Ideal.comap (chartHom k i : Ring3 k →+* Ring3 k) (primeOf k q).asIdeal =
        RingHom.ker (MvPolynomial.eval (0 : Fin 3 → k)) at hb'
    have hmem : ∀ f : Ring3 k, MvPolynomial.eval 0 f = 0 →
        (chartHom k i : Ring3 k →+* Ring3 k) f ∈ (primeOf k q).asIdeal := by
      intro f hf
      have : f ∈ RingHom.ker (MvPolynomial.eval (0 : Fin 3 → k)) := hf
      rw [← hb'] at this
      exact this
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · exfalso
      rw [comap_chartι_zero_strictCentre, mem_support_idealSheafOf_iff] at hJ
      have h0 : (X 0 : Ring3 k) ∈ (primeOf k q).asIdeal := by
        simpa [chartHom_zero_eq] using hmem (X 0) (by simp)
      have h1 : (1 - X 0 * X 1 ^ 2 : Ring3 k) ∈ (primeOf k q).asIdeal :=
        hJ (Ideal.subset_span (Set.mem_insert _ _))
      have : (1 : Ring3 k) ∈ (primeOf k q).asIdeal := by
        rw [show (1 : Ring3 k) = (1 - X 0 * X 1 ^ 2) + X 1 ^ 2 * X 0 by ring]
        exact add_mem h1 (Ideal.mul_mem_left _ _ h0)
      exact (primeOf k q).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)
    · rw [comap_chartι_one_strictCentre, mem_support_idealSheafOf_iff] at hJ
      have h1 : (X 1 : Ring3 k) ∈ (primeOf k q).asIdeal := by
        simpa [chartHom_one_eq] using hmem (X 1) (by simp)
      have h01 : (X 0 - X 1 : Ring3 k) ∈ (primeOf k q).asIdeal :=
        hJ (Ideal.subset_span (Set.mem_insert _ _))
      have h2 : (X 2 : Ring3 k) ∈ (primeOf k q).asIdeal :=
        hJ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
      have hq : (q : ambient k) = kPoint k 0 := by
        refine eq_kPoint_of_mem k 0 q fun j ↦ ?_
        fin_cases j
        · simpa using add_mem h01 h1
        · simpa using h1
        · simpa using h2
      rw [hq]
  · rintro rfl
    refine ⟨?_, ?_⟩
    · exact chartι_one_kPoint_mem_support_strictCentre k 0 rfl rfl
    · exact blowUpToBase_chartι_one_kPoint k 0 0 (by ext j; fin_cases j <;> simp)

/-- The point `d = (1, 1, 0)` of `Spec k[x, y, z]`. -/
abbrev pointD : ambient k := kPoint k ![1, 1, 0]

/-- `d` lies on `V(J)`. -/
theorem pointD_mem_support_curveIdeal : pointD k ∈ (curveIdeal k).support := by
  refine (mem_support_idealSheafOf_iff k _ (kPoint k ![1, 1, 0])).mpr ?_
  rw [Ideal.span_le]
  rintro _ (rfl | rfl) <;> simp [kPoint_asIdeal]

/-- `d` does not lie on `V(I)`. -/
theorem pointD_not_mem_support_centreIdeal : pointD k ∉ (centreIdeal k).support := by
  intro h
  have := (mem_support_idealSheafOf_iff k _ (kPoint k ![1, 1, 0])).mp h
    (Ideal.subset_span (Set.mem_insert _ _))
  simp [kPoint_asIdeal] at this

/-- **The point of `V(J')` over `d`.** The point `d = (1, 1, 0)` of `V(J) ∖ V(I)` has exactly one
preimage in the strict transform `V(J')`, namely the `k`-point `x₁ = y = 1, z = 0` of
`U₂ = Spec k[x₁, y, z]`. -/
theorem existsUnique_mem_support_strictCentre_and_eq_d :
    ∃! p : blowUp (centreIdeal k),
      p ∈ (strictCentre (centreIdeal k) (curveIdeal k)).support ∧
        blowUpToBase (centreIdeal k) p = pointD k := by
  have hb : blowUpToBase (centreIdeal k) (chartι k 1 (kPoint k ![1, 1, 0])) = pointD k :=
    blowUpToBase_chartι_one_kPoint k _ _ (by ext j; fin_cases j <;> simp)
  refine ⟨chartι k 1 (kPoint k ![1, 1, 0]), ⟨?_, hb⟩, ?_⟩
  · exact chartι_one_kPoint_mem_support_strictCentre k _ rfl rfl
  · rintro p ⟨-, hp⟩
    refine eq_of_blowUpToBase_eq (centreIdeal k) (hp.trans hb.symm) ?_
    rw [hp]
    exact pointD_not_mem_support_centreIdeal k

end Stacks.Examples.HironakaLocalModel
