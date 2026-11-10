module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwoStepTowerOpen
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CoordinateBlowupChartPresentation

/-!
# The first blow-up of the local model of Hironaka's example: its two charts

Let `k` be a field, `A = k[x, y, z]` (`MvPolynomial (Fin 3) k`, with `x = X 0`, `y = X 1`,
`z = X 2`), and on `Spec A` let `I = (x, y)` and `J = (x - y², z)`. This is the local model of
both halves of Hironaka's threefold (the source of [Stacks, Tag 08J1]): `V(I)` and `V(J)` are
two smooth curves meeting only at the origin.

This file describes the blow-up `Bl_I Spec A` (`AlgebraicGeometry.blowUp`) by its two standard
charts, each an affine `3`-space:

* `U₁ = Spec k[x, y₁, z]`, with `y = x·y₁` (the chart of the pivot `x`), and
* `U₂ = Spec k[x₁, y, z]`, with `x = x₁·y` (the chart of the pivot `y`),

the chart coordinates being again `X 0, X 1, X 2` of `MvPolynomial (Fin 3) k`.

## Main definitions

* `Stacks.Examples.HironakaLocalModel.centreIdeal`,
  `Stacks.Examples.HironakaLocalModel.curveIdeal`: the ideal sheaves of `I = (x, y)` and
  `J = (x - y², z)` on `Spec A`, as `Scheme.IdealSheafData.ofIdealTop` of the image of the ideal
  in `Γ(Spec A, ⊤)`.
* `Stacks.Examples.HironakaLocalModel.chartHom`: the two chart maps
  `x ↦ x, y ↦ x·y₁, z ↦ z` and `x ↦ x₁·y, y ↦ y, z ↦ z`.
* `Stacks.Examples.HironakaLocalModel.chartι`: the two chart open immersions
  `Spec A ⟶ Bl_I Spec A`.

## Main results

* `Stacks.Examples.HironakaLocalModel.chartι_comp_blowUpToBase`: the chart followed by the
  blow-up morphism is `Spec` of the chart map.
* `Stacks.Examples.HironakaLocalModel.opensRange_chartι_sup`: the two charts cover the blow-up.

## Implementation notes

The charts are the standard charts `AlgebraicGeometry.blowupChartι` of the blow-up attached to
the global sections `x` and `y` of `I`. Their coordinate rings are identified with polynomial
rings by the coordinate-blow-up computation of [Stacks, Tag 0H1H]
(`Stacks.MoreMorphisms.exists_coordinateChartEquiv_blowupChartHom`), for the ambient ring
`k[z] [x, y] = MvPolynomial (Fin 1 ⊕ Fin 2) k`, transported to `MvPolynomial (Fin 3) k` along
the renaming `Stacks.Examples.HironakaLocalModel.coordReindex` and to the ring of global sections
along `Scheme.ΓSpecIso`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

universe u

namespace Stacks.Examples.HironakaLocalModel

variable (k : Type u) [Field k]

/-- The coordinate ring `k[x, y, z]` of the local model. -/
abbrev Ring3 := MvPolynomial (Fin 3) k

/-- The ambient affine space `𝔸³_k = Spec k[x, y, z]` of the local model. -/
abbrev ambient : Scheme.{u} := Spec (.of (Ring3 k))

/-- The identification of `k[x, y, z]` with the global sections of `Spec k[x, y, z]`. -/
abbrev gammaEquiv : Ring3 k ≃+* Γ(ambient k, ⊤) :=
  (Scheme.ΓSpecIso (.of (Ring3 k))).symm.commRingCatIsoToRingEquiv

/-- The ideal sheaf on `Spec A` of an ideal of `A`. -/
abbrev idealSheafOf (K : Ideal (Ring3 k)) : (ambient k).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (K.map (Scheme.ΓSpecIso (.of (Ring3 k))).inv.hom)

/-- The ideal `I = (x, y)` of the first centre. -/
abbrev centreRingIdeal : Ideal (Ring3 k) := Ideal.span {X 0, X 1}

/-- The ideal `J = (x - y², z)` of the second curve. -/
abbrev curveRingIdeal : Ideal (Ring3 k) := Ideal.span {X 0 - X 1 ^ 2, X 2}

/-- The ideal sheaf of the first centre `I = (x, y)` on `Spec k[x, y, z]`. -/
abbrev centreIdeal : (ambient k).IdealSheafData := idealSheafOf k (centreRingIdeal k)

/-- The ideal sheaf of the second curve `J = (x - y², z)` on `Spec k[x, y, z]`. -/
abbrev curveIdeal : (ambient k).IdealSheafData := idealSheafOf k (curveRingIdeal k)

/-- On global sections, the ideal sheaf of `K` is the image of `K` in `Γ(Spec A, ⊤)`. -/
theorem idealSheafOf_ideal_top (K : Ideal (Ring3 k)) :
    (idealSheafOf k K).ideal ⟨⊤, isAffineOpen_top _⟩ =
      K.map (gammaEquiv k : Ring3 k →+* Γ(ambient k, ⊤)) :=
  Scheme.IdealSheafData.equivOfIsAffine.apply_symm_apply _

/-! ### The renaming `k[x, y, z] ≅ k[z][x, y]` -/

/-- The reindexing of the coordinates `x, y, z` of `k[x, y, z]` as the coordinates of
`MvPolynomial (Fin 1 ⊕ Fin 2) k`, the centre `(x, y)` being the last two. -/
def coordReindex : Fin 3 ≃ Fin 1 ⊕ Fin 2 where
  toFun := ![Sum.inr 0, Sum.inr 1, Sum.inl 0]
  invFun := Sum.elim (fun _ ↦ 2) Fin.castSucc
  left_inv j := by fin_cases j <;> rfl
  right_inv v := by rcases v with j | j <;> fin_cases j <;> rfl

/-- The renaming isomorphism `k[x, y, z] ≅ MvPolynomial (Fin 1 ⊕ Fin 2) k`. -/
abbrev coordRename : Ring3 k ≃ₐ[k] MvPolynomial (Fin 1 ⊕ Fin 2) k :=
  renameEquiv k (coordReindex)

/-- The renaming carries `(x, y)` to the ideal of the last two coordinates. -/
theorem map_coordRename_centreRingIdeal :
    (centreRingIdeal k).map (coordRename k : Ring3 k →+* MvPolynomial (Fin 1 ⊕ Fin 2) k) =
      Stacks.MoreMorphisms.coordinateRingIdeal k 1 2 := by
  rw [Ideal.map_span, Stacks.MoreMorphisms.coordinateRingIdeal]
  congr 1
  ext p
  simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_range, Fin.exists_fin_two]
  simp [coordReindex, eq_comm]

/-! ### The chart maps -/

/-- The two chart maps of the blow-up of `(x, y)`: the chart of the pivot `x`
(`x ↦ x, y ↦ x·y₁, z ↦ z`) and the chart of the pivot `y` (`x ↦ x₁·y, y ↦ y, z ↦ z`). -/
def chartHom : Fin 2 → (Ring3 k →ₐ[k] Ring3 k) :=
  ![aeval ![X 0, X 0 * X 1, X 2], aeval ![X 0 * X 1, X 1, X 2]]

/-- The chart maps are the coordinate chart maps `Stacks.Kaehler.blowupChartHom`, renamed. -/
theorem chartHom_eq (i : Fin 2) :
    chartHom k i = ((coordRename k).symm.toAlgHom.comp
      (Stacks.Kaehler.blowupChartHom k (Fin 1) (Fin 2) i)).comp (coordRename k).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [chartHom, coordReindex, Stacks.Kaehler.blowupChartHom, mul_comm]

/-! ### The chart rings -/

/-- The `i`-th chart pivot, `x` for `i = 0` and `y` for `i = 1`, as a global section of `I`. -/
abbrev pivot (i : Fin 2) : Γ(ambient k, ⊤) := gammaEquiv k (X i.castSucc)

/-- On global sections, the ideal `I` is generated by the pivots `x, y`. -/
private theorem centreIdeal_ideal_top_eq_span :
    (centreIdeal k).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span (Set.range (pivot k)) := by
  rw [idealSheafOf_ideal_top, Ideal.map_span]
  congr 1
  ext
  simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_two]
  exact or_congr eq_comm eq_comm

/-- The pivots lie in `I`. -/
theorem pivot_mem (i : Fin 2) :
    pivot k i ∈ (centreIdeal k).ideal ⟨⊤, isAffineOpen_top _⟩ :=
  centreIdeal_ideal_top_eq_span k ▸ Ideal.subset_span ⟨i, rfl⟩

/-- The pivot as an element of the ideal `I(⊤)`. -/
abbrev pivotSection (i : Fin 2) : (centreIdeal k).ideal ⟨⊤, isAffineOpen_top _⟩ :=
  ⟨pivot k i, pivot_mem k i⟩

/-- The coordinate ring of the `i`-th standard chart, as `AlgebraicGeometry.blowupChartι`
presents it: the affine blowup algebra `Γ(Spec A, ⊤)[I/pivot]`. -/
abbrev chartRing (i : Fin 2) :=
  affineBlowupAlgebra ((centreIdeal k).ideal ⟨⊤, isAffineOpen_top _⟩) (pivot k i)
    (Localization.Away (pivot k i))

/-- The identification of `Γ(Spec A, ⊤)` with `MvPolynomial (Fin 1 ⊕ Fin 2) k`. -/
abbrev gammaRename : Γ(ambient k, ⊤) ≃+* MvPolynomial (Fin 1 ⊕ Fin 2) k :=
  (gammaEquiv k).symm.trans (coordRename k).toRingEquiv

/-- The pivot `x` (resp. `y`) is the `0`-th (resp. `1`-st) coordinate of the centre. -/
theorem gammaRename_pivot (i : Fin 2) :
    gammaRename k (pivot k i) = X (Sum.inr i) := by
  simp only [gammaRename, RingEquiv.trans_apply, RingEquiv.symm_apply_apply,
    AlgEquiv.coe_toRingEquiv, renameEquiv_apply, rename_X]
  fin_cases i <;> rfl

/-- **The chart rings are polynomial rings.** The `i`-th chart ring is `k[x, y, z]`, in such a
way that the structure map from `Γ(Spec A, ⊤) ≅ A` is the chart map `chartHom k i`. -/
theorem exists_chartRingEquiv (i : Fin 2) :
    ∃ F : chartRing k i ≃+* Ring3 k, ∀ p : Ring3 k,
      F (algebraMap Γ(ambient k, ⊤) (chartRing k i) (gammaEquiv k p)) = chartHom k i p := by
  have hpow : (Submonoid.powers (pivot k i)).map (gammaRename k) =
      Submonoid.powers (X (Sum.inr i) : MvPolynomial (Fin 1 ⊕ Fin 2) k) := by
    rw [Submonoid.map_powers, gammaRename_pivot]
  let Λ : Localization.Away (pivot k i) ≃+*
      Localization.Away (X (Sum.inr i) : MvPolynomial (Fin 1 ⊕ Fin 2) k) :=
    IsLocalization.ringEquivOfRingEquiv _ _ (gammaRename k) hpow
  have hJ : Stacks.MoreMorphisms.coordinateRingIdeal k 1 2 =
      ((centreIdeal k).ideal ⟨⊤, isAffineOpen_top _⟩).map
        (gammaRename k : Γ(ambient k, ⊤) →+* MvPolynomial (Fin 1 ⊕ Fin 2) k) := by
    rw [idealSheafOf_ideal_top, Ideal.map_map, ← map_coordRename_centreRingIdeal]
    congr 1
    exact RingHom.ext fun p ↦ by simp [gammaRename]
  obtain ⟨E, hE⟩ := Stacks.Blowup.exists_ringEquiv_affineBlowupAlgebra' (gammaRename k) Λ
    (pivot k i) ((centreIdeal k).ideal ⟨⊤, isAffineOpen_top _⟩)
    (Stacks.MoreMorphisms.coordinateRingIdeal k 1 2) (X (Sum.inr i))
    (fun x ↦ IsLocalization.ringEquivOfRingEquiv_eq _ x) hJ (gammaRename_pivot k i).symm
  obtain ⟨e, he⟩ := Stacks.MoreMorphisms.exists_coordinateChartEquiv_blowupChartHom k 1 2 i
  refine ⟨E.trans (e.trans (coordRename k).symm.toRingEquiv), fun p ↦ ?_⟩
  have hEp : E (algebraMap Γ(ambient k, ⊤) (chartRing k i) (gammaEquiv k p)) =
      algebraMap (MvPolynomial (Fin 1 ⊕ Fin 2) k)
        (Stacks.MoreMorphisms.coordinateChartAlgebra k 1 2 i) (coordRename k p) := by
    refine Subtype.ext ?_
    rw [hE, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap]
    exact (IsLocalization.ringEquivOfRingEquiv_eq _ _).trans (by simp [gammaRename])
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply, hEp, he, chartHom_eq]
  rfl

/-- The chosen identification of the `i`-th chart ring with `k[x, y, z]`. -/
def chartRingEquiv (i : Fin 2) : chartRing k i ≃+* Ring3 k :=
  (exists_chartRingEquiv k i).choose

/-- `Stacks.Examples.HironakaLocalModel.chartRingEquiv` carries the structure map to the chart
map. -/
theorem chartRingEquiv_algebraMap (i : Fin 2) (p : Ring3 k) :
    chartRingEquiv k i (algebraMap Γ(ambient k, ⊤) (chartRing k i) (gammaEquiv k p)) =
      chartHom k i p :=
  (exists_chartRingEquiv k i).choose_spec p

/-! ### The chart open immersions -/

/-- The `i`-th chart `Spec k[x, y, z] ⟶ Bl_I Spec A` of the blow-up of `I = (x, y)`: for `i = 0`
the chart `U₁ = Spec k[x, y₁, z]` with `y = x·y₁`, for `i = 1` the chart `U₂ = Spec k[x₁, y, z]`
with `x = x₁·y`. It is the standard chart `AlgebraicGeometry.blowupChartι` of the pivot, read
through `Stacks.Examples.HironakaLocalModel.chartRingEquiv`. -/
def chartι (i : Fin 2) : ambient k ⟶ blowUp (centreIdeal k) :=
  Spec.map (chartRingEquiv k i).toCommRingCatIso.hom ≫
    blowupChartι (centreIdeal k) ⟨⊤, isAffineOpen_top _⟩ (pivotSection k i)

/-- The charts are open immersions. -/
instance (i : Fin 2) : IsOpenImmersion (chartι k i) := by
  rw [chartι]
  infer_instance

/-- **The charts over the base.** The `i`-th chart followed by the blow-up morphism is `Spec` of
the chart map `chartHom k i`. -/
theorem chartι_comp_blowUpToBase (i : Fin 2) :
    chartι k i ≫ blowUpToBase (centreIdeal k) =
      Spec.map (CommRingCat.ofHom (chartHom k i : Ring3 k →+* Ring3 k)) := by
  rw [chartι, Category.assoc, blowupChartι_comp_blowUpToBase, IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun p ↦ chartRingEquiv_algebraMap k i p)

/-- The pivots `x, y` generate `I` on global sections. -/
theorem centreIdeal_ideal_top_le_span :
    (centreIdeal k).ideal ⟨⊤, isAffineOpen_top _⟩ ≤ Ideal.span (Set.range (pivot k)) :=
  (centreIdeal_ideal_top_eq_span k).le

/-- **The two charts cover the blow-up.** -/
theorem exists_chartι_eq (x : blowUp (centreIdeal k)) : ∃ (i : Fin 2) (y : ambient k),
    chartι k i y = x := by
  obtain ⟨i, y, hy⟩ := exists_mem_range_blowupChartι (centreIdeal k) ⟨⊤, isAffineOpen_top _⟩
    (pivot k) (pivot_mem k) (centreIdeal_ideal_top_le_span k) x trivial
  let e := Scheme.Spec.mapIso (chartRingEquiv k i).toCommRingCatIso.op
  refine ⟨i, e.inv y, ?_⟩
  rw [← hy, chartι, Scheme.Hom.comp_apply]
  congr 1
  rw [← Scheme.Hom.comp_apply]
  change (e.inv ≫ e.hom) y = y
  rw [Iso.inv_hom_id]
  rfl

/-- The two charts cover the blow-up, as opens. -/
theorem opensRange_chartι_sup :
    (chartι k 0).opensRange ⊔ (chartι k 1).opensRange = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ ?_
  obtain ⟨i, y, rfl⟩ := exists_chartι_eq k x
  fin_cases i
  · exact Or.inl ⟨y, rfl⟩
  · exact Or.inr ⟨y, rfl⟩

/-- The two charts, as an open cover of the blow-up. -/
def chartCover : (blowUp (centreIdeal k)).OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (Fin 2) (fun _ ↦ ambient k) (chartι k)
    (exists_chartι_eq k) (fun i ↦ inferInstanceAs (IsOpenImmersion (chartι k i)))

end Stacks.Examples.HironakaLocalModel
