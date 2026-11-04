module

public import StacksFrontier.AlgebraicGeometry.Examples.HironakaLocalModel.SecondBlowupFamily

/-!
# The fibre of the second blow-up of Hironaka's local model over the origin

Hironaka's example (the source of [Stacks, Tag 08J1]) is, near its special point `O`, the two-step
blow-up of `Spec k[x, y, z]`. On the chart `U₂ = Spec k[v, y, z]` of the first blow-up
(`x = (v + y)·y`) the second blow-up is `Bl_{(v,z)} Spec k[v, y, z]`, with the charts
`Spec k[v, y, z₂]` (`z = v·z₂`) and `Spec k[v₂, y, z]` (`v = z·v₂`). This file computes, on these
two charts, the fibre over `O` (statement (M2) of the local model):

* on the first chart it is the closed subscheme `(y, v·z₂) = (y, v) ⊓ (y, z₂)`, the
  scheme-theoretic union of `{y = v = 0}` and `{y = z₂ = 0}`, which meet in the reduced `k`-point
  `v = y = z₂ = 0`;
* on the second chart it is `(y, z)`;
* the piece `{y = v = 0}` of the first chart and the whole fibre `{y = z = 0}` of the second are,
  on each chart, the fibre of `Bl_{(v,z)} Spec k[v, y, z] ⟶ Spec k[v, y, z]` over the point
  `v = y = z = 0`.

## Main results

* `Stacks.Examples.HironakaLocalModel.ker_originMap`: the origin of `Spec k[x, y, z]` is the
  closed point `(x, y, z)`.
* `Stacks.Examples.HironakaLocalModel.isPullback_secondChartOne_origin`,
  `Stacks.Examples.HironakaLocalModel.isPullback_secondChartTwo_origin`: the fibres over the origin
  on the two charts, as cartesian squares.
* `Stacks.Examples.HironakaLocalModel.fibreIdeal_chartOne_eq_inf`,
  `Stacks.Examples.HironakaLocalModel.sup_fibreComponents_chartOne`: the decomposition of the fibre
  on the first chart and the intersection point of its two pieces.
* `Stacks.Examples.HironakaLocalModel.map_originIdeal_chartOneMap`,
  `Stacks.Examples.HironakaLocalModel.map_originIdeal_chartTwoMap`: the fibre of the second blow-up
  over the point `v = y = z = 0` of its centre.

The identification of `{y = v = 0} ∪ {y = z = 0}` (glued along `v₂ = 1/z₂`) with `ℙ¹_k` is not
made here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

universe u

namespace Stacks.Examples.HironakaLocalModel

variable (k : Type u) [Field k]

/-- The origin `x = y = z = 0` of `Spec k[x, y, z]`, as the evaluation `k[x, y, z] ⟶ k`. -/
def originMap : MvPolynomial (Fin 3) k →ₐ[k] k :=
  aeval 0

/-- The evaluation at the origin `k[x, y, z] ⟶ k` is surjective. -/
theorem originMap_surjective : Function.Surjective (originMap k) :=
  fun c => ⟨C c, by simp [originMap]⟩

/-- Each coordinate `X i` lies in the ideal of the origin. -/
private theorem X_mem_originIdeal (i : Fin 3) : (X i : MvPolynomial (Fin 3) k) ∈ originIdeal k := by
  fin_cases i <;> exact Ideal.subset_span (by simp)

/-- **The origin is the closed point `(x, y, z)`.** -/
theorem ker_originMap :
    RingHom.ker (originMap k : MvPolynomial (Fin 3) k →+* k) = originIdeal k := by
  refine ker_eq_of_sub_mem _ (C : k →+* MvPolynomial (Fin 3) k) _ ?_ ?_
  · rw [Ideal.span_le]
    rintro _ (rfl | rfl | rfl) <;> simp [originMap]
  · refine sub_mem_of_forall ((C : k →+* MvPolynomial (Fin 3) k).comp
      (originMap k : MvPolynomial (Fin 3) k →+* k)) _ ?_ ?_
    · intro c
      simp [originMap]
    · intro i
      simpa [originMap] using X_mem_originIdeal k i

/-- The fibre over the origin on a chart `φ` with fibre ideal `J`: the square of rings is a
pushout. -/
private theorem isPushout_fibre (φ : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 3) k)
    (J : Ideal (MvPolynomial (Fin 3) k))
    (hJ : (originIdeal k).map (φ : MvPolynomial (Fin 3) k →+* MvPolynomial (Fin 3) k) = J) :
    IsPushout (CommRingCat.ofHom (φ : MvPolynomial (Fin 3) k →+* MvPolynomial (Fin 3) k))
      (CommRingCat.ofHom (originMap k : MvPolynomial (Fin 3) k →+* k))
      (CommRingCat.ofHom (Ideal.Quotient.mk J))
      (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin 3) k ⧸ J))) := by
  refine isPushout_of_surjective _ _ _ _ ?_ (originMap_surjective k)
    Ideal.Quotient.mk_surjective ?_
  · refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_coe, RingHom.coe_coe,
        MvPolynomial.algHom_C, MvPolynomial.algHom_C, Ideal.Quotient.mk_algebraMap]
      rfl
    · have hφ : φ (X i) ∈ J := hJ ▸ Ideal.mem_map_of_mem _ (X_mem_originIdeal k i)
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hφ]
      simp [originMap]
  · rw [Ideal.mk_ker, ker_originMap, hJ]

/-- **The fibre over the origin on the first chart** `Spec k[v, y, z₂]` is
`Spec k[v, y, z₂]/(y, v·z₂)`. -/
theorem isPullback_secondChartOne_origin :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span {X 1, X 0 * X 2} : Ideal (MvPolynomial (Fin 3) k)))))
      (Spec.map (CommRingCat.ofHom (algebraMap k
        (MvPolynomial (Fin 3) k ⧸ (Ideal.span {X 1, X 0 * X 2} :
          Ideal (MvPolynomial (Fin 3) k))))))
      (secondChartOne k ≫ secondBlowupToBase k)
      (Spec.map (CommRingCat.ofHom (originMap k : MvPolynomial (Fin 3) k →+* k))) := by
  rw [secondChartOne_secondBlowupToBase]
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (isPushout_fibre k _ _ (fibreIdeal_chartOne k))

/-- **The fibre over the origin on the second chart** `Spec k[v₂, y, z]` is
`Spec k[v₂, y, z]/(y, z)`. -/
theorem isPullback_secondChartTwo_origin :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span {X 1, X 2} : Ideal (MvPolynomial (Fin 3) k)))))
      (Spec.map (CommRingCat.ofHom (algebraMap k
        (MvPolynomial (Fin 3) k ⧸ (Ideal.span {X 1, X 2} : Ideal (MvPolynomial (Fin 3) k))))))
      (secondChartTwo k ≫ secondBlowupToBase k)
      (Spec.map (CommRingCat.ofHom (originMap k : MvPolynomial (Fin 3) k →+* k))) := by
  rw [secondChartTwo_secondBlowupToBase]
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (isPushout_fibre k _ _ (fibreIdeal_chartTwo k))

/-- **The fibre over the origin on the first chart is the union of two lines**:
`(y, v·z₂) = (y, v) ⊓ (y, z₂)`. -/
theorem fibreIdeal_chartOne_eq_inf :
    (originIdeal k).map (((chartOneMap k).comp (towerMap k) : _ →ₐ[k] _) :
        MvPolynomial (Fin 3) k →+* MvPolynomial (Fin 3) k) =
      Ideal.span {X 1, X 0} ⊓ Ideal.span {X 1, X 2} := by
  rw [fibreIdeal_chartOne, span_X_one_mul_eq_inf]

/-- **The two lines of the fibre on the first chart meet in the reduced `k`-point
`v = y = z₂ = 0`**: `(y, v) ⊔ (y, z₂) = (v, y, z₂)`, the kernel of the evaluation at the origin. -/
theorem sup_fibreComponents_chartOne :
    (Ideal.span {X 1, X 0} ⊔ Ideal.span {X 1, X 2} : Ideal (MvPolynomial (Fin 3) k)) =
      RingHom.ker (originMap k : MvPolynomial (Fin 3) k →+* k) := by
  rw [ker_originMap, ← Ideal.span_union]
  congr 1
  ext p
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- A ring map sending each coordinate into `(X a, X b)` and fixing `X a` and `X b` extends the
ideal of the origin to `(X a, X b)`. -/
private theorem map_originIdeal_eq_span_pair (φ : MvPolynomial (Fin 3) k →+* MvPolynomial (Fin 3) k)
    (a b : Fin 3)
    (h₀ : φ (X 0) ∈ (Ideal.span {X a, X b} : Ideal (MvPolynomial (Fin 3) k)))
    (h₁ : φ (X 1) ∈ (Ideal.span {X a, X b} : Ideal (MvPolynomial (Fin 3) k)))
    (h₂ : φ (X 2) ∈ (Ideal.span {X a, X b} : Ideal (MvPolynomial (Fin 3) k)))
    (ha : φ (X a) = X a) (hb : φ (X b) = X b) :
    (originIdeal k).map φ = Ideal.span {X a, X b} := by
  refine le_antisymm ((Ideal.map_le_iff_le_comap).2 ?_) ?_
  · rw [Ideal.span_le]
    rintro _ (rfl | rfl | rfl)
    exacts [h₀, h₁, h₂]
  · rw [Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact ha ▸ Ideal.mem_map_of_mem φ (X_mem_originIdeal k a)
    · exact hb ▸ Ideal.mem_map_of_mem φ (X_mem_originIdeal k b)

/-- **The fibre of `Bl_{(v,z)} Spec k[v, y, z]` over the point `v = y = z = 0`, on the first
chart**, is `{y = v = 0}`: the extension of `(v, y, z)` along `z ↦ v·z₂` is `(y, v)`. -/
theorem map_originIdeal_chartOneMap :
    (originIdeal k).map (chartOneMap k : MvPolynomial (Fin 3) k →+* MvPolynomial (Fin 3) k) =
      Ideal.span {X 1, X 0} := by
  refine map_originIdeal_eq_span_pair k _ 1 0 ?_ ?_ ?_ (by simp [blowupChartMap])
    (by simp [blowupChartMap])
  · exact Ideal.subset_span (by simp [blowupChartMap])
  · exact Ideal.subset_span (by simp [blowupChartMap])
  · simp only [RingHom.coe_coe, blowupChartMap_X_self]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Or.inr rfl))

/-- **The fibre of `Bl_{(v,z)} Spec k[v, y, z]` over the point `v = y = z = 0`, on the second
chart**, is `{y = z = 0}`: the extension of `(v, y, z)` along `v ↦ z·v₂` is `(y, z)`, which is also
the whole fibre of the tower over the origin on that chart
(`Stacks.Examples.HironakaLocalModel.fibreIdeal_chartTwo`). -/
theorem map_originIdeal_chartTwoMap :
    (originIdeal k).map (chartTwoMap k : MvPolynomial (Fin 3) k →+* MvPolynomial (Fin 3) k) =
      Ideal.span {X 1, X 2} := by
  refine map_originIdeal_eq_span_pair k _ 1 2 ?_ ?_ ?_ (by simp [blowupChartMap])
    (by simp [blowupChartMap])
  · simp only [RingHom.coe_coe, blowupChartMap_X_self]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Or.inr rfl))
  · exact Ideal.subset_span (by simp [blowupChartMap])
  · exact Ideal.subset_span (by simp [blowupChartMap])

end Stacks.Examples.HironakaLocalModel

end
