module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionDecomposition

/-!
# Associativity of composition of correspondences of mixed dimension

Let `k` be a field and let `X`, `Y`, `Z`, `W` be schemes smooth over `k`, with `Y` and `Z`
proper. Section 0FFZ of the Stacks Project defines

`Corrʳ(X, Y) = ⊕_d ⊕_e CH_{e-r}(X_d × Y_e) ⊗ ℚ`

over the equidimensional parts `X = ∐_d X_d`, `Y = ∐_e Y_e`, and the composition
`Corrʳ(X, Y) × Corrˢ(Y, Z) ⟶ Corr^{r+s}(X, Z)`, given on the pieces by
`(c' ∘ c)_{d,f} = Σ_e c'_{e,f} ∘ c_{d,e}`. Stacks 0FG0 (1) asserts that this composition is
`ℚ`-bilinear and associative. Bilinearity holds by construction. This file proves associativity,
`c'' ∘ (c' ∘ c) = (c'' ∘ c') ∘ c`, for arbitrary (not necessarily equidimensional) `X`, `Y`, `Z`,
`W`, from associativity of composition of correspondences between schemes of constant dimension,
applied to the pieces `X_d`, `Y_e`, `Z_f`, `W_g`.

## Main definitions

* `Stacks.WeilCohomology.corrCongr`: the identification `Corrʳ(X, Y) ≃ Corr^{r'}(X, Y)` for
  `r = r'`, blockwise `Stacks.WeilCohomology.correspondenceCongr`.

## Main results

* `Stacks.WeilCohomology.Corr.induction_on`: a property of correspondences that holds for `0`, is
  stable under addition and holds on every pure block `Corrʳ(X_d, Y_e)` holds everywhere.
* `Stacks.WeilCohomology.comp_lof_lof_lof_lof`, `Stacks.WeilCohomology.comp_lof_lof_lof_of_ne`:
  composition of two pure blocks, `c'_{e',f} ∘ c_{d,e}`, is the equidimensional composition
  placed in the block `(d, f)` when `e = e'`, and vanishes when `e ≠ e'`.
* `Stacks.WeilCohomology.comp_assoc_lof`: associativity on pure blocks.
* `Stacks.WeilCohomology.comp_assoc`: associativity of composition (the second half of
  Stacks 0FG0 (1)), for any family of diagonal classes whose equidimensional composition is
  associative.
* `Stacks.WeilCohomology.comp_bilinear_assoc`: Stacks 0FG0 (1) in full, bilinearity and
  associativity together.

## Implementation notes

As in `Stacks.WeilCohomology.DiagonalClassFamily.CompositionAssoc`, the two sides of
associativity live in degrees `(r + s) + t` and `r + (s + t)`, and are compared through
`Stacks.WeilCohomology.corrCongr`. The intersection products are formed with an arbitrary
family of diagonal classes `Δ`, and associativity in the equidimensional case is the
hypothesis `Δ.CompositionAssoc`; the reduction to that case is what is proved here.

## References

* [Stacks Project, Section 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
* [Stacks Project, Tag 0FG0](https://stacks.math.columbia.edu/tag/0FG0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  (sZ : Z ⟶ (fieldChowSituation k).S) (sW : W ⟶ (fieldChowSituation k).S)
  [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY] [Smooth sZ] [IsSeparated sZ]
  [Smooth sW] [IsSeparated sW]

omit [IsSeparated sX] [IsSeparated sY] in
/-- Induction on correspondences of mixed dimension: a property of `Corrʳ(X, Y)` that holds for
`0`, is stable under addition and holds on every pure block `Corrʳ(X_d, Y_e)` holds everywhere. -/
@[elab_as_elim]
theorem Corr.induction_on {r : ℤ} {motive : Corr k sX sY r → Prop} (c : Corr k sX sY r)
    (zero : motive 0) (add : ∀ a b, motive a → motive b → motive (a + b))
    (lof : ∀ (d e : ℕ)
      (x : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r),
      motive (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))) :
    motive c := by
  induction c using DirectSum.induction_on with
  | zero => exact zero
  | add a b ha hb => exact add a b ha hb
  | of d x =>
    induction x using DirectSum.induction_on with
    | zero => simpa only [map_zero] using zero
    | add a b ha hb => simpa only [map_add] using add _ _ ha hb
    | of e x => exact lof d e x

/-- Transport of correspondences of mixed dimension along an equality of degrees,
`Corrʳ(X, Y) ≃ Corr^{r'}(X, Y)` for `r = r'`, blockwise `correspondenceCongr`. -/
def corrCongr {r r' : ℤ} (h : r = r') : Corr k sX sY r ≃ₗ[ℚ] Corr k sX sY r' :=
  DirectSum.congrLinearEquiv fun d ↦ DirectSum.congrLinearEquiv fun e ↦
    correspondenceCongr k (partBase sX d) (partBase sY e) h

omit [IsSeparated sX] [IsSeparated sY] in
/-- On a pure block `Corrʳ(X_d, Y_e)`, `corrCongr` acts as `correspondenceCongr`. -/
@[simp]
theorem corrCongr_lof_lof {r r' : ℤ} (h : r = r') (d e : ℕ)
    (c : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r) :
    corrCongr k sX sY h
        (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e c)) =
      DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e
        (correspondenceCongr k (partBase sX d) (partBase sY e) h c)) := by
  simp [corrCongr, DirectSum.coe_congrLinearEquiv]

variable (Δ : DiagonalClassFamily k)

omit [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ] in
/-- Composition of two pure blocks with the same middle index: `c' ∘ c` for
`c ∈ Corrʳ(X_d, Y_e)` and `c' ∈ Corrˢ(Y_e, Z_f)` is the equidimensional composition, in the
block `(d, f)`. -/
@[simp]
theorem comp_lof_lof_lof_lof [IsProper sY] (r s : ℤ) (d e f : ℕ)
    (c : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r)
    (c' : Correspondence (fieldChowSituation k) (partBase sY e) (partBase sZ f) f s) :
    comp k sX sY sZ Δ r s (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e c))
        (DirectSum.lof ℚ ℕ _ e (DirectSum.lof ℚ ℕ _ f c')) =
      DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ f
        (composition k (partBase sX d) (partBase sY e) (partBase sZ f) Δ
          (relativeDimension_partBase sX d) (relativeDimension_partBase sY e)
          (relativeDimension_partBase sZ f) r s c c')) := by
  simp [comp, compBlock]

omit [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ] in
/-- Composition of two pure blocks with different middle indices vanishes: `c' ∘ c = 0` for
`c ∈ Corrʳ(X_d, Y_e)` and `c'` supported on `Y_{e'} × Z`, `e ≠ e'`. -/
theorem comp_lof_lof_lof_of_ne [IsProper sY] (r s : ℤ) (d e e' : ℕ) (h : e ≠ e')
    (c : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r)
    (c' : DirectSum ℕ fun f ↦
      Correspondence (fieldChowSituation k) (partBase sY e') (partBase sZ f) f s) :
    comp k sX sY sZ Δ r s (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e c))
        (DirectSum.lof ℚ ℕ (fun e : ℕ ↦ DirectSum ℕ fun f ↦
          Correspondence (fieldChowSituation k) (partBase sY e) (partBase sZ f) f s) e' c') =
      0 := by
  have : DirectSum.component ℚ ℕ (fun e : ℕ ↦ DirectSum ℕ fun f ↦
      Correspondence (fieldChowSituation k) (partBase sY e) (partBase sZ f) f s) e
        (DirectSum.lof ℚ ℕ _ e' c') = 0 := by
    rw [DirectSum.component.of, dite_eq_right (Ne.symm h)]
  simp [comp, compBlock, this]

omit [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ] [IsSeparated sW] in
private theorem comp_assoc_lof_of_ne_left [IsProper sY] [IsProper sZ] (r s t : ℤ)
    (d e : ℕ) (x : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r)
    (e' f : ℕ) (y : Correspondence (fieldChowSituation k) (partBase sY e') (partBase sZ f) f s)
    (f' g : ℕ) (z : Correspondence (fieldChowSituation k) (partBase sZ f') (partBase sW g) g t)
    (he : e ≠ e') :
    corrCongr k sX sW (add_assoc r s t)
        (comp k sX sZ sW Δ (r + s) t
          (comp k sX sY sZ Δ r s
            (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
            (DirectSum.lof ℚ ℕ _ e' (DirectSum.lof ℚ ℕ _ f y)))
          (DirectSum.lof ℚ ℕ _ f' (DirectSum.lof ℚ ℕ _ g z))) =
      comp k sX sY sW Δ r (s + t) (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
        (comp k sY sZ sW Δ s t
          (DirectSum.lof ℚ ℕ _ e' (DirectSum.lof ℚ ℕ _ f y))
          (DirectSum.lof ℚ ℕ _ f' (DirectSum.lof ℚ ℕ _ g z))) := by
  simp only [comp_lof_lof_lof_of_ne k sX sY sZ Δ r s d e e' he, LinearEquiv.map_zero,
    LinearMap.map_zero, LinearMap.zero_apply]
  by_cases hf : f = f'
  · subst hf
    simp only [comp_lof_lof_lof_lof, comp_lof_lof_lof_of_ne k sX sY sW Δ r (s + t) d e e' he]
  · simp only [comp_lof_lof_lof_of_ne k sY sZ sW Δ s t e' f f' hf,
      LinearMap.map_zero]

omit [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ] [IsSeparated sW] in
private theorem comp_assoc_lof_of_ne_right [IsProper sY] [IsProper sZ] (r s t : ℤ)
    (d e : ℕ) (x : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r)
    (e' f : ℕ) (y : Correspondence (fieldChowSituation k) (partBase sY e') (partBase sZ f) f s)
    (f' g : ℕ) (z : Correspondence (fieldChowSituation k) (partBase sZ f') (partBase sW g) g t)
    (he : e = e') (hf : f ≠ f') :
    corrCongr k sX sW (add_assoc r s t)
        (comp k sX sZ sW Δ (r + s) t
          (comp k sX sY sZ Δ r s
            (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
            (DirectSum.lof ℚ ℕ _ e' (DirectSum.lof ℚ ℕ _ f y)))
          (DirectSum.lof ℚ ℕ _ f' (DirectSum.lof ℚ ℕ _ g z))) =
      comp k sX sY sW Δ r (s + t) (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
        (comp k sY sZ sW Δ s t
          (DirectSum.lof ℚ ℕ _ e' (DirectSum.lof ℚ ℕ _ f y))
          (DirectSum.lof ℚ ℕ _ f' (DirectSum.lof ℚ ℕ _ g z))) := by
  subst he
  simp only [comp_lof_lof_lof_of_ne k sY sZ sW Δ s t e f f' hf,
    comp_lof_lof_lof_of_ne k sX sZ sW Δ (r + s) t d f f' hf, comp_lof_lof_lof_lof,
    LinearEquiv.map_zero, LinearMap.map_zero]

/-- Associativity of composition on pure blocks: for `c ∈ Corrʳ(X_d, Y_e)`,
`c' ∈ Corrˢ(Y_{e'}, Z_f)` and `c'' ∈ Corrᵗ(Z_{f'}, W_g)`, `c'' ∘ (c' ∘ c) = (c'' ∘ c') ∘ c`,
both sides vanishing unless `e = e'` and `f = f'`. -/
theorem comp_assoc_lof [IsProper sY] [IsProper sZ] (hassoc : Δ.CompositionAssoc) (r s t : ℤ)
    (d e : ℕ) (x : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r)
    (e' f : ℕ) (y : Correspondence (fieldChowSituation k) (partBase sY e') (partBase sZ f) f s)
    (f' g : ℕ) (z : Correspondence (fieldChowSituation k) (partBase sZ f') (partBase sW g) g t) :
    corrCongr k sX sW (add_assoc r s t)
        (comp k sX sZ sW Δ (r + s) t
          (comp k sX sY sZ Δ r s
            (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
            (DirectSum.lof ℚ ℕ _ e' (DirectSum.lof ℚ ℕ _ f y)))
          (DirectSum.lof ℚ ℕ _ f' (DirectSum.lof ℚ ℕ _ g z))) =
      comp k sX sY sW Δ r (s + t) (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
        (comp k sY sZ sW Δ s t
          (DirectSum.lof ℚ ℕ _ e' (DirectSum.lof ℚ ℕ _ f y))
          (DirectSum.lof ℚ ℕ _ f' (DirectSum.lof ℚ ℕ _ g z))) := by
  by_cases he : e = e'
  · by_cases hf : f = f'
    · subst he hf
      simp only [comp_lof_lof_lof_lof, corrCongr_lof_lof]
      rw [hassoc]
    · exact comp_assoc_lof_of_ne_right k sX sY sZ sW Δ r s t d e x e' f y f' g z he hf
  · exact comp_assoc_lof_of_ne_left k sX sY sZ sW Δ r s t d e x e' f y f' g z he

private theorem comp_assoc_of_lof_of_lof [IsProper sY] [IsProper sZ]
    (hassoc : Δ.CompositionAssoc) (r s t : ℤ)
    (d e : ℕ) (x : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r)
    (e' f : ℕ) (y : Correspondence (fieldChowSituation k) (partBase sY e') (partBase sZ f) f s)
    (c'' : Corr k sZ sW t) :
    corrCongr k sX sW (add_assoc r s t)
        (comp k sX sZ sW Δ (r + s) t
          (comp k sX sY sZ Δ r s (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
            (DirectSum.lof ℚ ℕ _ e' (DirectSum.lof ℚ ℕ _ f y))) c'') =
      comp k sX sY sW Δ r (s + t) (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
        (comp k sY sZ sW Δ s t (DirectSum.lof ℚ ℕ _ e' (DirectSum.lof ℚ ℕ _ f y)) c'') := by
  induction c'' using Corr.induction_on with
  | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | lof f' g z => exact comp_assoc_lof k sX sY sZ sW Δ hassoc r s t d e x e' f y f' g z

private theorem comp_assoc_of_lof [IsProper sY] [IsProper sZ] (hassoc : Δ.CompositionAssoc)
    (r s t : ℤ)
    (d e : ℕ) (x : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r)
    (c' : Corr k sY sZ s) (c'' : Corr k sZ sW t) :
    corrCongr k sX sW (add_assoc r s t)
        (comp k sX sZ sW Δ (r + s) t
          (comp k sX sY sZ Δ r s (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x)) c') c'') =
      comp k sX sY sW Δ r (s + t) (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
        (comp k sY sZ sW Δ s t c' c'') := by
  induction c' using Corr.induction_on with
  | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero, LinearMap.zero_apply]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | lof e' f y =>
    exact comp_assoc_of_lof_of_lof k sX sY sZ sW Δ hassoc r s t d e x e' f y c''

/-- **Associativity of composition of correspondences** (the second half of Stacks 0FG0 (1)) for
smooth `X`, `Y`, `Z`, `W` over `k`, `Y` and `Z` proper, not necessarily equidimensional:
`c'' ∘ (c' ∘ c) = (c'' ∘ c') ∘ c`, the two sides compared through the identification of the
degrees `(r + s) + t = r + (s + t)`, for any family `Δ` of diagonal classes for which
composition of correspondences between schemes of constant dimension is associative. -/
theorem comp_assoc [IsProper sY] [IsProper sZ] (hassoc : Δ.CompositionAssoc) (r s t : ℤ)
    (c : Corr k sX sY r) (c' : Corr k sY sZ s) (c'' : Corr k sZ sW t) :
    corrCongr k sX sW (add_assoc r s t)
        (comp k sX sZ sW Δ (r + s) t (comp k sX sY sZ Δ r s c c') c'') =
      comp k sX sY sW Δ r (s + t) c (comp k sY sZ sW Δ s t c' c'') := by
  induction c using Corr.induction_on with
  | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero, LinearMap.zero_apply]
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | lof d e x => exact comp_assoc_of_lof k sX sY sZ sW Δ hassoc r s t d e x c' c''

/-- **Stacks 0FG0 (1)** for smooth `X`, `Y`, `Z`, `W` over `k`, `Y` and `Z` proper, not
necessarily equidimensional: composition of correspondences is `ℚ`-bilinear and associative,
for any family `Δ` of diagonal classes for which composition of correspondences between schemes
of constant dimension is associative. -/
theorem comp_bilinear_assoc [IsProper sY] [IsProper sZ] (hassoc : Δ.CompositionAssoc)
    (r s t : ℤ) :
    (∀ (a b : ℚ) (c₁ c₂ : Corr k sX sY r) (c' : Corr k sY sZ s),
      comp k sX sY sZ Δ r s (a • c₁ + b • c₂) c' =
        a • comp k sX sY sZ Δ r s c₁ c' + b • comp k sX sY sZ Δ r s c₂ c') ∧
    (∀ (a b : ℚ) (c : Corr k sX sY r) (c'₁ c'₂ : Corr k sY sZ s),
      comp k sX sY sZ Δ r s c (a • c'₁ + b • c'₂) =
        a • comp k sX sY sZ Δ r s c c'₁ + b • comp k sX sY sZ Δ r s c c'₂) ∧
    ∀ (c : Corr k sX sY r) (c' : Corr k sY sZ s) (c'' : Corr k sZ sW t),
      corrCongr k sX sW (add_assoc r s t)
          (comp k sX sZ sW Δ (r + s) t (comp k sX sY sZ Δ r s c c') c'') =
        comp k sX sY sW Δ r (s + t) c (comp k sY sZ sW Δ s t c' c'') :=
  ⟨fun a b c₁ c₂ c' ↦ by rw [LinearMap.map_add₂, LinearMap.map_smul₂, LinearMap.map_smul₂],
    fun a b c c'₁ c'₂ ↦ by rw [map_add, map_smul, map_smul],
    comp_assoc k sX sY sZ sW Δ hassoc r s t⟩

end Stacks.WeilCohomology

end
