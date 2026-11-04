module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DiagonalDualBasis
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilDataCoordinates
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Weil cohomology data in coordinates: cycle classes, traces and Poincaré duality

Let `W` be data (D0)–(D3) of Section 45.9 (Tag 0FHA) over the actual category of smooth
projective schemes over `k` (`Stacks.WeilCohomology.WeilData`). The construction of the functor
on Chow motives of Stacks 0FHL computes with the cycle classes `γ(c)` of correspondences, with
cup products in the rings `H^*(X × Y)` and with the trace maps `∫`. This file restates the
data and axioms (A), (B), (C) in the coordinates of the Tate twists
(`Stacks.WeilCohomology.WeilData.twCoord`), so that all of them become statements about the
cohomology rings themselves:

* the cycle class map read in `H^{2i}(X) ⊂ H^*(X)`, `WeilData.cycleClassRing`, and axioms
  (C)(a), (C)(c) for it (`cycleClassRing_codimensionGysin`, `cycleClassRing_mul`);
* axiom (C)(b) as the trace identity `∫_Y b ∪ γ(f_*α) = ∫_X f^*b ∪ γ(α)`
  (`traceProj_mul_cycleClassRing_pushforward`);
* axiom (B)(b) as `∫_{X × Y} pr₁^*x ∪ pr₂^*y = ∫_X x · ∫_Y y` for all classes `x`, `y`
  (`traceProj_pull_fst_mul_pull_snd`);
* axiom (A)(b) as the representation of linear forms on `H^{2e-i}(Y)` by classes of `H^i(Y)`
  through `(u, b) ↦ ∫_Y u ∪ b` (`traceDual`, `traceProj_traceDual_mul`,
  `eq_of_traceProj_mul_eq`).

Here `∫_X` is extended to the whole ring by zero outside the top degree
(`Stacks.WeilCohomology.WeilData.traceProj`).

## References

* [Stacks Project, Section 45.9 (Tag 0FHA)](https://stacks.math.columbia.edu/tag/0FHA)
* [Stacks Project, Tag 0FHL](https://stacks.math.columbia.edu/tag/0FHL)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology.WeilData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] (W : WeilData k F)

/-- The trace depends on the dimension only through its value. -/
theorem traceProj_congr (X : (SmoothProjectiveScheme k).FullSubcategory) {d d' : ℕ} (h : d = d')
    (hX : IsNonemptyEquidimensional X d) (hX' : IsNonemptyEquidimensional X d') :
    W.traceProj X d hX = W.traceProj X d' hX' := by
  subst h
  rfl

/-! ### The cycle class map in coordinates -/

/-- **The cycle class map `γ : CH^i(X) → H^{2i}(X)(i)` read in `H^*(X)`**, through the coordinate
`H^{2i}(X)(i) ≃ H^{2i}(X)` of the Tate twist. -/
def cycleClassRing (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ) :
    codimensionChowGroup k X.obj.hom i →+ W.H X :=
  (W.grade X (2 * i)).subtype.toAddMonoidHom.comp (W.cycleClassCoord X i)

/-- `cycleClassRing X i α` is the image of `γ(α) ∈ H^{2i}(X)(i)` under the coordinate
`H^{2i}(X)(i) ≃ H^{2i}(X)`. -/
theorem cycleClassRing_apply (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) :
    W.cycleClassRing X i α = (W.twCoord X (2 * i) i (W.cycleClass X i α) : W.H X) :=
  rfl

/-- The cycle class of a codimension `i` cycle is homogeneous of degree `2i`. -/
theorem cycleClassRing_mem (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) : W.cycleClassRing X i α ∈ W.grade X (2 * i) :=
  (W.twCoord X (2 * i) i (W.cycleClass X i α)).2

variable {W}

/-- **Axiom (C)(a) in coordinates**: `γ(f^!β) = f^*γ(β)`. -/
theorem cycleClassRing_codimensionGysin (hCa : W.CycleClassPullback)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (i : ℤ)
    (β : codimensionChowGroup k Y.obj.hom i) :
    W.cycleClassRing X i (codimensionGysin X.obj.hom Y.obj.hom (Over.w f.hom) i β) =
      W.pull f (W.cycleClassRing Y i β) := by
  rw [cycleClassRing_apply, hCa f i β, twCoord_pullTw, coe_pullDeg]
  rfl

/-- **Axiom (C)(c) in coordinates**: `γ(α · β) = γ(α) ∪ γ(β)`. -/
theorem cycleClassRing_mul (hCc : W.CycleClassMul) (X : (SmoothProjectiveScheme k).FullSubcategory)
    (i j : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) (β : codimensionChowGroup k X.obj.hom j) :
    W.cycleClassRing X (i + j) (codimensionIntersectionProduct k X.obj.hom i j α β) =
      W.cycleClassRing X i α * W.cycleClassRing X j β := by
  rw [cycleClassRing_apply, hCc X i j α β, twCoord_cupTw, coe_cup]
  rfl

/-- **Axiom (C)(b) in coordinates**, as a trace identity: for a morphism `f : X ⟶ Y` of nonempty
equidimensional smooth projective schemes of dimensions `d` and `e` and `α ∈ CH^p(X)`,
`∫_Y b ∪ γ(f_*α) = ∫_X f^*b ∪ γ(α)` for every `b ∈ H^*(Y)`. -/
theorem traceProj_mul_cycleClassRing_pushforward (hA : W.PerfectPairing)
    (hCb : W.CycleClassPushforward hA) {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e) (p q : ℤ)
    (h : q = p + e - d) (α : codimensionChowGroup k X.obj.hom p) (b : W.H Y) :
    W.traceProj Y e hY (b * W.cycleClassRing Y q (equidimensionalPushforward f d e p q h α)) =
      W.traceProj X d hX (W.pull f b * W.cycleClassRing X p α) := by
  induction b using DirectSum.Decomposition.inductionOn (W.grade Y) with
  | zero => simp
  | add x y hx hy => rw [add_mul, map_add, hx, map_add, add_mul, map_add, hy]
  | @homogeneous m b =>
    obtain ⟨b, hbm⟩ := b
    show W.traceProj Y e hY (b * _) = W.traceProj X d hX (W.pull f b * _)
    by_cases hm : m = 2 * e - 2 * q
    · subst hm
      have key := pushforward_trace' hA f hX hY (2 * p) p (2 * q) q (by omega) (by omega)
        (2 * e - 2 * q) (e - q) (by omega) (by omega) (by omega) (by omega)
        ((W.twCoord Y _ (e - q)).symm ⟨b, hbm⟩) (W.cycleClass X p α)
      rw [← hCb f d e hX hY p q h α, pairingTw_eq_traceProj, pairingTw_eq_traceProj,
        twCoord_pullTw, LinearEquiv.apply_symm_apply, coe_pullDeg] at key
      rw [cycleClassRing_apply, cycleClassRing_apply]
      exact key.symm
    · rw [W.traceProj_of_mem_ne Y e hY (SetLike.GradedMul.mul_mem hbm (W.cycleClassRing_mem Y q _))
        (by omega), W.traceProj_of_mem_ne X d hX (SetLike.GradedMul.mul_mem
          (W.pull_grade f m b hbm) (W.cycleClassRing_mem X p α)) (by omega)]

/-! ### Axiom (B)(b) on all classes -/

/-- **Axiom (B)(b) in coordinates, on all classes**: for `X`, `Y` nonempty and equidimensional of
dimensions `d` and `e`, `∫_{X × Y} pr₁^*x ∪ pr₂^*y = ∫_X x · ∫_Y y` for all `x ∈ H^*(X)`,
`y ∈ H^*(Y)`, the traces being zero outside the top degrees. -/
theorem traceProj_pull_fst_mul_pull_snd (hK : W.KunnethTrace)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {d e : ℕ} (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (hXY : IsNonemptyEquidimensional (prod X Y) (d + e)) (x : W.H X) (y : W.H Y) :
    W.traceProj (prod X Y) (d + e) hXY (W.pull (fst X Y) x * W.pull (snd X Y) y) =
      W.traceProj X d hX x * W.traceProj Y e hY y := by
  induction x using DirectSum.Decomposition.inductionOn (W.grade X) with
  | zero => simp
  | add x x' hx hx' => rw [map_add, add_mul, map_add, hx, hx', map_add, add_mul]
  | @homogeneous m x =>
    obtain ⟨x, hxm⟩ := x
    show W.traceProj _ _ hXY (W.pull (fst X Y) x * _) = W.traceProj X d hX x * _
    induction y using DirectSum.Decomposition.inductionOn (W.grade Y) with
    | zero => simp
    | add y y' hy hy' => rw [map_add, mul_add, map_add, hy, hy', map_add, mul_add]
    | @homogeneous m' y =>
      obtain ⟨y, hym⟩ := y
      show W.traceProj _ _ hXY (_ * W.pull (snd X Y) y) = _ * W.traceProj Y e hY y
      have hprod : W.pull (fst X Y) x * W.pull (snd X Y) y ∈ W.grade (prod X Y) (m + m') :=
        SetLike.GradedMul.mul_mem (W.pull_grade _ m x hxm) (W.pull_grade _ m' y hym)
      by_cases hm : m = 2 * d
      · subst hm
        by_cases hm' : m' = 2 * e
        · subst hm'
          have h := (hK X Y d e hX hY hXY).1 ((W.twCoord X _ d).symm ⟨x, hxm⟩)
            ((W.twCoord Y _ e).symm ⟨y, hym⟩)
          rw [trace_eq_traceProj, twCoord_cupTw, coe_cup, twCoord_pullTw, twCoord_pullTw,
            coe_pullDeg, coe_pullDeg, LinearEquiv.apply_symm_apply,
            LinearEquiv.apply_symm_apply] at h
          rw [h, traceProj_of_mem _ _ _ _ hxm, traceProj_of_mem _ _ _ _ hym]
        · rw [W.traceProj_of_mem_ne _ _ hXY hprod (by push_cast; omega),
            W.traceProj_of_mem_ne Y e hY hym hm', mul_zero]
      · rw [W.traceProj_of_mem_ne X d hX hxm hm, zero_mul]
        by_cases htot : m + m' = 2 * ((d + e : ℕ) : ℤ)
        · have h := (hK X Y d e hX hY hXY).2 m m' htot hm ((W.twCoord X m d).symm ⟨x, hxm⟩)
            ((W.twCoord Y m' e).symm ⟨y, hym⟩)
          rwa [trace_eq_traceProj, twCoord_cupTw, coe_cup, twCoord_pullTw, twCoord_pullTw,
            coe_pullDeg, coe_pullDeg, LinearEquiv.apply_symm_apply,
            LinearEquiv.apply_symm_apply] at h
        · exact W.traceProj_of_mem_ne _ _ hXY hprod htot

/-! ### Axiom (A)(b): representing linear forms by classes -/

variable (W) in
/-- **The class representing a linear form, by Poincaré duality.** For `Y` nonempty and
equidimensional of dimension `e`, a linear form `φ` on `H^{2e-i}(Y)` is `b ↦ ∫_Y u ∪ b` for a
unique `u ∈ H^i(Y)`: axiom (A)(b). -/
def traceDual (hA : W.PerfectPairing) (Y : (SmoothProjectiveScheme k).FullSubcategory) {e : ℕ}
    (hY : IsNonemptyEquidimensional Y e) (i : ℤ) :
    (W.grade Y (2 * e - i) →ₗ[F] F) →ₗ[F] W.grade Y i :=
  haveI := hA Y e hY i (2 * e - i) (add_sub_cancel i (2 * (e : ℤ)))
  (W.pairing Y e hY i (2 * e - i) (add_sub_cancel i (2 * (e : ℤ)))).toPerfPair.symm.toLinearMap ∘ₗ
    (W.twCoord Y (2 * e - i) e).toLinearMap.dualMap

/-- The class `traceDual φ` represents `φ`: `∫_Y u ∪ b = φ(b)`. -/
theorem traceProj_traceDual_mul (hA : W.PerfectPairing)
    (Y : (SmoothProjectiveScheme k).FullSubcategory) {e : ℕ}
    (hY : IsNonemptyEquidimensional Y e) (i : ℤ) (φ : W.grade Y (2 * e - i) →ₗ[F] F)
    (b : W.grade Y (2 * e - i)) :
    W.traceProj Y e hY ((W.traceDual hA Y hY i φ : W.H Y) * b) = φ b := by
  have := hA Y e hY i (2 * e - i) (add_sub_cancel i (2 * (e : ℤ)))
  have h := LinearMap.apply_symm_toPerfPair_self
    (W.pairing Y e hY i (2 * e - i) (add_sub_cancel i (2 * (e : ℤ))))
    ((W.twCoord Y (2 * e - i) e).toLinearMap.dualMap φ)
  have h' := LinearMap.congr_fun h ((W.twCoord Y (2 * e - i) e).symm b)
  rw [pairing_eq_traceProj, LinearEquiv.apply_symm_apply] at h'
  rw [traceDual, LinearMap.comp_apply, LinearEquiv.coe_coe]
  simpa using h'

/-- **Axiom (A)(b): a class of `H^i(Y)` is determined by its pairings with `H^{2e-i}(Y)`.** -/
theorem eq_of_traceProj_mul_eq (hA : W.PerfectPairing)
    {Y : (SmoothProjectiveScheme k).FullSubcategory} {e : ℕ}
    (hY : IsNonemptyEquidimensional Y e) {i : ℤ} {u u' : W.grade Y i}
    (h : ∀ b : W.grade Y (2 * e - i),
      W.traceProj Y e hY ((u : W.H Y) * b) = W.traceProj Y e hY ((u' : W.H Y) * b)) :
    u = u' := by
  have := hA Y e hY i (2 * e - i) (add_sub_cancel i (2 * (e : ℤ)))
  refine (LinearMap.IsPerfPair.bijective_left
    (W.pairing Y e hY i (2 * e - i) (add_sub_cancel i (2 * (e : ℤ))))).injective
    (LinearMap.ext fun b ↦ ?_)
  rw [pairing_eq_traceProj, pairing_eq_traceProj]
  exact h _

/-- `traceDual` is characterised by the trace identity. -/
theorem eq_traceDual_iff (hA : W.PerfectPairing)
    {Y : (SmoothProjectiveScheme k).FullSubcategory} {e : ℕ}
    (hY : IsNonemptyEquidimensional Y e) {i : ℤ} (φ : W.grade Y (2 * e - i) →ₗ[F] F)
    (u : W.grade Y i) :
    u = W.traceDual hA Y hY i φ ↔ ∀ b : W.grade Y (2 * e - i),
      W.traceProj Y e hY ((u : W.H Y) * b) = φ b := by
  refine ⟨fun h b ↦ h ▸ traceProj_traceDual_mul hA Y hY i φ b, fun h ↦ ?_⟩
  exact eq_of_traceProj_mul_eq hA hY fun b ↦ by rw [h, traceProj_traceDual_mul]

end Stacks.WeilCohomology.WeilData

end
