module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalExtension.Data
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Poincaré duality for the extension of a classical Weil cohomology theory

The data (D0)–(D3) of Section 45.9 (Tag 0FHA) obtained from a classical Weil cohomology theory
by taking products over connected components
(`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.toWeilData`) satisfy axiom (A): the
cohomology groups `H^i(X) = ∏_c H^i(X_c)` are finite dimensional, and for `X` nonempty and
equidimensional of dimension `d` the pairing `(a, b) ↦ ∫_X a ∪ b = ∑_c ∫_{X_c} a_c ∪ b_c` is
perfect, since each component is a smooth projective variety of dimension `d` on which Poincaré
duality holds. The twisted operations of (D0)–(D3) are also computed in the coordinate
`F(m) = F`.

## Main definitions

* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.twCoord`: the coordinate
  `H^n(X)(m) = H^n(X)` of the extension.

## Main results

* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.finiteDimensionality`: axiom (A)(a).
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.perfectPairing`: axiom (A)(b).
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.poincareDuality`: axiom (A).
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry DirectSum Stacks.Chow

universe u v

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

namespace ClassicalWeilCohomologyTheory

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  (T : ChowClassicalWeilCohomologyTheory.{u, v, v} k F)

/-! ### The twisted operations in coordinates -/

/-- The coordinate `H^n(X)(m) = H^n(X)` of the extension, `F(1)` being `F`. -/
def twCoord (X : (SmoothProjectiveScheme k).FullSubcategory) (n m : ℤ) :
    T.toWeilData.Tw X n m ≃ₗ[F] T.toWeilData.grade X n :=
  tateTwistCoordinates (LinearEquiv.refl F F) m

/-- In the coordinate `twCoord`, the twisted pullback is the pullback `pullDeg`. -/
theorem twistCoord_pullTw {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (n m : ℤ)
    (x : T.toWeilData.Tw Y n m) :
    T.twCoord X n m (T.toWeilData.pullTw f n m x) =
      T.toWeilData.pullDeg f n (T.twCoord Y n m x) :=
  tateTwistCoordinates_map _ _ _ _

/-- The pullback `pullDeg f n x` is `extPull f x` in the total cohomology of `X`. -/
@[simp]
theorem coe_pullDeg {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (n : ℤ)
    (x : T.toWeilData.grade Y n) : (T.toWeilData.pullDeg f n x : T.extH X) = T.extPull f x :=
  rfl

/-- In the coordinate `twCoord`, the twisted cup product is the cup product. -/
theorem twistCoord_cupTw (X : (SmoothProjectiveScheme k).FullSubcategory) (i j n : ℤ)
    (h : i + j = n)
    (s t m : ℤ) (h' : s + t = m) (x : T.toWeilData.Tw X i s) (y : T.toWeilData.Tw X j t) :
    T.twCoord X n m (T.toWeilData.cupTw X i j n h s t m h' x y) =
      T.toWeilData.cup X i j n h (T.twCoord X i s x) (T.twCoord X j t y) := by
  rw [WeilData.cupTw, tateCup_eq_with _ (LinearEquiv.refl F F)]
  simp [tateCupWith, twCoord]

/-- In the coordinate `twCoord`, the cycle class of `α` is the untwisted cycle class
`extCycleClassUntw X r α`. -/
@[simp]
theorem coe_twistCoord_cycleClass (X : (SmoothProjectiveScheme k).FullSubcategory) (r : ℤ)
    (α : codimensionChowGroup k X.obj.hom r) :
    (T.twCoord X (2 * r) r (T.toWeilData.cycleClass X r α) : T.extH X) =
      T.extCycleClassUntw X r α := by
  simp [toWeilData, extCycleClass, twCoord]

/-- The trace of the extension is `extTraceUntw` in the coordinate `twCoord`. -/
theorem toWeilData_trace (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) (x : T.toWeilData.Tw X (2 * d) d) :
    T.toWeilData.trace X d hX x = T.extTraceUntw X hX (T.twCoord X (2 * d) d x) :=
  rfl

/-- The trace of `x` is the sum over the connected components `X_i` of the integrals of the
degree-`2d` components of `x i`. -/
theorem extTraceUntw_apply (X : (SmoothProjectiveScheme k).FullSubcategory) {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) (x : T.extH X) :
    T.extTraceUntw X hX x = ∑ i, T.integration (compAt X i)
      (ExternallyGraded.degreeCast (R := F) (X := (T.H (compAt X i)).piece)
        (by rw [T.dimension_compAt hX i]) (component F ℤ _ (2 * (d : ℤ)) (x i))) := by
  simp [extTraceUntw, LinearMap.sum_apply]

/-- The trace of a class supported on the component `X_c` is the integral over `X_c` of its
degree-`2d` component. -/
theorem extTraceUntw_single (X : (SmoothProjectiveScheme k).FullSubcategory) {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) (c : Idx X) (z : T.totalH (compAt X c)) :
    T.extTraceUntw X hX (Pi.single c z) = T.integration (compAt X c)
      (ExternallyGraded.degreeCast (R := F) (X := (T.H (compAt X c)).piece)
        (by rw [T.dimension_compAt hX c]) (component F ℤ _ (2 * (d : ℤ)) z)) := by
  rw [extTraceUntw_apply, Finset.sum_eq_single c (fun b _ hb ↦ by simp [Pi.single_eq_of_ne hb])
    (by simp)]
  simp

/-- The pairing of the extension is `(a, b) ↦ extTraceUntw (a * b)`, with `b` read in the
coordinate `twCoord`. -/
theorem toWeilData_pairing (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) (i j : ℤ) (h : i + j = 2 * d) (a : T.extGrade X i)
    (b : T.toWeilData.Tw X j d) :
    T.toWeilData.pairing X d hX i j h a b =
      T.extTraceUntw X hX ((a : T.extH X) * (T.twCoord X j d b : T.extH X)) := by
  simp only [WeilData.pairing, LinearMap.compr₂_apply, tateCupLeft, LinearMap.mk₂_apply,
    extTrace, LinearMap.comp_apply, LinearEquiv.coe_coe, twistCoord, twCoord,
    Submodule.coe_subtype]
  rw [tateTwistCoordinates_map]
  rfl

/-- The trace of `a ∪ b` for `a`, `b` supported on one component, in complementary degrees, is
the trace pairing of that component. -/
theorem extTraceUntw_single_mul (X : (SmoothProjectiveScheme k).FullSubcategory) {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) (c : Idx X) (i j : ℤ) (h : i + j = 2 * d)
    (x : (T.H (compAt X c)).piece i) (y : (T.H (compAt X c)).piece j) :
    T.extTraceUntw X hX (Pi.single c (lof F ℤ _ i x * lof F ℤ _ j y)) =
      (T.H (compAt X c)).tracePairing (T.dimension (compAt X c))
        (T.integration (compAt X c)).toLinearMap i x
        (ExternallyGraded.degreeCast (R := F) (X := (T.H (compAt X c)).piece)
          (by rw [T.dimension_compAt hX c]; omega) y) := by
  rw [extTraceUntw_single, ExternallyGradedAlgebra.lof_mul_lof,
    ExternallyGradedAlgebra.component_lof_of_eq _ h]
  simp only [ExternallyGradedAlgebra.tracePairing, LinearMap.compr₂_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  congr 1
  exact eq_of_heq ((ExternallyGraded.degreeCast_heq _ _).trans
    ((ExternallyGraded.degreeCast_heq _ _).trans
      ((ExternallyGraded.degreeCast_heq _ _).trans
        ((T.H (compAt X c)).mul_degreeCast_right_heq _ x y)).symm))

/-! ### Axiom (A) -/

/-- Each graded piece `H^n(V)` of a smooth projective variety `V` is finite dimensional. -/
instance finiteDimensional_grade (V : (SmoothProjective k).FullSubcategory) (n : ℤ) :
    FiniteDimensional F ((T.H V).grade n) := by
  have := T.finite V n
  exact Module.Finite.range (lof F ℤ (T.H V).piece n)

/-- Each graded piece `H^n(X) = ∏_c H^n(X_c)` of the extension is finite dimensional. -/
instance finiteDimensional_extGrade (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) :
    FiniteDimensional F (T.extGrade X n) := by
  let e : T.extGrade X n →ₗ[F] ∀ c : Idx X, (T.H (compAt X c)).grade n :=
    LinearMap.pi fun c ↦ ((LinearMap.proj (R := F) (φ := fun c ↦ T.totalH (compAt X c)) c).comp
      (T.extGrade X n).subtype).codRestrict _ fun x ↦ T.mem_extGrade.1 x.2 c
  refine Module.Finite.of_injective e fun x y hxy ↦ Subtype.ext (funext fun c ↦ ?_)
  exact congrArg Subtype.val (congrFun hxy c)

/-- **Axiom (A)(a)** for the extension. -/
theorem finiteDimensionality : T.toWeilData.FiniteDimensionality :=
  fun X _ _ i ↦ T.finiteDimensional_extGrade X i

/-- A class of `H^n(X)` is zero when its component in degree `n` on every connected component
is. -/
theorem eq_zero_of_component {X : (SmoothProjectiveScheme k).FullSubcategory} {n : ℤ} {a : T.extH X}
    (ha : a ∈ T.extGrade X n) (h : ∀ c, component F ℤ _ n (a c) = 0) : a = 0 :=
  funext fun c ↦ by
    rw [← ExternallyGradedAlgebra.lof_component_of_mem _ (T.mem_extGrade.1 ha c), h c, map_zero]
    rfl

/-- A class supported on one connected component, in degree `n`, lies in `H^n(X)`. -/
private theorem single_lof_mem_extGrade {X : (SmoothProjectiveScheme k).FullSubcategory}
    (c : Idx X) (n : ℤ) (x : (T.H (compAt X c)).piece n) :
    Pi.single c (lof F ℤ _ n x) ∈ T.extGrade X n := T.mem_extGrade.2 fun c' ↦ by
  by_cases hc : c' = c
  · subst hc; simp
  · simp [Pi.single_eq_of_ne hc]

/-- **Axiom (A)(b)** for the extension: the pairing `(a, b) ↦ ∑_c ∫_{X_c} a_c ∪ b_c` is
perfect. -/
theorem perfectPairing : T.toWeilData.PerfectPairing := by
  intro X d hX i j h
  have : FiniteDimensional F (T.toWeilData.grade X i) := T.finiteDimensional_extGrade X i
  refine LinearMap.IsPerfPair.of_injective ?_ ?_
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    refine Subtype.ext (T.eq_zero_of_component a.2 fun c ↦ ?_)
    have := T.perfect (compAt X c) i
    refine (LinearMap.IsPerfPair.bijective_left
      ((T.H (compAt X c)).tracePairing (T.dimension (compAt X c))
        (T.integration (compAt X c)).toLinearMap i)).injective (LinearMap.ext fun y ↦ ?_)
    have hd := T.dimension_compAt hX c
    set y' : (T.H (compAt X c)).piece j :=
      ExternallyGraded.degreeCast (R := F) (X := (T.H (compAt X c)).piece) (by omega) y
    have h0 := LinearMap.congr_fun ha
      ((T.twCoord X j d).symm ⟨_, T.single_lof_mem_extGrade c j y'⟩)
    rw [LinearMap.zero_apply, toWeilData_pairing, LinearEquiv.apply_symm_apply] at h0
    have hmul : (a : T.extH X) * Pi.single c (lof F ℤ _ j y') =
        Pi.single c (lof F ℤ _ i (component F ℤ _ i ((a : T.extH X) c)) * lof F ℤ _ j y') := by
      rw [ExternallyGradedAlgebra.lof_component_of_mem _ (T.mem_extGrade.1 a.2 c)]
      funext c'
      by_cases hc : c' = c
      · subst hc; simp
      · simp [Pi.single_eq_of_ne hc]
    have hy : ExternallyGraded.degreeCast (R := F) (X := (T.H (compAt X c)).piece)
        (show j = 2 * (T.dimension (compAt X c) : ℤ) - i by omega) y' = y := by
      simp [y']
    rw [hmul, extTraceUntw_single_mul T X hX c i j h, hy] at h0
    rw [map_zero, LinearMap.zero_apply]
    exact h0
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    refine (T.twCoord X j d).injective ?_
    rw [LinearEquiv.map_zero]
    refine Subtype.ext (T.eq_zero_of_component (T.twCoord X j d b).2 fun c ↦ ?_)
    have := T.perfect (compAt X c) i
    have hd := T.dimension_compAt hX c
    set y := component F ℤ _ j ((T.twCoord X j d b : T.extH X) c)
    suffices hy : ExternallyGraded.degreeCast (R := F) (X := (T.H (compAt X c)).piece)
        (show j = 2 * (T.dimension (compAt X c) : ℤ) - i by omega) y = 0 by
      have h' := congrArg (ExternallyGraded.degreeCast (R := F) (X := (T.H (compAt X c)).piece)
        (show 2 * (T.dimension (compAt X c) : ℤ) - i = j by omega)) hy
      simpa [y] using h'
    refine (LinearMap.IsPerfPair.bijective_right
      ((T.H (compAt X c)).tracePairing (T.dimension (compAt X c))
        (T.integration (compAt X c)).toLinearMap i)).injective (LinearMap.ext fun x ↦ ?_)
    have h0 : T.toWeilData.pairing X d hX i j h ⟨_, T.single_lof_mem_extGrade c i x⟩ b = 0 := by
      simpa using LinearMap.congr_fun hb ⟨_, T.single_lof_mem_extGrade c i x⟩
    rw [toWeilData_pairing] at h0
    have hmul : Pi.single c (lof F ℤ _ i x) * (T.twCoord X j d b : T.extH X) =
        Pi.single c (lof F ℤ _ i x * lof F ℤ _ j y) := by
      funext c'
      by_cases hc : c' = c
      · subst hc
        simp only [Pi.mul_apply, Pi.single_eq_same, y]
        rw [ExternallyGradedAlgebra.lof_component_of_mem _
          (T.mem_extGrade.1 (T.twCoord X j d b).2 c')]
      · simp [Pi.single_eq_of_ne hc]
    rw [Subtype.coe_mk, hmul, extTraceUntw_single_mul T X hX c i j h] at h0
    rw [map_zero, LinearMap.zero_apply]
    exact h0

/-- **Axiom (A), Poincaré duality**, for the extension. -/
theorem poincareDuality : T.toWeilData.PoincareDuality :=
  ⟨T.finiteDimensionality, T.perfectPairing⟩

end ClassicalWeilCohomologyTheory

end Stacks.WeilCohomology

end
