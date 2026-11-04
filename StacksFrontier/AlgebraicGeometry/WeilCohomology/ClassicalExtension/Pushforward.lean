module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalExtension.ChowPushforward
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalExtension.CycleClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalTraceDegree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Axiom (C)(b) for the extension of a classical Weil cohomology theory

For the data (D0)–(D3) obtained from a classical Weil cohomology theory by taking products over
connected components (`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.toWeilData`), the
cycle class map is compatible with proper pushforward. Let `f : X ⟶ Y` be a morphism of nonempty
equidimensional smooth projective schemes. A class `α` on `X` is the sum `∑_c ι_{c,*}(α|_{X_c})`
of its restrictions to the components, and `f_*ι_{c,*} = ι_{d,*} f_{c,*}` for the restriction
`f_c : X_c ⟶ Y_d` of `f`; on cohomology, the pairing of `γ(f_*α)` with a class `b` is then the sum
over the components `X_c` of the pairings of `γ(f_{c,*}(α|_{X_c}))` with `b|_{Y_d}`, which by the
classical theory's axiom (C)(b) on `f_c` (in its trace form,
`ClassicalWeilCohomologyTheory.integration_pullback_mul_cycleClass`) is the pairing of
`γ(α|_{X_c})` with `f_c^* b|_{Y_d}`. Summing over `c` gives the trace equation characterising
`f_*γ(α)`.

## Main results

* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.cycleClassPushforward`: axiom (C)(b).
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.cycleClassAxiom`: axiom (C).
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry DirectSum Stacks.Chow

universe u v

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

namespace ClassicalWeilCohomologyTheory

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  (T : ChowClassicalWeilCohomologyTheory.{u, v, v} k F)

omit [IsAlgClosed k] in
/-- The pushforward between equidimensional schemes respects transport of both dimensions. -/
theorem equidimensionalPushforward_heq_of_eq {X' Y' : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X' ⟶ Y')
    {d d' e e' : ℕ} (hd : d = d') (he : e = e') (p : ℤ) {q q' : ℤ} (hq : q = p + e - d)
    (hq' : q' = p + e' - d') (α : codimensionChowGroup k X'.obj.hom p) :
    equidimensionalPushforward f d e p q hq α ≍ equidimensionalPushforward f d' e' p q' hq' α := by
  subst hd he hq hq'
  rfl

/-- Two transports of heterogeneously equal elements to the same degree are equal. -/
private theorem degreeCast_eq_degreeCast_of_heq {R : Type*} [CommRing R] {X : ℤ → Type*}
    [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)] {i i' j : ℤ} (h : i = j) (h' : i' = j)
    {x : X i} {y : X i'} (hxy : x ≍ y) :
    ExternallyGraded.degreeCast (R := R) h x =
      ExternallyGraded.degreeCast (R := R) h' y :=
  eq_of_heq ((ExternallyGraded.degreeCast_heq _ _).trans
    (hxy.trans (ExternallyGraded.degreeCast_heq _ _).symm))

/-- **Axiom (C)(b) of the classical theory, in the form used on components**: for
`g : V ⟶ W` of smooth projective varieties of dimensions `d` and `e`,
`∫_V g^*y ∪ γ(a) = ∫_W y ∪ γ(g_* a)`, on total cohomology. -/
theorem integration_pullTotal_mul_cycleClass {V W : (SmoothProjective k).FullSubcategory}
    (g : V ⟶ W) {d e : ℕ} (hV : T.dimension V = d) (hW : T.dimension W = e) (p q : ℤ)
    (h : q = p + e - d)
    (a : codimensionChowGroup k ((SmoothProjective.toSchemeCat k).obj V).obj.hom p)
    (y : (T.H W).piece (2 * d - 2 * p)) :
    T.integration V (ExternallyGraded.degreeCast (R := F) (X := (T.H V).piece)
      (by rw [hV]) (component F ℤ _ (2 * (d : ℤ))
        (T.pullTotal g (lof F ℤ _ _ y) * lof F ℤ _ (2 * p) (T.cycleClass V p a)))) =
    T.integration W (ExternallyGraded.degreeCast (R := F) (X := (T.H W).piece)
      (by rw [hW]) (component F ℤ _ (2 * (e : ℤ))
        (lof F ℤ _ _ y * lof F ℤ _ (2 * q) (T.cycleClass W q
          (equidimensionalPushforward ((SmoothProjective.toSchemeCat k).map g) d e p q h
            a))))) := by
  subst hV hW
  have hc := T.integration_pullback_mul_cycleClass g p a y
  simp only [ExternallyGradedAlgebra.tracePairing, LinearMap.compr₂_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe] at hc
  rw [pullTotal_lof, ExternallyGradedAlgebra.lof_mul_lof, ExternallyGradedAlgebra.lof_mul_lof,
    ExternallyGradedAlgebra.component_lof_of_eq _ (by ring),
    ExternallyGradedAlgebra.component_lof_of_eq _ (by omega),
    ExternallyGraded.degreeCast_degreeCast, ExternallyGraded.degreeCast_degreeCast]
  refine Eq.trans ?_ (hc.trans ?_)
  · refine congrArg _ (degreeCast_eq_degreeCast_of_heq _ _ ?_)
    exact (T.H V).mul_heq_mul rfl (by ring) HEq.rfl (ExternallyGraded.degreeCast_heq _ _).symm
  · refine congrArg _ (degreeCast_eq_degreeCast_of_heq _ _ ?_)
    refine (T.H W).mul_heq_mul rfl (by omega) HEq.rfl
      ((ExternallyGraded.degreeCast_heq _ _).trans ?_)
    refine T.cycleClass_heq _ (by omega) ?_
    exact equidimensionalPushforward_heq ((SmoothProjective.toSchemeCat k).map g) _ rfl p rfl h a

/-- The cycle class of a pushforward from a component is supported on that component. -/
theorem extCycleClassUntw_compPushforward {Y : (SmoothProjectiveScheme k).FullSubcategory} {e : ℕ}
    (hY : RelativeDimension Y.obj.hom e) (i : Idx Y) (q : ℤ)
    (z : codimensionChowGroup k ((SmoothProjective.toSchemeCat k).obj (compAt Y i)).obj.hom q) :
    T.extCycleClassUntw Y q (compPushforward Y e i q z) =
      Pi.single i (lof F ℤ _ (2 * q) (T.cycleClass (compAt Y i) q z)) := by
  funext i'
  rw [extCycleClassUntw_apply]
  by_cases hi : i' = i
  · subst hi
    rw [restrictChow_compPushforward_self hY, Pi.single_eq_same]
  · rw [restrictChow_compPushforward_of_ne hY (Ne.symm hi), Pi.single_eq_of_ne hi]
    exact (congrArg _ (map_zero (T.cycleClass (compAt Y i') q))).trans (map_zero _)

/-- Multiplication by `b` in the product over components acts on `Pi.single i z` through the
component `b i`: `b * Pi.single i z = Pi.single i (b i * z)`. -/
theorem mul_pi_single {X : (SmoothProjectiveScheme k).FullSubcategory} (b : T.extH X) (i : Idx X)
    (z : T.totalH (compAt X i)) : b * Pi.single i z = Pi.single i (b i * z) := by
  funext i'
  by_cases hi : i' = i
  · subst hi; simp
  · simp [Pi.single_eq_of_ne hi]

/-- **The trace equation for the pushforward of cycle classes**: for `f : X ⟶ Y` of nonempty
equidimensional schemes, `∫_Y b ∪ γ(f_*α) = ∫_X f^*b ∪ γ(α)`, by axiom (C)(b) of the classical
theory on each component. -/
theorem extTraceUntw_mul_extCycleClassUntw_pushforward
    {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) {d e : ℕ} (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y e) (p q : ℤ) (h : q = p + e - d)
    (α : codimensionChowGroup k X.obj.hom p) (b : T.extH Y)
    (hb : b ∈ T.extGrade Y (2 * d - 2 * p)) :
    T.extTraceUntw Y hY (b * T.extCycleClassUntw Y q (equidimensionalPushforward f d e p q h α)) =
      T.extTraceUntw X hX (T.extPull f b * T.extCycleClassUntw X p α) := by
  conv_lhs => rw [← sum_compPushforward_restrictChow hX.relativeDimension p α]
  simp only [map_sum, Finset.mul_sum,
    equidimensionalPushforward_compPushforward f hX.relativeDimension hY.relativeDimension,
    extCycleClassUntw_compPushforward T hY.relativeDimension, mul_pi_single, extTraceUntw_single]
  rw [extTraceUntw_apply]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Pi.mul_apply, extPull_apply, extCycleClassUntw_apply,
    ← ExternallyGradedAlgebra.lof_component_of_mem _ (T.mem_extGrade.1 hb (idxMap f c))]
  exact (T.integration_pullTotal_mul_cycleClass (resIdx f c) (T.dimension_compAt hX c)
    (T.dimension_compAt hY (idxMap f c)) p q h _ _).symm

/-- The twisted pairing of `T.toWeilData` on `X` sends `a` and `b` to the untwisted trace of the
product of their coordinates `T.twCoord X i s a` and `T.twCoord X j t b` in `T.extH X`. -/
theorem toWeilData_pairingTw (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) (i j : ℤ) (h : i + j = 2 * d) (s t : ℤ)
    (h' : s + t = d) (a : T.toWeilData.Tw X i s) (b : T.toWeilData.Tw X j t) :
    T.toWeilData.pairingTw X d hX i j h s t h' a b =
      T.extTraceUntw X hX ((T.twCoord X i s a : T.extH X) * (T.twCoord X j t b : T.extH X)) := by
  rw [WeilData.pairingTw, LinearMap.compr₂_apply, toWeilData_trace, twistCoord_cupTw]
  rfl

/-- **Axiom (C)(b)** for the extension: `γ(f_*α) = f_*γ(α)`. -/
theorem cycleClassPushforward : T.toWeilData.CycleClassPushforward T.perfectPairing := by
  intro X Y f d e hX hY p q h α
  have := T.perfectPairing.pairingTw Y e hY (2 * d - 2 * p) (2 * q) (by omega) (d - p) q
    (by omega)
  refine (LinearMap.IsPerfPair.bijective_right (T.toWeilData.pairingTw Y e hY (2 * d - 2 * p)
    (2 * q) _ (d - p) q _)).injective (LinearMap.ext fun b ↦ ?_)
  rw [LinearMap.flip_apply, LinearMap.flip_apply, ← WeilData.pushforward_trace,
    toWeilData_pairingTw, toWeilData_pairingTw, twistCoord_pullTw, coe_pullDeg,
    coe_twistCoord_cycleClass, coe_twistCoord_cycleClass]
  exact T.extTraceUntw_mul_extCycleClassUntw_pushforward f hX hY p q h α _
    (T.twCoord Y (2 * d - 2 * p) (d - p) b).2

/-- **Axiom (C), compatibility with cycle classes**, for the extension. -/
theorem cycleClassAxiom : T.toWeilData.CycleClassAxiom T.perfectPairing :=
  ⟨T.cycleClassPullback, T.cycleClassPushforward, T.cycleClassMul, T.cycleClassPoint⟩

end ClassicalWeilCohomologyTheory

end Stacks.WeilCohomology

end
