module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionClassCodimension
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationChowBridge
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationBlockAction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Tensor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase

/-!
# The cohomology class of a correspondence

Let `W` be data (D0)–(D3) of Section 45.9 (Tag 0FHA) satisfying (A), (B) and (C), with
coefficient field `F` of characteristic zero, and let `X`, `Y` be smooth projective schemes over
`k`, `Y` of dimension `e`. A rational correspondence `c ∈ Corrʳ(X, Y) = CH_{e-r}(X × Y) ⊗ ℚ` has
a cohomology class `γ(c) ∈ H^{2c}(X × Y)` (`WeilData.corrClass`), for `c` its codimension: the
cycle class map of (D2), read in coordinates and extended to rational coefficients.

The proof of Stacks 0FHL uses four properties of these classes, each from axiom (C):

* **composition** (`traceProj_corrClass_composition`): for `X`, `Y`, `Z` nonempty and
  equidimensional, `γ(c' ∘ c) = pr₁₃,*(pr₁₂^*γ(c) ∪ pr₂₃^*γ(c'))`, in trace form: (C)(b) for
  `pr₁₃`, (C)(c) for the intersection product and (C)(a) for the flat pullbacks along `pr₁₂`,
  `pr₂₃`, whose Gysin maps are flat pullback (Stacks 0FF4);
* **classes of closed subschemes** (`traceProj_corrClass_closedSubscheme`): the class of a
  closed subscheme `Γ ⊂ X × Y`, equidimensional of the dimension of `Y`, is `Γ_*1` (Stacks
  0FHG), in trace form `∫_{X × Y} γ([Γ]) ∪ v = ∫_Γ v|_Γ`; graphs and the diagonal are such;
* **tensor products** (`corrClass_tensorBlock`): `γ(c ⊗ c') = pr₁₃^*γ(c) ∪ pr₂₄^*γ(c')`;
* **proper pushforward** (`traceProj_corrClass_pushforward`): `γ(φ_*t)` is `φ_*γ(t)`, in trace
  form, by (C)(b).

## References

* [Stacks Project, Tag 0FHL](https://stacks.math.columbia.edu/tag/0FHL)
* [Stacks Project, Tag 0FHG](https://stacks.math.columbia.edu/tag/0FHG)
* [Stacks Project, Tag 0FF4](https://stacks.math.columbia.edu/tag/0FF4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open scoped TensorProduct

universe u w

namespace Stacks.WeilCohomology.WeilData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (W : WeilData k F)

/-- The cycle class of an integral class `α` of dimension `e - r` on `X × Y`, read in
codimension `c`. -/
def corrClassInt (X Y : (SmoothProjectiveScheme k).FullSubcategory) (e r c : ℤ) :
    chowGroup (fieldChowSituation k) (pullback.fst X.obj.hom Y.obj.hom ≫ X.obj.hom) (e - r) →+
      W.H (prod X Y) :=
  (W.cycleClassRing (prod X Y) c).comp (chowGroupToCodimension (prod X Y).obj.hom (e - r) c)

omit [CharZero F] in
/-- The cycle class `γ(α)` of an integral class `α` read in codimension `c` lies in
`H^{2c}(X × Y)`. -/
theorem corrClassInt_mem (X Y : (SmoothProjectiveScheme k).FullSubcategory) (e r c : ℤ)
    (α : chowGroup (fieldChowSituation k) (pullback.fst X.obj.hom Y.obj.hom ≫ X.obj.hom) (e - r)) :
    W.corrClassInt X Y e r c α ∈ W.grade (prod X Y) (2 * c) :=
  W.cycleClassRing_mem _ _ _

/-- **The cohomology class of a rational correspondence** `t ∈ Corrʳ(X, Y) = CH_{e-r}(X × Y) ⊗ ℚ`
(`Y` of dimension `e`), read in codimension `c`: `q ⊗ α ↦ q · γ(α)` in `H^{2c}(X × Y)`, the class
`α` of dimension `e - r` being read in `CH^c(X × Y)` (`chowGroupToCodimension`). -/
def corrClass (X Y : (SmoothProjectiveScheme k).FullSubcategory) (e r c : ℤ) :
    Correspondence (fieldChowSituation k) X.obj.hom Y.obj.hom e r →+ W.H (prod X Y) :=
  (TensorProduct.lift (R := ℤ) (LinearMap.mk₂ ℤ
    (fun (q : ℚ) α ↦ (q : F) • W.corrClassInt X Y e r c α)
    (fun q q' α ↦ by rw [Rat.cast_add, add_smul]) (fun n q α ↦ by
      rw [zsmul_eq_mul, Rat.cast_mul, Rat.cast_intCast, mul_smul, Int.cast_smul_eq_zsmul])
    (fun q α α' ↦ by rw [map_add, smul_add])
    (fun n q α ↦ by rw [map_zsmul, smul_comm]))).toAddMonoidHom

/-- The class of `q ⊗ α` is `q · γ(α)`. -/
@[simp]
theorem corrClass_tmul (X Y : (SmoothProjectiveScheme k).FullSubcategory) (e r c : ℤ) (q : ℚ)
    (α : chowGroup (fieldChowSituation k) (pullback.fst X.obj.hom Y.obj.hom ≫ X.obj.hom) (e - r)) :
    W.corrClass X Y e r c (q ⊗ₜ α) = (q : F) • W.corrClassInt X Y e r c α :=
  rfl

/-- The class `γ(t)` of a rational correspondence read in codimension `c` lies in
`H^{2c}(X × Y)`. -/
theorem corrClass_mem (X Y : (SmoothProjectiveScheme k).FullSubcategory) (e r c : ℤ)
    (t : Correspondence (fieldChowSituation k) X.obj.hom Y.obj.hom e r) :
    W.corrClass X Y e r c t ∈ W.grade (prod X Y) (2 * c) := by
  induction t using TensorProduct.inductionOn with
  | tmul q α => exact Submodule.smul_mem _ _ (W.corrClassInt_mem _ _ _ _ _ _)
  | add t t' h h' => rw [map_add]; exact Submodule.add_mem _ h h'

/-- The class of a rational correspondence is `ℚ`-linear: `γ(q • t) = q · γ(t)`. -/
theorem corrClass_smul (X Y : (SmoothProjectiveScheme k).FullSubcategory) (e r c : ℤ) (q : ℚ)
    (t : Correspondence (fieldChowSituation k) X.obj.hom Y.obj.hom e r) :
    W.corrClass X Y e r c (q • t) = (q : F) • W.corrClass X Y e r c t := by
  induction t using TensorProduct.inductionOn with
  | tmul q' α =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    rw [corrClass_tmul, corrClass_tmul, Rat.cast_mul, mul_smul]
  | add t t' h h' => rw [smul_add, map_add, h, h', map_add, smul_add]

variable {W}

omit [CharZero F] in
/-- The cycle class of a class read in codimension depends on the codimension only through its
value. -/
theorem cycleClassRing_chowGroupToCodimension_congr (X : (SmoothProjectiveScheme k).FullSubcategory)
    (m : ℤ) {c c' : ℤ} (h : c = c') (x : chowGroup (fieldChowSituation k) X.obj.hom m) :
    W.cycleClassRing X c (chowGroupToCodimension X.obj.hom m c x) =
      W.cycleClassRing X c' (chowGroupToCodimension X.obj.hom m c' x) := by
  subst h
  rfl

omit [CharZero F] in
/-- The reading in codimension of a class transported along an equality of degrees. -/
theorem chowGroupToCodimension_chowGroupDegreeEquiv (X : Scheme.{u})
    (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX] {m m' : ℤ} (h : m = m') (c : ℤ)
    (x : chowGroup (fieldChowSituation k) sX m) :
    chowGroupToCodimension sX m' c (chowGroupDegreeEquiv (fieldChowSituation k) sX h x) =
      chowGroupToCodimension sX m c x := by
  subst h
  rfl

/-- Flat pullback of the class of a cycle class in codimension `c`, as a flat pullback of
Chow groups ((C)(a) in coordinates). -/
private theorem pull_cycleClassRing_chowGroupToCodimension_flat {F : Type w} [Field F]
    {W : WeilData k F} (hCa : W.CycleClassPullback)
    {P Q : (SmoothProjectiveScheme k).FullSubcategory} (f : P ⟶ Q)
    (hfl : Flat f.hom.left) {d e t : ℕ}
    (hP : RelativeDimension P.obj.hom d) (hQ : RelativeDimension Q.obj.hom e)
    (ht : RelativeDimension f.hom.left t) (htd : t + e = d) (m c : ℤ) (hm : m = e - c)
    (x : chowGroup (fieldChowSituation k) Q.obj.hom m) :
    W.pull f (W.cycleClassRing Q c (chowGroupToCodimension Q.obj.hom m c x)) =
      W.cycleClassRing P c (chowGroupToCodimension P.obj.hom (m + t) c
        (flatPullbackChow (fieldChowSituation k) P.obj.hom Q.obj.hom f.hom.left (Over.w f.hom) t
          ht m (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) x)) := by
  have := hfl
  rw [← cycleClassRing_codimensionGysin hCa f c,
    codimensionGysin_chowGroupToCodimension_of_flat' _ _ _ hP hQ ht htd m c hm]

omit [CharZero F] in
/-- **The class of a composite, on integral classes.** -/
theorem traceProj_corrClassInt_compositionInt (hA : W.PoincareDuality)
    (hC : W.CycleClassAxiom hA.perfectPairing) {X Y Z : (SmoothProjectiveScheme k).FullSubcategory}
    {d e f : ℕ} (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (hZ : IsNonemptyEquidimensional Z f)
    (α : chowGroup (fieldChowSituation k) (pullback.fst X.obj.hom Y.obj.hom ≫ X.obj.hom)
      ((e : ℤ) - 0))
    (β : chowGroup (fieldChowSituation k) (pullback.fst Y.obj.hom Z.obj.hom ≫ Y.obj.hom)
      ((f : ℤ) - 0)) (v : W.H (prod X Z)) :
    W.traceProj (prod X Z) (d + f) (isNonemptyEquidimensional_prod hX hZ)
        (W.corrClassInt X Z f (0 + 0) d
          (compositionInt k X.obj.hom Y.obj.hom Z.obj.hom (canonicalDiagonalClassFamily k)
            hX.relativeDimension hY.relativeDimension hZ.relativeDimension 0 0 α β) * v) =
      W.traceProj (prod (prod X Y) Z) (d + e + f)
        (isNonemptyEquidimensional_prod (isNonemptyEquidimensional_prod hX hY) hZ)
        (W.pull (fst (prod X Y) Z) (W.corrClassInt X Y e 0 d α) *
          W.pull (prodPr₂₃ X Y Z) (W.corrClassInt Y Z f 0 e β) * W.pull (prodPr₁₃ X Y Z) v) := by
  have hT := isNonemptyEquidimensional_prod (isNonemptyEquidimensional_prod hX hY) hZ
  have hR := isNonemptyEquidimensional_prod hX hZ
  have hN : RelativeDimension (tripleBase X.obj.hom Y.obj.hom Z.obj.hom) (f + (e + d)) :=
    relativeDimension_tripleBase k _ _ _ hX.relativeDimension hY.relativeDimension
      hZ.relativeDimension
  set μ := compositionCycle k X.obj.hom Y.obj.hom Z.obj.hom (canonicalDiagonalClassFamily k)
    hX.relativeDimension hY.relativeDimension hZ.relativeDimension 0 0 α β
  have e1 : W.corrClassInt X Z f (0 + 0) d
      (compositionInt k X.obj.hom Y.obj.hom Z.obj.hom (canonicalDiagonalClassFamily k)
        hX.relativeDimension hY.relativeDimension hZ.relativeDimension 0 0 α β) =
      W.cycleClassRing (prod X Z) d (equidimensionalPushforward (prodPr₁₃ X Y Z) (d + e + f)
        (d + f) (d + e) d (by push_cast; ring)
        (chowGroupToCodimension (tripleBase X.obj.hom Y.obj.hom Z.obj.hom) ((f : ℤ) - (0 + 0))
          (d + e) μ)) :=
    congrArg (W.cycleClassRing (prod X Z) d)
      (chowGroupToCodimension_properChowPushforward hT.relativeDimension (prodPr₁₃ X Y Z) _ _ _
        (by push_cast; ring) (by push_cast; ring) μ)
  have hpush := traceProj_mul_cycleClassRing_pushforward hA.perfectPairing hC.pushforward
    (prodPr₁₃ X Y Z) hT hR (d + e) d (by push_cast; ring)
    (chowGroupToCodimension (tripleBase X.obj.hom Y.obj.hom Z.obj.hom) ((f : ℤ) - (0 + 0))
      (d + e) μ) v
  have e2 : chowGroupToCodimension (tripleBase X.obj.hom Y.obj.hom Z.obj.hom)
      ((f : ℤ) - (0 + 0)) (d + e) μ =
      codimensionIntersectionProduct k (prod (prod X Y) Z).obj.hom d e
        (chowGroupToCodimension (tripleBase X.obj.hom Y.obj.hom Z.obj.hom) ((e : ℤ) - 0 + f) d
          (flatPullbackChow (fieldChowSituation k) (tripleBase X.obj.hom Y.obj.hom Z.obj.hom)
    (prodBase X.obj.hom Y.obj.hom) (pr₁₂ X.obj.hom Y.obj.hom Z.obj.hom)
    (pr₁₂_comp_prodBase _ _ _) f (relativeDimension_pr₁₂ k _ _ _ hZ.relativeDimension) _
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) α))
        (chowGroupToCodimension (tripleBase X.obj.hom Y.obj.hom Z.obj.hom) ((f : ℤ) - 0 + d) e
          (flatPullbackChow (fieldChowSituation k) (tripleBase X.obj.hom Y.obj.hom Z.obj.hom)
    (prodBase Y.obj.hom Z.obj.hom) (pr₂₃ X.obj.hom Y.obj.hom Z.obj.hom)
    (pr₂₃_comp_prodBase _ _ _) d (relativeDimension_pr₂₃ k _ _ _ hX.relativeDimension) _
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) β)) := by
    refine (chowGroupToCodimension_chowGroupDegreeEquiv _ _ _ _ _).trans ?_
    exact chowGroupToCodimension_selfIntersectionProduct _ hN _ _ d e
      (by push_cast; ring) (by push_cast; ring) _ _
  have hP : RelativeDimension (prodBase X.obj.hom Y.obj.hom) (d + e) :=
    (isNonemptyEquidimensional_prod hX hY).relativeDimension
  have hQ : RelativeDimension (prodBase Y.obj.hom Z.obj.hom) (e + f) :=
    (isNonemptyEquidimensional_prod hY hZ).relativeDimension
  have hT' : RelativeDimension (tripleBase X.obj.hom Y.obj.hom Z.obj.hom) (d + e + f) :=
    hT.relativeDimension
  have key : W.cycleClassRing (prod (prod X Y) Z) (d + e)
      (chowGroupToCodimension (tripleBase X.obj.hom Y.obj.hom Z.obj.hom) ((f : ℤ) - (0 + 0))
        (d + e) μ) =
      W.pull (fst (prod X Y) Z) (W.corrClassInt X Y e 0 d α) *
        W.pull (prodPr₂₃ X Y Z) (W.corrClassInt Y Z f 0 e β) := by
    rw [e2]
    refine (cycleClassRing_mul hC.mul (prod (prod X Y) Z) d e _ _).trans ?_
    exact congrArg₂ (· * ·)
      (pull_cycleClassRing_chowGroupToCodimension_flat hC.pullback (fst (prod X Y) Z)
        (inferInstanceAs (Flat (pr₁₂ X.obj.hom Y.obj.hom Z.obj.hom))) hT' hP
        (relativeDimension_pr₁₂ k _ _ _ hZ.relativeDimension) (by ring) ((e : ℤ) - 0) d
        (by push_cast; ring) α).symm
      (pull_cycleClassRing_chowGroupToCodimension_flat hC.pullback (prodPr₂₃ X Y Z)
        (inferInstanceAs (Flat (pr₂₃ X.obj.hom Y.obj.hom Z.obj.hom))) hT' hQ
        (relativeDimension_pr₂₃ k _ _ _ hX.relativeDimension) (by ring) ((f : ℤ) - 0) e
        (by push_cast; ring) β).symm
  have hAB : W.pull (fst (prod X Y) Z) (W.corrClassInt X Y e 0 d α) *
      W.pull (prodPr₂₃ X Y Z) (W.corrClassInt Y Z f 0 e β) ∈
      W.grade (prod (prod X Y) Z) (2 * ((d : ℤ) + e)) := by
    have := SetLike.GradedMul.mul_mem
      (W.pull_grade (fst (prod X Y) Z) _ _ (W.corrClassInt_mem X Y e 0 d α))
      (W.pull_grade (prodPr₂₃ X Y Z) _ _ (W.corrClassInt_mem Y Z f 0 e β))
    rwa [show (2 : ℤ) * d + 2 * e = 2 * (d + e) by ring] at this
  rw [mul_comm_of_mem_grade_two_mul (W.corrClassInt_mem _ _ _ _ _ _), e1, hpush, key,
    mul_comm_of_mem_grade_two_mul hAB]

/-- **The class of a composite** (the steps of the proof of Stacks 0FHL using (C)(a), (C)(b),
(C)(c)): for `X`, `Y`, `Z` nonempty and equidimensional of dimensions `d`, `e`, `f` and
correspondences `c ∈ Corr⁰(X, Y)`, `c' ∈ Corr⁰(Y, Z)`,
`∫_{X × Z} γ(c' ∘ c) ∪ v = ∫_{X × Y × Z} pr₁₂^*γ(c) ∪ pr₂₃^*γ(c') ∪ pr₁₃^*v`, the trace form of
`γ(c' ∘ c) = pr₁₃,*(pr₁₂^*γ(c) ∪ pr₂₃^*γ(c'))`. -/
theorem traceProj_corrClass_composition (hA : W.PoincareDuality)
    (hC : W.CycleClassAxiom hA.perfectPairing) {X Y Z : (SmoothProjectiveScheme k).FullSubcategory}
    {d e f : ℕ} (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (hZ : IsNonemptyEquidimensional Z f)
    (c : Correspondence (fieldChowSituation k) X.obj.hom Y.obj.hom e 0)
    (c' : Correspondence (fieldChowSituation k) Y.obj.hom Z.obj.hom f 0) (v : W.H (prod X Z)) :
    W.traceProj (prod X Z) (d + f) (isNonemptyEquidimensional_prod hX hZ)
        (W.corrClass X Z f (0 + 0) d
          (composition k X.obj.hom Y.obj.hom Z.obj.hom (canonicalDiagonalClassFamily k)
            hX.relativeDimension hY.relativeDimension hZ.relativeDimension 0 0 c c') * v) =
      W.traceProj (prod (prod X Y) Z) (d + e + f)
        (isNonemptyEquidimensional_prod (isNonemptyEquidimensional_prod hX hY) hZ)
        (W.pull (fst (prod X Y) Z) (W.corrClass X Y e 0 d c) *
          W.pull (prodPr₂₃ X Y Z) (W.corrClass Y Z f 0 e c') * W.pull (prodPr₁₃ X Y Z) v) := by
  induction c using TensorProduct.inductionOn with
  | add c₁ c₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, add_mul, h₁, h₂]
  | tmul q α =>
    induction c' using TensorProduct.inductionOn with
    | add c₁ c₂ h₁ h₂ => simp only [map_add, mul_add, add_mul, h₁, h₂]
    | tmul q' β =>
      rw [composition_tmul, corrClass_tmul, corrClass_tmul, corrClass_tmul]
      simp only [smul_mul_assoc, mul_smul_comm, map_smul, Rat.cast_mul, mul_smul]
      rw [traceProj_corrClassInt_compositionInt hA hC hX hY hZ α β v, smul_comm (q : F)]

/-- **The class of a closed subscheme of a product** (Stacks 0FHG in trace form): for `X`, `Y`
nonempty and equidimensional of dimensions `d`, `e` and a closed immersion `Γ : T ⟶ X × Y` with
`T` nonempty and equidimensional of dimension `e`, the correspondence `[Γ] ∈ Corr⁰(X, Y)`
satisfies `∫_{X × Y} γ([Γ]) ∪ v = ∫_T Γ^*v`. -/
theorem traceProj_corrClass_closedSubscheme (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) {X Y T : (SmoothProjectiveScheme k).FullSubcategory}
    {d e : ℕ} (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
    (hT : IsNonemptyEquidimensional T e) (Γ : T ⟶ prod X Y) [IsClosedImmersion Γ.hom.left]
    (v : W.H (prod X Y)) :
    W.traceProj (prod X Y) (d + e) (isNonemptyEquidimensional_prod hX hY)
        (W.corrClass X Y e 0 d ((1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) (prod X Y).obj.hom Γ.hom.left
            ((e : ℤ) - 0))) * v) =
      W.traceProj T e hT (W.pull Γ v) := by
  have hXY := isNonemptyEquidimensional_prod hX hY
  have hΓ : RelativeDimension (Γ.hom.left ≫ (prod X Y).obj.hom) e :=
    relativeDimension_of_eq (Over.w Γ.hom).symm hT.relativeDimension
  have hcl : W.corrClass X Y e 0 d ((1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) (prod X Y).obj.hom Γ.hom.left
        ((e : ℤ) - 0))) =
      (W.twCoord _ (2 * (d : ℤ)) d (W.pushforward hA.perfectPairing Γ hT hXY 0 0 (2 * d) d
        (by push_cast; ring) (by push_cast; ring) (W.unitTw T 0 0 rfl)) : W.H (prod X Y)) := by
    rw [corrClass_tmul, Rat.cast_one, one_smul]
    change W.cycleClassRing (prod X Y) d (chowGroupToCodimension (prod X Y).obj.hom ((e : ℤ) - 0) d
      (QuotientAddGroup.mk _)) = _
    rw [chowGroupToCodimension_mk_cycleAssociatedToClosedSubscheme _ _ hΓ _ _ (sub_zero _),
      cycleClassRing_apply, W.cycleClass_closedSubschemeClass_eq_pushforward_one hA hB hC Γ hT hXY
        d (by push_cast; ring)]
  rw [hcl]
  induction v using DirectSum.Decomposition.inductionOn (W.grade _) with
  | zero => simp
  | add v v' h h' => rw [mul_add, map_add, h, h', map_add, map_add]
  | @homogeneous m v =>
    obtain ⟨v, hvm⟩ := v
    change W.traceProj _ _ _ (_ * v) = W.traceProj T e hT (W.pull Γ v)
    by_cases hm : m = 2 * e
    · subst hm
      have h := pushforward_trace' hA.perfectPairing Γ hT hXY 0 0 (2 * d) d (by push_cast; ring)
        (by push_cast; ring) (2 * e) e (by ring) (by ring) (by push_cast; ring)
        (by push_cast; ring) ((W.twCoord _ (2 * (e : ℤ)) e).symm ⟨v, hvm⟩) (W.unitTw T 0 0 rfl)
      rw [pairingTw_eq_traceProj, pairingTw_eq_traceProj, twCoord_pullTw, coe_pullDeg,
        LinearEquiv.apply_symm_apply, coe_twCoord_unitTw, mul_one] at h
      rw [h, mul_comm_of_mem_grade_two_mul (W.twCoord _ (2 * (d : ℤ)) d _).2]
    · rw [W.traceProj_of_mem_ne T e hT (W.pull_grade Γ m v hvm) hm,
        W.traceProj_of_mem_ne _ _ hXY (SetLike.GradedMul.mul_mem
          (W.twCoord _ (2 * (d : ℤ)) d _).2 hvm) (by push_cast; omega)]

omit [CharZero F] in
/-- **The class of a tensor product, on integral classes.** -/
theorem corrClassInt_tensorInt (hA : W.PoincareDuality)
    (hC : W.CycleClassAxiom hA.perfectPairing)
    {X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory}
    {d d' e e' : ℕ} (hX : IsNonemptyEquidimensional X d) (hX' : IsNonemptyEquidimensional X' d')
    (hY : IsNonemptyEquidimensional Y e) (hY' : IsNonemptyEquidimensional Y' e')
    (α : chowGroup (fieldChowSituation k) (pullback.fst X.obj.hom Y.obj.hom ≫ X.obj.hom)
      ((e : ℤ) - 0))
    (β : chowGroup (fieldChowSituation k) (pullback.fst X'.obj.hom Y'.obj.hom ≫ X'.obj.hom)
      ((e' : ℤ) - 0)) :
    W.corrClassInt (prod X X') (prod Y Y') ((e + e' : ℕ) : ℤ) (0 + 0) ((d + d' : ℕ) : ℤ)
        (tensorInt k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k)
          hX.relativeDimension hX'.relativeDimension hY.relativeDimension hY'.relativeDimension
          0 0 α β) =
      W.pull (prodTensorPr₁₃ X X' Y Y') (W.corrClassInt X Y e 0 d α) *
        W.pull (prodTensorPr₂₄ X X' Y Y') (W.corrClassInt X' Y' e' 0 d' β) := by
  have hN := relativeDimension_tensorBase k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom
    hX.relativeDimension hX'.relativeDimension hY.relativeDimension hY'.relativeDimension
  have hD : RelativeDimension (tensorBase X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom)
      ((e' + d') + (d + e)) := by
    rw [show (e' + d') + (d + e) = (e' + e) + (d' + d) by ring]; exact hN
  have hD' : RelativeDimension (tensorBase X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom)
      ((e + d) + (d' + e')) := by
    rw [show (e + d) + (d' + e') = (e' + e) + (d' + d) by ring]; exact hN
  have hP : RelativeDimension (prodBase X.obj.hom Y.obj.hom) (d + e) :=
    (isNonemptyEquidimensional_prod hX hY).relativeDimension
  have hP' : RelativeDimension (prodBase X'.obj.hom Y'.obj.hom) (d' + e') :=
    (isNonemptyEquidimensional_prod hX' hY').relativeDimension
  have e2 : chowGroupToCodimension (prod (prod X X') (prod Y Y')).obj.hom
      (((e + e' : ℕ) : ℤ) - (0 + 0)) ((d : ℤ) + d')
      (tensorInt k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k)
          hX.relativeDimension hX'.relativeDimension hY.relativeDimension hY'.relativeDimension
          0 0 α β) =
      codimensionIntersectionProduct k (prod (prod X X') (prod Y Y')).obj.hom d d'
        (chowGroupToCodimension (tensorBase X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom)
          ((e : ℤ) - 0 + ((e' + d' : ℕ) : ℤ)) d
          (flatPullbackChow (fieldChowSituation k)
            (tensorBase X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom) (prodBase X.obj.hom Y.obj.hom)
            (tensorPr₁₃ X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom)
            (tensorPr₁₃_comp_prodBase _ _ _ _)
            (e' + d') (relativeDimension_tensorPr₁₃ k _ _ _ _ hX'.relativeDimension
              hY'.relativeDimension) _
            (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) α))
        (chowGroupToCodimension (tensorBase X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom)
          ((e' : ℤ) - 0 + ((e + d : ℕ) : ℤ)) d'
          (flatPullbackChow (fieldChowSituation k)
            (tensorBase X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom)
            (prodBase X'.obj.hom Y'.obj.hom)
            (tensorPr₂₄ X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom)
            (tensorPr₂₄_comp_prodBase _ _ _ _)
            (e + d) (relativeDimension_tensorPr₂₄ k _ _ _ _ hX.relativeDimension
              hY.relativeDimension) _
            (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) β)) := by
    refine (chowGroupToCodimension_chowGroupDegreeEquiv _
      (tensorBase X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom) _ _ _).trans ?_
    exact chowGroupToCodimension_selfIntersectionProduct _ hN _ _ d d'
      (by push_cast; ring) (by push_cast; ring) _ _
  refine (cycleClassRing_chowGroupToCodimension_congr (prod (prod X X') (prod Y Y')) _
    (by push_cast; rfl : ((d + d' : ℕ) : ℤ) = (d : ℤ) + d')
    (tensorInt k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k)
      hX.relativeDimension hX'.relativeDimension hY.relativeDimension hY'.relativeDimension
      0 0 α β)).trans ?_
  refine (congrArg (W.cycleClassRing _ _) e2).trans ?_
  refine (cycleClassRing_mul hC.mul (prod (prod X X') (prod Y Y')) d d' _ _).trans ?_
  exact congrArg₂ (· * ·)
    (pull_cycleClassRing_chowGroupToCodimension_flat hC.pullback (prodTensorPr₁₃ X X' Y Y')
      (inferInstanceAs (Flat (tensorPr₁₃ X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom))) hD hP
      (relativeDimension_tensorPr₁₃ k _ _ _ _ hX'.relativeDimension hY'.relativeDimension)
      (by ring) ((e : ℤ) - 0) d (by push_cast; ring) α).symm
    (pull_cycleClassRing_chowGroupToCodimension_flat hC.pullback (prodTensorPr₂₄ X X' Y Y')
      (inferInstanceAs (Flat (tensorPr₂₄ X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom))) hD' hP'
      (relativeDimension_tensorPr₂₄ k _ _ _ _ hX.relativeDimension hY.relativeDimension)
      (by ring) ((e' : ℤ) - 0) d' (by push_cast; ring) β).symm

/-- **The class of a tensor product of correspondences**: `γ(c ⊗ c') = pr₁₃^*γ(c) ∪ pr₂₄^*γ(c')`
on `(X × X') × (Y × Y')`, for `X, X', Y, Y'` nonempty and equidimensional. -/
theorem corrClass_tensorBlock (hA : W.PoincareDuality)
    (hC : W.CycleClassAxiom hA.perfectPairing)
    {X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory}
    {d d' e e' : ℕ} (hX : IsNonemptyEquidimensional X d) (hX' : IsNonemptyEquidimensional X' d')
    (hY : IsNonemptyEquidimensional Y e) (hY' : IsNonemptyEquidimensional Y' e')
    (c : Correspondence (fieldChowSituation k) X.obj.hom Y.obj.hom e 0)
    (c' : Correspondence (fieldChowSituation k) X'.obj.hom Y'.obj.hom e' 0) :
    W.corrClass (prod X X') (prod Y Y') ((e + e' : ℕ) : ℤ) (0 + 0) ((d + d' : ℕ) : ℤ)
        (tensorBlock k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom (canonicalDiagonalClassFamily k)
          hX.relativeDimension hX'.relativeDimension hY.relativeDimension hY'.relativeDimension
          0 0 c c') =
      W.pull (prodTensorPr₁₃ X X' Y Y') (W.corrClass X Y e 0 d c) *
        W.pull (prodTensorPr₂₄ X X' Y Y') (W.corrClass X' Y' e' 0 d' c') := by
  induction c using TensorProduct.inductionOn with
  | add c₁ c₂ h₁ h₂ =>
    rw [map_add (tensorBlock k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom
        (canonicalDiagonalClassFamily k) hX.relativeDimension hX'.relativeDimension
        hY.relativeDimension hY'.relativeDimension 0 0),
      LinearMap.add_apply]
    refine (map_add (W.corrClass _ _ _ _ _) _ _).trans ?_
    rw [h₁, h₂, map_add, map_add, add_mul]
  | tmul q α =>
    induction c' using TensorProduct.inductionOn with
    | add c₁ c₂ h₁ h₂ =>
      rw [map_add ((tensorBlock k X.obj.hom X'.obj.hom Y.obj.hom Y'.obj.hom
        (canonicalDiagonalClassFamily k) hX.relativeDimension hX'.relativeDimension
        hY.relativeDimension hY'.relativeDimension 0 0)
        (q ⊗ₜ α))]
      refine (map_add (W.corrClass _ _ _ _ _) _ _).trans ?_
      rw [h₁, h₂, map_add, map_add, mul_add]
    | tmul q' β =>
      rw [tensorBlock_tmul, corrClass_tmul, corrClass_tmul]
      refine (W.corrClass_tmul _ _ _ _ _ _ _).trans ?_
      rw [corrClassInt_tensorInt hA hC hX hX' hY hY' α β]
      simp only [map_smul, smul_mul_assoc, mul_smul_comm, Rat.cast_mul, mul_smul]
      exact smul_comm _ _ _

omit [CharZero F] in
/-- **The class of a proper pushforward** ((C)(b) in trace form): for a proper morphism
`φ : M ⟶ N` over `k` of nonempty schemes equidimensional of the same dimension `n`, and a
rational class `t` of dimension `m` on `M`, `∫_N γ(φ_*t) ∪ v = ∫_M γ(t) ∪ φ^*v`. -/
theorem traceProj_cycleClassRing_properChowPushforward (hA : W.PoincareDuality)
    (hC : W.CycleClassAxiom hA.perfectPairing)
    {M N : (SmoothProjectiveScheme k).FullSubcategory} {n : ℕ} (hM : IsNonemptyEquidimensional M n)
    (hN : IsNonemptyEquidimensional N n) (φ : M.obj.left ⟶ N.obj.left) [IsProper φ]
    (hφ : φ ≫ N.obj.hom = M.obj.hom) (m c : ℤ) (hc : c = n - m)
    (x : chowGroup (fieldChowSituation k) M.obj.hom m) (v : W.H N) :
    W.traceProj N n hN (W.cycleClassRing N c (chowGroupToCodimension N.obj.hom m c
        (properChowPushforward (fieldChowSituation k) M.obj.hom N.obj.hom φ hφ m
          (properPushforwardDescends _ _ _ _ _ _) x)) * v) =
      W.traceProj M n hM (W.cycleClassRing M c (chowGroupToCodimension M.obj.hom m c x) *
        W.pull (ObjectProperty.homMk (Over.homMk φ hφ)) v) := by
  obtain rfl : m = n - c := by omega
  rw [show chowGroupToCodimension N.obj.hom (n - c) c
      (properChowPushforward (fieldChowSituation k) M.obj.hom N.obj.hom φ hφ (n - c)
        (properPushforwardDescends _ _ _ _ _ _) x) = _ from
      chowGroupToCodimension_properChowPushforward hM.relativeDimension
        (ObjectProperty.homMk (Over.homMk φ hφ)) _ c c (by ring) (by ring) x,
    mul_comm_of_mem_grade_two_mul (W.cycleClassRing_mem _ _ _),
    traceProj_mul_cycleClassRing_pushforward hA.perfectPairing hC.pushforward _ hM hN c c
      (by ring),
    mul_comm_of_mem_grade_two_mul (W.cycleClassRing_mem _ _ _)]

end Stacks.WeilCohomology.WeilData

end
