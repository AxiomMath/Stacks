module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotiveMonoidDuality
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationFunctorTestClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationLieberman
public import StacksFrontier.CategoryTheory.GradedObject.MonoidalFunctorContraction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# A realization on a morphism of motives, from its name

Let `G : M_k ⥤ graded F-vector spaces` be a realization (side (2) of Stacks 0FHM) with data
`H^*(X) = G(h(X))` (Stacks 0FHK), and let `X`, `Y` be nonempty and equidimensional, of dimensions
`d` and `e`. By Stacks 0FGI, `h(X)(d)` is a right dual of `h(X)`, so a morphism of motives
`c : h(X) ⟶ h(Y)` is determined by its name, a morphism `𝟙 ⟶ h(X) ⊗ h(Y)(d)`. This file shows that
if the name of `c` is (the twist by `𝟏(d)` of) a class `z ∈ H^{2d}(X × Y)`, then `G(c)` is the
action `a ↦ pr₂,*(z ∪ pr₁^*a)` of `z` (`Stacks.WeilCohomology.WeilRealization.map_eq_blockAct`):
contracting with the counit, which is cup product followed by the trace, gives
`G(c)(a) = Σ ∫_X(a ∪ x_j) y_j` for `z = Σ pr₁^*x_j ∪ pr₂^*y_j`, and this is the action of `z`.
This is the core of the proof of Stacks 0FHM that the realization of Stacks 0FHL recovers `G`.

## References

* [Stacks Project, Tag 0FGI](https://stacks.math.columbia.edu/tag/0FGI)
* [Stacks Project, Tag 0FHM](https://stacks.math.columbia.edu/tag/0FHM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CategoryTheory.GradedCategory Stacks.Chow

universe u w

namespace Stacks.WeilCohomology.WeilData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] {W : WeilData k F}

/-- **The action of an exterior product off the matching degree vanishes**:
`pr₂,*((pr₁^*x ∪ pr₂^*y) ∪ pr₁^*a) = 0` for `y ∈ H^j(Y)`, `a ∈ H^i(X)`, `j ≠ i`. -/
theorem blockAct_pull_fst_mul_pull_snd_of_ne (hA : W.PerfectPairing) (hK : W.KunnethTrace)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y e) (x : W.H X) {i j : ℤ} {y : W.H Y}
    (hy : y ∈ W.grade Y j) (hij : j ≠ i) (a : W.grade X i) :
    W.blockAct hA hX hY (W.pull (fst X Y) x * W.pull (snd X Y) y) i a = 0 := by
  refine ((eq_blockAct_iff hA hX hY _ a 0).2 fun b ↦ ?_).symm
  rw [ZeroMemClass.coe_zero, zero_mul, map_zero, mul_assoc, pull_fst_mul_pull_snd_mul X Y x hy a.2,
    map_zsmul, traceProj_pull_fst_mul_pull_snd hK hX hY,
    W.traceProj_of_mem_ne Y e hY (SetLike.GradedMul.mul_mem hy b.2) (by omega), mul_zero,
    smul_zero]

end Stacks.WeilCohomology.WeilData

namespace Stacks.WeilCohomology.WeilRealization

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (G : WeilRealization k F)

section

attribute [-instance] ChowMotiveCat.monoidalCategory ChowMotiveCat.braidedCategory
  ChowMotiveCat.symmetricCategory TwistedKaroubi.monoidalCategoryStruct
  CorrespondenceCategory.monoidalCategoryStruct TwistedKaroubi.symmetricCategory

attribute [local instance] braidedTK monoidalTK

local notation "𝐎" => (GradedCompositionData.Obj.mk :
  CategoryTheory.ObjectProperty.FullSubcategory (SmoothProjectiveScheme _) →
  CorrespondenceCategory _)

/-- The isomorphism `κ : h(X) ⊗ h(Y) ⟶ h(X × Y)`, `x ⊗ y ↦ pr₁^*x · pr₂^*y`. -/
abbrev kunnethMot (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ⊗ TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y) ⟶
      TwistedKaroubi.ofObj (R := ℚ) (𝐎 (X ⊗ Y)) :=
  (ChowMotiveCat.motMap (CorrespondenceCategory.tensorFst X Y) ⊗ₘ
    ChowMotiveCat.motMap (CorrespondenceCategory.tensorSnd X Y)) ≫ MonObj.mul

/-- **`G(κ)(x ⊗ y) = pr₁^*x ∪ pr₂^*y`.** -/
theorem of_map_kunnethMot_gradedMul (X Y : (SmoothProjectiveScheme k).FullSubcategory) (i j : ℤ)
    (x : G.functorTK.obj (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X)) i)
    (y : G.functorTK.obj (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y)) j) :
    DirectSum.of (G.cohAlg (prod X Y)).piece (i + j)
        (G.functorTK.map (kunnethMot X Y) (i + j)
          (Functor.gradedMul G.functorTK _ _ i j (i + j) rfl x y)) =
      G.toWeilData.pull (fst X Y) (DirectSum.of (G.cohAlg X).piece i x) *
        G.toWeilData.pull (snd X Y) (DirectSum.of (G.cohAlg Y).piece j y) := by
  change _ = G.cohPull _ (DirectSum.of (G.cohAlg X).piece i x) *
    G.cohPull _ (DirectSum.of (G.cohAlg Y).piece j y)
  rw [cohPull, cohPull]
  refine Eq.trans ?_ (congrArg₂ (· * ·) (G.functorTK.cohomologyMap_of _ i x).symm
    (G.functorTK.cohomologyMap_of _ j y).symm)
  refine Eq.trans ?_ ((G.cohAlg (prod X Y)).of_mul_of _ _).symm
  congr 1
  exact (Functor.gradedMonMul_map_map _ _ i j (i + j) rfl x y).symm

/-- **The trace of a cup product in terms of `G`**: `∫_X a ∪ x = [X](a x ⊗ e_d)`. -/
theorem traceProj_mul_eq_gradedTrace {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) {p q : ℤ} (h : p + q = 2 * (d : ℤ))
    (a : G.toWeilData.grade X p) (x : G.toWeilData.grade X q) :
    G.toWeilData.traceProj X d hX ((a : G.toWeilData.H X) * x) =
      G.functorTK.gradedTrace (ChowMotiveCat.fundamentalClassMot hX.relativeDimension)
        (G.tateGen d) (2 * d) (by ring)
        (Functor.gradedMonMul G.functorTK _ p q (2 * d) h ((G.cohAlg X).gradeEquiv p a)
          ((G.cohAlg X).gradeEquiv q x)) := by
  rw [show ((a : G.toWeilData.H X) * x) =
      (G.toWeilData.cup X p q (2 * d) h a x : G.toWeilData.H X) from rfl,
    WeilData.traceProj_eq_traceCoord, toWeilData_traceCoord]
  exact congrArg (G.functorTK.gradedTrace _ _ _ _) (G.gradeEquiv_cup X p q _ h a x)

/-- The action `z ↦ pr₂,*(z ∪ pr₁^*a)` of classes on a fixed `a`, as a linear map. -/
def blockActLeft (hP : G.toWeilData.PerfectPairing)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {d e : ℕ} (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e) (n : ℤ)
    (a : G.toWeilData.grade X n) :
    G.toWeilData.H (prod X Y) →ₗ[F] G.toWeilData.grade Y n where
  toFun z := G.toWeilData.blockAct hP hX hY z n a
  map_add' z z' := by rw [WeilData.blockAct_add]; rfl
  map_smul' c z := by rw [WeilData.blockAct_smul]; rfl

/-- `blockActLeft` sends a class `z` to `pr₂,*(z ∪ pr₁^*a)`. -/
@[simp]
theorem blockActLeft_apply (hP : G.toWeilData.PerfectPairing)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {d e : ℕ} (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e) (n : ℤ)
    (a : G.toWeilData.grade X n) (z : G.toWeilData.H (prod X Y)) :
    G.blockActLeft hP hX hY n a z = G.toWeilData.blockAct hP hX hY z n a :=
  rfl

/-- The contraction of `a ⊗ e_d` with `x ⊗ (y ⊗ e_d)` is the action of `pr₁^*x ∪ pr₂^*y` on
`a`, twisted by `e_d`. -/
theorem gradedContract_gradedMul_eq_blockAct (hP : G.toWeilData.PerfectPairing)
    (hK : G.toWeilData.KunnethTrace) {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e) (n : ℤ)
    (a : G.toWeilData.grade X n) {i j : ℤ} (hl : i + j = 2 * (d : ℤ))
    (x : G.functorTK.obj (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X)) i)
    (y : G.functorTK.obj (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y)) j) :
    letI := ChowMotiveCat.exactPairingMotive hX.relativeDimension
    Functor.gradedContract G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
        (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ⊗
          TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)
        (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y) ⊗
          TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)
        (n + -2 * d)
        (Functor.gradedMul G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
          (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) n
          (-2 * d) (n + -2 * d) rfl ((G.cohAlg X).gradeEquiv n a) (G.tateGen d))
        (Functor.gradedMul G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
          (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y) ⊗
            TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)
          i (j + -2 * d) 0 (by omega) x
          (Functor.gradedMul G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y))
            (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) j
            (-2 * d) (j + -2 * d) rfl y (G.tateGen d))) =
      Functor.gradedMul G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y))
        (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) n
        (-2 * d) (n + -2 * d) rfl
        ((G.cohAlg Y).gradeEquiv n (G.toWeilData.blockAct hP hX hY
          (G.toWeilData.pull (fst X Y) (DirectSum.of (G.cohAlg X).piece i x) *
            G.toWeilData.pull (snd X Y) (DirectSum.of (G.cohAlg Y).piece j y)) n a))
        (G.tateGen d) := by
  obtain ⟨x', rfl⟩ : ∃ x' : G.toWeilData.grade X i, (G.cohAlg X).gradeEquiv i x' = x :=
    ((G.cohAlg X).gradeEquiv i).surjective x
  obtain ⟨y', rfl⟩ : ∃ y' : G.toWeilData.grade Y j, (G.cohAlg Y).gradeEquiv j y' = y :=
    ((G.cohAlg Y).gradeEquiv j).surjective y
  rw [← coe_eq_of_gradeEquiv G i x', ← coe_eq_of_gradeEquiv G j y']
  by_cases hj : j = n
  · subst hj
    let := ChowMotiveCat.exactPairingMotive hX.relativeDimension
    have hji : j + i = 2 * (d : ℤ) := by omega
    have hb : (G.cohAlg Y).gradeEquiv j (G.toWeilData.blockAct hP hX hY
        (G.toWeilData.pull (fst X Y) x'.1 * G.toWeilData.pull (snd X Y) y'.1) j a) =
        ((((j * j).negOnePow : ℤ) : F) * G.toWeilData.traceProj X d hX (x'.1 * a.1)) •
          (G.cohAlg Y).gradeEquiv j y' := by
      have h : G.toWeilData.blockAct hP hX hY
          (G.toWeilData.pull (fst X Y) x'.1 * G.toWeilData.pull (snd X Y) y'.1) j a =
          (((j * j).negOnePow : ℤ) : F) •
            (G.toWeilData.traceProj X d hX (x'.1 * a.1) • y') :=
        Subtype.ext (by
          rw [WeilData.blockAct_pull_fst_mul_pull_snd hP hK hX hY x'.1 y'.2 a, SetLike.val_smul,
            SetLike.val_smul, Int.cast_smul_eq_zsmul])
      rw [h]
      refine (((G.cohAlg Y).gradeEquiv j).map_smul _ _).trans ?_
      refine (congrArg (_ • ·) (((G.cohAlg Y).gradeEquiv j).map_smul _ _)).trans ?_
      exact smul_smul _ _ _
    have hs : G.functorTK.gradedCounit (G.functorTK.map (ε_ (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
        (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ⊗
          TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)) 0
        (Functor.gradedMul G.functorTK _ _ (j + -2 * d) i 0 (by omega)
          (Functor.gradedMul G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
            (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) j
            (-2 * d) (j + -2 * d) rfl ((G.cohAlg X).gradeEquiv j a) (G.tateGen d))
          ((G.cohAlg X).gradeEquiv i x'))) =
        (((j * j).negOnePow : ℤ) : F) * G.toWeilData.traceProj X d hX (x'.1 * a.1) := by
      refine (Functor.gradedCounit_map_evaluation_gradedMul (G := G.functorTK)
        (P := ChowMotiveCat.exactPairingMotive hX.relativeDimension) _ _
        (ChowMotiveCat.fundamentalClassMot hX.relativeDimension)
        (ChowMotiveCat.evaluation_exactPairingMotive hX.relativeDimension) ⟨-(d : ℤ), by ring⟩
        (G.tateGen d) rfl _ hji (by ring) ((G.cohAlg X).gradeEquiv j a)
        ((G.cohAlg X).gradeEquiv i x')).trans ?_
      refine (traceProj_mul_eq_gradedTrace G hX hji a x').symm.trans ?_
      rw [G.toWeilData.graded_comm X i j _ _ x'.2 a.2, map_zsmul, zsmul_eq_mul, ← mul_assoc,
        ← Int.cast_mul, ← Units.val_mul, ← Int.negOnePow_add,
        Int.negOnePow_even _ ⟨(d : ℤ) * j, by linear_combination j * hl⟩, Units.val_one,
        Int.cast_one, one_mul]
    rw [hb]
    exact (Functor.gradedContract_gradedMul (G := G.functorTK)
      (P := ChowMotiveCat.exactPairingMotive hX.relativeDimension) (by omega) _ _ _).trans
      ((congrArg (· • _) hs).trans (LinearMap.map_smul₂ _ _ _ _).symm)
  · rw [WeilData.blockAct_pull_fst_mul_pull_snd_of_ne hP hK hX hY x'.1 y'.2 hj a]
    exact (Functor.gradedContract_gradedMul_of_ne (G := G.functorTK)
      (P := ChowMotiveCat.exactPairingMotive hX.relativeDimension) _ (by omega) _ _ _).trans
      ((LinearMap.map_zero₂ _ _).symm.trans (congrArg (fun z ↦ Functor.gradedMul G.functorTK
        (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y))
        (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) n (-2 * d)
        (n + -2 * d) rfl z (G.tateGen d)) (map_zero ((G.cohAlg Y).gradeEquiv n)).symm))

/-- `gradedContract_gradedMul_eq_blockAct`, with the class written as `G(κ)(x ⊗ y)`. -/
theorem gradedContract_gradedMul_eq_blockAct_kunneth (hP : G.toWeilData.PerfectPairing)
    (hK : G.toWeilData.KunnethTrace) {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e) (n : ℤ)
    (a : G.toWeilData.grade X n) {i j : ℤ} (hl : i + j = 2 * (d : ℤ))
    (x : G.functorTK.obj (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X)) i)
    (y : G.functorTK.obj (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y)) j) :
    letI := ChowMotiveCat.exactPairingMotive hX.relativeDimension
    Functor.gradedContract G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
        (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ⊗
          TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)
        (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y) ⊗
          TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)
        (n + -2 * d)
        (Functor.gradedMul G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
          (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) n
          (-2 * d) (n + -2 * d) rfl ((G.cohAlg X).gradeEquiv n a) (G.tateGen d))
        (Functor.gradedMul G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
          (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y) ⊗
            TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)
          i (j + -2 * d) 0 (by omega) x
          (Functor.gradedMul G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y))
            (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) j
            (-2 * d) (j + -2 * d) rfl y (G.tateGen d))) =
      Functor.gradedMul G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y))
        (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) n
        (-2 * d) (n + -2 * d) rfl
        ((G.cohAlg Y).gradeEquiv n (G.toWeilData.blockAct hP hX hY
          (DirectSum.of (G.cohAlg (prod X Y)).piece (i + j)
            (G.functorTK.map (kunnethMot X Y) (i + j)
              (Functor.gradedMul G.functorTK _ _ i j (i + j) rfl x y))) n a))
        (G.tateGen d) := by
  rw [of_map_kunnethMot_gradedMul]
  exact gradedContract_gradedMul_eq_blockAct G hP hK hX hY n a hl x y

/-- **A realization on a morphism of motives whose name is a class.** Let `X`, `Y` be nonempty and
equidimensional of dimensions `d`, `e`, and `c : h(X) ⟶ h(Y)`. If the image of `1` under the name
`η ≫ h(X) ◁ (c ▷ 𝟏(d)) : 𝟙 ⟶ h(X) ⊗ h(Y)(d)` of `c ▷ 𝟏(d)` is `v ⊗ e_d` for
`v ∈ G(h(X) ⊗ h(Y))^{2d}`, then `G(c)` is the action `a ↦ pr₂,*(z ∪ pr₁^*a)` of the class
`z = G(κ)(v) ∈ H^{2d}(X × Y)`. -/
theorem map_eq_blockAct (hP : G.toWeilData.PerfectPairing) (hK : G.toWeilData.KunnethTrace)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y e)
    (c : TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ⟶ TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y)) {l : ℤ}
    (hl : l = 2 * (d : ℤ))
    (v : G.functorTK.obj (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ⊗
      TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y)) l)
    (hv : letI := ChowMotiveCat.exactPairingMotive hX.relativeDimension
      G.functorTK.map (η_ (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
          (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ⊗
            TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) ≫
        TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ◁
          (c ▷ TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)) 0
          (Functor.gradedOne G.functorTK) =
        G.functorTK.map (α_ (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
          (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y))
          (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)).hom 0
          (Functor.gradedMul G.functorTK _ _ l (-2 * d) 0 (by omega) v (G.tateGen d)))
    (n : ℤ) (a : G.toWeilData.grade X n) :
    G.functorTK.map c n ((G.cohAlg X).gradeEquiv n a) =
      (G.cohAlg Y).gradeEquiv n (G.toWeilData.blockAct hP hX hY
        (DirectSum.of (G.cohAlg (prod X Y)).piece l (G.functorTK.map (kunnethMot X Y) l v)) n
        a) := by
  let := ChowMotiveCat.exactPairingMotive hX.relativeDimension
  have hT : ∀ i, i ≠ -2 * (d : ℤ) → IsZero (G.functorTK.obj
      (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) i) :=
    fun i hi ↦ ChowMotiveCat.isZero_tate_apply G.tate_degree d i hi
  have hinj := (Functor.bijective_gradedMul_right hT (G.tateGen_ne_zero d)
    (ChowMotiveCat.finrank_tate_apply G.tate_degree d) (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y)) n
    (n + -2 * d) rfl).1
  apply hinj
  dsimp only
  refine (Functor.map_whiskerRight_gradedMul (G := G.functorTK) c
      (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) n (-2 * d)
      (n + -2 * d) rfl _ (G.tateGen d)).symm.trans ?_
  refine (Functor.map_eq_gradedContract (A := TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
    (B := TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ⊗
      TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)
    (c ▷ TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) _
    _).trans ?_
  rw [hv]
  have key : (Functor.gradedContract G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
        (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ⊗
          TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)
        (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y) ⊗
          TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)
        (n + -2 * d) (Functor.gradedMul G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
          (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) n
          (-2 * d) (n + -2 * d) rfl ((G.cohAlg X).gradeEquiv n a) (G.tateGen d))) ∘ₗ
      (G.functorTK.map (α_ (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
          (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y))
          (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)).hom
            0).hom ∘ₗ
      (Functor.gradedMul G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ⊗
        TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y))
        (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) l (-2 * d)
        0 (by omega)).flip (G.tateGen d) =
      (Functor.gradedMul G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y))
        (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) n (-2 * d)
        (n + -2 * d) rfl).flip (G.tateGen d) ∘ₗ
        ((G.cohAlg Y).gradeEquiv n).toLinearMap ∘ₗ G.blockActLeft hP hX hY n a ∘ₗ
        DirectSum.lof F ℤ (G.cohAlg (prod X Y)).piece l ∘ₗ
        (G.functorTK.map (kunnethMot X Y) l).hom := by
    refine Functor.linearMap_ext_gradedMul fun i j hij x y ↦ ?_
    subst hij
    change Functor.gradedContract G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
        (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X) ⊗
          TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)
        (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y) ⊗
          TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)
        (n + -2 * d)
        (Functor.gradedMul G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
          (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) n
          (-2 * d) (n + -2 * d) rfl
          ((G.cohAlg X).gradeEquiv n a) (G.tateGen d))
        (G.functorTK.map (α_ (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
          (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y))
          (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)).hom 0
          (Functor.gradedMul G.functorTK _
            (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d)
            (i + j) (-2 * d) 0 _
            (Functor.gradedMul G.functorTK _ _ i j (i + j) rfl x y) (G.tateGen d))) =
      Functor.gradedMul G.functorTK (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y))
        (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) n
        (-2 * d) (n + -2 * d) rfl
        ((G.cohAlg Y).gradeEquiv n (G.toWeilData.blockAct hP hX hY
          (DirectSum.of (G.cohAlg (prod X Y)).piece (i + j)
            (G.functorTK.map (kunnethMot X Y) (i + j)
              (Functor.gradedMul G.functorTK _ _ i j (i + j) rfl x y))) n a)) (G.tateGen d)
    rw [Functor.map_associator_gradedMul' (G := G.functorTK) (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))
      (TwistedKaroubi.ofObj (R := ℚ) (𝐎 Y))
      (TwistedKaroubi.tateTriple ℚ (canonicalCorrespondenceCompositionData k).Obj d) i j (-2 * d)
      (i + j) (j + -2 * d) 0 rfl rfl _ (by omega) x y (G.tateGen d)]
    exact gradedContract_gradedMul_eq_blockAct_kunneth G hP hK hX hY n a hl x y
  exact LinearMap.congr_fun key v

end

end Stacks.WeilCohomology.WeilRealization

end
