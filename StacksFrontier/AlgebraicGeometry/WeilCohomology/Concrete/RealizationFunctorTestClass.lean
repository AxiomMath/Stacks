module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotiveAlgebra
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationChowBridge
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationFunctorTransport
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionDecompositionBasePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The realization of the correspondences `pr₂^!β`

Let `W` be data (D0)–(D3) satisfying (A), (B), (C), let `X` be nonempty and equidimensional of
dimension `d` and `Y` nonempty and equidimensional, and let `β ∈ CH^d(Y)`. The class
`pr₂^!β ∈ CH^d(X × Y)` is a correspondence of degree `0` from `X` to `Y`
(`Stacks.WeilCohomology.pullbackCorr`), and its action `a ↦ pr₂,*(γ(pr₂^!β) ∪ pr₁^*a)` of
Stacks 0FHL on `H^{2d}(X)` is `a ↦ (∫_X a) γ(β)`
(`Stacks.WeilCohomology.WeilData.corrMap_pullbackCorr`). This is how the proof of Stacks 0FHM
recovers the trace maps and the cycle class maps from the realization of correspondences.

## Main definitions

* `Stacks.WeilCohomology.pullbackCorr`: the correspondence `pr₂^!β ∈ Corr⁰(X, Y)`.

## Main results

* `Stacks.WeilCohomology.exists_chowGroupToCodimension_eq`: on an equidimensional `X`, every
  class of `CH^c(X)` is a class of dimension `dim X - c`.
* `Stacks.WeilCohomology.WeilData.blockAct_pull_snd`: `pr₂,*(pr₂^*z ∪ pr₁^*a) = (∫_X a) z`.
* `Stacks.WeilCohomology.WeilData.corrMap_pullbackCorr`: the action of `pr₂^!β`.

## References

* [Stacks Project, Tag 0FHL](https://stacks.math.columbia.edu/tag/0FHL)
* [Stacks Project, Tag 0FHM](https://stacks.math.columbia.edu/tag/0FHM)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow MonoidalCategory

universe u w

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-- **On an equidimensional `X` of dimension `n`, every class of `CH^c(X)` is a class of dimension
`n - c`**: the pushforward of its component on `X_n`, the other parts being empty. -/
theorem exists_chowGroupToCodimension_eq {X : (SmoothProjectiveScheme k).FullSubcategory} {n : ℕ}
    (hX : AlgebraicGeometry.RelativeDimension X.obj.hom n) (c : ℤ)
    (β : codimensionChowGroup k X.obj.hom c) :
    ∃ α : chowGroup (fieldChowSituation k) X.obj.hom ((n : ℤ) - c),
      chowGroupToCodimension X.obj.hom ((n : ℤ) - c) c α = β := by
  have := (isClopenDecomposition_dimPart X.obj.hom).isProper_ι n
  refine ⟨properChowPushforward (fieldChowSituation k) (partBase X.obj.hom n) X.obj.hom
    (dimPart X.obj.hom n).ι rfl _
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _) (β n), ?_⟩
  funext e
  by_cases h : e = n
  · subst h
    rw [chowGroupToCodimension_apply_of_eq _ _ _ _ _ rfl,
      chowGroupRestrict_properChowPushforward_opens_self]
    rfl
  · have := isEmpty_dimPart_of_ne X.obj.hom hX h
    exact @Subsingleton.elim _ (subsingleton_chowGroup_of_isEmpty _ _ _) _ _

/-- Every point of an equidimensional `X` of dimension `n` lies in the part of dimension `n`. -/
private theorem mem_range_partι {X : (SmoothProjectiveScheme k).FullSubcategory} {n : ℕ}
    (hX : AlgebraicGeometry.RelativeDimension X.obj.hom n) (x : X.obj.left) :
    x ∈ Set.range (partι X n).hom.left := by
  rw [range_partι, dimPart_self_eq_top _ hX]
  trivial

/-- The part of dimension `n` of a nonempty equidimensional `X` of dimension `n` is nonempty. -/
private theorem nonempty_part_of_isNonemptyEquidimensional
    {X : (SmoothProjectiveScheme k).FullSubcategory} {n : ℕ} (hX : IsNonemptyEquidimensional X n) :
    Nonempty (part X n).obj.left := by
  obtain ⟨x⟩ := hX.nonempty
  exact nonempty_part_iff.2 ⟨x, by
    simpa only [range_partι] using mem_range_partι hX.relativeDimension x⟩

/-- The inclusion of the part of dimension `n` of an equidimensional `X` of dimension `n` is an
isomorphism. -/
theorem isIso_partι_hom_left (X : (SmoothProjectiveScheme k).FullSubcategory) {n : ℕ}
    (hX : AlgebraicGeometry.RelativeDimension X.obj.hom n) : IsIso (partι X n).hom.left := by
  have : Epi (partι X n).hom.left.base :=
    (TopCat.epi_iff_surjective _).2 fun x ↦ mem_range_partι hX x
  exact IsOpenImmersion.isIso _

/-! ### The correspondence `pr₂^!β` -/

section PullbackCorr

variable {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d m : ℕ}
    (hX : IsNonemptyEquidimensional X d)
  (hY : IsNonemptyEquidimensional Y m)

/-- The restriction `β|_{Y_m} ∈ CH^d(Y_m)` of `β ∈ CH^d(Y)` to the part of dimension `m`. -/
def pullbackCorrRestrict (β : codimensionChowGroup k Y.obj.hom d) :
    codimensionChowGroup k (part Y m).obj.hom d :=
  codimensionGysin (part Y m).obj.hom Y.obj.hom (Over.w (partι Y m).hom) d β

/-- A class of dimension `m - d` on `Y_m` whose codimension reading is `β|_{Y_m}`. -/
def pullbackCorrDim (β : codimensionChowGroup k Y.obj.hom d) :
    chowGroup (fieldChowSituation k) (part Y m).obj.hom ((m : ℤ) - d) :=
  (exists_chowGroupToCodimension_eq (relativeDimension_partBase Y.obj.hom m) d
    (pullbackCorrRestrict β)).choose

/-- The codimension reading of `pullbackCorrDim β` is `β|_{Y_m}`. -/
theorem chowGroupToCodimension_pullbackCorrDim (β : codimensionChowGroup k Y.obj.hom d) :
    chowGroupToCodimension (part Y m).obj.hom ((m : ℤ) - d) d (pullbackCorrDim β) =
      pullbackCorrRestrict β :=
  (exists_chowGroupToCodimension_eq (relativeDimension_partBase Y.obj.hom m) d
    (pullbackCorrRestrict β)).choose_spec

/-- The relative dimension of `pr₂ : X_d × Y_m ⟶ Y_m` is `d`. -/
theorem relativeDimension_snd_part :
    AlgebraicGeometry.RelativeDimension (snd (part X d) (part Y m)).hom.left d :=
  relativeDimension_pullbackSnd (part X d).obj.hom (relativeDimension_partBase X.obj.hom d)
    (part Y m).obj.hom

/-- The projection `pr₂ : X_d × Y_m ⟶ Y_m` is flat. -/
instance : Flat (snd (part X d) (part Y m)).hom.left :=
  inferInstanceAs (Flat (Limits.pullback.snd (part X d).obj.hom (part Y m).obj.hom))

/-- The block `pr₂^*(β|_{Y_m}) ∈ CH_m(X_d × Y_m) ⊗ ℚ` of `pr₂^!β`. -/
def pullbackBlock (β : codimensionChowGroup k Y.obj.hom d) :
    Correspondence (fieldChowSituation k) (part X d).obj.hom (part Y m).obj.hom m 0 :=
  (1 : ℚ) ⊗ₜ[ℤ] chowGroupDegreeEquiv _ _ (by ring)
    (flatPullbackChow (fieldChowSituation k) (prod (part X d) (part Y m)).obj.hom
      (part Y m).obj.hom (snd (part X d) (part Y m)).hom.left (Over.w (snd _ _).hom) d
      relativeDimension_snd_part ((m : ℤ) - d)
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
      (pullbackCorrDim β))

/-- **The correspondence `pr₂^!β ∈ Corr⁰(X, Y)`** for `X` equidimensional of dimension `d`,
`Y` equidimensional of dimension `m` and `β ∈ CH^d(Y)`: its only block is the class
`pr₂^*(β|_{Y_m})` on `X_d × Y_m`. -/
def pullbackCorr (β : codimensionChowGroup k Y.obj.hom d) : Corr k X.obj.hom Y.obj.hom 0 :=
  DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ m
    ((WeilData.blockEquiv X Y d m 0).symm (pullbackBlock (X := X) (m := m) β)))

end PullbackCorr

/-- A morphism of smooth projective schemes which is an isomorphism of schemes is an
isomorphism. -/
theorem isIso_of_isIso_hom_left {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y)
    [IsIso f.hom.left] : IsIso f := by
  have : IsIso ((Over.forget _).map f.hom) := inferInstanceAs (IsIso f.hom.left)
  have : IsIso f.hom := isIso_of_reflects_iso f.hom (Over.forget _)
  have : IsIso ((ObjectProperty.ι _).map f) := inferInstanceAs (IsIso f.hom)
  exact isIso_of_reflects_iso f (ObjectProperty.ι _)

/-- The tensor product of two morphisms which are isomorphisms of schemes is one. -/
instance isIso_tensorHom_hom_left {X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X' ⟶ X) (g : Y' ⟶ Y) [IsIso f.hom.left] [IsIso g.hom.left] : IsIso (f ⊗ₘ g).hom.left := by
  have := isIso_of_isIso_hom_left f
  have := isIso_of_isIso_hom_left g
  exact inferInstanceAs (IsIso ((ObjectProperty.ι _ ⋙ Over.forget _).map (f ⊗ₘ g)))

/-- The product of two morphisms which are isomorphisms of schemes is one. -/
instance isIso_prodMap_hom_left {X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X' ⟶ X)
    (g : Y' ⟶ Y) [IsIso f.hom.left] [IsIso g.hom.left] : IsIso (prodMap f g).hom.left :=
  isIso_tensorHom_hom_left f g

namespace WeilData

variable {F : Type w} [Field F] [CharZero F] {W : WeilData k F}

omit [CharZero F] in
/-- **`pr₂,*(pr₂^*z ∪ pr₁^*a) = (∫_X a) z`** for `z ∈ H^{2d}(Y)` and `a ∈ H^{2d}(X)`, `X` of
dimension `d`: the trace equation, Poincaré duality on `Y` and the Künneth formula for traces. -/
theorem blockAct_pull_snd (hA : W.PerfectPairing) (hK : W.KunnethTrace)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d m : ℕ}
    (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y m) {z : W.H Y} (hz : z ∈ W.grade Y (2 * (d : ℤ)))
    (a : W.grade X (2 * (d : ℤ))) :
    (W.blockAct hA hX hY (W.pull (snd X Y) z) (2 * d) a : W.H Y) =
      W.traceProj X d hX a • z := by
  have h := (eq_blockAct_iff hA hX hY (W.pull (snd X Y) z) a
    ⟨W.traceProj X d hX a • z, Submodule.smul_mem _ _ hz⟩).2 fun b ↦ by
    rw [mul_comm_of_mem_grade_two_mul (W.pull_grade _ _ _ hz), mul_assoc, ← map_mul,
      traceProj_pull_fst_mul_pull_snd hK hX hY, smul_mul_assoc, map_smul, smul_eq_mul]
  exact congrArg Subtype.val h.symm

omit [CharZero F] in
/-- **The action of an exterior product**:
`pr₂,*((pr₁^*x ∪ pr₂^*y) ∪ pr₁^*a) = (-1)^i (∫_X x ∪ a) y` for `y ∈ H^i(Y)`, `a ∈ H^i(X)`. -/
theorem blockAct_pull_fst_mul_pull_snd (hA : W.PerfectPairing) (hK : W.KunnethTrace)
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d m : ℕ}
    (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y m) (x : W.H X) {i : ℤ} {y : W.H Y}
    (hy : y ∈ W.grade Y i) (a : W.grade X i) :
    (W.blockAct hA hX hY (W.pull (fst X Y) x * W.pull (snd X Y) y) i a : W.H Y) =
      ((i * i).negOnePow : ℤ) • (W.traceProj X d hX (x * a) • y) := by
  have hmem : ((i * i).negOnePow : ℤ) • (W.traceProj X d hX (x * a) • y) ∈ W.grade Y i :=
    Submodule.smul_of_tower_mem _ _ (Submodule.smul_mem _ _ hy)
  have h := (eq_blockAct_iff hA hX hY (W.pull (fst X Y) x * W.pull (snd X Y) y) a
    ⟨_, hmem⟩).2 fun b ↦ by
    rw [show W.pull (fst X Y) x * W.pull (snd X Y) y *
        W.pull (fst X Y) (a : W.H X) * W.pull (snd X Y) (b : W.H Y) =
        W.pull (fst X Y) x * W.pull (snd X Y) y *
          (W.pull (fst X Y) (a : W.H X) * W.pull (snd X Y) (b : W.H Y)) by
      rw [mul_assoc (W.pull (fst X Y) x * W.pull (snd X Y) y)],
      pull_fst_mul_pull_snd_mul X Y x hy a.2, map_zsmul,
      traceProj_pull_fst_mul_pull_snd hK hX hY]
    simp only [smul_mul_assoc, map_zsmul, map_smul, smul_eq_mul]
  exact congrArg Subtype.val h.symm

omit [CharZero F] in
/-- **The action of a class is invariant under isomorphisms**: for isomorphisms `φ : X' ≅ X`
and `ψ : Y' ≅ Y`, `pr₂,*((φ × ψ)^*z ∪ pr₁^*φ^*a) = ψ^* pr₂,*(z ∪ pr₁^*a)`. -/
theorem blockAct_pull_of_isIso (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing)
    {X X' Y Y' : (SmoothProjectiveScheme k).FullSubcategory}
    {d e : ℕ} (φ : X' ⟶ X) (ψ : Y' ⟶ Y) [IsIso φ.hom.left] [IsIso ψ.hom.left]
    (hX : IsNonemptyEquidimensional X d) (hX' : IsNonemptyEquidimensional X' d)
    (hY : IsNonemptyEquidimensional Y e) (hY' : IsNonemptyEquidimensional Y' e)
    (z : W.H (prod X Y)) (i : ℤ) (a : W.grade X i) :
    W.blockAct hA.perfectPairing hX' hY' (W.pull (prodMap φ ψ) z) i (W.pullDeg φ i a) =
      W.pullDeg ψ i (W.blockAct hA.perfectPairing hX hY z i a) := by
  refine ((eq_blockAct_iff hA.perfectPairing hX' hY' _ _ _).2 fun b' ↦ ?_).symm
  have := isIso_of_isIso_hom_left ψ
  obtain ⟨b, rfl⟩ : ∃ b : W.grade Y (2 * e - i), W.pullDeg ψ _ b = b' :=
    ⟨W.pullDeg (inv ψ) _ b', Subtype.ext (by
      rw [coe_pullDeg, coe_pullDeg, pull_pull, IsIso.hom_inv_id, W.pull_id, AlgHom.id_apply])⟩
  rw [coe_pullDeg, coe_pullDeg, ← map_mul, traceProj_pull_of_isIso (hA := hA) (hB := hB)
    (hC := hC) ψ hY hY', blockAct_spec]
  have e₁ : W.pull (fst X' Y') (W.pull φ (a : W.H X)) =
      W.pull (prodMap φ ψ) (W.pull (fst X Y) (a : W.H X)) := by
    rw [pull_pull, pull_pull, prodMap_fst]
  have e₂ : W.pull (snd X' Y') (W.pull ψ (b : W.H Y)) =
      W.pull (prodMap φ ψ) (W.pull (snd X Y) (b : W.H Y)) := by
    rw [pull_pull, pull_pull, prodMap_snd]
  rw [show ((W.pullDeg φ i a : W.grade X' i) : W.H X') = W.pull φ a from rfl, e₁, e₂, ← map_mul,
    ← map_mul,
    traceProj_pull_of_isIso (hA := hA) (hB := hB) (hC := hC) (prodMap φ ψ)
      (isNonemptyEquidimensional_prod hX hY) (isNonemptyEquidimensional_prod hX' hY')]

variable (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)

/-- **The action of `pr₂^!β` on `H^{2d}(X)` is `a ↦ (∫_X a) γ(β)`**, for `X` nonempty
equidimensional of dimension `d`, `Y` nonempty equidimensional and `β ∈ CH^d(Y)`, in coordinates
of the Tate line. -/
theorem corrMap_pullbackCorr {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d m : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y m)
    (β : codimensionChowGroup k Y.obj.hom d) (a : W.grade X (2 * (d : ℤ))) :
    (corrMap hA hB hC X Y 0 (2 * d) (pullbackCorr (X := X) (m := m) β) a : W.H Y) =
      W.traceCoord X d hX a • (W.cycleClassCoord Y d β : W.H Y) := by
  have hXd := nonempty_part_of_isNonemptyEquidimensional hX
  have hYm := nonempty_part_of_isNonemptyEquidimensional hY
  have := isIso_partι_hom_left X hX.relativeDimension
  have hXd' := isNonemptyEquidimensional_part X hXd
  have hYm' := isNonemptyEquidimensional_part Y hYm
  have e₁ : chowGroupToCodimension (prod (part X d) (part Y m)).obj.hom ((m : ℤ) - 0) d
      (chowGroupDegreeEquiv (fieldChowSituation k) (prod (part X d) (part Y m)).obj.hom
        (by ring) (flatPullbackChow (fieldChowSituation k) (prod (part X d) (part Y m)).obj.hom
          (part Y m).obj.hom (snd (part X d) (part Y m)).hom.left (Over.w (snd _ _).hom) d
          relativeDimension_snd_part ((m : ℤ) - d)
          (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
          (pullbackCorrDim β))) =
      codimensionGysin (prod (part X d) (part Y m)).obj.hom (part Y m).obj.hom
        (Over.w (snd (part X d) (part Y m)).hom) d (pullbackCorrRestrict β) := by
    rw [chowGroupToCodimension_chowGroupDegreeEquiv,
      ← codimensionGysin_chowGroupToCodimension_of_flat' (prod (part X d) (part Y m)).obj.hom
        (part Y m).obj.hom (Over.w (snd (part X d) (part Y m)).hom)
        (isNonemptyEquidimensional_prod hXd' hYm').relativeDimension
        (relativeDimension_partBase Y.obj.hom m) relativeDimension_snd_part rfl _ _ rfl,
      chowGroupToCodimension_pullbackCorrDim]
  have hcc : W.corrClass (part X d) (part Y m) m 0 d (pullbackBlock (X := X) (m := m) β) =
      W.pull (snd (part X d) (part Y m)) (W.pull (partι Y m) (W.cycleClassRing Y d β)) := by
    rw [pullbackBlock, corrClass_tmul, Rat.cast_one, one_smul]
    refine (congrArg (W.cycleClassRing (prod (part X d) (part Y m)) d) e₁).trans ?_
    rw [cycleClassRing_codimensionGysin hC.pullback, pullbackCorrRestrict,
      cycleClassRing_codimensionGysin hC.pullback]
  rw [pullbackCorr, corrMap_lof_lof, LinearEquiv.apply_symm_apply,
    blockMap_of_nonempty hA hB hC _ hXd hYm]
  simp only [LinearMap.comp_apply, coe_extendDeg]
  rw [hcc, blockAct_pull_snd hA.perfectPairing hB.kunnethTrace hXd' hYm'
      (W.pull_grade _ _ _ (W.cycleClassRing_mem Y d β)),
    map_smul, coe_pullDeg, traceProj_pull_of_isIso (hA := hA) (hB := hB) (hC := hC) _ hX,
    traceProj_eq_traceCoord]
  congr 1
  have h := sum_extendByZero_pull (hA := hA) (hB := hB) (hC := hC) ({m} : Finset ℕ)
    (fun e ↦ partι Y e) (fun y ↦ ⟨m, Finset.mem_singleton_self m, by
      rw [range_partι, dimPart_self_eq_top _ hY.relativeDimension]; trivial⟩)
    (fun s hs t ht hst ↦ absurd ((Finset.mem_singleton.1 hs).trans (Finset.mem_singleton.1 ht).symm)
      hst) (W.cycleClassRing Y d β)
  rw [Finset.sum_singleton] at h
  exact h

end WeilData

end Stacks.WeilCohomology

end
