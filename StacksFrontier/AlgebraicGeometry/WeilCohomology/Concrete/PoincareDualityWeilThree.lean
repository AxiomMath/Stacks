module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TraceUniqueness

/-!
# Lemma 0FIJ: axiom (A) for data satisfying (A1)–(A7)

Let (D0), (D1), (D2') satisfy axioms (A1)–(A7), with `γ` the cycle class map of Tag 0FIF. They
define data of the shape of Section 0FHA (`Stacks.WeilCohomology.WeilData`): the same `F(1)`,
`H^*` and pullbacks, the cycle class map `γ` read in `H^{2i}(X)(i)`, and the trace map
`∫_X = λ` of axiom (A6), unique by Remark 0FIK. Lemma 0FIJ: these data satisfy axiom (A),
Poincaré duality.

The proof is the source's: `H^*(X)(d)[2d]` is a left dual of `H^*(X)` with coevaluation
`γ([Δ])` and evaluation `λ ∘ Δ^*`, the triangle identity resting on
`γ([Δ]) ∪ p₁^*a = γ([Δ]) ∪ p₂^*a` (`key_diagonalClass`). The linear algebra
(`Stacks.WeilCohomology.DiagonalExpansion`) extracts from this the finite dimensionality of
`H^*(X)` and the perfectness of `(a, b) ↦ λ(a ∪ b)` directly, which is axiom (A).

In namespace `Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter`:

## Main definitions

* `toWeilData`.

## Main results

* `poincareDuality_toWeilData`: Lemma 0FIJ.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] {𝔇 : FirstChernClassData k F}
  {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((SmoothProjectiveScheme.toScheme k).obj X) →
      ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
  (h : 𝔇.IsCohomologicalChernCharacter ch) (hA1 : 𝔇.CoproductAxiom)
  (hA3 : 𝔇.ProjectiveBundleAxiom)

include hA1 hA3 in
/-- `κ(γ(a)) ∈ H^{2n}(X)` for `a ∈ CH^n(X)`. -/
theorem κ_codimensionCycleClass_mem (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℕ)
    (a : codimensionChowGroup k X.obj.hom n) :
    𝔇.κ X n (h.codimensionCycleClass X n a) ∈ 𝔇.grade X (2 * (n : ℤ)) := by
  obtain ⟨y, hy⟩ := h.codimensionCycleClass_mem hA1 hA3 X n a
  rw [← hy, κ, tateTwistCoordinates_map]
  exact Submodule.coe_mem _

/-- The cycle class map `γ : CH^n(X) ⟶ H^{2n}(X)(n)`, with values in the twist of the degree-`2n`
part. -/
def cycleClassGrade (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℕ) :
    codimensionChowGroup k X.obj.hom n →+ tateTwist F 𝔇.tate (𝔇.grade X (2 * (n : ℤ))) n where
  toFun a := (tateTwistCoordinates 𝔇.coord (n : ℤ)).symm
    ⟨𝔇.κ X n (h.codimensionCycleClass X n a), h.κ_codimensionCycleClass_mem hA1 hA3 X n a⟩
  map_zero' := by
    rw [← map_zero (tateTwistCoordinates (V := 𝔇.grade X (2 * (n : ℤ))) 𝔇.coord (n : ℤ)).symm]
    congr 1
    exact Subtype.ext (by simp)
  map_add' a b := by
    rw [← map_add]
    congr 1
    exact Subtype.ext (by simp)

/-- The image of `cycleClassGrade` in `H^*(X)(n)` is `γ`. -/
theorem tateTwistMap_cycleClassGrade (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℕ)
    (a : codimensionChowGroup k X.obj.hom n) :
    tateTwistMap (𝔇.grade X (2 * (n : ℤ))).subtype n (h.cycleClassGrade hA1 hA3 X n a) =
      h.codimensionCycleClass X n a := by
  refine (𝔇.κ X n).injective ?_
  rw [κ, tateTwistCoordinates_map, cycleClassGrade, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    LinearEquiv.apply_symm_apply]
  rfl

variable (hA5 : 𝔇.KunnethAxiom) (hA6 : 𝔇.TraceAxiomFor hA5 h.codimensionCycleClass)

/-- **The data of Section 0FHA defined by (D0), (D1), (D2') satisfying (A1)–(A6)**: `F(1)`,
`H^*` and the pullbacks of the data, the cycle class map `γ` of Tag 0FIF (zero in negative
codimension, where the Chow groups vanish), and the trace map `∫_X = λ` of axiom (A6), unique by
Remark 0FIK (`trace_unique`). -/
def toWeilData : WeilData k F where
  tate := 𝔇.tate
  finrank_tate := 𝔇.finrank_tate
  H := 𝔇.H
  grade := 𝔇.grade
  graded_comm := 𝔇.graded_comm
  pull := 𝔇.pull
  pull_id := 𝔇.pull_id
  pull_comp := 𝔇.pull_comp
  pull_grade := 𝔇.pull_grade
  cycleClass X i := match i with
    | Int.ofNat n => h.cycleClassGrade hA1 hA3 X n
    | Int.negSucc _ => 0
  trace X d hX := (hA6 X d hX).choose

/-- The trace map of `toWeilData` is a trace map of axiom (A6). -/
theorem traceContract_toWeilData_trace (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) :
    𝔇.traceContract hA5 X d ((h.toWeilData hA1 hA3 hA5 hA6).trace X d hX)
      (h.codimensionCycleClass (prod X X) d (diagonalClass X d)) = 1 :=
  (hA6 X d hX).choose_spec

/-- The cycle class map of `toWeilData` is `γ`. -/
theorem tateTwistMap_toWeilData_cycleClass (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℕ)
    (a : codimensionChowGroup k X.obj.hom n) :
    tateTwistMap (𝔇.grade X (2 * (n : ℤ))).subtype n
        ((h.toWeilData hA1 hA3 hA5 hA6).cycleClass X n a) =
      h.codimensionCycleClass X n a :=
  h.tateTwistMap_cycleClassGrade hA1 hA3 X n a

variable (hA4 : 𝔇.DivisorAxiom) (hA7 : 𝔇.BlowupAxiom)

include hA4 hA7 in
/-- **Stacks Project, Lemma 0FIJ.** Let (D0), (D1), (D2') satisfy axioms (A1)–(A7). Then axiom
(A) of Section 0FHA holds with `∫_X = λ` as in axiom (A6): for `X` nonempty and equidimensional
of dimension `d`, `H^i(X)` is finite dimensional and `H^i(X) × H^{2d-i}(X)(d) ⟶ F`,
`(a, b) ↦ λ(a ∪ b)`, is a perfect pairing. -/
@[stacks 0FIJ "axiom (A) for the data of (A1)-(A7), with trace map λ of (A6) and γ the cycle \
class map of 0FIF"]
theorem poincareDuality_toWeilData : (h.toWeilData hA1 hA3 hA5 hA6).PoincareDuality := by
  set W := h.toWeilData hA1 hA3 hA5 hA6
  have hD : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
      (hX : IsNonemptyEquidimensional X d),
      ∃ l, DiagonalExpansion.DiagonalData (𝔇.grade X) (𝔇.grade (prod X X))
        (𝔇.pull (fst X X)) (𝔇.pull (snd X X)) (2 * (d : ℤ))
        (𝔇.untwistClass X d (h.codimensionCycleClass (prod X X) d (diagonalClass X d)))
        (𝔇.untwistTrace X d (W.trace X d hX)) l := fun X d hX ↦
    𝔇.exists_diagonalData hA5 X d _
      (𝔇.untwistClass_mem_of_mem_range X _ (h.codimensionCycleClass_mem hA1 hA3 _ _ _))
      _ (h.traceContract_toWeilData_trace hA1 hA3 hA5 hA6 X d hX)
      (h.key_diagonalClass hA1 hA3 hA4 hA7 X d hX)
  refine ⟨fun X d hX i ↦ ?_, fun X d hX i j hij ↦ ?_⟩
  · obtain ⟨l, hl⟩ := hD X d hX
    have := DiagonalExpansion.finiteDimensional hl
    exact inferInstanceAs (FiniteDimensional F (𝔇.grade X i))
  · obtain ⟨l, hl⟩ := hD X d hX
    have := DiagonalExpansion.isPerfPair_tracePairing hl (by omega : j + i = 2 * (d : ℤ))
    have heq : W.pairing X d hX i j hij =
        (DiagonalExpansion.tracePairing (𝒜 := 𝔇.grade X) (𝔇.untwistTrace X d (W.trace X d hX))
          j i).compl₁₂ (LinearEquiv.refl F (𝔇.grade X i)).toLinearMap
          (tateTwistCoordinates (V := 𝔇.grade X j) 𝔇.coord (d : ℤ)).toLinearMap := by
      refine LinearMap.ext fun a ↦ LinearMap.ext fun b ↦ ?_
      simp only [WeilData.pairing, LinearMap.compr₂_apply, untwistTrace]
      refine congrArg (W.trace X d hX) ?_
      refine (tateTwistCoordinates (V := 𝔇.grade X (2 * (d : ℤ))) 𝔇.coord (d : ℤ)).injective ?_
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      refine (tateTwistCoordinates_tateCupLeft (L := 𝔇.tate) 𝔇.coord
        (W.cup X i j (2 * (d : ℤ)) hij) (d : ℤ) a b).trans ?_
      refine Subtype.ext ?_
      rw [coe_projGrade, DirectSum.decompose_of_mem_same _
        (hij ▸ SetLike.GradedMul.mul_mem a.2 (Submodule.coe_mem _))]
      rfl
    rw [heq]
    exact LinearMap.IsPerfPair.compl₁₂ _ _ _

end Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter

end
