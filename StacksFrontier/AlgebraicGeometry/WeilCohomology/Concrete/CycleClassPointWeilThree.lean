module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.PoincareDualityWeilThree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilChernData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CohomologyOfPoint
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DiagonalDualBasis

/-!
# Lemma 0FIM: axiom (C)(d) for data satisfying (A1)–(A7)

Let (D0), (D1), (D2') satisfy axioms (A1)–(A7) (`Stacks.WeilCohomology.WeilChernData`), and let
`WeilChernData.toWeilData` be the data of Section 0FHA they define (`γ` the cycle class map of
Tag 0FIF, `∫_X = λ` the trace map of axiom (A6)). Lemma 0FIM: axiom (C)(d) of Section 0FHA holds,
`∫_{Spec k} γ([Spec k]) = 1`.

The proof is the source's. Write `P = Spec k`. The diagonal `P ⟶ P × P` is an isomorphism, so
`[Δ] = [P × P]` and `γ([Δ]) = γ([P × P]) = 1`, the last by construction of `γ`. The Künneth
isomorphism of (A5) sends `1 ⊗ 1` to `1`, so the normalisation `(id ⊗ λ) γ([Δ]) = 1` of (A6)
reads `λ(1) · 1 = 1` in `H^*(P)`. Since `F ⟶ H^*(P)` is injective by (A5), `λ(1) = 1`; and
`γ([P]) = 1` again by construction, so `∫_P γ([P]) = λ(1) = 1`. Only (A1), (A3), (A5) and (A6)
are used.

## Main results

* `FirstChernClassData.IsCohomologicalChernCharacter.untwistTrace_point_one`:
  every `λ` normalised as in (A6) on `Spec k` sends `1` to `1`.
* `FirstChernClassData.IsCohomologicalChernCharacter.cycleClassPoint_toWeilData`:
  the axiom (C)(d) for the data of (A1), (A3), (A5), (A6).
* `Stacks.WeilCohomology.WeilChernData.cycleClassPoint`: Lemma 0FIM.

## References

* [Stacks Project, Lemma 0FIM](https://stacks.math.columbia.edu/tag/0FIM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Stacks.Chow

universe u w

namespace Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] {𝔇 : FirstChernClassData k F}
  {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((SmoothProjectiveScheme.toScheme k).obj X) →
      ∀ n : ℕ, tateTwist F 𝔇.tate (𝔇.H X) n}
  (h : 𝔇.IsCohomologicalChernCharacter ch) (hA1 : 𝔇.CoproductAxiom)
  (hA3 : 𝔇.ProjectiveBundleAxiom) (hA5 : 𝔇.KunnethAxiom)
  (hA6 : 𝔇.TraceAxiomFor hA5 h.codimensionCycleClass)

/-- The diagonal of `Spec k` is an isomorphism of schemes. -/
instance isIso_diag_point_hom_left : IsIso (diag (point k)).hom.left :=
  ⟨⟨(fst (point k) (point k)).hom.left, congrArg (fun f ↦ f.hom.left) (diag_fst_point (k := k)),
    congrArg (fun f ↦ f.hom.left) (fst_diag_point (k := k))⟩⟩

/-- **`[Δ] = [Spec k × Spec k]`**: the diagonal of `Spec k` is an isomorphism. -/
theorem diagonalClass_point :
    diagonalClass (point k) 0 = fundamentalClass (prod (point k) (point k)) :=
  WeilData.closedSubschemeClass_of_isIso (diag (point k))
    (isNonemptyEquidimensional_prod isNonemptyEquidimensional_point
      isNonemptyEquidimensional_point).relativeDimension

/-- **A trace map `λ` of (A6) on `Spec k` sends `1` to `1`**: for every `F`-linear
`λ : H^0(Spec k)(0) ⟶ F` with `(id ⊗ λ) γ([Δ]) = 1`, `λ(1) = 1`. -/
theorem untwistTrace_point_one
    (lam : tateTwist F 𝔇.tate (𝔇.grade (point k) (2 * ((0 : ℕ) : ℤ))) (0 : ℕ) →ₗ[F] F)
    (hlam : 𝔇.traceContract hA5 (point k) 0 lam
      (h.codimensionCycleClass (prod (point k) (point k)) 0 (diagonalClass (point k) 0)) = 1) :
    𝔇.untwistTrace (point k) 0 lam 1 = 1 := by
  rw [diagonalClass_point, h.codimensionCycleClass_fundamentalClass] at hlam
  have hk : (𝔇.kunnethEquiv hA5 (point k) (point k)).symm 1 = (1 : 𝔇.H (point k)) ⊗ₜ 1 := by
    rw [LinearEquiv.symm_apply_eq]
    simp [kunnethEquiv]
  simp only [traceContract, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at hlam
  rw [show 𝔇.κ (prod (point k) (point k)) ((0 : ℕ) : ℤ) (𝔇.unitTw _) = 1 from 𝔇.κ_unitTw _,
    hk, DiagonalExpansion.contractRight_tmul] at hlam
  refine hA5.1.1 ?_
  rwa [Algebra.linearMap_apply, Algebra.linearMap_apply, (algebraMap F (𝔇.H (point k))).map_one,
    Algebra.algebraMap_eq_smul_one]

/-- **Stacks 0FIM**, for the data `toWeilData`: axiom (C)(d), `∫_{Spec k} γ([Spec k]) = 1`, with
`γ` the cycle class map of Tag 0FIF and `∫ = λ` the trace map of axiom (A6). -/
theorem cycleClassPoint_toWeilData : (h.toWeilData hA1 hA3 hA5 hA6).CycleClassPoint := by
  refine Eq.trans ?_ (h.untwistTrace_point_one hA5 _
    (h.traceContract_toWeilData_trace hA1 hA3 hA5 hA6 (point k) 0 isNonemptyEquidimensional_point))
  refine congrArg ((h.toWeilData hA1 hA3 hA5 hA6).trace (point k) 0
    isNonemptyEquidimensional_point) ?_
  show h.cycleClassGrade hA1 hA3 (point k) 0 (fundamentalClass (point k)) =
    (tateTwistCoordinates 𝔇.coord ((0 : ℕ) : ℤ)).symm
      (𝔇.projGrade (point k) (2 * ((0 : ℕ) : ℤ)) 1)
  rw [cycleClassGrade, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  congr 1
  refine Subtype.ext ?_
  rw [coe_projGrade, DirectSum.decompose_of_mem_same _
    (by simpa using SetLike.GradedOne.one_mem (A := 𝔇.grade (point k)))]
  show 𝔇.κ (point k) ((0 : ℕ) : ℤ)
    (h.codimensionCycleClass (point k) 0 (fundamentalClass (point k))) = 1
  rw [h.codimensionCycleClass_fundamentalClass]
  exact 𝔇.κ_unitTw _

end Stacks.WeilCohomology.FirstChernClassData.IsCohomologicalChernCharacter

namespace Stacks.WeilCohomology.WeilChernData

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (𝔚 : WeilChernData k F)

/-- **Stacks Project, Lemma 0FIM.** Assume given data (D0), (D1) and (D2') satisfying axioms
(A1)–(A7). Then axiom (C)(d) of Section 0FHA holds for the data of Section 0FHA they define:
`∫_{Spec k} γ([Spec k]) = 1`, where `γ` is the cycle class map of Tag 0FIF and `∫ = λ` is the
trace map of axiom (A6). -/
@[stacks 0FIM]
theorem cycleClassPoint : 𝔚.toWeilData.CycleClassPoint :=
  𝔚.isCohomologicalChernCharacter.cycleClassPoint_toWeilData 𝔚.coproduct 𝔚.projectiveBundle
    𝔚.kunneth 𝔚.trace

end Stacks.WeilCohomology.WeilChernData

end
