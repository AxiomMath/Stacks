module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilChernData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectionFormula
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TraceDisjointUnion
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ClosedImmersionClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassCupVanishing
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ClosedImmersionGysinPushforward

/-!
# Axiom (A) and the trace maps of (A6), and `γ(θ) ∪ γ([E]) = b^*γ([Z])`

Let data (D0), (D1), (D2') satisfy (A1)–(A7) (`Stacks.WeilCohomology.WeilChernData`), with the
data of Section 0FHA they define (`WeilChernData.toWeilData`: `γ` of Tag 0FIF and `∫_X = λ` of
(A6)). This file collects pieces of the proof of Tag 0FIT: axiom (A) for these data (Lemma 0FIJ),
the reading of the trace maps of (A6) in the coordinates of `F(1)`, and the identity
`γ(θ) ∪ γ([E]) = b^*γ([Z])` that the first relation `b^![Z] = [E] · θ` of Lemma 0FIH gives.

In the proof of Tag 0FIT, `i_*1 = γ([Y])` for a smooth divisor `Y` is axiom (A9) read through the
trace equation of the pushforward. Under (A1)–(A8) it is proved, not assumed: see
`WeilChernData.divisorTrace_of_globalSections`.

## Main results

* `Stacks.WeilCohomology.WeilChernData.poincareDuality`: axiom (A) for `toWeilData` (Tag 0FIJ).
* `Stacks.WeilCohomology.WeilChernData.untwistTrace_twCoord`: a trace map read in coordinates.
* `Stacks.WeilCohomology.WeilChernData.cupTw_cycleClass_eq_pullTw_of_heq`:
  `γ(θ) ∪ γ([E]) = b^*γ([Z])` from `b^![Z] = [E] · θ`.

## References

* [Stacks Project, Section 45.14 (Tag 0FID)](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0FIT](https://stacks.math.columbia.edu/tag/0FIT)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

namespace WeilData

variable {k : Type u} [Field k] {F : Type w} [Field F] (W : WeilData k F)

/-- A linear map `λ : H^n(X)(m) ⟶ F` read in the coordinate of `F(1)` (as
`FirstChernClassData.untwistTrace` does) and evaluated on the coordinate of a class `x` is
`λ(x)`. -/
theorem trace_twCoord_symm (X : (SmoothProjectiveScheme k).FullSubcategory) (n m : ℤ)
    (lam : W.Tw X n m →ₗ[F] F) (x : W.Tw X n m) :
    lam ((W.twCoord X n m).symm (W.twCoord X n m x)) = lam x := by
  rw [LinearEquiv.symm_apply_apply]

end WeilData

namespace WeilChernData

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (𝔚 : WeilChernData k F)

open SmoothProjectiveScheme

/-- **Axiom (A) for the data of `𝔚`** (Tag 0FIJ): `H^i(X)` is finite dimensional and the pairing
`(a, b) ↦ λ(a ∪ b)` is perfect, `λ` the trace map of (A6). -/
theorem poincareDuality : 𝔚.toWeilData.PoincareDuality :=
  𝔚.isCohomologicalChernCharacter.poincareDuality_toWeilData 𝔚.coproduct 𝔚.projectiveBundle
    𝔚.kunneth 𝔚.trace 𝔚.divisor 𝔚.blowup

/-- `untwistTrace` of the trace map `λ` of `toWeilData` on the coordinate of a class
`x ∈ H^{2d}(X)(d)` is `λ(x)`. -/
theorem untwistTrace_twCoord (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (lam : tateTwist F 𝔚.tate (𝔚.grade X (2 * (d : ℤ))) d →ₗ[F] F)
    (x : 𝔚.toWeilData.Tw X (2 * (d : ℤ)) d) :
    𝔚.untwistTrace X d lam (𝔚.toWeilData.twCoord X (2 * (d : ℤ)) d x).1 = lam x := by
  let c : 𝔚.grade X (2 * (d : ℤ)) := 𝔚.toWeilData.twCoord X (2 * (d : ℤ)) d x
  have hp : 𝔚.projGrade X (2 * (d : ℤ)) c.1 = c :=
    Subtype.ext ((FirstChernClassData.coe_projGrade _ _ _ _).trans
      (DirectSum.decompose_of_mem_same _ c.2))
  change lam ((tateTwistCoordinates 𝔚.coord (d : ℤ)).symm (𝔚.projGrade X (2 * (d : ℤ)) c.1)) =
    lam x
  rw [hp]
  exact congrArg lam (LinearEquiv.symm_apply_apply _ x)

/-- `κ(γ(a))` depends only on the class `a`, through a heterogeneous equality across a change of
codimension. -/
theorem κ_γ_congr (X : (SmoothProjectiveScheme k).FullSubcategory) {n n' : ℕ} (hn : n = n')
    {a : codimensionChowGroup k X.obj.hom n} {a' : codimensionChowGroup k X.obj.hom n'}
    (h : a ≍ a') : 𝔚.κ X n (𝔚.γ X n a) = 𝔚.κ X n' (𝔚.γ X n' a') := by
  subst hn
  rw [eq_of_heq h]

/-- **`γ(θ) ∪ γ([E]) = b^*γ([Z])` from `b^![Z] = [E] · θ`**: for a morphism `b : X' ⟶ X`,
classes `[Z] ∈ CH^r(X)`, `[E] ∈ CH^1(X')` and `θ ∈ CH^{r-1}(X')` with `b^![Z] = [E] · θ`
(the first relation of Lemma 0FIH, the two sides lying in `CH^r(X')` and `CH^{1+(r-1)}(X')`),
`γ(θ) ∪ γ([E]) = b^*γ([Z])` in `H^{2r}(X')(r)`: `γ` is compatible with the Gysin map `b^!` and
multiplicative, and its values have even degree. -/
theorem cupTw_cycleClass_eq_pullTw_of_heq {X X' : (SmoothProjectiveScheme k).FullSubcategory}
    (b : X' ⟶ X) {r : ℕ} (hr0 : 0 < r) (gZ : codimensionChowGroup k X.obj.hom r)
    (gE : codimensionChowGroup k X'.obj.hom 1)
    (θ : codimensionChowGroup k X'.obj.hom ((r - 1 : ℕ) : ℤ))
    (h : codimensionGysin X'.obj.hom X.obj.hom (Over.w b.hom) (r : ℤ) gZ ≍
      codimensionIntersectionProduct k X'.obj.hom 1 ((r - 1 : ℕ) : ℤ) gE θ) :
    𝔚.toWeilData.cupTw X' (2 * ((r - 1 : ℕ) : ℤ)) (2 * 1) (2 * (r : ℤ)) (by omega)
        ((r - 1 : ℕ) : ℤ) 1 r (by omega)
        (𝔚.toWeilData.cycleClass X' ((r - 1 : ℕ) : ℤ) θ) (𝔚.toWeilData.cycleClass X' 1 gE) =
      𝔚.toWeilData.pullTw b _ _ (𝔚.toWeilData.cycleClass X r gZ) := by
  apply (𝔚.toWeilData.twCoord X' (2 * (r : ℤ)) r).injective
  apply Subtype.ext
  have hl : (𝔚.toWeilData.twCoord X' (2 * (r : ℤ)) r (𝔚.toWeilData.cupTw X'
      (2 * ((r - 1 : ℕ) : ℤ)) (2 * 1) (2 * (r : ℤ)) (by omega) ((r - 1 : ℕ) : ℤ) 1 r (by omega)
        (𝔚.toWeilData.cycleClass X' ((r - 1 : ℕ) : ℤ) θ)
        (𝔚.toWeilData.cycleClass X' 1 gE))).1 =
      𝔚.κ X' (r - 1 : ℕ) (𝔚.γ X' (r - 1) θ) * 𝔚.κ X' (1 : ℕ) (𝔚.γ X' 1 gE) :=
    (congrArg Subtype.val (WeilData.twCoord_cupTw _ _ _ _ _ _ _ _ _ _ _ _)).trans
      (congrArg₂ (· * ·) (𝔚.isCohomologicalChernCharacter.coe_twCoord_toWeilData_cycleClass
        𝔚.coproduct 𝔚.projectiveBundle 𝔚.kunneth 𝔚.trace X' (r - 1) θ)
        (𝔚.isCohomologicalChernCharacter.coe_twCoord_toWeilData_cycleClass
        𝔚.coproduct 𝔚.projectiveBundle 𝔚.kunneth 𝔚.trace X' 1 gE))
  have hr : (𝔚.toWeilData.twCoord X' (2 * (r : ℤ)) r
      (𝔚.toWeilData.pullTw b _ _ (𝔚.toWeilData.cycleClass X r gZ))).1 =
      𝔚.κ X' r (𝔚.γ X' r (codimensionGysin X'.obj.hom X.obj.hom (Over.w b.hom) (r : ℤ) gZ)) := by
    refine (congrArg Subtype.val (WeilData.twCoord_pullTw _ b _ _ _)).trans ?_
    refine (congrArg (𝔚.pull b)
      (𝔚.isCohomologicalChernCharacter.coe_twCoord_toWeilData_cycleClass 𝔚.coproduct
        𝔚.projectiveBundle 𝔚.kunneth 𝔚.trace X r gZ)).trans ?_
    rw [𝔚.isCohomologicalChernCharacter.codimensionCycleClass_codimensionGysin b r gZ,
      FirstChernClassData.κ_pullTw]
  have hmid : 𝔚.κ X' r (𝔚.γ X' r (codimensionGysin X'.obj.hom X.obj.hom (Over.w b.hom) (r : ℤ)
      gZ)) = 𝔚.κ X' (1 : ℕ) (𝔚.γ X' 1 gE) * 𝔚.κ X' (r - 1 : ℕ) (𝔚.γ X' (r - 1) θ) := by
    refine (𝔚.κ_γ_congr X' (show r = 1 + (r - 1) by omega) h).trans ?_
    refine (congrArg (𝔚.κ X' ((1 + (r - 1) : ℕ) : ℤ))
      (𝔚.isCohomologicalChernCharacter.codimensionCycleClass_codimensionIntersectionProduct
        𝔚.coproduct 𝔚.projectiveBundle X' 1 (r - 1) gE θ)).trans ?_
    exact tateTwistCoordinates_tateCup _ _ _ _ _ _ _ _
  have hcomm := 𝔚.graded_comm X' (2 * ((1 : ℕ) : ℤ)) (2 * ((r - 1 : ℕ) : ℤ)) _ _
    (𝔚.isCohomologicalChernCharacter.κ_codimensionCycleClass_mem 𝔚.coproduct 𝔚.projectiveBundle
      X' 1 gE)
    (𝔚.isCohomologicalChernCharacter.κ_codimensionCycleClass_mem 𝔚.coproduct 𝔚.projectiveBundle
      X' (r - 1) θ)
  rw [Int.negOnePow_even _ ⟨2 * ((r - 1 : ℕ) : ℤ), by push_cast; ring⟩, Units.val_one,
    one_smul] at hcomm
  rw [hl, hr, hmid, hcomm]

end WeilChernData

end Stacks.WeilCohomology

end
