module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalCorrespondence.Realization

/-!
# A realization `(G, F[2] ≅ G(𝟏(1)))` gives a classical Weil cohomology theory

The first paragraph of the proof of Stacks 0FH3. For a realization
`R = (G, F[2] ≅ G(𝟏(1)))` (`Stacks.WeilCohomology.ClassicalMotiveRealization`), setting
`H^*(X) = G(h(X))` gives data (D1), (D2), (D3) satisfying all of (A), (B), (C) except possibly
(A)(c), (A)(d) (Stacks 0FH1), read in the coordinate of the Tate line given by
`F[2] ≅ G(𝟏(1))`; conditions (1) and (2) of `R` give (A)(c) and (A)(d).

This file also defines what it means for a classical Weil cohomology theory `H^*` and a
realization `R` to correspond, `H^*(X) = G(h(X))` with all its structure
(`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.Corresponds`): an identification
`H^*(X) ≅ G(h(X))`, natural in `X`, of graded algebras, carrying the cycle classes to
`γ(α) = G(a_α)(e_{-r})` and the trace to `x ↦ G([X])(x ⊗ e_d)` for the generators `eₙ` of
`F[2] ≅ G(𝟏(1))`; and proves that the theory of `R` corresponds to `R`.

## Main definitions

* `Stacks.WeilCohomology.ClassicalMotiveRealization.toClassicalWeilCohomologyTheory`.
* `Stacks.WeilCohomology.ClassicalMotiveRealization.motiveComparison`: `H^*(X) = G(h(X))`.
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.Corresponds`.

## Main results

* `Stacks.WeilCohomology.ClassicalMotiveRealization.corresponds_toClassicalWeilCohomologyTheory`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite CategoryTheory.GradedCategory
  Stacks.Chow
open Stacks.WeilCohomology.ChowMotiveCat (h tate)

universe u v

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]

local notation "𝐎" =>
  (GradedCompositionData.Obj.mk :
    CategoryTheory.ObjectProperty.FullSubcategory (SmoothProjectiveScheme _) →
      CorrespondenceCategory _)

attribute [-instance] ChowMotiveCat.monoidalCategory ChowMotiveCat.braidedCategory
  ChowMotiveCat.symmetricCategory TwistedKaroubi.monoidalCategoryStruct
  CorrespondenceCategory.monoidalCategoryStruct TwistedKaroubi.symmetricCategory

attribute [local instance] WeilRealization.braidedTK WeilRealization.monoidalTK

namespace WeilRealization

variable (G : WeilRealization k F)

/-- The unit of `H^*(X) = G(h(X))` is the unit of the graded algebra `G(h(X))`. -/
theorem gradeEquiv_one (X : (SmoothProjectiveScheme k).FullSubcategory) :
    (G.cohAlg X).gradeEquiv 0 ⟨1, SetLike.GradedOne.one_mem⟩ = (G.cohAlg X).one :=
  ExternallyGradedAlgebra.gradeEquiv_apply _ _ _ (ExternallyGradedAlgebra.one_eq_of _)

/-- The cup product of `H^*(X) = G(h(X))` is the product of the graded algebra `G(h(X))`. -/
theorem gradeEquiv_mul (X : (SmoothProjectiveScheme k).FullSubcategory) (i j : ℤ)
    (a : G.toWeilData.grade X i) (b : G.toWeilData.grade X j) :
    (G.cohAlg X).gradeEquiv (i + j) (G.toWeilData.cup X i j (i + j) rfl a b) =
      (G.cohAlg X).mul i j ((G.cohAlg X).gradeEquiv i a) ((G.cohAlg X).gradeEquiv j b) := by
  apply ExternallyGradedAlgebra.gradeEquiv_apply
  obtain ⟨a, rfl⟩ := ((G.cohAlg X).gradeEquiv i).symm.surjective a
  obtain ⟨b, rfl⟩ := ((G.cohAlg X).gradeEquiv j).symm.surjective b
  simp only [LinearEquiv.apply_symm_apply]
  change (((G.cohAlg X).gradeEquiv i).symm a : (G.cohAlg X).Total) *
    (((G.cohAlg X).gradeEquiv j).symm b : (G.cohAlg X).Total) = _
  exact (congrArg₂ (· * ·) ((G.cohAlg X).gradeEquiv_symm_apply_coe i a)
    ((G.cohAlg X).gradeEquiv_symm_apply_coe j b)).trans ((G.cohAlg X).of_mul_of a b)

end WeilRealization

namespace ClassicalMotiveRealization

variable (R : ClassicalMotiveRealization k F)

/-- **The data of Stacks 0FH1 for `R`, read in the coordinate `e₁` of `F[2] ≅ G(𝟏(1))`**:
`H^*(X) = G(h(X))`, `γ(α) = G(a_α)(e_{-r})`, `∫_X x = G([X])(x ⊗ e_d)`. -/
def toPreClassical : PreClassicalWeilCohomologyTheory.{u, v, v, u} k F (chowCycleData k) :=
  R.toWeilRealization.toPreClassical.rescale R.tateScalar

/-- `H^n(X) = G(h(X))^n`. -/
def pieceEquiv (X : (SmoothProjective k).FullSubcategory) (n : ℤ) :
    (R.toPreClassical.H X).piece n ≃ₗ[F]
      (R.toWeilRealization.functor.obj
        (TwistedKaroubi.ofObj (R := ℚ) (𝐎 ((SmoothProjective.toSchemeCat k).obj X)))) n :=
  R.toWeilRealization.toPreClassicalPieceEquiv X n

/-- The cycle class map of `R.toPreClassical` is the cycle class map of `R`. -/
theorem pieceEquiv_cycleClass (X : (SmoothProjective k).FullSubcategory) (r : ℤ)
    (α : (chowCycleData k).group X r) :
    R.pieceEquiv X (2 * r) (R.toPreClassical.cycleClass X r α) = R.cycleClass X r α := by
  rw [R.cycleClass_eq]
  exact ((R.pieceEquiv X (2 * r)).map_smul ((R.tateScalar ^ (-r) : Fˣ) : F)
    (R.toWeilRealization.toPreClassical.cycleClass X r α)).trans
    (congrArg _ (R.toWeilRealization.toPreClassicalPieceEquiv_cycleClass X r α))

/-- The trace map of `R.toPreClassical` is the trace map of `R`. -/
theorem trace_pieceEquiv (X : (SmoothProjective k).FullSubcategory)
    (a : (R.toPreClassical.H X).piece (2 * (SmoothProjective.dim X : ℤ))) :
    R.trace X (SmoothProjective.dim X) (SmoothProjective.isNonemptyEquidimensional_dim X)
      (R.pieceEquiv X _ a) = R.toPreClassical.integration X a := by
  refine (R.trace_eq X _ _ _).trans ?_
  change _ = ((R.tateScalar ^ (SmoothProjective.dim X : ℤ) : Fˣ) : F) •
    R.toWeilRealization.toWeilData.traceCoord _ (SmoothProjective.dim X)
      (SmoothProjective.isNonemptyEquidimensional_dim X) a
  rw [WeilRealization.toWeilData_traceCoord]
  rfl

/-- Conditions (1) and (2) of `R` hold for `R.toPreClassical`: `H^i(X) = 0` for `i < 0`. -/
theorem toPreClassical_eq_zero_of_neg (X : (SmoothProjective k).FullSubcategory) (i : ℤ)
    (hi : i < 0) (a : (R.toPreClassical.H X).piece i) : a = 0 :=
  (R.pieceEquiv X i).injective (((ModuleCat.isZero_iff_subsingleton.1 (R.nonneg X i hi)).elim
    (R.pieceEquiv X i a) 0).trans (map_zero _).symm)

/-- Condition (2) of `R` for `R.toPreClassical`: `dim_F H⁰(X) = 1`. -/
theorem toPreClassical_finrank_zero (X : (SmoothProjective k).FullSubcategory) :
    Module.finrank F ((R.toPreClassical.H X).piece 0) = 1 :=
  (R.pieceEquiv X 0).finrank_eq.trans (R.finrank_zero X)

/-- **The classical Weil cohomology theory of a realization `(G, F[2] ≅ G(𝟏(1)))`** (the first
paragraph of the proof of Stacks 0FH3): `H^*(X) = G(h(X))`, `γ(α) = G(a_α)(e_{-r})`,
`∫_X x = G([X])(x ⊗ e_d)`, for the generators `eₙ` of `F[2] ≅ G(𝟏(1))`; conditions (1) and (2)
give axioms (A)(c) and (A)(d). -/
def toClassicalWeilCohomologyTheory :
    ClassicalWeilCohomologyTheory.{u, v, v, u} k F (chowCycleData k) :=
  R.toPreClassical.toClassicalOfNonneg R.toPreClassical_eq_zero_of_neg
    R.toPreClassical_finrank_zero

@[simp]
theorem toPre_toClassicalWeilCohomologyTheory :
    R.toClassicalWeilCohomologyTheory.toPre = R.toPreClassical :=
  rfl

end ClassicalMotiveRealization

namespace ClassicalWeilCohomologyTheory

/-- **`H^*(X) = G(h(X))` with all its structure** (Stacks 0FH3), for a classical Weil cohomology
theory `H^*` and a realization `R = (G, F[2] ≅ G(𝟏(1)))`: isomorphisms `H^i(X) ≅ G(h(X))^i` for
every smooth projective variety `X`, where `h(X) = (X, 1, 0)`, such that

* `f^*` corresponds to `G(h(f))`, `h(f) = [Γ_f]`;
* the unit and the cup product of `H^*(X)` correspond to the unit and the product of the graded
  algebra `G(h(X))` of the commutative monoid `h(X)`;
* the cycle class `γ(α)` corresponds to `G(a_α)(e_{-r})` (`ClassicalMotiveRealization.cycleClass`);
* the trace `∫_X` corresponds to `x ↦ G([X])(x ⊗ e_d)` (`ClassicalMotiveRealization.trace`),

for the generators `eₙ ∈ G^{-2n}(𝟏(n))` of the isomorphism `F[2] ≅ G(𝟏(1))`. -/
structure Comparison (T : ClassicalWeilCohomologyTheory.{u, v, v, u} k F (chowCycleData k))
    (R : ClassicalMotiveRealization k F) where
  /-- The isomorphisms `H^i(X) ≅ G(h(X))^i`. -/
  iso : ∀ (X : (SmoothProjective k).FullSubcategory) (i : ℤ),
    (T.H X).piece i ≃ₗ[F]
      (R.toWeilRealization.functor.obj
        (TwistedKaroubi.ofObj (R := ℚ) (𝐎 ((SmoothProjective.toSchemeCat k).obj X)))) i
  /-- Pullback `f^*` corresponds to `G(h(f))`. -/
  iso_pullback : ∀ {X Y : (SmoothProjective k).FullSubcategory} (f : X ⟶ Y) (i : ℤ)
    (a : (T.H Y).piece i), iso X i (T.pullback f i a) =
      R.toWeilRealization.functor.map
        (ChowMotiveCat.motMap ((SmoothProjective.toSchemeCat k).map f)) i (iso Y i a)
  /-- The unit of `H^*(X)` is the unit of `G(h(X))`. -/
  iso_one : ∀ X, iso X 0 (T.H X).one =
    (R.toWeilRealization.cohAlg ((SmoothProjective.toSchemeCat k).obj X)).one
  /-- The cup product of `H^*(X)` is the product of `G(h(X))`. -/
  iso_mul : ∀ X (i j : ℤ) (a : (T.H X).piece i) (b : (T.H X).piece j),
    iso X (i + j) ((T.H X).mul i j a b) =
      (R.toWeilRealization.cohAlg ((SmoothProjective.toSchemeCat k).obj X)).mul i j (iso X i a)
        (iso X j b)
  /-- The cycle class `γ(α)` is `G(a_α)(e_{-r})`. -/
  iso_cycleClass : ∀ X (r : ℤ) (α : (chowCycleData k).group X r),
    iso X (2 * r) (T.cycleClass X r α) = R.cycleClass X r α
  /-- The trace `∫_X` is `x ↦ G([X])(x ⊗ e_d)`. -/
  trace_iso : ∀ X (a : (T.H X).piece (2 * (T.dimension X : ℤ))),
    R.trace X (T.dimension X) (SmoothProjective.isNonemptyEquidimensional X (T.dimension_eq X))
      (iso X _ a) = T.integration X a

/-- **A classical Weil cohomology theory `H^*` and a realization `R = (G, F[2] ≅ G(𝟏(1)))`
correspond**: `H^*(X) = G(h(X))` with all its structure
(`ClassicalWeilCohomologyTheory.Comparison`), the sense of Stacks 0FH3. -/
def Corresponds (T : ClassicalWeilCohomologyTheory.{u, v, v, u} k F (chowCycleData k))
    (R : ClassicalMotiveRealization k F) : Prop :=
  Nonempty (T.Comparison R)

end ClassicalWeilCohomologyTheory

namespace ClassicalMotiveRealization

variable (R : ClassicalMotiveRealization k F)

/-- **`H^*(X) = G(h(X))`** for the theory of `R`, with all its structure. -/
def comparison : R.toClassicalWeilCohomologyTheory.Comparison R where
  iso X n := R.pieceEquiv X n
  iso_pullback _ n a := R.toWeilRealization.gradeEquiv_pullDeg _ n a
  iso_one _ := R.toWeilRealization.gradeEquiv_one _
  iso_mul _ i j a b := R.toWeilRealization.gradeEquiv_mul _ i j a b
  iso_cycleClass X r α := R.pieceEquiv_cycleClass X r α
  trace_iso X a := R.trace_pieceEquiv X a

/-- **The theory of `R` corresponds to `R`.** -/
theorem corresponds_toClassicalWeilCohomologyTheory :
    R.toClassicalWeilCohomologyTheory.Corresponds R :=
  ⟨R.comparison⟩

end ClassicalMotiveRealization

end Stacks.WeilCohomology

end
