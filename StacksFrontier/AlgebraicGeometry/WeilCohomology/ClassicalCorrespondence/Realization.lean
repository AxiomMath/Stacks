module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalCorrespondence.Iso
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalCorrespondence.Rescale
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationPreClassical
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiTateGenMap

/-!
# The classical Weil cohomology theory of a realization `(G, F[2] ≅ G(𝟏(1)))`

Let `R = (G, F[2] ≅ G(𝟏(1)))` be a realization of Chow motives as in Stacks 0FH3
(`Stacks.WeilCohomology.ClassicalMotiveRealization`). The isomorphism `F[2] ≅ G(𝟏(1))` is the
choice of a basis `e₁ ∈ G^{-2}(𝟏(1))`, the image of `1 ∈ F`, and so of compatible generators
`eₙ ∈ G^{-2n}(𝟏(n))`. Following the first paragraph of the proof of Stacks 0FH3 (and of
Stacks 0FH1), `R` gives a classical Weil cohomology theory with

* `H^*(X) = G(h(X))`, with the cup product and the pullbacks `G(h(f))`;
* `γ(α) = G(a_α)(e_{-r})` for `α ∈ CHʳ(X)` (`ClassicalMotiveRealization.cycleClass`);
* `∫_X x = G([X])(x ⊗ e_d)` for `X` of dimension `d` (`ClassicalMotiveRealization.trace`).

The theory is `WeilRealization.toPreClassical` (Stacks 0FH1), read in the coordinate of the Tate
line given by `e₁` (`PreClassicalWeilCohomologyTheory.rescale` by the ratio of `e₁` and the basis
used there), with axioms (A)(c), (A)(d) from conditions (1), (2).

## Main definitions

* `Stacks.WeilCohomology.ClassicalMotiveRealization.tateVec`: `e₁`.
* `Stacks.WeilCohomology.ClassicalMotiveRealization.tateGen`: the generators `eₙ`.
* `Stacks.WeilCohomology.ClassicalMotiveRealization.cycleClass`,
  `Stacks.WeilCohomology.ClassicalMotiveRealization.trace`: `γ` and `∫` on `G(h(X))`.
* `Stacks.WeilCohomology.ClassicalMotiveRealization.toClassicalWeilCohomologyTheory`: the theory.
* `Stacks.WeilCohomology.ClassicalWeilCohomologyTheory.Corresponds`: `H^*(X) = G(h(X))` with all
  its structure.

## Main results

* `Stacks.WeilCohomology.ClassicalMotiveRealization.corresponds_toClassicalWeilCohomologyTheory`:
  the theory of `R` corresponds to `R`.
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

namespace ChowMotiveCat

variable {F' : Type v} [Field F'] (G : ChowMotiveCat k ⥤ GradedObject ℤ (ModuleCat.{v} F'))
  [G.Additive]

/-- The cycle class map of rescaled generators `cⁿ eₙ` is `c⁻ⁱ γ`. -/
theorem cycleClassMotive_smul (e : ∀ n : ℤ, (G.obj (tate k n)) (-2 * n)) (c : F'ˣ)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) :
    cycleClassMotive G (fun n ↦ ((c ^ n : F'ˣ) : F') • e n) X i α =
      ((c ^ (-i) : F'ˣ) : F') • cycleClassMotive G e X i α := by
  rw [cycleClassMotive_apply, cycleClassMotive_apply, tateGenNeg, tateGenNeg]
  rw [map_smul, map_smul]

end ChowMotiveCat

namespace ClassicalMotiveRealization

variable (R : ClassicalMotiveRealization k F)

/-- The isomorphism `F ≅ G^{-2}(𝟏(1))` of `F[2] ≅ G(𝟏(1))` in degree `-2`. -/
def tateEquiv : F ≃ₗ[F] R.toWeilRealization.tateLine :=
  (GradedObject.singleObjApplyIso (-2) (ModuleCat.of F F)).symm.toLinearEquiv.trans
    ((GradedObject.eval (-2)).mapIso R.tateIso).toLinearEquiv

/-- **The basis `e₁ ∈ G^{-2}(𝟏(1))`** given by `F[2] ≅ G(𝟏(1))`: the image of `1`. -/
def tateVec : R.toWeilRealization.tateLine :=
  R.tateEquiv 1

theorem tateVec_ne_zero : R.tateVec ≠ 0 :=
  (map_ne_zero_iff _ R.tateEquiv.injective).2 one_ne_zero

/-- The coordinate of `e₁` in the coordinate of the Tate line used by `WeilRealization.toWeilData`,
a unit. -/
def tateScalar : Fˣ :=
  Units.mk0 (tateLineCoordinate R.toWeilRealization.finrank_tateLine R.tateVec)
    ((map_ne_zero_iff _ (LinearEquiv.injective _)).2 R.tateVec_ne_zero)

/-- `e₁` is `c` times the basis vector of `WeilRealization.toWeilData`, `c = tateScalar`. -/
theorem tateVec_eq : R.tateVec = (R.tateScalar : F) • R.toWeilRealization.tateBasis := by
  apply (tateLineCoordinate R.toWeilRealization.finrank_tateLine).injective
  rw [tateScalar, Units.val_mk0, WeilRealization.tateBasis, map_smul, LinearEquiv.apply_symm_apply,
    smul_eq_mul, mul_one]

section

attribute [-instance] ChowMotiveCat.monoidalCategory ChowMotiveCat.braidedCategory
  ChowMotiveCat.symmetricCategory TwistedKaroubi.monoidalCategoryStruct
  CorrespondenceCategory.monoidalCategoryStruct TwistedKaroubi.symmetricCategory

attribute [local instance] WeilRealization.braidedTK WeilRealization.monoidalTK

/-- A monoidal natural transformation of realizations commutes with the traces
`x ↦ G([X])(x ⊗ e)`, `e` being replaced by its image. -/
theorem _root_.Stacks.WeilCohomology.WeilRealization.gradedTrace_fundamentalClassMot_app
    {G G' : WeilRealization k F} (θ : G.functorTK ⟶ G'.functorTK) [θ.IsMonoidal]
    {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}
    (hX : RelativeDimension X.obj.hom d) (e : TwistedKaroubi.tateLine G.functorTK (-2) d)
    (x : (G.functorTK.obj (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X))) (2 * d)) :
    G'.functorTK.gradedTrace (ChowMotiveCat.fundamentalClassMot hX)
        (θ.app (TwistedKaroubi.tateTriple ℚ _ d) _ e) (2 * d) (by ring) (θ.app _ _ x) =
      G.functorTK.gradedTrace (ChowMotiveCat.fundamentalClassMot hX) e (2 * d) (by ring) x :=
  NatTrans.gradedTrace_app θ _ e _ _ x

/-- The generators `eₙ⁰` of the basis `e₁⁰` of `WeilRealization.toWeilData`, as elements of the
lines `G(T(n))^{-2n}`. -/
def _root_.Stacks.WeilCohomology.WeilRealization.baseGen (G : WeilRealization k F) (n : ℤ) :
    TwistedKaroubi.tateLine G.functorTK (-2) n :=
  TwistedKaroubi.tateGen (G := G.functorTK) G.tate_degree G.tateBasis_ne_zero n

/-- **The generators `eₙ ∈ G^{-2n}(𝟏(n))`** determined by `e₁ = tateVec`. -/
def tateGen (n : ℤ) : TwistedKaroubi.tateLine R.toWeilRealization.functorTK (-2) n :=
  TwistedKaroubi.tateGen (G := R.toWeilRealization.functorTK) R.toWeilRealization.tate_degree
    R.tateVec_ne_zero n

/-- The generators of `e₁ = c e₁⁰` are `cⁿ` times those of `WeilRealization.toWeilData`. -/
theorem tateGen_eq (n : ℤ) :
    R.tateGen n = ((R.tateScalar ^ n : Fˣ) : F) • R.toWeilRealization.baseGen n := by
  have hce : (R.tateScalar : F) • R.toWeilRealization.tateBasis ≠ 0 :=
    R.tateVec_eq ▸ R.tateVec_ne_zero
  have key : ∀ (e e' : R.toWeilRealization.tateLine) (he : e ≠ 0) (he' : e' ≠ 0), e = e' →
      TwistedKaroubi.tateGen (G := R.toWeilRealization.functorTK) R.toWeilRealization.tate_degree
        he n =
      TwistedKaroubi.tateGen (G := R.toWeilRealization.functorTK) R.toWeilRealization.tate_degree
        he' n := by
    rintro e _ he he' rfl
    rfl
  exact (key _ _ R.tateVec_ne_zero hce R.tateVec_eq).trans
    (TwistedKaroubi.tateGen_smul R.toWeilRealization.tate_degree
      R.toWeilRealization.tateBasis_ne_zero R.tateScalar hce n)

/-- **The cycle class map of `R`**, `γ(α) = G(a_α)(e_{-r})` in `G(h(X))^{2r}`, for the generators
of `F[2] ≅ G(𝟏(1))`. -/
def cycleClass (X : (SmoothProjective k).FullSubcategory) (r : ℤ) :
    (chowCycleData k).group X r →+
      (R.toWeilRealization.functor.obj
        (TwistedKaroubi.ofObj (R := ℚ) (𝐎 ((SmoothProjective.toSchemeCat k).obj X))))
        (2 * r) :=
  ChowMotiveCat.cycleClassMotive R.toWeilRealization.functor (fun n ↦ R.tateGen n)
    ((SmoothProjective.toSchemeCat k).obj X) r

/-- **The trace map of `R`**, `∫_X x = G([X])(x ⊗ e_d)` on `G(h(X))^{2d}`, for `X` of dimension
`d` and the generators of `F[2] ≅ G(𝟏(1))`. -/
def trace (X : (SmoothProjective k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional ((SmoothProjective.toSchemeCat k).obj X) d) :
    (R.toWeilRealization.functor.obj
      (TwistedKaroubi.ofObj (R := ℚ) (𝐎 ((SmoothProjective.toSchemeCat k).obj X))))
      (2 * (d : ℤ)) →ₗ[F] F :=
  R.toWeilRealization.functorTK.gradedTrace
    (ChowMotiveCat.fundamentalClassMot hX.relativeDimension) (R.tateGen d) (2 * d) (by ring)

/-- The cycle class map of `R` is `c⁻ʳ` times that of `WeilRealization.toWeilData`. -/
theorem cycleClass_eq (X : (SmoothProjective k).FullSubcategory) (r : ℤ)
    (α : (chowCycleData k).group X r) :
    R.cycleClass X r α = ((R.tateScalar ^ (-r) : Fˣ) : F) •
      ChowMotiveCat.cycleClassMotive R.toWeilRealization.functorTK R.toWeilRealization.tateGen
        ((SmoothProjective.toSchemeCat k).obj X) r α := by
  have h : (fun n ↦ R.tateGen n) =
      fun n ↦ ((R.tateScalar ^ n : Fˣ) : F) • R.toWeilRealization.baseGen n :=
    funext R.tateGen_eq
  rw [cycleClass, h]
  exact ChowMotiveCat.cycleClassMotive_smul _ (fun n ↦ R.toWeilRealization.baseGen n)
    R.tateScalar _ r α

/-- The trace map of `R` is `c^d` times that of `WeilRealization.toWeilData`. -/
theorem trace_eq (X : (SmoothProjective k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional ((SmoothProjective.toSchemeCat k).obj X) d) (x) :
    R.trace X d hX x = ((R.tateScalar ^ (d : ℤ) : Fˣ) : F) •
      R.toWeilRealization.functorTK.gradedTrace
        (ChowMotiveCat.fundamentalClassMot hX.relativeDimension) (R.toWeilRealization.baseGen d)
        (2 * d) (by ring) x := by
  rw [trace, R.tateGen_eq]
  exact Functor.gradedTrace_smul R.toWeilRealization.functorTK
    (ChowMotiveCat.fundamentalClassMot hX.relativeDimension) ((R.tateScalar ^ (d : ℤ) : Fˣ) : F)
    (R.toWeilRealization.baseGen d) (2 * d) (by ring) x

end

end ClassicalMotiveRealization

end Stacks.WeilCohomology

end
