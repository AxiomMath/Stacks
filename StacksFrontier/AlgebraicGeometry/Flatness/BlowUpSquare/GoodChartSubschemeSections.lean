module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleSubschemeExistence

/-!
# The coordinate ring of the closed subscheme of Tag 0GTZ over a good chart

Let `(X, D, M)` be a good triple and `T ⊆ D` the closed subscheme of More on Flatness,
Tag 0GTZ, whose ideal over `D ∩ U` is the total obstruction ideal `J(M^•, f) ⊆ A ⧸ fA` for every
affine chart `(U, A, f, M^•)` with principal determinantal ideals.  The inverse image `T ∩ U` of
`U` in `T` is affine, and the restriction map `A = Γ(X, U) → Γ(T, T ∩ U)` is surjective with
kernel the inverse image of `J(M^•, f)` in `A`: the coordinate ring of `T ∩ U` is
`(A ⧸ fA) ⧸ J(M^•, f)`, the ring `C` of More on Algebra, Tag 0F81.

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.goodChartSubschemeIncl`: the composite
  `T ⟶ D ⟶ X`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.subschemeChartOpen`: the affine open
  `T ∩ U` of `T`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.subschemeSectionMap`: the
  restriction map `Γ(X, U) → Γ(T, T ∩ U)`.

## Main results

* `AffineChart.surjective_subschemeSectionMap` and `AffineChart.ker_subschemeSectionMap`: the
  restriction map is surjective with kernel the inverse image of `J(M^•, f)`.
* `AffineChart.ker_subschemeSectionMap_of_le_locallyFreeLocus`: over a chart contained in the
  locally free locus the kernel is `fA`.

## References

* [Stacks Project, Tag 0GTZ](https://stacks.math.columbia.edu/tag/0GTZ)
* [Stacks Project, Tag 0F81](https://stacks.math.columbia.edu/tag/0F81)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

variable {S : ComplexAndDivisorSituation.{u, d}} (hS : S.IsGoodTriple)

/-- The closed immersion `T ⟶ D ⟶ X` of the closed subscheme of Tag 0GTZ. -/
abbrev goodChartSubschemeIncl : (S.goodChartSubscheme hS).subscheme ⟶ S.X :=
  (S.goodChartSubscheme hS).subschemeι ≫ S.D.subschemeι

namespace AffineChart

open Stacks.Decalage.DirectSumIdeal

variable (C : AffineChart S)

/-- The affine open `T ∩ U` of the closed subscheme of Tag 0GTZ over an affine chart. -/
def subschemeChartOpen : (S.goodChartSubscheme hS).subscheme.affineOpens :=
  ⟨(S.goodChartSubscheme hS).subschemeι ⁻¹ᵁ (C.divisorAffineOpen : S.D.subscheme.Opens),
    (S.goodChartSubscheme hS).isAffineOpen_preimage_subschemeι C.divisorAffineOpen⟩

/-- The open `T ∩ U` of `T` is contained in the inverse image of `U` under `T ⟶ X`. -/
theorem subschemeChartOpen_le :
    ((C.subschemeChartOpen hS : (S.goodChartSubscheme hS).subscheme.Opens)) ≤
      goodChartSubschemeIncl hS ⁻¹ᵁ (C.U : S.X.Opens) :=
  le_rfl

/-- The restriction map `Γ(X, U) → Γ(T, T ∩ U)`. -/
def subschemeSectionMap :
    Γ(S.X, C.U) →+* Γ((S.goodChartSubscheme hS).subscheme,
      (C.subschemeChartOpen hS : (S.goodChartSubscheme hS).subscheme.Opens)) :=
  ((goodChartSubschemeIncl hS).appLE (C.U : S.X.Opens) _ (C.subschemeChartOpen_le hS)).hom

/-- The restriction map is the restriction map of `D ⟶ X` followed by that of `T ⟶ D`. -/
theorem subschemeSectionMap_eq :
    C.subschemeSectionMap hS =
      ((S.goodChartSubscheme hS).subschemeι.app (C.divisorAffineOpen :
        S.D.subscheme.Opens)).hom.comp (S.D.subschemeι.app (C.U : S.X.Opens)).hom := by
  rw [subschemeSectionMap, Scheme.Hom.comp_appLE, CommRingCat.hom_comp]
  congr 1
  exact congrArg CommRingCat.Hom.hom
    (Scheme.Hom.appLE_eq_app (S.goodChartSubscheme hS).subschemeι
      (U := (C.divisorAffineOpen : S.D.subscheme.Opens)))

/-- The restriction map `Γ(X, U) → Γ(T, T ∩ U)` is surjective. -/
theorem surjective_subschemeSectionMap : Function.Surjective (C.subschemeSectionMap hS) := by
  rw [subschemeSectionMap_eq]
  exact ((S.goodChartSubscheme hS).subschemeι_app_surjective C.divisorAffineOpen).comp
    (S.D.subschemeι_app_surjective C.U)

/-- The kernel of the restriction map is the inverse image of the ideal of `T` over `D ∩ U`. -/
theorem ker_subschemeSectionMap_eq_comap :
    RingHom.ker (C.subschemeSectionMap hS) =
      ((S.goodChartSubscheme hS).ideal C.divisorAffineOpen).comap
        (S.D.subschemeι.app (C.U : S.X.Opens)).hom := by
  rw [subschemeSectionMap_eq]
  exact (RingHom.comap_ker _ _).symm.trans (congrArg (Ideal.comap _)
    ((S.goodChartSubscheme hS).ker_subschemeι_app C.divisorAffineOpen))

/-- **The coordinate ring of `T ∩ U` is `(A ⧸ fA) ⧸ J(M^•, f)`**: over a chart with principal
determinantal ideals, the kernel of `Γ(X, U) → Γ(T, T ∩ U)` is the inverse image of the total
obstruction ideal. -/
theorem ker_subschemeSectionMap (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) :
    RingHom.ker (C.subschemeSectionMap hS) =
      (etaTotalDirectSumIdeal C.complex C.f).comap (Ideal.Quotient.mk (Ideal.span {C.f})) := by
  refine (C.ker_subschemeSectionMap_eq_comap hS).trans ?_
  rw [S.ideal_goodChartSubscheme hS C hI]
  ext a
  exact (Ideal.mem_map_of_equiv C.divisorQuotEquiv.symm _).trans
    ⟨fun ⟨y, hy, h⟩ => by
        rw [Ideal.mem_comap, ← C.divisorQuotEquiv.symm.injective
          (h.trans (C.divisorQuotEquiv_symm_mk a).symm)]
        exact hy,
      fun h => ⟨_, h, C.divisorQuotEquiv_symm_mk a⟩⟩

/-- Over a chart contained in the locally free locus the kernel of `Γ(X, U) → Γ(T, T ∩ U)` is
`fA`: the obstruction ideal vanishes there. -/
theorem ker_subschemeSectionMap_of_le_locallyFreeLocus
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal)
    (hW : (C.U : S.X.Opens) ≤ S.locallyFreeLocus) :
    RingHom.ker (C.subschemeSectionMap hS) = Ideal.span {C.f} := by
  refine (C.ker_subschemeSectionMap_eq_comap hS).trans ?_
  refine (congrArg (Ideal.comap _) ((S.ideal_goodChartSubscheme hS C hI).trans
    (C.obstructionIdeal_eq_bot_of_le_locallyFreeLocus hI hW))).trans ?_
  exact (RingHom.ker_eq_comap_bot _).symm.trans ((S.D.ker_subschemeι_app C.U).trans
    C.divisor_ideal)

end AffineChart

end AlgebraicGeometry.ComplexAndDivisorSituation
