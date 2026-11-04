module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisonsOnHomotopyCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitUnboundedIdentification

/-!
# The unbounded comparison, pinned against the underived comparison

Let `f : C' ⥤ C` be a functor between small categories with their chaotic topologies, let `g^{-1}`
be restriction of diagrams along `f`, and let the coefficients `D` be abelian with enough
projectives in the two diagram categories. This file identifies the comparison
`Stacks.ChaoticSite.unboundedComparison` of the two derived lower shrieks on the **unbounded**
derived category, composed with the comparison of `Lπ_!` with `π_!`, with the *underived*
comparison `Stacks.CategoryHomology.diagramColimitRestrictionPre` of the two colimits. At a complex
`K` of diagrams on `C`, writing `τ` for the comparison, `ε`, `ε'` for the two derived-functor
comparisons and `π_!`-pre for the underived one,

`τ_{Q_h K} ≫ ε_K = Lπ'_!(g^{-1}-factorisation) ≫ ε'_{g^{-1}K} ≫ Q_h(π_!-pre on complexes)`.

Since the comparison of `Lπ_!` with `π_!` is invertible at a diagram projective along a point
resolution (`Stacks.ChaoticSite.isIso_totalDerivedColimitCounit_single_of_projective_restrict`) and
the underived comparison is invertible under the source's hypothesis
(`Stacks.ChaoticSite.isIso_colimitPre_op_of_isPointResolutions`), this identity turns
[Stacks, Tag 08QA] on the unbounded derived category into those two statements.

## Main results

* `Stacks.ChaoticSite.restrict_colimConstAdj_unit_mapHomologicalComplex` and
  `Stacks.ChaoticSite.restrict_colimConstAdj_unit_mapHomotopyCategory`:
  `Stacks.ChaoticSite.restrict_colimConstAdj_unit` read degreewise on cochain complexes and then on
  homotopy categories — the underived input of the identification.
* `Stacks.ChaoticSite.unboundedComparison_app_comp_counit_of_unit`: the identification, stated for
  an abstract morphism `u` of homotopy categories satisfying the underived identity.
* `Stacks.ChaoticSite.unboundedComparison_app_comp_counit`: the identification itself.

## Implementation notes

Both sides have the same transpose along `Lπ'_! ⊣ π'^{-1}`: the left one by
`Stacks.ChaoticSite.unit_comp_unboundedComparison_comp_counit` together with the value of the
composition comparison of the derived constant diagrams at an object coming from the homotopy
category (`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Qh`), the right one
by naturality of the unit and
`Stacks.CategoryHomology.totalDerivedColimitAdjunction_unit_app_comp_counit` read for `C'`.

The two transposes are compared **in term mode**. `rw [Adjunction.homEquiv_unit,
Adjunction.homEquiv_unit]` rewrites only the first of the two occurrences and leaves the goal
ill-typed at `implicit` transparency; the comparison is therefore handed to
`CategoryTheory.Equiv.injective` as a single term, where the equality of
`⇑(adj.homEquiv _ _) φ` with `unit ≫ π'^{-1}(φ)` is checked at `default` transparency, which is
where it holds.

Two composites appearing in the computation are well typed only at `default` transparency, because
`g^{-1}(π^{-1}(-))` and `π'^{-1}(-)` on homotopy categories are the same functor written two ways.
A tactic may not build such a composite: `rw` reports *"the target expression is not type-correct
under the `implicit` transparency level"*. Both are therefore handled by keeping the offending
factor abstract — `Stacks.ChaoticSite.unboundedComparison_app_comp_counit_of_unit` is stated at a
variable `u` rather than at the underived comparison itself, and the cancellation of the two copies
of the comparison of `π^{-1}` is proved at an abstract tail — and by assembling the rest with
`congrArg` and `CategoryTheory.Category.assoc` as terms.

## References

* [Stacks Project, Tag 08QA](https://stacks.math.columbia.edu/tag/08QA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryHomology

namespace Stacks.ChaoticSite

universe uD vD u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {C C' : Type u} [SmallCategory C] [SmallCategory C'] (f : C' ⥤ C)
  (D : Type uD) [Category.{vD} D] [Abelian D]
  [EnoughProjectives (Cᵒᵖ ⥤ D)] [EnoughProjectives (C'ᵒᵖ ⥤ D)]
  [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D]
  [HasColimitsOfShape Cᵒᵖ D] [HasColimitsOfShape C'ᵒᵖ D]

omit [EnoughProjectives (Cᵒᵖ ⥤ D)] [EnoughProjectives (C'ᵒᵖ ⥤ D)] [HasColimitsOfShape ℕ D]
  [HasExactColimitsOfShape ℕ D] in
/-- **`Stacks.ChaoticSite.restrict_colimConstAdj_unit` read degreewise on cochain complexes.**
Restriction along `f.op` carries the unit of `colim_{Cᵒᵖ} ⊣ const_{Cᵒᵖ}` on a complex of diagrams
to the unit of `colim_{C'ᵒᵖ} ⊣ const_{C'ᵒᵖ}` followed by the constant diagram of the underived
comparison. Both sides are degreewise, so this is the statement at a single diagram applied in
each degree. -/
theorem restrict_colimConstAdj_unit_mapHomologicalComplex (K : CochainComplex (Cᵒᵖ ⥤ D) ℤ) :
    (((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex
          (colimConstAdj : (colim : (Cᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const Cᵒᵖ).unit
          (ComplexShape.up ℤ)).app K) =
      (NatTrans.mapHomologicalComplex
            (colimConstAdj : (colim : (C'ᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const C'ᵒᵖ).unit
            (ComplexShape.up ℤ)).app
          ((((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        ((Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (diagramColimitRestrictionPre f D)
            (ComplexShape.up ℤ)).app K) :=
  HomologicalComplex.hom_ext _ _ fun i ↦ restrict_colimConstAdj_unit f D (K.X i)

omit [EnoughProjectives (Cᵒᵖ ⥤ D)] [EnoughProjectives (C'ᵒᵖ ⥤ D)] [HasColimitsOfShape ℕ D]
  [HasExactColimitsOfShape ℕ D] in
/-- **`Stacks.ChaoticSite.restrict_colimConstAdj_unit` read on homotopy categories.** The unit of
`CategoryTheory.Adjunction.mapHomotopyCategory` is the quotient of the degreewise unit, and so is
the action of restriction on a quotient, so this is the previous statement under
`HomotopyCategory.quotient`. -/
theorem restrict_colimConstAdj_unit_mapHomotopyCategory
    (X : HomotopyCategory (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)) :
    (((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomotopyCategory
          (ComplexShape.up ℤ)).map
        (((colimConstAdj : (colim : (Cᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const Cᵒᵖ).mapHomotopyCategory
          (ComplexShape.up ℤ)).unit.app X) =
      ((colimConstAdj : (colim : (C'ᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const C'ᵒᵖ).mapHomotopyCategory
            (ComplexShape.up ℤ)).unit.app
          ((((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj X) ≫
        ((Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex (diagramColimitRestrictionPre f D)
              (ComplexShape.up ℤ)).app X.as)) :=
  (congrArg (HomotopyCategory.quotient (C'ᵒᵖ ⥤ D) (ComplexShape.up ℤ)).map
      (restrict_colimConstAdj_unit_mapHomologicalComplex f D X.as)).trans
    ((HomotopyCategory.quotient (C'ᵒᵖ ⥤ D) (ComplexShape.up ℤ)).map_comp _ _)

/-- **The unbounded comparison, pinned against an underived comparison.** Let `u` be a morphism
`π'_!(g^{-1}X) ⟶ π_!(X)` of homotopy categories through which restriction along `f` carries the
unit of `colim_{Cᵒᵖ} ⊣ const_{Cᵒᵖ}` at `X` to the unit of `colim_{C'ᵒᵖ} ⊣ const_{C'ᵒᵖ}` at
`g^{-1}X`. Then `u` computes the comparison `Stacks.ChaoticSite.unboundedComparison` at `Q_h X`,
after the comparison of `Lπ_!` with `π_!`.

Both sides have the same transpose along `Lπ'_! ⊣ π'^{-1}`, and the transpose is a bijection. The
hypothesis is the *only* thing used about `u`; stating the identity at a variable rather than at
the underived comparison itself is what keeps the composites in the proof type-correct for the
tactics that build them. -/
theorem unboundedComparison_app_comp_counit_of_unit
    (X : HomotopyCategory (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ))
    (u : ((colim : (C'ᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj X) ⟶
        ((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)
    (hu : (((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomotopyCategory
            (ComplexShape.up ℤ)).map
          (((colimConstAdj : (colim : (Cᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const Cᵒᵖ).mapHomotopyCategory
            (ComplexShape.up ℤ)).unit.app X) =
        ((colimConstAdj : (colim : (C'ᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const C'ᵒᵖ).mapHomotopyCategory
              (ComplexShape.up ℤ)).unit.app
            ((((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj X) ≫
          ((Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapHomotopyCategory
            (ComplexShape.up ℤ)).map u) :
    (unboundedComparison f D).app (DerivedCategory.Qh.obj X) ≫
        (totalDerivedColimitCounit C D).app X =
      (totalDerivedColimit C' D).map
          (((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategoryFactorsh.hom.app X) ≫
        (totalDerivedColimitCounit C' D).app
            ((((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj X) ≫
          DerivedCategory.Qh.map u := by
  -- the composition comparison of the derived constant diagrams, at an object of the homotopy
  -- category: the residue the two modules' notes named, now available
  have hcomp : (derivedConstRestrictionIso f D).hom.app
        (DerivedCategory.Qh.obj
          (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) =
      ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory.map
          ((Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.hom.app
            (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) ≫
        ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategoryFactorsh.hom.app
            (((Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj
              (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) ≫
          (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv.app
            (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj X) :=
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Qh
      (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)) ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op)
      (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)
  -- naturality of the comparison of `g^{-1}` with `DerivedCategory.Qh`
  have hnatf : ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory.map
          (DerivedCategory.Qh.map
            (((colimConstAdj : (colim : (Cᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const Cᵒᵖ).mapHomotopyCategory
              (ComplexShape.up ℤ)).unit.app X)) ≫
        ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategoryFactorsh.hom.app
          (((Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) =
      ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategoryFactorsh.hom.app X ≫
        DerivedCategory.Qh.map
          ((((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomotopyCategory
              (ComplexShape.up ℤ)).map
            (((colimConstAdj : (colim : (Cᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const Cᵒᵖ).mapHomotopyCategory
              (ComplexShape.up ℤ)).unit.app X)) :=
    ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategoryFactorsh.hom.naturality
      (((colimConstAdj : (colim : (Cᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const Cᵒᵖ).mapHomotopyCategory
        (ComplexShape.up ℤ)).unit.app X)
  -- naturality of the comparison of `π'^{-1}` with `DerivedCategory.Qh`, at `u`
  have hnatc : DerivedCategory.Qh.map
          (((Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapHomotopyCategory
            (ComplexShape.up ℤ)).map u) ≫
        (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv.app
          (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj X) =
      (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv.app
          (((colim : (C'ᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj X)) ≫
        (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategory.map
          (DerivedCategory.Qh.map u) :=
    (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv.naturality u
  -- naturality of the unit of `Lπ'_! ⊣ π'^{-1}`
  have hnatu : (totalDerivedColimitAdjunction C' D).unit.app
          (((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory.obj
            (DerivedCategory.Qh.obj X)) ≫
        (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategory.map
          ((totalDerivedColimit C' D).map
            (((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategoryFactorsh.hom.app
              X)) =
      ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategoryFactorsh.hom.app X ≫
        (totalDerivedColimitAdjunction C' D).unit.app
          (DerivedCategory.Qh.obj
            ((((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj X)) :=
    ((totalDerivedColimitAdjunction C' D).unit.naturality
      (((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategoryFactorsh.hom.app
        X)).symm
  -- the two copies of the comparison of the derived constant diagram on `C` cancel. The tail is
  -- kept abstract: the composite it stands for is well typed only at `default` transparency, so a
  -- tactic may not build it, while a variable of its type carries no spelling at all
  have hcan : ∀ w : ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory.obj
        (DerivedCategory.Qh.obj
          (((Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj X))) ⟶
        (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategory.obj
          (DerivedCategory.Qh.obj
            (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)),
      ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory.map
            (DerivedCategory.Qh.map
                (((colimConstAdj :
                      (colim : (Cᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const Cᵒᵖ).mapHomotopyCategory
                    (ComplexShape.up ℤ)).unit.app X) ≫
              (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv.app
                (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) ≫
          ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory.map
              ((Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.hom.app
                (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj X)) ≫
            w =
        ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory.map
            (DerivedCategory.Qh.map
              (((colimConstAdj : (colim : (Cᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const Cᵒᵖ).mapHomotopyCategory
                (ComplexShape.up ℤ)).unit.app X)) ≫
          w := by
    intro w
    rw [CategoryTheory.Functor.map_comp, Category.assoc,
      ← Category.assoc
        (((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory.map
          ((Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv.app _))
        (((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory.map
          ((Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.hom.app _)) w,
      ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  -- the tail, assembled in term mode
  have htail : DerivedCategory.Qh.map
          ((((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomotopyCategory
              (ComplexShape.up ℤ)).map
            (((colimConstAdj : (colim : (Cᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const Cᵒᵖ).mapHomotopyCategory
              (ComplexShape.up ℤ)).unit.app X)) ≫
        (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv.app
          (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj X) =
      DerivedCategory.Qh.map
          (((colimConstAdj : (colim : (C'ᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const C'ᵒᵖ).mapHomotopyCategory
              (ComplexShape.up ℤ)).unit.app
            ((((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj X)) ≫
        (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv.app
            (((colim : (C'ᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj
              ((((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj X)) ≫
          (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategory.map
            (DerivedCategory.Qh.map u) :=
    (congrArg
        (fun z => z ≫
          (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv.app
            (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj X))
        ((congrArg DerivedCategory.Qh.map hu).trans
          (DerivedCategory.Qh.map_comp _ _))).trans
      ((Category.assoc _ _ _).trans
        (congrArg
          (fun z => DerivedCategory.Qh.map
              (((colimConstAdj :
                    (colim : (C'ᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const C'ᵒᵖ).mapHomotopyCategory
                  (ComplexShape.up ℤ)).unit.app
                ((((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomotopyCategory
                  (ComplexShape.up ℤ)).obj X)) ≫ z)
          hnatc))
  -- the transpose of the left side
  have hA : (totalDerivedColimitAdjunction C' D).unit.app
          (((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory.obj
            (DerivedCategory.Qh.obj X)) ≫
        (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategory.map
          ((unboundedComparison f D).app (DerivedCategory.Qh.obj X) ≫
            (totalDerivedColimitCounit C D).app X) =
      ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategoryFactorsh.hom.app X ≫
        DerivedCategory.Qh.map
            (((colimConstAdj : (colim : (C'ᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const C'ᵒᵖ).mapHomotopyCategory
                (ComplexShape.up ℤ)).unit.app
              ((((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj X)) ≫
          (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv.app
              (((colim : (C'ᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj
                ((((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomotopyCategory
                  (ComplexShape.up ℤ)).obj X)) ≫
            (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategory.map
              (DerivedCategory.Qh.map u) := by
    refine (unit_comp_unboundedComparison_comp_counit f D X).trans ?_
    rw [hcomp]
    refine (hcan _).trans ((Category.assoc _ _ _).symm.trans ?_)
    refine (congrArg
      (fun z => z ≫ (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv.app
        (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj X))
      hnatf).trans ((Category.assoc _ _ _).trans ?_)
    exact congrArg
      (fun z => ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategoryFactorsh.hom.app
        X ≫ z) htail
  -- the transpose of the right side
  have hB : (totalDerivedColimitAdjunction C' D).unit.app
          (((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategory.obj
            (DerivedCategory.Qh.obj X)) ≫
        (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategory.map
          ((totalDerivedColimit C' D).map
              (((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategoryFactorsh.hom.app
                X) ≫
            (totalDerivedColimitCounit C' D).app
                ((((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomotopyCategory
                  (ComplexShape.up ℤ)).obj X) ≫
              DerivedCategory.Qh.map u) =
      ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategoryFactorsh.hom.app X ≫
        DerivedCategory.Qh.map
            (((colimConstAdj : (colim : (C'ᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const C'ᵒᵖ).mapHomotopyCategory
                (ComplexShape.up ℤ)).unit.app
              ((((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj X)) ≫
          (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv.app
              (((colim : (C'ᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj
                ((((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomotopyCategory
                  (ComplexShape.up ℤ)).obj X)) ≫
            (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategory.map
              (DerivedCategory.Qh.map u) := by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, ← Category.assoc,
      hnatu, Category.assoc, ← Category.assoc
        ((totalDerivedColimitAdjunction C' D).unit.app (DerivedCategory.Qh.obj _))
        ((Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).mapDerivedCategory.map
          ((totalDerivedColimitCounit C' D).app _)),
      totalDerivedColimitAdjunction_unit_app_comp_counit C' D
        ((((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj X), Category.assoc]
  exact ((totalDerivedColimitAdjunction C' D).homEquiv _ _).injective (hA.trans hB.symm)

/-- **The unbounded comparison composed with the derived-functor comparison is the underived
comparison.** At a complex `K` of diagrams on `C`, the comparison
`Stacks.ChaoticSite.unboundedComparison` at `Q_h K`, followed by the comparison of `Lπ_!` with
`π_!`, is the degreewise action of `Stacks.CategoryHomology.diagramColimitRestrictionPre` on `K`,
read after the comparison of `g^{-1}` with `DerivedCategory.Qh` and the comparison of `Lπ'_!` with
`π'_!`.

This is `Stacks.ChaoticSite.unboundedComparison_app_comp_counit_of_unit` at the underived
comparison, whose hypothesis is
`Stacks.ChaoticSite.restrict_colimConstAdj_unit_mapHomotopyCategory`. It is the identity that
turns [Stacks, Tag 08QA] on the unbounded derived category into the invertibility of the two
comparisons of `Lπ_!` with `π_!` and of the underived comparison. -/
theorem unboundedComparison_app_comp_counit
    (X : HomotopyCategory (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)) :
    (unboundedComparison f D).app (DerivedCategory.Qh.obj X) ≫
        (totalDerivedColimitCounit C D).app X =
      (totalDerivedColimit C' D).map
          (((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapDerivedCategoryFactorsh.hom.app X) ≫
        (totalDerivedColimitCounit C' D).app
            ((((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj X) ≫
          DerivedCategory.Qh.map
            ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
              ((NatTrans.mapHomologicalComplex (diagramColimitRestrictionPre f D)
                (ComplexShape.up ℤ)).app X.as)) :=
  unboundedComparison_app_comp_counit_of_unit f D X _
    (restrict_colimConstAdj_unit_mapHomotopyCategory f D X)

end Stacks.ChaoticSite

end
