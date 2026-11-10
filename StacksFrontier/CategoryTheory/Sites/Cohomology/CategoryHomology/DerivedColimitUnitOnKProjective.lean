module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.DerivedColimitOnKProjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.DerivedColimitOnKProjectiveQuotient

/-!
# The unit of the derived lower-shriek adjunction at a K-projective complex

Let `C` be a small category with the chaotic topology and `D` abelian coefficients with enough
projectives in `Cᵒᵖ ⥤ D`, so that derived lower shriek `Lπ_!` of [Stacks, Tag 08Q6] exists and is
left adjoint to the derived constant diagram
(`Stacks.CategoryHomology.totalDerivedColimitAdjunction`).  The unit of that adjunction is
*defined* as a lift through the universal property of the left derived functor, and the only
identity it satisfies by construction is
`Stacks.CategoryHomology.totalDerivedColimitAdjunction_unit_app_comp_counit`, which computes the
unit followed by the derived constant diagram of the derived-functor comparison.

This file solves that identity for the unit itself wherever the comparison is invertible, which by
`Stacks.Homology.isIso_leftDerivedCounit_app_of_isKProjective` is the case at every K-projective
complex, hence at a projective diagram placed in degree zero.  So at the compact generators of a
dévissage of `D(Cᵒᵖ ⥤ D)` the derived unit is the *underived* unit of `colim ⊣ const`, read
through the comparison of the derived constant diagram with its degreewise action and through the
inverse of the derived-functor comparison.

## Main results

* `Stacks.CategoryHomology.isIso_totalDerivedColimitCounit_app_quotient_of_isKProjective`: the
  derived-functor comparison of `Lπ_!` is invertible at a K-projective complex.
* `Stacks.CategoryHomology.totalDerivedColimitAdjunction_unit_app_of_isIso_counit`: **the derived
  unit, computed outright** wherever that comparison is invertible.
* `Stacks.CategoryHomology.totalDerivedColimitAdjunction_unit_app_single`: the same at a
  projective diagram placed in degree zero -- the shape the generators of the dévissage have.
* `Stacks.CategoryHomology.totalDerivedColimitAdjunction_unit_app_Q_single`: the same statement
  carried over to `DerivedCategory.Q`, read through
  `Stacks.CategoryHomology.totalDerivedColimitObjSingleIso`: the derived unit at `G[0]` for a
  projective `G` is `Q` of the underived unit of `colim ⊣ const`.

## Implementation notes

The first three statements are made at `DerivedCategory.Qh`, where the computation is three
rewrites, and `Stacks.CategoryHomology.totalDerivedColimitAdjunction_unit_app_Q_single` transports
the last of them to `DerivedCategory.Q` along `DerivedCategory.quotientCompQhIso`.  That transport
is not a rewrite, because the identity it produces is well typed only up to definitional
unfolding: `const_*(quotient M)` and `quotient(const_* M)` are two spellings of one object, so
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` and
`CategoryTheory.Functor.mapDerivedCategoryFactors` cannot be composed by a tactic -- `rw` and
`simp` report the target as not type-correct at `implicit` transparency, exactly as recorded in
`StacksFrontier/CategoryTheory/Sites/Cohomology/ChaoticSite/DerivedColimitUnboundedPinning.lean`.

The transport proceeds in four legs.  Cancelling `DerivedCategory.quotientCompQhIso` on the left
and applying naturality of the unit and of that comparison puts both sides in the image of
`DerivedCategory.Qh`.  On the left
`Stacks.CategoryHomology.map_quotientCompQhIso_hom_comp_totalDerivedColimitObjSingleIso_hom`
exposes the derived-functor comparison, which
`Stacks.CategoryHomology.totalDerivedColimitAdjunction_unit_app_comp_counit` evaluates; on the
right
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso_hom`
read backwards -- as an iso cancellation, not as a rewrite -- exchanges the two factorizations of
the derived constant diagram.  What is left is an identity of `DerivedCategory.Qh`-images, hence
of morphisms of the homotopy category, hence of morphisms of complexes, where the unit of
`CategoryTheory.Adjunction.mapHomotopyCategory` is a `HomotopyCategory.quotient`-image of the
degreewise unit and the degreewise identity is checked in each degree.

Every leg that meets the seam is assembled from `Eq.trans`, `congrArg` with hand-written motives
and `CategoryTheory.Category.assoc` as *terms*, which elaborate at `default` transparency; the
same technique as in
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso_hom`
itself.

The last step of `Stacks.CategoryHomology.totalDerivedColimitAdjunction_unit_app_of_isIso_counit`
is `CategoryTheory.Category.comp_id` used as a *term*: the identity it cancels sits at
`(Lπ_! ⋙ const_*)(Q_h X)` while the unit's target is spelled `const_*(Lπ_!(Q_h X))`, and the
keyed matching of `rw` does not cross that.

## References

* [Stacks Project, Tag 08Q6](https://stacks.math.columbia.edu/tag/08Q6)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe uD vD u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.CategoryHomology

variable (C : Type u) [SmallCategory C] (D : Type uD) [Category.{vD} D] [Abelian D]
  [EnoughProjectives (Cᵒᵖ ⥤ D)] [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D]
  [HasColimitsOfShape Cᵒᵖ D]

/-- **The derived-functor comparison of `Lπ_!` is invertible at a K-projective complex.**  This is
`Stacks.Homology.isIso_leftDerivedCounit_app_of_isKProjective` read for derived lower shriek. -/
theorem isIso_totalDerivedColimitCounit_app_quotient_of_isKProjective
    (P : CochainComplex (Cᵒᵖ ⥤ D) ℤ) [P.IsKProjective] :
    IsIso ((totalDerivedColimitCounit C D).app
      ((HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).obj P)) :=
  have := colim_hasPointwiseLeftDerivedFunctor C D
  have := totalDerivedColimit_isLeftDerivedFunctor C D
  Stacks.Homology.isIso_leftDerivedCounit_app_of_isKProjective
    (totalDerivedColimit C D) (totalDerivedColimitCounit C D) P

/-- **The unit of the derived lower-shriek adjunction, computed outright** at an object of the
derived category coming from the homotopy category at which the derived-functor comparison of
`Lπ_!` is invertible: it is the unit of `colim ⊣ const` on homotopy categories, followed by the
comparison of the derived constant diagram with its degreewise action and by the derived constant
diagram of the inverse of the comparison.

`Stacks.CategoryHomology.totalDerivedColimitAdjunction_unit_app_comp_counit` is the only identity
the derived unit satisfies by construction; this is that identity solved for the unit, which is
possible exactly where the comparison is invertible. -/
theorem totalDerivedColimitAdjunction_unit_app_of_isIso_counit
    (X : HomotopyCategory (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ))
    [IsIso ((totalDerivedColimitCounit C D).app X)] :
    (totalDerivedColimitAdjunction C D).unit.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map
          (((colimConstAdj : (colim : (Cᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const Cᵒᵖ).mapHomotopyCategory
            (ComplexShape.up ℤ)).unit.app X) ≫
        (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv.app
            (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj X) ≫
          (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategory.map
            (CategoryTheory.inv ((totalDerivedColimitCounit C D).app X)) := by
  rw [← Category.assoc, ← totalDerivedColimitAdjunction_unit_app_comp_counit, Category.assoc,
    ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm

/-- **The unit of the derived lower-shriek adjunction at a projective diagram placed in degree
zero.**  A projective object in degree zero is a K-projective complex
(`Stacks.Homology.isKProjective_single`), so the derived-functor comparison is invertible there and
`Stacks.CategoryHomology.totalDerivedColimitAdjunction_unit_app_of_isIso_counit` applies.  This is
the shape the compact generators `j_{U!}P` of a dévissage of `D(Cᵒᵖ ⥤ D)` have. -/
theorem totalDerivedColimitAdjunction_unit_app_single (G : Cᵒᵖ ⥤ D) [Projective G] :
    letI := Stacks.Homology.isKProjective_single (A := Cᵒᵖ ⥤ D) G
    letI := isIso_totalDerivedColimitCounit_app_quotient_of_isKProjective C D
      ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj G)
    (totalDerivedColimitAdjunction C D).unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj G))) =
      DerivedCategory.Qh.map
          (((colimConstAdj : (colim : (Cᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const Cᵒᵖ).mapHomotopyCategory
            (ComplexShape.up ℤ)).unit.app
            ((HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj G))) ≫
        (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv.app
            (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj
              ((HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).obj
                ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj G))) ≫
          (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategory.map
            (CategoryTheory.inv ((totalDerivedColimitCounit C D).app
              ((HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).obj
                ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj G)))) :=
  let := Stacks.Homology.isKProjective_single (A := Cᵒᵖ ⥤ D) G
  let := isIso_totalDerivedColimitCounit_app_quotient_of_isKProjective C D
    ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj G)
  totalDerivedColimitAdjunction_unit_app_of_isIso_counit C D _

omit [EnoughProjectives (Cᵒᵖ ⥤ D)] [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D] in
/-- The underived unit of `colim ⊣ const` at a diagram placed in degree zero, read degreewise on
complexes: the degreewise unit at `G[0]`, followed by the constant diagram of the identification
of `colim` applied degreewise to `G[0]` with `colim G` placed in degree zero, is `G[0] ⟶
(colim G)[0]` of the unit itself, followed by the same identification for `const` read
backwards. -/
private lemma mapHomologicalComplex_colimConstAdj_unit_app_single (G : Cᵒᵖ ⥤ D) :
    (NatTrans.mapHomologicalComplex
            (colimConstAdj : (colim : (Cᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const Cᵒᵖ).unit
            (ComplexShape.up ℤ)).app
          ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj G) ≫
        ((Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex
            (colim : (Cᵒᵖ ⥤ D) ⥤ D) (ComplexShape.up ℤ) 0).app G).hom =
      (HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).map
          (colimConstAdj.unit.app G) ≫
        ((HomologicalComplex.singleMapHomologicalComplex
          (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)) (ComplexShape.up ℤ) 0).app (colimit G)).inv := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  by_cases hn : n = 0
  · subst hn
    simp [HomologicalComplex.single_map_f_self,
      reassoc_of% (colimConstAdj.unit.naturality
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).hom)]
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 G n hn).eq_of_src _ _

omit [EnoughProjectives (Cᵒᵖ ⥤ D)] [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D] in
/-- `Stacks.CategoryHomology.mapHomologicalComplex_colimConstAdj_unit_app_single` read on the
homotopy categories: the unit of `CategoryTheory.Adjunction.mapHomotopyCategory` and the action of
`CategoryTheory.Functor.mapHomotopyCategory` are both `HomotopyCategory.quotient`-images of the
degreewise data, so this is the degreewise identity under the quotient. -/
private lemma quotient_colimConstAdj_unit_app_single (G : Cᵒᵖ ⥤ D) :
    ((colimConstAdj : (colim : (Cᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const Cᵒᵖ).mapHomotopyCategory
            (ComplexShape.up ℤ)).unit.app
          ((HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj G)) ≫
        ((Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
            ((HomologicalComplex.singleMapHomologicalComplex
              (colim : (Cᵒᵖ ⥤ D) ⥤ D) (ComplexShape.up ℤ) 0).app G).hom) =
      (HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).map
        ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).map
            (colimConstAdj.unit.app G) ≫
          ((HomologicalComplex.singleMapHomologicalComplex
            (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)) (ComplexShape.up ℤ) 0).app (colimit G)).inv) := by
  refine (congrArg (_ ≫ ·) (Functor.mapHomotopyCategory_map (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D))
    ((HomologicalComplex.singleMapHomologicalComplex
      (colim : (Cᵒᵖ ⥤ D) ⥤ D) (ComplexShape.up ℤ) 0).app G).hom)).trans ?_
  exact ((HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).map_comp _ _).symm.trans
    (congrArg (HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).map
      (mapHomologicalComplex_colimConstAdj_unit_app_single C D G))

omit [EnoughProjectives (Cᵒᵖ ⥤ D)] [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D] in
/-- `Stacks.CategoryHomology.quotient_colimConstAdj_unit_app_single` read in the derived category:
the derived constant diagram of `DerivedCategory.Qh` of the identification of `colim` applied
degreewise to `G[0]` with `colim G` placed in degree zero is moved across
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` by its naturality, and the two
`DerivedCategory.Qh`-images that meet there are the homotopy-category identity. -/
private lemma qh_colimConstAdj_unit_app_single_comp_mapDerivedCategoryFactorsh_inv
    (G : Cᵒᵖ ⥤ D) :
    DerivedCategory.Qh.map
          (((colimConstAdj : (colim : (Cᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const Cᵒᵖ).mapHomotopyCategory
            (ComplexShape.up ℤ)).unit.app
            ((HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj G))) ≫
        (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv.app
            (((colim : (Cᵒᵖ ⥤ D) ⥤ D).mapHomotopyCategory (ComplexShape.up ℤ)).obj
              ((HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).obj
                ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj G))) ≫
          (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategory.map
            (DerivedCategory.Qh.map
              ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
                ((HomologicalComplex.singleMapHomologicalComplex
                  (colim : (Cᵒᵖ ⥤ D) ⥤ D) (ComplexShape.up ℤ) 0).app G).hom)) =
      DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).map
            ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).map
                (colimConstAdj.unit.app G) ≫
              ((HomologicalComplex.singleMapHomologicalComplex
                (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)) (ComplexShape.up ℤ) 0).app
                (colimit G)).inv)) ≫
        (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).obj (colimit G))) := by
  have hnat := ((Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv.naturality
    ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (colim : (Cᵒᵖ ⥤ D) ⥤ D) (ComplexShape.up ℤ) 0).app G).hom)).symm
  refine (congrArg (DerivedCategory.Qh.map _ ≫ ·) hnat).trans ((Category.assoc _ _ _).symm.trans ?_)
  exact congrArg (· ≫ _) ((DerivedCategory.Qh.map_comp _ _).symm.trans
    (congrArg DerivedCategory.Qh.map (quotient_colimConstAdj_unit_app_single C D G)))

omit [EnoughProjectives (Cᵒᵖ ⥤ D)] [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D] in
open Stacks.DerivedCategoryComparisons in
/-- The right-hand side of
`Stacks.CategoryHomology.totalDerivedColimitAdjunction_unit_app_Q_single`, rewritten at
`DerivedCategory.Qh`: the degreewise identification of the constant diagram is absorbed into the
`DerivedCategory.Qh`-image by naturality of `DerivedCategory.quotientCompQhIso`, and the two
factorizations of the derived constant diagram are exchanged by
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso_hom`
read backwards. -/
private lemma rhs_leg_of_unit_app_Q_single (G : Cᵒᵖ ⥤ D) :
    DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).map
            ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).map
              (colimConstAdj.unit.app G))) ≫
        (DerivedCategory.quotientCompQhIso (Cᵒᵖ ⥤ D)).hom.app
            ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj
              ((Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).obj (colimit G))) ≫
          DerivedCategory.Q.map
              ((HomologicalComplex.singleMapHomologicalComplex
                (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)) (ComplexShape.up ℤ) 0).app (colimit G)).inv ≫
            (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategoryFactors.inv.app
              ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).obj (colimit G)) =
      DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).map
            ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).map
                (colimConstAdj.unit.app G) ≫
              ((HomologicalComplex.singleMapHomologicalComplex
                (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)) (ComplexShape.up ℤ) 0).app
                (colimit G)).inv)) ≫
        (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.inv.app
            ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).obj (colimit G))) ≫
          (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategory.map
            ((DerivedCategory.quotientCompQhIso D).hom.app
              ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).obj (colimit G))) := by
  have hnat := ((DerivedCategory.quotientCompQhIso (Cᵒᵖ ⥤ D)).hom.naturality
    ((HomologicalComplex.singleMapHomologicalComplex
      (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)) (ComplexShape.up ℤ) 0).app (colimit G)).inv).symm
  have h0 := mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso_hom
    (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D))
    ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).obj (colimit G))
  have hbridge := (Iso.comp_inv_eq
      ((Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategoryFactors.app
        ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).obj (colimit G)))).mpr
    (((Iso.eq_inv_comp
          ((Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategoryFactorsh.app
            ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).obj (colimit G))))).mpr
        h0).trans (Category.assoc _ _ _).symm)
  have hmap := (congrArg DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).map_comp
        ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).map
          (colimConstAdj.unit.app G))
        ((HomologicalComplex.singleMapHomologicalComplex
          (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)) (ComplexShape.up ℤ) 0).app
          (colimit G)).inv)).trans (DerivedCategory.Qh.map_comp _ _)
  have htail := ((reassoc_of% hnat)
      ((Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategoryFactors.inv.app
        ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).obj (colimit G)))).trans
    (congrArg (DerivedCategory.Qh.map _ ≫ ·) hbridge)
  exact (congrArg (DerivedCategory.Qh.map _ ≫ ·) htail).trans ((reassoc_of% hmap) _).symm

/-- **The unit of the derived lower-shriek adjunction at a projective diagram placed in degree
zero, read at `DerivedCategory.Q`.**  Composed with the derived constant diagram of the
computation `Stacks.CategoryHomology.totalDerivedColimitObjSingleIso` of `Lπ_!` there, the derived
unit is `DerivedCategory.Q` of the *underived* unit of `colim ⊣ const` placed in degree zero,
followed by the two comparisons that identify the degreewise constant diagram of `(colim G)[0]`
with the derived constant diagram of it.

This is `Stacks.CategoryHomology.totalDerivedColimitAdjunction_unit_app_single` transported from
`DerivedCategory.Qh` to `DerivedCategory.Q`; the implementation notes of this file describe the
transport. -/
theorem totalDerivedColimitAdjunction_unit_app_Q_single (G : Cᵒᵖ ⥤ D) [Projective G] :
    (totalDerivedColimitAdjunction C D).unit.app
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj G)) ≫
        (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategory.map
          (totalDerivedColimitObjSingleIso C D G).hom =
      DerivedCategory.Q.map
          ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).map
            (colimConstAdj.unit.app G)) ≫
        DerivedCategory.Q.map
            ((HomologicalComplex.singleMapHomologicalComplex
              (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)) (ComplexShape.up ℤ) 0).app (colimit G)).inv ≫
          (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategoryFactors.inv.app
            ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).obj (colimit G)) := by
  have := Stacks.Homology.isKProjective_single (A := Cᵒᵖ ⥤ D) G
  have := isIso_totalDerivedColimitCounit_app_quotient_of_isKProjective C D
    ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj G)
  rw [← Iso.cancel_iso_hom_left ((DerivedCategory.quotientCompQhIso (Cᵒᵖ ⥤ D)).app
    ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj G))]
  simp only [Iso.app_hom, ← Category.assoc]
  rw [← (totalDerivedColimitAdjunction C D).unit_naturality,
    ← (DerivedCategory.quotientCompQhIso (Cᵒᵖ ⥤ D)).hom.naturality]
  simp only [Functor.comp_obj, Functor.comp_map]
  rw [Category.assoc, ← Functor.map_comp,
    map_quotientCompQhIso_hom_comp_totalDerivedColimitObjSingleIso_hom, Functor.map_comp,
    reassoc_of% (totalDerivedColimitAdjunction_unit_app_comp_counit C D
      ((HomotopyCategory.quotient (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (Cᵒᵖ ⥤ D) (ComplexShape.up ℤ) 0).obj G)))]
  simp only [Category.assoc]
  refine (congrArg (_ ≫ _ ≫ ·)
    ((congrArg (Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategory.map
        (((DerivedCategory.quotientCompQhIso D).hom.naturality
          ((HomologicalComplex.singleMapHomologicalComplex
            (colim : (Cᵒᵖ ⥤ D) ⥤ D) (ComplexShape.up ℤ) 0).app G).hom).symm)).trans
      ((Functor.const Cᵒᵖ : D ⥤ (Cᵒᵖ ⥤ D)).mapDerivedCategory.map_comp _ _))).trans ?_
  refine ((reassoc_of%
      (qh_colimConstAdj_unit_app_single_comp_mapDerivedCategoryFactorsh_inv C D G)) _).trans ?_
  exact (rhs_leg_of_unit_app_Q_single C D G).symm

end Stacks.CategoryHomology

end

