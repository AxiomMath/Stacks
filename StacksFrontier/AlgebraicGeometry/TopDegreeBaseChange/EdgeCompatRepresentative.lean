module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EdgeCompatDerived
public import StacksFrontier.CategoryTheory.CompositeCancellation
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.RepresentativeHomology

/-!
# The two units against the cohomology edge morphism, at a representative complex

Let `adj : E ⊣ F` be an adjunction of additive functors of abelian categories, let `dadj : L ⊣ R`
be an adjunction of the unbounded derived categories, and suppose the two are compatible in the
sense that the unit of `dadj` at the class of a complex `P`, followed by `R` of the comparison
`L(Q P) ⟶ Q(E P)`, is `Q` of the degreewise unit `P ⟶ F(E P)` followed by the comparison
`F(Q -) ⟶ R(Q -)`. That hypothesis is [Stacks, Tag 079W] for the pullback–pushforward adjunction
of a morphism of ringed spaces,
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_unit_fac`.

This file proves the resulting identity on degree-`q` cohomology, **at a representative complex**:
the cohomology class of `P` in `K`, followed by `H^q` of the unit of `dadj`, by the cohomology edge
morphism `H^q(R -) ⟶ F(H^q -)` of
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedHomologyComparison`, and by `F`
of the comparison of `L K` with `E P` that the representative supplies, is the unit of `adj` at
`H^q P` followed by `F` of the right-exact comparison `E(H^q P) ⟶ H^q(E P)`.

That is the content of the compatibility of the top-degree pullback comparison of
[Stacks, Tag 0EX3] with the cohomology edge morphism of the derived direct image. The two
comparisons it equates are exactly the two whose cycle-level characterisations the geometric
consumer has: `Stacks.MapHomologyCycles.mapHomology` is what
`…TopDegreeBaseChange.representativeClass_comp_eq_mapHomology` computes the top-degree pullback
comparison to be, and the edge morphism is characterised by
`…HomologyComparison.homologyπ_comp_homologyComparison` at the cycle level — which is where
`Stacks.EdgeCompat.unit_homologyMap_comp_homologyComparison` matches them.

## Main results

* `Stacks.EdgeCompat.classOfRepresentative_comp_unit_comp_edge`: **the identity.**

## Implementation notes

*Everything is a term, and every junction is definitional.* The composites here run through eight
objects spelled as iterated applications of derived functors, and at almost every junction the two
neighbouring factors name the object they share by different — definitionally equal — terms:
`(R ⋙ H^q).obj X` against `H^q(R X)`, `(L ⋙ R).obj X` against `R(L X)`,
`(Q ⋙ H^q_B).obj X` against `H^q_B(Q X)`. Neither `rw`, nor `simp`, nor even `Category.assoc`
fires at such a junction: substituting for one factor of a composite does not change the object
the composite records between its two factors, so the rewritten term no longer matches the
lemma's pattern, in which that object is one variable. Term application, by contrast, unifies at
default transparency, so each step below is an application of one of the rearrangements of the
first section — all stated at variables of an abstract category, where the reassociation is
free — and the steps are joined by `Eq.trans`.

*`calc` cannot be used for the same reason.* A `calc` chain needs a `Trans` instance, which is
only available when the successive relations are at the **same** type; the first link here goes
from a morphism out of `HomologicalComplex.homology P q` to one out of
`(HomologicalComplex.homologyFunctor B c q).obj P`, and `Trans` does not see those as one type.
`Eq.trans` does.

*The degreewise unit and the compatibility of the two units are hypotheses.* The unit of
`CategoryTheory.Adjunction.mapHomologicalComplexAdjunction` has target
`(E.mapHomologicalComplex c ⋙ F.mapHomologicalComplex c).obj P`, and the unit of
`CategoryTheory.Adjunction.mapHomotopyCategoryAdjunction` at the class of `P` is `Q` of it; both
are the spelling this file does not use. They are supplied in **argument** position, where the
`rfl` is discharged at default transparency; this is the discipline
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/RepresentativeHomology.lean` records for the
comparison `L(Q P) ⟶ Q(E P)`, which is taken here as a family with one naturality square for the
same reason.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison
open Stacks.RepresentativeHomology

namespace Stacks.EdgeCompat

open DerivedCategory

universe vA uA vB uB

/-! ### The rearrangements, on variables -/

/-- Replacing a two-fold prefix by a two-fold composite. -/
theorem comp_comp_eq_comp₂ {C : Type*} [Category C] {X Y Y₁ Y' W : C} {a : X ⟶ Y} {m : Y ⟶ Y'}
    {a₁ : X ⟶ Y₁} {a₂ : Y₁ ⟶ Y'} (h : a ≫ m = a₁ ≫ a₂) (r : Y' ⟶ W) :
    a ≫ m ≫ r = a₁ ≫ a₂ ≫ r := by
  rw [← assoc, h, assoc]

/-- Replacing a two-fold segment inside a composite. -/
theorem comp_seg₂_eq {C : Type*} [Category C] {X Y₁ Y₂ Y₂' Z W : C} (a : X ⟶ Y₁) {m₁ : Y₁ ⟶ Y₂}
    {m₂ : Y₂ ⟶ Z} {n₁ : Y₁ ⟶ Y₂'} {n₂ : Y₂' ⟶ Z} (h : m₁ ≫ m₂ = n₁ ≫ n₂) (r : Z ⟶ W) :
    a ≫ m₁ ≫ m₂ ≫ r = a ≫ n₁ ≫ n₂ ≫ r := by
  rw [← assoc m₁, h, assoc]

/-- Cancelling a tail that composes to the identity. -/
theorem comp₃_tail_id {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ : C} (a : X₀ ⟶ X₁)
    (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (t₁ : X₃ ⟶ X₄) (t₂ : X₄ ⟶ X₅) (r : X₅ ⟶ X₃)
    (h : t₁ ≫ t₂ ≫ r = 𝟙 X₃) : (a ≫ b ≫ c ≫ t₁ ≫ t₂) ≫ r = a ≫ b ≫ c := by
  simp only [assoc]
  rw [h, comp_id]

/-- Expanding a known three-fold factorisation of the head of a composite. -/
theorem comp₃_expand {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ W : C} {a : X₀ ⟶ X₁}
    {b : X₁ ⟶ X₂} {m : X₂ ⟶ X₃} {cl : X₀ ⟶ X₃} (h : cl = a ≫ b ≫ m) (x : X₃ ⟶ X₄)
    (y : X₄ ⟶ X₅) {n : X₂ ⟶ X₅} (hn : m ≫ x ≫ y = n) (r : X₅ ⟶ W) :
    cl ≫ x ≫ y ≫ r = a ≫ b ≫ n ≫ r := by
  rw [h, ← hn]
  simp only [assoc]

/-- Replacing a five-fold prefix by one morphism. -/
theorem comp₅_eq {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ W : C} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂)
    (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (g : X₄ ⟶ X₅) {n : X₀ ⟶ X₅}
    (h : a ≫ b ≫ c ≫ d ≫ g = n) (r : X₅ ⟶ W) :
    a ≫ b ≫ c ≫ d ≫ g ≫ r = n ≫ r := by
  rw [← h]
  simp only [assoc]

/-- Replacing a two-fold segment in the third and fourth places of a composite. -/
theorem comp₂_seg₂_eq {C : Type*} [Category C] {X X' Y₁ Y₂ Y₂' Z W : C} (a : X ⟶ X')
    (b : X' ⟶ Y₁) {m₁ : Y₁ ⟶ Y₂} {m₂ : Y₂ ⟶ Z} {n₁ : Y₁ ⟶ Y₂'} {n₂ : Y₂' ⟶ Z}
    (h : m₁ ≫ m₂ = n₁ ≫ n₂) (r : Z ⟶ W) :
    a ≫ b ≫ m₁ ≫ m₂ ≫ r = a ≫ b ≫ n₁ ≫ n₂ ≫ r := by
  rw [← assoc m₁, h, assoc]

/-- Rewriting the tail of a composite. -/
theorem comp_tail_eq {C : Type*} [Category C] {X Y Z : C} (a : X ⟶ Y) {m m' : Y ⟶ Z}
    (h : m = m') : a ≫ m = a ≫ m' :=
  congrArg (fun z => a ≫ z) h

/-- Rewriting the tail of a composite past a two-fold prefix. -/
theorem comp_tail_eq₂ {C : Type*} [Category C] {X X' Y Z : C} (a : X ⟶ X') (b : X' ⟶ Y)
    {m m' : Y ⟶ Z} (h : m = m') : a ≫ b ≫ m = a ≫ b ≫ m' :=
  congrArg (fun z => a ≫ b ≫ z) h

/-- Rewriting the tail of a composite past a three-fold prefix. -/
theorem comp_tail_eq₃ {C : Type*} [Category C] {X X' X'' Y Z : C} (a : X ⟶ X') (b : X' ⟶ X'')
    (c : X'' ⟶ Y) {m m' : Y ⟶ Z} (h : m = m') : a ≫ b ≫ c ≫ m = a ≫ b ≫ c ≫ m' :=
  congrArg (fun z => a ≫ b ≫ c ≫ z) h

/-! ### The compatibility at a representative -/

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory B]
  {E : B ⥤ A} {F : A ⥤ B} [E.Additive] [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits E] (adj : E ⊣ F)
  {L : DerivedCategory B ⥤ DerivedCategory A} {R : DerivedCategory A ⥤ DerivedCategory B}
  (dadj : L ⊣ R)
  (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
  [R.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)
  (cmp : ∀ P : CochainComplex B ℤ,
    L.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P)) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))
  (q : ℤ)

/-- **The two units against the cohomology edge morphism, at a representative complex.** Let `P`
be a cochain complex with an identification `e` of its class in the derived category with `K`, let
`u : P ⟶ F(E P)` be the degreewise unit of `adj`, and suppose the unit of the derived adjunction
`dadj` agrees with `u` after the two comparisons (`hunit`). Then

> `class ≫ H^q(dadj.unit) ≫ edge ≫ F(comparison) = adj.unit ≫ F(mapHomology E P q)`,

the left-hand side reading the derived unit through the cohomology edge morphism of `R` and the
comparison of `L K` with `E P` that `P` supplies, and the right-hand side being the degreewise
unit followed by `F` of the comparison that the right exact `E` supplies.

The proof moves the identification `e` out of the way by the naturality of the derived unit and of
the edge morphism, applies `hunit`, replaces the edge morphism by the comparison it extends
(`…derivedHomologyComparison_fac_app`), reads that comparison at the complex
(`homotopyHomologyComparisonToDerived_app_quotient`), and matches the result with the right-hand
side by `unit_homologyMap_comp_homologyComparison`. The two factorisations of the cohomology
functor cancel against the ones inside `classOfRepresentative` and
`comparisonOfRepresentative`. -/
theorem classOfRepresentative_comp_unit_comp_edge
    (P : CochainComplex B ℤ) {K : DerivedCategory B}
    (e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P) ≅ K)
    (u : P ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    (hu : ∀ n : ℤ, u.f n = adj.unit.app (P.X n))
    (hunit : dadj.unit.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P)) ≫
        R.map (cmp P) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map u) ≫
        α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) :
    classOfRepresentative P e q ≫
        (homologyFunctor B q).map (dadj.unit.app K) ≫
        (derivedHomologyComparison F R α hres q).app (L.obj K) ≫
        F.map (comparisonOfRepresentative E L cmp P e q) =
      adj.unit.app (P.homology q) ≫ F.map (Stacks.MapHomologyCycles.mapHomology E P q) := by
  have hmor : e.hom ≫ dadj.unit.app K ≫ R.map (L.map e.inv) =
      dadj.unit.app
        (Qh.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P)) :=
    (congrArg (fun z => e.hom ≫ z) (dadj.unit.naturality e.inv).symm).trans
      (e.hom_inv_id_assoc _)
  have hmor2 : e.hom ≫ dadj.unit.app K ≫ R.map (L.map e.inv ≫ cmp P) =
      Qh.map ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map u) ≫
        α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
    ((congrArg (fun z => e.hom ≫ dadj.unit.app K ≫ z) (R.map_comp _ _)).trans
      (comp₃_prefix_eq _ _ _ hmor _)).trans hunit
  have hfold : (homologyFunctor B q).map e.hom ≫
        (homologyFunctor B q).map (dadj.unit.app K) ≫
        (homologyFunctor B q).map (R.map (L.map e.inv ≫ cmp P)) =
      (homologyFunctor B q).map
          (Qh.map ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map u)) ≫
        (homologyFunctor B q).map
          (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) :=
    ((((homologyFunctor B q).map_comp _ _).trans
            (congrArg (fun z => (homologyFunctor B q).map e.hom ≫ z)
              ((homologyFunctor B q).map_comp _ _))).symm.trans
          (congrArg (fun w => (homologyFunctor B q).map w) hmor2)).trans
      ((homologyFunctor B q).map_comp _ _)
  have hedge : (derivedHomologyComparison F R α hres q).app (L.obj K) ≫
        F.map (comparisonOfRepresentative E L cmp P e q) =
      (homologyFunctor B q).map (R.map (L.map e.inv ≫ cmp P)) ≫
        (derivedHomologyComparison F R α hres q).app
          (Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
        F.map ((homologyFunctorFactorsh A q).hom.app
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
                ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
            (HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) q).hom.app
              ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
    (comp_tail_eq _ (F.map_comp _ _)).trans
      (comp_comp_eq_comp₂
        ((derivedHomologyComparison F R α hres q).naturality (L.map e.inv ≫ cmp P)).symm _)
  have htail : F.map ((HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) q).inv.app
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        F.map ((homologyFunctorFactorsh A q).inv.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
        F.map ((homologyFunctorFactorsh A q).hom.app
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
              ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
          (HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) q).hom.app
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) = 𝟙 _ :=
    by rw [← F.map_comp, ← F.map_comp, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, F.map_id]
  have hmid := derivedHomologyComparison_fac_app F R α hres q
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
  have hstep4 : (homotopyHomologyComparisonToDerived F q).app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        F.map ((homologyFunctorFactorsh A q).hom.app
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
              ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
          (HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) q).hom.app
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) =
      (homologyFunctorFactorsh B q).hom.app
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
        (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) q).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        homologyComparison F ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) q :=
    (congrArg (fun z => z ≫ F.map ((homologyFunctorFactorsh A q).hom.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        (HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) q).hom.app
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))
      (homotopyHomologyComparisonToDerived_app_quotient F q
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))).trans
      (comp₃_tail_id _ _ _ _ _ _ htail)
  have hhead : (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) q).inv.app P ≫
        (homologyFunctorFactorsh B q).inv.app
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj P) ≫
        (homologyFunctor B q).map
          (Qh.map ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map u)) ≫
        (homologyFunctorFactorsh B q).hom.app
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
        (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) q).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) =
      HomologicalComplex.homologyMap u q :=
    ((comp₂_seg₂_eq _ _ ((homologyFunctorFactorsh B q).hom.naturality
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map u)) _).trans
        (comp_tail_eq _
          (comp_cancel_id ((homologyFunctorFactorsh B q).inv_hom_id_app _) _))).trans
      ((comp_tail_eq _
          ((HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) q).hom.naturality
            u)).trans
        (comp_cancel_id
          ((HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) q).inv_hom_id_app P) _))
  exact (comp_tail_eq₂ _ _ hedge).trans
    ((comp₃_expand rfl _ _ hfold _).trans
      ((comp_tail_eq₂ _ _ (assoc _ _ _)).trans
        ((comp_tail_eq₃ _ _ _ (comp_comp_eq_comp hmid _)).trans
          ((comp_tail_eq₃ _ _ _ hstep4).trans
            ((comp₅_eq _ _ _ _ _ hhead _).trans
              (unit_homologyMap_comp_homologyComparison adj P u hu q))))))

end Stacks.EdgeCompat

end
