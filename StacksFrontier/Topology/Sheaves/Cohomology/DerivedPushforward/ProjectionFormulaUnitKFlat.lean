module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComplexCoherence

/-!
# The right-unitor coherence of [Stacks, Tag 079U], and [Stacks, Tag 08EU] at `K = 𝒪_Y[0]`

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  This file discharges the
right-unitor coherence of the comparison of [Stacks, Tag 079U] — the last hypothesis of the base
case of [Stacks, Tag 08EU] — and with it proves that base case unconditionally.

`Stacks.Cohomology.DerivedProjectionFormula.rightUnitorCoherence_of_kFlat` had reduced the
coherence to its value at `QK` for a **K-flat** complex `K`, and
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso_rightUnitor` proves the
corresponding statement **at the level of complexes**, with no hypothesis.  What was missing was
the localization bridge between the two.  This file is that bridge.

## Main results

* `Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso`: the canonical unit
  comparison `ν : Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]`, built from `Lf^*(QM) ⟶ Q(f^*M)` at the K-flat complex
  `𝒪_Y[0]` and the complex-level unit comparison of `f^*`.  This is the `ν` the complex-level
  coherence is stated with, hence the one at which the coherence below is provable.
* `Stacks.Cohomology.DerivedProjectionFormula.rightUnitorCoherence_app_q_of_kFlat`: **the
  right-unitor coherence at a K-flat representative** — the hypothesis `h` of
  `rightUnitorCoherence_of_kFlat`, discharged.  This is the shared lemma: it is what both
  [Stacks, Tag 0B54] and [Stacks, Tag 0GM7] need.
* `Stacks.Cohomology.DerivedProjectionFormula.rightUnitorCoherence_unitObject`: the same
  coherence at **every** object of `D(𝒪_Y)`, with no hypothesis — the `hcoh` of
  `isIso_projectionFormulaMap_unitObject`.
* `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject_unconditional`:
  **[Stacks, Tag 08EU] at `K = 𝒪_Y[0]`, with no hypothesis at all.**

## Which right unitor this is about

The library carries **two** right unit constraints for `⊗^𝐋_{𝒪_Z}` with no identification
between them proved anywhere:
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso` (pointwise, read on a ringed
space as `Stacks.RingedSpace.derivedTensorRightUnitIso`) and
`…DerivedTensorProduct.rightUnitorNatIso` (natural, read as
`Stacks.RingedSpace.derivedTensorRightUnitorNatIso`).

Everything here is about the **natural** one, `rightUnitorNatIso`.  That is forced, not chosen:
the reduction `rightUnitorCoherence_of_kFlat` consumes the naturality of the unitor on both `X`
and `Y`, and the pointwise isomorphism carries none.  It is also what makes the computation
possible, since `…rightUnitorNatIso_hom_app_q` evaluates the natural unitor at an image `QK`
and the pointwise one has no such formula.  A consumer holding `rightUnitIso` instead cannot use
these statements until that identification is proved; it is not proved below.

## How the bridge works, and what it did not need

The chain is: at a K-flat `K` the comparison of [Stacks, Tag 079U] is
`Stacks.Cohomology.DerivedPullbackTensor.modelComparison`
(`pullbackTensorComparison_app_q_of_kFlat`), which is the left comparison followed by the
**inverse** of the right one.  The two are discharged separately — `leftComparison_comp_rho` and
`whiskerUnit_rightUnitor_comp_natTrans` — and what glues them is that the comparison
`Lf^*(QK) ⟶ Q(f^*K)` is invertible at a K-flat `K`
(`Stacks.Cohomology.DerivedPullbackTensor.isIso_derivedPullbackNatTrans_app`), which is the only
place K-flatness of `K` is used.  The complex-level coherence enters at exactly one point,
`whiskerUnit_comp_rightUnitor_q`.

**Three of the four identifications that the note on `rightUnitorCoherence_of_kFlat` listed as
owed are not needed, because they hold by `rfl`.**  That note is wrong on this point, and it
mattered: the first of them was described there as something that "must be pushed through both
slots of the comparison by its bifunctorial naturality", which would have been a substantial
construction.  In fact

* `singleUnit Y = DerivedCategory.Q.obj (unitComplex …)` by `rfl` — this is Mathlib's
  `DerivedCategory.Q_obj_single_obj`, and `DerivedCategory.singleFunctorIsoCompQ`, which the note
  proposed transporting along, is literally `Iso.refl`;
* `𝟙_ (CochainComplex …) = unitComplex …` by `rfl`;
* `(tensorComplexRightUnitorNatIso …).app K |>.hom = (ρ_ K).hom` by `rfl`
  (`tensorComplexRightUnitorNatIso_app_hom` below).

So only the fourth — specializing `ν`, which `derivedPullbackUnitIso` does — was real work, and
the remaining difficulty was not mathematical but the seam described next.

## Implementation notes

**Two spellings of the structure sheaf, and what they cost.**  The structure sheaf of a ringed
space is `TopCat.Sheaf CommRingCat X.carrier`, while the derived tensor product is indexed by a
`CategoryTheory.Sheaf` for the canonical topology.  The two are the same type, but `TopCat.Sheaf`
is a `def`, so a goal mentioning both is not type-correct at `implicit` transparency: `rw` reports
that it cannot find a pattern the goal visibly contains, and `dsimp` silently does nothing.  The
`attribute [local implicit_reducible] TopCat.Sheaf` below is what makes the rewrites of this file
fire at all.  Where even that is not enough, the step is supplied as a **generic lemma applied by
unification** with every object a variable — `map_map_inv_cancel`, `assoc_middle`,
`assoc_map_comp₃`, `uncurry_whisker_merge` — which is the move this directory prescribes for the
seams of a composite.

**No enlarged heartbeat budget.**  `uncurry_whisker_merge` exists for this reason.  Done inline,
its step is `rw [Functor.map_comp]` against a functor built from the derived tensor product, the
derived pullback and `Functor.uncurry`, and matching `?F.map (?a ≫ ?b)` there exhausts the
default budget inside `isDefEq`; pinning the functor explicitly does not help, because the
metavariables remain.  Against the rigid left-hand side of that lemma the same step is immediate.

## What this does *not* finish

In `Stacks.Cohomology.ProjectionFormulaPerfect`, the theorem
`isIso_projectionFormulaMap_of_isStrictlyPerfect_of_singleUnit`
asks its `hunit` for invertibility at `𝒪_Y[i]` for **every** `i : ℤ`, not only at `i = 0`.  The
base case proved here is the `i = 0` case, so it does not on its own discharge that `hunit`.
What is still owed there is the passage from `𝒪_Y[0]` to `𝒪_Y[i]`, which is a shift statement —
`𝒪_Y[i] ≅ 𝒪_Y[0]⟦-i⟧` is `…singleUnitShiftIso` — and not a unitor statement; nothing in this
file bears on it.

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPQ](https://stacks.math.columbia.edu/tag/0FPQ)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedProjectionFormula

open Stacks.Cohomology.DerivedPullbackTensor in
attribute [local instance] monoidalModules symmetricModules monoidalPreadditiveModules
  monoidalClosedModules hasTensorModules monoidalComplexes
  modulePullback_preservesAntidiagonalCoproducts abelianModulesSheafTensor liftMonoidal

-- The structure sheaf of a ringed space is named `TopCat.Sheaf CommRingCat X.carrier`, while the
-- derived tensor product is indexed by a `CategoryTheory.Sheaf` for the canonical topology.  The
-- two are the same type, but `TopCat.Sheaf` is a `def`, so a goal mentioning both is not
-- type-correct at `implicit` transparency; without this attribute `rw [Category.assoc]` reports
-- that it cannot find the pattern `?f ≫ ?g ≫ ?h` that the goal visibly contains, and `dsimp`
-- silently does nothing.
-- `structureSheafRing` is `@[instance_reducible]`, so it unfolds at `implicit` transparency
-- already, and its reduct stops at an explicit-constructor projection;
-- `Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf` — the spelling the derived tensor product is
-- named at — is semireducible and reduces to a constructor over `X.sheaf.obj ⋙ forget₂ _ _`.
-- That definition and the last two Mathlib ones are the gap between the two spellings, and
-- without all three the two `instCategoryDerivedCategory` instances on `D(𝒪_X)` are not
-- recognised as equal.
attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing
  StacksDraft.KFlat.modulePullback CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

attribute [local instance] HasDerivedCategory.standard

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Cancelling an isomorphism against its inverse under two successive functors, in arbitrary
categories.  Stated generically and applied by unification: at the objects below the composite
crosses two spellings of the structure sheaf of `X`, and there `rw [Category.assoc]` reports
that it cannot find the pattern `?f ≫ ?g ≫ ?h` that the goal visibly contains. -/
private lemma map_map_inv_cancel {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) {A B : C} (e : A ⟶ B) [IsIso e] {Z : E}
    (k : G.obj (F.obj B) ⟶ Z) :
    G.map (F.map (inv e)) ≫ G.map (F.map e) ≫ k = k := by
  rw [← Category.assoc, ← G.map_comp, ← F.map_comp, IsIso.inv_hom_id, F.map_id, G.map_id,
    Category.id_comp]

omit [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] in
open Stacks.Cohomology.DerivedPullbackTensor in
/-- The K-flatness of `f^*𝒪_Y[0]`. -/
private theorem kFlat_pullback_unit :
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat X
      ((pullbackComplex f).obj (unitComplex (Stacks.RingedSpace.toRingedSite Y))) :=
  Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional f _
    (Stacks.SheafOfModules.isKFlat_single_unit (Stacks.RingedSpace.toRingedSite Y).O)

open Stacks.Cohomology.DerivedPullbackTensor in
/-- **Naturality of the right K-flat comparison along the unit comparison of `f^*`.**  This is
the `comparisonRight_naturality` field at the identity of `A` and at `ε`, whose left factor
collapses; both `𝒪_X[0]` and `f^*𝒪_Y[0]` are K-flat, so both comparisons exist. -/
private theorem comparisonRight_comp_whiskerLeft_epsilon
    (A : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) :
    ((canonicalDerivedTensorProduct X.sheaf).comparisonRight A
          (unitComplex (Stacks.RingedSpace.toRingedSite X))
          (Stacks.SheafOfModules.isKFlat_single_unit
            (Stacks.RingedSpace.toRingedSite X).O)).hom ≫
        DerivedCategory.Q.map (A ◁ ε (pullbackComplex f)) =
      ((canonicalDerivedTensorProduct X.sheaf).tensor.obj (DerivedCategory.Q.obj A)).map
          (DerivedCategory.Q.map (ε (pullbackComplex f))) ≫
        ((canonicalDerivedTensorProduct X.sheaf).comparisonRight A
            ((pullbackComplex f).obj (unitComplex (Stacks.RingedSpace.toRingedSite Y)))
            (kFlat_pullback_unit f)).hom := by
  have h := (canonicalDerivedTensorProduct X.sheaf).comparisonRight_naturality (𝟙 A)
    (ε (pullbackComplex f))
    (Stacks.SheafOfModules.isKFlat_single_unit (Stacks.RingedSpace.toRingedSite X).O)
    (kFlat_pullback_unit f)
  rw [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at h
  exact h.symm

open Stacks.Cohomology.DerivedPullbackTensor in
/-- **The canonical map to the total tensor complex against `f^*𝒪_Y[0]`, expressed at the unit
complex of `X`.**  Transporting the right K-flat comparison along `ε` and cancelling `ε` against
its inverse leaves the comparison at `f^*𝒪_Y[0]`, which is the canonical map because that
complex is K-flat. -/
private theorem toTensor_pullback_unit_eq
    (A : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) :
    (canonicalDerivedTensorProduct X.sheaf).toTensor A
        ((pullbackComplex f).obj (unitComplex (Stacks.RingedSpace.toRingedSite Y))) =
      ((canonicalDerivedTensorProduct X.sheaf).tensor.obj (DerivedCategory.Q.obj A)).map
          (DerivedCategory.Q.map (inv (ε (pullbackComplex f)))) ≫
        ((canonicalDerivedTensorProduct X.sheaf).comparisonRight A
              (unitComplex (Stacks.RingedSpace.toRingedSite X))
              (Stacks.SheafOfModules.isKFlat_single_unit
                (Stacks.RingedSpace.toRingedSite X).O)).hom ≫
          DerivedCategory.Q.map (A ◁ ε (pullbackComplex f)) := by
  rw [comparisonRight_comp_whiskerLeft_epsilon f A]
  exact ((canonicalDerivedTensorProduct X.sheaf).toTensor_eq_comparisonRight A _
      (kFlat_pullback_unit f)).trans
    (map_map_inv_cancel DerivedCategory.Q
      ((canonicalDerivedTensorProduct X.sheaf).tensor.obj (DerivedCategory.Q.obj A))
      (ε (pullbackComplex f)) _).symm

/-- Bracketing the first three factors of a four-fold composite.  Stated generically and applied
by unification, for the reason given on `map_map_inv_cancel`. -/
private lemma assoc_middle {C : Type*} [Category C] {A B D E Z : C} (a : A ⟶ B) (b : B ⟶ D)
    (c : D ⟶ E) (d : E ⟶ Z) : a ≫ b ≫ c ≫ d = (a ≫ b ≫ c) ≫ d := by
  simp only [Category.assoc]

/-- Reassociation of a composite whose last factor is the functor image of a triple composite.
Stated generically and applied by unification, for the reason given on `map_map_inv_cancel`. -/
private lemma assoc_map_comp₃ {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {W V : D} {A B Z T : C} (a : W ⟶ V) (b : V ⟶ F.obj A) (c : A ⟶ B) (d : B ⟶ Z) (e : Z ⟶ T) :
    a ≫ b ≫ F.map (c ≫ d ≫ e) = (a ≫ b ≫ F.map c) ≫ F.map d ≫ F.map e := by
  simp only [F.map_comp, Category.assoc]

/-- The right unitor of the total tensor complex is the monoidal right unitor.  True by
definition; recorded so that the statements above, which are spelled at
`tensorComplexRightUnitorNatIso`, can be rewritten into the spelling of the complex-level
coherence, which is spelled at `ρ_`. -/
private lemma tensorComplexRightUnitorNatIso_app_hom (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    ((tensorComplexRightUnitorNatIso (Stacks.RingedSpace.toRingedSite Z)).app K).hom =
      (ρ_ K).hom := rfl

open Stacks.Cohomology.DerivedPullbackTensor in
/-- **The right unit constraint of `⊗^𝐋_{𝒪_X}` at the image of a pullback complex, carried to
the total tensor complex on `Y`.**  This is where the complex-level coherence of
[Stacks, Tag 079U] enters: the right unitor at `Q(f^*K)` is the right K-flat comparison followed
by `Q` of the right unitor of complexes, and that unitor is rewritten by
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso_rightUnitor`. -/
private theorem whiskerUnit_comp_rightUnitor_q
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    ((canonicalDerivedTensorProduct X.sheaf).tensor.obj
            (DerivedCategory.Q.obj ((pullbackComplex f).obj K))).map
          (DerivedCategory.Q.map (inv (ε (pullbackComplex f)))) ≫
        (Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).hom.app
          (DerivedCategory.Q.obj ((pullbackComplex f).obj K)) =
      ((canonicalDerivedTensorProduct X.sheaf).toTensor ((pullbackComplex f).obj K)
            ((pullbackComplex f).obj (unitComplex (Stacks.RingedSpace.toRingedSite Y)))) ≫
        DerivedCategory.Q.map
            (pullbackTensorComplexIsoOfIsIso f K
              (unitComplex (Stacks.RingedSpace.toRingedSite Y))).inv ≫
          DerivedCategory.Q.map ((pullbackComplex f).map (ρ_ K).hom) := by
  rw [derivedTensorRightUnitorNatIso_hom_app_q X ((pullbackComplex f).obj K),
    tensorComplexRightUnitorNatIso_app_hom X ((pullbackComplex f).obj K),
    pullbackTensorComplexIso_rightUnitor f K, toTensor_pullback_unit_eq f]
  exact assoc_map_comp₃ DerivedCategory.Q _ _ _ _ _

/-- `Stacks.RingedSpace.derivedTensorRightUnitor_naturality` with the unitor written as a
component of the natural transformation rather than as the `hom` of a component.  The two are
the same term; the restatement is what lets `rw` use it in the goals below. -/
private lemma rightUnitor_naturality' (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {W W' : DerivedCategory
      (_root_.SheafOfModules.{u} (structureSheafRing Z))} (u : W ⟶ W') :
    (Functor.uncurry.obj (derivedTensorProductFunctor Z.sheaf)).map
          ((u ×ₘ 𝟙 (singleUnit Z)) : ((W, singleUnit Z) : _ × _) ⟶ (W', singleUnit Z)) ≫
        (Stacks.RingedSpace.derivedTensorRightUnitorNatIso Z).hom.app W' =
      (Stacks.RingedSpace.derivedTensorRightUnitorNatIso Z).hom.app W ≫ u :=
  Stacks.RingedSpace.derivedTensorRightUnitor_naturality Z u

/-- The uncurried bifunctor applied to a morphism whose first component is an identity is the
fixed-left-argument functor applied to the second component. -/
private lemma uncurry_map_id_prod {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D ⥤ E) (A : C) {B B' : D} (g : B ⟶ B') :
    (Functor.uncurry.obj F).map ((𝟙 A ×ₘ g) : ((A, B) : C × D) ⟶ (A, B')) =
      (F.obj A).map g := by
  rw [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

/-- A morphism of a product category whose first component is an identity, followed by one whose
second component is an identity. -/
private lemma id_prod_comp_prod_id {C D : Type*} [Category C] [Category D] {A A' : C}
    {B B' : D} (a : A ⟶ A') (b : B ⟶ B') :
    ((𝟙 A ×ₘ b) : ((A, B) : C × D) ⟶ (A, B')) ≫ (a ×ₘ 𝟙 B') = (a ×ₘ b) := by
  rw [prod_comp, Category.id_comp, Category.comp_id]

/-- Splitting the second component of a morphism of a product category. -/
private lemma prod_split_right {C D : Type*} [Category C] [Category D] {A A' : C}
    {B B' B'' : D} (a : A ⟶ A') (b : B ⟶ B') (b' : B' ⟶ B'') :
    ((a ×ₘ (b ≫ b')) : ((A, B) : C × D) ⟶ (A', B'')) = (a ×ₘ b) ≫ (𝟙 A' ×ₘ b') := by
  rw [prod_comp, Category.comp_id]

/-- **Merging a whiskering by a composite with a whiskering on the other side.**  The two
whiskerings of the uncurried bifunctor compose to the whiskering by the pair, and the second
factor of the composite is then peeled off as a map of the fixed-left-argument functor.

Stated generically, with every object and morphism a variable.  This is the step the concrete
goal below needs, and at the concrete terms — where the bifunctor is the derived tensor product
of a ringed space — `rw [Functor.map_comp]` exhausts the heartbeat budget inside `isDefEq`:
the pattern `?F.map (?a ≫ ?b)` has to be matched against a functor built from the derived tensor
product, the derived pullback and `Functor.uncurry`.  Applied by unification against this
lemma's rigid left-hand side, the same step is immediate. -/
private lemma uncurry_whisker_merge {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D ⥤ E) {A A' : C} {B B' B'' : D} (a : A ⟶ A') (b : B ⟶ B') (b' : B' ⟶ B'') :
    (Functor.uncurry.obj F).map ((𝟙 A ×ₘ (b ≫ b')) : ((A, B) : C × D) ⟶ (A, B'')) ≫
        (Functor.uncurry.obj F).map ((a ×ₘ 𝟙 B'') : ((A, B'') : C × D) ⟶ (A', B'')) =
      (Functor.uncurry.obj F).map ((a ×ₘ b) : ((A, B) : C × D) ⟶ (A', B')) ≫
        (F.obj A').map b' := by
  rw [← Functor.map_comp, id_prod_comp_prod_id, prod_split_right, Functor.map_comp,
    uncurry_map_id_prod]

/-- The right unitor read as the `hom` of a component rather than as a component of the `hom`.
True by definition; both spellings occur among the imported statements. -/
private lemma rightUnitor_app_hom (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (W : DerivedCategory
      (_root_.SheafOfModules.{u} (structureSheafRing Z))) :
    ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso Z).app W).hom =
      (Stacks.RingedSpace.derivedTensorRightUnitorNatIso Z).hom.app W := rfl

/-- **The right unit constraint of `⊗^𝐋_{𝒪_Z}` at the image of a complex, as the canonical map
to the total tensor complex followed by `Q` of the right unitor of complexes.**  This is
`derivedTensorRightUnitorNatIso_hom_app_q` with the right K-flat comparison replaced by the
canonical map, which is legitimate because `𝒪_Z[0]` is K-flat. -/
private theorem rightUnitor_hom_app_q_toTensor (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    (Stacks.RingedSpace.derivedTensorRightUnitorNatIso Z).hom.app
        (DerivedCategory.Q.obj K) =
      (canonicalDerivedTensorProduct Z.sheaf).toTensor K
          (unitComplex (Stacks.RingedSpace.toRingedSite Z)) ≫
        DerivedCategory.Q.map (ρ_ K).hom := by
  rw [derivedTensorRightUnitorNatIso_hom_app_q Z K, tensorComplexRightUnitorNatIso_app_hom Z K,
    (canonicalDerivedTensorProduct Z.sheaf).toTensor_eq_comparisonRight K _
      (Stacks.SheafOfModules.isKFlat_single_unit (Stacks.RingedSpace.toRingedSite Z).O)]

open Stacks.Cohomology.DerivedPullbackTensor in
/-- **The left comparison of [Stacks, Tag 079U] against the unit, followed by the right unitor
of complexes, is the derived pullback of the right unitor.**  The left comparison is the derived
pullback of the canonical map to the total tensor complex followed by the comparison
`Lf^*(QM) ⟶ Q(f^*M)`, and that comparison is natural; at a K-flat `K` it is invertible, which is
what lets it be cancelled. -/
private theorem leftComparison_comp_rho
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (leftComparison f).app (K, unitComplex (Stacks.RingedSpace.toRingedSite Y)) ≫
        DerivedCategory.Q.map ((pullbackComplex f).map (ρ_ K).hom) =
      (derivedPullback f).map
          ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y).hom.app
            (DerivedCategory.Q.obj K)) ≫
        (derivedPullbackNatTrans f).app K := by
  -- The naturality of `Lf^*(QM) ⟶ Q(f^*M)` at the right unitor of complexes, with the source of
  -- the unitor spelled as the total complex of the pair rather than as a monoidal product; the
  -- two are the same complex, and this is the spelling `leftComparison` presents.
  have hnat : (derivedPullback f).map (DerivedCategory.Q.map (ρ_ K).hom) ≫
        (derivedPullbackNatTrans f).app K =
      (derivedPullbackNatTrans f).app
          ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).obj
            (K, unitComplex (Stacks.RingedSpace.toRingedSite Y))) ≫
        DerivedCategory.Q.map ((pullbackComplex f).map (ρ_ K).hom) :=
    (derivedPullbackNatTrans f).naturality (ρ_ K).hom
  have hρ : (derivedPullback f).map
        ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y).hom.app
          (DerivedCategory.Q.obj K)) =
      (derivedPullback f).map
          ((canonicalDerivedTensorProduct Y.sheaf).toTensor K
            (unitComplex (Stacks.RingedSpace.toRingedSite Y))) ≫
        (derivedPullback f).map (DerivedCategory.Q.map (ρ_ K).hom) := by
    rw [rightUnitor_hom_app_q_toTensor Y K]
    exact (derivedPullback f).map_comp _ _
  rw [hρ]
  dsimp only [leftComparison, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, derivedToTensorNatTrans]
  simp only [Category.assoc]
  rw [← hnat]
  rfl

/-- **The canonical unit comparison `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]` built from the comparison
`Lf^*(QM) ⟶ Q(f^*M)` and the complex-level unit comparison of `f^*`.**

`𝒪_Y[0]` is K-flat, so the first is invertible there; the second is the lax unit of the monoidal
lift of `f^*` to complexes, invertible because that lift is monoidal rather than merely lax.
This is the unit comparison the complex-level coherence of [Stacks, Tag 079U] is stated with,
and the one at which the coherence below is therefore provable. -/
def derivedPullbackUnitIso :
    (derivedPullback f).obj (singleUnit Y) ≅ singleUnit X :=
  (@asIso _ _ _ _ ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans f).app
        (unitComplex (Stacks.RingedSpace.toRingedSite Y)))
      (Stacks.Cohomology.DerivedPullbackTensor.isIso_derivedPullbackNatTrans_app f _
        (Stacks.SheafOfModules.isKFlat_single_unit
          (Stacks.RingedSpace.toRingedSite Y).O))) ≪≫
    (DerivedCategory.Q.mapIso (@asIso _ _ _ _
      (ε (Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex f)) inferInstance)).symm

open Stacks.Cohomology.DerivedPullbackTensor in
/-- The canonical unit comparison, written out. -/
private lemma derivedPullbackUnitIso_hom :
    (derivedPullbackUnitIso f).hom =
      (derivedPullbackNatTrans f).app (unitComplex (Stacks.RingedSpace.toRingedSite Y)) ≫
        DerivedCategory.Q.map (inv (ε (pullbackComplex f))) := by
  dsimp only [derivedPullbackUnitIso, Iso.trans_hom, asIso_hom, Iso.symm_hom,
    Functor.mapIso_inv, asIso_inv]

open Stacks.Cohomology.DerivedPullbackTensor in
/-- **The right comparison of [Stacks, Tag 079U] against the unit accounts for the unit
comparison and the right unitor on `X`.**  Both sides are read after the comparison
`Lf^*(QK) ⟶ Q(f^*K)`, which is where `whiskerUnit_comp_rightUnitor_q` — and with it the
complex-level coherence — is applied; no invertibility is used, so no K-flatness of `K` is
needed here. -/
private theorem whiskerUnit_rightUnitor_comp_natTrans
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
          ((𝟙 ((derivedPullback f).obj (DerivedCategory.Q.obj K)) ×ₘ
              (derivedPullbackUnitIso f).hom) :
            (((derivedPullback f).obj (DerivedCategory.Q.obj K),
                (derivedPullback f).obj (singleUnit Y)) : _ × _) ⟶
              ((derivedPullback f).obj (DerivedCategory.Q.obj K), singleUnit X)) ≫
        (Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).hom.app
            ((derivedPullback f).obj (DerivedCategory.Q.obj K)) ≫
          (derivedPullbackNatTrans f).app K =
      (rightComparison f).app (K, unitComplex (Stacks.RingedSpace.toRingedSite Y)) ≫
        DerivedCategory.Q.map ((pullbackComplex f).map (ρ_ K).hom) := by
  have hnat := rightUnitor_naturality' X
    (W := (derivedPullback f).obj (DerivedCategory.Q.obj K))
    (W' := DerivedCategory.Q.obj ((pullbackComplex f).obj K))
    ((derivedPullbackNatTrans f).app K)
  rw [← hnat, derivedPullbackUnitIso_hom, ← Category.assoc, uncurry_whisker_merge,
    Category.assoc, whiskerUnit_comp_rightUnitor_q f K]
  dsimp only [rightComparison, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, derivedToTensorNatTrans, NatTrans.prod, Functor.prod_obj,
    pullbackTensorComplexNatIso_inv_app]
  apply assoc_middle

open Stacks.Cohomology.DerivedPullbackTensor in
/-- **The right-unitor coherence of the comparison of [Stacks, Tag 079U] at a K-flat
representative.**  For a K-flat complex `K` of `𝒪_Y`-modules, the comparison

`Lf^*(QK ⊗^𝐋_{𝒪_Y} 𝒪_Y[0]) ⟶ Lf^*(QK) ⊗^𝐋_{𝒪_X} Lf^*(𝒪_Y[0])`,

followed by `𝟙 ⊗ ν` for the canonical unit comparison `ν` of `derivedPullbackUnitIso` and by the
right unitor on `X`, is the derived pullback of the right unitor on `Y`.

This is the hypothesis `h` of
`Stacks.Cohomology.DerivedProjectionFormula.rightUnitorCoherence_of_kFlat`, discharged.  The
unitor is the one carried by
`Stacks.RingedSpace.derivedTensorRightUnitorNatIso`, that is
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitorNatIso` — **not**
`…rightUnitIso`, with which the library proves no identification.

The proof is the localization bridge from the complex-level coherence
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso_rightUnitor`.  At a K-flat `K`
the comparison is `Stacks.Cohomology.DerivedPullbackTensor.modelComparison`, which is the left
comparison followed by the inverse of the right one; the two are handled by
`leftComparison_comp_rho` and `whiskerUnit_rightUnitor_comp_natTrans`, and what glues them is
that `Lf^*(QK) ⟶ Q(f^*K)` is invertible at a K-flat `K`. -/
theorem rightUnitorCoherence_app_q_of_kFlat
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K) :
    (pullbackTensorComparison f).app (DerivedCategory.Q.obj K, singleUnit Y) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
          ((𝟙 ((derivedPullback f).obj (DerivedCategory.Q.obj K)) ×ₘ
              (derivedPullbackUnitIso f).hom) :
            (((derivedPullback f).obj (DerivedCategory.Q.obj K),
                (derivedPullback f).obj (singleUnit Y)) : _ × _) ⟶
              ((derivedPullback f).obj (DerivedCategory.Q.obj K), singleUnit X)) ≫
          ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).app
            ((derivedPullback f).obj (DerivedCategory.Q.obj K))).hom =
      (derivedPullback f).map
        ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y).app
          (DerivedCategory.Q.obj K)).hom := by
  have := isIso_derivedPullbackNatTrans_app f K hK
  have hcmp : (pullbackTensorComparison f).app (DerivedCategory.Q.obj K, singleUnit Y) =
      (Stacks.Cohomology.DerivedPullbackTensor.modelComparison f K
        (unitComplex (Stacks.RingedSpace.toRingedSite Y)) hK
        (Stacks.SheafOfModules.isKFlat_single_unit
          (Stacks.RingedSpace.toRingedSite Y).O)).hom :=
    pullbackTensorComparison_app_q_of_kFlat f K _ hK
      (Stacks.SheafOfModules.isKFlat_single_unit (Stacks.RingedSpace.toRingedSite Y).O)
  rw [rightUnitor_app_hom X, rightUnitor_app_hom Y, hcmp]
  refine (cancel_mono ((derivedPullbackNatTrans f).app K)).1 ?_
  dsimp only [modelComparison, Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv]
  simp only [Category.assoc]
  rw [whiskerUnit_rightUnitor_comp_natTrans f K, IsIso.inv_hom_id_assoc]
  exact leftComparison_comp_rho f K

/-- **The right-unitor coherence of the comparison of [Stacks, Tag 079U], at every object of
`D(𝒪_Y)`, with no hypothesis.**  This is `rightUnitorCoherence_app_q_of_kFlat` fed to
`Stacks.Cohomology.DerivedProjectionFormula.rightUnitorCoherence_of_kFlat`, which upgrades the
coherence from K-flat representatives to all of `D(𝒪_Y)` by essential surjectivity of the K-flat
objects, [Stacks, Tag 06YS].

This is the hypothesis `hcoh` of
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject`, discharged
at the unit comparison `derivedPullbackUnitIso`. -/
theorem rightUnitorCoherence_unitObject
    (Z : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (pullbackTensorComparison f).app (Z, singleUnit Y) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
          ((𝟙 ((derivedPullback f).obj Z) ×ₘ (derivedPullbackUnitIso f).hom) :
            (((derivedPullback f).obj Z, (derivedPullback f).obj (singleUnit Y)) : _ × _) ⟶
              ((derivedPullback f).obj Z, singleUnit X)) ≫
          ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso X).app
            ((derivedPullback f).obj Z)).hom =
      (derivedPullback f).map
        ((Stacks.RingedSpace.derivedTensorRightUnitorNatIso Y).app Z).hom :=
  rightUnitorCoherence_of_kFlat f (derivedPullbackUnitIso f)
    (rightUnitorCoherence_app_q_of_kFlat f) Z

/-- **[Stacks, Tag 08EU] at `K = 𝒪_Y[0]`.**  For an arbitrary
morphism of ringed spaces `f : X ⟶ Y` and an arbitrary `E` in `D(𝒪_X)`, the derived
projection-formula morphism

`Rf_*E ⊗^𝐋_{𝒪_Y} 𝒪_Y ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*𝒪_Y)`

is an isomorphism.

This is the base case of the source's dévissage for [Stacks, Tag 08EU].  The inputs of
`isIso_projectionFormulaMap_unitObject` are: the two right unitors and the
naturality of the one on `X` by `Stacks.RingedSpace.derivedTensorRightUnitorNatIso`, the unit
comparison by `derivedPullbackUnitIso`, and the right-unitor coherence of [Stacks, Tag 079U] by
`rightUnitorCoherence_unitObject`. -/
@[stacks 08EU "the case K = 𝒪_Y[0]: for an arbitrary morphism of ringed spaces f and an \
arbitrary E in D(𝒪_X), the projection-formula morphism Rf_*E ⊗ᴸ 𝒪_Y ⟶ Rf_*(E ⊗ᴸ Lf^*𝒪_Y) is \
invertible; the right unitors are derivedTensorRightUnitorNatIso, the unit comparison is \
derivedPullbackUnitIso and the right-unitor coherence of Tag 079U is \
rightUnitorCoherence_unitObject"]
theorem isIso_projectionFormulaMap_unitObject_unconditional
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    IsIso (projectionFormulaMap f E (singleUnit Y)) :=
  isIso_projectionFormulaMap_unitObject_of_kFlat f (derivedPullbackUnitIso f)
    (rightUnitorCoherence_app_q_of_kFlat f) E

end Stacks.Cohomology.DerivedProjectionFormula

end
