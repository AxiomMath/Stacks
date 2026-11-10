module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingAssociativity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedAssociatorToTensorOnASite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCompositionApplicationPinning
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingInternalHomNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.AssociatorOnLocalSections

/-!
# Applying a composite is applying the factors in turn, on a ringed site

Let `(C, O)` be a ringed site and let `K`, `L`, `M` be objects of `D(O)`.  Write
`cmp : R𝓗om_O(L, M) ⊗^𝐋_O R𝓗om_O(K, L) ⟶ R𝓗om_O(K, M)` for the composition morphism of
**Stacks 0A8V** and `ε_{K,M} : R𝓗om_O(K, M) ⊗^𝐋_O K ⟶ M` for the application morphism of
**Stacks 08J8**.  Then

`(cmp ▷ K) ≫ ε_{K,M} = α ≫ (1 ◁ ε_{K,L}) ≫ ε_{L,M}`:

applying a composite is applying the two factors in turn.  This is the equation the
derived-duality cluster of Example **0FPC** and **Stacks 0FPU** calls **(C)**.

`Stacks.SheafOfModules.compositionApplicationLaw` is this statement for a ringed *space*; the
slice site `C/U` of a ringed site is not a ringed space, and the left-dual clause of
Stacks 0FPU over an arbitrary ringed site needs (C) there.  This file states it for an arbitrary
ringed site, with the same proof.

## The proof, in two steps

1. On K-injective models of `L` and `M` the identity is
   `derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_model`.  Its two inputs
   are already proved over a ringed site:
   `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_composition_application`, the join
   of the two pinnings of the composition morphism of Stacks 0A8V to the cochain level, and
   `AlgebraicGeometry.RingedSite.derivedApplication_eq_cochainEvaluation_toTensor`, which reads
   the application morphism of Stacks 08J8 as the cochain-level evaluation.  What is new here is
   the associator leg, `AlgebraicGeometry.RingedSite.derivedAssociator_toTensor` of
   `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedAssociatorToTensorOnASite`,
   and the transposition of the double contraction twice, which is
   `AlgebraicGeometry.RingedSite.curryHomEquiv_curryHomEquiv_of_reassociate` against
   `AlgebraicGeometry.RingedSite.associator_tensorComplexSection`.  The descent along the three
   comparisons of Stacks 08DM is `Stacks.Cohomology.DualityDescent.comp_app_descent`.
2. Both sides are natural in `K` and `M` and dinatural in `L`, so the identity is carried to
   arbitrary objects along the K-injective model isomorphisms, by
   `Stacks.Cohomology.DualityDescent.transport_target`, `…transport_middle` and
   `…transport_source`.

## Main results

* `AlgebraicGeometry.RingedSite.CompositionApplicationLaw`: the equation, as a proposition.
* `derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_model`: it holds on the
  classes of complexes `P`, `J`, `I` with `J` and `I` K-injective.
* `AlgebraicGeometry.RingedSite.compositionApplicationLaw`: **(C)**, for arbitrary objects of
  `D(O)`.

## Nothing here is tagged

Stacks 0A8V is carried by `AlgebraicGeometry.RingedSite.derivedSheafHomComposition`,
Stacks 08J8 by `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` and Stacks 08DM by
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison`.  A compatibility between them is
asserted by no published statement, which is the reason
`DerivedCompositionApplicationPinning.lean` (in this directory)
carries no attribute either.

## Implementation notes

The application morphism is written out as `AlgebraicGeometry.RingedSite.derivedSheafHomCounit`
in every statement, while the existing inputs of Stacks 08J8 state it as the bijection of
Stacks 08DI at an identity.  The two are the same term by definition, but **no proof below
crosses between them by conversion**: a `rfl` crossing them reaches the maximum recursion depth,
and so does a `rw` or a `congrArg` that abstracts a motive through the bijection; this is the same
wall
`DerivedCompositionApplicationPinning.lean` (in this directory)
records.  Every crossing is made instead by *rewriting with*
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_apply`, which computes the bijection against
the application morphism: at an identity the whiskering it leaves behind collapses by
`CategoryTheory.Functor.map_id`, and the step is a rewrite at the top of an application with no
conversion check at all.  `derivedSheafHomCounit_eq_transpose` records the resulting equation,
for consumers that want it in one piece.

The comparison of Stacks 08DM at the outer pair stays a variable in
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_composition_application`, for the
reason recorded there; it is instantiated below at the comparison itself.

## References

* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 0FPU](https://stacks.math.columbia.edu/tag/0FPU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
  Opposite
open Stacks.SheafOfModules.Tensor (sheafTensor tensorComplex)
open Stacks.Cohomology.DualityDescent

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
attribute [local instance 10000] CochainComplex.symmetricCategory
  SheafOfModules.monoidalCategorySheafTensor

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]

/-- The monoidal structure on `Comp(Mod(O))`, as a top-priority local instance, for the reason
`AlgebraicGeometry.RingedSite.monoidalCategoryStructComplexesSite` gives. -/
local instance (priority := 100000) monoidalCategoryStructComplexesC :
    MonoidalCategoryStruct
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :=
  inferInstance

/-! ### Pinned spellings -/

/-- The comparison `Q(SheafHom(B, C)) ⟶ R𝓗om_O(QB, QC)` of Stacks 08DM, at the derived internal
Hom of the bifunctor. -/
abbrev homComparisonSite
    (B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    DerivedCategory.Q.obj (sheafHomComplex X B C).obj ⟶
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
        (DerivedCategory.Q.obj C) :=
  strictlyPerfectHomComparison X (derivedInternalHomOfBifunctor X) B C

/-- The composition morphism of Stacks 0A8V at the canonical derived tensor product of
Stacks 06YU and the derived internal Hom of the bifunctor. -/
abbrev derivedCompositionSite
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (((derivedSheafHomBifunctor X).obj (op L)).obj M)).obj
        (((derivedSheafHomBifunctor X).obj (op K)).obj L) ⟶
      ((derivedSheafHomBifunctor X).obj (op K)).obj M :=
  derivedSheafHomComposition X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
    (derivedInternalHomOfBifunctor X) K L M

/-- **The application morphism of Stacks 08J8 is the transpose of the identity.**  This is the
definition of `AlgebraicGeometry.RingedSite.derivedSheafHomCounit`, named so that the step can be
taken by `rw`.

It is *not* proved by `rfl`: although the two sides are the same term, the conversion check at
these arguments reaches the maximum recursion depth, which is the wall
`DerivedCompositionApplicationPinning.lean` (in this directory)
records for the same crossing.  It is proved instead from
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_apply`, the computation of the
bijection of Stacks 08DI against the application morphism, read at the identity: there the
whiskering is by an identity and collapses. -/
theorem derivedSheafHomCounit_eq_transpose
    (K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedSheafHomCounit X K M =
      derivedCurryHomEquiv X (((derivedSheafHomBifunctor X).obj (op K)).obj M) K M
        (𝟙 (((derivedSheafHomBifunctor X).obj (op K)).obj M)) := by
  rw [derivedCurryHomEquiv_apply, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp]

/-! ### The model step -/

/-- **The application morphism of Stacks 08J8 against a cochain-level transpose.**  For complexes
`A`, `B`, `C` of `O`-modules and `f : A ⟶ SheafHom(B, C)`,
`(Q f ▷ QB) ≫ (σ ▷ QB) ≫ ε = t_{A,B} ≫ Q(curry f)`, with no hypothesis on the complexes. -/
theorem derivedSheafHomCounit_homComparison_curry
    (A B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (f : A ⟶ (sheafHomComplex X B C).obj) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
            (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj B) ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
            (homComparisonSite X B C)).app (DerivedCategory.Q.obj B) ≫
          derivedSheafHomCounit X (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C) =
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor A B ≫
        DerivedCategory.Q.map (curryHomEquiv X A B C f) := by
  obtain ⟨B', v, hB', _⟩ := Stacks.SheafOfModules.exists_kFlat_quasiIso X B
  have h := derivedApplication_curryingSquare_toTensor X A B B' C v hB' _ _
    (strictlyPerfectHomComparison_naturality_source X (derivedInternalHomOfBifunctor X)
      B B' C v).symm
    (derivedSheafHomGlobalSectionsEquiv_precomposedHomComparisonClass X
      (derivedInternalHomOfBifunctor X) B' C _ hB'
      (isKFlat_kFlatHomResolution X B' C) (kFlatHomResolutionMap X B' C)) f
  rw [derivedCurryHomEquiv_apply, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at h
  exact h

/-- **The application morphism of Stacks 08J8 is the cochain-level evaluation**, conjugated by
the comparison `σ` of Stacks 08DM and the canonical map `t` of Stacks 06YU:
`(σ ▷ QB) ≫ ε = t ≫ Q(ev)`, with no hypothesis on the complexes. -/
theorem derivedSheafHomCounit_homComparison
    (B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
            (homComparisonSite X B C)).app (DerivedCategory.Q.obj B) ≫
        derivedSheafHomCounit X (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C) =
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor
          (sheafHomComplex X B C).obj B ≫
        DerivedCategory.Q.map (cochainEvaluation X B C) := by
  have h := derivedSheafHomCounit_homComparison_curry X _ B C (𝟙 _)
  rw [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at h
  exact h

/-- **The composition morphism of Stacks 0A8V against the comparison of Stacks 08DM**:
conjugated by `σ` on both tensor factors and on the target, it is the class of the transpose of
the double contraction. -/
theorem homComparison_derivedSheafHomComposition
    (P J I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
          (homComparisonSite X J I)).app
        (DerivedCategory.Q.obj (sheafHomComplex X P J).obj) ≫
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj _).map
        (homComparisonSite X P J) ≫
      derivedCompositionSite X (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj J)
        (DerivedCategory.Q.obj I) =
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor _ _ ≫
      DerivedCategory.Q.map (curryHomEquiv X _ _ _ (doubleContraction X P J I)) ≫
        homComparisonSite X P I := by
  have h := strictlyPerfectHomComparison_composition_doubleContraction X P J I
  rw [← Category.assoc]
  exact h

/-- The canonical map of Stacks 06YU is natural in its second complex. -/
theorem toTensor_naturality_right
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g : B ⟶ B') :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj A)).map (DerivedCategory.Q.map g) ≫
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor A B' =
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor A B ≫
        DerivedCategory.Q.map (((tensorComplex X.O).obj A).map g) := by
  have h := (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor_naturality (𝟙 A) g
  rw [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at h
  exact h

/-- **The associator of total tensor complexes**, at the
`Stacks.SheafOfModules.Tensor.tensorComplex` spelling of its source and target. -/
def associatorTot
    (A B D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((tensorComplex X.O).obj (((tensorComplex X.O).obj A).obj B)).obj D ⟶
      ((tensorComplex X.O).obj A).obj (((tensorComplex X.O).obj B).obj D) :=
  (α_ A B D).hom

/-- The associator of total tensor complexes reassociates an iterated local pure tensor. -/
theorem associatorTot_tensorComplexSection
    (A B D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (W : X.C) (a b d j : ℤ) (h : a + b + d = j) (h' : a + (b + d) = j)
    (x : (A.X a).val.obj (op W)) (y : (B.X b).val.obj (op W)) (z : (D.X d).val.obj (op W)) :
    ((associatorTot X A B D).f j).val.app (op W)
        (tensorComplexSection X (a + b) d j h
          (tensorComplexSection X a b (a + b) rfl x y) z) =
      tensorComplexSection X a (b + d) j h' x (tensorComplexSection X b d (b + d) rfl y z) :=
  associator_tensorComplexSection X A B D W a b d j h h' x y z

/-- **The double contraction, transposed twice, is evaluation twice**: the morphism
`Tot(Tot(SheafHom(J, I) ⊗ SheafHom(P, J)) ⊗ P) ⟶ I` obtained from the double contraction by the
currying bijection of Stacks 0A90 twice is the associator of total tensor complexes followed by
`1 ⊗ ev_{P,J}` and `ev_{J,I}`. -/
theorem curryHomEquiv_curryHomEquiv_doubleContraction
    (P J I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    curryHomEquiv X _ P I (curryHomEquiv X _ _ _ (doubleContraction X P J I)) =
      associatorTot X (sheafHomComplex X J I).obj (sheafHomComplex X P J).obj P ≫
        ((tensorComplex X.O).obj (sheafHomComplex X J I).obj).map
            (cochainEvaluation X P J) ≫
        cochainEvaluation X J I := by
  have h1 := curryHomEquiv_curryHomEquiv_of_reassociate X _ _ _ _
    (doubleContraction X P J I) _ (associatorTot_tensorComplexSection X _ _ _)
  have h2 : doubleContraction X P J I ≫
      (sheafHomTensorCurryIso X (sheafHomComplex X P J).obj P I).hom =
      homMap X (cochainEvaluation X P J) (𝟙 I) := by
    rw [doubleContraction, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h3 := curryHomEquiv_homMap_source X J
    (((tensorComplex X.O).obj (sheafHomComplex X P J).obj).obj P) I
    (cochainEvaluation X P J)
  rw [h1, h2, h3]

/-- `AlgebraicGeometry.RingedSite.derivedAssociator_toTensor` at the `tensorComplex` spelling. -/
theorem derivedAssociator_toTensor_tot
    (A B D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
          ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor A B)).app
        (DerivedCategory.Q.obj D) ≫
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor _ D ≫
        DerivedCategory.Q.map (associatorTot X A B D) =
    derivedAssociatorHom X _ _ _ ≫
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
        (DerivedCategory.Q.obj A)).map
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor B D) ≫
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor A _ :=
  derivedAssociator_toTensor X A B D

/-- The double contraction transposed twice, read in `D(O)`. -/
theorem Q_map_curryHomEquiv_curryHomEquiv_doubleContraction
    (P J I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    DerivedCategory.Q.map (curryHomEquiv X _ P I
        (curryHomEquiv X _ _ _ (doubleContraction X P J I))) =
      DerivedCategory.Q.map (associatorTot X (sheafHomComplex X J I).obj
          (sheafHomComplex X P J).obj P) ≫
        DerivedCategory.Q.map (((tensorComplex X.O).obj (sheafHomComplex X J I).obj).map
            (cochainEvaluation X P J)) ≫
        DerivedCategory.Q.map (cochainEvaluation X J I) := by
  rw [curryHomEquiv_curryHomEquiv_doubleContraction, Functor.map_comp, Functor.map_comp]

/-- The associativity constraint of `D(O)` is natural in its first two variables. -/
theorem derivedAssociatorHom_naturality_left_middle
    {A A' B B' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (D : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (a : A' ⟶ A) (b : B' ⟶ B) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map a).app B' ≫
          ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).map b)).app D ≫
        derivedAssociatorHom X A B D =
      derivedAssociatorHom X A' B' D ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map a).app _ ≫
          ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).map
            (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map b).app D) := by
  have h := derivedAssociatorHom_naturality X a b (𝟙 D)
  simp only [derivedWhiskerLeft, derivedWhiskerRight, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id] at h
  exact h

/-- **Applying a composite is applying the two factors in turn**, on the classes of complexes
`P`, `J`, `I` with `J` and `I` K-injective: for the composition morphism `cmp` of Stacks 0A8V
and the application morphisms `ε` of Stacks 08J8,

`(cmp ▷ QP) ≫ ε_{P,I} = α ≫ (1 ◁ ε_{P,J}) ≫ ε_{J,I}`. -/
theorem derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_model
    (P J I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [J.IsKInjective] [I.IsKInjective] :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
          (derivedCompositionSite X (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj J)
            (DerivedCategory.Q.obj I))).app (DerivedCategory.Q.obj P) ≫
        derivedSheafHomCounit X (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I) =
      derivedAssociatorHom X _ _ _ ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj _).map
            (derivedSheafHomCounit X (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj J)) ≫
          derivedSheafHomCounit X (DerivedCategory.Q.obj J) (DerivedCategory.Q.obj I) := by
  have hJI : IsIso (homComparisonSite X J I) :=
    isIso_strictlyPerfectHomComparison_of_isKInjective _ _ _ _
  have hPJ : IsIso (homComparisonSite X P J) :=
    isIso_strictlyPerfectHomComparison_of_isKInjective _ _ _ _
  exact comp_app_descent (Stacks.SheafOfModules.derivedTensorProductFunctor X)
    (homComparisonSite X J I) (homComparisonSite X P J) (homComparisonSite X P I) hJI hPJ
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (homComparison_derivedSheafHomComposition X P J I)
    (derivedSheafHomCounit_homComparison_curry X _ P I _)
    (derivedSheafHomCounit_homComparison X P J)
    (derivedSheafHomCounit_homComparison X J I)
    (toTensor_naturality_right X _ _)
    (derivedAssociator_toTensor_tot X _ _ P)
    (Q_map_curryHomEquiv_curryHomEquiv_doubleContraction X P J I)
    (derivedAssociatorHom_naturality_left_middle X _ _ _)

/-! ### Releasing the models -/

/-- **Applying a composite is applying the two factors in turn**, as a proposition: for objects
`K`, `L`, `M` of `D(O)`, the composition morphism `cmp` of Stacks 0A8V and the application
morphisms `ε` of Stacks 08J8 satisfy `(cmp ▷ K) ≫ ε_{K,M} = α ≫ (1 ◁ ε_{K,L}) ≫ ε_{L,M}`. -/
def CompositionApplicationLaw
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    Prop :=
  ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
        (derivedCompositionSite X K L M)).app K ≫ derivedSheafHomCounit X K M =
    derivedAssociatorHom X _ _ _ ≫
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (((derivedSheafHomBifunctor X).obj (op L)).obj M)).map
        (derivedSheafHomCounit X K L) ≫ derivedSheafHomCounit X L M

/-- The application morphism is natural in its target. -/
theorem derivedSheafHomCounit_naturality_target
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (m : M ⟶ M') :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
          (((derivedSheafHomBifunctor X).obj (op K)).map m)).app K ≫
        derivedSheafHomCounit X K M' =
      derivedSheafHomCounit X K M ≫ m := by
  have h := derivedCurryHomEquiv_naturality_target X m
    (𝟙 (((derivedSheafHomBifunctor X).obj (op K)).obj M))
  rw [derivedCurryHomEquiv_apply, derivedCurryHomEquiv_apply, Category.id_comp,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h
  exact h

/-- The application morphism is dinatural in its source. -/
theorem derivedSheafHomCounit_dinaturality_source
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (k : K' ⟶ K)
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (((derivedSheafHomBifunctor X).obj (op K)).obj M)).map k ≫
        derivedSheafHomCounit X K M =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
          (((derivedSheafHomBifunctor X).map k.op).app M)).app K' ≫
        derivedSheafHomCounit X K' M := by
  have h := derivedCurryHomEquiv_dinaturality X
    (((derivedSheafHomBifunctor X).obj (op K)).obj M) M k
    (𝟙 (((derivedSheafHomBifunctor X).obj (op K)).obj M))
  rw [derivedCurryHomEquiv_apply, derivedCurryHomEquiv_apply, Category.id_comp,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h
  exact h.symm

/-- The composition morphism of Stacks 0A8V is natural in its target. -/
theorem derivedSheafHomComposition_naturality_target'
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (m : M ⟶ M') :
    derivedCompositionSite X K L M ≫ ((derivedSheafHomBifunctor X).obj (op K)).map m =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
            (((derivedSheafHomBifunctor X).obj (op L)).map m)).app
          (((derivedSheafHomBifunctor X).obj (op K)).obj L) ≫
        derivedCompositionSite X K L M' := by
  have h := derivedSheafHomComposition_natural_target X
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) (derivedInternalHomOfBifunctor X)
    K L m
  rw [derivedSheafHomMap_id_left X (derivedInternalHomOfBifunctor X) K m,
    derivedSheafHomMap_id_left X (derivedInternalHomOfBifunctor X) L m] at h
  rw [h]
  exact congrArg (· ≫ derivedCompositionSite X K L M')
    (derivedTensorMap_id_right X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
      (((derivedSheafHomBifunctor X).obj (op L)).map m)
      (((derivedSheafHomBifunctor X).obj (op K)).obj L))

/-- The composition morphism of Stacks 0A8V is dinatural in its intermediate object. -/
theorem derivedSheafHomComposition_dinaturality_middle'
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (l : L ⟶ L')
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
            (((derivedSheafHomBifunctor X).obj (op L')).obj M)).map
          (((derivedSheafHomBifunctor X).obj (op K)).map l) ≫
        derivedCompositionSite X K L' M =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
            (((derivedSheafHomBifunctor X).map l.op).app M)).app
          (((derivedSheafHomBifunctor X).obj (op K)).obj L) ≫
        derivedCompositionSite X K L M := by
  have h := derivedSheafHomComposition_dinatural_middle X
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) (derivedInternalHomOfBifunctor X)
    K l M
  rw [derivedSheafHomMap_id_left X (derivedInternalHomOfBifunctor X) K l,
    derivedSheafHomMap_id_right X (derivedInternalHomOfBifunctor X) l M] at h
  rw [← derivedTensorMap_id_left X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
      (((derivedSheafHomBifunctor X).obj (op L')).obj M)
      (((derivedSheafHomBifunctor X).obj (op K)).map l),
    ← derivedTensorMap_id_right X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
      (((derivedSheafHomBifunctor X).map l.op).app M)
      (((derivedSheafHomBifunctor X).obj (op K)).obj L)]
  exact h

/-- The composition morphism of Stacks 0A8V is natural in its source. -/
theorem derivedSheafHomComposition_naturality_source'
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (k : K' ⟶ K)
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedCompositionSite X K L M ≫ ((derivedSheafHomBifunctor X).map k.op).app M =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
            (((derivedSheafHomBifunctor X).obj (op L)).obj M)).map
          (((derivedSheafHomBifunctor X).map k.op).app L) ≫
        derivedCompositionSite X K' L M := by
  have h := derivedSheafHomComposition_natural_source X
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) (derivedInternalHomOfBifunctor X)
    k L M
  rw [derivedSheafHomMap_id_right X (derivedInternalHomOfBifunctor X) k M,
    derivedSheafHomMap_id_right X (derivedInternalHomOfBifunctor X) k L] at h
  rw [← derivedTensorMap_id_left X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
    (((derivedSheafHomBifunctor X).obj (op L)).obj M)
    (((derivedSheafHomBifunctor X).map k.op).app L)]
  exact h

/-- The associativity constraint of `D(O)` is natural in its first variable. -/
theorem derivedAssociatorHom_naturality_first
    {A A' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (a : A' ⟶ A)
    (B D : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map a).app B)).app D ≫
        derivedAssociatorHom X A B D =
      derivedAssociatorHom X A' B D ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map a).app _ := by
  have h := derivedAssociatorHom_naturality X a (𝟙 B) (𝟙 D)
  simp only [derivedWhiskerLeft, derivedWhiskerRight, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp, Category.comp_id] at h
  exact h

/-- The associativity constraint of `D(O)` is natural in its second variable. -/
theorem derivedAssociatorHom_naturality_second
    (A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {B B' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (b : B' ⟶ B)
    (D : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).map b)).app D ≫
        derivedAssociatorHom X A B D =
      derivedAssociatorHom X A B' D ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).map
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map b).app D) := by
  have h := derivedAssociatorHom_naturality X (𝟙 A) b (𝟙 D)
  simp only [derivedWhiskerLeft, derivedWhiskerRight, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp, Category.comp_id] at h
  exact h

/-- The associativity constraint of `D(O)` is natural in its third variable. -/
theorem derivedAssociatorHom_naturality_third
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {D D' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (d : D' ⟶ D) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
            (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).obj B)).map d ≫
        derivedAssociatorHom X A B D =
      derivedAssociatorHom X A B D' ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).map
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj B).map d) := by
  have h := derivedAssociatorHom_naturality X (𝟙 A) (𝟙 B) d
  simp only [derivedWhiskerLeft, derivedWhiskerRight, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp, Category.comp_id] at h
  exact h

/-- The composition law on K-injective models, as
`AlgebraicGeometry.RingedSite.CompositionApplicationLaw`. -/
theorem compositionApplicationLaw_model
    (P J I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [J.IsKInjective] [I.IsKInjective] :
    CompositionApplicationLaw X (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj J)
      (DerivedCategory.Q.obj I) :=
  derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_model X P J I

/-- The composition law is transported along an isomorphism of the target. -/
theorem compositionApplicationLaw_of_iso_target
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (m : M ⟶ M') [IsIso m]
    (h : CompositionApplicationLaw X K L M) : CompositionApplicationLaw X K L M' :=
  transport_target (Stacks.SheafOfModules.derivedTensorProductFunctor X)
    _ _ _ _ _ _ _ _ _ m
    (((derivedSheafHomBifunctor X).obj (op K)).map m)
    (((derivedSheafHomBifunctor X).obj (op L)).map m)
    (derivedSheafHomComposition_naturality_target' X K L m)
    (derivedSheafHomCounit_naturality_target X K m)
    (derivedSheafHomCounit_naturality_target X L m)
    (derivedAssociatorHom_naturality_first X _ _ _) h

/-- The composition law is transported along an isomorphism of the intermediate object. -/
theorem compositionApplicationLaw_of_iso_middle
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (l : L ⟶ L') [IsIso l]
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : CompositionApplicationLaw X K L M) : CompositionApplicationLaw X K L' M :=
  transport_middle (Stacks.SheafOfModules.derivedTensorProductFunctor X)
    _ _ _ _ _ _ _ _ _ _ l
    (((derivedSheafHomBifunctor X).obj (op K)).map l)
    (((derivedSheafHomBifunctor X).map l.op).app M)
    (derivedSheafHomComposition_dinaturality_middle' X K l M)
    (derivedSheafHomCounit_naturality_target X K l)
    (derivedSheafHomCounit_dinaturality_source X l M)
    (derivedAssociatorHom_naturality_first X _ _ _)
    (derivedAssociatorHom_naturality_second X _ _ _) h

/-- The composition law is transported along an isomorphism of the source. -/
theorem compositionApplicationLaw_of_iso_source
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (k : K' ⟶ K) [IsIso k]
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : CompositionApplicationLaw X K L M) : CompositionApplicationLaw X K' L M :=
  transport_source (Stacks.SheafOfModules.derivedTensorProductFunctor X)
    _ _ _ _ _ _ _ _ _ _ k
    (((derivedSheafHomBifunctor X).map k.op).app M)
    (((derivedSheafHomBifunctor X).map k.op).app L)
    (derivedSheafHomComposition_naturality_source' X k L M)
    (derivedSheafHomCounit_dinaturality_source X k M)
    (derivedSheafHomCounit_dinaturality_source X k L)
    (derivedAssociatorHom_naturality_third X _ _ _)
    (derivedAssociatorHom_naturality_second X _ _ _) h

/-- **(C): applying a composite is applying the two factors in turn.**  For objects `K`, `L`,
`M` of `D(O)` on a ringed site, the composition morphism `cmp` of Stacks 0A8V and the
application morphisms `ε` of Stacks 08J8 satisfy

`(cmp ▷ K) ≫ ε_{K,M} = α ≫ (1 ◁ ε_{K,L}) ≫ ε_{L,M}`.

The ringed-space form is `Stacks.SheafOfModules.compositionApplicationLaw`. -/
theorem compositionApplicationLaw
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    CompositionApplicationLaw X K L M := by
  have := isKInjective_kInjectiveModel X L
  have := isKInjective_kInjectiveModel X M
  have h := compositionApplicationLaw_model X (kInjectiveModel X K) (kInjectiveModel X L)
    (kInjectiveModel X M)
  have h₁ := compositionApplicationLaw_of_iso_target X _ _ (kInjectiveModelIso X M).hom h
  have h₂ := compositionApplicationLaw_of_iso_middle X _ (kInjectiveModelIso X L).hom M h₁
  exact compositionApplicationLaw_of_iso_source X (kInjectiveModelIso X K).inv L M h₂

end AlgebraicGeometry.RingedSite

end
