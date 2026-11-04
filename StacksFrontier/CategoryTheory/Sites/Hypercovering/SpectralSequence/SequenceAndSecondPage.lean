module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.CategoryTheory.Sites.FunctorialInjectiveEmbeddings
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SectionsComplexFunctorial
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.ObjectAcyclicity
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.AbutmentIsCohomology

/-!
# The hypercovering spectral sequence and its second page

Let `C` be a site with fibre products, `X` an object of `C`, `K` a hypercovering of `X` and `F` a
sheaf of abelian groups on `C`.  The third clause of [Stacks, Tag 01GY] asserts that there is a
first-quadrant `E₂` cohomological spectral sequence, functorial in `F`, whose second page is
`Ȟ^p(K, H̲^q(F))` and which converges to `H^{p+q}(X, F)`.  This file constructs the spectral
sequence and identifies its second page; the abutment is in
`StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequence.Abutment` and the assembled
statement, together with the functoriality in `K`, in
`StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequence.Assembled`.

## The construction

Choose an injective resolution `F ⟶ I^•` and form the double complex

```
A^{p,q}(F) = s(I^p(K))^q,
```

the `q`-th term of the complex of sections of `K` with coefficients in `I^p`, with the
**resolution degree outer and the hypercovering degree inner**.  That orientation is forced: the
second spectral sequence of a double complex has `''E_2^{p,q} = H^p_{II}(H^q_I(A^{•,•}))` and
`H^q_I` differentiates the *outer* index, so it is the resolution degree that has to come first if
`''E_2^{p,q}` is to be hypercovering cohomology of a derived functor.  The inner index is extended
by zero from `ℕ` to `ℤ`, which is what makes the first-quadrant vanishing immediate.  See the
module documentation of
`StacksFrontier/Topology/Sheaves/Cohomology/CechSpectralSequence/SequenceAndSecondPage.lean`, which
carries out the same construction for an open covering of a ringed space and which this file
mirrors throughout.

An injective resolution is functorial in the sheaf only up to homotopy, so the double complex is
not a functor; it is the object part of a functor up to filtered homotopy, which is the input of
`HomologicalComplex₂.e₂FunctorOfHomotopyClasses`.

The second page is identified in two steps.  First `HomologicalComplex₂.pageTwoNatIso` gives
`''E_2^{p,q} ≅ H^p_{II}(H^q_I(A^{•,•}))` ([Stacks, Tag 0130]).  Then the coefficient comparison
`hypercoverDoubleHomologyNatIso` rewrites the right-hand side as `Ȟ^p(K, H^q(-))`: the functor
`FormalCoproduct.cochainComplexFunctor K` is *exact on presheaves*, hence commutes with homology,
so taking homology of the double complex in the resolution direction is the same as taking
homology of the complex of presheaves underlying the resolution.  At the chosen injective
resolution that homology is `H̲^q(F)` restricted to `Over X`, i.e. the `q`-th right derived functor
of the inclusion of abelian sheaves into presheaves on `Over X` ([Stacks, Tag 01ER]).

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.cechCohomologyOverFunctor`: `Ȟ^p(K, -)` on presheaves on
  `Over X`.
* `Stacks.CategoryTheory.Hypercovering.sectionsEpsNatTrans`: the degree-zero augmentation
  `Γ(X, -)[0] ⟶ s(-(K))`, as a natural transformation.
* `Stacks.CategoryTheory.Hypercovering.hypercoverDoubleFunctor`: the double complex
  `A^{p,q} = s(Y^p(K))^q` of a complex `Y^•` of abelian sheaves.
* `Stacks.CategoryTheory.Hypercovering.hypercoverDouble`,
  `Stacks.CategoryTheory.Hypercovering.hypercoverDoubleMap`: the same at the chosen injective
  resolution of a sheaf, with the morphism induced by a morphism of sheaves.
* `Stacks.CategoryTheory.Hypercovering.hypercoverE₂Functor`,
  `Stacks.CategoryTheory.Hypercovering.hypercoverSpectralSequenceFunctor`: the resulting
  functorial `E₂` spectral sequence, on `ℤ × ℤ` and then on `ℕ × ℕ`.
* `Stacks.CategoryTheory.Hypercovering.cochainComplexFunctorMap`: the sections complex of a
  simplicial formal coproduct, contravariantly in that simplicial object.

## Main results

* `Stacks.CategoryTheory.Hypercovering.cochainComplexFunctor_preservesHomology`: the sections
  complex functor of a simplicial formal coproduct is exact on presheaves.
* `Stacks.CategoryTheory.Hypercovering.hypercoverDoubleHomologyNatIso`: the coefficient
  comparison.
* `Stacks.CategoryTheory.Hypercovering.hypercoverPageTwoIso`: the second page is
  `Ȟ^p(K, H̲^q(F))`, naturally in `F`.
* `Stacks.CategoryTheory.Hypercovering.quasiIso_sectionsEps`: the augmentation
  `Γ(X, F)[0] ⟶ s(F(K))` is a quasi-isomorphism at an injective sheaf -- [Stacks, Tag 01GW] and
  [Stacks, Tag 01GV] together.

## Implementation notes

The cohomology presheaf `H̲^q` is represented by the right derived functors of the restriction to
`Over X` of the inclusion of abelian sheaves into presheaves, which is [Stacks, Tag 01ER]'s
description of it, exactly as the open-covering case is stated with
`(SheafOfModules.forget O).rightDerived q`; cohomology on `X` is the right derived functor of
sections on `X`.  Both are Mathlib's `CategoryTheory.Functor.rightDerived`, so both are computed
from the same chosen injective resolutions as the double complex.

Sheafification for abelian sheaves in the module universe `max u v w` is taken as a hypothesis, as
in `StacksFrontier/CategoryTheory/Sites/Hypercovering/DerivedComparison.lean`; existence of enough
injectives and of functorial injective embeddings is *not*, being supplied by
`CategoryTheory.Sheaf.enoughInjectives_addCommGrpCat`.

## References

* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
* [Stacks Project, Tag 01GV](https://stacks.math.columbia.edu/tag/01GV)
* [Stacks Project, Tag 01GW](https://stacks.math.columbia.edu/tag/01GW)
* [Stacks Project, Tag 01ER](https://stacks.math.columbia.edu/tag/01ER)
* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject.Augmented

universe w v u

namespace Stacks.CategoryTheory.Hypercovering

/-! ### Exactness of the sections complex of a simplicial formal coproduct -/

section Exactness

/-- The diagonal diagram of a family of functors: `a ↦ (i ↦ F i a)`.  Composed with `lim` it is
the product of the family, which is how a product of evaluations is presented to the
limit-preservation lemmas. -/
@[simps]
def piDiagram {I D E : Type*} [Category* D] [Category* E] (F : I → (D ⥤ E)) :
    D ⥤ (Discrete I ⥤ E) where
  obj a := Discrete.functor (fun i => (F i).obj a)
  map {_ _} f := Discrete.natTrans (fun i => (F i.as).map f)
  map_id _ := by ext ⟨_⟩; simp [Discrete.natTrans]
  map_comp _ _ := by ext ⟨_⟩; simp [Discrete.natTrans]

/-- Evaluating `piDiagram F` at the object `i` of the discrete category recovers `F i`. -/
def piDiagramCompEval {I D E : Type*} [Category* D] [Category* E] (F : I → (D ⥤ E)) (i : I) :
    piDiagram F ⋙ (evaluation (Discrete I) E).obj ⟨i⟩ ≅ F i :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (by intro _ _ f; simp [piDiagram, Discrete.natTrans])

/-- A diagonal diagram of finite-limit-preserving functors preserves finite limits, since limits
in a functor category are detected by evaluation. -/
instance piDiagram_preservesFiniteLimits {I D E : Type*} [Category* D] [Category* E]
    (F : I → (D ⥤ E)) [∀ i, PreservesFiniteLimits (F i)] :
    PreservesFiniteLimits (piDiagram F) :=
  ⟨fun _ _ _ => preservesLimitsOfShape_of_evaluation _ _ fun ⟨i⟩ =>
    preservesLimitsOfShape_of_natIso (piDiagramCompEval F i).symm⟩

/-- A diagonal diagram of finite-colimit-preserving functors preserves finite colimits, since
colimits in a functor category are detected by evaluation. -/
instance piDiagram_preservesFiniteColimits {I D E : Type*} [Category* D] [Category* E]
    (F : I → (D ⥤ E)) [∀ i, PreservesFiniteColimits (F i)] :
    PreservesFiniteColimits (piDiagram F) :=
  ⟨fun _ _ _ => preservesColimitsOfShape_of_evaluation _ _ fun ⟨i⟩ =>
    preservesColimitsOfShape_of_natIso (piDiagramCompEval F i).symm⟩

variable {D : Type u} [Category.{v} D] {A : Type*} [Category* A] [HasProducts.{w} A]
  [Preadditive A]

/-- The degree-`n` term of the sections complex of a simplicial formal coproduct, as a functor of
the presheaf: the product, over the summands of the `n`-th level, of the evaluations at those
summands. -/
def levelFunctor (E : SimplicialObject (FormalCoproduct.{w} D)) (n : ℕ) : (Dᵒᵖ ⥤ A) ⥤ A :=
  piDiagram (fun i : (E.obj (op (SimplexCategory.mk n))).I =>
    (evaluation Dᵒᵖ A).obj (op ((E.obj (op (SimplexCategory.mk n))).obj i))) ⋙ lim

/-- **The degree-`n` term of the sections complex is `levelFunctor`**, on the nose. -/
def cochainComplexFunctorCompEvalIso (E : SimplicialObject (FormalCoproduct.{w} D)) (n : ℕ) :
    FormalCoproduct.cochainComplexFunctor (A := A) E ⋙
        HomologicalComplex.eval A (ComplexShape.up ℕ) n ≅
      levelFunctor.{w} E n :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

/-- **The degree-`n` term of the sections complex preserves finite limits**: it is a product of
evaluations, and products preserve limits. -/
instance levelFunctor_preservesFiniteLimits [HasFiniteLimits A]
    (E : SimplicialObject (FormalCoproduct.{w} D)) (n : ℕ) :
    PreservesFiniteLimits (levelFunctor.{w} (A := A) E n) := by
  dsimp only [levelFunctor]; infer_instance

omit [Preadditive A] in
/-- **The degree-`n` term of the sections complex preserves finite colimits**, given that
products indexed by the summand types are exact in the target. -/
theorem levelFunctor_preservesFiniteColimits [HasFiniteColimits A]
    (hex : ∀ I : Type w, HasExactLimitsOfShape (Discrete I) A)
    (E : SimplicialObject (FormalCoproduct.{w} D)) (n : ℕ) :
    PreservesFiniteColimits (levelFunctor.{w} (A := A) E n) := by
  have := hex (E.obj (op (SimplexCategory.mk n))).I
  dsimp only [levelFunctor]; infer_instance

/-- **The sections complex functor of a simplicial formal coproduct preserves finite limits**:
limits of complexes are computed degreewise, and each degree is `levelFunctor`. -/
instance cochainComplexFunctor_preservesFiniteLimits [HasFiniteLimits A]
    (E : SimplicialObject (FormalCoproduct.{w} D)) :
    PreservesFiniteLimits (FormalCoproduct.cochainComplexFunctor (A := A) E) :=
  ⟨fun _ _ _ => HomologicalComplex.preservesLimitsOfShape_of_eval _ fun n =>
    preservesLimitsOfShape_of_natIso (cochainComplexFunctorCompEvalIso.{w} E n).symm⟩

/-- **The sections complex functor of a simplicial formal coproduct preserves finite
colimits**, given that products indexed by the summand types are exact in the target. -/
theorem cochainComplexFunctor_preservesFiniteColimits [HasFiniteColimits A]
    (hex : ∀ I : Type w, HasExactLimitsOfShape (Discrete I) A)
    (E : SimplicialObject (FormalCoproduct.{w} D)) :
    PreservesFiniteColimits (FormalCoproduct.cochainComplexFunctor (A := A) E) :=
  ⟨fun _ _ _ => HomologicalComplex.preservesColimitsOfShape_of_eval _ fun n =>
    have := levelFunctor_preservesFiniteColimits.{w} hex E n
    preservesColimitsOfShape_of_natIso (cochainComplexFunctorCompEvalIso.{w} E n).symm⟩

/-- **The sections complex functor of a simplicial formal coproduct is additive.**  It preserves
finite limits, hence binary products. -/
instance cochainComplexFunctor_additive [HasFiniteLimits A]
    (E : SimplicialObject (FormalCoproduct.{w} D)) :
    (FormalCoproduct.cochainComplexFunctor (A := A) E).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The sections complex functor of a simplicial formal coproduct preserves homology.**  This is
the exactness on presheaves that makes the coefficient comparison of the second page work:
evaluation of presheaves is exact and products of abelian groups are exact. -/
theorem cochainComplexFunctor_preservesHomology {A : Type*} [Category* A] [Abelian A]
    [HasProducts.{w} A] (hex : ∀ I : Type w, HasExactLimitsOfShape (Discrete I) A)
    (E : SimplicialObject (FormalCoproduct.{w} D)) :
    (FormalCoproduct.cochainComplexFunctor (A := A) E).PreservesHomology :=
  have := cochainComplexFunctor_preservesFiniteColimits.{w} hex E
  Functor.preservesHomologyOfExact _

/-- **Products indexed by a type of `Type w` are exact in abelian groups of the universe
`max u v w`.**  Mathlib's instance is stated for an index type in the universe of the groups; the
passage to a smaller index universe is the equivalence `ULift I ≃ I` of shapes. -/
theorem hasExactLimitsOfShape_discrete_addCommGrpCat.{t, s} (I : Type s) :
    HasExactLimitsOfShape (Discrete I) AddCommGrpCat.{max t s} :=
  HasExactLimitsOfShape.of_domain_equivalence AddCommGrpCat.{max t s}
    (Discrete.equivalence (Equiv.ulift.{t, s} (α := I)))

/-- **An additive functor commutes with extension by zero and with homology in a degree coming
from `ℕ`.**  Extending an `ℕ`-indexed complex by zero, applying the functor degreewise and taking
cohomology in degree `(n : ℤ)` is applying the functor degreewise and taking cohomology in degree
`n`.  This is `CategoryTheory.Functor.mapExtendNatIso` followed by
`ComplexShape.Embedding.extendFunctorHomologyIso`. -/
def extendUpNatMapHomologyNatIso {A : Type*} [Category* A] [Abelian A] {B : Type*} [Category* B]
    [Abelian B] (G : A ⥤ B) [G.Additive] (n : ℕ) :
    ComplexShape.embeddingUpNat.extendFunctor A ⋙
        G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) (n : ℤ) ≅
      G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) n :=
  Functor.isoWhiskerRight (Functor.mapExtendNatIso G ComplexShape.embeddingUpNat)
      (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) (n : ℤ)) ≪≫
    Functor.isoWhiskerLeft (G.mapHomologicalComplex (ComplexShape.up ℕ))
      (ComplexShape.embeddingUpNat.extendFunctorHomologyIso B n (n : ℤ) rfl)

omit [Preadditive A] in
/-- **The cosimplicial object of sections of a simplicial formal coproduct is contravariantly
functorial in that simplicial object.**  A morphism `ψ : E ⟶ E'` of simplicial formal coproducts
is in each degree a morphism of formal coproducts, which pulls sections on `E'` back to sections
on `E`; in the description
`FormalCoproduct.cosimplicialObjectFunctor E = evalOp ⋙ (whiskeringLeft _ _ _).obj E.rightOp`
this is precomposition with `NatTrans.rightOp ψ`. -/
def cosimplicialObjectFunctorMap
    {E E' : SimplicialObject (FormalCoproduct.{w} D)} (ψ : E ⟶ E') :
    FormalCoproduct.cosimplicialObjectFunctor.{w} (A := A) E' ⟶
      FormalCoproduct.cosimplicialObjectFunctor.{w} (A := A) E :=
  ((Functor.whiskeringLeft (Dᵒᵖ ⥤ A) ((FormalCoproduct.{w} D)ᵒᵖ ⥤ A)
    (CosimplicialObject A)).obj (FormalCoproduct.evalOp.{w} D A)).map
      ((Functor.whiskeringLeft _ _ A).map (NatTrans.rightOp ψ))

omit [Preadditive A] in
/-- `cosimplicialObjectFunctorMap` takes an identity to an identity. -/
lemma cosimplicialObjectFunctorMap_id (E : SimplicialObject (FormalCoproduct.{w} D)) :
    cosimplicialObjectFunctorMap.{w} (A := A) (𝟙 E) = 𝟙 _ := by
  simp only [cosimplicialObjectFunctorMap, NatTrans.rightOp_id, CategoryTheory.Functor.map_id]
  rfl

omit [Preadditive A] in
/-- `cosimplicialObjectFunctorMap` reverses composition. -/
lemma cosimplicialObjectFunctorMap_comp {E E' E'' : SimplicialObject (FormalCoproduct.{w} D)}
    (ψ : E ⟶ E') (φ : E' ⟶ E'') :
    cosimplicialObjectFunctorMap.{w} (A := A) (ψ ≫ φ) =
      cosimplicialObjectFunctorMap.{w} (A := A) φ ≫
        cosimplicialObjectFunctorMap.{w} (A := A) ψ := by
  simp only [cosimplicialObjectFunctorMap, NatTrans.rightOp_comp, Functor.map_comp]
  rfl

/-- **The sections complex `s(-(E))` of a simplicial formal coproduct is contravariantly
functorial in that simplicial object**: the alternating coface complex of
`cosimplicialObjectFunctorMap`.  This is what makes the hypercovering spectral sequence
functorial in the hypercovering. -/
def cochainComplexFunctorMap
    {E E' : SimplicialObject (FormalCoproduct.{w} D)} (ψ : E ⟶ E') :
    FormalCoproduct.cochainComplexFunctor.{w} (A := A) E' ⟶
      FormalCoproduct.cochainComplexFunctor.{w} (A := A) E :=
  ((Functor.whiskeringRight (Dᵒᵖ ⥤ A) (CosimplicialObject A)
    (CochainComplex A ℕ)).obj (AlgebraicTopology.alternatingCofaceMapComplex A)).map
      (cosimplicialObjectFunctorMap.{w} (A := A) ψ)

/-- `cochainComplexFunctorMap` takes an identity to an identity. -/
lemma cochainComplexFunctorMap_id (E : SimplicialObject (FormalCoproduct.{w} D)) :
    cochainComplexFunctorMap.{w} (A := A) (𝟙 E) = 𝟙 _ := by
  simp only [cochainComplexFunctorMap, cosimplicialObjectFunctorMap_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- `cochainComplexFunctorMap` reverses composition. -/
lemma cochainComplexFunctorMap_comp {E E' E'' : SimplicialObject (FormalCoproduct.{w} D)}
    (ψ : E ⟶ E') (φ : E' ⟶ E'') :
    cochainComplexFunctorMap.{w} (A := A) (ψ ≫ φ) =
      cochainComplexFunctorMap.{w} (A := A) φ ≫ cochainComplexFunctorMap.{w} (A := A) ψ := by
  simp only [cochainComplexFunctorMap, cosimplicialObjectFunctorMap_comp, Functor.map_comp]
  rfl

end Exactness

/-! ### The hypercovering cochain complex and its augmentation -/

section Augmentation

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (J : Pretopology C) (X : C) (K : SimplicialObject (FormalCoproduct.{w} (Over X)))

/-- Restricting an abelian sheaf to the objects over `X` is additive. -/
instance sectionsOnOverFunctor_additive : (sectionsOnOverFunctor.{w} J X).Additive := by
  dsimp only [sectionsOnOverFunctor]; infer_instance

/-- **The hypercovering cochain complex vanishes in negative degrees**, the index being extended
by zero from `ℕ`.  This is the hypothesis `zero_of_neg` of [Stacks, Tag 0133]. -/
lemma isZero_hypercoverCochainIntFunctor_obj_X
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (q : ℤ) (hq : q < 0) :
    IsZero (((hypercoverCochainIntFunctor.{w} J X K).obj F).X q) :=
  HomologicalComplex.isZero_extend_X _ _ q
    (fun i => by simp only [ComplexShape.embeddingUpNat_f]; omega)

/-- **`Ȟ^p(K, -)`, the `p`-th cohomology of the sections complex of `K`**, as a functor of a
presheaf of abelian groups on the objects over `X`.  This is the coefficient functor appearing on
the second page of [Stacks, Tag 01GY]. -/
def cechCohomologyOverFunctor (p : ℕ) :
    ((Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v w}) ⥤ AddCommGrpCat.{max u v w} :=
  FormalCoproduct.cochainComplexFunctor K ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v w} (ComplexShape.up ℕ) p

variable [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]

/-- The augmented simplicial presheaf attached to `K`, whose complex of free abelian sheaves
carries the augmentation of [Stacks, Tag 01GX]. -/
abbrev augmentedPresheafOf : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type (max u v w)) :=
  associatedAugmentedSimplicialPresheafOver.{w} K

/-- [Stacks, Tag 01GX] for the `ℤ`-indexed complexes: the hypercovering cochain complex functor
extended by zero is the Hom complex of the free abelian sheaves of `K` extended by zero. -/
def hypercoverCochainIntIso :
    hypercoverCochainIntFunctor.{w} J X K ≅
      freeAbelianSheafHomCxZ J.toGrothendieck (augmentedPresheafOf.{w} X K) :=
  Functor.isoWhiskerRight (hypercoverCochainIsoHomFreeAbelianSheafComplexFunctor J X K)
    (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u v w})

/-- **The sections of an abelian sheaf on `X` are the morphisms out of the free abelian sheaf on
the presheaf represented by `X`**, naturally in the sheaf.  This is
`evaluationIsoFreeAbelianSheafSections` with its source spelled `sheafSectionsFunctor`, which is
the spelling the comparison of [Stacks, Tag 0133] is assembled against; the two are the same
functor by definition. -/
@[sga "4 XVIII 1.4.24" "(a), special case"]
def sheafSectionsIsoFreeAbelianSheafSections :
    sheafSectionsFunctor.{w} J X ≅
      freeAbelianSheafSections J.toGrothendieck (augmentedPresheafOf.{w} X K) :=
  evaluationIsoFreeAbelianSheafSections J.toGrothendieck K

/-- **The augmentation `Γ(X, -)[0] ⟶ s(-(K))`**, as a natural transformation of functors of the
coefficient sheaf.  It is
`CategoryTheory.SimplicialObject.Augmented.freeAbelianSheafEpsNatTrans` conjugated by the two
identifications of [Stacks, Tag 01GX] and of the Yoneda description of the sections on `X`. -/
def sectionsEpsNatTrans :
    sheafSectionsFunctor.{w} J X ⋙
        HomologicalComplex.single AddCommGrpCat.{max u v w} (ComplexShape.up ℤ) 0 ⟶
      hypercoverCochainIntFunctor.{w} J X K :=
  Functor.whiskerRight (sheafSectionsIsoFreeAbelianSheafSections J X K).hom
      (HomologicalComplex.single AddCommGrpCat.{max u v w} (ComplexShape.up ℤ) 0) ≫
    freeAbelianSheafEpsNatTrans J.toGrothendieck (augmentedPresheafOf.{w} X K) ≫
      (hypercoverCochainIntIso J X K).inv

/-- The augmentation at a single coefficient sheaf. -/
def sectionsEps (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    (HomologicalComplex.single AddCommGrpCat.{max u v w} (ComplexShape.up ℤ) 0).obj
        ((sheafSectionsFunctor.{w} J X).obj F) ⟶
      (hypercoverCochainIntFunctor.{w} J X K).obj F :=
  (sectionsEpsNatTrans J X K).app F

/-- The augmentation, unfolded as the conjugate of
`CategoryTheory.SimplicialObject.Augmented.freeAbelianSheafEps`. -/
lemma sectionsEps_eq (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    sectionsEps J X K F =
      (HomologicalComplex.single AddCommGrpCat.{max u v w} (ComplexShape.up ℤ) 0).map
          ((sheafSectionsIsoFreeAbelianSheafSections J X K).hom.app F) ≫
        freeAbelianSheafEps J.toGrothendieck (augmentedPresheafOf.{w} X K) F ≫
          (hypercoverCochainIntIso J X K).inv.app F :=
  rfl

/-- **The augmentation is natural in the coefficient sheaf**, which is the hypothesis `hε` of
[Stacks, Tag 0133]'s comparison. -/
lemma sectionsEps_naturality
    {F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}} (f : F ⟶ G) :
    (HomologicalComplex.single AddCommGrpCat.{max u v w} (ComplexShape.up ℤ) 0).map
          ((sheafSectionsFunctor.{w} J X).map f) ≫ sectionsEps J X K G =
      sectionsEps J X K F ≫ (hypercoverCochainIntFunctor.{w} J X K).map f :=
  (sectionsEpsNatTrans J X K).naturality f

/-- **The augmentation is a quasi-isomorphism at an injective sheaf.**  The sections complex of a
hypercovering with injective coefficients is acyclic in positive degrees ([Stacks, Tag 01GW]) and
its degree-zero cohomology is the sections on `X` ([Stacks, Tag 01GV]); the statement is
transported from the Hom complex spelling, in which it is
`CategoryTheory.SimplicialObject.Augmented.quasiIso_freeAbelianSheafEps`. -/
lemma sectionsEps_conj (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    (HomologicalComplex.single AddCommGrpCat.{max u v w} (ComplexShape.up ℤ) 0).map
          ((sheafSectionsIsoFreeAbelianSheafSections J X K).inv.app F) ≫
        sectionsEps J X K F =
      freeAbelianSheafEps J.toGrothendieck (augmentedPresheafOf.{w} X K) F ≫
        (hypercoverCochainIntIso J X K).inv.app F := by
  rw [sectionsEps_eq, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The augmentation is a quasi-isomorphism at an injective sheaf.**  The sections complex of a
hypercovering with injective coefficients is acyclic in positive degrees ([Stacks, Tag 01GW]) and
its degree-zero cohomology is the sections on `X` ([Stacks, Tag 01GV]); the statement is
transported from the Hom complex spelling, in which it is
`CategoryTheory.SimplicialObject.Augmented.quasiIso_freeAbelianSheafEps`. -/
theorem quasiIso_sectionsEps (hK : IsHypercovering J K)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) [Injective F] :
    QuasiIso (sectionsEps J X K F) := by
  have h := isLocallySurjective_of_isHypercovering.{w} J K hK
  have hq : QuasiIso (freeAbelianSheafEps J.toGrothendieck (augmentedPresheafOf.{w} X K) F) :=
    quasiIso_freeAbelianSheafEps J.toGrothendieck (augmentedPresheafOf.{w} X K)
      h.1 h.2.1 h.2.2 F
  exact quasiIso_of_arrow_mk_iso
    (freeAbelianSheafEps J.toGrothendieck (augmentedPresheafOf.{w} X K) F)
    (sectionsEps J X K F)
    (Arrow.isoMk
      ((HomologicalComplex.single AddCommGrpCat.{max u v w} (ComplexShape.up ℤ) 0).mapIso
        ((sheafSectionsIsoFreeAbelianSheafSections J X K).symm.app F))
      ((hypercoverCochainIntIso J X K).symm.app F)
      (sectionsEps_conj J X K F))

end Augmentation

/-! ### The double complex of a complex of abelian sheaves -/

section DoubleComplex

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (J : Pretopology C) (X : C) (K : SimplicialObject (FormalCoproduct.{w} (Over X)))

/-- **The double complex of a complex of abelian sheaves, with the inner index in `ℕ`**: in outer
degree `p` the sections complex `s(Y^p(K))` of the `p`-th term.  The **degree in the given complex
is the outer index and the hypercovering degree the inner one**; see the module documentation for
why that is forced. -/
def hypercoverDoubleNatFunctor :
    CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℤ ⥤
      HomologicalComplex (CochainComplex AddCommGrpCat.{max u v w} ℕ) (ComplexShape.up ℤ) :=
  (hypercoverCochainNatFunctor.{w} J X K).mapHomologicalComplex (ComplexShape.up ℤ)

/-- **The double complex of a complex of abelian sheaves**, over `ℤ × ℤ`: the inner index of
`hypercoverDoubleNatFunctor` extended by zero. -/
def hypercoverDoubleFunctor :
    CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℤ ⥤
      HomologicalComplex₂ AddCommGrpCat.{max u v w} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (hypercoverCochainIntFunctor.{w} J X K).mapHomologicalComplex (ComplexShape.up ℤ)

/-- `hypercoverDoubleFunctor` is `hypercoverDoubleNatFunctor` with the inner index extended by
zero. -/
lemma hypercoverDoubleFunctor_eq :
    hypercoverDoubleFunctor.{w} J X K =
      hypercoverDoubleNatFunctor.{w} J X K ⋙
        (ComplexShape.embeddingUpNat.extendFunctor
          AddCommGrpCat.{max u v w}).mapHomologicalComplex (ComplexShape.up ℤ) :=
  rfl

/-- **The double complex vanishes in negative inner degree**, the inner index being extended by
zero from `ℕ`. -/
lemma isZero_hypercoverDoubleFunctor_X_X_of_inner_neg
    (Y : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℤ) (p q : ℤ)
    (hq : q < 0) :
    IsZero ((((hypercoverDoubleFunctor.{w} J X K).obj Y).X p).X q) :=
  isZero_hypercoverCochainIntFunctor_obj_X J X K (Y.X p) q hq

/-- **The double complex vanishes in an outer degree where the given complex does**, the sections
complex functor being additive. -/
lemma isZero_hypercoverDoubleFunctor_X
    (Y : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℤ) (p : ℤ)
    (hp : IsZero (Y.X p)) :
    IsZero (((hypercoverDoubleFunctor.{w} J X K).obj Y).X p) :=
  (hypercoverCochainIntFunctor.{w} J X K).map_isZero hp

variable [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]

/-- **The coefficient half of the second-page identification.**  Taking the homology of the double
complex of a complex of abelian sheaves, first in the resolution direction and then in the
hypercovering direction, is the hypercovering cohomology of the homology of the complex of
*presheaves* underlying it, naturally in the complex.  This is the statement that the sections
complex functor of `K` commutes with homology, which it does because it is exact on presheaves
(`cochainComplexFunctor_preservesHomology`), together with the fact that extension by zero
does. -/
def hypercoverDoubleHomologyNatIso (p : ℕ) (q : ℤ) :
    hypercoverDoubleFunctor.{w} J X K ⋙
        HomologicalComplex₂.homologyIIHomologyIFunctor AddCommGrpCat.{max u v w} (p : ℤ) q ≅
      (sectionsOnOverFunctor.{w} J X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor ((Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v w})
            (ComplexShape.up ℤ) q ⋙
          cechCohomologyOverFunctor.{w} X K p :=
  haveI := cochainComplexFunctor_preservesHomology.{w}
    (A := AddCommGrpCat.{max u v w})
    (fun I => hasExactLimitsOfShape_discrete_addCommGrpCat.{max u v, w} I) K
  Functor.isoWhiskerLeft (hypercoverDoubleNatFunctor.{w} J X K)
      (Functor.isoWhiskerRight
          (Functor.mapHomologicalComplexHomologyIso
            (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u v w})
            (ComplexShape.up ℤ) q)
          (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v w}
            (ComplexShape.up ℤ) (p : ℤ)) ≪≫
        Functor.isoWhiskerLeft
          (HomologicalComplex.homologyFunctor
            (CochainComplex AddCommGrpCat.{max u v w} ℕ) (ComplexShape.up ℤ) q)
          (ComplexShape.embeddingUpNat.extendFunctorHomologyIso
            AddCommGrpCat.{max u v w} p (p : ℤ) rfl)) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        ((sectionsOnOverFunctor.{w} J X).mapHomologicalComplex (ComplexShape.up ℤ))
        (Functor.mapHomologicalComplexHomologyIso
          (FormalCoproduct.cochainComplexFunctor (A := AddCommGrpCat.{max u v w}) K)
          (ComplexShape.up ℤ) q))
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v w} (ComplexShape.up ℕ) p)

omit [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}] in
/-- **First-quadrant vanishing for the double complex** of a complex of abelian sheaves vanishing
in negative degrees: `H^p_{II}(H^q_I(A^{•,•}))` vanishes as soon as `p < 0` or `q < 0`.  In the
first case the complex `H^q_I(A^{•,•})` is zero in inner degree `p`, in the second the outer
complex is zero, hence exact, at `q`. -/
lemma isZero_homologyIIHomologyI_hypercoverDoubleFunctor
    (Y : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℤ)
    (hY : ∀ p : ℤ, p < 0 → IsZero (Y.X p)) (p q : ℤ) (h : p < 0 ∨ q < 0) :
    IsZero ((HomologicalComplex₂.homologyIIHomologyIFunctor
      AddCommGrpCat.{max u v w} p q).obj ((hypercoverDoubleFunctor.{w} J X K).obj Y)) := by
  rcases h with hp | hq
  · refine (Iso.isZero_iff ((HomologicalComplex.homologyFunctor
        AddCommGrpCat.{max u v w} (ComplexShape.up ℤ) p).mapIso
      ((Functor.mapHomologicalComplexHomologyIso
        (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u v w})
        (ComplexShape.up ℤ) q).app
          ((hypercoverDoubleNatFunctor.{w} J X K).obj Y)))).2 ?_
    refine ShortComplex.isZero_homology_of_isZero_X₂ _ ?_
    exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p
      fun i => by change ((i : ℕ) : ℤ) ≠ p; omega
  · refine Functor.map_isZero (HomologicalComplex.homologyFunctor
      AddCommGrpCat.{max u v w} (ComplexShape.up ℤ) p) ?_
    refine ShortComplex.isZero_homology_of_isZero_X₂ _ ?_
    exact isZero_hypercoverDoubleFunctor_X.{w} J X K Y q (hY q hq)

end DoubleComplex

/-! ### The spectral sequence and its second page -/

section Sequence

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (J : Pretopology C) (X : C) (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w}]

/-- **Abelian sheaves on a site have enough injectives** ([Stacks, Tag 01DP]), so the chosen
injective resolutions used below exist.  Kept a local instance: it is not a fact about the
hypercovering, only the ambient input the construction needs. -/
@[sga "4 I 7.13" "special case",
  sga "4 V 2.5.2" "special case",
  sga "4½ Arcata 1.6.3" "special case"]
theorem enoughInjectives_sheafAddCommGrpCat :
    EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :=
  Sheaf.enoughInjectives_addCommGrpCat.{max u v w} J.toGrothendieck

attribute [local instance] enoughInjectives_sheafAddCommGrpCat

/-- **The double complex of an `ℕ`-indexed complex of abelian sheaves**: the complex extended by
zero in the negative degrees, fed to `hypercoverDoubleFunctor`.  This is the functor the chosen
injective resolution is plugged into. -/
def hypercoverDoubleOfNatFunctor :
    CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℕ ⥤
      HomologicalComplex₂ AddCommGrpCat.{max u v w} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  ComplexShape.embeddingUpNat.extendFunctor
      (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ⋙
    hypercoverDoubleFunctor.{w} J X K

/-- A homotopy between morphisms of complexes of sheaves induces a homotopy between the induced
morphisms of double complexes: extension by zero carries homotopies to homotopies and the
hypercovering cochain complex functor is additive. -/
def hypercoverDoubleHomotopy
    {Y Z : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℕ} {φ ψ : Y ⟶ Z}
    (H : Homotopy φ ψ) :
    Homotopy ((hypercoverDoubleOfNatFunctor.{w} J X K).map φ)
      ((hypercoverDoubleOfNatFunctor.{w} J X K).map ψ) :=
  (hypercoverCochainIntFunctor.{w} J X K).mapHomotopy (H.extend ComplexShape.embeddingUpNat)

/-- **The double complex of a sheaf of abelian groups**: `A^{p,q}(F) = s(I^p(K))^q` for the chosen
injective resolution `I^•(F)` of `F`, with the resolution degree outer. -/
def hypercoverDouble (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    HomologicalComplex₂ AddCommGrpCat.{max u v w} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (hypercoverDoubleOfNatFunctor.{w} J X K).obj (injectiveResolution F).cocomplex

/-- The morphism of double complexes attached to a morphism of sheaves: the double complex of a
chosen descent of that morphism to the chosen injective resolutions.  This is functorial only up
to homotopy, which is all `HomologicalComplex₂.e₂FunctorOfHomotopyClasses` needs. -/
def hypercoverDoubleMap {F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}} (f : F ⟶ G) :
    hypercoverDouble.{w} J X K F ⟶ hypercoverDouble.{w} J X K G :=
  (hypercoverDoubleOfNatFunctor.{w} J X K).map
    (InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F))

/-- `hypercoverDoubleMap` sends an identity to a filtered homotopy class of the identity. -/
lemma filteredHomotopy₂_hypercoverDoubleMap_id
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    HomologicalComplex₂.FilteredHomotopy₂ (hypercoverDoubleMap.{w} J X K (𝟙 F)) (𝟙 _) :=
  HomologicalComplex₂.filteredHomotopy₂_of_homotopy
    ((hypercoverDoubleHomotopy.{w} J X K
        (InjectiveResolution.descIdHomotopy F (injectiveResolution F))).trans
      (Homotopy.ofEq ((hypercoverDoubleOfNatFunctor.{w} J X K).map_id _)))

/-- `hypercoverDoubleMap` is multiplicative up to filtered homotopy. -/
lemma filteredHomotopy₂_hypercoverDoubleMap_comp
    {F G H : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}} (f : F ⟶ G) (g : G ⟶ H) :
    HomologicalComplex₂.FilteredHomotopy₂ (hypercoverDoubleMap.{w} J X K (f ≫ g))
      (hypercoverDoubleMap.{w} J X K f ≫ hypercoverDoubleMap.{w} J X K g) :=
  HomologicalComplex₂.filteredHomotopy₂_of_homotopy
    ((hypercoverDoubleHomotopy.{w} J X K
        (InjectiveResolution.descCompHomotopy f g (injectiveResolution F)
          (injectiveResolution G) (injectiveResolution H))).trans
      (Homotopy.ofEq ((hypercoverDoubleOfNatFunctor.{w} J X K).map_comp _ _)))

/-- **The hypercovering-to-cohomology spectral sequence on `ℤ × ℤ`**, functorial in the sheaf: the
second spectral sequence of the double complex of an injective resolution, presented from its
second page. -/
def hypercoverE₂Functor :
    Sheaf J.toGrothendieck AddCommGrpCat.{max u v w} ⥤
      E₂CohomologicalSpectralSequence AddCommGrpCat.{max u v w} :=
  HomologicalComplex₂.e₂FunctorOfHomotopyClasses (hypercoverDouble.{w} J X K)
    (hypercoverDoubleMap.{w} J X K) (filteredHomotopy₂_hypercoverDoubleMap_id.{w} J X K)
    (fun f g => filteredHomotopy₂_hypercoverDoubleMap_comp.{w} J X K f g)

/-- The double complex of the chosen injective resolution vanishes in negative outer degree. -/
lemma isZero_resolutionExtend_X (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) (p : ℤ)
    (hp : p < 0) :
    IsZero (((ComplexShape.embeddingUpNat.extendFunctor
      (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w})).obj
        (injectiveResolution F).cocomplex).X p) :=
  HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p
    fun i => by change ((i : ℕ) : ℤ) ≠ p; omega

/-- The hypercovering spectral sequence of a sheaf is first quadrant from its second page on. -/
lemma isFirstQuadrant_hypercoverE₂Functor
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    CategoryTheory.SpectralSequence.IsFirstQuadrant (u := fun r => (r, 1 - r))
      ((hypercoverE₂Functor.{w} J X K).obj F) :=
  HomologicalComplex₂.isFirstQuadrant_e₂SpectralSequence₂Functor _
    (hypercoverDouble.{w} J X K F) fun p q h =>
      isZero_homologyIIHomologyI_hypercoverDoubleFunctor.{w} J X K _
        (isZero_resolutionExtend_X J F) p q h

/-- **The `sequence` field of `HypercoveringSpectralSequenceData`**: the functorial first-quadrant
`E₂` cohomological spectral sequence of the hypercovering `K`, carried on `ℕ × ℕ`. -/
def hypercoverSpectralSequenceFunctor :
    Sheaf J.toGrothendieck AddCommGrpCat.{max u v w} ⥤
      E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{max u v w} :=
  CategoryTheory.SpectralSequence.natRestrictE₂Comp (hypercoverE₂Functor.{w} J X K)
    (isFirstQuadrant_hypercoverE₂Functor.{w} J X K)


/-! ### The second page -/

/-- **The homology of the restriction of an `ℕ`-indexed complex of abelian sheaves**: extending
the complex by zero and taking homology in degree `(q : ℤ)` is taking homology in degree `q`.
This is `extendUpNatMapHomologyNatIso` for the restriction to `Over X`. -/
def resolutionPresheafHomologyNatIso (q : ℕ) :
    ComplexShape.embeddingUpNat.extendFunctor
          (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ⋙
        (sectionsOnOverFunctor.{w} J X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomologicalComplex.homologyFunctor ((Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v w})
            (ComplexShape.up ℤ) (q : ℤ) ≅
      (sectionsOnOverFunctor.{w} J X).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor ((Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v w})
          (ComplexShape.up ℕ) q :=
  extendUpNatMapHomologyNatIso (sectionsOnOverFunctor.{w} J X) q

/-- **[Stacks, Tag 0130] (6) for the hypercovering spectral sequence.**  The second page of
`hypercoverE₂Functor` at `((p : ℤ), (q : ℤ))` is `H^p_{II}(H^q_I(A^{•,•}(F)))`. -/
def hypercoverPageTwoAppIso (p q : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    (hypercoverE₂Functor.{w} J X K ⋙
        CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
          HomologicalComplex.eval _ _ ((p : ℤ), (q : ℤ))).obj F ≅
      (HomologicalComplex₂.homologyIIHomologyIFunctor
        AddCommGrpCat.{max u v w} (p : ℤ) (q : ℤ)).obj (hypercoverDouble.{w} J X K F) :=
  HomologicalComplex₂.isoTwoPageTotalFiltration₂ (hypercoverDouble.{w} J X K F) _
    (HomologicalComplex₂.pageIso₂ _) (HomologicalComplex₂.exists_delta₂ _) (p : ℤ) (q : ℤ)

/-- `hypercoverPageTwoAppIso` is natural in the sheaf, for the morphisms `hypercoverDoubleMap` of
double complexes.  This is
`HomologicalComplex₂.pageTwoIso_naturality_of_homotopyClasses`. -/
lemma hypercoverPageTwoAppIso_naturality (p q : ℕ)
    {F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}} (f : F ⟶ G) :
    (hypercoverE₂Functor.{w} J X K ⋙
          CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
            HomologicalComplex.eval _ _ ((p : ℤ), (q : ℤ))).map f ≫
        (hypercoverPageTwoAppIso.{w} J X K p q G).hom =
      (hypercoverPageTwoAppIso.{w} J X K p q F).hom ≫
        (HomologicalComplex₂.homologyIIHomologyIFunctor
          AddCommGrpCat.{max u v w} (p : ℤ) (q : ℤ)).map
            (hypercoverDoubleMap.{w} J X K f) :=
  HomologicalComplex₂.pageTwoIso_naturality_of_homotopyClasses
    (hypercoverDouble.{w} J X K) (hypercoverDoubleMap.{w} J X K)
    (filteredHomotopy₂_hypercoverDoubleMap_id.{w} J X K)
    (fun f g => filteredHomotopy₂_hypercoverDoubleMap_comp.{w} J X K f g) f (p : ℤ) (q : ℤ)

/-- **The coefficient comparison for an `ℕ`-indexed complex of abelian sheaves**: taking the
homology of the double complex of the extension of such a complex, first in the resolution
direction and then in the hypercovering direction, is the hypercovering cohomology of the homology
of the restricted complex of presheaves.  Composite of `hypercoverDoubleHomologyNatIso` and
`resolutionPresheafHomologyNatIso`. -/
def hypercoverResolutionCoefficientNatIso (p q : ℕ) :
    ComplexShape.embeddingUpNat.extendFunctor
          (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ⋙
        hypercoverDoubleFunctor.{w} J X K ⋙
          HomologicalComplex₂.homologyIIHomologyIFunctor
            AddCommGrpCat.{max u v w} (p : ℤ) (q : ℤ) ≅
      (sectionsOnOverFunctor.{w} J X).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor ((Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v w})
            (ComplexShape.up ℕ) q ⋙
          cechCohomologyOverFunctor.{w} X K p :=
  Functor.isoWhiskerLeft
      (ComplexShape.embeddingUpNat.extendFunctor
        (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}))
      (hypercoverDoubleHomologyNatIso.{w} J X K p (q : ℤ)) ≪≫
    Functor.isoWhiskerRight (resolutionPresheafHomologyNatIso.{w} J X q)
      (cechCohomologyOverFunctor.{w} X K p)

/-- `hypercoverResolutionCoefficientNatIso` at the chosen injective resolution of a sheaf, with
the coefficient presheaf written as the `ℕ`-indexed homology of the restricted resolution. -/
def hypercoverDoubleHomologyIso (p q : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    (HomologicalComplex₂.homologyIIHomologyIFunctor
        AddCommGrpCat.{max u v w} (p : ℤ) (q : ℤ)).obj (hypercoverDouble.{w} J X K F) ≅
      (cechCohomologyOverFunctor.{w} X K p).obj
        ((HomologicalComplex.homologyFunctor ((Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v w})
          (ComplexShape.up ℕ) q).obj
            (((sectionsOnOverFunctor.{w} J X).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex)) :=
  (hypercoverResolutionCoefficientNatIso.{w} J X K p q).app (injectiveResolution F).cocomplex

/-- `hypercoverDoubleHomologyIso` read as a naturality square for `hypercoverDoubleMap`. -/
lemma hypercoverDoubleHomologyIso_naturality (p q : ℕ)
    {F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}} (f : F ⟶ G) :
    (HomologicalComplex₂.homologyIIHomologyIFunctor
          AddCommGrpCat.{max u v w} (p : ℤ) (q : ℤ)).map (hypercoverDoubleMap.{w} J X K f) ≫
        (hypercoverDoubleHomologyIso.{w} J X K p q G).hom =
      (hypercoverDoubleHomologyIso.{w} J X K p q F).hom ≫
        (cechCohomologyOverFunctor.{w} X K p).map
          ((HomologicalComplex.homologyFunctor ((Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v w})
            (ComplexShape.up ℕ) q).map
              (((sectionsOnOverFunctor.{w} J X).mapHomologicalComplex
                (ComplexShape.up ℕ)).map
                  (InjectiveResolution.desc f (injectiveResolution G)
                    (injectiveResolution F)))) := by
  have h := (hypercoverResolutionCoefficientNatIso.{w} J X K p q).hom.naturality
    (InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F))
  dsimp only [Functor.comp_map] at h
  exact h

/-- **The coefficient comparison at a sheaf**: `H^p_{II}(H^q_I(A^{•,•}(F))) ≅ Ȟ^p(K, H̲^q(F))`.
This is `hypercoverDoubleHomologyIso` followed by the computation of the cohomology presheaf
`H̲^q(F)` by the chosen injective resolution of `F`. -/
@[simps]
def hypercoverCoefficientIso (p q : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    (HomologicalComplex₂.homologyIIHomologyIFunctor
        AddCommGrpCat.{max u v w} (p : ℤ) (q : ℤ)).obj (hypercoverDouble.{w} J X K F) ≅
      ((sectionsOnOverFunctor.{w} J X).rightDerived q ⋙
        cechCohomologyOverFunctor.{w} X K p).obj F where
  hom := (hypercoverDoubleHomologyIso.{w} J X K p q F).hom ≫
    (cechCohomologyOverFunctor.{w} X K p).map
      ((injectiveResolution F).isoRightDerivedObj (sectionsOnOverFunctor.{w} J X) q).inv
  inv := (cechCohomologyOverFunctor.{w} X K p).map
      ((injectiveResolution F).isoRightDerivedObj (sectionsOnOverFunctor.{w} J X) q).hom ≫
    (hypercoverDoubleHomologyIso.{w} J X K p q F).inv
  hom_inv_id := by
    rw [Category.assoc, ← Category.assoc
      ((cechCohomologyOverFunctor.{w} X K p).map _), ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]
  inv_hom_id := by
    rw [Category.assoc, ← Category.assoc
      ((hypercoverDoubleHomologyIso.{w} J X K p q F).inv), Iso.inv_hom_id,
      Category.id_comp, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
    rfl

/-- The coefficient comparison is natural in the sheaf, for the morphisms `hypercoverDoubleMap`
of double complexes. -/
lemma hypercoverCoefficientIso_naturality (p q : ℕ)
    {F G : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}} (f : F ⟶ G) :
    (HomologicalComplex₂.homologyIIHomologyIFunctor
          AddCommGrpCat.{max u v w} (p : ℤ) (q : ℤ)).map (hypercoverDoubleMap.{w} J X K f) ≫
        (hypercoverCoefficientIso.{w} J X K p q G).hom =
      (hypercoverCoefficientIso.{w} J X K p q F).hom ≫
        ((sectionsOnOverFunctor.{w} J X).rightDerived q ⋙
          cechCohomologyOverFunctor.{w} X K p).map f := by
  have h3 := InjectiveResolution.isoRightDerivedObj_inv_naturality f
    (injectiveResolution F) (injectiveResolution G) _
    (InjectiveResolution.desc_commutes_zero f (injectiveResolution G)
      (injectiveResolution F)) (sectionsOnOverFunctor.{w} J X) q
  dsimp only [Functor.comp_map] at h3
  rw [hypercoverCoefficientIso_hom, hypercoverCoefficientIso_hom,
    reassoc_of% hypercoverDoubleHomologyIso_naturality.{w} J X K p q f, ← Functor.map_comp]
  dsimp only [Functor.comp_map]
  rw [Category.assoc, ← Functor.map_comp, h3]

/-- **The second page of the hypercovering spectral sequence, on `ℤ × ℤ`.**  At
`((p : ℤ), (q : ℤ))` it is `Ȟ^p(K, H̲^q(F))`, naturally in `F`: the spectral-sequence
identification `''E_2^{p,q} ≅ H^p_{II}(H^q_I(A^{•,•}(F)))` of [Stacks, Tag 0130] (6), followed by
the coefficient comparison. -/
def hypercoverPageTwoIsoInt (p q : ℕ) :
    hypercoverE₂Functor.{w} J X K ⋙
        CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
          HomologicalComplex.eval _ _ ((p : ℤ), (q : ℤ)) ≅
      (sectionsOnOverFunctor.{w} J X).rightDerived q ⋙
        cechCohomologyOverFunctor.{w} X K p :=
  NatIso.ofComponents
    (fun F => hypercoverPageTwoAppIso.{w} J X K p q F ≪≫
      hypercoverCoefficientIso.{w} J X K p q F)
    (fun f => by
      rw [Iso.trans_hom, Iso.trans_hom, ← Category.assoc,
        hypercoverPageTwoAppIso_naturality.{w} J X K p q f, Category.assoc,
        hypercoverCoefficientIso_naturality.{w} J X K p q f, Category.assoc])

/-- **The `pageTwoIso` field of `HypercoveringSpectralSequenceData`**: the second page of the
hypercovering spectral sequence at `(p, q) : ℕ × ℕ` is `Ȟ^p(K, H̲^q(F))`, naturally in the sheaf
`F`.  The passage from `ℤ × ℤ` to `ℕ × ℕ` is on the nose, by
`CategoryTheory.SpectralSequence.natRestrictE₂Comp_pageTwoIso`. -/
def hypercoverPageTwoIso (p q : ℕ) :
    hypercoverSpectralSequenceFunctor.{w} J X K ⋙
        CategoryTheory.SpectralSequence.pageFunctor _ _ 2 2 ⋙
          HomologicalComplex.eval _ _ (p, q) ≅
      (sectionsOnOverFunctor.{w} J X).rightDerived q ⋙
        cechCohomologyOverFunctor.{w} X K p :=
  CategoryTheory.SpectralSequence.natRestrictE₂Comp_pageTwoIso
      (hypercoverE₂Functor.{w} J X K)
      (isFirstQuadrant_hypercoverE₂Functor.{w} J X K) p q ≪≫
    hypercoverPageTwoIsoInt.{w} J X K p q

end Sequence

end Stacks.CategoryTheory.Hypercovering

end
