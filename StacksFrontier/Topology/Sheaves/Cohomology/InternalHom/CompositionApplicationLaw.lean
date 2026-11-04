module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedAssociatorToTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationCompositionReduction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCompositionApplicationPinning
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingAssociativity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DualityDescentDiagrams
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.AssociatorOnLocalSections

/-!
# Composition against application in `D(O_X)`

Let `(X, O_X)` be a ringed space and let `K`, `L`, `M` be objects of `D(O_X)`.  Write
`cmp : RSheafHom(L, M) ⊗^L RSheafHom(K, L) ⟶ RSheafHom(K, M)` for the composition morphism of
Stacks 0A8V and `ε_{K,M} : RSheafHom(K, M) ⊗^L K ⟶ M` for the application morphism of
Stacks 08J8.  Then

`(cmp ⊗ 1_K) ≫ ε_{K,M} = α ≫ (1 ⊗ ε_{K,L}) ≫ ε_{L,M}`:

applying a composite is applying the two factors in turn.

## Main results

* `Stacks.SheafOfModules.derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_model`:
  the identity on the classes of complexes `P`, `J`, `I` with `J` and `I` K-injective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

/-- **Composition against application, transported along comparisons**, for an arbitrary
bifunctor `F`.  The conclusion is an identity of morphisms out of `F(F(RH, RG), QP)`; after
precomposition with the invertible `F(F(σH, σG), QP)` both sides are computed by the hypotheses
on the source side of the comparisons `σ`. -/
private alias comp_app_descent := Stacks.Cohomology.DualityDescent.comp_app_descent

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- The comparison `Q(SheafHom(B, C)) ⟶ RSheafHom(QB, QC)` of Stacks 08DM. -/
abbrev homComparisonSpace (B C : CochainComplex (StructureSheafModules Rc) ℤ) :
    DerivedCategory.Q.obj (RingedSite.sheafHomComplex (ringedSite Rc) B C).obj ⟶
      ((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj B))).obj (DerivedCategory.Q.obj C) :=
  RingedSite.strictlyPerfectHomComparison (ringedSite Rc)
    (RingedSite.derivedInternalHomOfBifunctor (ringedSite Rc)) B C

/-- **The application morphism of Stacks 08J8 against a cochain-level transpose.**  For complexes
`A`, `B`, `C` of `O_X`-modules and `f : A ⟶ SheafHom(B, C)`,
`(Q f ⊗ 1) ≫ (σ ⊗ 1) ≫ ε = t_{A,B} ≫ Q(curry f)`, with no hypothesis on the complexes. -/
theorem derivedSheafHomCounit_homComparison_curry
    (A B C : CochainComplex (StructureSheafModules Rc) ℤ)
    (f : A ⟶ (RingedSite.sheafHomComplex (ringedSite Rc) B C).obj) :
    ((derivedTensor Rc).map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj B) ≫
        ((derivedTensor Rc).map (homComparisonSpace Rc B C)).app (DerivedCategory.Q.obj B) ≫
        derivedSheafHomCounit Rc (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C) =
      (canonicalDerivedTensorProduct (ringedSite Rc)).toTensor A B ≫
        DerivedCategory.Q.map (RingedSite.curryHomEquiv (ringedSite Rc) A B C f) := by
  obtain ⟨B', v, hB', _⟩ := Stacks.SheafOfModules.exists_kFlat_quasiIso (ringedSite Rc) B
  have h := RingedSite.derivedApplication_curryingSquare_toTensor (ringedSite Rc) A B B' C v
    hB' _ _ (RingedSite.strictlyPerfectHomComparison_naturality_source (ringedSite Rc)
      (RingedSite.derivedInternalHomOfBifunctor (ringedSite Rc)) B B' C v).symm
    (RingedSite.derivedSheafHomGlobalSectionsEquiv_precomposedHomComparisonClass (ringedSite Rc)
      (RingedSite.derivedInternalHomOfBifunctor (ringedSite Rc)) B' C _ hB'
      (RingedSite.isKFlat_kFlatHomResolution (ringedSite Rc) B' C)
      (RingedSite.kFlatHomResolutionMap (ringedSite Rc) B' C)) f
  rw [derivedSheafHomCounit_eq, derivedSheafHomTensorEquiv_eq, h]

/-- **The application morphism of Stacks 08J8 is the cochain-level evaluation**, conjugated by
the comparison `σ` of Stacks 08DM and the canonical map `t` of Stacks 06YU:
`(σ ⊗ 1) ≫ ε = t ≫ Q(ev)`, with no hypothesis on the complexes. -/
theorem derivedSheafHomCounit_homComparison (B C : CochainComplex (StructureSheafModules Rc) ℤ) :
    ((derivedTensor Rc).map (homComparisonSpace Rc B C)).app (DerivedCategory.Q.obj B) ≫
        derivedSheafHomCounit Rc (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C) =
      (canonicalDerivedTensorProduct (ringedSite Rc)).toTensor _ B ≫
        DerivedCategory.Q.map (RingedSite.cochainEvaluation (ringedSite Rc) B C) := by
  have h := derivedSheafHomCounit_homComparison_curry Rc _ B C (𝟙 _)
  have hce : RingedSite.curryHomEquiv (ringedSite Rc) _ B C
      (𝟙 (RingedSite.sheafHomComplex (ringedSite Rc) B C).obj) =
      RingedSite.cochainEvaluation (ringedSite Rc) B C := by
    rw [← RingedSite.curryHomEquiv_symm_cochainEvaluation]
    exact (RingedSite.curryHomEquiv (ringedSite Rc) _ B C).apply_symm_apply _
  simpa only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, hce] using h

/-- The composition morphism of Stacks 0A8V on a ringed space is the ringed-site one at the derived
internal Hom of the bifunctor. -/
theorem derivedSheafHomComposition_eq_ofBifunctor (K L M : DerivedCategory (StructureSheafModules Rc)) :
    derivedSheafHomComposition Rc K L M = RingedSite.derivedSheafHomComposition (ringedSite Rc)
      (canonicalDerivedTensorProduct (ringedSite Rc))
      (RingedSite.derivedInternalHomOfBifunctor (ringedSite Rc)) K L M := rfl

/-- **The composition morphism of Stacks 0A8V against the comparison of Stacks 08DM**: conjugated
by `σ` on both tensor factors and on the target, it is the class of the transpose of the double
contraction. -/
theorem homComparison_derivedSheafHomComposition (P J I : CochainComplex (StructureSheafModules Rc) ℤ) :
    ((derivedTensor Rc).map (homComparisonSpace Rc J I)).app
        (DerivedCategory.Q.obj (RingedSite.sheafHomComplex (ringedSite Rc) P J).obj) ≫
      ((derivedTensor Rc).obj _).map (homComparisonSpace Rc P J) ≫
      derivedSheafHomComposition Rc (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj J)
        (DerivedCategory.Q.obj I) =
    (canonicalDerivedTensorProduct (ringedSite Rc)).toTensor _ _ ≫
      DerivedCategory.Q.map (RingedSite.curryHomEquiv (ringedSite Rc) _ _ _
        (RingedSite.doubleContraction (ringedSite Rc) P J I)) ≫ homComparisonSpace Rc P I := by
  have h := RingedSite.strictlyPerfectHomComparison_composition_doubleContraction (ringedSite Rc)
    P J I
  rw [derivedSheafHomComposition_eq_ofBifunctor]
  exact (Category.assoc _ _ _).symm.trans h

/-- The canonical map of Stacks 06YU is natural in its second complex. -/
theorem toTensor_naturality_right (A : CochainComplex (StructureSheafModules Rc) ℤ)
    {B B' : CochainComplex (StructureSheafModules Rc) ℤ} (g : B ⟶ B') :
    ((derivedTensor Rc).obj (DerivedCategory.Q.obj A)).map (DerivedCategory.Q.map g) ≫
        (canonicalDerivedTensorProduct (ringedSite Rc)).toTensor A B' =
      (canonicalDerivedTensorProduct (ringedSite Rc)).toTensor A B ≫
        DerivedCategory.Q.map (((Tensor.tensorComplex (ringedSite Rc).O).obj A).map g) := by
  have h := (canonicalDerivedTensorProduct (ringedSite Rc)).toTensor_naturality (𝟙 A) g
  have hid : ((canonicalDerivedTensorProduct (ringedSite Rc)).tensor.map
        (DerivedCategory.Q.map (𝟙 A))).app (DerivedCategory.Q.obj B) =
      𝟙 (((canonicalDerivedTensorProduct (ringedSite Rc)).tensor.obj
        (DerivedCategory.Q.obj A)).obj (DerivedCategory.Q.obj B)) :=
    (congrArg (fun φ => ((canonicalDerivedTensorProduct (ringedSite Rc)).tensor.map φ).app
          (DerivedCategory.Q.obj B)) (CategoryTheory.Functor.map_id DerivedCategory.Q A)).trans
      (congrArg (fun ψ => NatTrans.app ψ (DerivedCategory.Q.obj B))
        (CategoryTheory.Functor.map_id (canonicalDerivedTensorProduct (ringedSite Rc)).tensor
          (DerivedCategory.Q.obj A)))
  exact (Category.id_comp (((canonicalDerivedTensorProduct (ringedSite Rc)).tensor.obj
          (DerivedCategory.Q.obj A)).map (DerivedCategory.Q.map g) ≫
        (canonicalDerivedTensorProduct (ringedSite Rc)).toTensor A B')).symm.trans
    ((congrArg (· ≫ ((canonicalDerivedTensorProduct (ringedSite Rc)).tensor.obj
            (DerivedCategory.Q.obj A)).map (DerivedCategory.Q.map g) ≫
          (canonicalDerivedTensorProduct (ringedSite Rc)).toTensor A B') hid).symm.trans h)

section Chain

attribute [local instance] Stacks.SheafOfModules.monoidalSpace'
attribute [local instance 10000] CochainComplex.symmetricCategory
attribute [local instance 100000] monoidalCategoryStructComplexesAC

/-- **The associator of total tensor complexes**, at the `Tot` spelling of its source and
target. -/
def associatorTot (A B D : CochainComplex (StructureSheafModules Rc) ℤ) :
    ((Tensor.tensorComplex (ringedSite Rc).O).obj
        (((Tensor.tensorComplex (ringedSite Rc).O).obj A).obj B)).obj D ⟶
      ((Tensor.tensorComplex (ringedSite Rc).O).obj A).obj
        (((Tensor.tensorComplex (ringedSite Rc).O).obj B).obj D) :=
  (α_ A B D).hom

/-- The associator of total tensor complexes reassociates an iterated local pure tensor. -/
theorem associatorTot_tensorComplexSection (A B D : CochainComplex (StructureSheafModules Rc) ℤ)
    (W : Opens X) (a b d j : ℤ) (h : a + b + d = j) (h' : a + (b + d) = j)
    (x : (A.X a).val.obj (op W)) (y : (B.X b).val.obj (op W)) (z : (D.X d).val.obj (op W)) :
    ((associatorTot Rc A B D).f j).val.app (op W)
        (RingedSite.tensorComplexSection (ringedSite Rc) (a + b) d j h
          (RingedSite.tensorComplexSection (ringedSite Rc) a b (a + b) rfl x y) z) =
      RingedSite.tensorComplexSection (ringedSite Rc) a (b + d) j h' x
        (RingedSite.tensorComplexSection (ringedSite Rc) b d (b + d) rfl y z) :=
  RingedSite.associator_tensorComplexSection (ringedSite Rc) A B D W a b d j h h' x y z

/-- **The double contraction, transposed twice, is evaluation twice**: the morphism
`Tot(Tot(SheafHom(J, I) ⊗ SheafHom(P, J)) ⊗ P) ⟶ I` obtained from the double contraction by the
currying bijection of Stacks 0A90 twice is the associator of total tensor complexes followed by
`1 ⊗ ev_{P,J}` and `ev_{J,I}`. -/
theorem curryHomEquiv_curryHomEquiv_doubleContraction_space
    (P J I : CochainComplex (StructureSheafModules Rc) ℤ) :
    RingedSite.curryHomEquiv (ringedSite Rc) _ P I
        (RingedSite.curryHomEquiv (ringedSite Rc) _ _ _
          (RingedSite.doubleContraction (ringedSite Rc) P J I)) =
      associatorTot Rc (RingedSite.sheafHomComplex (ringedSite Rc) J I).obj
          (RingedSite.sheafHomComplex (ringedSite Rc) P J).obj P ≫
        ((Tensor.tensorComplex (ringedSite Rc).O).obj
          (RingedSite.sheafHomComplex (ringedSite Rc) J I).obj).map
            (RingedSite.cochainEvaluation (ringedSite Rc) P J) ≫
        RingedSite.cochainEvaluation (ringedSite Rc) J I := by
  have h1 := RingedSite.curryHomEquiv_curryHomEquiv_of_reassociate (ringedSite Rc) _ _ _ _
    (RingedSite.doubleContraction (ringedSite Rc) P J I) _
    (associatorTot_tensorComplexSection Rc _ _ _)
  have h2 : RingedSite.doubleContraction (ringedSite Rc) P J I ≫
      (RingedSite.sheafHomTensorCurryIso (ringedSite Rc)
        (RingedSite.sheafHomComplex (ringedSite Rc) P J).obj P I).hom =
      RingedSite.homMap (ringedSite Rc) (RingedSite.cochainEvaluation (ringedSite Rc) P J)
        (𝟙 I) :=
    (Category.assoc
        (RingedSite.homMap (ringedSite Rc) (RingedSite.cochainEvaluation (ringedSite Rc) P J)
          (𝟙 I))
        (RingedSite.sheafHomTensorCurryIso (ringedSite Rc)
          (RingedSite.sheafHomComplex (ringedSite Rc) P J).obj P I).inv
        (RingedSite.sheafHomTensorCurryIso (ringedSite Rc)
          (RingedSite.sheafHomComplex (ringedSite Rc) P J).obj P I).hom).trans
      ((congrArg
            (RingedSite.homMap (ringedSite Rc) (RingedSite.cochainEvaluation (ringedSite Rc) P J)
              (𝟙 I) ≫ ·)
            (RingedSite.sheafHomTensorCurryIso (ringedSite Rc)
              (RingedSite.sheafHomComplex (ringedSite Rc) P J).obj P I).inv_hom_id).trans
        (Category.comp_id _))
  have h3 := RingedSite.curryHomEquiv_homMap_source (ringedSite Rc) J
    (((Tensor.tensorComplex (ringedSite Rc).O).obj
      (RingedSite.sheafHomComplex (ringedSite Rc) P J).obj).obj P)
    I (RingedSite.cochainEvaluation (ringedSite Rc) P J)
  rw [h1, h2]
  exact congrArg (associatorTot Rc (RingedSite.sheafHomComplex (ringedSite Rc) J I).obj
    (RingedSite.sheafHomComplex (ringedSite Rc) P J).obj P ≫ ·) h3

end Chain

section Model

attribute [local instance] Stacks.SheafOfModules.monoidalSpace'
attribute [local instance 10000] CochainComplex.symmetricCategory
attribute [local instance 100000] monoidalCategoryStructComplexesAC

/-- `Stacks.SheafOfModules.derivedAssociator_toTensor` at the `Tot` spelling. -/
theorem derivedAssociator_toTensor_tot (A B D : CochainComplex (StructureSheafModules Rc) ℤ) :
    ((derivedTensor Rc).map ((canonicalDerivedTensorProduct (ringedSite Rc)).toTensor A B)).app
        (DerivedCategory.Q.obj D) ≫
      (canonicalDerivedTensorProduct (ringedSite Rc)).toTensor _ D ≫
        DerivedCategory.Q.map (associatorTot Rc A B D) =
    derivedAssociatorHom Rc _ _ _ ≫
      ((derivedTensor Rc).obj (DerivedCategory.Q.obj A)).map
        ((canonicalDerivedTensorProduct (ringedSite Rc)).toTensor B D) ≫
      (canonicalDerivedTensorProduct (ringedSite Rc)).toTensor A _ :=
  derivedAssociator_toTensor Rc A B D

/-- The double contraction transposed twice, read in `D(O_X)`. -/
theorem Q_map_curryHomEquiv_curryHomEquiv_doubleContraction
    (P J I : CochainComplex (StructureSheafModules Rc) ℤ) :
    DerivedCategory.Q.map (RingedSite.curryHomEquiv (ringedSite Rc) _ P I
        (RingedSite.curryHomEquiv (ringedSite Rc) _ _ _
          (RingedSite.doubleContraction (ringedSite Rc) P J I))) =
      DerivedCategory.Q.map (associatorTot Rc (RingedSite.sheafHomComplex (ringedSite Rc) J I).obj
          (RingedSite.sheafHomComplex (ringedSite Rc) P J).obj P) ≫
        DerivedCategory.Q.map (((Tensor.tensorComplex (ringedSite Rc).O).obj
          (RingedSite.sheafHomComplex (ringedSite Rc) J I).obj).map
            (RingedSite.cochainEvaluation (ringedSite Rc) P J)) ≫
        DerivedCategory.Q.map (RingedSite.cochainEvaluation (ringedSite Rc) J I) := by
  rw [curryHomEquiv_curryHomEquiv_doubleContraction_space]
  exact (DerivedCategory.Q.map_comp _ _).trans
    (congrArg (DerivedCategory.Q.map (associatorTot Rc
          (RingedSite.sheafHomComplex (ringedSite Rc) J I).obj
          (RingedSite.sheafHomComplex (ringedSite Rc) P J).obj P) ≫ ·)
      (DerivedCategory.Q.map_comp _ _))

/-- The associativity constraint of `D(O_X)` is natural in its first two variables. -/
theorem derivedAssociatorHom_naturality_left_middle
    {A A' B B' : DerivedCategory (StructureSheafModules Rc)}
    (D : DerivedCategory (StructureSheafModules Rc)) (a : A' ⟶ A) (b : B' ⟶ B) :
    ((derivedTensor Rc).map (((derivedTensor Rc).map a).app B' ≫
        ((derivedTensor Rc).obj A).map b)).app D ≫ derivedAssociatorHom Rc A B D =
      derivedAssociatorHom Rc A' B' D ≫ ((derivedTensor Rc).map a).app _ ≫
        ((derivedTensor Rc).obj A).map (((derivedTensor Rc).map b).app D) := by
  have h := derivedAssociatorHom_naturality Rc a b (𝟙 D)
  simp only [derivedWhiskerLeft, derivedWhiskerRight, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id] at h
  exact h

/-- **Applying a composite is applying the two factors in turn**, on the classes of complexes
`P`, `J`, `I` with `J` and `I` K-injective: for the composition morphism `cmp` of Stacks 0A8V
and the application morphisms `ε` of Stacks 08J8,

`(cmp ⊗ 1) ≫ ε_{P,I} = α ≫ (1 ⊗ ε_{P,J}) ≫ ε_{J,I}`. -/
theorem derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_model
    (P J I : CochainComplex (StructureSheafModules Rc) ℤ) [J.IsKInjective] [I.IsKInjective] :
    ((derivedTensor Rc).map (derivedSheafHomComposition Rc (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj J) (DerivedCategory.Q.obj I))).app (DerivedCategory.Q.obj P) ≫
      derivedSheafHomCounit Rc (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I) =
    derivedAssociatorHom Rc _ _ _ ≫
      ((derivedTensor Rc).obj _).map
        (derivedSheafHomCounit Rc (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj J)) ≫
      derivedSheafHomCounit Rc (DerivedCategory.Q.obj J) (DerivedCategory.Q.obj I) := by
  haveI : (show CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf (ringedSite Rc).O)) ℤ
      from J).IsKInjective := ‹J.IsKInjective›
  haveI : (show CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf (ringedSite Rc).O)) ℤ
      from I).IsKInjective := ‹I.IsKInjective›
  have hJI : IsIso (homComparisonSpace Rc J I) :=
    RingedSite.isIso_strictlyPerfectHomComparison_of_isKInjective _ _ _ _
  have hPJ : IsIso (homComparisonSpace Rc P J) :=
    RingedSite.isIso_strictlyPerfectHomComparison_of_isKInjective _ _ _ _
  exact comp_app_descent (derivedTensor Rc) (homComparisonSpace Rc J I)
    (homComparisonSpace Rc P J) (homComparisonSpace Rc P I) hJI hPJ
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (homComparison_derivedSheafHomComposition Rc P J I)
    (derivedSheafHomCounit_homComparison_curry Rc _ P I _)
    (derivedSheafHomCounit_homComparison Rc P J)
    (derivedSheafHomCounit_homComparison Rc J I)
    (toTensor_naturality_right Rc _ _)
    (derivedAssociator_toTensor_tot Rc _ _ P)
    (Q_map_curryHomEquiv_curryHomEquiv_doubleContraction Rc P J I)
    (derivedAssociatorHom_naturality_left_middle Rc _ _ _)

end Model

end Stacks.SheafOfModules

end
