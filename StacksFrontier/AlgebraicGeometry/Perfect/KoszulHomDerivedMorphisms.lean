module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import StacksFrontier.Algebra.Homology.Koszul.AlternatingCechTotal
public import StacksFrontier.AlgebraicGeometry.Perfect.Koszul
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCechIdentification
public import StacksFrontier.Homology.HomologyColimit
public import StacksFrontier.Homology.HomComplex.RHom

/-!
# Morphisms in the derived category out of the Koszul system

Let `A` be a commutative ring and `f` a finite family of elements of `A`. Every stage of the
Koszul system is a bounded above complex of projective `A`-modules, so the degree-zero homology
of its Hom complex into a complex `M` is the group of morphisms into `M` in the derived category.
Passing to the filtered colimit over the exponent identifies the colimit of these morphism groups
with the degree-zero homology of the total alternating Čech complex of `M`.

## Main definitions

* `Stacks.Koszul.Cech.koszulCochain` and `Stacks.Koszul.Cech.koszulCochainDiagram`: the stages of
  the Koszul system and the system itself, read as cochain complexes.
* `Stacks.Koszul.Cech.koszulDerivedHomDiagramFunctor`: the diagram of morphism groups in the
  derived category out of the Koszul system.

## Main results

* `Stacks.Koszul.Cech.koszulDerivedHomColimitIsoCech`: the colimit of the derived morphism groups
  out of the Koszul system is the degree-zero homology of the total alternating Čech complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex CochainComplex.HomComplex

namespace Stacks.Koszul.Cech

attribute [local instance] HasDerivedCategory.standard

universe u

variable {A : Type u} [CommRing A]

/-- The stage with exponent `e + 1` of the Koszul system, read as a cochain complex concentrated
in nonpositive degrees. -/
abbrev koszulCochain {r : ℕ} (f : Fin r → A) (e : ℕ) : CochainComplex (ModuleCat.{u} A) ℤ :=
  (Koszul.koszulIdealComplexPower f e).extend ComplexShape.embeddingDownNat

/-- The stages of the Koszul system are concentrated in nonpositive degrees. -/
theorem koszulCochain_isStrictlyLE {r : ℕ} (f : Fin r → A) (e : ℕ) :
    (koszulCochain f e).IsStrictlyLE 0 := by
  dsimp [koszulCochain]
  infer_instance

attribute [local instance] koszulCochain_isStrictlyLE

/-- Each term of a stage of the Koszul system is an exterior power of a finite free module, hence
projective. -/
theorem koszulCochain_projective {r : ℕ} (f : Fin r → A) (e : ℕ) (i : ℤ) :
    Projective ((koszulCochain f e).X i) := by
  have (n : ℕ) : Projective ((Koszul.koszulIdealComplexPower f e).X n) := by
    change Projective (ModuleCat.of A (⋀[A]^(n + 1) (Fin r → A)))
    let b := (Pi.basisFun A (Fin r)).exteriorPower (n + 1)
    let := Module.Free.of_basis b
    infer_instance
  dsimp [koszulCochain]
  infer_instance

attribute [local instance] koszulCochain_projective

/-- For `P` a bounded above complex of projectives, the degree-zero homology of `Hom^•(P, L)` is
the group of morphisms from `P` to `L` in the derived category. -/
def homologyHomComplexZeroEquiv
    (P L : CochainComplex (ModuleCat.{u} A) ℤ)
    [P.IsStrictlyLE 0] [∀ i, Projective (P.X i)] :
    (P.HomComplex L).homology 0 ≃+ (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L) :=
  (homComplexHomologyRHomAddEquiv P L 0 0).trans
    (Linear.homCongr ℤ ((DerivedCategory.quotientCompQhIso _).app P)
      (((DerivedCategory.quotientCompQhIso _).app (L⟦(0 : ℤ)⟧)) ≪≫
        DerivedCategory.Q.mapIso ((shiftFunctorZero _ ℤ).app L))).toAddEquiv

/-- Precomposition by `f` and postcomposition by `g` on the Hom complex, as left homology map
data on cocycles and cohomology classes. -/
def homClassesMapData
    {P P' L L' : CochainComplex (ModuleCat.{u} A) ℤ}
    (f : P' ⟶ P) (g : L ⟶ L') (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℤ) n).map
        (((forget₂ (ModuleCat A) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
          (Stacks.HomComplex.TensorHomMap.precomp A P' P L f ≫
            Stacks.HomComplex.TensorHomMap.postcomp A P' L L' g)))
      (leftHomologyData P L n) (leftHomologyData P' L' n) :=
  { StacksDraft.DerivedHom.Construction.homLeftHomologyMapData
      (Stacks.HomComplex.TensorHomMap.precomp A P' P L f ≫
        Stacks.HomComplex.TensorHomMap.postcomp A P' L L' g) n with
    φK := AddCommGrpCat.ofHom
      ((cocyclePostcompAddMonoidHom P' g n).comp (cocyclePrecompAddMonoidHom f L n))
    φH := AddCommGrpCat.ofHom
      ((cohomologyClassPostcomp P' g n).comp (cohomologyClassPrecomp f L n)) }

/-- The identification of the homology of the Hom complex with cohomology classes is natural with
respect to precomposition and postcomposition. -/
lemma homologyAddEquiv_naturality
    {P P' L L' : CochainComplex (ModuleCat.{u} A) ℤ}
    (f : P' ⟶ P) (g : L ⟶ L') (n : ℤ) (x : (P.HomComplex L).homology n) :
    homologyAddEquiv P' L' n
      ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) n).map
        (((forget₂ (ModuleCat A) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
        (Stacks.HomComplex.TensorHomMap.precomp A P' P L f ≫
          Stacks.HomComplex.TensorHomMap.postcomp A P' L L' g)) x) =
      cohomologyClassPostcomp P' g n (cohomologyClassPrecomp f L n
        (homologyAddEquiv P L n x)) :=
  ConcreteCategory.congr_hom (homClassesMapData f g n).homologyMap_comm x

/-- The comparison between morphisms out of the homotopy category and morphisms in the derived
category is natural in both variables. -/
lemma homCongrQuotientCompQhIso_naturality
    {P P' L L' : CochainComplex (ModuleCat.{u} A) ℤ} (f : P' ⟶ P) (g : L ⟶ L')
    (a : DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).obj P) ⟶
        DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).obj (L⟦(0 : ℤ)⟧))) :
    Linear.homCongr ℤ ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app P')
        (((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app (L'⟦(0 : ℤ)⟧)) ≪≫
          DerivedCategory.Q.mapIso
            ((shiftFunctorZero (CochainComplex (ModuleCat.{u} A) ℤ) ℤ).app L'))
        (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).map f) ≫ a ≫
          DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).map (g⟦(0 : ℤ)⟧'))) =
      DerivedCategory.Q.map f ≫
        Linear.homCongr ℤ ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app P)
          (((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app (L⟦(0 : ℤ)⟧)) ≪≫
            DerivedCategory.Q.mapIso
              ((shiftFunctorZero (CochainComplex (ModuleCat.{u} A) ℤ) ℤ).app L)) a ≫
          DerivedCategory.Q.map g := by
  have hQh {X Y : CochainComplex (ModuleCat.{u} A) ℤ} (u : X ⟶ Y) :
      DerivedCategory.Qh.map ((HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).map u) =
        (HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ) ⋙ DerivedCategory.Qh).map u := rfl
  simp only [Linear.homCongr_apply, Iso.trans_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Category.assoc, hQh]
  rw [← (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).inv.naturality_assoc f,
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.naturality_assoc (g⟦(0 : ℤ)⟧'),
    ← DerivedCategory.Q.map_comp, (shiftFunctorZero _ ℤ).hom.naturality g]
  simp only [Functor.map_comp, Functor.id_map]

/-- Transport of the naturality statement for `homologyHomComplexZeroEquiv` along the
identification of the homology of the Hom complex with cohomology classes. -/
lemma homologyHomComplexZeroEquiv_naturality_aux
    {P P' L L' : CochainComplex (ModuleCat.{u} A) ℤ}
    [P.IsStrictlyLE 0] [∀ i, Projective (P.X i)]
    [P'.IsStrictlyLE 0] [∀ i, Projective (P'.X i)]
    (f : P' ⟶ P) (g : L ⟶ L')
    (x : (P.HomComplex L).homology 0) (y : (P'.HomComplex L').homology 0)
    (hy : homologyAddEquiv P' L' 0 y =
      cohomologyClassPostcomp P' g 0 (cohomologyClassPrecomp f L 0 (homologyAddEquiv P L 0 x))) :
    homologyHomComplexZeroEquiv P' L' y =
      DerivedCategory.Q.map f ≫ homologyHomComplexZeroEquiv P L x ≫
        DerivedCategory.Q.map g := by
  simp only [homologyHomComplexZeroEquiv, homComplexHomologyRHomAddEquiv,
    AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv]
  rw [hy, cohomologyClassRHomAddEquiv_naturality_right P' L L' g 0 0,
    cohomologyClassRHomAddEquiv_naturality_left P P' L f 0 0 0]
  rw [Category.assoc]
  exact homCongrQuotientCompQhIso_naturality f g _

/-- The identification of the degree-zero homology of the Hom complex with morphisms in the
derived category is natural in both variables. -/
lemma homologyHomComplexZeroEquiv_naturality
    {P P' L L' : CochainComplex (ModuleCat.{u} A) ℤ}
    [P.IsStrictlyLE 0] [∀ i, Projective (P.X i)]
    [P'.IsStrictlyLE 0] [∀ i, Projective (P'.X i)]
    (f : P' ⟶ P) (g : L ⟶ L') (x : (P.HomComplex L).homology 0) :
    homologyHomComplexZeroEquiv P' L'
      ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).map
        (((forget₂ (ModuleCat A) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
          (Stacks.HomComplex.TensorHomMap.precomp A P' P L f ≫
            Stacks.HomComplex.TensorHomMap.postcomp A P' L L' g)) x) =
      DerivedCategory.Q.map f ≫ homologyHomComplexZeroEquiv P L x ≫
        DerivedCategory.Q.map g :=
  homologyHomComplexZeroEquiv_naturality_aux f g x _ (homologyAddEquiv_naturality f g 0 x)

/-- The Koszul system, read as a diagram of cochain complexes. -/
abbrev koszulCochainDiagram {r : ℕ} (f : Fin r → A) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  (Koszul.koszulIdealComplexSystem f).diagram ⋙
    ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)

/-- Degreewise, the degree-zero homology of the Koszul Hom diagram is the diagram of morphisms in
the derived category out of the Koszul system. -/
def koszulHomologyDiagramIso {r : ℕ} (f : Fin r → A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    (Koszul.koszulHomDiagramFunctor f).obj K ⋙
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) 0 ⋙
      AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
    (koszulCochainDiagram f ⋙ DerivedCategory.Q).rightOp ⋙
      preadditiveYoneda.obj (DerivedCategory.Q.obj K) :=
  NatIso.ofComponents (fun e ↦
    (AddEquiv.ulift.trans (homologyHomComplexZeroEquiv (koszulCochain f e) K)).toAddCommGrpIso)
    (by
      intro i j h
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      change ULift.{u + 1} (((koszulCochain f i).HomComplex K).homology 0) at x
      let g : koszulCochain f j ⟶ koszulCochain f i := (koszulCochainDiagram f).map h.op
      change homologyHomComplexZeroEquiv (koszulCochain f j) K
        ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).map
          (((forget₂ (ModuleCat A) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
            (Stacks.HomComplex.TensorHomMap.precomp A _ _ K g ≫
              Stacks.HomComplex.TensorHomMap.postcomp A _ K K (𝟙 K))) x.down) =
        DerivedCategory.Q.map g ≫ homologyHomComplexZeroEquiv (koszulCochain f i) K x.down
      simpa only [DerivedCategory.Q.map_id K, Category.comp_id] using
        homologyHomComplexZeroEquiv_naturality g (𝟙 K) x.down)

/-- The diagram of morphism groups in the derived category out of the Koszul system, functorial in
the target. -/
abbrev koszulDerivedHomDiagramFunctor {r : ℕ} (f : Fin r → A) :
    DerivedCategory (ModuleCat.{u} A) ⥤ (ℕ ⥤ AddCommGrpCat.{u + 1}) :=
  preadditiveYoneda ⋙
    (Functor.whiskeringLeft ℕ (DerivedCategory (ModuleCat.{u} A))ᵒᵖ AddCommGrpCat.{u + 1}).obj
      (koszulCochainDiagram f ⋙ DerivedCategory.Q).rightOp

/-- Degree-zero homology of a complex of `A`-modules, with values in the larger universe. -/
abbrev liftedHomologyFunctor : CochainComplex (ModuleCat.{u} A) ℤ ⥤ AddCommGrpCat.{u + 1} :=
  (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) 0 ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- The degreewise identification of the Koszul Hom diagram with the diagram of derived morphism
groups is natural in the coefficient complex. -/
def koszulHomologyDiagramNatIso {r : ℕ} (f : Fin r → A) :
    Koszul.koszulHomDiagramFunctor f ⋙
      (Functor.whiskeringRight ℕ _ _).obj (liftedHomologyFunctor (A := A)) ≅
    DerivedCategory.Q ⋙ koszulDerivedHomDiagramFunctor f :=
  NatIso.ofComponents (koszulHomologyDiagramIso f) (by
    intro K L g
    apply NatTrans.ext
    funext e
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    change ULift.{u + 1} (((koszulCochain f e).HomComplex K).homology 0) at x
    change homologyHomComplexZeroEquiv (koszulCochain f e) L
        ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).map
          (((forget₂ (ModuleCat A) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
            (Stacks.HomComplex.TensorHomMap.precomp A _ _ K (𝟙 (koszulCochain f e)) ≫
              Stacks.HomComplex.TensorHomMap.postcomp A _ K L g)) x.down) =
      homologyHomComplexZeroEquiv (koszulCochain f e) K x.down ≫ DerivedCategory.Q.map g
    simpa only [DerivedCategory.Q.map_id (koszulCochain f e), Category.id_comp] using
      homologyHomComplexZeroEquiv_naturality (𝟙 (koszulCochain f e)) g x.down)

/-- The colimit of the morphism groups in the derived category out of the Koszul system is the
degree-zero homology of the total alternating Čech complex. -/
def koszulDerivedHomColimitIsoCech {r : ℕ} (f : Fin r → A) :
    DerivedCategory.Q ⋙ koszulDerivedHomDiagramFunctor f ⋙ colim ≅
      Koszul.alternatingCechTotalFunctor f ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) 0 ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u} := by
  letI : AB5OfSize.{0, 0} AddCommGrpCat.{u} := AB5OfSize_shrink _
  letI := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor
    (A := AddCommGrpCat.{u}) (J := ℕ) (.up ℤ) (0 : ℤ)
  let h := preservesColimitNatIso (J := ℕ) (liftedHomologyFunctor (A := A))
  exact (Functor.isoWhiskerRight (koszulHomologyDiagramNatIso f) colim).symm ≪≫
    (Functor.isoWhiskerLeft (Koszul.koszulHomDiagramFunctor f) h).symm ≪≫
    Functor.isoWhiskerRight (Koszul.koszulHomColimitIsoAlternatingCechTotal f)
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) 0 ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u})

end Stacks.Koszul.Cech

end
