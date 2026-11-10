module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.Algebra.Homology.DerivedCategory.FunctorialInjectiveResolution
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo
public import StacksFrontier.Algebra.Homology.SpectralSequence.DerivedTensor
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Functoriality
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeExactness
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.TwoFibreProductEqualizers
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafFunctoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Injectives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
public import StacksFrontier.CategoryTheory.Subobject.CokernelComparisons
public import StacksFrontier.Homology.DerivedIndexing.Extend
public import StacksFrontier.Algebra.Homology.Embedding.UpNatZero
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequenceModules.CechSections
import all StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequenceModules.ModuleRestriction
import all StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequenceModules.CechSections

/-!
# Acyclicity of the rows of the relative Čech double complex

The relative Čech complex of a sheaf of modules, built from right Kan extensions along the terms
of the relative Čech nerve, is identified with the complex of sections; for an injective sheaf of
modules it is an injective resolution, so the augmentation of its complex of sections is a
quasi-isomorphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ZeroObject

namespace Stacks.RelativeCech

universe u vᵤ vₓ wᵤ wₓ a v₁ w₁ v₂ w₂ r

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒰 : Type vᵤ} [Category.{wᵤ} 𝒰] {𝒳 : Type vₓ} [Category.{wₓ} 𝒳]
  (p : 𝒰 ⥤ AlgebraicGeometry.BigFppfOver B S hS) (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (f : 𝒰 ⥤ 𝒳) (τ : AlgebraicGeometry.SiteKind)

attribute [local instance] siteHasSheafifyAt siteWEqualsLocallyBijectiveAt

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

section CechRows

attribute [local implicit_reducible] SheafOfModules.toSheaf
  AlgebraicTopology.alternatingCofaceMapComplex
  AlgebraicTopology.AlternatingCofaceMapComplex.obj

open Opposite AlgebraicTopology

variable (hq : q.IsFiberedInGroupoids)
  (h : ∀ n, (tupleStructureFunctor B S hS q f n).IsFiberedInGroupoids)

include hq h in
/-- The projection of the degree-`n` term of the relative Čech nerve to `𝒳` is continuous for the
associated topologies. -/
lemma cechProjection_continuous (n : ℕ) :
    (Tuple.projection q f n).IsContinuous
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
          (tupleStructureFunctor B S hS q f n) τ)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ) := by
  let := (h n).isFibered
  let := hq.isFibered
  exact ((hq.isFibredOneMorphism (show Tuple.projection q f n ⋙ q =
    tupleStructureFunctor B S hS q f n from rfl)).isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology τ).over (B.obj hS))).1

include hq h in
/-- The projection of the degree-`n` term of the relative Čech nerve to `𝒳` is cocontinuous for
the associated topologies. -/
private lemma cechProjection_cocontinuous (n : ℕ) :
    (Tuple.projection q f n).IsCocontinuous
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
          (tupleStructureFunctor B S hS q f n) τ)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ) := by
  let := (h n).isFibered
  let := hq.isFibered
  exact ((hq.isFibredOneMorphism (show Tuple.projection q f n ⋙ q =
    tupleStructureFunctor B S hS q f n from rfl)).isContinuous_and_isCocontinuous_inheritedTopology
    ((B.baseTopology τ).over (B.obj hS))).2

variable (M : SheafOfModules.{max u vᵤ vₓ wᵤ wₓ a}
  (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)))

/-- The underlying presheaf of modules of the degree-`n` term of the relative Čech complex of `M`:
the right Kan extension of the restriction of `M`. -/
private abbrev cechModulePresheaf (n : ℕ) :=
  ranPresheaf.{max wᵤ wₓ, wₓ, max vᵤ vₓ wₓ, vₓ, u, max u vᵤ vₓ wᵤ wₓ a} (Tuple.projection q f n)
    (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)).obj
    ((PresheafOfModules.pushforward₀ (Tuple.projection q f n)
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)).obj).obj M.val)

/-- The degree-`n` term of the relative Čech complex of a sheaf of modules `M`: the right Kan
extension along the projection of the restriction of `M` to the degree-`n` term of the nerve. -/
@[implicit_reducible] private def cechModuleSheaf (n : ℕ) :
    SheafOfModules.{max u vᵤ vₓ wᵤ wₓ a}
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)) where
  val := cechModulePresheaf.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq M n
  isSheaf := by
    let := cechProjection_continuous B S hS q f τ hq h n
    let := cechProjection_cocontinuous B S hS q f τ hq h n
    exact (ranSheaf.{max wᵤ wₓ, wₓ, max vᵤ vₓ wₓ, vₓ, u, max u vᵤ vₓ wᵤ wₓ a}
      (Tuple.projection q f n)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
          (tupleStructureFunctor B S hS q f n) τ)
      (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ))
      { val := (PresheafOfModules.pushforward₀ (Tuple.projection q f n)
          (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)).obj).obj M.val
        isSheaf := ((Tuple.projection q f n).sheafPushforwardContinuous
          AddCommGrpCat.{max u vᵤ vₓ wᵤ wₓ a}
          (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
              (tupleStructureFunctor B S hS q f n) τ)
          (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ) |>.obj
            ((SheafOfModules.toSheaf _).obj M)).property }).isSheaf

/-- Reindexing tuples along `φ`, as a functor between the comma categories computing the two right
Kan extensions. -/
private def cechCommaReindex {m n : ℕ} (φ : Fin (m + 1) → Fin (n + 1))
    (x : 𝒳ᵒᵖ) :
    StructuredArrow x (Tuple.projection q f n).op ⥤
      StructuredArrow x (Tuple.projection q f m).op where
  obj j := StructuredArrow.mk (Y := (Tuple.reindex q f φ).op.obj j.right) j.hom
  map g := StructuredArrow.homMk ((Tuple.reindex q f φ).op.map g.right)
    (StructuredArrow.w g)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The map from the degree-`m` to the degree-`n` term of the relative Čech complex of `M` induced
by a map of index sets. -/
private def cechModuleSheafMap {m n : ℕ} (φ : Fin (m + 1) → Fin (n + 1)) :
    cechModuleSheaf.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M m ⟶
      cechModuleSheaf.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M n where
  val :=
    { app x := ModuleCat.ofHom
        { toFun := fun s => ⟨fun j => s.val ((cechCommaReindex B S hS q f φ x).obj j),
            fun {_ _} g => s.property ((cechCommaReindex B S hS q f φ x).map g)⟩
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      naturality := by intros; rfl }

/-- The relative Čech nerve of a sheaf of modules, as a cosimplicial object. -/
@[implicit_reducible] private def cechModuleCosimplicial :
    CosimplicialObject (SheafOfModules.{max u vᵤ vₓ wᵤ wₓ a}
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ))) where
  obj n := cechModuleSheaf.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M n.len
  map φ := cechModuleSheafMap.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M φ.toOrderHom
  map_id n := by ext x s; rfl
  map_comp φ ψ := by ext x s; rfl

/-- The relative Čech complex of a sheaf of modules: the alternating coface complex of
`cechModuleCosimplicial`. -/
private abbrev cechModuleComplex :=
  (alternatingCofaceMapComplex _).obj
      (cechModuleCosimplicial.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M)

/-- The augmentation of `M` into degree zero of its relative Čech complex: the unit of the
restriction adjunction. -/
private def cechModuleAugmentation :
    M ⟶ cechModuleSheaf.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M 0 :=
  ⟨(ranUnit.{max wᵤ wₓ, wₓ, max vᵤ vₓ wₓ, vₓ, u, max u vᵤ vₓ wᵤ wₓ a}
    (Tuple.projection q f 0)
    (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)).obj).app M.val⟩

/-- The augmentation of `M` lands in the kernel of the first differential of its relative Čech
complex. -/
private lemma cechModuleAugmentation_d :
    cechModuleAugmentation.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M ≫
      (cechModuleComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M).d 0 1 = 0 := by
  change cechModuleAugmentation.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M ≫
    AlternatingCofaceMapComplex.objD
      (cechModuleCosimplicial.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M) 0 = 0
  simp only [AlternatingCofaceMapComplex.objD, Nat.reduceAdd, Fin.sum_univ_two,
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul,
    ← sub_eq_add_neg]
  rw [Preadditive.comp_sub, sub_eq_zero]
  ext x s
  rfl

/-- The augmentation of `M` into its relative Čech complex, as a map of cochain complexes. -/
private def cechModuleAugmentationComplex :
    (CochainComplex.single₀ _).obj M ⟶
      cechModuleComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M :=
  HomologicalComplex.mkHomFromSingle
      (cechModuleAugmentation.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M)
    (fun j hj => by
      have : j = 1 := hj.symm
      subst j
      exact cechModuleAugmentation_d.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M)

/-- The underlying abelian presheaf of the degree-`n` term of the relative Čech complex of `M` is
the degree-`n` term of the abelian relative Čech construction. -/
private def cechModulePresheafIso (n : ℕ) :
    (cechModulePresheaf.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq M n).presheaf ≅
      term.{wᵤ, wₓ, _, vᵤ, vₓ, _, max u vᵤ vₓ wᵤ wₓ a} q f M.val.presheaf n := by
  have h2 : ((Tuple.projection q f n).op.ran.obj
      ((Tuple.projection q f n).op ⋙ M.val.presheaf)).IsRightKanExtension
      ((Tuple.projection q f n).op.ranCounit.app
        ((Tuple.projection q f n).op ⋙ M.val.presheaf)) := inferInstance
  dsimp only [term]
  exact @Functor.rightKanExtensionUnique _ _ _ _ _ _
    (cechModulePresheaf.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq M n).presheaf _ _
    (ranCounit.{max wᵤ wₓ, wₓ, max vᵤ vₓ wₓ, vₓ, u, max u vᵤ vₓ wᵤ wₓ a}
      (Tuple.projection q f n) _ _)
    (ranIsRightKanExtension.{max wᵤ wₓ, wₓ, max vᵤ vₓ wₓ, vₓ, u,
      max u vᵤ vₓ wᵤ wₓ a} (Tuple.projection q f n)
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)).obj
      ((PresheafOfModules.pushforward₀ (Tuple.projection q f n)
        (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
          (B.baseTopology_le_topology τ)).obj).obj M.val))
    ((Tuple.projection q f n).op.ran.obj ((Tuple.projection q f n).op ⋙ M.val.presheaf))
    ((Tuple.projection q f n).op.ranCounit.app _) h2

/-- `cechModulePresheafIso` is compatible with the counits of the two right Kan extensions. -/
private lemma cechModulePresheafIso_fac (n : ℕ) :
    Functor.whiskerLeft (Tuple.projection q f n).op
        (cechModulePresheafIso.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq M n).hom ≫
      (Tuple.projection q f n).op.ranCounit.app
        ((Tuple.projection q f n).op ⋙ M.val.presheaf) =
      ranCounit.{max wᵤ wₓ, wₓ, max vᵤ vₓ wₓ, vₓ, u, max u vᵤ vₓ wᵤ wₓ a}
        (Tuple.projection q f n) _ _ := by
  simp only [cechModulePresheafIso, id_eq]
  exact Functor.liftOfIsRightKanExtension_fac
    ((Tuple.projection q f n).op.ran.obj ((Tuple.projection q f n).op ⋙ M.val.presheaf))
    ((Tuple.projection q f n).op.ranCounit.app _)
    (cechModulePresheaf.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq M n).presheaf
    (ranCounit.{max wᵤ wₓ, wₓ, max vᵤ vₓ wₓ, vₓ, u, max u vᵤ vₓ wᵤ wₓ a}
      (Tuple.projection q f n) _ _)

/-- `cechModulePresheafIso` is natural in the simplicial index. -/
private lemma cechModulePresheafIso_naturality {m n : SimplexCategory} (φ : m ⟶ n) :
    ((SheafOfModules.toSheaf _).map
        (cechModuleSheafMap.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M φ.toOrderHom)).hom ≫
      (cechModulePresheafIso.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq M n.len).hom =
      (cechModulePresheafIso.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq M m.len).hom ≫
        reindexMap.{wᵤ, wₓ, _, vᵤ, vₓ, _, max u vᵤ vₓ wᵤ wₓ a} q f M.val.presheaf φ := by
  apply ((Tuple.projection q f n.len).op.ran.obj
    ((Tuple.projection q f n.len).op ⋙ M.val.presheaf)).hom_ext_of_isRightKanExtension
    ((Tuple.projection q f n.len).op.ranCounit.app _)
  simp only [Functor.whiskerLeft_comp, Category.assoc]
  rw [cechModulePresheafIso_fac, reindexMap_fac]
  ext x s
  exact (ConcreteCategory.congr_hom
    (congr_app (cechModulePresheafIso_fac.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq M m.len)
      ((Tuple.reindex q f φ.toOrderHom).op.obj x)) s).symm

/-- On underlying abelian presheaves, the cosimplicial relative Čech nerve of `M` is the abelian
relative Čech nerve. -/
private def cechModuleCosimplicialForgetIso :
    cechModuleCosimplicial.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M ⋙
        SheafOfModules.toSheaf _ ⋙ sheafToPresheaf _ _ ≅
      cosimplicial.{wᵤ, wₓ, _, vᵤ, vₓ, _, max u vᵤ vₓ wᵤ wₓ a} q f M.val.presheaf :=
  NatIso.ofComponents
      (fun n => cechModulePresheafIso.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq M n.len)
    (fun φ => cechModulePresheafIso_naturality.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M φ)

/-- On underlying abelian sheaves, the cosimplicial relative Čech nerve of `M` is the
sheafification of the abelian relative Čech nerve. -/
private def cechModuleCosimplicialSheafIso :
    cechModuleCosimplicial.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M ⋙ SheafOfModules.toSheaf _ ≅
      cosimplicial.{wᵤ, wₓ, _, vᵤ, vₓ, _, max u vᵤ vₓ wᵤ wₓ a} q f M.val.presheaf ⋙
        presheafToSheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
          AddCommGrpCat.{max u vᵤ vₓ wᵤ wₓ a} :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (sheafificationNatIso _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
        (cechModuleCosimplicialForgetIso.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M) _

/-- An additive functor commutes with the alternating coface complex of a cosimplicial object. -/
private def mapAlternatingCofaceIso {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (X : CosimplicialObject C) :
    (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((alternatingCofaceMapComplex C).obj X) ≅
      (alternatingCofaceMapComplex D).obj (X ⋙ G) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n => Iso.refl _) ?_
  intro i j hij
  have : i + 1 = j := hij
  subst j
  simp [alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj,
    AlternatingCofaceMapComplex.objD, CosimplicialObject.δ]

/-- On underlying abelian sheaves, the relative Čech complex of `M` is the sheafification of the
abelian relative Čech complex. -/
private def cechModuleComplexSheafIso :
    ((SheafOfModules.toSheaf _).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cechModuleComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M) ≅
      ((presheafToSheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
        AddCommGrpCat.{max u vᵤ vₓ wᵤ wₓ a}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
              (complex.{wᵤ, wₓ, _, vᵤ, vₓ, _, max u vᵤ vₓ wᵤ wₓ a} q f M.val.presheaf) :=
  mapAlternatingCofaceIso _ _ ≪≫
    (alternatingCofaceMapComplex _).mapIso
      (cechModuleCosimplicialSheafIso.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M) ≪≫
    (mapAlternatingCofaceIso _ _).symm

/-- Global sections of the degree-`n` term of the relative Čech complex of `M` are the degree-`n`
sections of the relative Čech nerve. -/
private def cechModuleSectionsIso (n : ℕ) :
    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{vₓ, wₓ, u, max u vᵤ vₓ wᵤ wₓ a} _).obj
        (cechModuleSheaf.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M n) ≅
      (cechLevelSectionsFunctor.{u, vᵤ, vₓ, wᵤ, wₓ, a}
        B S hS q f τ hq n (h n)).obj M := by
  let X := (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{vₓ, wₓ, u, max u vᵤ vₓ wᵤ wₓ a}
    (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ))).obj
      (cechModuleSheaf.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M n)
  let Y := (cechLevelSectionsFunctor.{u, vᵤ, vₓ, wᵤ, wₓ, a}
    B S hS q f τ hq n (h n)).obj M
  have key : ∀ (s : X) {x : 𝒳ᵒᵖ} {y : (Tuple q f n)ᵒᵖ}
      (g : x ⟶ (Tuple.projection q f n).op.obj y),
      (s.val x).val (StructuredArrow.mk g) =
        (s.val ((Tuple.projection q f n).op.obj y)).val (StructuredArrow.mk (𝟙 _)) :=
    fun s x y g => by
    have hs := congrArg (fun z => z.val (StructuredArrow.mk (𝟙 _))) (s.property g)
    change (s.val x).val (StructuredArrow.mk (g ≫ 𝟙 _)) = _ at hs
    rwa [Category.comp_id] at hs
  let e : X ≃ₗ[Stacks.Cohomology.SiteModules.GlobalSectionRing
    (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ))] Y :=
    { toFun := fun s => ⟨fun x => (s.val ((Tuple.projection q f n).op.obj x)).val
          (StructuredArrow.mk (𝟙 _)), by
        intro x y g
        have ht := (s.val ((Tuple.projection q f n).op.obj x)).property
          (StructuredArrow.homMk g : StructuredArrow.mk (𝟙 _) ⟶
            StructuredArrow.mk ((Tuple.projection q f n).op.map g))
        change M.val.map ((Tuple.projection q f n).op.map g) _ = _
        change M.val.map ((Tuple.projection q f n).op.map g) _ = _ at ht
        rw [ht]
        exact key s _⟩
      invFun := fun t => ⟨fun x => ⟨fun j => t.val j.right,
          fun {_ _} g => t.property g.right⟩, fun g => rfl⟩
      left_inv := by
        intro s
        apply Subtype.ext
        funext x
        apply Subtype.ext
        funext j
        exact (key s j.hom).symm
      right_inv := by intro t; rfl
      map_add' := by intros; rfl
      map_smul' := by
        intro r s
        apply Subtype.ext
        funext x
        change (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)).obj.map (𝟙 _)
          (r.val ((Tuple.projection q f n).op.obj x)) •
            (s.val ((Tuple.projection q f n).op.obj x)).val (StructuredArrow.mk (𝟙 _)) =
          r.val ((Tuple.projection q f n).op.obj x) •
            (s.val ((Tuple.projection q f n).op.obj x)).val (StructuredArrow.mk (𝟙 _))
        rw [CategoryTheory.Functor.map_id]
        rfl }
  exact e.toModuleIso

/-- Global sections carry the cosimplicial relative Čech nerve of `M` to the cosimplicial object of
sections. -/
private def cechModuleSectionsCosimplicialIso :
    cechModuleCosimplicial.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{vₓ, wₓ, u, max u vᵤ vₓ wᵤ wₓ a} _ ≅
      (cechSectionsCosimplicial.{u, vᵤ, vₓ, wᵤ, wₓ, a}
        B S hS q f τ hq h).flip.obj M :=
  NatIso.ofComponents
      (fun n => cechModuleSectionsIso.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M n.len)
    (by intros; ext s; rfl)

/-- Global sections carry the relative Čech complex of `M` to the relative Čech complex of
sections. -/
private def cechModuleSectionsComplexIso :
    ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{vₓ, wₓ, u, max u vᵤ vₓ wᵤ wₓ a}
        _).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cechModuleComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M) ≅
      (cechSectionsComplexFunctor.{u, vᵤ, vₓ, wᵤ, wₓ, a}
        B S hS q f τ hq h).obj M :=
  mapAlternatingCofaceIso _ _ ≪≫
    (alternatingCofaceMapComplex _).mapIso
      (cechModuleSectionsCosimplicialIso.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M)

/-- Global sections carry the augmentation of the relative Čech complex of `M` to the augmentation
of the relative Čech complex of sections. -/
private lemma cechModuleSectionsAugmentation :
    (HomologicalComplex.singleMapHomologicalComplex
      (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{vₓ, wₓ, u, max u vᵤ vₓ wᵤ wₓ a} _)
          (ComplexShape.up ℕ) 0).inv.app M ≫
        ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{vₓ, wₓ, u, max u vᵤ vₓ wᵤ wₓ a}
            _).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (cechModuleAugmentationComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M) ≫
        (cechModuleSectionsComplexIso.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M).hom =
      (cechSectionsAugmentationComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a}
        B S hS q f τ hq h).app M := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    Functor.mapHomologicalComplex_map_f, cechModuleAugmentationComplex,
    cechSectionsAugmentationComplex, HomologicalComplex.mkHomFromSingle_f,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc]
  apply congrArg ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
    ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{vₓ, wₓ, u, max u vᵤ vₓ wᵤ wₓ a}
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ))).obj M)).hom ≫ ·)
  ext s
  apply Subtype.ext
  funext x
  change M.val.presheaf.map (𝟙 _) _ = _
  rw [M.val.presheaf.map_id]
  rfl

/-- The degree-`n` term of the relative Čech complex of an injective sheaf of modules is
injective. -/
private lemma cechModuleSheaf_injective [f.Faithful]
    (heq : ∀ n, HasEqualizers (Tuple q f n)) [Injective M] (n : ℕ) :
    Injective (cechModuleSheaf.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M n) := by
  let := heq n
  let := tuple_projection_faithful q f n
  let := cechProjection_continuous B S hS q f τ hq h n
  let := cechProjection_cocontinuous B S hS q f τ hq h n
  let R := restrictSheaf.{max wᵤ wₓ, wₓ, max vᵤ vₓ wₓ, vₓ, u, max u vᵤ vₓ wᵤ wₓ a}
    (Tuple.projection q f n)
    (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
      (tupleStructureFunctor B S hS q f n) τ)
    (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
    (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
      (B.baseTopology_le_topology τ))
  let : PreservesFiniteLimits R := by
    refine ⟨fun I _ _ => ?_⟩
    have : ReflectsLimitsOfShape I (SheafOfModules.toSheaf
        (((Tuple.projection q f n).sheafPushforwardContinuous RingCat.{u}
          (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
            (tupleStructureFunctor B S hS q f n) τ)
          (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)).obj
          (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
            (B.baseTopology_le_topology τ)))) :=
      reflectsLimitsOfShape_of_reflectsIsomorphisms
    have : PreservesLimitsOfShape I (R ⋙ SheafOfModules.toSheaf _) :=
      preservesLimitsOfShape_of_natIso
        (F := SheafOfModules.toSheaf
            (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
              (B.baseTopology_le_topology τ)) ⋙
          (Tuple.projection q f n).sheafPushforwardContinuous
            AddCommGrpCat.{max u vᵤ vₓ wᵤ wₓ a}
            (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
              (tupleStructureFunctor B S hS q f n) τ)
            (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)) (Iso.refl _)
    exact preservesLimitsOfShape_of_reflects_of_preserves _ (SheafOfModules.toSheaf _)
  let := preservesMonomorphisms_of_preservesLimitsOfShape R
  have hi : Injective (R.obj M) :=
    moduleRestriction_preservesInjectives.{u, max vᵤ vₓ wₓ, vₓ, max wᵤ wₓ, wₓ, a}
      B S hS q (Tuple.projection q f n) τ hq (h n) M
  exact (restrictSheafAdjunction.{max wᵤ wₓ, wₓ, max vᵤ vₓ wₓ, vₓ, u,
    max u vᵤ vₓ wᵤ wₓ a} (Tuple.projection q f n)
    (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS
      (tupleStructureFunctor B S hS q f n) τ)
    (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
    (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
      (B.baseTopology_le_topology τ))).map_injective _ hi

/-- On underlying abelian presheaves, the augmentation of `M` is the unit of the right Kan
extension adjunction. -/
private lemma cechModuleAugmentation_presheafIso :
    ((SheafOfModules.toSheaf _).map
        (cechModuleAugmentation.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M)).hom ≫
        (cechModulePresheafIso.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq M 0).hom =
      ((Tuple.projection q f 0).op.ranAdjunction
        AddCommGrpCat.{max u vᵤ vₓ wᵤ wₓ a}).unit.app M.val.presheaf := by
  apply ((Tuple.projection q f 0).op.ran.obj
    ((Tuple.projection q f 0).op ⋙ M.val.presheaf)).hom_ext_of_isRightKanExtension
    ((Tuple.projection q f 0).op.ranCounit.app _)
  rw [Functor.whiskerLeft_comp, Category.assoc, cechModulePresheafIso_fac]
  trans 𝟙 ((Tuple.projection q f 0).op ⋙ M.val.presheaf)
  · ext x s
    change M.val.presheaf.map (𝟙 _) s = s
    rw [M.val.presheaf.map_id]
    rfl
  · exact (((Tuple.projection q f 0).op.ranAdjunction
      AddCommGrpCat.{max u vᵤ vₓ wᵤ wₓ a}).left_triangle_components M.val.presheaf).symm

/-- The degree-`n` component of `cechModuleComplexSheafIso` is sheafification followed by
`cechModulePresheafIso`. -/
private lemma cechModuleComplexSheafIso_hom_f (n : ℕ) :
    (cechModuleComplexSheafIso.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M).hom.f n =
      (sheafificationIso ((SheafOfModules.toSheaf _).obj
        (cechModuleSheaf.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M n))).hom ≫
      (presheafToSheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
        AddCommGrpCat.{max u vᵤ vₓ wᵤ wₓ a}).map
        (cechModulePresheafIso.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq M n).hom := by
  simp only [Functor.mapHomologicalComplex_obj_X, Stack.ringStructureSheafCore_obj,
    BigFppfOver.structureSheaf_obj, complex_X, cechModuleComplexSheafIso,
    alternatingCofaceMapComplex, AlternatingCofaceMapComplex.map,
    AlternatingCofaceMapComplex.obj, CochainComplex.of, cechModuleCosimplicial,
    Functor.comp_obj, mapAlternatingCofaceIso, cosimplicial, cechModuleCosimplicialSheafIso,
    sheafificationNatIso, cechModuleCosimplicialForgetIso, Functor.mapIso_trans, Functor.id_obj,
    Functor.mapIso_symm, ObjectProperty.ι_obj, Iso.trans_assoc, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, Functor.rightUnitor_inv_app, Functor.mapIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, NatIso.ofComponents_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    HomologicalComplex.comp_f, HomologicalComplex.Hom.isoOfComponents_hom_f, Iso.refl_hom,
    HomologicalComplex.Hom.isoOfComponents_inv_f, Iso.refl_inv, Category.comp_id,
    Category.id_comp]
  exact Category.id_comp _

/-- On underlying abelian sheaves, the augmentation of `M` is the augmentation of the abelian
relative Čech complex. -/
private lemma cechModuleAugmentation_sheafIso :
    (SheafOfModules.toSheaf _).map
        (cechModuleAugmentation.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M) ≫
        (cechModuleComplexSheafIso.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M).hom.f 0 =
      Stacks.RelativeCech.sheafAugmentation B S hS q f τ
        ((SheafOfModules.toSheaf _).obj M) := by
  rw [cechModuleComplexSheafIso_hom_f, ← Category.assoc]
  rw [show (SheafOfModules.toSheaf _).map
      (cechModuleAugmentation.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M) ≫
          (sheafificationIso _).hom =
      (sheafificationIso _).hom ≫ (presheafToSheaf _ _).map
        (((SheafOfModules.toSheaf _).map
          (cechModuleAugmentation.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M)).hom) from
    (sheafificationNatIso _ _).hom.naturality _]
  rw [Category.assoc, ← Functor.map_comp, cechModuleAugmentation_presheafIso]
  rfl

variable (hp : p.IsFiberedInGroupoids) (hf : p.IsFibredOneMorphism q f)
  (hcover : ∀ x : 𝒳, ∃ R : Presieve x,
    Sieve.generate R ∈ AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ x ∧
      ∀ ⦃y : 𝒳⦄ (g : y ⟶ x), R g → ∃ z : 𝒰, Nonempty (y ≅ f.obj z))

include hp hf hcover

omit hp hf in
/-- If the image of `f` covers every object of `𝒳` locally, the augmentation of `M` into its
relative Čech complex is a monomorphism. -/
private lemma cechModuleAugmentation_mono :
    Mono (cechModuleAugmentation.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M) := by
  have : Mono ((SheafOfModules.toSheaf _).map
      (cechModuleAugmentation.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M) ≫
      (cechModuleComplexSheafIso.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M).hom.f 0) := by
    rw [cechModuleAugmentation_sheafIso.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M]
    exact Stacks.RelativeCech.mono_sheafAugmentation.{u, vᵤ, vₓ, wᵤ, wₓ,
      max u vᵤ vₓ wᵤ wₓ a} B S hS q f τ hcover _
  exact (SheafOfModules.toSheaf _).mono_of_mono_map
    (mono_of_mono ((SheafOfModules.toSheaf _).map
        (cechModuleAugmentation.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M))
      ((cechModuleComplexSheafIso.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M).hom.f 0))

/-- If the image of `f` covers every object of `𝒳` locally, the augmentation of `M` is the kernel
of the first differential of its relative Čech complex. -/
private lemma cechModuleAugmentation_exact :
    (ShortComplex.mk (cechModuleAugmentation.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M)
      ((cechModuleComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M).d 0 1)
      (cechModuleAugmentation_d.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M)).Exact := by
  let U := SheafOfModules.toSheaf (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq
      (B.baseTopology τ)
        (B.baseTopology_le_topology τ))
  have hexact := Stacks.RelativeCech.exact_sheafAugmentation.{u, vᵤ, vₓ,
    wᵤ, wₓ, max u vᵤ vₓ wᵤ wₓ a} B S hS p q f τ hp hq hf hcover (U.obj M)
  apply U.reflects_exact_of_faithful
  let e := cechModuleComplexSheafIso.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M
  refine (ShortComplex.exact_iff_of_iso ?_).mpr hexact
  refine ShortComplex.isoMk (Iso.refl _)
    ((HomologicalComplex.eval _ _ 0).mapIso e)
    ((HomologicalComplex.eval _ _ 1).mapIso e) ?_ ?_
  · exact (Category.id_comp _).trans
      (cechModuleAugmentation_sheafIso.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M).symm
  · exact e.hom.comm 0 1

/-- If the image of `f` covers every object of `𝒳` locally, the relative Čech complex of `M` is
exact in every positive degree. -/
private lemma cechModuleComplex_exactAt_succ (n : ℕ) :
    (cechModuleComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M).ExactAt (n + 1) := by
  let U := SheafOfModules.toSheaf (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq
      (B.baseTopology τ)
        (B.baseTopology_le_topology τ))
  have he := Stacks.RelativeCech.exactAt_sheafComplex_succ.{u, vᵤ, vₓ, wᵤ, wₓ,
    max u vᵤ vₓ wᵤ wₓ a} B S hS p q f τ hp hq hf hcover (U.obj M) n
  have he' := he.of_iso (cechModuleComplexSheafIso.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M).symm
  rw [HomologicalComplex.exactAt_iff] at he' ⊢
  exact U.reflects_exact_of_faithful _ he'

/-- If the image of `f` covers every object of `𝒳` locally, the augmentation of `M` into its
relative Čech complex is a quasi-isomorphism. -/
private lemma cechModuleAugmentation_quasiIso :
    QuasiIso (cechModuleAugmentationComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M) := by
  let := cechModuleAugmentation_mono.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M hcover
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
        ⟨cechModuleAugmentation_exact.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS p q f τ hq h M hp hf hcover,
          by dsimp; infer_instance⟩
      refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
      · change 𝟙 M ≫ cechModuleAugmentation.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M =
          (cechModuleAugmentationComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M).f 0 ≫
            𝟙 ((cechModuleComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M).X 0)
        rw [Category.id_comp, Category.comp_id]
        simp [cechModuleAugmentationComplex]
      · change 𝟙 ((cechModuleComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M).X 0) ≫
            (cechModuleComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M).d 0 1 =
          (cechModuleComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M).d 0 1 ≫
            𝟙 ((cechModuleComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M).X 1)
        rw [Category.id_comp, Category.comp_id]
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _)]
    exact cechModuleComplex_exactAt_succ.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS p q f τ hq h M hp hf hcover n

/-- For `M` injective, the augmentation of the relative Čech complex of sections of `M` is a
quasi-isomorphism. -/
private lemma cechSectionsAugmentation_quasiIso [f.Faithful]
    (heq : ∀ n, HasEqualizers (Tuple q f n)) [Injective M] :
    QuasiIso ((cechSectionsAugmentationComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a}
      B S hS q f τ hq h).app M) := by
  let I : InjectiveResolution M :=
    { cocomplex := cechModuleComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M
      injective := cechModuleSheaf_injective.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M heq
      ι := cechModuleAugmentationComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M
      quasiIso := cechModuleAugmentation_quasiIso.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS p q f τ hq h M hp
          hf hcover }
  let G := Stacks.Cohomology.SiteModules.globalSectionsFunctor
    (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ))
  let e := (InjectiveResolution.self M).homotopyEquiv I
  have he : e.hom = I.ι :=
    (Category.id_comp e.hom).symm.trans
      (InjectiveResolution.homotopyEquiv_hom_ι (InjectiveResolution.self M) I)
  have : QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι) := by
    rw [← he]
    exact (G.mapHomotopyEquiv e).quasiIso_hom
  rw [← cechModuleSectionsAugmentation.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M]
  infer_instance

end CechRows

end Stacks.RelativeCech

end
