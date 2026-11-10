module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Tactic.Abel
public import StacksCore.Algebra.Homology.TotalComplex
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.RecoveryC.CechCupProduct.AlexanderWhitney

/-!
# The cup-product map on Čech total complexes

The Alexander--Whitney formula, with the Koszul signs dictated by totalization, gives a
map from the tensor product of two total Čech complexes to the total Čech complex of the
tensor product.

## Main definitions

* `Stacks.Cech.CupProduct.cechCupProductSummand` is the signed Alexander--Whitney map on the
  tensor product of two homogeneous summands.
* `Stacks.Cech.CupProduct.cechCupProduct` is the signed Alexander--Whitney map.

## Main results

* `Stacks.Cech.CupProduct.cechCupProduct_ι`: the cup product on a pair of homogeneous Čech
  summands is the signed front/back restriction formula of Tag 07MB.

## Implementation notes

The tensor product of two total Čech complexes is described in each degree through the tensor
product of two coproducts of modules, which is the coproduct of the tensor products of the
summands. The summand formula is the formula of Tag 07MB with `n = r + a` and `p = r + s`; by
additivity it gives the displayed sum over `r`. The construction applies to presheaf complexes,
arbitrary families of opens and unbounded complexes, since all totalizations use direct sums.

## References

* [Stacks Project, Tag 07MB](https://stacks.math.columbia.edu/tag/07MB)
* [SGA4, Exposé XVII]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape DirectSum Opposite

universe u v w w' r

namespace Stacks.Cech.CupProduct

attribute [local implicit_reducible] CategoryTheory.cechComplexFunctor
  HomologicalComplex₂.ofGradedObject
  HomologicalComplex₂.flip
  HomologicalComplex₂.flipFunctor
  ComplexShape.Embedding.extendFunctor
  CategoryTheory.Functor.mapBifunctorHomologicalComplex
  CategoryTheory.Functor.mapBifunctorHomologicalComplexObj
  CategoryTheory.GradedObject.mapBifunctor
  HomologicalComplex₂.totalFunctor
  CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor
  CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor
  CategoryTheory.Limits.FormalCoproduct.evalOp

open scoped TensorProduct

variable (X : TopCat.{u}) {ι : Type v} (U : ι → TopologicalSpace.Opens X)

/-- `HomologicalComplex.extend_d_eq` with the Čech cochains named. -/
private theorem cechExtend_d_eq (F : ZPresheaf.{u, max v w} X) (p : ℕ) {p' q' : ℤ}
    (hp : (p : ℤ) = p') (hq : ((p + 1 : ℕ) : ℤ) = q') :
    (((CategoryTheory.cechComplexFunctor U).obj F).extend embeddingUpNat).d p' q' =
      (cechExtendXIso.{u, v, w} X U F p hp).hom ≫ cechD.{u, v, w} X U F p ≫
        (cechExtendXIso.{u, v, w} X U F (p + 1) hq).inv :=
  HomologicalComplex.extend_d_eq _ _ hp hq

/-- `HomologicalComplex.extendMap_f` with the Čech cochains named. -/
private theorem cechExtendMap_f {F G : ZPresheaf.{u, max v w} X} (φ : F ⟶ G) (p : ℕ) {p' : ℤ}
    (h : (p : ℤ) = p') :
    (HomologicalComplex.extendMap
        ((CategoryTheory.cechComplexFunctor U).map φ) embeddingUpNat).f p' =
      (cechExtendXIso.{u, v, w} X U F p h).hom ≫ cechCochainsMap.{u, v, w} X U φ p ≫
        (cechExtendXIso.{u, v, w} X U G p h).inv :=
  HomologicalComplex.extendMap_f _ _ h

/-- The differential of the total Čech complex is the differential of the total complex of
the Čech double complex. -/
private theorem totalCechComplex_d (F : CochainComplex (ZPresheaf.{u, max v w} X) ℤ)
    (n m : ℤ) :
    ((totalCechComplexFunctor.{u, v, w} X U).obj F).d n m =
      ((totalCechBicomplex.{u, v, w} X U F).total (up ℤ)).d n m :=
  rfl

/-- The tensor product of two coproducts of modules is the coproduct of the tensor products of
the summands. -/
noncomputable def moduleCoprodTensorCoprodIso
    {R : Type r} [CommRing R] {ι : Type} {κ : Type}
    (M : ι → ModuleCat.{w} R) (N : κ → ModuleCat.{w'} R)
    [DecidableEq ι] [DecidableEq κ] [HasCoproduct M] [HasCoproduct N]
    [HasCoproduct (fun ij : ι × κ =>
      ((tensorModules.{w, w'} R).obj (M ij.1)).obj (N ij.2))] :
    ((tensorModules.{w, w'} R).obj (∐ M)).obj (∐ N) ≅
      ∐ fun ij : ι × κ =>
        ((tensorModules.{w, w'} R).obj (M ij.1)).obj (N ij.2) := by
  let eM : (∐ M) ≅ ModuleCat.of R (⨁ i, M i) := ModuleCat.coprodIsoDirectSum M
  let eN : (∐ N) ≅ ModuleCat.of R (⨁ i, N i) := ModuleCat.coprodIsoDirectSum N
  let eMN := ModuleCat.coprodIsoDirectSum
    (fun ij : ι × κ =>
      ((tensorModules.{w, w'} R).obj (M ij.1)).obj (N ij.2))
  let eRight := ((tensorModules.{w, w'} R).obj (∐ M)).mapIso eN
  let eLeft := ((tensorModules.{w, w'} R).mapIso eM).app
    (ModuleCat.of R (⨁ i, N i))
  let eDS := TensorProduct.directSum R R (fun i => (M i).1) (fun i => (N i).1)
  exact eRight ≪≫ eLeft ≪≫
    eDS.toModuleIso ≪≫ eMN.symm

/-- A morphism out of the tensor product of two coproducts of modules, given on the tensor
product of each pair of summands. -/
noncomputable def moduleCoprodTensorCoprodDesc
    {R : Type r} [CommRing R] {ι κ : Type}
    (M : ι → ModuleCat.{w} R) (N : κ → ModuleCat.{w'} R)
    [DecidableEq ι] [DecidableEq κ] [HasCoproduct M] [HasCoproduct N]
    [HasCoproduct (fun ij : ι × κ =>
      ((tensorModules.{w, w'} R).obj (M ij.1)).obj (N ij.2))]
    {A : ModuleCat.{max w w'} R}
    (f : ∀ i j, ((tensorModules.{w, w'} R).obj (M i)).obj (N j) ⟶ A) :
    ((tensorModules.{w, w'} R).obj (∐ M)).obj (∐ N) ⟶ A :=
  let e := moduleCoprodTensorCoprodIso M N
  e.hom ≫ Sigma.desc (fun ij : ι × κ => f ij.1 ij.2)

/-- The tensor of two summand inclusions followed by `moduleCoprodTensorCoprodIso` is the
corresponding summand inclusion. -/
private theorem tensorModulesMap_ι_comp_moduleCoprodTensorCoprodIso_hom
    {R : Type r} [CommRing R] {ι κ : Type}
    (M : ι → ModuleCat.{w} R) (N : κ → ModuleCat.{w'} R)
    [DecidableEq ι] [DecidableEq κ] [HasCoproduct M] [HasCoproduct N]
    [HasCoproduct (fun ij : ι × κ =>
      ((tensorModules.{w, w'} R).obj (M ij.1)).obj (N ij.2))]
    (i : ι) (j : κ) :
    tensorModulesMap R (Sigma.ι M i) (Sigma.ι N j) ≫ (moduleCoprodTensorCoprodIso M N).hom =
      Sigma.ι
        (fun ij : ι × κ => ((tensorModules.{w, w'} R).obj (M ij.1)).obj (N ij.2)) (i, j) := by
  let P : ι × κ → ModuleCat.{max w w'} R :=
    fun ij => ModuleCat.of R ((M ij.1).1 ⊗[R] (N ij.2).1)
  let eMN := ModuleCat.coprodIsoDirectSum P
  have hcomp : tensorModulesMap R (Sigma.ι M i) (Sigma.ι N j) ≫
      (moduleCoprodTensorCoprodIso M N).hom ≫ eMN.hom = Sigma.ι P (i, j) ≫ eMN.hom := by
    let eM := ModuleCat.coprodIsoDirectSum M
    let eN := ModuleCat.coprodIsoDirectSum N
    let eRight := ((tensorModules.{w, w'} R).obj (∐ M)).mapIso eN
    let eLeft := ((tensorModules.{w, w'} R).mapIso eM).app
      (ModuleCat.of R (⨁ i, (N i).1))
    let eDS := TensorProduct.directSum R R (fun i => (M i).1) (fun i => (N i).1)
    have hm (x : M i) : eM.hom.hom ((Sigma.ι M i).hom x) =
        DirectSum.lof R ι (fun k => (M k).1) i x := by
      exact congrArg (fun f => f.hom x) (ModuleCat.ι_coprodIsoDirectSum_hom (Z := M) i)
    have hn (y : N j) : eN.hom.hom ((Sigma.ι N j).hom y) =
        DirectSum.lof R κ (fun k => (N k).1) j y := by
      exact congrArg (fun f => f.hom y) (ModuleCat.ι_coprodIsoDirectSum_hom (Z := N) j)
    have hprefix : tensorModulesMap R (Sigma.ι M i) (Sigma.ι N j) ≫
        eRight.hom ≫ eLeft.hom = ModuleCat.ofHom (TensorProduct.map
          (DirectSum.lof R ι (fun k => (M k).1) i)
          (DirectSum.lof R κ (fun k => (N k).1) j)) := by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      ext x y
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, tensorModulesMap]
      dsimp [eRight, eLeft, tensorModules]
      change (eM.hom.hom ((Sigma.ι M i).hom x)) ⊗ₜ[R]
          (eN.hom.hom ((Sigma.ι N j).hom y)) =
        (DirectSum.lof R ι (fun k => (M k).1) i x) ⊗ₜ[R]
          (DirectSum.lof R κ (fun k => (N k).1) j y)
      rw [hm, hn]
    have hprefixL : (tensorModulesMap R (Sigma.ι M i) (Sigma.ι N j) ≫ eRight.hom) ≫
        eLeft.hom = ModuleCat.ofHom (TensorProduct.map
          (DirectSum.lof R ι (fun k => (M k).1) i)
          (DirectSum.lof R κ (fun k => (N k).1) j)) := by
      rw [Category.assoc]
      exact hprefix
    have hpost : ModuleCat.ofHom (TensorProduct.map
        (DirectSum.lof R ι (fun k => (M k).1) i)
        (DirectSum.lof R κ (fun k => (N k).1) j)) ≫
        ModuleCat.ofHom eDS.toLinearMap = Sigma.ι P (i, j) ≫ eMN.hom := by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      ext x y
      simp [eDS, eMN, TensorProduct.directSum_lof_tmul_lof,
        ModuleCat.ι_coprodIsoDirectSum_hom, ModuleCat.hom_comp]
      rfl
    change tensorModulesMap R (Sigma.ι M i) (Sigma.ι N j) ≫
      eRight.hom ≫ eLeft.hom ≫ eDS.toModuleIso.hom ≫ eMN.symm.hom ≫ eMN.hom = _
    rw [← Category.assoc, ← Category.assoc, hprefixL]
    rw [← hpost]
    calc
      _ = ModuleCat.ofHom (TensorProduct.map
            (DirectSum.lof R ι (fun k => (M k).1) i)
            (DirectSum.lof R κ (fun k => (N k).1) j)) ≫ eDS.toModuleIso.hom ≫
            (eMN.symm.hom ≫ eMN.hom) := rfl
      _ = ModuleCat.ofHom (TensorProduct.map
            (DirectSum.lof R ι (fun k => (M k).1) i)
            (DirectSum.lof R κ (fun k => (N k).1) j)) ≫ eDS.toModuleIso.hom ≫ 𝟙 _ := by
          simp only [Iso.symm_hom, Iso.inv_hom_id]
      _ = ModuleCat.ofHom (TensorProduct.map
            (DirectSum.lof R ι (fun k => (M k).1) i)
            (DirectSum.lof R κ (fun k => (N k).1) j)) ≫ eDS.toModuleIso.hom := by simp
  exact (cancel_mono eMN.hom).mp hcomp

/-- `moduleCoprodTensorCoprodDesc` restricted to the tensor of two summand inclusions is the
corresponding component of the given family. -/
theorem moduleCoprodTensorCoprodDesc_ι
    {R : Type r} [CommRing R] {ι κ : Type}
    (M : ι → ModuleCat.{w} R) (N : κ → ModuleCat.{w'} R)
    [DecidableEq ι] [DecidableEq κ] [HasCoproduct M] [HasCoproduct N]
    [HasCoproduct (fun ij : ι × κ =>
      ((tensorModules.{w, w'} R).obj (M ij.1)).obj (N ij.2))]
    {A : ModuleCat.{max w w'} R}
    (f : ∀ i j, ((tensorModules.{w, w'} R).obj (M i)).obj (N j) ⟶ A)
    (i : ι) (j : κ) :
    tensorModulesMap R (Sigma.ι M i) (Sigma.ι N j) ≫
      moduleCoprodTensorCoprodDesc M N f = f i j := by
  change tensorModulesMap R (Sigma.ι M i) (Sigma.ι N j) ≫
      (moduleCoprodTensorCoprodIso M N).hom ≫ Sigma.desc (fun ij : ι × κ => f ij.1 ij.2) = _
  rw [← Category.assoc, tensorModulesMap_ι_comp_moduleCoprodTensorCoprodIso_hom]
  simp

/-- Two morphisms out of the tensor product of two coproducts agree as soon as they agree on
the tensor of every pair of summand inclusions. -/
theorem moduleCoprodTensorCoprod_hom_ext
    {R : Type r} [CommRing R] {ι κ : Type}
    (M : ι → ModuleCat.{w} R) (N : κ → ModuleCat.{w'} R)
    [HasCoproduct M] [HasCoproduct N]
    [HasCoproduct (fun ij : ι × κ =>
      ((tensorModules.{w, w'} R).obj (M ij.1)).obj (N ij.2))]
    {A : ModuleCat.{max w w'} R}
    {f g : ((tensorModules.{w, w'} R).obj (∐ M)).obj (∐ N) ⟶ A}
    (h : ∀ i j, tensorModulesMap R (Sigma.ι M i) (Sigma.ι N j) ≫ f =
      tensorModulesMap R (Sigma.ι M i) (Sigma.ι N j) ≫ g) : f = g := by
  classical
  let P : ι × κ → ModuleCat.{max w w'} R :=
    fun ij => ((tensorModules.{w, w'} R).obj (M ij.1)).obj (N ij.2)
  let e := moduleCoprodTensorCoprodIso M N
  have hι (i : ι) (j : κ) :
      Sigma.ι P (i, j) ≫ e.symm.hom = tensorModulesMap R (Sigma.ι M i) (Sigma.ι N j) := by
    rw [Iso.symm_hom, Iso.comp_inv_eq]
    exact (tensorModulesMap_ι_comp_moduleCoprodTensorCoprodIso_hom M N i j).symm
  apply (cancel_epi e.symm.hom).1
  apply Sigma.hom_ext
  rintro ⟨i, j⟩
  change (Sigma.ι P (i, j) ≫ e.symm.hom) ≫ f =
    (Sigma.ι P (i, j) ≫ e.symm.hom) ≫ g
  rw [hι i j]
  exact h i j

/-- The map from a tensor of coefficient sheaves into the corresponding tensor-total term. -/
noncomputable abbrev ιTensorSheafComplex
    (F : CochainComplex (ZPresheaf.{u, max u w} X) ℤ)
    (G : CochainComplex (ZPresheaf.{u, max u w'} X) ℤ)
    (a b : ℤ) :
    ((tensorPresheaves ℤ X).obj (F.X a)).obj (G.X b) ⟶
      (tensorSheafComplex X F G).X (a + b) :=
  HomologicalComplex.ιMapBifunctor F G (tensorPresheaves ℤ X) (up ℤ)
      a b (a + b) rfl ≫
      toSheafify (Opens.grothendieckTopology X)
      ((HomologicalComplex.mapBifunctor F G (tensorPresheaves ℤ X) (up ℤ)).X
        (a + b))

private noncomputable def ιTotalCechTo
    (F : CochainComplex (ZPresheaf.{u, max v w} X) ℤ)
    (p : ℕ) (a n : ℤ) (h : (p : ℤ) + a = n) :
    cechCochains.{u, v, w} X U (F.X a) p ⟶
      ((totalCechComplexFunctor.{u, v, w} X U).obj F).X n :=
  (cechExtendXIso.{u, v, w} X U (F.X a) p rfl).inv ≫
    (totalCechBicomplex X U F).ιTotal (up ℤ) p a n h

private theorem ιTotalCechTo_eq
    (F : CochainComplex (ZPresheaf.{u, max v w} X) ℤ)
    (p : ℕ) (a n : ℤ) (h : (p : ℤ) + a = n) :
    ιTotalCechTo X U F p a n h = ιTotalCech X U F p a ≫
      eqToHom (congrArg (((totalCechComplexFunctor X U).obj F).X) h) := by
  subst n
  simp only [eqToHom_refl, Category.comp_id]
  rfl

private theorem ιTotalCechTo_d
    (F : CochainComplex (ZPresheaf.{u, max v w} X) ℤ)
    (p : ℕ) (a n : ℤ) (h : (p : ℤ) + a = n) :
    ιTotalCechTo X U F p a n h ≫
      ((totalCechComplexFunctor X U).obj F).d n (n + 1) =
    cechD.{u, v, w} X U (F.X a) p ≫
      ιTotalCechTo X U F (p + 1) a (n + 1) (by push_cast; omega) +
    (p : ℤ).negOnePow • (cechCochainsMap X U (F.d a (a + 1)) p ≫
      ιTotalCechTo X U F p (a + 1) (n + 1) (by omega)) := by
  unfold ιTotalCechTo
  rw [Category.assoc, totalCechComplex_d, HomologicalComplex₂.ιTotal_d_up_ℤ,
    Preadditive.comp_add, Linear.comp_units_smul]
  congr 1
  · change _ ≫ (((CategoryTheory.cechComplexFunctor U).obj (F.X a)).extend
      embeddingUpNat).d (p : ℤ) (p + 1) ≫ _ = _
    rw [cechExtend_d_eq X U (F.X a) p rfl (q' := (p : ℤ) + 1) (by push_cast; ring)]
    simp only [Iso.inv_hom_id_assoc, Category.assoc]
    congr 1
  · congr 1
    change _ ≫ (HomologicalComplex.extendMap
      ((CategoryTheory.cechComplexFunctor U).map (F.d a (a + 1))) embeddingUpNat).f (p : ℤ) ≫ _ = _
    rw [cechExtendMap_f X U (F.d a (a + 1)) p rfl]
    simp only [Iso.inv_hom_id_assoc, Category.assoc]

private noncomputable def ιTensorSheafTo
    (F : CochainComplex (ZPresheaf.{u, max u w} X) ℤ)
    (G : CochainComplex (ZPresheaf.{u, max u w'} X) ℤ)
    (a b n : ℤ) (h : a + b = n) :
    ((tensorPresheaves ℤ X).obj (F.X a)).obj (G.X b) ⟶
      (tensorSheafComplex X F G).X n :=
  HomologicalComplex.ιMapBifunctor F G (tensorPresheaves ℤ X) (up ℤ) a b n h ≫
    toSheafify (Opens.grothendieckTopology X)
      ((HomologicalComplex.mapBifunctor F G (tensorPresheaves ℤ X) (up ℤ)).X n)

private theorem ιTensorSheafTo_d
    (F : CochainComplex (ZPresheaf.{u, max u w} X) ℤ)
    (G : CochainComplex (ZPresheaf.{u, max u w'} X) ℤ)
    (a b n : ℤ) (h : a + b = n) :
    ιTensorSheafTo X F G a b n h ≫ (tensorSheafComplex X F G).d n (n + 1) =
    ((tensorPresheaves ℤ X).map (F.d a (a + 1))).app (G.X b) ≫
      ιTensorSheafTo X F G (a + 1) b (n + 1) (by omega) +
    a.negOnePow • (((tensorPresheaves ℤ X).obj (F.X a)).map (G.d b (b + 1)) ≫
      ιTensorSheafTo X F G a (b + 1) (n + 1) (by omega)) := by
  change (_ ≫ toSheafify _ _) ≫ sheafifyMap _ _ = _
  rw [Category.assoc, ← toSheafify_naturality, ← Category.assoc]
  rw [HomologicalComplex₂.ιTotal_d_up_ℤ]
  rw [Preadditive.add_comp, Category.assoc, Linear.units_smul_comp, Category.assoc]
  rfl

@[reassoc] private theorem cechCochainsMap_comp {F G H : ZPresheaf.{u, max v w} X}
    (f : F ⟶ G) (g : G ⟶ H) (p : ℕ) :
    cechCochainsMap X U (f ≫ g) p = cechCochainsMap X U f p ≫ cechCochainsMap X U g p :=
  congrArg (fun φ => HomologicalComplex.Hom.f φ p)
    ((CategoryTheory.cechComplexFunctor U).map_comp f g)

private theorem cechCochainsMap_id (F : ZPresheaf.{u, max v w} X) (p : ℕ) :
    cechCochainsMap X U (𝟙 F) p = 𝟙 _ :=
  congrArg (fun φ => HomologicalComplex.Hom.f φ p)
    ((CategoryTheory.cechComplexFunctor U).map_id F)

private theorem cechCochainsMap_add {F G : ZPresheaf.{u, max v w} X}
    (f g : F ⟶ G) (p : ℕ) :
    cechCochainsMap X U (f + g) p = cechCochainsMap X U f p + cechCochainsMap X U g p := by
  apply Pi.hom_ext (f := fun t : Fin (p + 1) → ι => G.obj (op (∏ᶜ (U ∘ t))))
  intro t
  simp only [cechCochainsMap_comp_π, Preadditive.add_comp]
  change _ ≫ (f.app _ + g.app _) = _
  rw [Preadditive.comp_add]

private theorem cechCochainsMap_zsmul {F G : ZPresheaf.{u, max v w} X}
    (f : F ⟶ G) (p : ℕ) (z : ℤ) :
    cechCochainsMap X U (z • f) p = z • cechCochainsMap X U f p := by
  apply Pi.hom_ext (f := fun t : Fin (p + 1) → ι => G.obj (op (∏ᶜ (U ∘ t))))
  intro t
  simp [cechCochainsMap_comp_π]

@[reassoc] private theorem cechCochainsMap_d {F G : ZPresheaf.{u, max v w} X}
    (f : F ⟶ G) (p : ℕ) :
    cechCochainsMap X U f p ≫ cechD X U G p =
      cechD X U F p ≫ cechCochainsMap X U f (p + 1) :=
  ((CategoryTheory.cechComplexFunctor U).map f).comm p (p + 1)

private noncomputable def tensorCechι
    (F : CochainComplex (ZPresheaf.{u, max v w} X) ℤ)
    (G : CochainComplex (ZPresheaf.{u, max v w'} X) ℤ)
    (r s : ℕ) (a b n : ℤ) (h : (r + a) + (s + b) = n) :
    ((tensorModules.{max v w, max v w'} ℤ).obj (cechCochains.{u, v, w} X U (F.X a) r)).obj
      (cechCochains.{u, v, w'} X U (G.X b) s) ⟶
    (HomologicalComplex.mapBifunctor ((totalCechComplexFunctor.{u, v, w} X U).obj F)
      ((totalCechComplexFunctor.{u, v, w'} X U).obj G)
      (tensorModules.{max v w, max v w'} ℤ) (up ℤ)).X n :=
  tensorModulesMap ℤ (ιTotalCech.{u, v, w} X U F r a) (ιTotalCech.{u, v, w'} X U G s b) ≫
    HomologicalComplex.ιMapBifunctor ((totalCechComplexFunctor.{u, v, w} X U).obj F)
      ((totalCechComplexFunctor.{u, v, w'} X U).obj G) (tensorModules ℤ) (up ℤ) (r + a) (s + b) n h

private theorem tensorCechι_eq
    (F : CochainComplex (ZPresheaf.{u, max v w} X) ℤ)
    (G : CochainComplex (ZPresheaf.{u, max v w'} X) ℤ)
    (r s : ℕ) (a b i j n : ℤ) (hi : r + a = i) (hj : s + b = j) (h : i + j = n) :
    tensorModulesMap ℤ (ιTotalCechTo.{u, v, w} X U F r a i hi)
        (ιTotalCechTo.{u, v, w'} X U G s b j hj) ≫
      HomologicalComplex.ιMapBifunctor ((totalCechComplexFunctor.{u, v, w} X U).obj F)
        ((totalCechComplexFunctor.{u, v, w'} X U).obj G) (tensorModules ℤ) (up ℤ) i j n h =
    tensorCechι.{u, v, w, w'} X U F G r s a b n (by omega) := by
  subst i j
  rfl

private theorem tensorModules_ι_d
    (K : CochainComplex (ModuleCat.{w} ℤ) ℤ)
    (L : CochainComplex (ModuleCat.{w'} ℤ) ℤ)
    (i j n : ℤ) (h : i + j = n) :
    HomologicalComplex.ιMapBifunctor K L (tensorModules ℤ) (up ℤ) i j n h ≫
      (HomologicalComplex.mapBifunctor K L (tensorModules ℤ) (up ℤ)).d n (n + 1) =
    tensorModulesMap ℤ (K.d i (i + 1)) (𝟙 _) ≫
      HomologicalComplex.ιMapBifunctor K L (tensorModules ℤ) (up ℤ) (i + 1) j (n + 1)
        (by (try dsimp); omega) +
    i.negOnePow • (tensorModulesMap ℤ (𝟙 _) (L.d j (j + 1)) ≫
      HomologicalComplex.ιMapBifunctor K L (tensorModules ℤ) (up ℤ) i (j + 1) (n + 1)
        (by (try dsimp); omega)) := by
  exact HomologicalComplex₂.ιTotal_d_up_ℤ _ i j n h

private theorem tensorModulesMap_add_left
    {M M' : ModuleCat.{w} ℤ} {N N' : ModuleCat.{w'} ℤ}
    (f f' : M ⟶ M') (g : N ⟶ N') :
    tensorModulesMap ℤ (f + f') g = tensorModulesMap ℤ f g + tensorModulesMap ℤ f' g :=
  ModuleCat.hom_ext (TensorProduct.map_add_left _ _ _)

private theorem tensorModulesMap_add_right
    {M M' : ModuleCat.{w} ℤ} {N N' : ModuleCat.{w'} ℤ}
    (f : M ⟶ M') (g g' : N ⟶ N') :
    tensorModulesMap ℤ f (g + g') = tensorModulesMap ℤ f g + tensorModulesMap ℤ f g' :=
  ModuleCat.hom_ext (TensorProduct.map_add_right _ _ _)

/-- Precomposing the first leg of `tensorCechι` with a cochain map, in terms of `tensorCechι`. -/
private theorem tensorModulesMap_comp_tensorCechι_left
    (F : CochainComplex (ZPresheaf.{u, max v w} X) ℤ)
    (G : CochainComplex (ZPresheaf.{u, max v w'} X) ℤ)
    (r s : ℕ) (a b i n : ℤ) (hi : r + a = i) (h : i + (s + b) = n)
    {M : ModuleCat.{max v w} ℤ} (f : M ⟶ cechCochains.{u, v, w} X U (F.X a) r) :
    tensorModulesMap ℤ (f ≫ ιTotalCechTo.{u, v, w} X U F r a i hi)
        (ιTotalCech.{u, v, w'} X U G s b) ≫
      HomologicalComplex.ιMapBifunctor ((totalCechComplexFunctor.{u, v, w} X U).obj F)
        ((totalCechComplexFunctor.{u, v, w'} X U).obj G) (tensorModules ℤ) (up ℤ)
        i (s + b) n h =
    tensorModulesMap ℤ f (𝟙 _) ≫ tensorCechι.{u, v, w, w'} X U F G r s a b n (by omega) := by
  rw [show ιTotalCech.{u, v, w'} X U G s b = 𝟙 _ ≫ ιTotalCech.{u, v, w'} X U G s b by simp,
    ← tensorModulesMap_comp, Category.assoc]
  exact congrArg (tensorModulesMap ℤ f (𝟙 _) ≫ ·)
    (tensorCechι_eq.{u, v, w, w'} X U F G r s a b i _ n hi rfl h)

/-- Precomposing the second leg of `tensorCechι` with a cochain map, in terms of `tensorCechι`. -/
private theorem tensorModulesMap_comp_tensorCechι_right
    (F : CochainComplex (ZPresheaf.{u, max v w} X) ℤ)
    (G : CochainComplex (ZPresheaf.{u, max v w'} X) ℤ)
    (r s : ℕ) (a b j n : ℤ) (hj : s + b = j) (h : (r + a) + j = n)
    {N : ModuleCat.{max v w'} ℤ} (g : N ⟶ cechCochains.{u, v, w'} X U (G.X b) s) :
    tensorModulesMap ℤ (ιTotalCech.{u, v, w} X U F r a)
        (g ≫ ιTotalCechTo.{u, v, w'} X U G s b j hj) ≫
      HomologicalComplex.ιMapBifunctor ((totalCechComplexFunctor.{u, v, w} X U).obj F)
        ((totalCechComplexFunctor.{u, v, w'} X U).obj G) (tensorModules ℤ) (up ℤ)
        (r + a) j n h =
    tensorModulesMap ℤ (𝟙 _) g ≫ tensorCechι.{u, v, w, w'} X U F G r s a b n (by omega) := by
  rw [show ιTotalCech.{u, v, w} X U F r a = 𝟙 _ ≫ ιTotalCech.{u, v, w} X U F r a by simp,
    ← tensorModulesMap_comp, Category.assoc]
  exact congrArg (tensorModulesMap ℤ (𝟙 _) g ≫ ·)
    (tensorCechι_eq.{u, v, w, w'} X U F G r s a b _ j n rfl hj h)

private theorem tensorCechι_d
    (F : CochainComplex (ZPresheaf.{u, max v w} X) ℤ)
    (G : CochainComplex (ZPresheaf.{u, max v w'} X) ℤ)
    (r s : ℕ) (a b n : ℤ) (h : (r + a) + (s + b) = n) :
    tensorCechι.{u, v, w, w'} X U F G r s a b n h ≫
      (HomologicalComplex.mapBifunctor ((totalCechComplexFunctor.{u, v, w} X U).obj F)
        ((totalCechComplexFunctor.{u, v, w'} X U).obj G) (tensorModules ℤ) (up ℤ)).d n (n + 1) =
    tensorModulesMap ℤ (cechD.{u, v, w} X U (F.X a) r) (𝟙 _) ≫
      tensorCechι.{u, v, w, w'} X U F G (r + 1) s a b (n + 1) (by push_cast; omega) +
    (r : ℤ).negOnePow • (tensorModulesMap ℤ
        (cechCochainsMap.{u, v, w} X U (F.d a (a + 1)) r) (𝟙 _) ≫
      tensorCechι.{u, v, w, w'} X U F G r s (a + 1) b (n + 1) (by omega)) +
    (r + a).negOnePow • (tensorModulesMap ℤ (𝟙 _) (cechD.{u, v, w'} X U (G.X b) s) ≫
      tensorCechι.{u, v, w, w'} X U F G r (s + 1) a b (n + 1) (by push_cast; omega) +
      (s : ℤ).negOnePow • (tensorModulesMap ℤ (𝟙 _)
          (cechCochainsMap.{u, v, w'} X U (G.d b (b + 1)) s) ≫
        tensorCechι.{u, v, w, w'} X U F G r s a (b + 1) (n + 1) (by omega))) := by
  change (tensorModulesMap ℤ _ _ ≫ _) ≫ _ = _
  rw [Category.assoc, tensorModules_ι_d]
  simp only [Units.smul_def]
  rw [Preadditive.comp_add, Preadditive.comp_zsmul,
    ← Category.assoc, tensorModulesMap_comp, Category.comp_id,
    ← Category.assoc, tensorModulesMap_comp, Category.comp_id]
  change tensorModulesMap ℤ (ιTotalCechTo.{u, v, w} X U F r a (r + a) rfl ≫ _) _ ≫ _ +
    ((r + a).negOnePow : ℤ) •
      (tensorModulesMap ℤ _ (ιTotalCechTo.{u, v, w'} X U G s b (s + b) rfl ≫ _) ≫ _) = _
  rw [ιTotalCechTo_d, ιTotalCechTo_d]
  simp only [Units.smul_def]
  rw [tensorModulesMap_add_left, tensorModulesMap_add_right,
    tensorModulesMap_smul_left, tensorModulesMap_smul_right]
  simp only [Preadditive.add_comp, Preadditive.zsmul_comp]
  simp only [tensorModulesMap_comp_tensorCechι_left, tensorModulesMap_comp_tensorCechι_right]
/-- The signed Alexander--Whitney map on the tensor product of two homogeneous summands of total
Čech complexes. -/
noncomputable def cechCupProductSummand
    (F : CochainComplex (ZPresheaf.{u, max u v w} X) ℤ)
    (G : CochainComplex (ZPresheaf.{u, max u v w'} X) ℤ)
    {n₁ n₂ n : ℤ} (hn : n₁ + n₂ = n)
    (α : totalCechIndex n₁)
    (β : totalCechIndex n₂) :
    ((tensorModules.{max u v w, max u v w'} ℤ).obj
      (totalCechSummand.{u, v, max u w} X U F n₁ α)).obj
        (totalCechSummand.{u, v, max u w'} X U G n₂ β) ⟶
      ((totalCechComplexFunctor.{u, v, max u w w'} X U).obj
        (tensorSheafComplex.{u, max v w, max v w'} X F G)).X n := by
  let r : ℕ := α.1.1
  let a : ℤ := α.1.2
  let s : ℕ := β.1.1
  let b : ℤ := β.1.2
  have htotal : (r + s : ℕ) + (a + b) = n := by
    have h₁ := α.2
    have h₂ := β.2
    dsimp [r, a, s, b] at h₁ h₂ ⊢
    omega
  exact cupProductSign (r + a) (r + s) r •
    (cechAlexanderWhitney.{u, v, max u w, max u w'} X U (F.X a) (G.X b) r s ≫
      cechCochainsMap.{u, v, max u w w'} X U
        (ιTensorSheafComplex.{u, max v w, max v w'} X F G a b) (r + s) ≫
      ιTotalCech.{u, v, max u w w'} X U
        (tensorSheafComplex.{u, max v w, max v w'} X F G) (r + s) (a + b) ≫
      eqToHom (congrArg
        (((totalCechComplexFunctor.{u, v, max u w w'} X U).obj
          (tensorSheafComplex.{u, max v w, max v w'} X F G)).X) htotal))

/-- The degree-`n` component of the cup-product map. -/
noncomputable def cechCupProductDegree
    (F : CochainComplex (ZPresheaf.{u, max u v w} X) ℤ)
    (G : CochainComplex (ZPresheaf.{u, max u v w'} X) ℤ) (n : ℤ) :
    ((HomologicalComplex.mapBifunctor
      ((totalCechComplexFunctor.{u, v, max u w} X U).obj F)
      ((totalCechComplexFunctor.{u, v, max u w'} X U).obj G)
      (tensorModules.{max u v w, max u v w'} ℤ) (up ℤ)).X n) ⟶
      ((totalCechComplexFunctor.{u, v, max u w w'} X U).obj
        (tensorSheafComplex.{u, max v w, max v w'} X F G)).X n :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := (totalCechComplexFunctor.{u, v, max u w} X U).obj F)
    (K₂ := (totalCechComplexFunctor.{u, v, max u w'} X U).obj G)
    (F := tensorModules.{max u v w, max u v w'} ℤ) (c := up ℤ)
    (j := n)
    (A := ((totalCechComplexFunctor.{u, v, max u w w'} X U).obj
        (tensorSheafComplex.{u, max v w, max v w'} X F G)).X n)
    (fun n₁ n₂ hn =>
      let M := totalCechSummand.{u, v, max u w} X U F n₁
      let N := totalCechSummand.{u, v, max u w'} X U G n₂
      tensorModulesMap ℤ
          ((totalCechXIsoCoproduct.{u, v, max u w} X U F n₁).hom)
          ((totalCechXIsoCoproduct.{u, v, max u w'} X U G n₂).hom) ≫
        moduleCoprodTensorCoprodDesc M N (fun α β =>
          cechCupProductSummand.{u, v, w, w'} X U F G hn α β))

private theorem tensorCechι_cechCupProductDegree
    (F : CochainComplex (ZPresheaf.{u, max u v w} X) ℤ)
    (G : CochainComplex (ZPresheaf.{u, max u v w'} X) ℤ)
    (r s : ℕ) (a b n : ℤ) (h : (r + a) + (s + b) = n) :
    tensorCechι.{u, v, max u w, max u w'} X U F G r s a b n h ≫
      cechCupProductDegree.{u, v, w, w'} X U F G n =
    cechCupProductSummand.{u, v, w, w'} X U F G h ⟨(r, a), rfl⟩ ⟨(s, b), rfl⟩ := by
  unfold tensorCechι cechCupProductDegree
  rw [Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
  rw [← Category.assoc, tensorModulesMap_comp,
    ιTotalCechIsoCoproduct.{u, v, max u w}, ιTotalCechIsoCoproduct.{u, v, max u w'},
    moduleCoprodTensorCoprodDesc_ι]

private noncomputable def cechTensorι
    (F : CochainComplex (ZPresheaf.{u, max u v w} X) ℤ)
    (G : CochainComplex (ZPresheaf.{u, max u v w'} X) ℤ)
    (r s : ℕ) (a b n : ℤ) (h : (r + a) + (s + b) = n) :=
  cechAlexanderWhitney.{u, v, max u w, max u w'} X U (F.X a) (G.X b) r s ≫
    cechCochainsMap.{u, v, max u w w'} X U
      (ιTensorSheafTo.{u, max v w, max v w'} X F G a b (a + b) rfl) (r + s) ≫
    ιTotalCechTo.{u, v, max u w w'} X U
      (tensorSheafComplex.{u, max v w, max v w'} X F G) (r + s) (a + b) n
      (by push_cast; omega)

private theorem cechTensorι_eq
    (F : CochainComplex (ZPresheaf.{u, max u v w} X) ℤ)
    (G : CochainComplex (ZPresheaf.{u, max u v w'} X) ℤ)
    (r s p : ℕ) (a b c n : ℤ) (hp : r + s = p) (hc : a + b = c)
    (hn : (p : ℤ) + c = n) :
    cechAlexanderWhitneyTo.{u, v, max u w, max u w'} X U (F.X a) (G.X b) r s p hp ≫
      cechCochainsMap.{u, v, max u w w'} X U
        (ιTensorSheafTo.{u, max v w, max v w'} X F G a b c hc) p ≫
      ιTotalCechTo.{u, v, max u w w'} X U
        (tensorSheafComplex.{u, max v w, max v w'} X F G) p c n hn =
      cechTensorι.{u, v, w, w'} X U F G r s a b n (by omega) := by
  subst p c
  rfl

@[reassoc] private theorem cechAlexanderWhitney_naturality_left
    {F F' : ZPresheaf.{u, max v w} X} (G : ZPresheaf.{u, max v w'} X)
    (f : F ⟶ F') (r s : ℕ) :
    cechAlexanderWhitney.{u, v, w, w'} X U F G r s ≫
      cechCochainsMap.{u, v, max w w'} X U (((tensorPresheaves ℤ X).map f).app G) (r + s) =
    tensorModulesMap ℤ (cechCochainsMap X U f r) (𝟙 _) ≫
      cechAlexanderWhitney.{u, v, w, w'} X U F' G r s := by
  have hn := cechAlexanderWhitney_naturality.{u, v, w, w'} X U f (𝟙 G) r s
  rw [CategoryTheory.Functor.map_id, Category.comp_id, cechCochainsMap_id] at hn
  exact hn

@[reassoc] private theorem cechAlexanderWhitney_naturality_right
    (F : ZPresheaf.{u, max v w} X) {G G' : ZPresheaf.{u, max v w'} X}
    (g : G ⟶ G') (r s : ℕ) :
    cechAlexanderWhitney.{u, v, w, w'} X U F G r s ≫
      cechCochainsMap.{u, v, max w w'} X U (((tensorPresheaves ℤ X).obj F).map g) (r + s) =
    tensorModulesMap ℤ (𝟙 _) (cechCochainsMap X U g s) ≫
      cechAlexanderWhitney.{u, v, w, w'} X U F G' r s := by
  have hn := cechAlexanderWhitney_naturality.{u, v, w, w'} X U (𝟙 F) g r s
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, cechCochainsMap_id] at hn
  exact hn

private theorem cechTensorι_d
    (F : CochainComplex (ZPresheaf.{u, max u v w} X) ℤ)
    (G : CochainComplex (ZPresheaf.{u, max u v w'} X) ℤ)
    (r s : ℕ) (a b n : ℤ) (h : (r + a) + (s + b) = n) :
    cechTensorι.{u, v, w, w'} X U F G r s a b n h ≫
      ((totalCechComplexFunctor.{u, v, max u w w'} X U).obj
        (tensorSheafComplex.{u, max v w, max v w'} X F G)).d n (n + 1) =
    tensorModulesMap ℤ (cechD.{u, v, max u w} X U (F.X a) r) (𝟙 _) ≫
      cechTensorι.{u, v, w, w'} X U F G (r + 1) s a b (n + 1) (by push_cast; omega) +
    (r : ℤ).negOnePow • (tensorModulesMap ℤ (𝟙 _) (cechD.{u, v, max u w'} X U (G.X b) s) ≫
      cechTensorι.{u, v, w, w'} X U F G r (s + 1) a b (n + 1) (by push_cast; omega)) +
    ((r + s : ℕ) : ℤ).negOnePow •
      (tensorModulesMap ℤ (cechCochainsMap.{u, v, max u w} X U (F.d a (a + 1)) r) (𝟙 _) ≫
        cechTensorι.{u, v, w, w'} X U F G r s (a + 1) b (n + 1) (by omega) +
      a.negOnePow • (tensorModulesMap ℤ (𝟙 _)
          (cechCochainsMap.{u, v, max u w'} X U (G.d b (b + 1)) s) ≫
        cechTensorι.{u, v, w, w'} X U F G r s a (b + 1) (n + 1) (by omega))) := by
  conv_lhs => unfold cechTensorι
  rw [Category.assoc, Category.assoc, ιTotalCechTo_d]
  simp only [Units.smul_def, Preadditive.comp_add, Preadditive.comp_zsmul]
  rw [← Category.assoc (cechCochainsMap _ _ _ _) _ _, cechCochainsMap_d,
    Category.assoc, ← Category.assoc, cechAlexanderWhitney_d]
  simp only [Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc]
  rw [← cechCochainsMap_comp_assoc, ιTensorSheafTo_d]
  simp only [Units.smul_def, cechCochainsMap_add, cechCochainsMap_zsmul,
    cechCochainsMap_comp, Preadditive.add_comp, Preadditive.zsmul_comp,
    Preadditive.comp_add, Preadditive.comp_zsmul, Category.assoc]
  rw [cechAlexanderWhitney_naturality_left_assoc,
    cechAlexanderWhitney_naturality_right_assoc]
  rw [Int.coe_negOnePow_natCast]
  congr 1
  · congr 1
    · congr 1
      exact cechTensorι_eq.{u, v, w, w'} X U F G (r + 1) s (r + s + 1)
        a b (a + b) (n + 1) (by omega) rfl (by push_cast; omega)
  · congr 1
    congr 1
    · congr 1
      exact cechTensorι_eq.{u, v, w, w'} X U F G r s (r + s)
        (a + 1) b (a + b + 1) (n + 1) rfl (by omega) (by push_cast; omega)
    · congr 1
      congr 1
      exact cechTensorι_eq.{u, v, w, w'} X U F G r s (r + s)
        a (b + 1) (a + b + 1) (n + 1) rfl (by omega) (by push_cast; omega)

/-- The sign identity rearranging the four terms of the Leibniz expansion of the cup product
differential into the four terms of the differential of the source. -/
theorem signed_four_terms {A : Type*} [AddCommGroup A]
    (r s a : ℤ) (x y z t : A) :
    ((a * s).negOnePow : ℤ) •
        (x + (r.negOnePow : ℤ) • y + ((r + s).negOnePow : ℤ) •
          (z + (a.negOnePow : ℤ) • t)) =
      ((a * s).negOnePow : ℤ) • x +
        (r.negOnePow : ℤ) • ((((a + 1) * s).negOnePow : ℤ) • z) +
        ((r + a).negOnePow : ℤ) •
          (((a * (s + 1)).negOnePow : ℤ) • y +
            (s.negOnePow : ℤ) • (((a * s).negOnePow : ℤ) • t)) := by
  have hy : ((a * s).negOnePow : ℤ) * (r.negOnePow : ℤ) =
      ((r + a).negOnePow : ℤ) * ((a * (s + 1)).negOnePow : ℤ) := by
    norm_cast
    simp only [← Int.negOnePow_add]
    apply (Int.negOnePow_eq_iff _ _).2
    change ∃ k : ℤ, _ = k + k
    refine ⟨-a, ?_⟩
    ring
  have hz : ((a * s).negOnePow : ℤ) * ((r + s).negOnePow : ℤ) =
      (r.negOnePow : ℤ) * (((a + 1) * s).negOnePow : ℤ) := by
    norm_cast
    simp only [← Int.negOnePow_add]
    congr 1
    ring
  have ht : ((a * s).negOnePow : ℤ) *
      (((r + s).negOnePow : ℤ) * (a.negOnePow : ℤ)) =
      ((r + a).negOnePow : ℤ) * ((s.negOnePow : ℤ) * ((a * s).negOnePow : ℤ)) := by
    norm_cast
    simp only [← Int.negOnePow_add]
    congr 1
    ring
  simp only [smul_add, smul_smul]
  rw [← hy, ← hz, ← ht]
  abel

/-- On the summand of Čech degrees `r` and `s` and first coefficient degree `a`, the
Alexander--Whitney sign reduces to `(-1)^(a * s)`. -/
theorem cupProductSign_summand (r s a : ℤ) :
    cupProductSign (r + a) (r + s) r = ((a * s).negOnePow : ℤ) := by
  unfold cupProductSign
  norm_cast
  apply (Int.negOnePow_eq_iff _ _).2
  change ∃ k : ℤ, _ = k + k
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self r
  refine ⟨k + r * r + r * s + r * a, ?_⟩
  calc
    _ = r * (r + 1) + 2 * (r * r) + 2 * (r * s) + 2 * (r * a) := by ring
    _ = _ := by rw [hk]; ring

private theorem cechCupProductSummand_eq
    (F : CochainComplex (ZPresheaf.{u, max u v w} X) ℤ)
    (G : CochainComplex (ZPresheaf.{u, max u v w'} X) ℤ)
    (r s : ℕ) (a b n : ℤ) (h : (r + a) + (s + b) = n) :
    cechCupProductSummand.{u, v, w, w'} X U F G h ⟨(r, a), rfl⟩ ⟨(s, b), rfl⟩ =
      ((a * s).negOnePow : ℤ) • cechTensorι.{u, v, w, w'} X U F G r s a b n h := by
  simp only [cechCupProductSummand, cechTensorι, ιTotalCechTo_eq, cupProductSign_summand]
  rfl

private theorem tensorCechι_hom_ext
    (F : CochainComplex (ZPresheaf.{u, max u v w} X) ℤ)
    (G : CochainComplex (ZPresheaf.{u, max u v w'} X) ℤ)
    {n : ℤ} {A : ModuleCat.{max u v w w'} ℤ}
    {f g : (HomologicalComplex.mapBifunctor
      ((totalCechComplexFunctor.{u, v, max u w} X U).obj F)
      ((totalCechComplexFunctor.{u, v, max u w'} X U).obj G)
      (tensorModules.{max u v w, max u v w'} ℤ) (up ℤ)).X n ⟶ A}
    (h : ∀ (r s : ℕ) (a b : ℤ) (h : (r + a) + (s + b) = n),
      tensorCechι.{u, v, max u w, max u w'} X U F G r s a b n h ≫ f =
      tensorCechι.{u, v, max u w, max u w'} X U F G r s a b n h ≫ g) : f = g := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro n₁ n₂ hn
  let M := totalCechSummand.{u, v, max u w} X U F n₁
  let N := totalCechSummand.{u, v, max u w'} X U G n₂
  let eF := totalCechXIsoCoproduct.{u, v, max u w} X U F n₁
  let eG := totalCechXIsoCoproduct.{u, v, max u w'} X U G n₂
  let tF := ((totalCechComplexFunctor.{u, v, max u w} X U).obj F).X n₁
  let tG := ((totalCechComplexFunctor.{u, v, max u w'} X U).obj G).X n₂
  let eL : ((tensorModules.{max u v w, max u v w'} ℤ).obj tF).obj tG ≅
      ((tensorModules.{max u v w, max u v w'} ℤ).obj (∐ M)).obj tG :=
    ((tensorModules.{max u v w, max u v w'} ℤ).mapIso eF).app tG
  let eR : ((tensorModules.{max u v w, max u v w'} ℤ).obj (∐ M)).obj tG ≅
      ((tensorModules.{max u v w, max u v w'} ℤ).obj (∐ M)).obj (∐ N) :=
    ((tensorModules.{max u v w, max u v w'} ℤ).obj (∐ M)).mapIso eG
  let e := eL ≪≫ eR
  apply (cancel_epi e.symm.hom).1
  apply moduleCoprodTensorCoprod_hom_ext M N
  intro α β
  rcases α with ⟨⟨r, a⟩, hr⟩
  subst n₁
  rcases β with ⟨⟨s, b⟩, hs⟩
  subst n₂
  have hF := ιTotalCechIsoCoproduct.{u, v, max u w} X U F r a
  have hG := ιTotalCechIsoCoproduct.{u, v, max u w'} X U G s b
  have hFinv : Sigma.ι M ⟨(r, a), by push_cast; rfl⟩ ≫ eF.inv =
      ιTotalCech.{u, v, max u w} X U F r a := by
    rw [← hF, Category.assoc]
    simp [M, eF]
  have hGinv : Sigma.ι N ⟨(s, b), by push_cast; rfl⟩ ≫ eG.inv =
      ιTotalCech.{u, v, max u w'} X U G s b := by
    rw [← hG, Category.assoc]
    simp [N, eG]
  have hinput : tensorModulesMap ℤ (Sigma.ι M ⟨(r, a), by push_cast; rfl⟩)
        (Sigma.ι N ⟨(s, b), by push_cast; rfl⟩) ≫ e.symm.hom =
      tensorModulesMap ℤ (ιTotalCech.{u, v, max u w} X U F r a)
        (ιTotalCech.{u, v, max u w'} X U G s b) := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change eF.inv.hom ((Sigma.ι M ⟨(r, a), by push_cast; rfl⟩).hom x) ⊗ₜ[ℤ]
          eG.inv.hom ((Sigma.ι N ⟨(s, b), by push_cast; rfl⟩).hom y) =
        (ιTotalCech.{u, v, max u w} X U F r a).hom x ⊗ₜ[ℤ]
          (ιTotalCech.{u, v, max u w'} X U G s b).hom y
    rw [show eF.inv.hom ((Sigma.ι M ⟨(r, a), by push_cast; rfl⟩).hom x) =
          (ιTotalCech.{u, v, max u w} X U F r a).hom x from
        congrArg (fun f => f.hom x) hFinv,
      show eG.inv.hom ((Sigma.ι N ⟨(s, b), by push_cast; rfl⟩).hom y) =
          (ιTotalCech.{u, v, max u w'} X U G s b).hom y from
        congrArg (fun f => f.hom y) hGinv]
  simp only [← Category.assoc, hinput]
  exact h r s a b hn

private theorem cechCupProductDegree_comm
    (F : CochainComplex (ZPresheaf.{u, max u v w} X) ℤ)
    (G : CochainComplex (ZPresheaf.{u, max u v w'} X) ℤ) (n : ℤ) :
    cechCupProductDegree.{u, v, w, w'} X U F G n ≫
        ((totalCechComplexFunctor.{u, v, max u w w'} X U).obj
          (tensorSheafComplex.{u, max v w, max v w'} X F G)).d n (n + 1) =
      (HomologicalComplex.mapBifunctor
        ((totalCechComplexFunctor.{u, v, max u w} X U).obj F)
        ((totalCechComplexFunctor.{u, v, max u w'} X U).obj G)
        (tensorModules.{max u v w, max u v w'} ℤ) (up ℤ)).d n (n + 1) ≫
        cechCupProductDegree.{u, v, w, w'} X U F G (n + 1) := by
  apply tensorCechι_hom_ext.{u, v, w, w'} X U F G
  intro r s a b h
  rw [← Category.assoc, tensorCechι_cechCupProductDegree,
    cechCupProductSummand_eq, Preadditive.zsmul_comp, cechTensorι_d]
  conv_rhs => rw [← Category.assoc, tensorCechι_d]
  simp only [Units.smul_def, Preadditive.add_comp, Preadditive.zsmul_comp,
    Category.assoc, tensorCechι_cechCupProductDegree, cechCupProductSummand_eq,
    Preadditive.comp_zsmul, Nat.cast_add, Nat.cast_one]
  exact signed_four_terms (r : ℤ) (s : ℤ) a _ _ _ _

/-- The signed Alexander--Whitney cup-product map

`Tot(Tot(Č(U,F)) ⊗_ℤ Tot(Č(U,G))) ⟶ Tot(Č(U,Tot(F ⊗_ℤ G)))`.

On the summand on which `α` has total degree `n`, the target has Čech degree `p`, and
the front face of `α` has Čech degree `r`, its coefficient is
`cupProductSign n p r = (-1)^((p+r)n+rp+r)`. -/
@[stacks 07MB]
noncomputable def cechCupProduct
    (F : CochainComplex (ZPresheaf.{u, max u v w} X) ℤ)
    (G : CochainComplex (ZPresheaf.{u, max u v w'} X) ℤ) :
    HomologicalComplex.mapBifunctor ((totalCechComplexFunctor.{u, v, max u w} X U).obj F)
        ((totalCechComplexFunctor.{u, v, max u w'} X U).obj G)
        (tensorModules.{max u v w, max u v w'} ℤ) (up ℤ) ⟶
      (totalCechComplexFunctor.{u, v, max u w w'} X U).obj
        (tensorSheafComplex.{u, max v w, max v w'} X F G) where
  f := cechCupProductDegree.{u, v, w, w'} X U F G
  comm' n n' hnn' := by
    obtain rfl : n + 1 = n' := by simpa [ComplexShape.up] using hnn'
    exact cechCupProductDegree_comm.{u, v, w, w'} X U F G n

/-- On homogeneous summands the cup product is the front/back restriction formula with
the sign `(-1)^((p+r)n+rp+r)`. -/
@[stacks 07MB "the signed Alexander--Whitney formula"]
theorem cechCupProduct_ι (F : CochainComplex (ZPresheaf.{u, max u v w} X) ℤ)
    (G : CochainComplex (ZPresheaf.{u, max u v w'} X) ℤ) (r s : ℕ) (a b : ℤ) :
    tensorModulesMap ℤ (ιTotalCech.{u, v, max u w} X U F r a)
      (ιTotalCech.{u, v, max u w'} X U G s b) ≫
        HomologicalComplex.ιMapBifunctor ((totalCechComplexFunctor.{u, v, max u w} X U).obj F)
          ((totalCechComplexFunctor.{u, v, max u w'} X U).obj G)
          (tensorModules.{max u v w, max u v w'} ℤ)
          (up ℤ) (r + a) (s + b) ((r + a) + (s + b)) rfl ≫
        (cechCupProduct.{u, v, w, w'} X U F G).f ((r + a) + (s + b)) =
      cupProductSign (r + a) (r + s) r •
        (cechAlexanderWhitney.{u, v, max u w, max u w'} X U (F.X a) (G.X b) r s ≫
          cechCochainsMap.{u, v, max u w w'} X U
            (ιTensorSheafComplex.{u, max v w, max v w'} X F G a b) (r + s) ≫
          ιTotalCech.{u, v, max u w w'} X U
            (tensorSheafComplex.{u, max v w, max v w'} X F G) (r + s) (a + b) ≫
          eqToHom (congrArg
            (((totalCechComplexFunctor.{u, v, max u w w'} X U).obj
              (tensorSheafComplex.{u, max v w, max v w'} X F G)).X)
            (by push_cast; ring))) := by
  change tensorCechι.{u, v, max u w, max u w'} X U F G r s a b _ rfl ≫
    cechCupProductDegree.{u, v, w, w'} X U F G _ = _
  rw [tensorCechι_cechCupProductDegree]
  rfl

end Stacks.Cech.CupProduct
