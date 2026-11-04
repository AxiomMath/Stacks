module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightTExactness
public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensor
import StacksCore.Tactic.StacksAttribute

/-!
# Degree-zero bookkeeping for the derived tensor product

A map out of an object of `D^{≤ 0}` into a module placed in degree zero is determined by what
it does on `H⁰`; in particular it vanishes as soon as its effect on `H⁰` does. For two modules
placed in degree zero and a K-flat left factor, the derived tensor product has `H⁰` the
ordinary tensor product of the two modules. Together these say that a map
`I ⊗^L_O G ⟶ G'[0]` out of a derived tensor product of two modules is zero as soon as the
induced map `I ⊗_O G ⟶ G'` is.

## Main definitions

* `Stacks.SheafOfModules.DerivedTensorProduct.tensorSingleIso`: `I[0] ⊗^L_O G[0]` is
  `(I ⊗_O G)[0]` when `I[0]` is K-flat.
* `Stacks.SheafOfModules.DerivedTensorProduct.homologyTensorSingleIso`: the same comparison
  read on `H⁰`.

## Main results

* `Stacks.DerivedCategory.eq_zero_of_homologyMap_eq_zero_of_isLE`: a map from an object of
  `D^{≤ 0}` to a module in degree zero which is zero on `H⁰` is zero.
* `Stacks.DerivedCategory.homologyMap_injective_of_isLE`: two such maps agreeing on `H⁰` are
  equal.
* `Stacks.SheafOfModules.DerivedTensorProduct.isLE_tensor_single`: `I[0] ⊗^L_O G[0]` lies in
  `D^{≤ 0}`.
* `Stacks.SheafOfModules.DerivedTensorProduct.eq_zero_iff_homologyTensorSingleIso_inv_comp_eq_zero`
  : a map `I[0] ⊗^L_O G[0] ⟶ G'[0]` is zero exactly when the map it induces from `I ⊗_O G` is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

universe w v u d

namespace Stacks.DerivedCategory

open _root_.DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- `H⁰` is faithful on the heart of the canonical t-structure, in the special case of a map
into a module placed in degree zero: if it vanishes on `H⁰` it vanishes. -/
theorem eq_zero_of_homologyMap_eq_zero_of_isGE {E : _root_.DerivedCategory A} [E.IsLE 0]
    [E.IsGE 0] {G : A} (f : E ⟶ (singleFunctor A 0).obj G)
    (hf : (homologyFunctor A 0).map f = 0) : f = 0 := by
  obtain ⟨B, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE E 0
  obtain ⟨f₀, hf₀⟩ := (singleFunctor A 0).map_surjective (e.inv ≫ f)
  have key := NatIso.naturality_1 (singleFunctorCompHomologyFunctorIso A 0) f₀
  dsimp at key
  rw [hf₀, Functor.map_comp, hf, comp_zero, zero_comp, comp_zero] at key
  rw [← cancel_epi e.inv, ← hf₀, ← key, Functor.map_zero, comp_zero]

/-- The truncation `E ⟶ τ^{≥ 0} E` is an isomorphism on `H⁰`. -/
theorem isIso_homologyMap_truncGEπ_app (E : _root_.DerivedCategory A) :
    IsIso ((homologyFunctor A 0).map ((TStructure.t.truncGEπ (0 : ℤ)).app E)) := by
  have hT : (TStructure.t.triangleLTGE (0 : ℤ)).obj E ∈ distinguishedTriangles :=
    TStructure.triangleLTGE_distinguished _ 0 E
  have h₁ : (homologyFunctor A 0).map ((TStructure.t.triangleLTGE (0 : ℤ)).obj E).mor₁ = 0 :=
    (isZero_of_isLE ((TStructure.t.truncLT (0 : ℤ)).obj E) (0 - 1) 0 (by norm_num)).eq_of_src _ _
  have h₂ : HomologySequence.δ ((TStructure.t.triangleLTGE (0 : ℤ)).obj E) 0 1 rfl = 0 :=
    (isZero_of_isLE ((TStructure.t.truncLT (0 : ℤ)).obj E) (0 - 1) 1 (by norm_num)).eq_of_tgt _ _
  have _ : Mono ((homologyFunctor A 0).map ((TStructure.t.truncGEπ (0 : ℤ)).app E)) :=
    (HomologySequence.mono_homologyMap_mor₂_iff _ hT 0).2 h₁
  have _ : Epi ((homologyFunctor A 0).map ((TStructure.t.truncGEπ (0 : ℤ)).app E)) :=
    (HomologySequence.epi_homologyMap_mor₂_iff _ hT 0 1 rfl).2 h₂
  exact isIso_of_mono_of_epi _

/-- A map out of `D^{≤ 0}` into a module placed in degree zero is zero as soon as it is zero on
`H⁰`. -/
theorem eq_zero_of_homologyMap_eq_zero_of_isLE {E : _root_.DerivedCategory A} (hE : E.IsLE 0)
    {G : A} (f : E ⟶ (singleFunctor A 0).obj G)
    (hf : (homologyFunctor A 0).map f = 0) : f = 0 := by
  have hfac : (TStructure.t.truncGEπ 0).app E ≫ TStructure.t.descTruncGE f 0 = f :=
    TStructure.t.π_descTruncGE f 0
  have _ := isIso_homologyMap_truncGEπ_app E
  have h : (homologyFunctor A 0).map (TStructure.t.descTruncGE f 0) = 0 := by
    rw [← cancel_epi ((homologyFunctor A 0).map ((TStructure.t.truncGEπ 0).app E)),
      ← Functor.map_comp, hfac, hf, comp_zero]
  rw [← hfac, eq_zero_of_homologyMap_eq_zero_of_isGE _ h, comp_zero]

/-- A map out of `D^{≤ 0}` into a module placed in degree zero is determined by `H⁰`. -/
theorem homologyMap_injective_of_isLE {E : _root_.DerivedCategory A} (hE : E.IsLE 0) {G : A}
    (f g : E ⟶ (singleFunctor A 0).obj G)
    (h : (homologyFunctor A 0).map f = (homologyFunctor A 0).map g) : f = g := by
  rw [← sub_eq_zero]
  exact eq_zero_of_homologyMap_eq_zero_of_isLE hE _ (by rw [Functor.map_sub, h, sub_self])

end Stacks.DerivedCategory

namespace Stacks.SheafOfModules.DerivedTensorProduct

open AlgebraicGeometry

variable {X : RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- The derived tensor product of two modules placed in degree zero is their ordinary tensor
product placed in degree zero, provided the left factor placed in degree zero is K-flat. -/
def tensorSingleIso (T : DerivedTensorProduct.{u, v, w, d} X)
    (I G : RingedSite.Modules.{u, v, w} X)
    (hI : IsKFlat X.O ((CochainComplex.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj I)) :
    (T.tensor.obj ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj I)).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj G) ≅
      (DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj I).obj G) :=
  T.comparisonLeft _ _ hI ≪≫
    DerivedCategory.Q.mapIso
      (HomologicalComplex.mapBifunctorSingleIso
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) I G)

/-- `H⁰` of the derived tensor product of two modules placed in degree zero is their ordinary
tensor product, provided the left factor placed in degree zero is K-flat. -/
def homologyTensorSingleIso (T : DerivedTensorProduct.{u, v, w, d} X)
    (I G : RingedSite.Modules.{u, v, w} X)
    (hI : IsKFlat X.O ((CochainComplex.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj I)) :
    (DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) 0).obj
        ((T.tensor.obj
            ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj I)).obj
          ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj G)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj I).obj G :=
  (DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) 0).mapIso
      (T.tensorSingleIso I G hI) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (RingedSite.Modules.{u, v, w} X) 0).app _

section Vanishing

variable {Y : RingedSite.{u, u, u}}
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} Y)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} Y) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- The derived tensor product of two modules placed in degree zero lies in `D^{≤ 0}`. -/
theorem isLE_tensor_single (T : DerivedTensorProduct.{u, u, u, d} Y)
    (I G : RingedSite.Modules.{u, u, u} Y) :
    ((T.tensor.obj ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} Y) 0).obj I)).obj
      ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} Y) 0).obj G)).IsLE 0 := by
  have h := isLE_tensor T
    ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} Y) 0).obj I)
    ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} Y) 0).obj G) 0 0
  rwa [zero_add] at h

/-- A map from the derived tensor product of two modules placed in degree zero to a module placed
in degree zero vanishes exactly when the induced map on the ordinary tensor product does, provided
the left factor placed in degree zero is K-flat. -/
theorem eq_zero_iff_homologyTensorSingleIso_inv_comp_eq_zero
    (T : DerivedTensorProduct.{u, u, u, d} Y) (I G G' : RingedSite.Modules.{u, u, u} Y)
    (hI : IsKFlat Y.O ((CochainComplex.singleFunctor (RingedSite.Modules.{u, u, u} Y) 0).obj I))
    (f : (T.tensor.obj
          ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} Y) 0).obj I)).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} Y) 0).obj G) ⟶
      (DerivedCategory.singleFunctor (RingedSite.Modules.{u, u, u} Y) 0).obj G') :
    f = 0 ↔ (T.homologyTensorSingleIso I G hI).inv ≫
      (DerivedCategory.homologyFunctor (RingedSite.Modules.{u, u, u} Y) 0).map f = 0 := by
  refine ⟨fun hf ↦ by rw [hf, Functor.map_zero, comp_zero], fun hf ↦
    Stacks.DerivedCategory.eq_zero_of_homologyMap_eq_zero_of_isLE (isLE_tensor_single T I G) f ?_⟩
  rwa [← cancel_epi (T.homologyTensorSingleIso I G hI).inv, comp_zero]

end Vanishing

end Stacks.SheafOfModules.DerivedTensorProduct

end
