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

/-!
# Total Čech complexes and the Alexander--Whitney product

This file sets up the ingredients of the cup-product map on Čech total complexes: tensor
bifunctors of modules and of presheaves of modules with independent universes, the total Čech
complex of a complex of presheaves of `ℤ`-modules, the unsigned Alexander--Whitney product of
Čech cochains together with its Leibniz rule, and the description of the total Čech complex in
each degree as a coproduct of Čech cochain modules.

## Main definitions

* `Stacks.Cech.CupProduct.totalCechComplexFunctor` is the total Čech complex for presheaves of
  `ℤ`-modules.
* `Stacks.Cech.CupProduct.tensorSheafComplex` is the sheaf tensor-total complex.
* `Stacks.Cech.CupProduct.cechAlexanderWhitney` restricts to the front and back faces and tensors.
* `Stacks.Cech.CupProduct.totalCechXIsoCoproduct` identifies a degree of the total Čech complex
  with the coproduct of its summands.

## Implementation notes

Abelian groups are represented by modules over `ℤ`. The tensor bifunctors allow independent
universes for the two coefficient complexes, and the coefficient universes include those of the
space and the cover index, so that the required products and sheafification exist. The tensor
product of sheaves is the sheafification of the pointwise tensor product; since sheafification
commutes with direct sums, sheafifying the presheaf tensor-total gives the sheaf tensor-total,
whose differential is the Koszul differential of `HomologicalComplex.mapBifunctor`. The Čech
degree is the first degree of the double complex. All totalizations use direct sums, so the
constructions apply to presheaf complexes, arbitrary families of opens and unbounded complexes.

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

section Tensor

open scoped TensorProduct

variable (R : Type r) [CommRing R]

/-- Tensor product over a ring with independent module universes. -/
@[implicit_reducible]
def tensorModules : ModuleCat.{w} R ⥤ ModuleCat.{w'} R ⥤ ModuleCat.{max w w'} R :=
  Functor.curry.obj
    { obj := fun M => ModuleCat.of R (M.1 ⊗[R] M.2)
      map := fun f => ModuleCat.ofHom (TensorProduct.map f.1.hom f.2.hom)
      map_id := by intro M; ext : 1; apply TensorProduct.ext; rfl
      map_comp := by intro M N P f g; ext : 1; apply TensorProduct.ext; rfl }

/-- Tensor two module homomorphisms over the same ring. -/
def tensorModulesMap {M M' : ModuleCat.{w} R} {N N' : ModuleCat.{w'} R}
    (f : M ⟶ M') (g : N ⟶ N') :
    ((tensorModules R).obj M).obj N ⟶ ((tensorModules R).obj M').obj N' :=
  ModuleCat.ofHom (TensorProduct.map f.hom g.hom)

/-- Tensoring two composites is the composite of the tensors. -/
theorem tensorModulesMap_comp
    {M M' M'' : ModuleCat.{w} R} {N N' N'' : ModuleCat.{w'} R}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N'') :
    tensorModulesMap R f g ≫ tensorModulesMap R f' g' =
      tensorModulesMap R (f ≫ f') (g ≫ g') :=
  ModuleCat.hom_ext (TensorProduct.ext' fun _ _ => rfl)

/-- Tensoring with a module, in the first variable, preserves zero morphisms. -/
instance : (tensorModules.{w, w'} R).PreservesZeroMorphisms where
  map_zero := by
    intro M N
    apply NatTrans.ext
    funext P
    apply ModuleCat.hom_ext
    exact TensorProduct.map_zero_left _

/-- Tensoring with a module, in the second variable, preserves zero morphisms. -/
instance (M : ModuleCat.{w} R) : ((tensorModules.{w, w'} R).obj M).PreservesZeroMorphisms where
  map_zero := by
    intro N P
    apply ModuleCat.hom_ext
    exact TensorProduct.map_zero_right _

/-- Pointwise tensor product, allowing the two presheaves independent carrier universes. -/
@[implicit_reducible]
def tensorPresheaves (X : TopCat.{u}) :
    ((TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat.{w} R) ⥤
    ((TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat.{w'} R) ⥤
    ((TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat.{max w w'} R) :=
  Functor.curry.obj
    { obj := fun F =>
        { obj := fun V => ModuleCat.of R (F.1.obj V ⊗[R] F.2.obj V)
          map := fun f => ModuleCat.ofHom (TensorProduct.map (F.1.map f).hom (F.2.map f).hom)
          map_id := by intro V; simp
          map_comp := by
            intro V W T f g
            simp only [Functor.map_comp, ModuleCat.hom_comp]
            ext : 1
            exact TensorProduct.map_comp _ _ _ _ }
      map := fun f =>
        { app := fun V => ModuleCat.ofHom (TensorProduct.map (f.1.app V).hom (f.2.app V).hom)
          naturality := by
            intro V W g
            ext : 1
            change (TensorProduct.map _ _).comp (TensorProduct.map _ _) =
              (TensorProduct.map _ _).comp (TensorProduct.map _ _)
            rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
            congr 1
            · exact congrArg ModuleCat.Hom.hom (f.1.naturality g)
            · exact congrArg ModuleCat.Hom.hom (f.2.naturality g) }
      map_id := by
        intro F
        apply NatTrans.ext
        funext V
        apply ModuleCat.hom_ext
        exact TensorProduct.map_id
      map_comp := by
        intro F G H f g
        apply NatTrans.ext
        funext V
        apply ModuleCat.hom_ext
        exact TensorProduct.map_comp _ _ _ _ }

/-- The pointwise tensor product of presheaves preserves zero morphisms in the first variable. -/
instance (X : TopCat.{u}) : (tensorPresheaves.{u, w, w'} R X).PreservesZeroMorphisms where
  map_zero := by
    intro F G
    apply NatTrans.ext
    funext H
    apply NatTrans.ext
    funext V
    apply ModuleCat.hom_ext
    exact TensorProduct.map_zero_left _

/-- The pointwise tensor product of presheaves preserves zero morphisms in the second variable. -/
instance (X : TopCat.{u}) (F : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat.{w} R) :
    ((tensorPresheaves.{u, w, w'} R X).obj F).PreservesZeroMorphisms where
  map_zero := by
    intro G H
    apply NatTrans.ext
    funext V
    apply ModuleCat.hom_ext
    exact TensorProduct.map_zero_right _

end Tensor

/-- Presheaves of `ℤ`-modules on a topological space. -/
abbrev ZPresheaf (X : TopCat.{u}) :=
  (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat.{w} ℤ

/-- The forgetful functor on `ℤ`-modules preserves filtered colimits. -/
noncomputable instance : PreservesFilteredColimits (forget (ModuleCat.{w} ℤ)) :=
  Limits.comp_preservesFilteredColimits (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w})
    (forget AddCommGrpCat.{w})

/-- The forgetful functor on `ℤ`-modules in `Type w` preserves filtered colimits of size `u`
when `u ≤ w`. -/
noncomputable instance [UnivLE.{u, w}] :
    PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{w} ℤ)) :=
  preservesFilteredColimitsOfSize_of_univLE.{w, w} _

/-- Presheaves of `ℤ`-modules on a topological space have sheafifications. -/
noncomputable instance integerHasSheafify (X : TopCat.{u}) [UnivLE.{u, w}] :
    HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{w} ℤ) := by
  infer_instance

variable (X : TopCat.{u}) {ι : Type v} (U : ι → TopologicalSpace.Opens X)

/-- The Čech complex of a presheaf of `ℤ`-modules, extended from `ℕ` to `ℤ`. -/
@[implicit_reducible]
noncomputable def cechComplexFunctorInt :
    ZPresheaf.{u, max v w} X ⥤ CochainComplex (ModuleCat.{max v w} ℤ) ℤ :=
  CategoryTheory.cechComplexFunctor U ⋙
    ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{max v w} ℤ)

/-- The Čech complex functor of `ℤ`-module presheaves preserves zero morphisms. -/
instance :
    (CategoryTheory.cechComplexFunctor
      (A := ModuleCat.{max v w} ℤ) U).PreservesZeroMorphisms where
  map_zero := by
    intro A B
    apply HomologicalComplex.Hom.ext
    funext n
    change Limits.Pi.map (fun i => (0 : A.obj _ ⟶ B.obj _)) = 0
    apply Limits.Pi.hom_ext
    intro j
    rw [Limits.Pi.map_π]
    simp

/-- The integer-indexed Čech complex functor preserves zero morphisms. -/
instance : (cechComplexFunctorInt.{u, v, w} X U).PreservesZeroMorphisms := by
  constructor
  intro A B
  change (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{max v w} ℤ)).map
    ((CategoryTheory.cechComplexFunctor U).map 0) = 0
  rw [Functor.map_zero, Functor.map_zero]

/-- The total Čech complex of a complex of presheaves of `ℤ`-modules. -/
@[implicit_reducible]
noncomputable def totalCechComplexFunctor :
    CochainComplex (ZPresheaf.{u, max v w} X) ℤ ⥤ CochainComplex (ModuleCat.{max v w} ℤ) ℤ :=
  ((cechComplexFunctorInt.{u, v, w} X U).mapHomologicalComplex (up ℤ) ⋙
    HomologicalComplex₂.flipFunctor (ModuleCat.{max v w} ℤ) (up ℤ) (up ℤ)) ⋙
    HomologicalComplex₂.totalFunctor (ModuleCat.{max v w} ℤ) (up ℤ) (up ℤ) (up ℤ)


/-- The sign in the homogeneous Alexander--Whitney summand of Tag 07MB. -/
abbrev cupProductSign (n p r : ℤ) : ℤ :=
  ((p + r) * n + r * p + r).negOnePow

private theorem cupProductSign_diff_coeffF (n p r : ℤ) :
    (p + 1).negOnePow * cupProductSign n (p + 1) r =
      cupProductSign (n + 1) (p + 1) r * r.negOnePow := by
  norm_cast
  simp only [← Int.negOnePow_add]
  apply (Int.negOnePow_eq_iff _ _).2
  exact ⟨-r, by ring⟩

private theorem cupProductSign_diff_coeffG (n p r : ℤ) :
    (p + 1).negOnePow * cupProductSign n (p + 1) r * (n - r).negOnePow =
      n.negOnePow * cupProductSign n (p + 1) r * (p + 1 - r).negOnePow := by
  norm_cast
  simp only [← Int.negOnePow_add]
  apply (Int.negOnePow_eq_iff _ _).2
  exact ⟨0, by ring⟩

private theorem cupProductSign_face_boundary (n p r : ℤ) :
    cupProductSign (n + 1) (p + 1) r * r.negOnePow =
      (n + 1).negOnePow * cupProductSign n (p + 1) (r - 1) := by
  norm_cast
  simp only [← Int.negOnePow_add]
  apply (Int.negOnePow_eq_iff _ _).2
  exact ⟨1 + p + r, by ring⟩

private theorem cupProductSign_face_back (n p r j : ℤ) :
    j.negOnePow * cupProductSign n p r =
      n.negOnePow * cupProductSign n (p + 1) r * (j - r).negOnePow := by
  norm_cast
  simp only [← Int.negOnePow_add]
  apply (Int.negOnePow_eq_iff _ _).2
  exact ⟨-n, by ring⟩

private theorem cupProductSign_face_front (n p r j : ℤ) :
    j.negOnePow * cupProductSign n p (r - 1) =
      cupProductSign (n + 1) (p + 1) r * j.negOnePow := by
  norm_cast
  simp only [← Int.negOnePow_add]
  apply (Int.negOnePow_eq_iff _ _).2
  exact ⟨-1 - p - r - n, by ring⟩

/-- Sheafification of the pointwise tensor-total, equivalently the total of sheaf tensors. -/
noncomputable def tensorSheafComplex
    (F : CochainComplex (ZPresheaf.{u, max u w} X) ℤ)
    (G : CochainComplex (ZPresheaf.{u, max u w'} X) ℤ) :
    CochainComplex (ZPresheaf.{u, max u w w'} X) ℤ :=
  ((sheafification (Opens.grothendieckTopology X)
      (ModuleCat.{max u w w'} ℤ)).mapHomologicalComplex (up ℤ)).obj
    (HomologicalComplex.mapBifunctor F G (tensorPresheaves ℤ X) (up ℤ))

/-- The ordinary Čech cochains in degree `p`. -/
noncomputable abbrev cechCochains (F : ZPresheaf.{u, max v w} X) (p : ℕ) :
    ModuleCat.{max v w} ℤ :=
  ∏ᶜ fun i : Fin (p + 1) → ι => F.obj (op (∏ᶜ (U ∘ i)))

/-- The map on Čech cochains induced by a morphism of coefficient presheaves. -/
noncomputable def cechCochainsMap {F G : ZPresheaf.{u, max v w} X} (f : F ⟶ G) (p : ℕ) :
    cechCochains.{u, v, w} X U F p ⟶ cechCochains.{u, v, w} X U G p :=
  ((CategoryTheory.cechComplexFunctor U).map f).f p

theorem cechCochainsMap_comp_π {F G : ZPresheaf.{u, max v w} X}
    (f : F ⟶ G) (p : ℕ) (t : Fin (p + 1) → ι) :
    cechCochainsMap X U f p ≫
        Pi.π (fun i : Fin (p + 1) → ι => G.obj (op (∏ᶜ (U ∘ i)))) t =
      Pi.π (fun i : Fin (p + 1) → ι => F.obj (op (∏ᶜ (U ∘ i)))) t ≫
        f.app (op (∏ᶜ (U ∘ t))) := by
  simp [cechCochainsMap, CategoryTheory.cechComplexFunctor,
    Limits.FormalCoproduct.cochainComplexFunctor,
    Limits.FormalCoproduct.cosimplicialObjectFunctor,
    Limits.FormalCoproduct.cech, Limits.FormalCoproduct.mapPower,
    Limits.FormalCoproduct.power]

/-- Restrict a Čech cochain along a map of the vertices of an intersection. -/
noncomputable abbrev cechFaceRestriction (F : ZPresheaf.{u, max v w} X) {p q : ℕ}
    (θ : Fin (p + 1) → Fin (q + 1)) (t : Fin (q + 1) → ι) :
    cechCochains.{u, v, w} X U F p ⟶ F.obj (op (∏ᶜ (U ∘ t))) :=
  Pi.π (fun i : Fin (p + 1) → ι => F.obj (op (∏ᶜ (U ∘ i)))) (t ∘ θ) ≫
    F.map (Pi.lift (fun i => Pi.π (U ∘ t) (θ i))).op

private theorem cechFaceRestriction_naturality
    {F G : ZPresheaf.{u, max v w} X} (f : F ⟶ G) {p q : ℕ}
    (θ : Fin (p + 1) → Fin (q + 1)) (t : Fin (q + 1) → ι) :
    cechFaceRestriction X U F θ t ≫ f.app (op (∏ᶜ (U ∘ t))) =
      cechCochainsMap X U f p ≫ cechFaceRestriction X U G θ t := by
  simp [cechFaceRestriction, cechCochainsMap, cechCochains,
    CategoryTheory.cechComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor,
    CategoryTheory.Limits.FormalCoproduct.cech,
    CategoryTheory.Limits.FormalCoproduct.mapPower,
    CategoryTheory.Limits.FormalCoproduct.power,
    f.naturality]

private theorem cechFaceRestriction_comp
    (F : ZPresheaf.{u, max v w} X) {p q k : ℕ}
    (θ : Fin (p + 1) → Fin (q + 1)) (φ : Fin (q + 1) → Fin (k + 1))
    (t : Fin (k + 1) → ι) :
    cechFaceRestriction X U F θ (t ∘ φ) ≫
        F.map (Pi.lift (fun i => Pi.π (U ∘ t) (φ i))).op =
      cechFaceRestriction X U F (φ ∘ θ) t := by
  unfold cechFaceRestriction
  rw [Category.assoc, ← Functor.map_comp]
  congr 1

/-- The Čech differential, with its source and target named as `cechCochains`. -/
noncomputable def cechD (F : ZPresheaf.{u, max v w} X) (p : ℕ) :
    cechCochains.{u, v, w} X U F p ⟶ cechCochains.{u, v, w} X U F (p + 1) :=
  ((CategoryTheory.cechComplexFunctor U).obj F).d p (p + 1)

private theorem cechDifferential_comp_π (F : ZPresheaf.{u, max v w} X) (p : ℕ)
    (t : Fin (p + 2) → ι) :
    cechD.{u, v, w} X U F p ≫
      Pi.π (fun i : Fin (p + 2) → ι => F.obj (op (∏ᶜ (U ∘ i)))) t =
    ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
      cechFaceRestriction X U F (fun i => j.succAbove i) t := by
  simp only [cechD, cechComplexFunctor, FormalCoproduct.cochainComplexFunctor,
    FormalCoproduct.cech, FormalCoproduct.power, OrderHom.toFun_eq_coe,
    FormalCoproduct.mapPower, FormalCoproduct.cosimplicialObjectFunctor,
    AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.map,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, Functor.comp_obj,
    Functor.whiskeringLeft_obj_obj, Functor.rightOp_obj, CochainComplex.of_d,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD, Int.reduceNeg,
    Preadditive.sum_comp, Linear.smul_comp, cechFaceRestriction, Function.comp_apply]
  apply Fintype.sum_congr
  intro j
  congr 1
  apply ModuleCat.hom_ext
  ext x
  have hfun : (j.succAboveOrderEmb.toOrderHom : Fin (p + 1) → Fin (p + 2)) =
      fun i => j.succAbove i := by
    funext i
    exact Fin.succAboveOrderEmb_apply j i
  simp [CosimplicialObject.δ, SimplexCategory.δ]
  cases hfun
  rfl

private theorem cechDifferential_comp_restriction
    (F : ZPresheaf.{u, max v w} X) (p : ℕ) {q : ℕ}
    (θ : Fin (p + 2) → Fin (q + 1)) (t : Fin (q + 1) → ι) :
    cechD.{u, v, w} X U F p ≫
      cechFaceRestriction X U F θ t =
    ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
      cechFaceRestriction X U F (θ ∘ j.succAbove) t := by
  unfold cechFaceRestriction
  rw [← Category.assoc, cechDifferential_comp_π]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact cechFaceRestriction_comp X U F _ θ t

/-- The unsigned Alexander--Whitney product of Čech cochains: tensor the restrictions
from the front `r + 1` vertices and the back `s + 1` vertices. -/
noncomputable def cechAlexanderWhitney
    (F : ZPresheaf.{u, max v w} X) (G : ZPresheaf.{u, max v w'} X) (r s : ℕ) :
    ((tensorModules.{max v w, max v w'} ℤ).obj (cechCochains.{u, v, w} X U F r)).obj
        (cechCochains.{u, v, w'} X U G s) ⟶
      cechCochains.{u, v, max w w'} X U (((tensorPresheaves ℤ X).obj F).obj G) (r + s) :=
  Pi.lift (fun t : Fin (r + s + 1) → ι =>
    tensorModulesMap ℤ
      (cechFaceRestriction.{u, v, w} X U F (p := r) (q := r + s)
        (fun i => ⟨i.val, by omega⟩) t)
      (cechFaceRestriction.{u, v, w'} X U G (p := s) (q := r + s)
        (fun i => ⟨r + i.val, by omega⟩) t))

private theorem cechAlexanderWhitney_comp_π
    (F : ZPresheaf.{u, max v w} X) (G : ZPresheaf.{u, max v w'} X)
    (r s : ℕ) (t : Fin (r + s + 1) → ι) :
    cechAlexanderWhitney.{u, v, w, w'} X U F G r s ≫
      Pi.π (fun i : Fin (r + s + 1) → ι =>
        ((tensorPresheaves ℤ X).obj F).obj G |>.obj (op (∏ᶜ (U ∘ i)))) t =
      tensorModulesMap ℤ
        (cechFaceRestriction X U F (fun i => ⟨i.val, by omega⟩) t)
        (cechFaceRestriction X U G (fun i => ⟨r + i.val, by omega⟩) t) := by
  rw [cechAlexanderWhitney, Pi.lift_comp_π]

private theorem cechAlexanderWhitney_comp_restriction
    (F : ZPresheaf.{u, max v w} X) (G : ZPresheaf.{u, max v w'} X)
    (r s : ℕ) {q : ℕ} (θ : Fin (r + s + 1) → Fin (q + 1))
    (t : Fin (q + 1) → ι) :
    cechAlexanderWhitney.{u, v, w, w'} X U F G r s ≫
      cechFaceRestriction.{u, v, max w w'} X U (((tensorPresheaves ℤ X).obj F).obj G) θ t =
    tensorModulesMap ℤ
      (cechFaceRestriction X U F (fun i => θ ⟨i.val, by omega⟩) t)
      (cechFaceRestriction X U G (fun i => θ ⟨r + i.val, by omega⟩) t) := by
  unfold cechFaceRestriction
  rw [← Category.assoc, cechAlexanderWhitney_comp_π]
  show tensorModulesMap ℤ _ _ ≫ tensorModulesMap ℤ _ _ = _
  rw [tensorModulesMap_comp]
  congr 1 <;> exact cechFaceRestriction_comp X U _ _ θ t

noncomputable def cechAlexanderWhitneyTo
    (F : ZPresheaf.{u, max v w} X) (G : ZPresheaf.{u, max v w'} X)
    (r s q : ℕ) (h : r + s = q) :
    ((tensorModules ℤ).obj (cechCochains X U F r)).obj (cechCochains X U G s) ⟶
      cechCochains.{u, v, max w w'} X U (((tensorPresheaves ℤ X).obj F).obj G) q :=
  Pi.lift (fun t : Fin (q + 1) → ι => tensorModulesMap ℤ
    (cechFaceRestriction X U F (fun i => ⟨i.val, by omega⟩) t)
    (cechFaceRestriction X U G (fun i => ⟨r + i.val, by omega⟩) t))

private theorem cechAlexanderWhitneyTo_eq
    (F : ZPresheaf.{u, max v w} X) (G : ZPresheaf.{u, max v w'} X)
    (r s q : ℕ) (h : r + s = q) :
    cechAlexanderWhitneyTo.{u, v, w, w'} X U F G r s q h =
      cechAlexanderWhitney.{u, v, w, w'} X U F G r s ≫ eqToHom (congrArg
        (cechCochains.{u, v, max w w'} X U (((tensorPresheaves ℤ X).obj F).obj G)) h) := by
  subst q
  simp only [eqToHom_refl, Category.comp_id]
  rfl

private theorem cechAlexanderWhitneyTo_comp_π
    (F : ZPresheaf.{u, max v w} X) (G : ZPresheaf.{u, max v w'} X)
    (r s q : ℕ) (h : r + s = q) (t : Fin (q + 1) → ι) :
    cechAlexanderWhitneyTo.{u, v, w, w'} X U F G r s q h ≫
      Pi.π (fun i : Fin (q + 1) → ι =>
        ((tensorPresheaves ℤ X).obj F).obj G |>.obj (op (∏ᶜ (U ∘ i)))) t =
    tensorModulesMap ℤ
      (cechFaceRestriction X U F (fun i => ⟨i.val, by omega⟩) t)
      (cechFaceRestriction X U G (fun i => ⟨r + i.val, by omega⟩) t) := by
  exact Pi.lift_comp_π _ t

/-- Tensoring in the first variable is additive. -/
private def tensorModulesMapAddLeft {M M' : ModuleCat.{w} ℤ} {N N' : ModuleCat.{w'} ℤ}
    (g : N ⟶ N') :
    (M ⟶ M') →+ (((tensorModules ℤ).obj M).obj N ⟶ ((tensorModules ℤ).obj M').obj N') where
  toFun f := tensorModulesMap ℤ f g
  map_zero' := ModuleCat.hom_ext (TensorProduct.map_zero_left _)
  map_add' _ _ := ModuleCat.hom_ext (TensorProduct.map_add_left _ _ _)

/-- Tensoring in the second variable is additive. -/
private def tensorModulesMapAddRight {M M' : ModuleCat.{w} ℤ} {N N' : ModuleCat.{w'} ℤ}
    (f : M ⟶ M') :
    (N ⟶ N') →+ (((tensorModules ℤ).obj M).obj N ⟶ ((tensorModules ℤ).obj M').obj N') where
  toFun g := tensorModulesMap ℤ f g
  map_zero' := ModuleCat.hom_ext (TensorProduct.map_zero_right _)
  map_add' _ _ := ModuleCat.hom_ext (TensorProduct.map_add_right _ _ _)

private theorem tensorModulesMap_sum_left
    {M M' : ModuleCat.{w} ℤ} {N N' : ModuleCat.{w'} ℤ}
    {I : Type*} (S : Finset I) (f : I → (M ⟶ M')) (g : N ⟶ N') :
    tensorModulesMap ℤ (∑ i ∈ S, f i) g = ∑ i ∈ S, tensorModulesMap ℤ (f i) g :=
  map_sum (tensorModulesMapAddLeft g) f S

private theorem tensorModulesMap_sum_right
    {M M' : ModuleCat.{w} ℤ} {N N' : ModuleCat.{w'} ℤ}
    {I : Type*} (S : Finset I) (f : M ⟶ M') (g : I → (N ⟶ N')) :
    tensorModulesMap ℤ f (∑ i ∈ S, g i) = ∑ i ∈ S, tensorModulesMap ℤ f (g i) :=
  map_sum (tensorModulesMapAddRight f) g S

theorem tensorModulesMap_smul_left
    {M M' : ModuleCat.{w} ℤ} {N N' : ModuleCat.{w'} ℤ}
    (z : ℤ) (f : M ⟶ M') (g : N ⟶ N') :
    tensorModulesMap ℤ (z • f) g = z • tensorModulesMap ℤ f g :=
  map_zsmul (tensorModulesMapAddLeft g) z f

theorem tensorModulesMap_smul_right
    {M M' : ModuleCat.{w} ℤ} {N N' : ModuleCat.{w'} ℤ}
    (z : ℤ) (f : M ⟶ M') (g : N ⟶ N') :
    tensorModulesMap ℤ f (z • g) = z • tensorModulesMap ℤ f g :=
  map_zsmul (tensorModulesMapAddRight f) z g

/-- A sum over `Fin (r + s + 2)` splits as a front sum over `Fin (r + 2)` plus a signed back
sum over `Fin (s + 2)`, when the two overlapping boundary terms cancel. -/
theorem sum_front_back {A : Type*} [AddCommGroup A]
    (r s : ℕ) (L : Fin (r + s + 2) → A) (F : Fin (r + 2) → A)
    (G : Fin (s + 2) → A) (z : ℤ)
    (hF : ∀ i : Fin (r + 1), L ⟨i.val, by omega⟩ = F i.castSucc)
    (hG : ∀ i : Fin (s + 1), L ⟨r + 1 + i.val, by omega⟩ = z • G i.succ)
    (h : F (Fin.last (r + 1)) + z • G 0 = 0) :
    ∑ i, L i = (∑ i, F i) + z • ∑ i, G i := by
  have hsum := Fin.sum_univ_add (a := r + 1) (b := s + 1)
    (fun i => L ((finCongr (show (r + 1) + (s + 1) = r + s + 2 by omega)) i))
  rw [Equiv.sum_comp] at hsum
  change (∑ i, L i) = (∑ i : Fin (r + 1), L ⟨i.val, _⟩) +
    ∑ i : Fin (s + 1), L ⟨r + 1 + i.val, _⟩ at hsum
  simp only [hF, hG, ← Finset.smul_sum] at hsum
  rw [hsum, Fin.sum_univ_castSucc F, Fin.sum_univ_succ G, smul_add]
  calc
    _ = (∑ i : Fin (r + 1), F i.castSucc) +
        (F (Fin.last (r + 1)) + z • G 0) + z • ∑ i : Fin (s + 1), G i.succ := by rw [h]; simp
    _ = _ := by abel

theorem cechAlexanderWhitney_naturality
    {F F' : ZPresheaf.{u, max v w} X} {G G' : ZPresheaf.{u, max v w'} X}
    (f : F ⟶ F') (g : G ⟶ G') (r s : ℕ) :
    cechAlexanderWhitney.{u, v, w, w'} X U F G r s ≫
      cechCochainsMap.{u, v, max w w'} X U
        (((tensorPresheaves ℤ X).map f).app G ≫ ((tensorPresheaves ℤ X).obj F').map g) (r + s) =
    tensorModulesMap ℤ (cechCochainsMap X U f r) (cechCochainsMap X U g s) ≫
      cechAlexanderWhitney.{u, v, w, w'} X U F' G' r s := by
  apply Pi.hom_ext (f := fun t : Fin (r + s + 1) → ι =>
    (((tensorPresheaves ℤ X).obj F').obj G').obj (op (∏ᶜ (U ∘ t))))
  intro t
  simp only [Category.assoc, cechCochainsMap_comp_π,
    cechAlexanderWhitney_comp_π]
  rw [← Category.assoc, cechAlexanderWhitney_comp_π]
  show tensorModulesMap ℤ _ _ ≫
    (tensorModulesMap ℤ (f.app _) (𝟙 _) ≫ tensorModulesMap ℤ (𝟙 _) (g.app _)) = _
  rw [tensorModulesMap_comp, Category.comp_id, Category.id_comp, tensorModulesMap_comp,
    cechFaceRestriction_naturality, cechFaceRestriction_naturality]
  exact (tensorModulesMap_comp ℤ _ _ _ _).symm

theorem cechAlexanderWhitney_d
    (F : ZPresheaf.{u, max v w} X) (G : ZPresheaf.{u, max v w'} X)
    (r s : ℕ) :
    cechAlexanderWhitney.{u, v, w, w'} X U F G r s ≫
      cechD.{u, v, max w w'} X U (((tensorPresheaves ℤ X).obj F).obj G) (r + s) =
    tensorModulesMap.{max v w, max v w', 0} ℤ (cechD.{u, v, w} X U F r) (𝟙 _) ≫
      cechAlexanderWhitneyTo.{u, v, w, w'} X U F G (r + 1) s (r + s + 1) (by omega) +
    (-1 : ℤ)^r • (tensorModulesMap.{max v w, max v w', 0} ℤ (𝟙 _)
      (cechD.{u, v, w'} X U G s) ≫
      cechAlexanderWhitneyTo.{u, v, w, w'} X U F G r (s + 1) (r + s + 1) (by omega)) := by
  apply Pi.hom_ext (f := fun t : Fin (r + s + 2) → ι =>
    (((tensorPresheaves ℤ X).obj F).obj G).obj (op (∏ᶜ (U ∘ t))))
  intro t
  simp only [Category.assoc, cechDifferential_comp_π, Preadditive.comp_sum,
    Preadditive.comp_zsmul, cechAlexanderWhitney_comp_restriction,
    Preadditive.add_comp, Preadditive.zsmul_comp,
    cechAlexanderWhitneyTo_comp_π, tensorModulesMap_comp, Category.id_comp,
    cechDifferential_comp_restriction, tensorModulesMap_sum_left,
    tensorModulesMap_sum_right, tensorModulesMap_smul_left, tensorModulesMap_smul_right]
  apply sum_front_back r s
  · intro i
    congr 2
    · congr 1
      funext j
      apply Fin.ext
      simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Function.comp_apply]
      split_ifs <;> simp_all
    · congr 1
      funext j
      apply Fin.ext
      simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
      split_ifs <;> simp_all <;> omega
  · intro i
    rw [← mul_smul, ← pow_add]
    congr 2
    · dsimp
      omega
    · congr 1
      funext j
      apply Fin.ext
      simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
      split_ifs <;> simp_all
      omega
    · congr 1
      funext j
      apply Fin.ext
      simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ,
        Function.comp_apply]
      split_ifs <;> simp_all <;> omega
  · simp only [Fin.succAbove_last, Fin.succAbove_zero, Function.comp_def,
      Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero, pow_zero, one_smul,
      pow_succ, mul_smul, neg_one_smul]
    have he : (fun j : Fin (s + 1) => (⟨r + (j.val + 1), by omega⟩ : Fin (r + s + 2))) =
        (fun j => (⟨r + 1 + j.val, by omega⟩ : Fin (r + s + 2))) := by
      funext j; apply Fin.ext; dsimp; omega
    simp only [he, smul_neg, neg_add_cancel]

/-- The degree-`p'` piece of the integer-indexed Čech complex, identified with the Čech
cochains of degree `p`. -/
noncomputable def cechExtendXIso (F : ZPresheaf.{u, max v w} X) (p : ℕ) {p' : ℤ}
    (h : (p : ℤ) = p') :
    (((CategoryTheory.cechComplexFunctor U).obj F).extend embeddingUpNat).X p' ≅
      cechCochains.{u, v, w} X U F p :=
  ((CategoryTheory.cechComplexFunctor U).obj F).extendXIso embeddingUpNat h

/-- Inclusion of Čech degree `p` and coefficient degree `a` in the total complex. -/
noncomputable def ιTotalCech (F : CochainComplex (ZPresheaf.{u, max v w} X) ℤ) (p : ℕ) (a : ℤ) :
    cechCochains.{u, v, w} X U (F.X a) p ⟶
      ((totalCechComplexFunctor.{u, v, w} X U).obj F).X (p + a) :=
  (cechExtendXIso.{u, v, w} X U (F.X a) p rfl).inv ≫
    (HomologicalComplex₂.flip
      (((cechComplexFunctorInt.{u, v, w} X U).mapHomologicalComplex (up ℤ)).obj F)).ιTotal
      (up ℤ) p a (p + a) rfl


/-- The pairs of a Čech degree and a coefficient degree with sum `n`. -/
abbrev totalCechIndex (n : ℤ) := {pa : ℕ × ℤ // (pa.1 : ℤ) + pa.2 = n}

/-- The summand of the total Čech complex in degree `n` indexed by such a pair. -/
noncomputable abbrev totalCechSummand
    (F : CochainComplex (ZPresheaf.{u, max v w} X) ℤ) (n : ℤ)
    (pa : totalCechIndex n) :=
  cechCochains.{u, v, w} X U (F.X pa.1.2) pa.1.1

/-- The Čech double complex of a complex of presheaves, Čech degree first. -/
noncomputable abbrev totalCechBicomplex
    (F : CochainComplex (ZPresheaf.{u, max v w} X) ℤ) :=
  HomologicalComplex₂.flip
    (((cechComplexFunctorInt.{u, v, w} X U).mapHomologicalComplex (up ℤ)).obj F)

/-- A morphism out of the degree-`n` total Čech complex, given on each summand. -/
noncomputable def totalCechDesc
    (F : CochainComplex (ZPresheaf.{u, max v w} X) ℤ) {n : ℤ}
    {A : ModuleCat.{max v w} ℤ}
    (f : ∀ (p : ℕ) (a : ℤ), (p : ℤ) + a = n → (cechCochains X U (F.X a) p ⟶ A)) :
    ((totalCechComplexFunctor X U).obj F).X n ⟶ A :=
  (totalCechBicomplex X U F).totalDesc (fun p a h =>
    match p with
    | .ofNat p => (cechExtendXIso.{u, v, w} X U (F.X a) p rfl).hom ≫ f p a h
    | .negSucc _ => 0)

private theorem ιTotalCech_desc
    (F : CochainComplex (ZPresheaf.{u, max v w} X) ℤ) {n : ℤ}
    {A : ModuleCat.{max v w} ℤ}
    (f : ∀ (p : ℕ) (a : ℤ), (p : ℤ) + a = n → (cechCochains X U (F.X a) p ⟶ A))
    (p : ℕ) (a : ℤ) (h : (p : ℤ) + a = n) :
    ιTotalCech X U F p a ≫ eqToHom (congrArg
      (((totalCechComplexFunctor X U).obj F).X) h) ≫ totalCechDesc X U F f = f p a h := by
  subst n
  simp only [eqToHom_refl, Category.id_comp, ιTotalCech, totalCechDesc, totalCechBicomplex,
    Category.assoc, HomologicalComplex₂.ι_totalDesc, Iso.inv_hom_id_assoc]

private theorem totalCech_hom_ext
    (F : CochainComplex (ZPresheaf.{u, max v w} X) ℤ) {n : ℤ}
    {A : ModuleCat.{max v w} ℤ}
    {f g : ((totalCechComplexFunctor X U).obj F).X n ⟶ A}
    (h : ∀ (p : ℕ) (a : ℤ) (hpa : (p : ℤ) + a = n),
      ιTotalCech X U F p a ≫ eqToHom (congrArg
        (((totalCechComplexFunctor X U).obj F).X) hpa) ≫ f =
      ιTotalCech X U F p a ≫ eqToHom (congrArg
        (((totalCechComplexFunctor X U).obj F).X) hpa) ≫ g) : f = g := by
  apply HomologicalComplex₂.total.hom_ext (up ℤ) (K := totalCechBicomplex X U F)
  intro p a hpa
  cases p with
  | ofNat p =>
    subst n
    apply (cancel_epi (cechExtendXIso.{u, v, w} X U (F.X a) p rfl).inv).mp
    have hh := h p a rfl
    simp only [ιTotalCech, eqToHom_refl, Category.id_comp] at hh
    exact ((Category.assoc _ _ _).symm.trans hh).trans (Category.assoc _ _ _)
  | negSucc p =>
    exact (((CategoryTheory.cechComplexFunctor U).obj (F.X a)).isZero_extend_X
      embeddingUpNat (Int.negSucc p) (by intro i; change (i : ℤ) ≠ _; omega)).eq_of_src _ _

/-- The degree-`n` total Čech complex is the coproduct of its summands. -/
noncomputable def totalCechXIsoCoproduct
    (F : CochainComplex (ZPresheaf.{u, max v w} X) ℤ) (n : ℤ) :
    ((totalCechComplexFunctor.{u, v, w} X U).obj F).X n ≅
      ∐ (totalCechSummand.{u, v, w} X U F n) where
  hom := totalCechDesc X U F (fun p a h => Sigma.ι (totalCechSummand X U F n) ⟨(p, a), h⟩)
  inv := Sigma.desc (fun pa => ιTotalCech X U F pa.1.1 pa.1.2 ≫
    eqToHom (congrArg (((totalCechComplexFunctor X U).obj F).X) pa.2))
  hom_inv_id := by
    apply totalCech_hom_ext
    intro p a h
    subst n
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    have hh := ιTotalCech_desc X U F
      (fun q b h => Sigma.ι (totalCechSummand X U F (p + a)) ⟨(q, b), h⟩) p a rfl
    simp only [eqToHom_refl, Category.id_comp] at hh
    rw [← Category.assoc, hh]
    simp
  inv_hom_id := by
    apply Sigma.hom_ext
    rintro ⟨⟨p, a⟩, h⟩
    simp only [Sigma.ι_desc_assoc, Category.comp_id, Category.assoc]
    exact ιTotalCech_desc X U F _ p a h

theorem ιTotalCechIsoCoproduct
    (F : CochainComplex (ZPresheaf.{u, max v w} X) ℤ) (r : ℕ) (a : ℤ) :
    ιTotalCech.{u, v, w} X U F r a ≫
      (totalCechXIsoCoproduct.{u, v, w} X U F (r + a)).hom =
    Limits.Sigma.ι (totalCechSummand.{u, v, w} X U F (r + a))
      ⟨(r, a), by push_cast; rfl⟩ := by
  show ιTotalCech X U F r a ≫ totalCechDesc X U F _ = _
  have h := ιTotalCech_desc X U F
    (fun p b h => Sigma.ι (totalCechSummand X U F (r + a)) ⟨(p, b), h⟩) r a rfl
  simp only [eqToHom_refl, Category.id_comp] at h
  exact h

/-- The degree-`n` total Čech complex is the direct sum of its summands. -/
noncomputable abbrev totalCechXIsoDirectSum
    (F : CochainComplex (ZPresheaf.{u, max v w} X) ℤ) (n : ℤ) :=
  totalCechXIsoCoproduct.{u, v, w} X U F n ≪≫
    ModuleCat.coprodIsoDirectSum (totalCechSummand.{u, v, w} X U F n)

end Stacks.Cech.CupProduct
