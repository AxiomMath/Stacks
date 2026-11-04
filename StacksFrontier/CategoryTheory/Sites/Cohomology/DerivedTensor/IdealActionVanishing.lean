module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Interface
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheaf
public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensor
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
import StacksCore.Tactic.StacksAttribute

/-!
# Tensoring a module killed by a sheaf of ideals with the inclusion of that ideal

Let `(C, O)` be a ringed site, `I ⊆ O` a sheaf of ideals and `G` a sheaf of `O`-modules killed
by `I`. Then the map

`I[0] ⊗^L_O G[0] ⟶ O[0] ⊗^L_O G[0]`

induced in the first variable by the inclusion `I ⟶ O` is zero. Consequently `G[0]` is a retract
of `(O/I)[0] ⊗^L_O G[0]`.

## Main definitions

* `Stacks.SheafOfModules.unitSheafTensorNatIso`: `O ⊗_O - ≅ id`, the left unit law for the tensor
  product of sheaves of modules.
* `Stacks.SheafOfModules.DerivedTensorProduct.unitTensorSingleIso`: `O[0] ⊗^L_O G[0] ≅ G[0]`.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.tensor_map_single_app_single_eq_zero`: the derived
  tensor product of a map of modules with a module placed in degree zero vanishes as soon as the
  ordinary tensor product of that map with the module does, provided the target of the map placed
  in degree zero is K-flat.
* `Stacks.SheafOfModules.DerivedTensorProduct.isSplitMono_tensor_map_single_g`: a short exact
  sequence whose first map dies after derived tensoring with a module placed in degree zero has
  a split monomorphism as its second map.
* `Stacks.Sites.tensor_map_single_idealι_app_single_eq_zero`: the map
  `I[0] ⊗^L_O G[0] ⟶ O[0] ⊗^L_O G[0]` induced by the inclusion of a sheaf of ideals vanishes on a
  module killed by that ideal.
* `Stacks.Sites.isSplitMono_unitTensorSingleIso_inv_comp`: `G[0]` is a retract of
  `(O/I)[0] ⊗^L_O G[0]` for a module `G` killed by `I`.

## Implementation notes

No K-flatness of `I[0]` is needed, and neither is any computation of `H⁰`. The canonical map
`toTensor` from the derived to the ordinary total tensor product is natural in both variables
with no flatness hypothesis, so the square comparing `I[0] ⊗^L_O G[0] ⟶ O[0] ⊗^L_O G[0]` with
`Tot(I[0] ⊗_O G[0]) ⟶ Tot(O[0] ⊗_O G[0])` commutes. Its right-hand vertical map is an
isomorphism because `O[0]` is K-flat (`Stacks.SheafOfModules.isKFlat_single_unit`), which is what
`toTensor_eq_comparisonLeft` asks for, so the derived map vanishes as soon as the ordinary one
does. The ordinary one is a map of total complexes whose only possibly nonzero component is the
`(0, 0)` summand in degree zero, where it is the ordinary tensor product of the given map with
`G`.

The hypothesis "`G` is killed by `I`" is therefore used only through the vanishing of the
ordinary map `I ⊗_O G ⟶ O ⊗_O G`, which is the multiplication `a ⊗ g ↦ a · g` read through the
unit isomorphism `O ⊗_O G ≅ G`; that is the form in which the hypothesis is stated.

The retract comes from the distinguished triangle of the short exact sequence
`0 → I → O → O/I → 0` tensored with `G[0]`: a distinguished triangle whose first map is zero
has a split monomorphism as its second map, by the exactness of the contravariant Hom functor
on a distinguished triangle applied to the identity of the middle vertex. The quotient `O/I` is
taken as the cokernel of the inclusion, so the sequence is `ShortComplex.cokernelSequence`. The
left unit law `O ⊗_O - ≅ id`, which identifies the source of that split monomorphism with
`G[0]`, is the right unit law `Stacks.SheafOfModules.sheafTensorUnitNatIso` composed with the
symmetry `Stacks.SheafOfModules.Tensor.sheafTensorBraiding`; it is stated with the sections
universe `max u v`, where the monoidal structure the right unit law reads off is available.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
* [Stacks Project, Tag 0FPH](https://stacks.math.columbia.edu/tag/0FPH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w d

namespace Stacks.SheafOfModules

open AlgebraicGeometry.RingedSite

variable {X : RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O)
      (ComplexShape.up ℤ)]

/-- A natural transformation vanishing at an object vanishes at every object isomorphic to it. -/
theorem app_eq_zero_of_iso {D₁ D₂ : Type*} [Category D₁] [Category D₂] [Preadditive D₂]
    {F₁ F₂ : D₁ ⥤ D₂} (α : F₁ ⟶ F₂) {Y Z : D₁} (e : Y ≅ Z) (h : α.app Z = 0) :
    α.app Y = 0 := by
  have hnat := α.naturality e.hom
  rw [h, comp_zero] at hnat
  rw [← cancel_mono (F₂.map e.hom), zero_comp]
  exact hnat.symm

/-- **The ordinary total tensor product of a map of modules with a module placed in degree zero
vanishes as soon as the ordinary tensor product does.** Both total complexes are concentrated in
degree zero, where the map is the ordinary tensor product of the given map with the module. -/
theorem mapBifunctorMap_single_eq_zero {A B G : Modules.{u, v, w} X} (f : A ⟶ B)
    (hf : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).map f).app G = 0) :
    HomologicalComplex.mapBifunctorMap
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map f)
        (𝟙 ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G))
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O) (ComplexShape.up ℤ) = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun k => ?_
  rw [HomologicalComplex.zero_f]
  refine HomologicalComplex.mapBifunctor.hom_ext fun i j hij => ?_
  rw [HomologicalComplex.ι_mapBifunctorMap, comp_zero]
  by_cases hij0 : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := hij0
    have h0 : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).map
          (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map f).f 0)).app
        (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G).X 0) = 0 := by
      rw [HomologicalComplex.single_map_f_self, CategoryTheory.Functor.map_comp,
        CategoryTheory.Functor.map_comp, NatTrans.comp_app, NatTrans.comp_app,
        app_eq_zero_of_iso ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).map f)
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G) hf,
        zero_comp, comp_zero]
    rw [h0, zero_comp]
  · exact (HomologicalComplex.isZero_obj_obj_single_obj_X
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O) A G i j
      (not_and_or.mp hij0)).eq_of_src _ _

section LeftUnit

variable {Y : RingedSite.{u, v, max u v}}
  [HasSheafify Y.J AddCommGrpCat.{max u v}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} Y.O).Additive]
  [∀ M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} Y.O).obj
      M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, v, max u v} Y) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} Y.O)
      (ComplexShape.up ℤ)]

/-- **The structure sheaf is a left unit for `⊗_O`:** `O ⊗_O F ≅ F`, naturally in the sheaf of
modules `F`. It is the right unit law read through the symmetry of the tensor product. -/
def unitSheafTensorNatIso :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} Y.O).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≅
      𝟭 (Modules.{u, v, max u v} Y) :=
  (Stacks.SheafOfModules.Tensor.sheafTensorBraiding Y.O).app
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≪≫
    sheafTensorUnitNatIso Y.O

end LeftUnit

namespace DerivedTensorProduct

variable [HasDerivedCategory.{d} (Modules.{u, v, w} X)]

/-- **The derived tensor product of a map of modules with a module placed in degree zero vanishes
as soon as the ordinary tensor product does**, provided the target of the map, placed in degree
zero, is K-flat. The canonical map to the ordinary total tensor product is natural with no
flatness hypothesis, and K-flatness of the target makes the comparison at the target an
isomorphism. -/
theorem tensor_map_single_app_single_eq_zero (T : DerivedTensorProduct.{u, v, w, d} X)
    {A B : Modules.{u, v, w} X} (f : A ⟶ B) (G : Modules.{u, v, w} X)
    (hB : IsKFlat X.O ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj B))
    (hf : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).map f).app G = 0) :
    (T.tensor.map ((DerivedCategory.singleFunctor (Modules.{u, v, w} X) 0).map f)).app
        ((DerivedCategory.singleFunctor (Modules.{u, v, w} X) 0).obj G) = 0 := by
  have hnat := T.toTensor_naturality
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map f)
    (𝟙 ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G))
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at hnat
  have hiso : IsIso (T.toTensor ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj B)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)) := by
    rw [T.toTensor_eq_comparisonLeft _ _ hB]
    infer_instance
  rw [← cancel_mono (T.toTensor ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj B)
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)), zero_comp]
  refine hnat.trans ?_
  exact (congrArg (fun z => T.toTensor
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj A)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G) ≫ z)
      ((congrArg (fun z => DerivedCategory.Q.map z)
          (mapBifunctorMap_single_eq_zero f hf)).trans
        (Functor.map_zero DerivedCategory.Q _ _))).trans comp_zero

/-- **A short exact sequence whose first map dies after derived tensoring splits off its middle
term.** Tensoring a short exact sequence of modules in the first variable with a module placed
in degree zero gives a distinguished triangle; if its first map is zero, its second map admits
a retraction. -/
theorem isSplitMono_tensor_map_single_g (T : DerivedTensorProduct.{u, v, w, d} X)
    {S : ShortComplex (Modules.{u, v, w} X)} (hS : S.ShortExact) (G : Modules.{u, v, w} X)
    (h : (T.tensor.map ((DerivedCategory.singleFunctor (Modules.{u, v, w} X) 0).map S.f)).app
        ((DerivedCategory.singleFunctor (Modules.{u, v, w} X) 0).obj G) = 0) :
    IsSplitMono ((T.tensor.map
        ((DerivedCategory.singleFunctor (Modules.{u, v, w} X) 0).map S.g)).app
      ((DerivedCategory.singleFunctor (Modules.{u, v, w} X) 0).obj G)) := by
  have hdist := (T.tensor.flip.obj
      ((DerivedCategory.singleFunctor (Modules.{u, v, w} X) 0).obj G)).map_distinguished
    _ hS.singleTriangle_distinguished
  have hmor : ((T.tensor.flip.obj
        ((DerivedCategory.singleFunctor (Modules.{u, v, w} X) 0).obj G)).mapTriangle.obj
      hS.singleTriangle).mor₁ ≫ 𝟙 _ = 0 := by
    rw [Category.comp_id]
    exact h
  obtain ⟨r, hr⟩ := Pretriangulated.Triangle.yoneda_exact₂ _ hdist (𝟙 _) hmor
  exact IsSplitMono.mk' ⟨r, hr.symm⟩

section LeftUnit

variable {Y : RingedSite.{u, v, max u v}}
  [HasSheafify Y.J AddCommGrpCat.{max u v}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasDerivedCategory.{d} (Modules.{u, v, max u v} Y)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} Y.O).Additive]
  [∀ M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} Y.O).obj
      M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, v, max u v} Y) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} Y.O)
      (ComplexShape.up ℤ)]

/-- **The structure sheaf in degree zero is a left unit for the derived tensor product**:
`O[0] ⊗^L_O G[0] ≅ G[0]`. The left factor is K-flat, so the K-flat comparison computes the
derived tensor product as the total tensor complex, which is concentrated in degree zero and
there is `O ⊗_O G ≅ G`. -/
def unitTensorSingleIso (T : DerivedTensorProduct.{u, v, max u v, d} Y)
    (G : Modules.{u, v, max u v} Y) :
    (T.tensor.obj ((DerivedCategory.singleFunctor (Modules.{u, v, max u v} Y) 0).obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))).obj
        ((DerivedCategory.singleFunctor (Modules.{u, v, max u v} Y) 0).obj G) ≅
      (DerivedCategory.singleFunctor (Modules.{u, v, max u v} Y) 0).obj G :=
  T.comparisonLeft _ _ (Stacks.SheafOfModules.isKFlat_single_unit Y.O) ≪≫
    DerivedCategory.Q.mapIso (HomologicalComplex.mapBifunctorSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} Y.O)
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) G) ≪≫
    (DerivedCategory.singleFunctor (Modules.{u, v, max u v} Y) 0).mapIso
      ((Stacks.SheafOfModules.unitSheafTensorNatIso (Y := Y)).app G)

end LeftUnit

end DerivedTensorProduct

end Stacks.SheafOfModules

namespace Stacks.Sites

open AlgebraicGeometry.RingedSite

variable {X : RingedSite.{u, v, max u v}}

/-- Sheaves of commutative rings on `X` remain sheaves after forgetting to sheaves of rings. -/
local instance hasSheafComposeForget₂RingCatIdealAction :
    X.J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v}) :=
  X.hasSheafCompose_forget₂_ringCat

variable [HasSheafify X.J AddCommGrpCat.{max u v}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasDerivedCategory.{d} (Modules.{u, v, max u v} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} X.O).Additive]
  [∀ M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} X.O).obj
      M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, v, max u v} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} X.O)
      (ComplexShape.up ℤ)]

/-- **The inclusion of a sheaf of ideals dies after derived tensoring with a module it kills.**
For a sheaf of ideals `I ⊆ O` and a sheaf of modules `G` killed by `I`, the map
`I[0] ⊗^L_O G[0] ⟶ O[0] ⊗^L_O G[0]` induced by the inclusion `I ⟶ O` is zero. The hypothesis is
the vanishing of the ordinary map `I ⊗_O G ⟶ O ⊗_O G`, which under `O ⊗_O G ≅ G` is the
multiplication `a ⊗ g ↦ a · g`. -/
theorem tensor_map_single_idealι_app_single_eq_zero
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, v, max u v, d} X)
    (I : IdealSubsheaf.{v, u, max u v} X.O) (G : Modules.{u, v, max u v} X)
    (hG : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} X.O).map
      I.ι).app G = 0) :
    (T.tensor.map
          ((DerivedCategory.singleFunctor (Modules.{u, v, max u v} X) 0).map I.ι)).app
        ((DerivedCategory.singleFunctor (Modules.{u, v, max u v} X) 0).obj G) = 0 :=
  T.tensor_map_single_app_single_eq_zero I.ι G
    (Stacks.SheafOfModules.isKFlat_single_unit X.O) hG

/-- **`O[0] ⊗^L_O G[0]` is a retract of `(O/I)[0] ⊗^L_O G[0]` for a module `G` killed by `I`.**
The short exact sequence `0 → I → O → O/I → 0` tensored with `G[0]` is a distinguished triangle
whose first map is zero, so the projection `O ⟶ O/I` induces a split monomorphism of derived
tensor products. -/
theorem isSplitMono_tensor_map_single_cokernelπ
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, v, max u v, d} X)
    (I : IdealSubsheaf.{v, u, max u v} X.O) (G : Modules.{u, v, max u v} X)
    (hG : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} X.O).map
      I.ι).app G = 0) :
    IsSplitMono ((T.tensor.map
        ((DerivedCategory.singleFunctor (Modules.{u, v, max u v} X) 0).map
          (cokernel.π I.ι))).app
      ((DerivedCategory.singleFunctor (Modules.{u, v, max u v} X) 0).obj G)) :=
  T.isSplitMono_tensor_map_single_g
    (ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact I.ι)
      (inferInstance : Mono I.ι) (inferInstance : Epi (cokernel.π I.ι))) G
    (tensor_map_single_idealι_app_single_eq_zero T I G hG)

/-- **`G[0]` is a retract of `(O/I)[0] ⊗^L_O G[0]` for a module `G` killed by `I`.** The left
unit isomorphism identifies `G[0]` with `O[0] ⊗^L_O G[0]`, out of which the projection
`O ⟶ O/I` induces a split monomorphism. -/
theorem isSplitMono_unitTensorSingleIso_inv_comp
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, v, max u v, d} X)
    (I : IdealSubsheaf.{v, u, max u v} X.O) (G : Modules.{u, v, max u v} X)
    (hG : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} X.O).map
      I.ι).app G = 0) :
    IsSplitMono ((T.unitTensorSingleIso G).inv ≫
      (T.tensor.map ((DerivedCategory.singleFunctor (Modules.{u, v, max u v} X) 0).map
          (cokernel.π I.ι))).app
        ((DerivedCategory.singleFunctor (Modules.{u, v, max u v} X) 0).obj G)) := by
  let morphism := (T.tensor.map
      ((DerivedCategory.singleFunctor (Modules.{u, v, max u v} X) 0).map
        (cokernel.π I.ι))).app
      ((DerivedCategory.singleFunctor (Modules.{u, v, max u v} X) 0).obj G)
  let unitComparison := T.unitTensorSingleIso G
  have : IsSplitMono morphism := isSplitMono_tensor_map_single_cokernelπ T I G hG
  exact IsSplitMono.mk' ⟨retraction morphism ≫ unitComparison.hom,
    (Category.assoc unitComparison.inv morphism (retraction morphism ≫ unitComparison.hom)).trans
      ((congrArg (fun arrow => unitComparison.inv ≫ arrow)
        ((Category.assoc morphism (retraction morphism) unitComparison.hom).symm.trans
          ((congrArg (fun arrow => arrow ≫ unitComparison.hom) (IsSplitMono.id morphism)).trans
            (Category.id_comp unitComparison.hom)))).trans unitComparison.inv_hom_id)⟩

end Stacks.Sites

end
