module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.RelativeExtTarget
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Composition

/-!
# Pulling back the complex `𝒢 ⊗_{𝒪_X} f^*ℱ`

Let `a : U ⟶ X` and `f : X ⟶ Y` be morphisms of ringed spaces and `𝒢` a complex of
`𝒪_X`-modules. Write `a^*𝒢` for the complex of `𝒪_U`-modules obtained by pulling back `𝒢`
termwise. For an `𝒪_Y`-module `ℱ`, the comparison `a^*(𝒜 ⊗ ℬ) ≅ a^*𝒜 ⊗ a^*ℬ` of
[Stacks, Tag 01CD] and the composition `a^* f^* ≅ (f ∘ a)^*` give an isomorphism of complexes

`a^*𝒢 ⊗_{𝒪_U} (f ∘ a)^*ℱ ≅ a^*(𝒢 ⊗_{𝒪_X} f^*ℱ)`,

natural in `ℱ`. This is how the complex of [Stacks, Tag 08IF] restricts to an open subscheme.

## Main definitions

* `Stacks.Cohomology.RelativeExt.pullbackComplex`: the termwise pullback `a^*𝒢`.
* `Stacks.Cohomology.RelativeExt.restrictTargetIso`: the isomorphism above, as an isomorphism
  of functors of `ℱ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open TopologicalSpace

universe u

namespace Stacks.Cohomology.RelativeExt

attribute [local implicit_reducible] structureSheafRing TopCat.Sheaf TopCat.Presheaf.IsSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf AlgebraicGeometry.SheafedSpace.sheaf

attribute [local instance] sheafTensorAdditiveSpace sheafTensorObjAdditiveSpace

variable {U X Y : RingedSpace.{u, u}} (a : U ⟶ X) (f : X ⟶ Y)
  (G : CochainComplex (TModules X) ℤ)

/-- **The termwise pullback `a^*𝒢`** of a complex of `𝒪_X`-modules. -/
abbrev pullbackComplex : CochainComplex (TModules U) ℤ :=
  ((modulePullback a).mapHomologicalComplex (ComplexShape.up ℤ)).obj G

/-- The term `a^*𝒢^q ⊗ (f ∘ a)^*ℱ ≅ a^*(𝒢^q ⊗ f^*ℱ)`. -/
def pullbackTensorTermIso (q : ℤ) (F : SheafOfModules.{u} (structureSheafRing Y)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} U.sheaf).obj
        ((modulePullback a).obj (G.X q))).obj ((modulePullback (a ≫ f)).obj F) ≅
      (modulePullback a).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (G.X q)).obj
          ((modulePullback f).obj F)) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} U.sheaf).obj
      ((modulePullback a).obj (G.X q))).mapIso
      ((Stacks.DerivedPullback.Composition.modulePullbackComp a f).symm.app F) ≪≫
    ((Stacks.RingedSpace.comparisonBifunctorIso a).app (G.X q, (modulePullback f).obj F)).symm

/-- Naturality of `pullbackTensorTermIso` in both the term of `𝒢` and `ℱ`. -/
private theorem pullbackTensorTermIso_hom_naturality_aux {q q' : ℤ} (g : G.X q ⟶ G.X q')
    {F F' : SheafOfModules.{u} (structureSheafRing Y)} (v : F ⟶ F') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} U.sheaf).map
          ((modulePullback a).map g)).app ((modulePullback (a ≫ f)).obj F) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} U.sheaf).obj
          ((modulePullback a).obj (G.X q'))).map ((modulePullback (a ≫ f)).map v) ≫
        (pullbackTensorTermIso a f G q' F').hom =
      (pullbackTensorTermIso a f G q F).hom ≫
        (modulePullback a).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map g).app
              ((modulePullback f).obj F) ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
              (G.X q')).map ((modulePullback f).map v)) := by
  have h := (Stacks.RingedSpace.comparisonBifunctorIso a).inv.naturality
    (X := (G.X q, (modulePullback f).obj F)) (Y := (G.X q', (modulePullback f).obj F'))
    (g, (modulePullback f).map v)
  have hc := (Stacks.DerivedPullback.Composition.modulePullbackComp a f).inv.naturality v
  simp only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map] at h
  simp only [pullbackTensorTermIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Category.assoc]
  have e := congrArg (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} U.sheaf).obj
    ((modulePullback a).obj (G.X q'))).map) hc
  simp only [Functor.map_comp] at e
  rw [reassoc_of% e, ← reassoc_of%
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} U.sheaf).map
      ((modulePullback a).map g)).naturality _)]
  congr 1

/-- The isomorphisms `pullbackTensorTermIso` commute with the differentials of `a^*𝒢 ⊗ (f ∘ a)^*ℱ`
and of `a^*(𝒢 ⊗ f^*ℱ)`. -/
theorem pullbackTensorTermIso_hom_comm (q q' : ℤ)
    (F : SheafOfModules.{u} (structureSheafRing Y)) :
    (pullbackTensorTermIso a f G q F).hom ≫
        (modulePullback a).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map
            (G.d q q')).app ((modulePullback f).obj F)) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} U.sheaf).map
          ((modulePullback a).map (G.d q q'))).app ((modulePullback (a ≫ f)).obj F) ≫
        (pullbackTensorTermIso a f G q' F).hom := by
  symm
  simpa only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Category.comp_id] using pullbackTensorTermIso_hom_naturality_aux a f G (G.d q q') (𝟙 F)

/-- **`a^*𝒢 ⊗ (f ∘ a)^*ℱ ≅ a^*(𝒢 ⊗ f^*ℱ)`**, as complexes, for one `𝒪_Y`-module `ℱ`. -/
def restrictTargetIsoApp (F : SheafOfModules.{u} (structureSheafRing Y)) :
    (relativeExtTargetFunctor (a ≫ f) (pullbackComplex a G)).obj F ≅
      ((modulePullback a).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((relativeExtTargetFunctor f G).obj F) :=
  HomologicalComplex.Hom.isoOfComponents (fun q => pullbackTensorTermIso a f G q F)
    (fun q q' _ => pullbackTensorTermIso_hom_comm a f G q q' F)

/-- The isomorphism `pullbackTensorTermIso` is natural in the `𝒪_Y`-module `ℱ`. -/
theorem pullbackTensorTermIso_hom_naturality (q : ℤ)
    {F F' : SheafOfModules.{u} (structureSheafRing Y)} (v : F ⟶ F') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} U.sheaf).obj
        ((modulePullback a).obj (G.X q))).map ((modulePullback (a ≫ f)).map v) ≫
        (pullbackTensorTermIso a f G q F').hom =
      (pullbackTensorTermIso a f G q F).hom ≫
        (modulePullback a).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
            (G.X q)).map ((modulePullback f).map v)) := by
  simpa only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Category.comp_id] using pullbackTensorTermIso_hom_naturality_aux a f G (𝟙 (G.X q)) v

/-- **`a^*𝒢 ⊗ (f ∘ a)^*ℱ ≅ a^*(𝒢 ⊗ f^*ℱ)`**, naturally in the `𝒪_Y`-module `ℱ`. -/
def restrictTargetIso :
    relativeExtTargetFunctor (a ≫ f) (pullbackComplex a G) ≅
      relativeExtTargetFunctor f G ⋙
        (modulePullback a).mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatIso.ofComponents (restrictTargetIsoApp a f G) (fun v =>
    HomologicalComplex.hom_ext _ _ (fun q => pullbackTensorTermIso_hom_naturality a f G q v))

end Stacks.Cohomology.RelativeExt

end
