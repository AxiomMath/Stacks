module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.Cohomology.ExtFromStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDualityLinear
public import StacksFrontier.Homology.DerivedLinear

/-!
# Morphisms out of the structure sheaf compute sheaf cohomology, `k`-linearly

For a scheme `X` over a field `k` and a sheaf of `𝒪_X`-modules `ℱ`, the comparison

  `Hom_{D(𝒪_X)}(𝒪_X[0], ℱ[0]⟦1⟧) = H¹(X, ℱ)`

of `AlgebraicGeometry.derivedHomStructureSheafEquivCohomologyOverField` is an isomorphism of
*abelian groups*, and that carries no dimension count: an additive isomorphism of `k`-vector
spaces says nothing about their dimensions over `k`. This file upgrades it to an isomorphism of
`k`-vector spaces, and at the same time moves it from the model
`CategoryTheory.HasDerivedCategory.standard` of the derived category — where
`AlgebraicGeometry.derivedHomStructureSheafEquivCohomologyOverField` is stated, and whose
morphism groups live one universe up — to the locally small
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which is where the duality of
[Stacks, Tag 0BS2] lives.

## Main definitions

* `AlgebraicGeometry.extOneLinearEquivCohomologyOverField` —
  `Ext^1(𝒪_X, ℱ) ≃ₗ[k] H¹(X, ℱ)`, with `CategoryTheory.Abelian.Ext` the model-independent
  Ext-group.
* `AlgebraicGeometry.zExtOneLinearEquivCohomologyOverField` —
  `Hom_{D(𝒪_X)}(𝒪_X[0], ℱ[0]⟦1⟧) ≃ₗ[k] H¹(X, ℱ)` at the locally small model.

## Main results

* `Stacks.Cohomology.SpaceModules.extEquivCohomology_naturality_one` and
  `...extEquivModuleCohomology_naturality_one` — the degree-one comparison of extensions of the
  structure sheaf with cohomology is natural in the coefficient module.
* `AlgebraicGeometry.linear_cohomologyOverFieldFunctor` — `Hⁿ(X, -)` is a `k`-linear functor.
* `AlgebraicGeometry.rightDerived_evaluation_map_smul_id_apply` — `Hⁿ(X, a·id)` is multiplication
  by `a`.

## Implementation notes

*The model transport.* `CategoryTheory.Abelian.Ext` does not mention a model of the derived
category, and `CategoryTheory.Abelian.Ext.homLinearEquiv` is its `R`-linear comparison with a
morphism group at *any* model. Composing the comparison above with that equivalence at the locally
small model is the transport. This is the `k`-linear form of the additive transport in
`Stacks.Duality.subsingleton_cohomologyOverField_of_subsingleton_zExt`.

*The structure sheaf has to be named at the type `X.Modules`.* `SheafOfModules.unit
X.ringCatSheaf` has type `SheafOfModules X.ringCatSheaf`, which is definitionally `X.Modules`
but is not that `def`; an `Ext`-group whose ambient category is inferred from it is read at the
wrong category and its module structure is then not found. `Stacks.Ample.unitModule` is the same
sheaf at the type `X.Modules`, and is what the statements below use.

## References

* [Stacks Project, Tag 0B3A](https://stacks.math.columbia.edu/tag/0B3A)
* [Stacks Project, Tag 03F1](https://stacks.math.columbia.edu/tag/03F1)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
  TopologicalSpace

universe u

namespace Stacks.Cohomology.SpaceModules

section Standard

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] HasExt.standard

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- **The comparison `Ext^1(𝒪_X, ℱ) = H¹(X, ℱ)` is natural in `ℱ`**, with the abelian-group
valued cohomology of [Stacks, Tag 01E3] on the right: postcomposing an extension class with
`g : ℱ ⟶ 𝒢` corresponds to applying `H¹(X, g)`. -/
theorem extEquivCohomology_naturality_one (M N : SheafOfModules.{u} R) (g : M ⟶ N)
    (e : Ext (_root_.SheafOfModules.unit R) M 1) :
    extEquivCohomology R N 1 (e.comp (Ext.mk₀ g) (add_zero 1)) =
      (Hfunctor R ⊤ 1).map g (extEquivCohomology R M 1 e) := by
  have h1 : SiteModules.extEquivCohomology R N 1 (e.comp (Ext.mk₀ g) (add_zero 1)) =
      (SiteModules.cohomologyFunctor R 1).map g (SiteModules.extEquivCohomology R M 1 e) :=
    SiteModules.extOneEquivFirstCohomology_naturality R g e
  have h2 := NatTrans.naturality_apply (cohomologyIsoSiteCohomology R 1).hom g
    (SiteModules.extEquivCohomology R M 1 e)
  dsimp [extEquivCohomology]
  rw [h1]
  exact h2

/-- **The comparison `Ext^1(𝒪_X, ℱ) = H¹(X, ℱ)` is natural in `ℱ`**, in the module-valued
presentation of cohomology: the right derived functor of module-valued sections over the whole
space. -/
theorem extEquivModuleCohomology_naturality_one (M N : SheafOfModules.{u} R) (g : M ⟶ N)
    (e : Ext (_root_.SheafOfModules.unit R) M 1) :
    extEquivModuleCohomology R N 1 (e.comp (Ext.mk₀ g) (add_zero 1)) =
      ((_root_.SheafOfModules.evaluation R (op (⊤ : Opens X))).rightDerived 1).map g
        (extEquivModuleCohomology R M 1 e) := by
  have h1 := extEquivCohomology_naturality_one R M N g e
  have h2 := NatTrans.naturality_apply (ModuleComparison.rightDerivedEvaluationForgetIso R ⊤ 1).inv
    g (extEquivCohomology R M 1 e)
  dsimp [extEquivModuleCohomology]
  rw [h1]
  exact h2

end Standard

end Stacks.Cohomology.SpaceModules

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **`Hⁿ(X, -) : X.Modules ⥤ ModuleCat k` is a `k`-linear functor.** -/
theorem linear_cohomologyOverFieldFunctor (n : ℕ) :
    letI := Scheme.Modules.linearOverBase f
    Functor.Linear k (cohomologyOverFieldFunctor k f n) := by
  let := Scheme.Modules.linearOverBase f
  let : Functor.Linear k (globalSectionsOver f) := globalSectionsOver_linear_linearOverBase f
  set e := Stacks.Duality.rightDerivedCompRestrictScalarsIso
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom
      (_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens)))
      (globalSectionsOver f) (Stacks.Duality.evaluationCompRestrictScalarsIsoGlobalSectionsOver k f)
      n (hE := AlgebraicGeometry.evaluationAdditive X)
      (hH := AlgebraicGeometry.globalSectionsOver_additive f) with he
  rw [Functor.linear_iff]
  intro M a
  have hlin : ((globalSectionsOver f).rightDerived n).map (a • 𝟙 M) =
      a • 𝟙 (((globalSectionsOver f).rightDerived n).obj M) :=
    (Functor.linear_iff k ((globalSectionsOver f).rightDerived n)).1
      (Stacks.DerivedLinear.rightDerived_linear _ n) M a
  refine Eq.trans (NatIso.naturality_2 e (a • 𝟙 M)).symm ?_
  refine Eq.trans (congrArg (fun z => e.hom.app M ≫ z ≫ e.inv.app M) hlin) ?_
  refine Eq.trans (congrArg (fun z => e.hom.app M ≫ z)
    (Linear.smul_comp _ _ _ a (𝟙 _) (e.inv.app M))) ?_
  refine Eq.trans (Linear.comp_smul _ _ _ (e.hom.app M) a (𝟙 _ ≫ e.inv.app M)) ?_
  refine congrArg (fun z => a • z) ?_
  refine Eq.trans (congrArg (fun z => e.hom.app M ≫ z) (Category.id_comp (e.inv.app M))) ?_
  exact e.hom_inv_id_app M

/-- **`Hⁿ(X, a · id)` is multiplication by `a` on `Hⁿ(X, ℱ)`**, read on elements. The morphism is
the one of the module-valued cohomology, whose underlying map is that of the `k`-linear one. -/
theorem rightDerived_evaluation_map_smul_id_apply (n : ℕ) (a : k) (F : X.Modules)
    (x : cohomologyOverField k f F n) :
    letI := Scheme.Modules.linearOverBase f
    ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n).map
      (a • 𝟙 F) x = a • x := by
  let := Scheme.Modules.linearOverBase f
  exact congrFun (congrArg (fun z => (ModuleCat.Hom.hom z).toFun)
    ((Functor.linear_iff k (cohomologyOverFieldFunctor k f n)).1
      (linear_cohomologyOverFieldFunctor f n) F a)) x

section ExtLinear

attribute [local instance] HasExt.standard

/-- **`Ext^1_{𝒪_X}(𝒪_X, ℱ) ≃ₗ[k] H¹(X, ℱ)`** on a scheme over a field: the comparison of
extensions of the structure sheaf with first cohomology, as an isomorphism of `k`-vector spaces.

The underlying additive isomorphism is
`Stacks.Cohomology.SpaceModules.extEquivModuleCohomology`, read over `k` — restricting scalars
changes the scalars and not the group. -/
def extOneLinearEquivCohomologyOverField (F : X.Modules) :
    letI := Scheme.Modules.linearOverBase f
    Abelian.Ext (Stacks.Ample.unitModule X) F 1 ≃ₗ[k] cohomologyOverField k f F 1 :=
  letI := Scheme.Modules.linearOverBase f
  { __ := Stacks.Cohomology.SpaceModules.extEquivModuleCohomology X.ringCatSheaf F 1
    map_smul' := fun a α => by
      refine Eq.trans (congrArg
        (Stacks.Cohomology.SpaceModules.extEquivModuleCohomology X.ringCatSheaf F 1)
        (Abelian.Ext.smul_eq_comp_mk₀ α a)) ?_
      refine Eq.trans (Stacks.Cohomology.SpaceModules.extEquivModuleCohomology_naturality_one
        X.ringCatSheaf F F (a • 𝟙 F) α) ?_
      exact rightDerived_evaluation_map_smul_id_apply f 1 a F
        (Stacks.Cohomology.SpaceModules.extEquivModuleCohomology X.ringCatSheaf F 1 α) }

/-- **`Hom_{D(𝒪_X)}(𝒪_X[0], ℱ[0]⟦1⟧) ≃ₗ[k] H¹(X, ℱ)` at the locally small model of the derived
category**.

`AlgebraicGeometry.extOneLinearEquivCohomologyOverField` identifies first cohomology with the
model-independent `CategoryTheory.Abelian.Ext`, and
`CategoryTheory.Abelian.Ext.homLinearEquiv` identifies that `k`-linearly with the morphism group
at whichever model is in scope. The composite therefore crosses from the model
`CategoryTheory.HasDerivedCategory.standard`, at which the comparison with sheaf cohomology is
baked and in whose universe the morphism group below does not even live, to the locally small
one. -/
def zExtOneLinearEquivCohomologyOverField (F : X.Modules) :
    letI := Scheme.Modules.linearOverBase f
    Abelian.zExt (Stacks.Ample.unitModule X) F (1 : ℤ) ≃ₗ[k] cohomologyOverField k f F 1 :=
  letI := Scheme.Modules.linearOverBase f
  (Abelian.Ext.homLinearEquiv (R := k) (X := Stacks.Ample.unitModule X)
      (Y := F) (n := 1)).symm.trans
    (extOneLinearEquivCohomologyOverField f F)

end ExtLinear

end AlgebraicGeometry

end
