module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafConstant
public import StacksFrontier.CategoryTheory.Trace.Sorites.Coinvariants
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Coinvariants of a finite `Λ`-module with a continuous group action

For a finite `Λ`-module `N` with a continuous action of a topological group `G`, this file
reads the action as a `Representation`, takes its coinvariants `N_G` in the sense of Tag 03UD
(`Stacks.Trace.coinvariants`), and gives the quotient map `N ⟶ N_G` as a morphism of finite
`Λ`-modules with continuous `G`-action onto `N_G` with the trivial action. That morphism is the
universal one from `N` to a module with trivial action.

## Main definitions

* `Stacks.GroupCohomology.finiteTypeContinuousModuleRepresentation` — the action as a
  representation.
* `Stacks.GroupCohomology.finiteTypeContinuousModuleCoinvariantsMap` — the map on coinvariants
  induced by a morphism.
* `Stacks.GroupCohomology.finiteTypeContinuousModuleCoinvariantsModule` — `N_G` as a finite
  `Λ`-module.
* `Stacks.GroupCohomology.finiteTypeContinuousModuleCoinvariantsQuotient` — `N ⟶ N_G` with the
  trivial action on the target.

## Main results

* `Stacks.GroupCohomology.finiteTypeContinuousModuleCoinvariantsQuotient_naturality`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe r u' w

namespace Stacks.GroupCohomology

variable (Λ : Type r) [Ring Λ] (G : Type u') [Group G] [TopologicalSpace G]

/-- **The action of `G` on a finite `Λ`-module with continuous action, as a representation.** -/
def finiteTypeContinuousModuleRepresentation (N : FiniteTypeContinuousModule.{r, u', w} Λ G) :
    Representation Λ G N.obj.obj.obj.V where
  toFun g := (N.obj.obj.obj.ρ g).hom
  map_one' := by rw [map_one]; rfl
  map_mul' g h := by rw [map_mul]; rfl

/-- The representation acts on `x` by the action of `g` on `N`. -/
lemma finiteTypeContinuousModuleRepresentation_apply
    (N : FiniteTypeContinuousModule.{r, u', w} Λ G) (g : G) (x : N.obj.obj.obj.V) :
    finiteTypeContinuousModuleRepresentation Λ G N g x = (N.obj.obj.obj.ρ g).hom x := rfl

variable {Λ G} in
/-- A morphism of finite `Λ`-modules with continuous `G`-action commutes with the action. -/
lemma finiteTypeContinuousModule_hom_comm {N N' : FiniteTypeContinuousModule.{r, u', w} Λ G}
    (u : N ⟶ N') (g : G) (x : N.obj.obj.obj.V) :
    u.hom.hom.hom.hom.hom (finiteTypeContinuousModuleRepresentation Λ G N g x) =
      finiteTypeContinuousModuleRepresentation Λ G N' g (u.hom.hom.hom.hom.hom x) :=
  congrArg (fun φ => φ.hom x) (u.hom.hom.hom.comm g)

/-- A morphism carries the differences `g x - x` into the differences. -/
lemma finiteTypeContinuousModule_coinvariantsKer_le_comap
    {N N' : FiniteTypeContinuousModule.{r, u', w} Λ G} (u : N ⟶ N') :
    Stacks.Trace.coinvariantsKer (finiteTypeContinuousModuleRepresentation Λ G N) ≤
      (Stacks.Trace.coinvariantsKer (finiteTypeContinuousModuleRepresentation Λ G N')).comap
        u.hom.hom.hom.hom.hom := by
  rw [Stacks.Trace.coinvariantsKer, Submodule.span_le]
  rintro _ ⟨⟨g, x⟩, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub, finiteTypeContinuousModule_hom_comm]
  exact Submodule.subset_span ⟨(g, u.hom.hom.hom.hom.hom x), rfl⟩

/-- **The map on coinvariants induced by a morphism.** -/
def finiteTypeContinuousModuleCoinvariantsMap {N N' : FiniteTypeContinuousModule.{r, u', w} Λ G}
    (u : N ⟶ N') :
    Stacks.Trace.coinvariants (finiteTypeContinuousModuleRepresentation Λ G N) →ₗ[Λ]
      Stacks.Trace.coinvariants (finiteTypeContinuousModuleRepresentation Λ G N') :=
  Submodule.mapQ _ _ u.hom.hom.hom.hom.hom
    (finiteTypeContinuousModule_coinvariantsKer_le_comap Λ G u)

/-- The map on coinvariants induced by `u` sends the class of `x` to the class of `u x`. -/
@[simp]
lemma finiteTypeContinuousModuleCoinvariantsMap_mk
    {N N' : FiniteTypeContinuousModule.{r, u', w} Λ G} (u : N ⟶ N') (x : N.obj.obj.obj.V) :
    finiteTypeContinuousModuleCoinvariantsMap Λ G u
        (Stacks.Trace.coinvariantsMk (finiteTypeContinuousModuleRepresentation Λ G N) x) =
      Stacks.Trace.coinvariantsMk (finiteTypeContinuousModuleRepresentation Λ G N')
        (u.hom.hom.hom.hom.hom x) := rfl

/-- **`N_G` as a finite `Λ`-module.** -/
def finiteTypeContinuousModuleCoinvariantsModule (N : FiniteTypeContinuousModule.{r, u', w} Λ G) :
    ObjectProperty.FullSubcategory (ModuleCat.isFG.{w} Λ) :=
  ⟨ModuleCat.of Λ (Stacks.Trace.coinvariants (finiteTypeContinuousModuleRepresentation Λ G N)),
    by
      have : Module.Finite Λ N.obj.obj.obj.V := N.property
      change Module.Finite Λ (_ ⧸ _)
      infer_instance⟩

/-- The underlying module of `N_G` is the coinvariants. -/
def finiteTypeContinuousModuleCoinvariantsModuleEquiv
    (N : FiniteTypeContinuousModule.{r, u', w} Λ G) :
    ((ModuleCat.isFG Λ).ι.obj (finiteTypeContinuousModuleCoinvariantsModule Λ G N)) ≃ₗ[Λ]
      Stacks.Trace.coinvariants (finiteTypeContinuousModuleRepresentation Λ G N) :=
  LinearEquiv.refl _ _

/-- The identification of `N_G` with the coinvariants carries the induced morphism to the map on
coinvariants. -/
lemma finiteTypeContinuousModuleCoinvariantsModuleEquiv_naturality
    {N N' : FiniteTypeContinuousModule.{r, u', w} Λ G} (u : N ⟶ N')
    (x : (ModuleCat.isFG Λ).ι.obj (finiteTypeContinuousModuleCoinvariantsModule Λ G N)) :
    finiteTypeContinuousModuleCoinvariantsModuleEquiv Λ G N'
        (ConcreteCategory.hom ((ModuleCat.isFG Λ).ι.map
          (ObjectProperty.homMk
              (ModuleCat.ofHom (finiteTypeContinuousModuleCoinvariantsMap Λ G u)) :
            finiteTypeContinuousModuleCoinvariantsModule Λ G N ⟶
              finiteTypeContinuousModuleCoinvariantsModule Λ G N')) x) =
      finiteTypeContinuousModuleCoinvariantsMap Λ G u
        (finiteTypeContinuousModuleCoinvariantsModuleEquiv Λ G N x) := rfl

/-- **The quotient `N ⟶ N_G`**, a morphism onto the coinvariants with the trivial action. -/
def finiteTypeContinuousModuleCoinvariantsQuotient
    (N : FiniteTypeContinuousModule.{r, u', w} Λ G) :
    N ⟶ (finiteTypeContinuousModuleTrivial Λ G).obj
      (finiteTypeContinuousModuleCoinvariantsModule Λ G N) :=
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom
        (Stacks.Trace.coinvariantsMk (finiteTypeContinuousModuleRepresentation Λ G N))
      comm := fun g => by
        ext x
        exact Stacks.Trace.coinvariantsMk_group_action _ g x }))

/-- The quotient `N ⟶ N_G` sends `x` to its class in the coinvariants. -/
@[simp]
lemma finiteTypeContinuousModuleCoinvariantsQuotient_apply
    (N : FiniteTypeContinuousModule.{r, u', w} Λ G) (x : N.obj.obj.obj.V) :
    (finiteTypeContinuousModuleCoinvariantsQuotient Λ G N).hom.hom.hom.hom.hom x =
      Stacks.Trace.coinvariantsMk (finiteTypeContinuousModuleRepresentation Λ G N) x := rfl

/-- **`N ⟶ N_G` is natural in `N`.** -/
theorem finiteTypeContinuousModuleCoinvariantsQuotient_naturality
    {N N' : FiniteTypeContinuousModule.{r, u', w} Λ G} (u : N ⟶ N') :
    u ≫ finiteTypeContinuousModuleCoinvariantsQuotient Λ G N' =
      finiteTypeContinuousModuleCoinvariantsQuotient Λ G N ≫
        (finiteTypeContinuousModuleTrivial Λ G).map
          (ObjectProperty.homMk
            (ModuleCat.ofHom (finiteTypeContinuousModuleCoinvariantsMap Λ G u))) := by
  ext
  rfl

end Stacks.GroupCohomology

end
