module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Topology.Sheaves.Modules.StalkExactness
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GrothendieckAbelian
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero

/-!
# Isomorphisms in the derived category of sheaves of modules are detected on stalks

Let `𝒪` be a sheaf of rings on a topological space `X`. A morphism of the unbounded derived
category of sheaves of `𝒪`-modules is an isomorphism exactly when, for every degree `i` and
every point `x : X`, it induces an isomorphism on the stalk at `x` of the `i`-th cohomology
sheaf. This is the shape in which Stacks 0E23 and its relatives reduce a base change comparison
to a statement about local rings.

The stalk functor
`AlgebraicGeometry.SheafOfModules.stalkFunctor 𝒪 x : SheafOfModules 𝒪 ⥤ ModuleCat 𝒪_x` is
additive (`stalkFunctor_additive`) and preserves finite limits and finite colimits
(`stalkFunctor_preservesFiniteLimits`, `instPreservesFiniteColimitsStalkFunctor`), hence is
exact, hence induces a functor on unbounded derived categories, the derived stalk functor.
Composing the stalkwise criterion with `CategoryTheory.Functor.isIso_mapDerivedCategory_map_iff`
replaces its doubly-indexed test by a single one: the morphism is invertible exactly when its
*derived* stalk is invertible at every point. That is the form in which a statement about the
derived category of a local ring, such as Stacks 0661, can be fed back into a statement about the
derived category of a space.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.derivedStalkFunctor`: the functor
  `D(SheafOfModules 𝒪) ⥤ D(ModuleCat 𝒪_x)` induced by the stalk functor.
* `AlgebraicGeometry.SheafOfModules.derivedStalkFunctorFactors`: it is induced by applying the
  stalk functor degreewise.

## Main results

* `Stacks.Cohomology.StalkwiseIso.isIso_iff_forall_stalkAddCommGroup_isIso`: invertibility in
  the derived category, tested by the `AddCommGrpCat`-valued stalks of the cohomology sheaves.
* `Stacks.Cohomology.StalkwiseIso.isIso_iff_forall_stalk_isIso`: the same criterion with the
  stalks taken over the stalk ring, i.e. in `ModuleCat 𝒪_x`.
* `Stacks.Cohomology.StalkwiseIso.isIso_iff_forall_derivedStalk_isIso`: a morphism of the derived
  category of sheaves of `𝒪`-modules is an isomorphism exactly when its derived stalk is an
  isomorphism at every point of `X`.

## Implementation notes

The stalkwise criterion composes two facts. `CategoryTheory.DerivedCategory.isIso_iff` says a
morphism of the derived category of an abelian category is invertible exactly when every
`homologyFunctor` carries it to an isomorphism; that reduces the question to morphisms of
sheaves of modules. `ExtensionByZeroModules.isIso_of_stalk_isIso` then says a morphism of
sheaves of modules which is invertible on every stalk of the underlying presheaf of abelian
groups is invertible, by reflection along `SheafOfModules.toSheaf`.

**The stalkwise criterion is stated at an arbitrary `HasDerivedCategory` instance**, carried as
an instance binder rather than fixed to `HasDerivedCategory.standard`. Neither input constrains
it: `DerivedCategory.isIso_iff` is stated at a free instance, and `isIso_of_stalk_isIso` is a
statement about sheaves of modules in which no derived category occurs. Keeping the binder free
lets the criterion be applied to a morphism of `D(𝒪_X)` at the locally small model, which is
where the derived-limit statements of Stacks 0D61 and 0D62 live. The derived stalk functor and
`isIso_iff_forall_derivedStalk_isIso` are stated with `HasDerivedCategory.standard`, declared as
a local instance, on both derived categories.

The two spellings of the stalk are interchanged by
`AlgebraicGeometry.SheafOfModules.stalkFunctor_comp_forget₂`, which holds by `rfl`: the
`AddCommGrpCat`-valued stalk functor of a sheaf of modules *is* the `ModuleCat 𝒪_x`-valued one
followed by `forget₂`. So the module-valued criterion is the abelian-group one composed with
`Functor.map_isIso`, and in the other direction with `isIso_of_reflects_iso`, `forget₂` to
`AddCommGrpCat` reflecting isomorphisms of modules.

Universes are collapsed to a single `u`, inherited from `stalkFunctor`: the sheaf of rings, the
space and the sheaves of modules all live at `u` there.

No declaration here is tagged. The criterion is the stalk criterion of Stacks 01AG transported
to the derived category, and it is an input to Stacks 0E23 rather than a clause of it; the
derived stalk functor is a construction the Stacks project does not state as a result.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.SheafOfModules
open ExtensionByZeroModules

namespace Stacks.Cohomology.StalkwiseIso

universe u d

variable {X : TopCat.{u}} (O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  [HasDerivedCategory.{d} (_root_.SheafOfModules.{u} O)]

/-- A morphism of the unbounded derived category of sheaves of `𝒪`-modules is an isomorphism
if, in every degree, the induced map of cohomology sheaves is an isomorphism on the stalk of
the underlying presheaf of abelian groups at every point. -/
theorem isIso_of_forall_stalkAddCommGroup_isIso
    {E F : DerivedCategory (_root_.SheafOfModules.{u} O)} (φ : E ⟶ F)
    (h : ∀ (i : ℤ) (x : X), IsIso ((stalkAddCommGroupFunctor O x).map
      ((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} O) i).map φ))) :
    IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro i
  exact isIso_of_stalk_isIso O _ (h i)

/-- **The stalkwise criterion for invertibility in the derived category.** A morphism of the
unbounded derived category of sheaves of `𝒪`-modules is an isomorphism exactly when, in every
degree, the induced map of cohomology sheaves is an isomorphism on every stalk of the
underlying presheaf of abelian groups. -/
theorem isIso_iff_forall_stalkAddCommGroup_isIso
    {E F : DerivedCategory (_root_.SheafOfModules.{u} O)} (φ : E ⟶ F) :
    IsIso φ ↔ ∀ (i : ℤ) (x : X), IsIso ((stalkAddCommGroupFunctor O x).map
      ((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} O) i).map φ)) := by
  refine ⟨fun hφ i x => ?_, isIso_of_forall_stalkAddCommGroup_isIso O φ⟩
  have := hφ
  exact Functor.map_isIso _ _

/-- The stalkwise criterion with the stalks taken over the stalk ring: a morphism of the
derived category is an isomorphism if each induced map of cohomology sheaves is an isomorphism
of `𝒪_x`-modules on every stalk. -/
theorem isIso_of_forall_stalk_isIso
    {E F : DerivedCategory (_root_.SheafOfModules.{u} O)} (φ : E ⟶ F)
    (h : ∀ (i : ℤ) (x : X), IsIso ((stalkFunctor O x).map
      ((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} O) i).map φ))) :
    IsIso φ := by
  refine isIso_of_forall_stalkAddCommGroup_isIso O φ fun i x => ?_
  have := h i x
  exact Functor.map_isIso
    (forget₂ (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x))
      AddCommGrpCat.{u})
    ((stalkFunctor O x).map
      ((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} O) i).map φ))

/-- **The stalkwise criterion over the stalk ring.** A morphism of the unbounded derived
category of sheaves of `𝒪`-modules is an isomorphism exactly when, in every degree, the
induced map of cohomology sheaves is an isomorphism of `𝒪_x`-modules on every stalk.

This is the form a statement about the local rings can be fed into, the stalk of the `i`-th
cohomology sheaf being an honest module over the stalk of `𝒪`. -/
theorem isIso_iff_forall_stalk_isIso
    {E F : DerivedCategory (_root_.SheafOfModules.{u} O)} (φ : E ⟶ F) :
    IsIso φ ↔ ∀ (i : ℤ) (x : X), IsIso ((stalkFunctor O x).map
      ((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} O) i).map φ)) := by
  refine ⟨fun hφ i x => ?_, isIso_of_forall_stalk_isIso O φ⟩
  have := hφ
  exact Functor.map_isIso _ _

end Stacks.Cohomology.StalkwiseIso

end

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.SheafOfModules

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (x : X)

/-- **The derived stalk functor.** The stalk functor at `x` is exact, so it induces a functor
from the derived category of sheaves of `𝒪`-modules to the derived category of
`𝒪_x`-modules. -/
def derivedStalkFunctor :
    DerivedCategory (_root_.SheafOfModules.{u} O) ⥤
      DerivedCategory (ModuleCat.{u}
        (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x)) :=
  (stalkFunctor O x).mapDerivedCategory

/-- The derived stalk functor is induced by taking stalks degreewise: on a complex of sheaves of
modules it is the complex of stalks. -/
def derivedStalkFunctorFactors :
    DerivedCategory.Q ⋙ derivedStalkFunctor O x ≅
      (stalkFunctor O x).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (stalkFunctor O x).mapDerivedCategoryFactors

/-- The derived stalk of the `n`-th cohomology sheaf: taking the derived stalk and then homology
in degree `n` is taking homology in degree `n` and then the stalk. -/
def derivedStalkHomologyIso (n : ℤ) :
    derivedStalkFunctor O x ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u}
        (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x)) n ≅
      DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} O) n ⋙ stalkFunctor O x :=
  (stalkFunctor O x).mapDerivedCategoryHomologyIso n

end AlgebraicGeometry.SheafOfModules

namespace Stacks.Cohomology.StalkwiseIso

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- **Invertibility in the derived category is detected by the derived stalks.** A morphism of
the unbounded derived category of sheaves of `𝒪`-modules is an isomorphism exactly when its
derived stalk is an isomorphism at every point.

This is `isIso_iff_forall_stalk_isIso` with its two quantifiers contracted to one, by
`CategoryTheory.Functor.isIso_mapDerivedCategory_map_iff`. -/
theorem isIso_iff_forall_derivedStalk_isIso
    {E F : DerivedCategory (_root_.SheafOfModules.{u} O)} (φ : E ⟶ F) :
    IsIso φ ↔ ∀ x : X,
      IsIso ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctor O x).map φ) := by
  rw [isIso_iff_forall_stalk_isIso O φ, forall_comm]
  exact forall_congr' fun x =>
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor O x).isIso_mapDerivedCategory_map_iff φ).symm

end Stacks.Cohomology.StalkwiseIso

end

end
