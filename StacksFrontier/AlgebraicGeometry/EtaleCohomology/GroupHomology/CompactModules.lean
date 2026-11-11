module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Module.PUnit
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Category.TopCat.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Compact abelian groups with a continuous group action

Let `G` be a topological group. A compact `G`-module is a compact Hausdorff abelian topological
group `M` together with an action of `G` on `M` by group automorphisms such that the action map
`G × M → M` is continuous. A morphism of compact `G`-modules is a continuous `G`-equivariant
homomorphism. These form the category on which the homology `H_i(G, -) = L_i H_0(G, -)` of a
profinite group is defined in [Stacks, Tag 03VI]. For `G` the trivial group this is the
category of compact abelian groups.

## Main definitions

* `Stacks.GroupHomology.CompactGModule G`: the category of compact abelian groups with continuous
  `G`-action.
* `Stacks.GroupHomology.CompactGModule.Hom.hom`: the continuous homomorphism underlying a
  morphism.
* `Stacks.GroupHomology.CompactAddCommGrp`: compact abelian groups, as compact modules over the
  trivial group.
* `Stacks.GroupHomology.CompactGModule.forgetAction`: the functor forgetting the action.
* `Stacks.GroupHomology.CompactGModule.forgetToAddCommGrp` and
  `Stacks.GroupHomology.CompactGModule.forgetToTop`: the underlying abelian group and the
  underlying topological space.

## Main results

* The category `CompactGModule G` is preadditive and has a zero object.

## Implementation notes

An object bundles the carrier with its group, topology and action structures as instance
arguments, and a morphism is a `ContinuousAddMonoidHom` with an equivariance proof. The group
structure on morphisms is transported from the additive subgroup of equivariant maps in
`M →ₜ+ N`, so the sum of two morphisms has underlying map the pointwise sum by `rfl`.

## References

* [Stacks Project, Tag 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace Stacks.GroupHomology

/-- A compact `G`-module: a compact Hausdorff abelian topological group with an action of `G` by
group automorphisms for which the action map `G × M → M` is continuous. -/
@[stacks 03VI "the category of compact abelian groups with continuous G-action"]
structure CompactGModule (G : Type u) [Group G] [TopologicalSpace G] where
  /-- The underlying type. -/
  carrier : Type v
  [addCommGroup : AddCommGroup carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [isTopologicalAddGroup : IsTopologicalAddGroup carrier]
  [compactSpace : CompactSpace carrier]
  [t2Space : T2Space carrier]
  [distribMulAction : DistribMulAction G carrier]
  [continuousSMul : ContinuousSMul G carrier]

namespace CompactGModule

attribute [instance] addCommGroup topologicalSpace isTopologicalAddGroup compactSpace t2Space
  distribMulAction continuousSMul

variable {G : Type u} [Group G] [TopologicalSpace G]

instance : CoeSort (CompactGModule.{u, v} G) (Type v) := ⟨carrier⟩

/-- The compact `G`-module given by a compact Hausdorff abelian group with a continuous action of
`G` by group automorphisms. -/
abbrev of (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [CompactSpace M] [T2Space M] [DistribMulAction G M] [ContinuousSMul G M] :
    CompactGModule.{u, v} G :=
  ⟨M⟩

/-- The carrier of `CompactGModule.of M` is `M`. -/
lemma coe_of (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [CompactSpace M] [T2Space M] [DistribMulAction G M] [ContinuousSMul G M] :
    (of (G := G) M : Type v) = M := rfl

/-- The additive subgroup of the continuous homomorphisms `M →ₜ+ N` that are `G`-equivariant. -/
def equivariantHoms (M N : CompactGModule.{u, v} G) : AddSubgroup (M →ₜ+ N) where
  carrier := {f | ∀ (g : G) (m : M), f (g • m) = g • f m}
  zero_mem' _ _ := (smul_zero _).symm
  add_mem' {f f'} hf hf' g m := by
    simp only [ContinuousAddMonoidHom.add_apply, hf g m, hf' g m, smul_add]
  neg_mem' {f} hf g m := by
    change -f (g • m) = g • -f m
    rw [hf g m, smul_neg]

/-- A morphism of compact `G`-modules: a continuous `G`-equivariant homomorphism. -/
@[ext]
structure Hom (M N : CompactGModule.{u, v} G) where
  /-- The continuous homomorphism underlying a morphism of compact `G`-modules. -/
  hom : M →ₜ+ N
  map_smul (g : G) (m : M) : hom (g • m) = g • hom m

attribute [simp] Hom.map_smul

instance : Category (CompactGModule.{u, v} G) where
  Hom M N := Hom M N
  id M := ⟨ContinuousAddMonoidHom.id M, fun _ _ ↦ rfl⟩
  comp f g := ⟨g.hom.comp f.hom, fun x m ↦ by simp⟩

variable {M N P : CompactGModule.{u, v} G}

/-- Two morphisms of compact `G`-modules are equal when their underlying maps are. -/
@[ext]
lemma hom_ext {f f' : M ⟶ N} (h : f.hom = f'.hom) : f = f' := Hom.ext h

/-- Two morphisms of compact `G`-modules are equal when they agree at every point. -/
lemma hom_ext_iff' {f f' : M ⟶ N} : f = f' ↔ ∀ m, f.hom m = f'.hom m :=
  ⟨fun h _ ↦ h ▸ rfl, fun h ↦ hom_ext (ContinuousAddMonoidHom.ext h)⟩

/-- The morphism of compact `G`-modules given by a continuous equivariant homomorphism. -/
abbrev ofHom (f : M →ₜ+ N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) : M ⟶ N :=
  ⟨f, hf⟩

/-- The identity morphism has the identity as underlying map. -/
@[simp] lemma id_hom_apply (m : M) : (𝟙 M : M ⟶ M).hom m = m := rfl

/-- The underlying map of a composite is the composite of the underlying maps. -/
@[simp] lemma comp_hom_apply (f : M ⟶ N) (f' : N ⟶ P) (m : M) :
    (f ≫ f').hom m = f'.hom (f.hom m) := rfl

/-- The morphisms of compact `G`-modules are the equivariant continuous homomorphisms. -/
def homEquiv (M N : CompactGModule.{u, v} G) : (M ⟶ N) ≃ equivariantHoms M N where
  toFun f := ⟨f.hom, f.map_smul⟩
  invFun f := ⟨f.1, f.2⟩

instance (M N : CompactGModule.{u, v} G) : AddCommGroup (M ⟶ N) :=
  (homEquiv M N).addCommGroup

/-- The underlying map of a sum of morphisms is the sum of the underlying maps. -/
@[simp] lemma add_hom (f f' : M ⟶ N) : (f + f').hom = f.hom + f'.hom := rfl

/-- The underlying map of the zero morphism is zero. -/
@[simp] lemma zero_hom : (0 : M ⟶ N).hom = 0 := rfl

/-- The underlying map of the negative of a morphism is the negative of its underlying map. -/
@[simp] lemma neg_hom (f : M ⟶ N) : (-f).hom = -f.hom := rfl

instance : Preadditive (CompactGModule.{u, v} G) where
  add_comp _ _ _ f f' h :=
    hom_ext (ContinuousAddMonoidHom.ext fun m ↦ by
      simp only [comp_hom_apply, add_hom, ContinuousAddMonoidHom.add_apply, map_add])
  comp_add _ _ _ _ _ _ := hom_ext (ContinuousAddMonoidHom.ext fun _ ↦ rfl)

/-- The trivial group is a topological group. -/
instance _root_.PUnit.isTopologicalAddGroup : IsTopologicalAddGroup PUnit.{v + 1} where
  continuous_add := continuous_of_const fun _ _ ↦ Subsingleton.elim _ _
  continuous_neg := continuous_of_const fun _ _ ↦ Subsingleton.elim _ _

/-- The trivial group carries the trivial continuous action of any topological group. -/
instance _root_.PUnit.continuousSMul : ContinuousSMul G PUnit.{v + 1} :=
  ⟨continuous_of_const fun _ _ ↦ Subsingleton.elim _ _⟩

/-- The zero compact `G`-module. -/
abbrev zero : CompactGModule.{u, v} G := of PUnit.{v + 1}

/-- The zero compact `G`-module is a zero object. -/
lemma isZero_zero : IsZero (zero : CompactGModule.{u, v} G) where
  unique_to _ := ⟨⟨⟨0⟩, fun f ↦ hom_ext (ContinuousAddMonoidHom.ext fun _ ↦
    (congrArg f.hom (Subsingleton.elim _ 0)).trans (map_zero f.hom))⟩⟩
  unique_from _ := ⟨⟨⟨0⟩, fun _ ↦ hom_ext (ContinuousAddMonoidHom.ext fun _ ↦
    Subsingleton.elim _ _)⟩⟩

instance : HasZeroObject (CompactGModule.{u, v} G) := ⟨⟨zero, isZero_zero⟩⟩

/-- The underlying abelian group of a compact `G`-module. -/
@[simps]
def forgetToAddCommGrp : CompactGModule.{u, v} G ⥤ AddCommGrpCat.{v} where
  obj M := AddCommGrpCat.of M
  map f := AddCommGrpCat.ofHom f.hom.toAddMonoidHom

/-- The functor to abelian groups is additive. -/
instance : (forgetToAddCommGrp (G := G)).Additive where
  map_add := rfl

/-- The underlying topological space of a compact `G`-module. -/
@[simps]
def forgetToTop : CompactGModule.{u, v} G ⥤ TopCat.{v} where
  obj M := TopCat.of M
  map f := TopCat.ofHom f.hom.toContinuousMap

end CompactGModule

/-- The trivial action of the trivial group on an abelian group. -/
abbrev trivialDistribMulAction (M : Type v) [AddCommGroup M] : DistribMulAction PUnit.{1} M where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- Compact abelian groups, as compact modules over the trivial group. -/
abbrev CompactAddCommGrp := CompactGModule.{0, v} PUnit.{1}

namespace CompactGModule

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A compact `G`-module with its action forgotten, as a compact abelian group. -/
def forgetActionObj (M : CompactGModule.{u, v} G) : CompactAddCommGrp.{v} :=
  letI : DistribMulAction PUnit.{1} M := trivialDistribMulAction M
  haveI : ContinuousSMul PUnit.{1} M := ⟨continuous_snd⟩
  of M

/-- The functor from compact `G`-modules to compact abelian groups forgetting the action. -/
@[simps]
def forgetAction : CompactGModule.{u, v} G ⥤ CompactAddCommGrp.{v} where
  obj M := forgetActionObj M
  map f := ⟨f.hom, fun _ _ ↦ rfl⟩

/-- Forgetting the action is an additive functor. -/
instance : (forgetAction (G := G)).Additive where
  map_add := rfl

end CompactGModule

end Stacks.GroupHomology
