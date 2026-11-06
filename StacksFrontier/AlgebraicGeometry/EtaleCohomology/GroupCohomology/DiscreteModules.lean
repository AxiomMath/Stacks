module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.MulAction
public import StacksFrontier.Homology.Injectives.Module.ContinuousGroupModules
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.DiscreteTopology

/-!
# Discrete modules over a topological group

Let `G` be a topological group. A `G`-module, also called a discrete `G`-module, is an abelian
group `M` with a left action of `G` by group homomorphisms which is continuous when `M` carries
the discrete topology; a morphism of `G`-modules is a `G`-equivariant homomorphism. Over a ring
`R` the same definition with `R`-linear maps and `R`-module maps gives the `R`-`G`-modules. The
two categories are `Mod_G` and `Mod_{R,G}`, and `Mod_{ℤ,G} = Mod_G`.

Continuity of the action for the discrete topology is equivalent to openness of the stabilizer
of every element, which is how the condition is usually checked.

## Main definitions

* `Stacks.GroupCohomology.actionOfRepresentation`: the action of `G` on an `R`-module by
  `R`-linear maps described by a representation.
* `Stacks.GroupCohomology.ofRepresentation`: an `R`-`G`-module, that is, an `R`-module with a
  continuous action of `G` by `R`-linear maps for the discrete topology.
* `Stacks.GroupCohomology.ofDistribMulAction`: a `G`-module, that is, an abelian group with a
  continuous action of `G` by group homomorphisms for the discrete topology.
* `Stacks.GroupCohomology.homEquiv` and `Stacks.GroupCohomology.gModuleHomEquiv`: the morphisms
  of `R`-`G`-modules are the `G`-equivariant `R`-linear maps, and the morphisms of `G`-modules
  are the `G`-equivariant homomorphisms.

## Main results

* `Stacks.GroupCohomology.isContinuous_actionOfRepresentation_iff` and
  `Stacks.GroupCohomology.isContinuous_ofDistribMulAction_iff`: the action is continuous for the
  discrete topology if and only if the stabilizer of every element is open.
* `Stacks.GroupCohomology.isOpen_stabilizer`: the stabilizer of an element of an `R`-`G`-module
  is open.

## Implementation notes

The categories `Mod_{R,G}` and `Mod_G` are `Stacks.Injectives.ContinuousModule R G` and its
value at `R = ℤ`: the full subcategory of `CategoryTheory.Action (ModuleCat R) G` on the objects
whose action is continuous for the topology obtained from the forgetful functor to `TopCat`
through `TopCat.discrete`. So `CategoryTheory.Action.IsContinuous` says exactly that
`G × M → M` is continuous when `M` is discrete, `CategoryTheory.ContAction.IsDiscrete` holds by
`rfl`, and the equality `Mod_{ℤ,G} = Mod_G` is definitional: the `G`-module declarations below
are literally about `Stacks.Injectives.ContinuousModule ℤ G`. The tag for the categories is
recorded against that declaration.

Objects are described by a `Representation R G M` rather than by a bare action map, which is the
same data: a monoid homomorphism from `G` to the `R`-linear endomorphisms of `M`.

## References

* [Stacks Project, Tag 04JP](https://stacks.math.columbia.edu/tag/04JP)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Stacks.GroupCohomology

open scoped Stacks.DiscreteModuleTopology

section RGModule

variable (R : Type u) [Ring R] (G : Type v) [Group G] [TopologicalSpace G]
  (M : Type w) [AddCommGroup M] [Module R M]

/-- The left action of `G` on an `R`-module `M` by `R`-linear maps given by a representation,
as an object of `CategoryTheory.Action (ModuleCat R) G`. -/
abbrev actionOfRepresentation (ρ : Representation R G M) : Action (ModuleCat.{w} R) G where
  V := ModuleCat.of R M
  ρ := (ModuleCat.endRingEquiv (ModuleCat.of R M)).symm.toMonoidHom.comp ρ

variable {R G M}

omit [TopologicalSpace G] in
/-- The action of a group element on an element of `M` is the value of the representation. -/
lemma actionOfRepresentation_ρ_hom (ρ : Representation R G M) (g : G) (x : M) :
    ((actionOfRepresentation R G M ρ).ρ g).asHom.hom x = ρ g x := rfl

/-- **The action of `G` on a discrete `R`-module is continuous exactly when the stabilizers are
open.** This is the standard reformulation of the continuity condition defining an
`R`-`G`-module. -/
theorem isContinuous_actionOfRepresentation_iff [IsTopologicalGroup G]
    (ρ : Representation R G M) :
    (actionOfRepresentation R G M ρ).IsContinuous ↔ ∀ x : M, IsOpen {g : G | ρ g x = x} :=
  continuousSMul_iff_stabilizer_isOpen

/-- **Stacks Project, Tag 04JP.** An `R`-`G`-module: an `R`-module `M` together with a left
action of `G` on `M` by `R`-linear maps which is continuous when `M` is given the discrete
topology. -/
@[stacks 04JP "R-G-modules"]
def ofRepresentation (ρ : Representation R G M)
    (h : (actionOfRepresentation R G M ρ).IsContinuous) :
    Stacks.Injectives.ContinuousModule.{u, v, w} R G :=
  ⟨⟨actionOfRepresentation R G M ρ, h⟩, ⟨rfl⟩⟩

/-- The underlying `R`-module of `Stacks.GroupCohomology.ofRepresentation` is the given one. -/
@[simp] lemma ofRepresentation_V (ρ : Representation R G M)
    (h : (actionOfRepresentation R G M ρ).IsContinuous) :
    (ofRepresentation ρ h).obj.obj.V = ModuleCat.of R M := rfl

/-- The action on `Stacks.GroupCohomology.ofRepresentation` is the given representation. -/
@[simp] lemma ofRepresentation_ρ_hom (ρ : Representation R G M)
    (h : (actionOfRepresentation R G M ρ).IsContinuous) (g : G) (x : M) :
    (((ofRepresentation ρ h).obj.obj.ρ g).asHom.hom x : M) = ρ g x := rfl

variable (R G)

/-- The stabilizer of an element of an `R`-`G`-module is an open subgroup of `G`: the action is
continuous and the module is discrete. -/
@[sga "4 IV 2.7.2" "partial"]
theorem isOpen_stabilizer (X : Stacks.Injectives.ContinuousModule.{u, v, w} R G)
    (x : X.obj.obj.V) : IsOpen {g : G | (X.obj.obj.ρ g).asHom.hom x = x} := by
  have hc : ContinuousSMul G
      ((forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj X.obj.obj) := X.obj.property
  have hd : DiscreteTopology
      ((forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj X.obj.obj) := ⟨rfl⟩
  exact stabilizer_isOpen G
    (show (forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj X.obj.obj from x)

/-- **Stacks Project, Tag 04JP.** A morphism of `R`-`G`-modules is a `G`-equivariant `R`-module
map. -/
@[stacks 04JP "morphisms of R-G-modules"]
def homEquiv (X Y : Stacks.Injectives.ContinuousModule.{u, v, w} R G) :
    (X ⟶ Y) ≃ {f : X.obj.obj.V →ₗ[R] Y.obj.obj.V // ∀ (g : G) (x : X.obj.obj.V),
      f ((X.obj.obj.ρ g).asHom.hom x) = (Y.obj.obj.ρ g).asHom.hom (f x)} where
  toFun f := ⟨f.hom.hom.hom.hom, fun g x => ConcreteCategory.congr_hom (f.hom.hom.comm g) x⟩
  invFun f := ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom f.1
      comm := fun g => ModuleCat.hom_ext (LinearMap.ext fun x => f.2 g x) })
  left_inv f := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    rfl
  right_inv f := Subtype.ext rfl

end RGModule

section GModule

/-- A homomorphism of abelian groups between `ℤ`-modules is `ℤ`-linear: the `ℤ`-module structure
on an abelian group is unique. -/
def intLinearMapOfAddMonoidHom {A B : Type w} [AddCommGroup A] [Module ℤ A] [AddCommGroup B]
    [Module ℤ B] (f : A →+ B) : A →ₗ[ℤ] B where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by simpa using map_intCast_smul f ℤ ℤ c x

variable (G : Type v) [Group G] [TopologicalSpace G]
  (M : Type w) [AddCommGroup M] [DistribMulAction G M]

/-- The left action of `G` on an abelian group `M` by group homomorphisms, as an object of
`CategoryTheory.Action (ModuleCat ℤ) G`. -/
abbrev actionOfDistribMulAction : Action (ModuleCat.{w} ℤ) G :=
  actionOfRepresentation ℤ G M (Representation.ofDistribMulAction ℤ G M)

variable {G M}

/-- **The action of `G` on a discrete abelian group is continuous exactly when the stabilizers
are open.** This is the standard reformulation of the continuity condition defining a
`G`-module. -/
@[sga "3 VIIB 2.5" "special case", sga "4 IV 2.7.2" "special case"]
theorem isContinuous_ofDistribMulAction_iff [IsTopologicalGroup G] :
    (actionOfDistribMulAction G M).IsContinuous ↔ ∀ x : M, IsOpen {g : G | g • x = x} :=
  isContinuous_actionOfRepresentation_iff _

/-- **Stacks Project, Tag 04JP.** A `G`-module, or discrete `G`-module: an abelian group `M`
together with a left action of `G` on `M` by group homomorphisms which is continuous when `M` is
given the discrete topology. -/
@[stacks 04JP "G-modules"]
def ofDistribMulAction (h : (actionOfDistribMulAction G M).IsContinuous) :
    Stacks.Injectives.ContinuousModule.{0, v, w} ℤ G :=
  ofRepresentation (Representation.ofDistribMulAction ℤ G M) h

/-- The action on `Stacks.GroupCohomology.ofDistribMulAction` is the given one. -/
@[simp] lemma ofDistribMulAction_ρ_hom (h : (actionOfDistribMulAction G M).IsContinuous)
    (g : G) (x : M) : (((ofDistribMulAction h).obj.obj.ρ g).asHom.hom x : M) = g • x := rfl

variable (G)

/-- **Stacks Project, Tag 04JP.** A morphism of `G`-modules is a `G`-equivariant homomorphism of
abelian groups. -/
@[stacks 04JP "morphisms of G-modules"]
def gModuleHomEquiv (X Y : Stacks.Injectives.ContinuousModule.{0, v, w} ℤ G) :
    (X ⟶ Y) ≃ {f : X.obj.obj.V →+ Y.obj.obj.V // ∀ (g : G) (x : X.obj.obj.V),
      f ((X.obj.obj.ρ g).asHom.hom x) = (Y.obj.obj.ρ g).asHom.hom (f x)} where
  toFun f := ⟨f.hom.hom.hom.hom.toAddMonoidHom,
    fun g x => ConcreteCategory.congr_hom (f.hom.hom.comm g) x⟩
  invFun f := ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom (intLinearMapOfAddMonoidHom f.1)
      comm := fun g => ModuleCat.hom_ext (LinearMap.ext fun x => f.2 g x) })
  left_inv f := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    rfl
  right_inv f := Subtype.ext rfl

end GModule

-- The category `Mod_{R,G}` of `R`-`G`-modules; its value at `R = ℤ` is the category `Mod_G` of
-- `G`-modules.
add_to_stacks 04JP "the categories Mod_G and Mod_{R,G}" Stacks.Injectives.ContinuousModule

end Stacks.GroupCohomology

end
