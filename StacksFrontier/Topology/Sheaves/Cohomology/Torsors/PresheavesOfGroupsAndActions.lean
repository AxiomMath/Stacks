module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Sets.Opens
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Torsors under a sheaf of groups on a topological space

Let `X` be a topological space and `G` a sheaf of (possibly non-commutative) groups on `X`. This
file defines, with presheaves given concretely by their sections and restriction maps, sheaves of
groups and of sets, actions of `G` on a sheaf of sets, pseudo `G`-torsors and `G`-torsors, their
morphisms, and the trivial `G`-torsor, and proves that a `G`-torsor is trivial if and only if it
has a global section.

## Main definitions

* `Stacks.SpaceTorsor.PresheafOfGroups`, `Stacks.SpaceTorsor.SheafOfGroups`: presheaves and
  sheaves of groups, the sheaf condition being that sections over an open `U` are in bijection
  with compatible families of sections over any open cover of `U`.
* `Stacks.SpaceTorsor.PresheafOfSets`, `Stacks.SpaceTorsor.SheafOfSets`: presheaves and sheaves
  of sets.
* `Stacks.SpaceTorsor.PresheafOfSets.StalkNonempty`: the stalk `F_x` is nonempty, that is,
  `F(U)` is nonempty for some open neighbourhood `U` of `x`.
* `Stacks.SpaceTorsor.Action`: a left action of `G` on `F`, compatible with restriction.
* `Stacks.SpaceTorsor.Action.IsPseudoTorsor`, `Stacks.SpaceTorsor.Action.IsTorsor`: pseudo
  `G`-torsors and `G`-torsors.
* `Stacks.SpaceTorsor.TorsorHom`: a morphism of pseudo `G`-torsors.
* `Stacks.SpaceTorsor.PresheafOfGroups.trivialAction`: the trivial `G`-torsor, `G` acting on
  itself by left multiplication.
* `Stacks.SpaceTorsor.Action.IsTrivial`: a torsor isomorphic to the trivial one.

## Main results

* `Stacks.SpaceTorsor.torsor_trivial_iff_global_section`: a `G`-torsor `F` is trivial if and
  only if `F(X)` is nonempty.

## References

* [Stacks Project, Tag 02FN](https://stacks.math.columbia.edu/tag/02FN)
* [Stacks Project, Tag 02FO](https://stacks.math.columbia.edu/tag/02FO)
* [Stacks Project, Tag 02FP](https://stacks.math.columbia.edu/tag/02FP)
-/

@[expose] public section

open TopologicalSpace

universe u v

namespace Stacks.SpaceTorsor

/-! ## Presheaves and sheaves of groups -/

/-- A presheaf of groups on a topological space `X`: for each open `U` a group
`obj U`, together with restriction group homomorphisms `res : obj U →* obj V`
for `V ≤ U`, satisfying functoriality. -/
@[sga "3 I 2.1.1" "special case"]
structure PresheafOfGroups (X : Type u) [TopologicalSpace X] where
  /-- The group of sections over an open set. -/
  obj : Opens X → Type v
  /-- Each `obj U` is a group. -/
  group : ∀ U, Group (obj U)
  /-- Restriction homomorphisms. -/
  res : ∀ {U V : Opens X}, V ≤ U → obj U →* obj V
  /-- Restricting along the identity is the identity. -/
  res_self : ∀ (U : Opens X) (g : obj U), res (le_refl U) g = g
  /-- Restriction is functorial. -/
  res_comp : ∀ {U V W : Opens X} (hWV : W ≤ V) (hVU : V ≤ U) (g : obj U),
    res hWV (res hVU g) = res (hWV.trans hVU) g

attribute [instance] PresheafOfGroups.group

namespace PresheafOfGroups

variable {X : Type u} [TopologicalSpace X] (G : PresheafOfGroups.{u, v} X)

/-- A family of local group sections over a cover agreeing on all common
refinements. -/
def CompatibleFamily {ι : Type u} (V : ι → Opens X) : Type _ :=
  { t : ∀ i, G.obj (V i) //
      ∀ i j (W : Opens X) (hWi : W ≤ V i) (hWj : W ≤ V j),
        G.res hWi (t i) = G.res hWj (t j) }

/-- The map sending a section over `U` to its family of restrictions to a cover. -/
def toCompatibleFamily {U : Opens X} {ι : Type u} (V : ι → Opens X)
    (hV : ∀ i, V i ≤ U) (g : G.obj U) : G.CompatibleFamily V :=
  ⟨fun i => G.res (hV i) g, by
    intro i j W hWi hWj
    rw [G.res_comp, G.res_comp]⟩

/-- The sheaf condition for a presheaf of groups: restriction to any open cover
is a bijection onto compatible families. -/
def IsSheaf : Prop :=
  ∀ (U : Opens X) (ι : Type u) (V : ι → Opens X) (hV : ∀ i, V i ≤ U),
    U = ⨆ i, V i → Function.Bijective (G.toCompatibleFamily V hV)

end PresheafOfGroups

/-- A sheaf of groups on `X` is a presheaf of groups satisfying the sheaf
condition. -/
structure SheafOfGroups (X : Type u) [TopologicalSpace X] extends
    PresheafOfGroups.{u, v} X where
  isSheaf : toPresheafOfGroups.IsSheaf

/-! ## Presheaves and sheaves of sets -/

/-- A presheaf of sets on a topological space `X`. -/
structure PresheafOfSets (X : Type u) [TopologicalSpace X] where
  /-- The set of sections over an open set. -/
  obj : Opens X → Type v
  /-- Restriction maps. -/
  res : ∀ {U V : Opens X}, V ≤ U → obj U → obj V
  /-- Restricting along the identity is the identity. -/
  res_self : ∀ (U : Opens X) (s : obj U), res (le_refl U) s = s
  /-- Restriction is functorial. -/
  res_comp : ∀ {U V W : Opens X} (hWV : W ≤ V) (hVU : V ≤ U) (s : obj U),
    res hWV (res hVU s) = res (hWV.trans hVU) s

namespace PresheafOfSets

variable {X : Type u} [TopologicalSpace X] (F : PresheafOfSets.{u, v} X)

/-- A family of local sections over a cover agreeing on all common refinements. -/
def CompatibleFamily {ι : Type u} (V : ι → Opens X) : Type _ :=
  { t : ∀ i, F.obj (V i) //
      ∀ i j (W : Opens X) (hWi : W ≤ V i) (hWj : W ≤ V j),
        F.res hWi (t i) = F.res hWj (t j) }

/-- The map sending a section over `U` to its family of restrictions to a cover. -/
def toCompatibleFamily {U : Opens X} {ι : Type u} (V : ι → Opens X)
    (hV : ∀ i, V i ≤ U) (s : F.obj U) : F.CompatibleFamily V :=
  ⟨fun i => F.res (hV i) s, by
    intro i j W hWi hWj
    rw [F.res_comp, F.res_comp]⟩

/-- The sheaf condition for a presheaf of sets: restriction to any open cover is
a bijection onto compatible families. -/
def IsSheaf : Prop :=
  ∀ (U : Opens X) (ι : Type u) (V : ι → Opens X) (hV : ∀ i, V i ≤ U),
    U = ⨆ i, V i → Function.Bijective (F.toCompatibleFamily V hV)

/-- The stalk `F_x = colim_{U ∋ x} F(U)` is nonempty: some `F(U)` with `U` an open
neighbourhood of `x` is nonempty. -/
def StalkNonempty (x : X) : Prop :=
  ∃ U : Opens X, x ∈ U ∧ Nonempty (F.obj U)

end PresheafOfSets

/-- A sheaf of sets on `X` is a presheaf of sets satisfying the sheaf condition. -/
structure SheafOfSets (X : Type u) [TopologicalSpace X] extends
    PresheafOfSets.{u, v} X where
  isSheaf : toPresheafOfSets.IsSheaf

/-! ## Actions of a sheaf of groups on a sheaf of sets -/

/-- An action of a presheaf of groups `G` on a presheaf of sets `F`: for each open `U` a left
action of `G(U)` on `F(U)`, compatible with the restriction maps. -/
structure Action {X : Type u} [TopologicalSpace X]
    (G : PresheafOfGroups.{u, v} X) (F : PresheafOfSets.{u, v} X) where
  /-- The action map over an open `U`. -/
  act : ∀ {U : Opens X}, G.obj U → F.obj U → F.obj U
  /-- The identity acts trivially. -/
  one_act : ∀ {U : Opens X} (s : F.obj U), act (1 : G.obj U) s = s
  /-- Compatibility of the action with the group multiplication. -/
  mul_act : ∀ {U : Opens X} (g h : G.obj U) (s : F.obj U),
    act (g * h) s = act g (act h s)
  /-- Compatibility of the action with restriction. -/
  res_act : ∀ {U V : Opens X} (hVU : V ≤ U) (g : G.obj U) (s : F.obj U),
    F.res hVU (act g s) = act (G.res hVU g) (F.res hVU s)

/-! ## Pseudo torsors and torsors -/

/-- A left action of a group `H` on a set `S` is *simply transitive* if `S` is nonempty and for
every pair `(s, t)` there is a unique `h ∈ H` with `h · s = t`. -/
def IsSimplyTransitive {H : Type*} [Group H] {S : Type*}
    (smul : H → S → S) : Prop :=
  Nonempty S ∧ ∀ s t : S, ∃! h : H, smul h s = t

/-- A presheaf of sets `F` with an action `a` of `G` is a *pseudo `G`-torsor* if for every open
`U` with `F(U)` nonempty, the action of `G(U)` on `F(U)` is simply transitive. -/
def Action.IsPseudoTorsor {X : Type u} [TopologicalSpace X]
    {G : PresheafOfGroups.{u, v} X} {F : PresheafOfSets.{u, v} X}
    (a : Action G F) : Prop :=
  ∀ U : Opens X, Nonempty (F.obj U) →
    IsSimplyTransitive (H := G.obj U) (S := F.obj U) (fun g s => a.act g s)

/-- A pseudo `G`-torsor is a *`G`-torsor* if in addition all stalks `F_x` are nonempty. -/
@[sga "4½ Arcata 1.6.6" "topological space"]
def Action.IsTorsor {X : Type u} [TopologicalSpace X]
    {G : PresheafOfGroups.{u, v} X} {F : PresheafOfSets.{u, v} X}
    (a : Action G F) : Prop :=
  a.IsPseudoTorsor ∧ ∀ x : X, F.StalkNonempty x

/-! ## Morphisms of (pseudo) torsors -/

/-- A morphism of presheaves of sets: a family of maps `F(U) → F'(U)` commuting
with restriction. -/
structure PresheafOfSets.Hom {X : Type u} [TopologicalSpace X]
    (F F' : PresheafOfSets.{u, v} X) where
  /-- The component map over an open `U`. -/
  app : ∀ U : Opens X, F.obj U → F'.obj U
  /-- Naturality with respect to restriction. -/
  naturality : ∀ {U V : Opens X} (hVU : V ≤ U) (s : F.obj U),
    app V (F.res hVU s) = F'.res hVU (app U s)

/-- A morphism of pseudo `G`-torsors `(F, a) → (F', a')`: a morphism of the underlying presheaves
of sets that is compatible with the `G`-actions. -/
structure TorsorHom {X : Type u} [TopologicalSpace X]
    {G : PresheafOfGroups.{u, v} X} {F F' : PresheafOfSets.{u, v} X}
    (a : Action G F) (a' : Action G F') extends F.Hom F' where
  /-- Equivariance: the map commutes with the `G`-action. -/
  map_act : ∀ {U : Opens X} (g : G.obj U) (s : F.obj U),
    app U (a.act g s) = a'.act g (app U s)

/-- A morphism of (pseudo) torsors is an isomorphism if every component is a bijection. -/
def TorsorHom.IsIso {X : Type u} [TopologicalSpace X]
    {G : PresheafOfGroups.{u, v} X} {F F' : PresheafOfSets.{u, v} X}
    {a : Action G F} {a' : Action G F'} (φ : TorsorHom a a') : Prop :=
  ∀ U : Opens X, Function.Bijective (φ.app U)

/-- Two pseudo `G`-torsors are isomorphic if there is a morphism between them
that is an isomorphism. -/
def Action.Iso {X : Type u} [TopologicalSpace X]
    {G : PresheafOfGroups.{u, v} X} {F F' : PresheafOfSets.{u, v} X}
    (a : Action G F) (a' : Action G F') : Prop :=
  ∃ φ : TorsorHom a a', φ.IsIso

/-! ## The trivial torsor -/

/-- The underlying presheaf of sets of a presheaf of groups `G`: `G` viewed as a
presheaf of sets by forgetting the group structure. -/
def PresheafOfGroups.toPresheafOfSets {X : Type u} [TopologicalSpace X]
    (G : PresheafOfGroups.{u, v} X) : PresheafOfSets.{u, v} X where
  obj U := G.obj U
  res hVU := G.res hVU
  res_self := G.res_self
  res_comp := G.res_comp

/-- The trivial `G`-torsor: `G` acting on itself by left multiplication. -/
def PresheafOfGroups.trivialAction {X : Type u} [TopologicalSpace X]
    (G : PresheafOfGroups.{u, v} X) : Action G G.toPresheafOfSets where
  act {U} g h := let h' : G.obj U := h; g * h'
  one_act {U} s := let s' : G.obj U := s; one_mul s'
  mul_act {U} g h s := let s' : G.obj U := s; mul_assoc g h s'
  res_act {U V} hVU g s := by
    change G.res hVU (g * (id s : G.obj U)) = G.res hVU g * G.res hVU (id s : G.obj U)
    rw [map_mul]

/-- A `G`-torsor `(F, a)` is *trivial* if it is isomorphic, as a pseudo `G`-torsor, to the
trivial torsor `G`. -/
def Action.IsTrivial {X : Type u} [TopologicalSpace X]
    {G : PresheafOfGroups.{u, v} X} {F : PresheafOfSets.{u, v} X}
    (a : Action G F) : Prop :=
  G.trivialAction.Iso a

/-- Let `X` be a topological space, `G` a sheaf of (possibly non-commutative) groups on `X`, and
`F` a sheaf of sets with an action `a` of `G` making it a `G`-torsor. Then `F` is trivial if and
only if `F(X)` is nonempty. -/
@[stacks 02FP]
theorem torsor_trivial_iff_global_section
    {X : Type u} [TopologicalSpace X]
    (G : SheafOfGroups.{u, v} X) (F : SheafOfSets.{u, v} X)
    (a : Action G.toPresheafOfGroups F.toPresheafOfSets)
    (htorsor : a.IsTorsor) :
    a.IsTrivial ↔ Nonempty (F.obj ⊤) := by
  refine ⟨fun ⟨φ, _⟩ => ⟨φ.app ⊤ (1 : G.obj ⊤)⟩, ?_⟩
  rintro ⟨s₀⟩
  set sU : ∀ U : Opens X, F.toPresheafOfSets.obj U := fun U =>
    F.toPresheafOfSets.res le_top s₀
  have hres : ∀ {U V : Opens X} (hVU : V ≤ U),
      F.toPresheafOfSets.res hVU (sU U) = sU V := fun hVU =>
    F.toPresheafOfSets.res_comp hVU le_top s₀
  refine ⟨{
    app := fun U g => a.act g (sU U)
    naturality := ?_
    map_act := fun {U} g h => a.mul_act g h (sU U) }, fun U => ?_⟩
  · intro U V hVU g
    change a.act (G.toPresheafOfGroups.res hVU g) (sU V)
      = F.toPresheafOfSets.res hVU (a.act g (sU U))
    rw [a.res_act hVU g (sU U), hres hVU]
  · obtain ⟨_, hst⟩ := htorsor.1 U ⟨sU U⟩
    refine ⟨fun g g' hgg => ?_, fun t => (hst (sU U) t).exists⟩
    obtain ⟨_, _, huniq⟩ := hst (sU U) (a.act g (sU U))
    exact (huniq g rfl).trans (huniq g' hgg.symm).symm

end Stacks.SpaceTorsor
