module

public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Maps.Basic
public import StacksFrontier.Topology.Algebra.AutomorphismGroup
public import StacksFrontier.Topology.Algebra.ProfiniteGroup
public import StacksCore.Tactic.StacksAttribute

/-!
# Automorphisms of a set-valued functor

The automorphism group of a set-valued functor embeds as the closed subgroup of the product of
the automorphism groups of its values consisting of the families compatible with every morphism.
When all the values are finite, its canonical topology is profinite.

## Main definitions

* `CategoryTheory.componentEmbedding` is the componentwise homomorphism from natural
  automorphisms.
* `CategoryTheory.automorphismProductTopology` is the product of the pointwise-convergence
  topologies on the automorphism groups of the values.
* `CategoryTheory.functorAutomorphismTopology` is the topology induced by the component
  embedding.
* `CategoryTheory.functorAutomorphismIsTopologicalGroup` gives this topology its
  topological-group structure.

## Main results

* `CategoryTheory.isClosedEmbedding_componentEmbedding` says that the component embedding is
  closed.
* `CategoryTheory.isProfiniteGrp_functorAutomorphismTopology` says that this automorphism group
  is profinite when every value of the functor is finite.

## Implementation notes

For an arbitrary set-valued functor, every value is given the discrete topology and its
automorphism group the pointwise-convergence topology. The closed-subgroup and profiniteness
assertions use this same induced topology.

## References

* [Stacks Project, Tag 0BMR](https://stacks.math.columbia.edu/tag/0BMR)
-/

@[expose] public section

open CategoryTheory Topology

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The homomorphism which evaluates a natural automorphism at every object. -/
public def componentEmbedding (F : C ⥤ Type w) :
    Aut F →* ∀ X, Equiv.Perm (F.obj X) :=
  MonoidHom.mk' (fun σ X ↦ (σ.asIso.app X).toEquiv) (fun _ _ ↦ rfl)

/-- The product of the pointwise-convergence topologies on the automorphism groups of the values
of a set-valued functor. -/
@[instance_reducible]
public def automorphismProductTopology (F : C ⥤ Type w) :
    TopologicalSpace (∀ X, Equiv.Perm (F.obj X)) := by
  letI (X : C) : TopologicalSpace (F.obj X) := ⊥
  letI (X : C) : DiscreteTopology (F.obj X) := ⟨rfl⟩
  letI (X : C) : TopologicalSpace (Equiv.Perm (F.obj X)) := autTopology
  exact inferInstance

/-- The topology on the automorphism group of a functor induced by evaluation at every object. -/
@[instance_reducible]
public def functorAutomorphismTopology (F : C ⥤ Type w) : TopologicalSpace (Aut F) :=
  TopologicalSpace.induced (componentEmbedding F) (automorphismProductTopology F)

/-- The topology induced by componentwise evaluation makes the automorphism group of a
set-valued functor a topological group. -/
public theorem functorAutomorphismIsTopologicalGroup (F : C ⥤ Type w) :
    @IsTopologicalGroup (Aut F) (functorAutomorphismTopology F) _ := by
  let (X : C) : TopologicalSpace (F.obj X) := ⊥
  let (X : C) : DiscreteTopology (F.obj X) := ⟨rfl⟩
  let (X : C) : TopologicalSpace (Equiv.Perm (F.obj X)) := autTopology
  let : TopologicalSpace (Aut F) :=
    TopologicalSpace.induced (componentEmbedding F) inferInstance
  change @IsTopologicalGroup (Aut F)
    (TopologicalSpace.induced (componentEmbedding F) inferInstance) _
  have hcomp : Continuous (componentEmbedding F) := continuous_induced_dom
  have heval (X : C) : Continuous (fun σ : Aut F => (σ.asIso.app X).toEquiv) :=
    (continuous_apply X).comp hcomp
  have hcont {α : Type (max u w)} [TopologicalSpace α] (f : α → Aut F)
      (h : ∀ X, Continuous fun a ↦ ((f a).asIso.app X).toEquiv) : Continuous f :=
    continuous_induced_rng.mpr (continuous_pi_iff.mpr h)
  refine @IsTopologicalGroup.mk _ _ _ ⟨hcont _ fun X ↦ ?_⟩ ⟨hcont _ fun X ↦ ?_⟩
  · exact (isTopologicalGroup_aut (E := F.obj X)).continuous_mul.comp
      (((heval X).comp continuous_fst).prodMk ((heval X).comp continuous_snd))
  · exact (show Continuous (fun e : Equiv.Perm (F.obj X) => e⁻¹) from
      continuous_perm_inv).comp (heval X)

/-- The componentwise map identifies the automorphism group of a set-valued functor with a
closed subgroup of the product of the automorphism groups of its values. -/
@[stacks 0BMR "closed subgroup"]
public lemma isClosedEmbedding_componentEmbedding (F : C ⥤ Type w) :
    @IsClosedEmbedding (Aut F) (∀ X, Equiv.Perm (F.obj X))
      (functorAutomorphismTopology F) (automorphismProductTopology F)
      (componentEmbedding F) := by
  let (X : C) : TopologicalSpace (F.obj X) := ⊥
  let (X : C) : DiscreteTopology (F.obj X) := ⟨rfl⟩
  let (X : C) : TopologicalSpace (Equiv.Perm (F.obj X)) := autTopology
  let : TopologicalSpace (Aut F) :=
    TopologicalSpace.induced (componentEmbedding F) inferInstance
  change IsClosedEmbedding (componentEmbedding F)
  rw [isClosedEmbedding_iff]
  constructor
  · refine ⟨Topology.IsInducing.induced _, ?_⟩
    intro σ τ h
    apply Aut.ext
    apply Iso.ext
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun e ↦ e x) (congrFun h X)
  · have hrange : Set.range (componentEmbedding F) =
        ⋂ X, ⋂ Y, ⋂ f : X ⟶ Y, ⋂ x : F.obj X,
          {g | F.map f (g X x) = g Y (F.map f x)} := by
      ext g
      simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨σ, rfl⟩ X Y f x
        change F.map f (ConcreteCategory.hom (σ.asIso.hom.app X) x) =
          ConcreteCategory.hom (σ.asIso.hom.app Y) (F.map f x)
        simpa only [types_comp_apply] using
          ConcreteCategory.congr_hom (σ.asIso.hom.naturality f).symm x
      · intro h
        let σ : Aut F := .of <| NatIso.ofComponents (fun X ↦ (g X).toIso) (fun {X Y} f ↦ by
          ext x
          exact (h X Y f x).symm)
        exact ⟨σ, funext fun X ↦ Equiv.ext fun _ ↦ rfl⟩
    rw [hrange]
    have heval (Z : C) (z : F.obj Z) :
        Continuous (fun g : ∀ X, Equiv.Perm (F.obj X) ↦ g Z z) :=
      ((continuous_apply z).comp continuous_induced_dom).comp (continuous_apply Z)
    refine isClosed_iInter fun X ↦ isClosed_iInter fun Y ↦ isClosed_iInter fun f ↦
      isClosed_iInter fun x ↦ isClosed_eq ?_ ?_
    · exact continuous_of_discreteTopology.comp (heval X x)
    · exact heval Y (F.map f x)

/-- If every value of a set-valued functor is finite, its automorphism group with the topology
induced by componentwise evaluation is a profinite group. -/
@[stacks 0BMR "profinite group"]
public lemma isProfiniteGrp_functorAutomorphismTopology (F : C ⥤ Type w)
    [∀ X, Finite (F.obj X)] :
    @Stacks.Chapter05.Tag_0BR1.IsProfiniteTop (Aut F)
      (functorAutomorphismTopology F) := by
  let (X : C) : TopologicalSpace (F.obj X) := ⊥
  let (X : C) : DiscreteTopology (F.obj X) := ⟨rfl⟩
  let (X : C) : TopologicalSpace (Equiv.Perm (F.obj X)) := autTopology
  let (X : C) : Finite (Equiv.Perm (F.obj X)) := Equiv.finite_left
  let (X : C) : T2Space (Equiv.Perm (F.obj X)) :=
    (⟨Topology.IsInducing.induced _, Equiv.coe_fn_injective⟩ :
      IsEmbedding (fun e : Equiv.Perm (F.obj X) ↦ (e : F.obj X → F.obj X))).t2Space
  let : TopologicalSpace (Aut F) :=
    TopologicalSpace.induced (componentEmbedding F) inferInstance
  let : IsTopologicalGroup (Aut F) := functorAutomorphismIsTopologicalGroup F
  change Stacks.Chapter05.Tag_0BR1.IsProfiniteTop (Aut F)
  have h : IsClosedEmbedding (componentEmbedding F) := isClosedEmbedding_componentEmbedding F
  exact ⟨h.compactSpace, h.isEmbedding.t2Space,
    h.isEmbedding.toHomeomorph.symm.totallyDisconnectedSpace⟩

end CategoryTheory
