module

public import Mathlib.Topology.Homeomorph.Lemmas
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
public import StacksFrontier.Topology.Irreducible.GenericPoints

/-!
# Generic points under injective maps and open embeddings

In a sober `T0` space the generic points of the irreducible components are the points with no
proper generalization. That description transports along generalizing maps, and it is also
reflected by an injective continuous map; consequently finiteness of the set of irreducible
components passes to the source of an open embedding.

## Main results

* `genericPoints_image_of_generalizingMap` transports generic points along a generalizing
  map.
* `mem_genericPoints_of_mem_genericPoints_image` reflects generic points along an injective
  continuous map.
* `Set.Finite.irreducibleComponents_of_isOpenEmbedding` transports finiteness of the set of
  irreducible components along an open embedding.
-/

@[expose] public section

open Topology

/-- A generalizing map sends generic points of irreducible components to generic points of
irreducible components. -/
theorem genericPoints_image_of_generalizingMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T0Space X] [T0Space Y] [QuasiSober X] [QuasiSober Y]
    (f : X → Y) (hf : GeneralizingMap f) {x : X} (hx : x ∈ genericPoints X) :
    f x ∈ genericPoints Y :=
  AlgebraicGeometry.mem_genericPoints_of_generalizingMap hf hx

/-- A point whose image under an injective continuous map is a generic point of an irreducible
component is itself a generic point of an irreducible component. -/
theorem mem_genericPoints_of_mem_genericPoints_image {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T0Space X] [QuasiSober X] [T0Space Y] [QuasiSober Y]
    (f : X → Y) (hf : Continuous f) (hinj : Function.Injective f) {x : X}
    (hx : f x ∈ genericPoints Y) : x ∈ genericPoints X :=
  (TopologicalSpace.mem_genericPoints_iff_forall_specializes_eq x).2 fun _ hy =>
    hinj ((TopologicalSpace.mem_genericPoints_iff_forall_specializes_eq (f x)).1 hx _ (hy.map hf))

/-- A space that embeds openly into a space with finitely many irreducible components has
finitely many irreducible components. -/
theorem Set.Finite.irreducibleComponents_of_isOpenEmbedding {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T0Space X] [T0Space Y] [QuasiSober X]
    [QuasiSober Y] (f : X → Y) (hf : IsOpenEmbedding f)
    (hY : (irreducibleComponents Y).Finite) : (irreducibleComponents X).Finite := by
  have : Finite (genericPoints Y) := genericPoints.finite hY
  have : Finite (genericPoints X) :=
    Finite.of_injective (fun x : genericPoints X =>
      (⟨f x.1, genericPoints_image_of_generalizingMap f hf.generalizingMap x.2⟩ : genericPoints Y))
      fun _ _ h => Subtype.ext (hf.injective (congrArg Subtype.val h))
  exact Finite.of_equiv (genericPoints X) (genericPoints.equiv (α := X))

end
