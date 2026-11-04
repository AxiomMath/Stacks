module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Connected.FiniteFibres

/-!
# Connected components after a finite extension of the base field

Let `K/k` be a finite extension of fields and let `X` be a scheme over `k`. The projection
`p : X_K → X` is a finite, universally open morphism, so topologically it is an open and closed
map with finite fibres. For such a map the image of a connected component is again a connected
component, and this gives the behaviour of connected components under a finite extension of the
base field.

## Main results

* `finite_fibre_image_connectedComponent`: for a continuous, open and closed map with finite
  fibres, the image of the connected component of a point is the connected component of its
  image.
* `AlgebraicGeometry.baseChange_image_connectedComponent_eq_connectedComponent`
  (Stacks 07VM): for a finite extension `K/k` and a scheme `X` over `k`, the projection
  `X_K → X` carries each connected component of `X_K` onto a connected component of `X`.

## Implementation notes

A scheme over `k` is represented by its structure morphism `f : X ⟶ Spec k`, and `X_K` is the
pullback of `f` along `Spec K ⟶ Spec k`, with `p` the first projection. A connected component of
`X_K` is the connected component `connectedComponent t` of one of its points `t`.

The topological reduction to a connected target is performed by restricting the map over the
connected component of the image point: the restriction is again open and closed with finite
fibres, and the component upstairs is a connected component of the restricted source.

## References

* [Stacks Project, Tag 07VM](https://stacks.math.columbia.edu/tag/07VM)
-/

@[expose] public section

universe u

open Set

/-- A continuous map which is open and closed and has finite fibres sends the connected
component of a point onto the connected component of its image. -/
@[ega "IV 2.3.6" "(ii), special case"]
public theorem finite_fibre_image_connectedComponent {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hcont : Continuous f)
    (hopen : IsOpenMap f) (hclosed : IsClosedMap f) (hfin : ∀ y, (f ⁻¹' {y}).Finite) (x : X) :
    f '' connectedComponent x = connectedComponent (f x) := by
  set B : Set Y := connectedComponent (f x) with hB
  have hxB : f x ∈ B := mem_connectedComponent
  have hsub : connectedComponent x ⊆ f ⁻¹' B :=
    fun z hz => hcont.image_connectedComponent_subset x (mem_image_of_mem f hz)
  have hmaps : ∀ a : X, a ∈ f ⁻¹' B → f a ∈ B := fun _ ha => ha
  -- The restriction of `f` to the part lying over the connected component `B` of `f x`.
  have hgopen : IsOpenMap (Subtype.map f hmaps) := hopen.restrictPreimage B
  have hgclosed : IsClosedMap (Subtype.map f hmaps) := hclosed.restrictPreimage B
  have : Nonempty (f ⁻¹' B) := ⟨⟨x, hxB⟩⟩
  have : Nonempty B := ⟨⟨f x, hxB⟩⟩
  have hBconn : ConnectedSpace B := Subtype.connectedSpace isConnected_connectedComponent
  have hfib : (Subtype.map f hmaps ⁻¹' {(⟨f x, hxB⟩ : B)}).Finite := by
    refine Set.Finite.subset ((hfin (f x)).preimage Subtype.val_injective.injOn) ?_
    intro z hz
    simp only [mem_preimage, mem_singleton_iff] at hz ⊢
    exact congrArg Subtype.val hz
  obtain ⟨-, -, -, -, -, himg⟩ :=
    connectedComponent_clopen_and_image_eq_univ (Subtype.map f hmaps) hBconn hgopen hgclosed
      ⟨f x, hxB⟩ hfib
      (connectedComponent (⟨x, hsub mem_connectedComponent⟩ : (f ⁻¹' B))) ⟨_, rfl⟩
  -- Since `connectedComponent x` lies in `f ⁻¹' B`, it is a connected component there too.
  have hcc : Subtype.val '' connectedComponent (⟨x, hsub mem_connectedComponent⟩ : (f ⁻¹' B))
      = connectedComponent x := by
    rw [← connectedComponentIn_eq_image (hsub mem_connectedComponent)]
    refine subset_antisymm (isPreconnected_connectedComponentIn.subset_connectedComponent
      (mem_connectedComponentIn (hsub mem_connectedComponent))) ?_
    exact isPreconnected_connectedComponent.subset_connectedComponentIn mem_connectedComponent hsub
  calc f '' connectedComponent x
      = f '' (Subtype.val ''
          connectedComponent (⟨x, hsub mem_connectedComponent⟩ : (f ⁻¹' B))) := by rw [hcc]
    _ = Subtype.val '' (Subtype.map f hmaps ''
          connectedComponent (⟨x, hsub mem_connectedComponent⟩ : (f ⁻¹' B))) := by
        rw [← image_comp, ← image_comp]; rfl
    _ = B := by rw [himg]; simp

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

/-- **Stacks Project, Tag 07VM.** Let `K/k` be a finite extension of fields and let `X` be a
scheme over `k`. The projection `X_K → X` sends every connected component of `X_K` onto a
connected component of `X`. -/
@[stacks 07VM, ega "IV 4.4.1" "partial, special case", sga "3 VIA 2.4.1" "partial"]
public theorem baseChange_image_connectedComponent_eq_connectedComponent
    {X : Scheme.{u}} (k K : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
    (f : X ⟶ Spec (.of k))
    (t : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base ''
        connectedComponent t =
      connectedComponent
        ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base t) := by
  have hfinK : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  set p := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) with hp
  -- `p` is finite, hence closed with finite fibres, and it is universally open.
  have hpfin : IsFinite p := inferInstance
  have hpopen : UniversallyOpen p := inferInstance
  exact finite_fibre_image_connectedComponent p.continuous p.isOpenMap p.isClosedMap
    (fun x => p.finite_preimage_singleton x) t

end AlgebraicGeometry

end
