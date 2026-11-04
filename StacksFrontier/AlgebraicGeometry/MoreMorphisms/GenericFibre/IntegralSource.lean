module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.Topology.Irreducible.DenseFibres
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An open morphism with irreducible generic fibre has irreducible source

Let `f : X ⟶ Y` be a morphism of schemes with `Y` irreducible, let `η` be the generic point of
`Y` and assume `f` is an open map. Then the set theoretic fibre over `η` is dense in `X`: the
image of a nonempty open of `X` is a nonempty open of `Y`, hence contains `η`. If moreover the
scheme theoretic fibre over `η` is irreducible, the dense subset `f ⁻¹' {η}` is irreducible and
therefore so is `X`. This is Stacks Tag 004Z applied to the dense set of points `{η}`.

Combined with reducedness this is how an integral source is produced in the reduction step of
Stacks Tag 0559: the morphism there is flat and of finite presentation, hence universally open,
its source is the reduction of a scheme, and its generic fibre is geometrically irreducible.

Three elementary facts about generic points are recorded alongside: a morphism with dense range
sends a generic point to a generic point, the generic point of a space lies in every nonempty
open subset of it, and consequently an open map between irreducible schemes sends the generic
point to the generic point. The last one supplies the generic point equation that Tag 0552 asks
for on the side of the source.

## Main results

* `AlgebraicGeometry.isGenericPoint_apply_of_denseRange`
* `AlgebraicGeometry.mem_of_isGenericPoint_univ`
* `AlgebraicGeometry.apply_genericPoint_of_isOpenMap`
* `AlgebraicGeometry.irreducibleSpace_of_isOpenMap_of_irreducibleSpace_fiber`

## References

* [Stacks Project, Tag 004Z](https://stacks.math.columbia.edu/tag/004Z)
* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes with dense range sends a generic point of its source to a generic
point of its target. -/
theorem isGenericPoint_apply_of_denseRange {X Y : Scheme.{u}} (h : X ⟶ Y)
    (hd : Dense (Set.range h)) {x : X} (hx : IsGenericPoint x Set.univ) :
    IsGenericPoint (h x) Set.univ := by
  have him := hx.image h.continuous
  rwa [Set.image_univ, hd.closure_eq] at him

/-- A generic point of a scheme lies in every nonempty open subset of it. -/
theorem mem_of_isGenericPoint_univ {Y : Scheme.{u}} {η : Y} (hη : IsGenericPoint η Set.univ)
    {U : Set Y} (hU : IsOpen U) (hUne : U.Nonempty) : η ∈ U := by
  rw [hη.mem_open_set_iff hU, Set.univ_inter]
  exact hUne

/-- The set theoretic fibre of a morphism of schemes over a point whose closure is the whole
target is irreducible as soon as the scheme theoretic fibre there is. -/
theorem isIrreducible_preimage_singleton {X Y : Scheme.{u}} (f : X ⟶ Y) (η : Y)
    [IrreducibleSpace (f.fiber η)] : IsIrreducible (f ⁻¹' {η}) := by
  rw [← f.range_fiberι η, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ (f.fiberι η).continuous.continuousOn

/-- An open map between irreducible schemes sends the generic point to the generic point: its
range is a nonempty open subset of the target, hence dense. -/
theorem apply_genericPoint_of_isOpenMap {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] (hf : IsOpenMap f) : f (genericPoint X) = genericPoint Y := by
  have hrange : Dense (Set.range f) := by
    rw [← Set.image_univ]
    refine (preirreducibleSpace_iff_open_dense Y).mp inferInstance (hf _ isOpen_univ) ?_
    exact ⟨f (genericPoint X), genericPoint X, trivial, rfl⟩
  refine (isGenericPoint_apply_of_denseRange f hrange ?_).eq ?_ <;>
    simpa using genericPoint_spec _

/-- A morphism of schemes which is an open map onto an irreducible target and whose fibre over
the generic point of the target is irreducible has irreducible source. -/
@[ega "IV 2.3.5" "(iii), special case"]
theorem irreducibleSpace_of_isOpenMap_of_irreducibleSpace_fiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace Y] (hf : IsOpenMap f) (η : Y) (hη : IsGenericPoint η Set.univ)
    [IrreducibleSpace (f.fiber η)] : IrreducibleSpace X := by
  refine irreducibleSpace_of_isOpenMap_of_dense_isIrreducible_fiber hf ?_
  refine Dense.mono (Set.singleton_subset_iff.mpr ?_) (dense_iff_closure_eq.mpr hη)
  exact isIrreducible_preimage_singleton f η

end AlgebraicGeometry

end
