module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiFibreProductSpace
public import StacksFrontier.Topology.Maps.Proper
public import StacksFrontier.Topology.Proper.Defs
public import StacksFrontier.Topology.Sheaves.ProperPushforward.BaseChangeFibre

/-!
# Proper morphisms of the locally quasi-compact Zariski site

Clause (7) of Stacks 0DCU is a statement about a *proper* morphism `f : X ⟶ Y` of the locally
quasi-compact Zariski site, properness being Stacks 005O (5): separated and universally closed.
For a universally closed underlying continuous map:

* the base change of `f` along any morphism of the site is a closed map, the fibre product of the
  site being identified with the topological one;
* `f` is closed and its fibres are quasi-compact, by the equivalence of Stacks 005R;
* the fibre of a base change over a point `z` is the fibre of `f` over the image of `z`.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiPullbackFibreHomeo`: the fibre of
  a base change over a point `z` is the fibre of the original morphism over the image of `z`.

## Main results

In the namespace `Stacks.Topology.LocallyQuasiCompactZariskiSituation`:

* `isClosedMap_pullback_fst_of_isUniversallyClosed`: the base change along a morphism of the
  site of a universally closed map is closed.
* `isClosedMap_and_isCompact_fibre_of_isUniversallyClosedMap`: a universally closed morphism of
  the site is closed with quasi-compact fibres.

## Implementation notes

`StacksDraft.Topology.IsUniversallyClosedMap` and `IsUniversallyClosed` are two spellings of one
condition: the first uses Mathlib's `Function.Pullback` and `Function.Pullback.fst`, the second
the local `FibreProduct` and `fibreProductFst`, whose definitions agree. Stacks 005R is stated
for the second.

The identification of the fibres of a base change is the topological statement
`Stacks.Topology.ProperBaseChange.fibreHomeomorph`, transported along `zariskiPullbackHomeo`.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 005O](https://stacks.math.columbia.edu/tag/005O)
* [Stacks Project, Tag 005R](https://stacks.math.columbia.edu/tag/005R)
* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y Z : S.category}
  (f : X ⟶ Y) (g : Z ⟶ Y)

/-- **The base change of a universally closed morphism of the site is closed.** Here universal
closedness, in the sense of Stacks 005O (4), is stated with the topological fibre product
`Function.Pullback`. -/
theorem isClosedMap_pullback_fst_of_isUniversallyClosed
    (hf : StacksDraft.Topology.IsUniversallyClosedMap.{u, u, u} (f : X.obj → Y.obj)) :
    IsClosedMap (pullback.fst g f : (pullback g f).obj → Z.obj) := by
  have hg : Continuous (g : Z.obj → Y.obj) := (ConcreteCategory.hom g).continuous
  have heq : (pullback.fst g f : (pullback g f).obj → Z.obj) =
      Function.Pullback.fst ∘ zariskiPullbackHomeo S f g :=
    funext fun p => (zariskiPullbackHomeo_fst S f g p).symm
  rw [heq]
  exact (hf Z.obj (g : Z.obj → Y.obj) hg).comp (zariskiPullbackHomeo S f g).isClosedMap

/-- **A universally closed morphism of the site is closed with quasi-compact fibres**, by the
equivalence of Stacks 005R. -/
theorem isClosedMap_and_isCompact_fibre_of_isUniversallyClosedMap
    (hf : StacksDraft.Topology.IsUniversallyClosedMap.{u, u, u} (f : X.obj → Y.obj)) :
    IsClosedMap (f : X.obj → Y.obj) ∧
      ∀ y : Y.obj, IsCompact ((f : X.obj → Y.obj) ⁻¹' {y}) := by
  have huc : IsUniversallyClosed (f : X.obj → Y.obj) := fun W _ k hk => hf W k hk
  exact ((isProperMap_tfae (f : X.obj → Y.obj) (ConcreteCategory.hom f).continuous).out 3 4).mp huc

/-- **The fibres of a base change in the Zariski site.** For a point `z` of the space of `Z`,
the fibre of `pullback.fst g f : Z ×_Y X ⟶ Z` over `z` is homeomorphic to the fibre of `f` over
`g z`. -/
noncomputable def zariskiPullbackFibreHomeo (z : Z.obj) :
    ((pullback.fst g f : (pullback g f).obj → Z.obj) ⁻¹' {z}) ≃ₜ
      ((f : X.obj → Y.obj) ⁻¹' {(g : Z.obj → Y.obj) z} : Set X.obj) :=
  (Homeomorph.subtype (zariskiPullbackHomeo S f g)
      (p := fun p => (pullback.fst g f : (pullback g f).obj → Z.obj) p ∈ ({z} : Set Z.obj))
      (q := fun q => Function.Pullback.fst q ∈ ({z} : Set Z.obj))
      (fun p => by rw [Set.mem_singleton_iff, Set.mem_singleton_iff,
        zariskiPullbackHomeo_fst S f g p])).trans
    (Stacks.Topology.ProperBaseChange.fibreHomeomorph
      (f : X.obj → Y.obj) (g : Z.obj → Y.obj) z)

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
