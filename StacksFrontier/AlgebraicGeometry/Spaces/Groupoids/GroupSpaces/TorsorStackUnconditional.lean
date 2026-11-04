module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.SheafTorsorsEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.StackOfFppfTorsors
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorTotalSpaceAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorsWithEquivariantMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.CategoryTheory.Sites.Stack.GroupoidTransport
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.MorSheafFromIsom

/-!
# The stack of fppf torsors, with nothing carried

Let `B` be an algebraic space over a scheme `S` of a big fppf site and let `G` be a group
algebraic space over `B`.  **Stacks 04US** says that the projection
`p : G-Torsors ⥤ (Sch/S)_fppf` of Stacks 04UR defines a stack in groupoids over the big fppf
site of `S`, that is, the three conditions of Stacks 026F.  Conditions (1) and (2) are proved
in `StackOfFppfTorsors`; condition (3), effectivity of descent, was available only on two
hypotheses (`AlgebraicGeometry.Space.FppfTorsors.hasEffectiveDescent_projection_of_bootstrap`):
Stacks 04S6 part (3), and condition (3) of Stacks 04UM for `𝒢/ℬ-Torsors`.

Both are now theorems — the first is
`AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`, the second
`AlgebraicGeometry.Space.SheafTorsors.projection_hasEffectiveDescent` — so this file discharges
them and assembles the tag outright.  It then carries 04US across to the second rendering of
the category of fppf torsors, `AlgebraicGeometry.Space.TorsorObj`, and records **Stacks 0370**
(proved in `TorsorsWithEquivariantMap`) with `hB` and `G` explicit.

## Main definitions

* `AlgebraicGeometry.Space.torsorObjComparison` and
  `AlgebraicGeometry.Space.torsorObjComparisonInverse`: the two functors identifying the
  library's two renderings of the category of fppf `G`-torsors,
  `AlgebraicGeometry.Space.FppfTorsors` and `AlgebraicGeometry.Space.TorsorObj`.
* `AlgebraicGeometry.Space.torsorObjBasedEquivalence`: those two functors as an equivalence of
  categories over the big fppf site of `S`.

## Main results

* `AlgebraicGeometry.Space.FppfTorsors.hasEffectiveDescent_projection`: **Stacks 04US**,
  condition (3) of Stacks 026F for `p : G-Torsors ⥤ (Sch/S)_fppf`, with nothing carried.
* `AlgebraicGeometry.Space.FppfTorsors.projection_isStack` and
  `AlgebraicGeometry.Space.FppfTorsors.projection_isStackInGroupoids`: **Stacks 04US** in full,
  with nothing carried, in the two renderings of "stack in groupoids".
* `AlgebraicGeometry.Space.torsorProjection_isFiberedInGroupoids` and
  `AlgebraicGeometry.Space.torsorProjection_isStack`: the same for
  `AlgebraicGeometry.Space.torsorProjection`, the projection of the second rendering.
* `AlgebraicGeometry.Space.TorsorWithMap.projection_isStackInGroupoids_of_isAlgebraicSpace`:
  **Stacks 0370**, with `hB` and `G` explicit.

## Implementation notes

Condition (2) of Stacks 04US is proved in `StackOfFppfTorsors` in the family-indexed
`isom_isSheaf` shape of Stacks 02ZI, not as `CategoryTheory.Functor.IsMorSheaf`; the passage to
the latter is `CategoryTheory.Functor.isMorSheaf_of_isomIsSheaf`, which consumes exactly that
clause together with fibredness in groupoids and needs fibre products in the base, available on
the big fppf site.  Nothing of either condition is reproved here.

The two renderings of the category of fppf torsors are field-for-field the same data: `U`/`b` of
`AlgebraicGeometry.Space.TorsorObj` against `base`/`sec` of
`AlgebraicGeometry.Space.TorsorsFor`, and `AlgebraicGeometry.Space.pullbackGroup` against
`AlgebraicGeometry.Space.fppfPullbackGroup`, which are the same base change of `G`.  So the two
comparison functors are the identity on the underlying data, their composites are the identity
functors on the nose, and the unit and counit of the equivalence over the site are `Iso.refl`.
The stack conditions then move across by Stacks 042X,
`CategoryTheory.BasedCategory.isFiberedInGroupoids_and_isStack_iff_of_equivalence`.

## References

* [Stacks Project, Tag 04US](https://stacks.math.columbia.edu/tag/04US)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 02ZJ](https://stacks.math.columbia.edu/tag/02ZJ)
* [Stacks Project, Tag 04UM](https://stacks.math.columbia.edu/tag/04UM)
* [Stacks Project, Tag 04UR](https://stacks.math.columbia.edu/tag/04UR)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 042X](https://stacks.math.columbia.edu/tag/042X)
* [Stacks Project, Tag 0370](https://stacks.math.columbia.edu/tag/0370)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}

/-! ### Stacks 04US with nothing carried -/

namespace FppfTorsors

/-- **Stacks 04US**, condition (3) of Stacks 026F for `p : G-Torsors ⥤ (Sch/S)_fppf`, with
nothing carried: every descent datum relative to a covering sieve of the big fppf site of `S` is
effective.

This is `AlgebraicGeometry.Space.FppfTorsors.hasEffectiveDescent_projection_of_bootstrap` with
both of its hypotheses discharged: Stacks 04S6 part (3) by
`AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`, and condition (3) of
Stacks 04UM for `𝒢/ℬ-Torsors` by
`AlgebraicGeometry.Space.SheafTorsors.projection_hasEffectiveDescent`, whose two sheaf
hypotheses hold because `B` and `G` are algebraic spaces. -/
@[stacks 04US "condition (3): effectivity of descent, with nothing carried"]
theorem hasEffectiveDescent_projection (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB) :
    letI : (projection hB G).IsFibered :=
      (projection_isFiberedInGroupoids (hB := hB) (G := G)).isFibered
    Functor.HasEffectiveDescent (projection hB G) (BigFppfOver.topology 𝒞 S hS) :=
  hasEffectiveDescent_projection_of_bootstrap hB G
    (isBootstrapAlgebraicSpaceAlongFlatSurjection 𝒞 S hS)
    (SheafTorsors.projection_hasEffectiveDescent G.obj hB.isSheaf G.property.isSheaf)

/-- **Stacks 04US**, with nothing carried: the projection
`p : G-Torsors ⥤ (Sch/S)_fppf` of Stacks 04UR is a stack over the big fppf site of `S`, in the
sense of Stacks 026F.

Condition (1) is `AlgebraicGeometry.Space.FppfTorsors.projection_isFiberedInGroupoids`;
condition (2) is `AlgebraicGeometry.Space.FppfTorsors.projection_isomIsSheaf`, read through
`CategoryTheory.Functor.isMorSheaf_of_isomIsSheaf`; condition (3) is
`AlgebraicGeometry.Space.FppfTorsors.hasEffectiveDescent_projection`. -/
@[stacks 04US "the three conditions of Stacks 026F together, with nothing carried"]
theorem projection_isStack (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB) :
    Functor.IsStack (projection hB G) (BigFppfOver.topology 𝒞 S hS) :=
  let : HasPullbacks (BigFppfOver 𝒞 S hS) := inferInstance
  let : (projection hB G).IsFibered :=
    (projection_isFiberedInGroupoids (hB := hB) (G := G)).isFibered
  { isFibered := inferInstance
    isMorSheaf :=
      Functor.isMorSheaf_of_isomIsSheaf
        (projection_isFiberedInGroupoids (hB := hB) (G := G))
        (fun {_U} a b ha hb {_K} V g hg Vij pr₁ pr₂ hVij ar br arij brij =>
          projection_isomIsSheaf a b ha hb V g hg Vij pr₁ pr₂ hVij ar br arij brij)
    hasEffectiveDescent := hasEffectiveDescent_projection hB G }

/-- **Stacks 04US**, with nothing carried, in the rendering of Stacks 02ZI: the projection
`p : G-Torsors ⥤ (Sch/S)_fppf` is a stack in groupoids over the big fppf site of `S`.

This is `AlgebraicGeometry.Space.FppfTorsors.projection_isStack` read through the forward bridge
of Stacks 02ZJ, `CategoryTheory.Functor.IsStack.isStackInGroupoids`. -/
@[stacks 04US "the stack in groupoids in the rendering of Stacks 02ZI, with nothing carried"]
theorem projection_isStackInGroupoids (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB) :
    Functor.IsStackInGroupoids.{w} (projection hB G) (BigFppfOver.topology 𝒞 S hS) :=
  (projection_isStack hB G).isStackInGroupoids
    (projection_isFiberedInGroupoids (hB := hB) (G := G))

end FppfTorsors

/-! ### The second rendering of the category of fppf torsors -/

variable (hB : IsAlgebraicSpace 𝒞 S hS B) (G : GroupAlgebraicSpace 𝒞 S hS B hB)

/-- The comparison functor from `AlgebraicGeometry.Space.FppfTorsors` to
`AlgebraicGeometry.Space.TorsorObj`, the library's two renderings of the category of fppf
`G`-torsors.  It is the identity on the underlying data: `base`, `sec` and the three remaining
fields become `U`, `b` and the same three fields, and `AlgebraicGeometry.Space.pullbackGroup` is
the same base change of `G` as `AlgebraicGeometry.Space.fppfPullbackGroup`. -/
def torsorObjComparison : FppfTorsors hB G ⥤ TorsorObj hB G where
  obj T :=
    { U := T.base
      b := T.sec
      total := T.total
      isAlgebraicSpace := T.isAlgebraicSpace
      action := T.action
      isFppfTorsor := T.isTorsor }
  map φ :=
    { f := φ.base
      comp_b := φ.comp_sec
      g := φ.map
      isPullback := φ.isPullback
      smul_comp := φ.smul_comp }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The comparison functor of `AlgebraicGeometry.Space.torsorObjComparison` read backwards, from
`AlgebraicGeometry.Space.TorsorObj` to `AlgebraicGeometry.Space.FppfTorsors`. -/
def torsorObjComparisonInverse : TorsorObj hB G ⥤ FppfTorsors hB G where
  obj T :=
    { base := T.U
      sec := T.b
      total := T.total
      isAlgebraicSpace := T.isAlgebraicSpace
      action := T.action
      isTorsor := T.isFppfTorsor }
  map φ :=
    { base := φ.f
      comp_sec := φ.comp_b
      map := φ.g
      isPullback := φ.isPullback
      smul_comp := φ.smul_comp }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `AlgebraicGeometry.Space.torsorObjComparison` as a functor over the big fppf site of `S`:
it sends a torsor to one with the same base. -/
def torsorObjBasedComparison :
    BasedCategory.ofFunctor (FppfTorsors.projection hB G) ⥤ᵇ
      BasedCategory.ofFunctor (torsorProjection hB G) where
  toFunctor := torsorObjComparison hB G
  w := rfl

/-- `AlgebraicGeometry.Space.torsorObjComparisonInverse` as a functor over the big fppf site of
`S`. -/
def torsorObjBasedComparisonInverse :
    BasedCategory.ofFunctor (torsorProjection hB G) ⥤ᵇ
      BasedCategory.ofFunctor (FppfTorsors.projection hB G) where
  toFunctor := torsorObjComparisonInverse hB G
  w := rfl

/-- The library's two renderings of the category of fppf `G`-torsors are equivalent as
categories over the big fppf site of `S`.  Both composites of the two comparison functors are
the identity functor on the nose, so the unit and the counit are the identity. -/
def torsorObjBasedEquivalence :
    BasedCategory.Equivalence (BasedCategory.ofFunctor (FppfTorsors.projection hB G))
      (BasedCategory.ofFunctor (torsorProjection hB G)) where
  functor := torsorObjBasedComparison hB G
  inverse := torsorObjBasedComparisonInverse hB G
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- **Stacks 04US**, condition (1) of Stacks 02ZI for the second rendering of the category of
fppf `G`-torsors: `AlgebraicGeometry.Space.torsorProjection` is fibred in groupoids.

This is `AlgebraicGeometry.Space.FppfTorsors.projection_isFiberedInGroupoids` transported along
`AlgebraicGeometry.Space.torsorObjBasedEquivalence` by Stacks 042G. -/
@[stacks 04US "condition (1) for the TorsorObj rendering, with nothing carried"]
theorem torsorProjection_isFiberedInGroupoids :
    (torsorProjection hB G).IsFiberedInGroupoids :=
  (torsorObjBasedEquivalence hB G).isFiberedInGroupoids
    (FppfTorsors.projection_isFiberedInGroupoids (hB := hB) (G := G))

/-- **Stacks 04US** in full, with nothing carried, for the second rendering of the category of
fppf `G`-torsors: `AlgebraicGeometry.Space.torsorProjection` is a stack over the big fppf site
of `S`.

This is `AlgebraicGeometry.Space.FppfTorsors.projection_isStack` transported along
`AlgebraicGeometry.Space.torsorObjBasedEquivalence` by Stacks 042W. -/
@[stacks 04US "the stack property for the TorsorObj rendering, with nothing carried"]
theorem torsorProjection_isStack :
    (torsorProjection hB G).IsStack (BigFppfOver.topology 𝒞 S hS) :=
  (torsorObjBasedEquivalence hB G).isStack _ (FppfTorsors.projection_isStack hB G)

/-! ### Stacks 0370 -/

namespace TorsorWithMap

/-- **Stacks 0370**: in Situation 04WL the projection `p : [[X/G]] ⟶ (Sch/S)_fppf` is a stack
in groupoids for the fppf topology.

This is `AlgebraicGeometry.Space.TorsorWithMap.projection_isStackInGroupoids_unconditional` with
`hB` and `G` explicit. The argument `hX` is part of Situation 04WL: `[[X/G]]` is formed for an
arbitrary object `X` of `Over B`, and the situation asks that it be an algebraic space. -/
@[stacks 0370 "in Situation 04WL: the projection of [[X/G]] is a stack in groupoids for the \
fppf topology, with hB and G explicit"]
theorem projection_isStackInGroupoids_of_isAlgebraicSpace (X : Over B) [ModObj G.obj.X X]
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) :
    Functor.IsStackInGroupoids.{w} (projection hB G X) (BigFppfOver.topology 𝒞 S hS) :=
  projection_isStackInGroupoids_unconditional X hX

end TorsorWithMap

end AlgebraicGeometry.Space

end
