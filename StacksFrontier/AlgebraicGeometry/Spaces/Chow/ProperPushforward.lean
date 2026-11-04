module

public import Mathlib.Topology.LocallyFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.LocallyFiniteImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Setup
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints

/-!
# Quasi-compact images of locally finite collections of closed subsets of an algebraic space

Over the base of the theory of cycles on algebraic spaces, let `X/B` and `Y/B` be good and let
`f : X ⟶ Y` be a quasi-compact morphism over `B`. The closures of the images under `|f|` of a
locally finite collection of closed subsets of `|X|` form a locally finite collection of closed
subsets of `|Y|`. This is the set-theoretic fact that makes proper pushforward of a cycle
land in the cycles of the target: the support of the pushforward is again locally finite.

## Main results

* `AlgebraicGeometry.Space.locallyFinite_closure_image_pointsMap`: **Stacks 0ENZ**.

## Implementation notes

A locally finite collection of subsets of a topological space, Stacks 0BDS, is Mathlib's
`LocallyFinite`: every point has a neighbourhood meeting only finitely many members of the
collection.

The argument is the topological one of Stacks 02R2,
`Stacks.Chow.locallyFinite_closure_image_of_isSpectralMap`: around a point of `|Y|` choose a
quasi-compact open neighbourhood `V`, available since the point space of an algebraic space has
a basis of quasi-compact opens, `AlgebraicGeometry.Space.prespectralSpace_points`; the closure
of the image of `T i` meets `V` exactly when `T i` meets `|f| ⁻¹' V`, which is quasi-compact
by Stacks 0EMK, `AlgebraicGeometry.Space.isQuasiCompactMap_pointsMap`.

Only algebraicity of `X` and `Y` enters. The quasi-separatedness and locally-of-finite-type
clauses of goodness, the compatibility of `f` with the structure morphisms, and closedness of
the `T i` are unused; they are retained, the latter two with underscored names, so that the
statement is the one of Stacks 0ENZ.

## References

* [Stacks Project, Tag 0ENZ](https://stacks.math.columbia.edu/tag/0ENZ)
* [Stacks Project, Tag 0EMK](https://stacks.math.columbia.edu/tag/0EMK)
* [Stacks Project, Tag 02R2](https://stacks.math.columbia.edu/tag/02R2)
* [Stacks Project, Tag 0BDS](https://stacks.math.columbia.edu/tag/0BDS)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})

/-- **Stacks 0ENZ.** Let `X/B` and `Y/B` be good algebraic spaces over the base of the theory
of cycles and let `f : X ⟶ Y` be a quasi-compact morphism over `B`. The closures of the images
under `|f|` of a locally finite collection of closed subsets of `|X|` form a locally finite
collection of closed subsets of `|Y|`. -/
@[stacks 0ENZ]
theorem locallyFinite_closure_image_pointsMap
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {f : X ⟶ Y} (_hfB : f ≫ sY = sX)
    (hf : IsQuasiCompact D.site D.base D.base_mem f)
    {I : Type v} (T : I → Set (points D.site D.base D.base_mem X))
    (_hT : ∀ i, IsClosed (T i)) (hTlf : LocallyFinite T) :
    LocallyFinite (fun i ↦ closure (pointsMap D.site D.base D.base_mem X f '' T i)) ∧
      ∀ i, IsClosed (closure (pointsMap D.site D.base D.base_mem X f '' T i)) := by
  let _ := prespectralSpace_points D.site D.base D.base_mem Y hY.1
  refine ⟨Stacks.Chow.locallyFinite_closure_image_of_isSpectralMap _
    ⟨continuous_pointsMap D.site D.base D.base_mem f, fun _ hVopen hVcompact ↦
      isQuasiCompactMap_pointsMap D.site D.base D.base_mem hX.1 hY.1 f hf hVopen hVcompact⟩
    T hTlf, fun _ ↦ isClosed_closure⟩

end AlgebraicGeometry.Space

end
