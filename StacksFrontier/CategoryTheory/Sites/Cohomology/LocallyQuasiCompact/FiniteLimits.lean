module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import StacksFrontier.Topology.Compact.LocallyQuasiCompactHausdorffCat
import StacksCore.Tactic.StacksAttribute

/-!
# Fibre products, a final object and finite limits in `LC`

`LC` is the category `Stacks.Topology.LocallyQuasiCompactHausdorff` of Hausdorff, locally
quasi-compact topological spaces and continuous maps. Three of the clauses of Stacks 09WZ are
proved here: `LC` has fibre products, `LC` has a final object, and hence `LC` has all finite
limits.

Fibre products are created from `TopCat`: the topological fibre product of two morphisms of
`LC` is a closed subspace of a product of Hausdorff locally compact spaces, hence is itself
Hausdorff and locally compact, so it lies in the full subcategory and the inclusion into
`TopCat` creates limits of cospan shape. The final object is a one-point space. A category
with a final object and fibre products has all finite limits, which gives the third clause.

## Main results

* `Stacks.Topology.LocallyQuasiCompactHausdorff.hasPullbacks`: `LC` has fibre products.
* `Stacks.Topology.LocallyQuasiCompactHausdorff.hasTerminal`: `LC` has a final object.
* `Stacks.Topology.LocallyQuasiCompactHausdorff.hasFiniteLimits`: `LC` has all finite limits.
* `Stacks.Topology.LocallyQuasiCompactHausdorff.createsLimitsOfShape_walkingCospan`: the
  inclusion of `LC` into `TopCat` creates fibre products. This is how the fibre products above
  are obtained, and it is also what lets a full subcategory of `LC` inherit them.

## Implementation notes

The results are stated as the standard typeclasses `HasPullbacks`, `HasTerminal` and
`HasFiniteLimits`, so the chosen fibre products and the chosen final object are available
through Mathlib's limits API.

Stacks 09WZ has a fourth clause: a fibre product of quasi-compact objects is quasi-compact.
That clause is
`Stacks.Topology.LocallyQuasiCompactHausdorff.compactSpace_pullback`, in
`StacksFrontier/CategoryTheory/Sites/Cohomology/LocallyQuasiCompact/QcFibreProducts.lean`, which
is where the covering set of the tag is completed. It is stated about the chosen apex of
`hasPullbacks` here, via the homeomorphism `pullbackHomeoFibreProduct` of that file onto the
subset `fibreProduct f g` of the product space — which is the subtype
`{p : X.obj × Y.obj // f.hom p.1 = g.hom p.2}` that
`t2Space_and_locallyCompactSpace_fibreProduct` below is about.

## References

* [Stacks Project, Tag 09WZ](https://stacks.math.columbia.edu/tag/09WZ)
* [Stacks Project, Section 21.31 (Tag 09WY)](https://stacks.math.columbia.edu/tag/09WY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Topology.LocallyQuasiCompactHausdorff

universe u

/-- The underlying set of the fibre product of two morphisms of `LC` is Hausdorff and locally
compact: it is a closed subspace of the product of the two sources, closed because the target
is Hausdorff, and both properties pass to closed subspaces of a product. -/
public lemma t2Space_and_locallyCompactSpace_fibreProduct
    {X Y Z : LocallyQuasiCompactHausdorff.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    T2Space { p : X.obj × Y.obj // f.hom p.1 = g.hom p.2 } ∧
      LocallyCompactSpace { p : X.obj × Y.obj // f.hom p.1 = g.hom p.2 } := by
  have he : Topology.IsClosedEmbedding
      (Subtype.val : { p : X.obj × Y.obj // f.hom p.1 = g.hom p.2 } → X.obj × Y.obj) := by
    refine ⟨Topology.IsEmbedding.subtypeVal, ?_⟩
    convert isClosed_eq (f.hom.hom.continuous.comp continuous_fst)
      (g.hom.hom.continuous.comp continuous_snd) using 1
    ext
    simp
  exact ⟨he.isEmbedding.t2Space, he.locallyCompactSpace⟩

/-- The inclusion of `LC` into `TopCat` creates limits of cospan shape: the topological
fibre product of two morphisms of `LC` is again an object of `LC`. -/
public noncomputable instance createsLimitsOfShape_walkingCospan :
    CreatesLimitsOfShape WalkingCospan (locallyQuasiCompactHausdorffToTop.{u}) where
  CreatesLimit := fun {F} =>
    let D := F ⋙ locallyQuasiCompactHausdorffToTop
    let t := TopCat.pullbackCone (D.map WalkingCospan.Hom.inl) (D.map WalkingCospan.Hom.inr)
    createsLimitFullSubcategoryInclusion' F
      ((IsLimit.postcomposeInvEquiv (diagramIsoCospan D) t).symm
        (TopCat.pullbackConeIsLimit _ _))
      (t2Space_and_locallyCompactSpace_fibreProduct _ _)

/-- **Stacks 09WZ, the fibre-product clause.** The category of Hausdorff, locally
quasi-compact spaces has fibre products. -/
@[stacks 09WZ "fibre_products"]
public noncomputable instance hasPullbacks :
    HasPullbacks (LocallyQuasiCompactHausdorff.{u}) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    locallyQuasiCompactHausdorffToTop

/-- A one-point space, the final object of `LC`. -/
private abbrev point := ULift.{u, 0} (Fin 1)

/-- The one-point space as an object of `LC`. -/
private abbrev terminalObject : LocallyQuasiCompactHausdorff.{u} :=
  LocallyQuasiCompactHausdorff.of point inferInstance

/-- There is exactly one continuous map from any Hausdorff, locally quasi-compact space to the
one-point space. -/
private instance unique_hom_terminalObject (X : LocallyQuasiCompactHausdorff.{u}) :
    Unique (X ⟶ terminalObject) where
  default := ObjectProperty.homMk (show X.obj ⟶ TopCat.of point from
    TopCat.ofHom (ContinuousMap.const _ (ULift.up 0 : point)))
  uniq _ := ObjectProperty.hom_ext _ (TopCat.ext fun _ => Subsingleton.elim _ _)

/-- **Stacks 09WZ, the final-object clause.** The category of Hausdorff, locally
quasi-compact spaces has a final object. -/
@[stacks 09WZ "final_object"]
public instance hasTerminal : HasTerminal LocallyQuasiCompactHausdorff.{u} :=
  (IsTerminal.ofUnique terminalObject).hasTerminal

/-- **Stacks 09WZ, the finite-limits clause.** The category of Hausdorff, locally
quasi-compact spaces has all finite limits: it has a final object and fibre products. -/
@[stacks 09WZ "finite_limits"]
public noncomputable instance hasFiniteLimits :
    HasFiniteLimits LocallyQuasiCompactHausdorff.{u} :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

end Stacks.Topology.LocallyQuasiCompactHausdorff

end
