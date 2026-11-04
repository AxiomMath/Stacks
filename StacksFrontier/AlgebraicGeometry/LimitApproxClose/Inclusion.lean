module

public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.CompatibleOpens
public import StacksFrontier.AlgebraicGeometry.LimitApproxFunctor.Stage

/-!
# The inclusions of a compatible family of opens, as a natural transformation

Let `D : J ⥤ Scheme` be a diagram of schemes and let `V j ≤ D.obj j` be a compatible family of
opens, so that `AlgebraicGeometry.compatibleOpensDiagram` is the subdiagram it cuts out. The
inclusions `V j ⟶ D.obj j` assemble into a natural transformation out of that subdiagram, with
open-immersion components, whose images are the `V j` themselves and are therefore inverse
images of one another along the transition morphisms.

## Main definitions

* `AlgebraicGeometry.compatibleOpensInclusion`: the natural transformation from
  `AlgebraicGeometry.compatibleOpensDiagram D V hV` to `D` whose component at `j` is the
  inclusion of `V j`.

## Main results

* `AlgebraicGeometry.opensRange_compatibleOpensInclusion_app`: the image of the component at `j`
  is `V j`.
* `AlgebraicGeometry.preimage_opensRange_compatibleOpensInclusion`: the inverse image of the
  image of the component at `k` along `D.map u : D.obj j ⟶ D.obj k` is the image of the component
  at `j`.

## Implementation notes

The transition morphisms of `AlgebraicGeometry.compatibleOpensDiagram` are restrictions
`AlgebraicGeometry.Scheme.Hom.resLE`, so naturality is `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι`.
The component equation `AlgebraicGeometry.compatibleOpensInclusion_app` holds by reflexivity and
is stated by hand.

## What is NOT done here

Nothing here glues, and nothing here produces the second natural transformation or an inhabitant
of `AlgebraicGeometry.Scheme.FiniteTypeApproximation`.  Tag 07RN is not proved and no tag
attribute is attached to anything in this file.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v w u

namespace AlgebraicGeometry

variable {J : Type w} [Category.{v} J] (D : J ⥤ Scheme.{u}) (V : ∀ j, (D.obj j).Opens)
  (hV : ∀ ⦃j k : J⦄ (f : j ⟶ k), D.map f ⁻¹ᵁ V k = V j)

/-- The natural transformation from the subdiagram cut out by a compatible family of opens `V` to
`D`, whose component at `j` is the inclusion `(V j).ι` of `V j` into `D.obj j`. -/
noncomputable def compatibleOpensInclusion : compatibleOpensDiagram D V hV ⟶ D where
  app j := (V j).ι
  naturality {_ _} f := Scheme.Hom.resLE_comp_ι (D.map f) (hV f).ge

/-- The component of `compatibleOpensInclusion D V hV` at `j` is the inclusion `(V j).ι`. -/
@[simp]
lemma compatibleOpensInclusion_app (j : J) :
    (compatibleOpensInclusion D V hV).app j = (V j).ι := rfl

/-- Each component of `compatibleOpensInclusion D V hV` is an open immersion. -/
instance isOpenImmersion_compatibleOpensInclusion_app (j : J) :
    IsOpenImmersion ((compatibleOpensInclusion D V hV).app j) :=
  inferInstanceAs (IsOpenImmersion (V j).ι)

/-- The image of a component of the inclusion is the member of the family. -/
lemma opensRange_compatibleOpensInclusion_app (j : J) :
    ((compatibleOpensInclusion D V hV).app j).opensRange = V j :=
  Scheme.Opens.opensRange_ι (V j)

/-- For `u : j ⟶ k`, the inverse image along `D.map u` of the image of the component of
`compatibleOpensInclusion D V hV` at `k` is the image of its component at `j`. -/
lemma preimage_opensRange_compatibleOpensInclusion ⦃j k : J⦄ (u : j ⟶ k) :
    D.map u ⁻¹ᵁ ((compatibleOpensInclusion D V hV).app k).opensRange =
      ((compatibleOpensInclusion D V hV).app j).opensRange := by
  rw [opensRange_compatibleOpensInclusion_app, opensRange_compatibleOpensInclusion_app]
  exact hV u

end AlgebraicGeometry
