module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksFrontier.AlgebraicGeometry.Stacks.ComponentMultiplicity
public import StacksFrontier.AlgebraicGeometry.Stacks.ComponentMultiplicityIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges

/-!
# The multiplicity of an irreducible component of an algebraic stack (Stacks 0DR8)

Let `𝒳` be a locally Noetherian algebraic stack over `S` and let `T` be an irreducible component
of the space of points of Stacks 04XL of `𝒳`. The multiplicity `m_{T, 𝒳}` of `T` in `𝒳` is the
multiplicity `m_{T', U}` of Stacks 02QU of any irreducible component `T'` of a smooth scheme chart
`U → 𝒳` whose image has closure `T`, that is, the length of the local ring of `U` at the generic
point of `T'`.

Such a chart and component exist because an algebraic stack has a smooth surjective scheme chart
and because Stacks 0DR5 realises every irreducible component of `|𝒳|` along a surjective one, and
the resulting integer does not depend on the chart or the component by Stacks 0DR7. Together these
say that exactly one integer is a chart multiplicity of `T`, and the multiplicity is that integer.

## Main definitions

* `AlgebraicGeometry.Stack.IsComponentMultiplicity`: the property of an integer of being computed
  as the multiplicity of an irreducible component of some smooth scheme chart lying over a given
  subset of the space of points.
* `AlgebraicGeometry.Stack.componentMultiplicity`: **Stacks 0DR8**, the multiplicity of an
  irreducible component of the space of points of a locally Noetherian algebraic stack.

## Main results

* `AlgebraicGeometry.Stack.existsUnique_isComponentMultiplicity`: exactly one integer is a chart
  multiplicity of an irreducible component, by Stacks 0DR5 and Stacks 0DR7.
* `AlgebraicGeometry.Stack.componentMultiplicity_eq`: the multiplicity is computed by any smooth
  scheme chart carrying an irreducible component over the given one.

## Implementation notes

The multiplicity is extracted from the `ExistsUnique` statement
`AlgebraicGeometry.Stack.existsUnique_isComponentMultiplicity`, so both halves of the source's
justification — existence from Stacks 0DR5 and uniqueness from Stacks 0DR7 — are used in forming
the value, and the definition has no junk branch: it is total on exactly the data of a locally
Noetherian algebraic stack and an irreducible component.

The condition relating a component `T'` of a chart to `T` is
`closure (chartPointMap … '' T') = T` rather than the source's containment `f(T') ⊆ T`. For `T` an
irreducible component of `|𝒳|` the two agree: the closure of the image of `T'` is an irreducible
component by the first clause of Stacks 0DR5, and an irreducible component contained in `T` equals
`T`. The equality form is the one Stacks 0DR7 consumes.

The image of a component of a chart in the space of points of Stacks 04XL is taken along
`AlgebraicGeometry.Stack.AlgebraicStacks.chartPointMap`, the map on points of the chart read on the
scheme through `AlgebraicGeometry.Stack.pointsHomeomorphScheme`. Stacks 0DR7 spells the same set as
the image along `AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap` of the image along that
homeomorphism, so the two are identified by `Set.image_comp`.

"`𝒳` is locally Noetherian" is the existential smooth-atlas condition of Stacks 04YF and
Stacks 04YG at the property `AlgebraicGeometry.IsLocallyNoetherian` of schemes, spelled
`AlgebraicGeometry.Stack.HasPropertyOnSomeSchemeAtlas`; no named predicate "locally Noetherian
algebraic stack" is used, because Stacks 04YG has no library site of its own.

The multiplicity of an irreducible component `T'` of a scheme `U` is
`Stacks.Chow.componentMultiplicity (𝟙 U) (TopologicalSpace.genericPoints.ofComponent T')`, the
length of the local ring of `U` at the generic point of `T'` read as the multiplicity of
Stacks 02QU of `U` as a closed subscheme of itself.

## References

* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 04YG](https://stacks.math.columbia.edu/tag/04YG)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 0DR5](https://stacks.math.columbia.edu/tag/0DR5)
* [Stacks Project, Tag 0DR7](https://stacks.math.columbia.edu/tag/0DR7)
* [Stacks Project, Tag 0DR8](https://stacks.math.columbia.edu/tag/0DR8)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

open TopologicalSpace

attribute [local instance] pointTopology

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The image of a subset of a scheme chart under the chart map on points of Stacks 04XL, written
as the image along the map on points of the image along the identification of the points of the
algebraic stack of the scheme with the scheme. -/
private theorem image_chartPointMap (U : BigFppfOver B S hS)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (T : Set ((BigFppfOver.toScheme B S hS).obj U)) :
    letI := pointTopology B S hS (schemeStack.{u, w} B S hS U).val
    AlgebraicStacks.chartPointMap B S hS U 𝒳 f '' T =
      AlgebraicStacks.pointsMap B S hS f ''
        ((pointsHomeomorphScheme B S hS U).symm '' T) :=
  Set.image_comp _ _ T

/-- `n` is a chart multiplicity of a subset `T` of the space of points of `𝒳`: some smooth
1-morphism to `𝒳` from the algebraic stack of a scheme of the site has an irreducible component
whose image on points has closure `T` and whose multiplicity of Stacks 02QU is `n`. -/
def IsComponentMultiplicity (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (T : Set (AlgebraicStacks.points B S hS 𝒳)) (n : ℤ) : Prop :=
  ∃ (U : BigFppfOver B S hS) (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (_ : AlgebraicStacks.IsSmooth B S hS f)
    (T' : irreducibleComponents ((BigFppfOver.toScheme B S hS).obj U)),
    closure (AlgebraicStacks.chartPointMap B S hS U 𝒳 f '' (T' : Set _)) = T ∧
      n = _root_.Stacks.Chow.componentMultiplicity
        (𝟙 ((BigFppfOver.toScheme B S hS).obj U)) (genericPoints.ofComponent T')

/-- **Stacks 0DR5 and Stacks 0DR7.** An irreducible component of the space of points of a locally
Noetherian algebraic stack over `S` has exactly one chart multiplicity: a smooth surjective scheme
chart has an irreducible component realising it, and any two such components have the same
multiplicity. -/
theorem existsUnique_isComponentMultiplicity (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hN : HasPropertyOnSomeSchemeAtlas B S hS
      (fun X : Scheme.{u} => IsLocallyNoetherian X) 𝒳)
    (T : Set (AlgebraicStacks.points B S hS 𝒳))
    (hT : T ∈ irreducibleComponents (AlgebraicStacks.points B S hS 𝒳)) :
    ∃! n : ℤ, IsComponentMultiplicity B S hS 𝒳 T n := by
  obtain ⟨U, a, haSmooth, haSurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  obtain ⟨T₀, hT₀, hclos⟩ := AlgebraicStacks.exists_mem_irreducibleComponents_closure_image_eq
    B S hS U 𝒳 hN a haSmooth haSurj T hT
  refine ⟨_root_.Stacks.Chow.componentMultiplicity
      (𝟙 ((BigFppfOver.toScheme B S hS).obj U)) (genericPoints.ofComponent ⟨T₀, hT₀⟩),
    ⟨U, a, haSmooth, ⟨T₀, hT₀⟩, hclos, rfl⟩, ?_⟩
  rintro n ⟨V, g, hgSmooth, T', hclos', rfl⟩
  refine componentMultiplicity_eq_of_closure_image_eq B S hS 𝒳 hN V U g a hgSmooth haSmooth
    T' ⟨T₀, hT₀⟩ T hT ?_ ?_
  · rw [← image_chartPointMap B S hS V 𝒳 g]
    exact hclos'
  · rw [← image_chartPointMap B S hS U 𝒳 a]
    exact hclos

/-- **Stacks 0DR8.** The multiplicity `m_{T, 𝒳}` of an irreducible component `T` of the space of
points of Stacks 04XL of a locally Noetherian algebraic stack `𝒳` over `S`: the multiplicity of
Stacks 02QU of an irreducible component of a smooth scheme chart of `𝒳` whose image on points has
closure `T`. -/
@[stacks 0DR8]
noncomputable def componentMultiplicity (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hN : HasPropertyOnSomeSchemeAtlas B S hS
      (fun X : Scheme.{u} => IsLocallyNoetherian X) 𝒳)
    (T : Set (AlgebraicStacks.points B S hS 𝒳))
    (hT : T ∈ irreducibleComponents (AlgebraicStacks.points B S hS 𝒳)) : ℤ :=
  (existsUnique_isComponentMultiplicity.{u, w} B S hS 𝒳 hN T hT).choose

/-- The multiplicity of an irreducible component of the space of points is a chart multiplicity:
it is realised by some smooth scheme chart and some irreducible component of it. -/
theorem isComponentMultiplicity_componentMultiplicity (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hN : HasPropertyOnSomeSchemeAtlas B S hS
      (fun X : Scheme.{u} => IsLocallyNoetherian X) 𝒳)
    (T : Set (AlgebraicStacks.points B S hS 𝒳))
    (hT : T ∈ irreducibleComponents (AlgebraicStacks.points B S hS 𝒳)) :
    IsComponentMultiplicity B S hS 𝒳 T (componentMultiplicity.{u, w} B S hS 𝒳 hN T hT) :=
  (existsUnique_isComponentMultiplicity.{u, w} B S hS 𝒳 hN T hT).choose_spec.1

/-- **Stacks 0DR8.** The multiplicity of an irreducible component `T` of the space of points of a
locally Noetherian algebraic stack over `S` is computed by *any* smooth 1-morphism `f : U → 𝒳` from
the algebraic stack of a scheme of the site and any irreducible component `T'` of `U` whose image
on points has closure `T`: it is the length of the local ring of `U` at the generic point of
`T'`. -/
@[stacks 0DR8 "the multiplicity is computed by any smooth chart"]
theorem componentMultiplicity_eq (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hN : HasPropertyOnSomeSchemeAtlas B S hS
      (fun X : Scheme.{u} => IsLocallyNoetherian X) 𝒳)
    (T : Set (AlgebraicStacks.points B S hS 𝒳))
    (hT : T ∈ irreducibleComponents (AlgebraicStacks.points B S hS 𝒳))
    (U : BigFppfOver B S hS) (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (hf : AlgebraicStacks.IsSmooth B S hS f)
    (T' : irreducibleComponents ((BigFppfOver.toScheme B S hS).obj U))
    (hT' : closure (AlgebraicStacks.chartPointMap B S hS U 𝒳 f '' (T' : Set _)) = T) :
    componentMultiplicity.{u, w} B S hS 𝒳 hN T hT =
      _root_.Stacks.Chow.componentMultiplicity
        (𝟙 ((BigFppfOver.toScheme B S hS).obj U)) (genericPoints.ofComponent T') :=
  (existsUnique_isComponentMultiplicity.{u, w} B S hS 𝒳 hN T hT).unique
    (isComponentMultiplicity_componentMultiplicity.{u, w} B S hS 𝒳 hN T hT)
    ⟨U, f, hf, T', hT', rfl⟩

end AlgebraicGeometry.Stack

end
