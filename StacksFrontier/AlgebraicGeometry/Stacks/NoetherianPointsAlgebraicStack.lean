module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatOpenPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.Topology.Noetherian.Image
public import StacksFrontier.Topology.Noetherian.QuasiCompactLocally
public import StacksFrontier.Topology.Sober.NoetherianSurjection

/-!
# The point space of a locally Noetherian algebraic stack (Stacks 0DQI, 0GVX)

The space of points of Stacks 04XL of a locally Noetherian algebraic stack over `S` is a locally
Noetherian topological space, is Noetherian as soon as the stack is in addition quasi-compact,
and is quasi-sober in the sense of Stacks 004X.

"Locally Noetherian" is the smooth-local atlas condition of Stacks 04YF at the property
`AlgebraicGeometry.IsLocallyNoetherian` of schemes: there is a smooth surjective 1-morphism to the
stack from the algebraic stack of a scheme of the site which is locally Noetherian. Reading that
condition as the existential it is gives a scheme `U`, so Stacks 01OZ makes the topological space
of `U` locally Noetherian, and the point space of the algebraic stack of `U` **is** that space, by
`AlgebraicGeometry.Stack.pointsHomeomorphScheme`. The chart is surjective on points — that is what
Stacks 04ZS asserts of it — and open on points, because a smooth 1-morphism is flat and locally of
finite presentation and Stacks 06R7 makes such a 1-morphism open on points. Stacks 04Z8 part (2)
then carries local Noetherianity along it, and Stacks 04ZB upgrades the conclusion to Noetherian
under quasi-compactness, which Stacks 04YB defines as compactness of the point space.

Quasi-sobriety is obtained from the same chart. The point space of `U` is quasi-sober because the
topological space of a scheme is, and a continuous open surjection out of a locally Noetherian
quasi-sober space has quasi-sober target.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_isSmooth`: a smooth 1-morphism of algebraic
  stacks is flat.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyNoetherianSpace_points_of_isLocallyNoetherian`:
  **Stacks 0DQI**, part (1).
* `AlgebraicGeometry.Stack.AlgebraicStacks.noetherianSpace_points_of_isQuasiCompactStack`:
  **Stacks 0DQI**, part (2).
* `AlgebraicGeometry.Stack.AlgebraicStacks.quasiSober_points_of_isLocallyNoetherian`:
  **Stacks 0GVX**.

## Implementation notes

The library form of Stacks 04Z8 part (2) concludes local Noetherianity of `Set.range f` rather than
of the codomain, so the surjective form used here is not a bare instantiation of it: it is that
statement composed with the transport of local Noetherianity along a homeomorphism. Both the
transport, `TopologicalSpace.IsLocallyNoetherianSpace.of_homeomorph`, and the surjective form built
from it, `TopologicalSpace.IsLocallyNoetherianSpace.of_isOpenMap_surjective`, are stated alongside
Stacks 04Z8 part (2) itself and are imported here. The transport is also what moves Stacks 01OZ's
conclusion about the scheme `U` across `AlgebraicGeometry.Stack.pointsHomeomorphScheme`.

`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_isSmooth` is the mirror at flatness of the
statement tagged `@[stacks 0DNP]`, which is the same statement at local finite presentation. Stacks
075U and Stacks 06PW are the existential smooth-diagram test of Stacks 06FM at smoothness and at
flatness respectively — the second recorded by the `Iff.rfl`
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram` — so the
implication is monotonicity of that test (Stacks 06PS) at the implication Stacks 04TA for
morphisms of algebraic spaces. It carries no `@[stacks]` attribute: the Stacks Project does not
state it, and the three tags it is built from are registered where they are proved.

Neither part is stated over a named predicate "locally Noetherian algebraic stack" (Stacks 04YG):
the existential atlas condition of Stacks 04YF is what the source's proof consumes.

The declaration names say `points` to keep them apart from the scheme-level Stacks 01OZ,
`AlgebraicGeometry.isLocallyNoetherianSpace_of_isLocallyNoetherian`, which takes a `Scheme` at one
universe rather than an `AlgebraicGeometry.Stack.AlgebraicStacks` at two, and which the proofs
apply to the chart `U`.

The source's proof of Stacks 0GVX picks an *affine* chart, so that its source is Noetherian and
decomposes into finitely many irreducible components. The chart supplied by Stacks 04YF is only
locally Noetherian, and the two topological inputs — the Noetherian case and its localization
along an open map — are `quasiSober_of_noetherianSpace_surjective` and
`quasiSober_of_isLocallyNoetherianSpace_isOpenMap_surjective`.

## References

* [Stacks Project, Tag 004X](https://stacks.math.columbia.edu/tag/004X)
* [Stacks Project, Tag 01OZ](https://stacks.math.columbia.edu/tag/01OZ)
* [Stacks Project, Tag 04YB](https://stacks.math.columbia.edu/tag/04YB)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 04Z8](https://stacks.math.columbia.edu/tag/04Z8)
* [Stacks Project, Tag 04ZB](https://stacks.math.columbia.edu/tag/04ZB)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 06R7](https://stacks.math.columbia.edu/tag/06R7)
* [Stacks Project, Tag 0DNP](https://stacks.math.columbia.edu/tag/0DNP)
* [Stacks Project, Tag 0DQI](https://stacks.math.columbia.edu/tag/0DQI)
* [Stacks Project, Tag 0GVX](https://stacks.math.columbia.edu/tag/0GVX)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

open TopologicalSpace

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A smooth 1-morphism of algebraic stacks over `S` is flat.** Stacks 075U and Stacks 06PW are
the existential smooth-diagram test of Stacks 06FM at smoothness and at flatness of morphisms of
algebraic spaces, so this is monotonicity of that test (Stacks 06PS) at Stacks 04TA.

The mirror of this statement at local finite presentation is the statement tagged
`@[stacks 0DNP]`. -/
theorem isFlat_of_isSmooth {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsSmooth B S hS f) : IsFlat B S hS f :=
  (isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS f).2
    (Stack.hasPropertyOnSomeSmoothDiagram_mono B S hS _ _
      (fun _ _ _ hg => Space.isFlat_of_isSmooth B S hS _ hg) f.hom hf)

/-- A smooth 1-morphism of algebraic stacks over `S` is open on points: it is flat and locally of
finite presentation, so Stacks 06R7 applies. -/
theorem isOpenMap_pointsMap_of_isSmooth
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsSmooth B S hS f) :
    @IsOpenMap _ _ (Stack.pointTopology B S hS 𝒳.val) (Stack.pointTopology B S hS 𝒴.val)
      (pointsMap B S hS f) :=
  isOpenMap_pointsMap B S hS f (isFlat_of_isSmooth B S hS f hf)
    (isLocallyOfFinitePresentation_of_isSmooth B S hS f hf)

/-- The point space of the algebraic stack of a locally Noetherian scheme `U` is locally
Noetherian, since it is homeomorphic to the topological space of `U`. -/
private theorem isLocallyNoetherianSpace_points_schemeStack (U : BigFppfOver B S hS)
    (hU : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)) :
    letI := Stack.pointTopology B S hS (Stack.schemeStack.{u, w} B S hS U).val
    IsLocallyNoetherianSpace
      (Stack.points B S hS (Stack.schemeStack.{u, w} B S hS U).val.val
        (Stack.schemeStack.{u, w} B S hS U).val.property) := by
  let := Stack.pointTopology B S hS (Stack.schemeStack.{u, w} B S hS U).val
  exact (isLocallyNoetherianSpace_of_isLocallyNoetherian
    ((BigFppfOver.toScheme B S hS).obj U)).of_homeomorph
    (Stack.pointsHomeomorphScheme B S hS U).symm

/-- **Stacks 0DQI, part (1).** The space of points of Stacks 04XL of a locally Noetherian
algebraic stack over `S` is a locally Noetherian topological space.

Local Noetherianity of the stack is read as the existential atlas condition of Stacks 04YF: a
smooth surjective 1-morphism from the algebraic stack of a locally Noetherian scheme `U` of the
site. The point space of that algebraic stack is the topological space of `U`, which is locally
Noetherian by Stacks 01OZ, and the chart is open on points by Stacks 06R7 and surjective on points
by the definition of Stacks 04ZS, so Stacks 04Z8 part (2) carries local Noetherianity across. -/
@[stacks 0DQI "part (1)"]
theorem isLocallyNoetherianSpace_points_of_isLocallyNoetherian
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (hN : Stack.HasPropertyOnSomeSchemeAtlas B S hS
      (fun X : Scheme.{u} => IsLocallyNoetherian X) 𝒳) :
    letI := Stack.pointTopology B S hS 𝒳.val
    IsLocallyNoetherianSpace (Stack.points B S hS 𝒳.val.val 𝒳.val.property) := by
  let := Stack.pointTopology B S hS 𝒳.val
  obtain ⟨U, a, hsurj, hsmooth, hU⟩ := hN
  let := Stack.pointTopology B S hS (Stack.schemeStack.{u, w} B S hS U).val
  have hsrc := isLocallyNoetherianSpace_points_schemeStack.{u, w} B S hS U hU
  exact hsrc.of_isOpenMap_surjective _ (Stack.continuous_pointsMap B S hS _ _ a.hom.hom)
    (isOpenMap_pointsMap_of_isSmooth B S hS a hsmooth) hsurj

/-- **Stacks 0DQI, part (2).** The space of points of Stacks 04XL of a quasi-compact locally
Noetherian algebraic stack over `S` is a Noetherian topological space.

Quasi-compactness of Stacks 04YB is compactness of the point space, so this is Stacks 04ZB applied
to part (1). The name records only the quasi-compactness hypothesis; the local-Noetherianity
hypothesis is the same atlas condition part (1) carries. -/
@[stacks 0DQI "part (2)"]
theorem noetherianSpace_points_of_isQuasiCompactStack
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (hqc : Stack.IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (hN : Stack.HasPropertyOnSomeSchemeAtlas B S hS
      (fun X : Scheme.{u} => IsLocallyNoetherian X) 𝒳) :
    letI := Stack.pointTopology B S hS 𝒳.val
    NoetherianSpace (Stack.points B S hS 𝒳.val.val 𝒳.val.property) := by
  let := Stack.pointTopology B S hS 𝒳.val
  let : CompactSpace (Stack.points B S hS 𝒳.val.val 𝒳.val.property) := hqc
  exact noetherianSpace_of_isLocallyNoetherianSpace _
    (isLocallyNoetherianSpace_points_of_isLocallyNoetherian B S hS 𝒳 hN)

/-- **Stacks 0GVX.** The space of points of Stacks 04XL of a locally Noetherian algebraic stack
over `S` is quasi-sober in the sense of Stacks 004X: every irreducible closed subset of it has a
generic point.

Local Noetherianity is read as the atlas condition of Stacks 04YF, which supplies a smooth
surjective 1-morphism from the algebraic stack of a locally Noetherian scheme `U` of the site.
The point space of that algebraic stack is the topological space of `U`, hence is quasi-sober and
locally Noetherian, and the chart is continuous, open and surjective on points, so quasi-sobriety
passes to `|𝒳|`. -/
@[stacks 0GVX]
theorem quasiSober_points_of_isLocallyNoetherian
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (hN : Stack.HasPropertyOnSomeSchemeAtlas B S hS
      (fun X : Scheme.{u} => IsLocallyNoetherian X) 𝒳) :
    letI := Stack.pointTopology B S hS 𝒳.val
    QuasiSober (Stack.points B S hS 𝒳.val.val 𝒳.val.property) := by
  let := Stack.pointTopology B S hS 𝒳.val
  obtain ⟨U, a, hsurj, hsmooth, hU⟩ := hN
  let := Stack.pointTopology B S hS (Stack.schemeStack.{u, w} B S hS U).val
  have hsrc := isLocallyNoetherianSpace_points_schemeStack.{u, w} B S hS U hU
  have : QuasiSober
      (Stack.points B S hS (Stack.schemeStack.{u, w} B S hS U).val.val
        (Stack.schemeStack.{u, w} B S hS U).val.property) :=
    (Stack.pointsHomeomorphScheme B S hS U).isOpenEmbedding.quasiSober
  exact quasiSober_of_isLocallyNoetherianSpace_isOpenMap_surjective hsrc
    (Stack.continuous_pointsMap B S hS _ _ a.hom.hom)
    (isOpenMap_pointsMap_of_isSmooth B S hS a hsmooth) hsurj

end AlgebraicGeometry.Stack.AlgebraicStacks

end
