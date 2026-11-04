module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAtAPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEvery
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Openness of the flat locus of a 1-morphism of algebraic stacks

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which is locally of finite
presentation (**Stacks 06Q2**, part (1)). The set of points of `|𝒳|` at which `f` is flat in the
sense of **Stacks 0CID** is open in the topology of **Stacks 04XL**.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isOpen_setOf_isFlatAt`: the flat locus of a
  1-morphism of algebraic stacks locally of finite presentation is open.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isFlatAt_spacePointMap_iff_of_smoothDiagram`: the
  chart computation the openness rests on — along the left vertical 1-morphism of a diagram of
  **Stacks 0CIC** whose comparisons are smooth, flatness of `f` at the image point is flatness
  of the top horizontal morphism at the point itself.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_forall_isFlatAt`: a 1-morphism of
  algebraic stacks is flat exactly when it is flat at every point of its source, with no
  finiteness hypothesis. This is what makes the openness above consumable: an open set of points
  on which `f` is flat at every point is one on which `f` is flat.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_chart_setOf_isFlatAt`: the chart both rest
  on — the flat locus of `f` pulled back to the flat locus of a morphism of algebraic spaces
  along a chart which is open and surjective on points.

## How it is proved

The locus is transported from the level of algebraic spaces along one chart, exactly as the
corresponding statement for algebraic spaces,
`AlgebraicGeometry.Space.isOpen_setOf_isFlatAt`, transports the scheme-level **Stacks 0399**
along one surjective étale chart.

The chart is the diagram of **Stacks 06FM** (2) that
`AlgebraicGeometry.Stack.exists_smoothDiagram_smoothComparison` builds over a smooth
presentation `b : V ⟶ 𝒴` of the target surjective on objects: an algebraic space `U`, a smooth
1-morphism `a : U ⟶ 𝒳` surjective on objects, a morphism `h : U ⟶ V` of algebraic spaces, a
2-cell filling the square and the smoothness of *every* comparison 1-morphism of the diagram to
*every* 2-fibre product of the cospan `(b, f)`. Three things come out of that one diagram.

1. It **is** a diagram of **Stacks 0CIC**, that is an
   `AlgebraicGeometry.Stack.AlgebraicStacks.PointedFlatDiagram`, marked at *any* point `u` of
   `|U|`: its right vertical 1-morphism and all its comparisons are smooth, hence flat
   (`AlgebraicGeometry.Space.isFlat_of_isSmooth` through the identity-diagram criterion
   `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth`), and the
   marked point lies over the image point by construction. So **Stacks 0CIC**,
   `AlgebraicGeometry.Stack.AlgebraicStacks.exists_isFlatAt_iff_forall_isFlatAt`, identifies
   flatness of `f` at the image of `u` with flatness of `h` at `u`: the existential condition
   gives the diagram at hand through the universal one, and the diagram at hand witnesses the
   existential one. The flat locus of `f` is therefore the image along the chart of the flat
   locus of `h`, and its preimage along the chart is that locus.
2. Local finite presentation of `f`, which is the universal smooth-diagram criterion of
   **Stacks 06Q2** part (1), applies to that very diagram and gives
   `AlgebraicGeometry.Space.IsLocallyOfFinitePresentation h`. So the flat locus of `h` is open,
   by `AlgebraicGeometry.Space.isOpen_setOf_isFlatAt`. This is the only place the hypothesis on
   `f` is used, and it is used on the one diagram — no locality on `|𝒳|` is needed.
3. `a` is smooth and surjective on objects, so the map it induces on points is open — the
   openness clause of **Stacks 04XL**, `AlgebraicGeometry.Stack.isOpenMap_spacePointMap`, whose
   hypothesis is discharged from smoothness of `a` by
   `AlgebraicGeometry.Space.isFlat_of_isSmooth` and
   `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_isSmooth` — and surjective, by
   **Stacks 04XI** in the form
   `AlgebraicGeometry.Stack.pointsMap_surjective_of_isSurjectiveOnObjects`.

The image of an open set under an open map is open, which finishes it.

## Implementation notes

The 2-cell of the diagram has to be available as *data*, not merely as a `Nonempty`: the
comparison 1-morphisms whose smoothness clause (1) consumes are indexed by it, and so is the
`iso` field of `AlgebraicGeometry.Stack.AlgebraicStacks.PointedFlatDiagram`. That is why the
construction is read off `AlgebraicGeometry.Stack.exists_smoothDiagram_smoothComparison` rather
than off `AlgebraicGeometry.Stack.exists_smoothDiagram_of_hasPropertyOnEverySmoothDiagram`,
which quantifies the 2-cell away and reports only the property of `h`; that statement is now a
three-line consequence of this one.

**The pointwise flat locus, not the largest flat open.** At the level of algebraic spaces the two
differ, and `StacksFrontier/AlgebraicGeometry/Stacks/FlatLocusWarning.lean` is **Stacks 06M4**, the
warning that they do: the point set of the largest flat open is the *interior* of the pointwise
flat locus
(`AlgebraicGeometry.Space.range_pointsMap_maximalFlatOpen_eq_interior`), so they agree exactly
when the pointwise locus is open
(`AlgebraicGeometry.Space.range_pointsMap_maximalFlatOpen_eq_setOf_isFlatAt_iff_isOpen`), and for
some morphism it is not. What is proved here is that under local finite presentation the
pointwise locus *is* open, which is the hypothesis that makes the two agree; it is the
stack-level counterpart of
`AlgebraicGeometry.Space.range_pointsMap_maximalFlatOpen_eq_setOf_isFlatAt`.

This is **not** an instance of **Stacks 06M3**, the largest-open-substack lemma of
`StacksFrontier/AlgebraicGeometry/Stacks/RelativePropertyLocus.lean`. That lemma asks for `f` to be
representable by algebraic spaces, and its hypothesis (4) — compatibility of the largest flat
open with base change along a flat 1-morphism locally of finite presentation — is the base-change
assertion of **Stacks 05X3**, which the library does not have; see the implementation notes of
`FlatLocusWarning.lean`. Neither is needed here: the argument runs on one chart.

No `@[stacks]` attribute is attached. The statement is not a tag of the chapter: **Stacks 0CID**
is the definition of flatness at a point and **Stacks 0CIC** its chart independence, and neither
asserts openness; the openness assertions the chapter does carry, **Stacks 0399** and
**Stacks 05X3**, are at the level of schemes and of algebraic spaces respectively and are formalized
there.

## References

* [Stacks Project, Tag 0399](https://stacks.math.columbia.edu/tag/0399)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 05X3](https://stacks.math.columbia.edu/tag/05X3)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06M4](https://stacks.math.columbia.edu/tag/06M4)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 0CIC](https://stacks.math.columbia.edu/tag/0CIC)
* [Stacks Project, Tag 0CID](https://stacks.math.columbia.edu/tag/0CID)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.pointTopology Stack.pointTopology

/-! ### A smooth diagram as a diagram of Stacks 0CIC -/

/-- **A diagram of Stacks 06FM (2) with smooth comparisons is a diagram of Stacks 0CIC at every
point of its top left corner.** The right vertical 1-morphism and the comparisons of such a
diagram are smooth, hence flat by `AlgebraicGeometry.Space.isFlat_of_isSmooth` read through the
identity-diagram criterion of **Stacks 06FM**, and the marked point lies over its own image. -/
def pointedFlatDiagramOfSmoothDiagram {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hV : IsAlgebraicSpace B S hS V)
    (a : Stack.fibredCategory B S hS U ⟶ 𝒳.val)
    (b : Stack.fibredCategory B S hS V ⟶ 𝒴.val) (h : U ⟶ V)
    (η : (Stack.associatedMap B S hS h).1 ≫ b ≅ a ≫ f.hom)
    (hbsm : Stack.IsRelativelySmooth B S hS b)
    (hk : ∀ (Q : Bicategory.TwoCommSq b f.hom) (_hQ : Bicategory.IsTwoFibreProduct Q)
      (k : Bicategory.TwoCommSq.PreHom (Stack.diagramCone B S hS f.hom a b h η) Q),
        Stack.IsRelativelySmooth B S hS k.hom)
    (u : Space.points B S hS U) :
    PointedFlatDiagram B S hS f (Stack.spacePointMap B S hS U 𝒳.val a.hom u) where
  U := U
  V := V
  algebraicU := hU
  algebraicV := hV
  a := a
  b := b
  h := h
  iso := η
  u := u
  liesOver := rfl
  flatB := Stack.hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS
    (fun _ _ g => Space.IsFlat B S hS g) b V hV
    (StacksRepresentableCFG.EquivalenceOver.refl _) hbsm (Space.isFlat_id B S hS hV)
  flatComparison := fun Q hQ k =>
    Stack.hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS
      (fun _ _ g => Space.IsFlat B S hS g) k.hom U hU
      (StacksRepresentableCFG.EquivalenceOver.refl _) (hk Q hQ k)
      (Space.isFlat_id B S hS hU)

/-- **Flatness at a point, read on a smooth diagram.** For a diagram of **Stacks 06FM** (2) over
`f` whose comparison 1-morphisms are smooth, `f` is flat at the image of a point `u` of `|U|`
exactly when the top horizontal morphism `h : U ⟶ V` of the diagram is flat at `u`.

Both directions are **Stacks 0CIC**: the diagram is one of those the tag tests flatness on, so
flatness of `h` at `u` witnesses the existential condition defining **Stacks 0CID**, and
conversely the existential condition gives the universal one, which applies to this diagram. -/
theorem isFlatAt_spacePointMap_iff_of_smoothDiagram
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hV : IsAlgebraicSpace B S hS V)
    (a : Stack.fibredCategory B S hS U ⟶ 𝒳.val)
    (b : Stack.fibredCategory B S hS V ⟶ 𝒴.val) (h : U ⟶ V)
    (η : (Stack.associatedMap B S hS h).1 ≫ b ≅ a ≫ f.hom)
    (hbsm : Stack.IsRelativelySmooth B S hS b)
    (hk : ∀ (Q : Bicategory.TwoCommSq b f.hom) (_hQ : Bicategory.IsTwoFibreProduct Q)
      (k : Bicategory.TwoCommSq.PreHom (Stack.diagramCone B S hS f.hom a b h η) Q),
        Stack.IsRelativelySmooth B S hS k.hom)
    (u : Space.points B S hS U) :
    IsFlatAt B S hS f (Stack.spacePointMap B S hS U 𝒳.val a.hom u) ↔
      Space.IsFlatAt B S hS h u := by
  let D := pointedFlatDiagramOfSmoothDiagram B S hS f hU hV a b h η hbsm hk u
  exact ⟨fun hx => (exists_isFlatAt_iff_forall_isFlatAt f _).1 hx D, fun hu => ⟨D, hu⟩⟩

/-! ### The flat locus read on one chart -/

/-- **The flat locus of a 1-morphism of algebraic stacks, read on one chart.** There is an
algebraic space `U` with a 1-morphism `a : U ⟶ 𝒳` which is open and surjective on points, and a
morphism `h : U ⟶ V` of algebraic spaces, such that the preimage along `a` of the flat locus of
`f` is the flat locus of `h`, flatness of `f` is flatness of `h`, and `h` inherits local finite
presentation from `f`.

This is the chart construction both results of this module rest on. It is stated with no
hypothesis on `f`, and returns `h` rather than only the loci, because a consumer which has to
produce an open *subspace* of a chart, rather than an open set of points of `|𝒳|`, needs the
morphism. -/
theorem exists_chart_setOf_isFlatAt {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    ∃ (U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS U)
      (_ : IsAlgebraicSpace B S hS V)
      (a : Stack.fibredCategory B S hS U ⟶ 𝒳.val) (h : U ⟶ V),
      Function.Surjective (Stack.spacePointMap B S hS U 𝒳.val a.hom) ∧
      IsOpenMap (Stack.spacePointMap B S hS U 𝒳.val a.hom) ∧
      Stack.spacePointMap B S hS U 𝒳.val a.hom ⁻¹'
          {x : points B S hS 𝒳 | IsFlatAt B S hS f x} =
        {y : Space.points B S hS U | Space.IsFlatAt B S hS h y} ∧
      (IsFlat B S hS f ↔ Space.IsFlat B S hS h) ∧
      (IsLocallyOfFinitePresentation B S hS f →
        Space.IsLocallyOfFinitePresentation B S hS h) := by
  classical
  obtain ⟨V, hV, b, hbsm, hbsu⟩ :=
    Stack.exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS
      𝒴.property
  obtain ⟨U, hU, a, h, η, hasm, hasu, hk⟩ :=
    Stack.exists_smoothDiagram_smoothComparison.{u, w} B S hS 𝒳.property 𝒴.property f.hom
      V hV b hbsm hbsu
  obtain ⟨harep, harel⟩ := hasm
  refine ⟨U, V, hU, hV, a, h, ?_, ?_, ?_, ?_, fun hf => hf U V hU hV a b h η ⟨harep, harel⟩
    hbsm hk⟩
  · -- surjectivity on points: Stacks 04XI for `a`, through the tautological bijection
    have hcomp := Stack.spacePointMap_comp B S hS U (Stack.fibredCategory B S hS U) 𝒳.val
      (BasedFunctor.id (Stack.fibredCategory B S hS U).val) a.hom
    rw [BasedFunctor.id_comp] at hcomp
    rw [hcomp]
    exact (Stack.pointsMap_surjective_of_isSurjectiveOnObjects B S hS
      (𝒳 := Stack.algebraicSpaceStack.{u, w} B S hS U hU) (𝒴 := 𝒳)
      (Bicategory.InducedBicategory.mkHom a) hasu).comp
      (Stack.spacePointMap_id_bijective B S hS U).surjective
  · -- openness on points: the openness clause of Stacks 04XL at the smooth `a`
    refine Stack.isOpenMap_spacePointMap B S hS U hU 𝒳.val 𝒳.property a.hom fun W y hy G hG hE =>
      ?_
    have hsm := harel W y hy G hG hE
    exact ⟨Space.isFlat_of_isSmooth B S hS _ hsm,
      Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hsm⟩
  · exact Set.ext fun y =>
      isFlatAt_spacePointMap_iff_of_smoothDiagram B S hS f hU hV a b h η hbsm hk y
  · -- flatness of `f` is flatness of `h`: the diagram passes both criteria of Stacks 06FM
    refine ⟨fun hflat => ?_, fun hh => (isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS f).2
      ⟨U, V, hU, hV, a, b, h, ⟨η⟩, ⟨harep, harel⟩, hasu, hbsm, hh⟩⟩
    exact (Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
        (fun _ _ g => Space.IsFlat B S hS g)
        (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) 𝒳.property 𝒴.property f.hom).2
      ((isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS f).1 hflat)
      U V hU hV a b h η ⟨harep, harel⟩ hbsm hk

/-! ### Flatness is flatness at every point -/

/-- **A 1-morphism of algebraic stacks is flat exactly when it is flat at every point of its
source.** Flatness is **Stacks 06PW**, the existential smooth-diagram criterion at flatness of
morphisms of algebraic spaces; flatness at a point is **Stacks 0CID**.

On one chart of `AlgebraicGeometry.Stack.AlgebraicStacks.exists_chart_setOf_isFlatAt` both sides
become the corresponding statement about the top horizontal morphism `h : U ⟶ V` of a diagram:
flatness of `f` is flatness of `h` by **Stacks 06FM**, and the flat locus of `f` pulls back to
the flat locus of `h` by **Stacks 0CIC**, the chart being surjective on points. The statement
about `h` is `AlgebraicGeometry.Space.isFlat_iff_forall_isFlatAt`, conditions (1) and (2) of
**Stacks 03MM**.

No hypothesis of local finite presentation is needed: this is not the openness of the flat
locus, which is `AlgebraicGeometry.Stack.AlgebraicStacks.isOpen_setOf_isFlatAt`, but the
pointwise criterion for flatness of the whole 1-morphism. -/
theorem isFlat_iff_forall_isFlatAt {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    IsFlat B S hS f ↔ ∀ x : points B S hS 𝒳, IsFlatAt B S hS f x := by
  obtain ⟨U, V, hU, hV, a, h, hsurj, -, hpre, hflatiff, -⟩ :=
    exists_chart_setOf_isFlatAt B S hS f
  have hmem : ∀ y : Space.points B S hS U,
      IsFlatAt B S hS f (Stack.spacePointMap B S hS U 𝒳.val a.hom y) ↔
        Space.IsFlatAt B S hS h y := fun y =>
    Set.ext_iff.1 hpre y
  have hh := Space.isFlat_iff_forall_isFlatAt B S hS h
  refine ⟨fun hflat x => ?_, fun hpt => hflatiff.2 (hh.2 fun y => (hmem y).1 (hpt _))⟩
  obtain ⟨y, rfl⟩ := hsurj x
  exact (hmem y).2 (hh.1 (hflatiff.1 hflat) y)

/-! ### Openness of the flat locus -/

/-- **Openness of the flat locus of a 1-morphism of algebraic stacks.** For a 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` which is locally of finite presentation
(**Stacks 06Q2**, part (1)), the set of points of `|𝒳|` at which `f` is flat in the sense of
**Stacks 0CID** is open in the topology of **Stacks 04XL**.

This is the stack-level counterpart of `AlgebraicGeometry.Space.isOpen_setOf_isFlatAt` for
algebraic spaces and of **Stacks 0399** for schemes, and it is proved from the first of them on
one chart: the flat locus of `f` is the image, along a chart which is open and surjective on
points, of the flat locus of a morphism of algebraic spaces locally of finite presentation. -/
@[sga "3 VIB 1.3" "more general", sga "3 VIB 7.5" "partial"]
theorem isOpen_setOf_isFlatAt {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsLocallyOfFinitePresentation B S hS f) :
    IsOpen {x : points B S hS 𝒳 | IsFlatAt B S hS f x} := by
  obtain ⟨U, V, hU, hV, a, h, hsurj, hopen, hpre, -, hlfp⟩ :=
    exists_chart_setOf_isFlatAt B S hS f
  have himg : Stack.spacePointMap B S hS U 𝒳.val a.hom ''
      {y : Space.points B S hS U | Space.IsFlatAt B S hS h y} =
      {x : points B S hS 𝒳 | IsFlatAt B S hS f x} := by
    rw [← hpre, Set.image_preimage_eq _ hsurj]
  rw [← himg]
  exact hopen _ (Space.isOpen_setOf_isFlatAt B S hS hU hV h (hlfp hf))

end AlgebraicGeometry.Stack.AlgebraicStacks

end
