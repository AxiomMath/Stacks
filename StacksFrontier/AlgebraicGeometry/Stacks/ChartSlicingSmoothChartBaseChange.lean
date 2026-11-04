module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartFactorisationLargeField
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# The stack-level reduction of Stacks 06MD: the chart base change, and lifting the point

Let `𝒳` be an algebraic stack over `S`, let `c : 𝒯 ⟶ 𝒳` be a 1-morphism and let `a : 𝒲 ⟶ 𝒳` be
another one — in the application `𝒯` is an algebraic space `U` and `a` is a smooth surjective
scheme chart of `𝒳`. This file carries out two of the four steps of the stack-level reduction
that **Stacks 06MD** performs before it applies **Stacks 06LW**, namely steps 2 and 3 of the
list in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Stacks/ChartSlicingRegularSequence.lean`:

* the flatness and the local finite presentation of the projection `U ×_𝒳 W ⟶ W`, read as a
  morphism of the representing algebraic spaces;
* a lift of a field-valued point `Spec k ⟶ 𝒳` through `a`, after a field extension, together
  with a geometric point of the fibre over that extension.

Step 1 of that list, `U ×_𝒳 W` **as an algebraic space**, needs nothing new: it is
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_chartBaseChange` of
`StacksFrontier/AlgebraicGeometry/Stacks/RelativeDimensionZeroLocusStack.lean`, already stated for
a 1-morphism out of any algebraic stack representable by an algebraic space and the canonical
2-fibre product square of its cospan with a scheme chart — which is exactly the square whose
first projection the two property statements below are about.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.isFlat_representingMap_chartBaseChange_fst` and
  `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_representingMap_chartBaseChange_fst`:
  the projection `𝒯 ×_𝒳 𝒲 ⟶ 𝒲`, read as a morphism of the representing algebraic spaces, is
  flat, respectively locally of finite presentation, as soon as `c` is.
* `AlgebraicGeometry.Stack.exists_fieldValuedPoint_lift_of_isSurjective`: a field-valued point
  of `𝒳` lifts through a *surjective* 1-morphism after a field extension, as a 1-morphism
  `Spec k' ⟶ 𝒲` together with a 2-isomorphism between `Spec k' ⟶ 𝒲 ⟶ 𝒳` and
  `Spec k' ⟶ Spec k ⟶ 𝒳`.
* `AlgebraicGeometry.Stack.exists_geometricPoint_lift_fieldSpectrum`: a geometric point of a
  presheaf over `Spec k` above a prescribed point of it, whose own residue field already
  receives the field extension, together with a geometric point of the base change of the
  presheaf to that residue field.

## Implementation notes

Nothing here is new mathematics; the point is that the statements these compose produce
data that `ChartSlicingRegularSequence.lean` would otherwise have to carry as hypotheses.

The two property statements are the composites of base change at the level of algebraic stacks,
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_baseChange` (**Stacks 06FQ** at flatness) and
`...isLocallyOfFinitePresentation_baseChange` (**Stacks 06Q4**), with the bridge of **Stacks
04SW** and **Stacks 06FM** from a property of a 1-morphism of algebraic stacks between objects
representable by algebraic spaces to the same property of the induced morphism of representing
algebraic spaces, `AlgebraicGeometry.Stack.isFlat_representingMap_of_isFlat` and its companion.
They are stated rather than inlined because a consumer has to pin the implicit algebraic stacks
of those bridges by hand, recovering them from a representing equivalence being a projection
problem on a metavariable; the same cost is paid, and explained, in
`StacksFrontier/AlgebraicGeometry/Stacks/RelativeDimensionZeroLocusStack.lean`.

The lift needs only surjectivity of the 1-morphism, not smoothness and not flatness:
surjectivity of a 1-morphism of algebraic stacks is surjectivity of the map on points
(**Stacks 04ZS**), which implies surjectivity on objects in the sense of **Stacks 06D4** by
`AlgebraicGeometry.Stack.isSurjectiveOnObjects_of_pointsMap_surjective`, and that predicate *is*
the lift of an object over the spectrum of a field to one over a field extension. What is added
here is to read the resulting arrow of `𝒳` as a 2-isomorphism of 1-morphisms, through the
2-Yoneda lemma (**Stacks 004B**) in each of its two variables. The geometric point is the same
pair of steps that the proof of the flatness half of Stacks 06LW,
`Space.exists_isOpenSubspace_isFlat_vanishingSubfunctor_of_isRegular_geometricFiber`,
takes for the enlargement of `k` there.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FQ](https://stacks.math.columbia.edu/tag/06FQ)
* [Stacks Project, Tag 06LW](https://stacks.math.columbia.edu/tag/06LW)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 06Q4](https://stacks.math.columbia.edu/tag/06Q4)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (𝒳 𝒯 𝒲 : AlgebraicStacks.{u, w} B S hS) (c : 𝒯 ⟶ 𝒳) (a : 𝒲 ⟶ 𝒳)
  (P W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hP : IsAlgebraicSpace B S hS P) (hW : IsAlgebraicSpace B S hS W)
  (eP : StacksRepresentableCFG.EquivalenceOver
    (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val.val.p
    (presheafOfCategories (P ⋙ typeToCat)).p)
  (eW : StacksRepresentableCFG.EquivalenceOver 𝒲.val.val.p
    (presheafOfCategories (W ⋙ typeToCat)).p)

include hP hW in
/-- **The projection `𝒯 ×_𝒳 𝒲 ⟶ 𝒲` is flat as a morphism of algebraic spaces.** Let `c : 𝒯 ⟶ 𝒳`
be a flat 1-morphism of algebraic stacks over `S`, let `a : 𝒲 ⟶ 𝒳` be another one — in the
application a smooth surjective scheme chart of `𝒳` — and let `P` and `W` be algebraic spaces
representing the apex of the canonical 2-fibre product square of the cospan `(a, c)` and the
source of `a`. Then the first projection of that square, read as a morphism `P ⟶ W` through
**Stacks 04SW**, is flat.

The projection is the base change of `c` along `a`, hence flat by **Stacks 06FQ** at flatness,
and flatness of a 1-morphism of algebraic stacks between objects representable by algebraic
spaces is flatness of the induced morphism of representing algebraic spaces, by the equivalence
of conditions (2) and (3) of **Stacks 06FM**.

The representing algebraic space `P` exists whenever `𝒯` is representable by an algebraic space
and `a` is a chart by a scheme of the site, by
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_chartBaseChange`. -/
theorem isFlat_representingMap_chartBaseChange_fst
    (hflat : AlgebraicStacks.IsFlat B S hS c) :
    Space.IsFlat B S hS
      (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
        𝒲.val P W eP eW (twoFibreProductSquareAlgebraicStacks B S hS a c).fst.hom) :=
  isFlat_representingMap_of_isFlat.{u, w} B S hS P W hP hW eP eW
    (twoFibreProductSquareAlgebraicStacks B S hS a c).fst
    (AlgebraicStacks.isFlat_baseChange B S hS c a
      (twoFibreProductSquareAlgebraicStacks B S hS a c)
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a c) hflat)

include hP hW in
/-- **The projection `𝒯 ×_𝒳 𝒲 ⟶ 𝒲` is locally of finite presentation as a morphism of algebraic
spaces**, the companion of `AlgebraicGeometry.Stack.isFlat_representingMap_chartBaseChange_fst`
through **Stacks 06Q4** and the equivalence of conditions (1), (2) and (3) of
**Stacks 06FM**. -/
theorem isLocallyOfFinitePresentation_representingMap_chartBaseChange_fst
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS c) :
    Space.IsLocallyOfFinitePresentation B S hS
      (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
        𝒲.val P W eP eW (twoFibreProductSquareAlgebraicStacks B S hS a c).fst.hom) :=
  isLocallyOfFinitePresentation_representingMap_of_isLocallyOfFinitePresentation.{u, w} B S hS
    P W hP hW eP eW (twoFibreProductSquareAlgebraicStacks B S hS a c).fst
    (AlgebraicStacks.isLocallyOfFinitePresentation_baseChange B S hS c a
      (twoFibreProductSquareAlgebraicStacks B S hS a c)
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a c) hlfp)

/-! ### Lifting a field-valued point through a surjective 1-morphism -/

/-- **A field-valued point of an algebraic stack lifts through a surjective 1-morphism, after a
field extension.** Let `c : 𝒲 ⟶ 𝒳` be a surjective 1-morphism of algebraic stacks over `S` and
let `q` be a field-valued point of `𝒳`, that is a 1-morphism `Spec k ⟶ 𝒳`. Then there are a
field-valued point `r` of `𝒲` — a 1-morphism `Spec k' ⟶ 𝒲` — and a morphism
`ρ : Spec k' ⟶ Spec k` of the site such that the composite `Spec k' ⟶ 𝒲 ⟶ 𝒳` is
2-isomorphic to `Spec k' ⟶ Spec k ⟶ 𝒳`.

Surjectivity of a 1-morphism of algebraic stacks is surjectivity of the map on points
(**Stacks 04ZS**), and that implies surjectivity on objects in the sense of **Stacks 06D4**,
`AlgebraicGeometry.Stack.isSurjectiveOnObjects_of_pointsMap_surjective` — which is exactly the
lift of `q.obj` to an object of `𝒲` over a field extension, together with an arrow `α` of `𝒳`
above the extension. Reading `α` through the 2-Yoneda lemma (**Stacks 004B**) in its two
variables turns it into the 2-isomorphism: once in the target, by
`AlgebraicGeometry.Stack.fieldValuedPointStackMorphism_comp_iso`, which identifies the
1-morphism of the image point `d(r)` with `r`'s own 1-morphism followed by `d`, and once in the
source, by `AlgebraicGeometry.Stack.fieldValuedPointMorphismBaseMapIso`, which factors the
1-morphism of `d(r)` through the morphism of the site that `α` lies over.

No flatness and no local finite presentation of `d` is needed, and in particular none of the
smoothness of a chart: surjectivity alone suffices. -/
theorem exists_fieldValuedPoint_lift_of_isSurjective
    (d : 𝒲 ⟶ 𝒳) (hd : IsSurjective B S hS d)
    (q : FieldValuedPoint B S hS 𝒳.val.val) :
    ∃ (r : FieldValuedPoint B S hS 𝒲.val.val) (ρ : r.base ⟶ q.base),
      Nonempty ((fieldValuedPointStackMorphism.{u, w} B S hS 𝒲 r ≫ d).hom ≅
        (schemeStackMap.{u, w} B S hS ρ ≫
          fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 q).hom) := by
  obtain ⟨V, hV, _ρ₀, x, hx, α, _hα⟩ :=
    isSurjectiveOnObjects_of_pointsMap_surjective B S hS d hd q.base
      ⟨q.carrier, q.field, ⟨q.isSpec⟩⟩ q.obj q.over
  obtain ⟨k', hk', ⟨eV⟩⟩ := hV
  let _ : Field k' := hk'
  let r : FieldValuedPoint B S hS 𝒲.val.val :=
    { carrier := k', base := V, isSpec := eV, obj := x, «over» := hx }
  let cr : FieldValuedPoint B S hS 𝒳.val.val :=
    fieldValuedPointMap B S hS 𝒲.val.val d.hom.hom r
  refine ⟨r, fieldValuedPointBaseMap B S hS (p := cr) (q := q) α, ⟨?_⟩⟩
  exact (fieldValuedPointStackMorphism_comp_iso.{u, w} B S hS d r).trans
    (Bicategory.InducedBicategory.isoMk
      (fieldValuedPointMorphismBaseMapIso B S hS 𝒳.val (p := cr) (q := q) α))

/-! ### A geometric point of the lifted fibre -/

/-- **A geometric point of the fibre, with the lift available at the point's own residue
field.** Let `Spec k' ⟶ Spec k` be a morphism of spectra of fields of the site and let `F` be a
presheaf over `Spec k` — in the application the fibre `U ×_𝒳 Spec k` and the field extension
along which `Spec k ⟶ 𝒳` was lifted through a surjective chart. Then every point of `|F|` is
the image of a geometric point `z'` of `F` whose residue field already receives `Spec k'`, and
the fibre of `F` over that residue field has a geometric point above `z'`.

This is what makes the lift usable at a *geometric* point: `z'` has the same image in `|F|` as
the point one started with, its structural map to `Spec k` is the morphism of the site that its
residue field names, and that morphism factors through `Spec k'`, so the lift pulls back to it.

Both halves are in the library: the enlargement of the residue field until the structural map factors
through a given presheaf-surjective morphism is
`AlgebraicGeometry.Space.exists_geometricPoint_factorThroughChart`, and the geometric point of
the base change is
`AlgebraicGeometry.Space.exists_geometricPoint_pullback_fst_eq`. The
presheaf-surjectivity they need holds for *every* morphism of spectra of fields, the target
having one point and the source at least one; it is produced here by
`AlgebraicGeometry.Space.presheaf_yoneda_map_of_inverseImage`. -/
theorem exists_geometricPoint_lift_fieldSpectrum
    {k : Type u} [Field k] (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (V : BigFppfOver B S hS) (hV : IsFieldObject B S hS V)
    (ρ : V ⟶ (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS) : BigFppfOver B S hS))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (π : F ⟶ yoneda.obj ((Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS) : BigFppfOver B S hS)))
    (z : Space.points B S hS F) :
    ∃ (z' : Space.GeometricPoint B S hS F)
      (c₀ : z'.val.siteObject ⟶ (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS) : BigFppfOver B S hS))
      (t : z'.val.siteObject ⟶ V),
      π.app (Opposite.op z'.val.siteObject) z'.val.value = c₀ ∧ t ≫ ρ = c₀ ∧
        z'.image = z ∧
        ∃ w : Space.GeometricPoint B S hS
            (CategoryTheory.Limits.pullback π (yoneda.map c₀)),
          Space.geometricPointMap
            (CategoryTheory.Limits.pullback.fst π (yoneda.map c₀)) w = z' := by
  obtain ⟨k', hk', ⟨eV⟩⟩ := hV
  let _ : Field k' := hk'
  have hne : Nonempty ((BigFppfOver.toScheme B S hS).obj V) :=
    ⟨eV.inv.base (Classical.arbitrary (Spec (CommRingCat.of k')))⟩
  have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj
      (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS) : BigFppfOver B S hS)) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  have hsurj : Surjective ((BigFppfOver.toScheme B S hS).map ρ) := inferInstance
  obtain ⟨z', c₀, t, hπ, hfac, himg⟩ :=
    Space.exists_geometricPoint_factorThroughChart B S hS V (yoneda.map ρ)
      (Space.presheaf_yoneda_map_of_inverseImage B S hS inferInstance ρ hsurj)
      hk b (𝟙 _) π z
  refine ⟨z', c₀, t, hπ, ?_, himg, Space.exists_geometricPoint_pullback_fst_eq
    B S hS π z' c₀ hπ⟩
  refine yoneda.map_injective ?_
  rw [Functor.map_comp, hfac, Category.comp_id]

end AlgebraicGeometry.Stack

end
