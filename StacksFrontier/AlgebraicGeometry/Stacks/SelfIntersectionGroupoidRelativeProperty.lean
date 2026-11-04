module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFppfLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionFlatProjections
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoid
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# The relative property of a point inherited by its self-intersection groupoid

Let `S` be a scheme contained in a big fppf site `B`, let `𝒳` be a category fibred in groupoids
over the big fppf site of `S`, let `𝒰` be another one representable by an algebraic space `U`, and
let `f : 𝒰 ⟶ 𝒳` be a 1-morphism whose self-intersection `ℛ = 𝒰 ×_{f, 𝒳, f} 𝒰` is representable by
an algebraic space `R`. The target and source morphisms `t`, `s : R ⟶ U` of the self-intersection
groupoid of Stacks 04T4 (4) are the morphisms of algebraic spaces named by the two projections
`pr₀`, `pr₁ : ℛ ⟶ 𝒰`, each of which is a base change of `f` along itself. So every property `P` of
morphisms of algebraic spaces which `f` has in the relative sense of Stacks 03YK is inherited by
`s` and `t`.

This is the step that the proofs of Stacks 04T5 (1) and of the second clause of Stacks 04WY make
to pass from a hypothesis on `f` to a conclusion about the structure morphisms of the groupoid.

## Main results

* `AlgebraicGeometry.Stack.SelfIntersection.prop_relationTarget` and
  `AlgebraicGeometry.Stack.SelfIntersection.prop_relationSource`: the structure morphisms of the
  self-intersection groupoid have every relative property of `f`.
* `AlgebraicGeometry.Stack.SelfIntersection.isFlat_relationSource_and_relationTarget`:
  **Stacks 04WY**, the flatness half of its clause on the structure morphisms.
* `...isLocallyOfFinitePresentation_relationSource_and_relationTarget`: **Stacks 04WY**, the
  local finite presentation half of the same clause.
* `AlgebraicGeometry.Stack.SelfIntersection.isSmooth_relationSource_and_relationTarget`:
  **Stacks 04T5 (1)**, the same at the smooth property.

## Implementation notes

The two inputs are both general in the property: Stacks 045C
(`AlgebraicGeometry.Stack.hasRelativeProperty_baseChange`) carries the relative property to the
first projection of a 2-fibre product square, and the bridge of Stacks 04XB
(`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap`) reads the relative
property of a 1-morphism between represented categories off the induced morphism of representing
presheaves. The canonical square of the cospan `(f, f)` has apex the self-intersection on the
nose, and its first projection induces exactly
`AlgebraicGeometry.Stack.SelfIntersection.relationTarget`, so the two compose with no comparison
to insert.

Both inputs speak of the *first* projection of a 2-commutative square, while the source morphism
is named by the second. The second projection is made into a first one by
`CategoryTheory.Bicategory.isTwoFibreProduct_swap`: exchanging the two legs of a 2-commutative
square and inverting its filler sends 2-fibre products to 2-fibre products, so the swapped
canonical square is again one and its first projection is `pr₁`.

Both halves of the clause of Stacks 04WY are instances of
`AlgebraicGeometry.Stack.SelfIntersection.prop_relationSource` and `...prop_relationTarget`, whose
property must be local at the target for the fppf precoverage — the form in which the relative
properties of Stacks 03YK ask for it. Flatness is so by Stacks 041W and the comparison of
precoverages, and that instance is recorded here because flatness, unlike smoothness
(Stacks 0429), does not yet carry it. Local finite presentation is so by
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_isLocalAtTarget_fppf`, which is proved at
the fppf level rather than inherited from an fpqc form: the argument that gives target locality
for flatness composes the property with a member of the covering family, and local finite
presentation after flat is not locally of finite presentation, whereas a member of an *fppf*
covering is itself locally of finite presentation.

Base-change stability of local finite presentation (Stacks 03XR) is available as a theorem rather
than an instance, and is promoted here beside the flat one: a relative property appears in the
*statement* of the lfp clause, so the instance must be in scope before the proof begins and
cannot be supplied inside it.

## References

* [Stacks Project, Tag 03XR](https://stacks.math.columbia.edu/tag/03XR)
* [Stacks Project, Tag 041W](https://stacks.math.columbia.edu/tag/041W)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04T5](https://stacks.math.columbia.edu/tag/04T5)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04WY](https://stacks.math.columbia.edu/tag/04WY)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v

/- Stacks 03MO, stability of flatness under base change, and Stacks 03XR, the same for local
finite presentation, are proved in the tree as theorems rather than instances; the relative
properties of Stacks 03YK ask for them as instances already when their statements are
elaborated. The same holds of locality at the target for the fppf precoverage, Stacks 041W. -/
attribute [instance] isFlat_isStableUnderBaseChange
  isLocallyOfFinitePresentation_isStableUnderBaseChange
  isFlat_isLocalAtTarget_fppf

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack.SelfIntersection

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (𝒰 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
variable (f : 𝒰 ⟶ 𝒳) (U R : AlgebraicSpaces B S hS)
variable (eU : StacksRepresentableCFG.EquivalenceOver
    𝒰.val.p (presheafOfCategories (U.obj ⋙ typeToCat)).p)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (relation B S hS 𝒰 𝒳 f.hom).val.p (presheafOfCategories (R.obj ⋙ typeToCat)).p)

/-- The canonical 2-fibre product square of the cospan `(f, f)`, whose apex is the
self-intersection `ℛ = 𝒰 ×_{f, 𝒳, f} 𝒰` of `f` and whose first projection is `pr₀`. -/
abbrev relationSquare : Bicategory.TwoCommSq f f :=
  CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f f

/-- The apex of `AlgebraicGeometry.Stack.SelfIntersection.relationSquare` is the
self-intersection of `f`. -/
theorem relationSquare_pt : (relationSquare B S hS 𝒰 𝒳 f).pt = relation B S hS 𝒰 𝒳 f.hom := rfl

/-- The first projection of the canonical square induces the target morphism of the
self-intersection groupoid of Stacks 04T4 (4). -/
theorem representingMap_relationSquare_fst :
    (ObjectProperty.homMk
        (representingMap B S hS (relation B S hS 𝒰 𝒳 f.hom) 𝒰 R.obj U.obj eR eU
          (relationSquare B S hS 𝒰 𝒳 f).fst) :
      R ⟶ U) =
    relationTarget eU eR :=
  rfl

/-- A 2-fibre product square of `(f, f)` with represented apex has its first projection induce a
morphism of algebraic spaces with every relative property `P` of `f`. -/
private theorem prop_representingMap_of_isTwoFibreProduct
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hP : HasRelativeProperty.{u, u, u + 1, u} B S hS P f hf)
    (sq : Bicategory.TwoCommSq f f) (hsq : Bicategory.IsTwoFibreProduct sq)
    (eR' : StacksRepresentableCFG.EquivalenceOver
      sq.pt.val.p (presheafOfCategories (R.obj ⋙ typeToCat)).p) :
    P (ObjectProperty.homMk
      (representingMap B S hS sq.pt 𝒰 R.obj U.obj eR' eU sq.fst) : R ⟶ U) :=
  (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS P sq.fst _ R.obj U.obj R.property
    U.property eR' eU).mp
    (hasRelativeProperty_baseChange.{u, u, u, u} B S hS P 𝒰 𝒳 𝒰 f f sq hsq hf hP)

/-- **The target morphism of the self-intersection groupoid inherits every relative property of
the point.** Let `P` be a property of morphisms of algebraic spaces over `S` which is stable under
base change and local at the target for the fppf topology, and let `f : 𝒰 ⟶ 𝒳` be a 1-morphism
representable by algebraic spaces which has `P` in the relative sense of Stacks 03YK. If `𝒰` and
the self-intersection `ℛ = 𝒰 ×_{f, 𝒳, f} 𝒰` are represented by algebraic spaces `U` and `R`, then
the target morphism `t : R ⟶ U` of Stacks 04T4 (4) has `P`.

The first projection `pr₀ : ℛ ⟶ 𝒰` is the base change of `f` along itself, so it has `P` in the
relative sense by Stacks 045C; and it names `t`, so `t` has `P` by the bridge of Stacks 04XB. -/
theorem prop_relationTarget
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hP : HasRelativeProperty.{u, u, u + 1, u} B S hS P f hf) :
    P (relationTarget eU eR) := by
  rw [← representingMap_relationSquare_fst B S hS 𝒰 𝒳 f U R eU eR]
  exact prop_representingMap_of_isTwoFibreProduct B S hS 𝒰 𝒳 f U R eU P hf hP _
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f f) eR

/-- The second projection of the canonical square induces the source morphism of the
self-intersection groupoid of Stacks 04T4 (4). It is the first projection of the square with its
two legs exchanged. -/
theorem representingMap_relationSquare_swap_fst :
    (ObjectProperty.homMk
        (representingMap B S hS (relation B S hS 𝒰 𝒳 f.hom) 𝒰 R.obj U.obj eR eU
          (relationSquare B S hS 𝒰 𝒳 f).swap.fst) :
      R ⟶ U) =
    relationSource eU eR :=
  rfl

/-- **The source morphism of the self-intersection groupoid inherits every relative property of
the point.** The hypotheses are those of
`AlgebraicGeometry.Stack.SelfIntersection.prop_relationTarget`, and the conclusion is the same
for the source morphism `s : R ⟶ U` of Stacks 04T4 (4).

The second projection `pr₁ : ℛ ⟶ 𝒰` is the first projection of the 2-fibre product square with
its two legs exchanged (`CategoryTheory.Bicategory.isTwoFibreProduct_swap`), hence a base change
of `f` along itself, so the argument is the same as for the target morphism. -/
theorem prop_relationSource
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hP : HasRelativeProperty.{u, u, u + 1, u} B S hS P f hf) :
    P (relationSource eU eR) := by
  rw [← representingMap_relationSquare_swap_fst B S hS 𝒰 𝒳 f U R eU eR]
  exact prop_representingMap_of_isTwoFibreProduct B S hS 𝒰 𝒳 f U R eU P hf hP _
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f f)) eR

/-- **Stacks 04WY**, the flatness half of its clause on the structure morphisms of the groupoid.
If the point `f : 𝒰 ⟶ 𝒳` is flat in the relative sense of Stacks 03YK, then the source and target
morphisms `s`, `t : R ⟶ U` of the self-intersection groupoid of Stacks 04T4 (4) are flat
morphisms of algebraic spaces over `S`.

The source statement is the remark that the conclusion of Stacks 04T5 survives weakening
smoothness of `f` to flatness together with local finite presentation, and that `s` and `t` are
then flat and locally of finite presentation; this is its flatness half. -/
@[stacks 04WY "second clause, flatness half: the structure morphisms of the groupoid are flat"]
theorem isFlat_relationSource_and_relationTarget
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hP : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) => Space.IsFlat B S hS g.hom) f hf) :
    Space.IsFlat B S hS (relationSource eU eR).hom ∧
      Space.IsFlat B S hS (relationTarget eU eR).hom :=
  ⟨prop_relationSource B S hS 𝒰 𝒳 f U R eU eR
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) => Space.IsFlat B S hS g.hom) hf hP,
    prop_relationTarget B S hS 𝒰 𝒳 f U R eU eR
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) => Space.IsFlat B S hS g.hom) hf hP⟩

/-- **Stacks 04WY**, the local finite presentation half of its clause on the structure morphisms
of the groupoid. If the point `f : 𝒰 ⟶ 𝒳` is locally of finite presentation in the relative sense
of Stacks 03YK, then the source and target morphisms `s`, `t : R ⟶ U` of the self-intersection
groupoid of Stacks 04T4 (4) are locally of finite presentation.

The source statement is the remark that the conclusion of Stacks 04T5 survives weakening
smoothness of `f` to flatness together with local finite presentation, and that `s` and `t` are
then flat and locally of finite presentation; this is its local finite presentation half. The
flatness half is
`AlgebraicGeometry.Stack.SelfIntersection.isFlat_relationSource_and_relationTarget`. -/
@[stacks 04WY "second clause, lfp half: the structure morphisms are locally of finite presentation"]
theorem isLocallyOfFinitePresentation_relationSource_and_relationTarget
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hP : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) =>
        Space.IsLocallyOfFinitePresentation B S hS g.hom) f hf) :
    Space.IsLocallyOfFinitePresentation B S hS
        (relationSource eU eR).hom ∧
      Space.IsLocallyOfFinitePresentation B S hS
        (relationTarget eU eR).hom :=
  ⟨prop_relationSource B S hS 𝒰 𝒳 f U R eU eR
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) =>
        Space.IsLocallyOfFinitePresentation B S hS g.hom) hf hP,
    prop_relationTarget B S hS 𝒰 𝒳 f U R eU eR
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (g : F ⟶ G) =>
        Space.IsLocallyOfFinitePresentation B S hS g.hom) hf hP⟩

/-- **Stacks 04T5 (1).** If the point `f : 𝒰 ⟶ 𝒳` is smooth in the sense of Stacks 04XB, then the
source and target morphisms `s`, `t : R ⟶ U` of the self-intersection groupoid of Stacks 04T4 (4)
are smooth morphisms of algebraic spaces over `S`. -/
@[stacks 04T5 "part (1): the structure morphisms of the groupoid are smooth"]
theorem isSmooth_relationSource_and_relationTarget (hf : IsRelativelySmooth B S hS f) :
    Space.IsSmooth B S hS (relationSource eU eR).hom ∧
      Space.IsSmooth B S hS (relationTarget eU eR).hom := by
  obtain ⟨hfr, hPf⟩ := hf
  exact ⟨prop_relationSource B S hS 𝒰 𝒳 f U R eU eR
      (Space.smoothMorphismProperty B S hS) hfr hPf,
    prop_relationTarget B S hS 𝒰 𝒳 f U R eU eR
      (Space.smoothMorphismProperty B S hS) hfr hPf⟩

end AlgebraicGeometry.Stack.SelfIntersection

end
