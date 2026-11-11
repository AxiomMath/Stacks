module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientAtlasFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.TwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence

/-!
# The self-square of the quotient-stack projection is the arrow space

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, and let `π : S_U ⟶ [U/R]` be the canonical projection of
Stacks 044R. **Stacks 04M9** says that the square

    S_R ---s---> S_U
     |            |
     t            π
     v            v
    S_U ---π---> [U/R]

is 2-cartesian. This file proves it in the 2-category of categories fibred in groupoids, and
deduces **Stacks 06FH**: if `s` and `t` are flat and locally of finite presentation, then `π` is
surjective, flat and locally of finite presentation.

## Main definitions

* `AlgebraicGeometry.Stack.QuotientAtlas.liftedArrowSpace`: the arrow space `R` as a category
  fibred in groupoids in the morphism universe of the quotient stack.
* `AlgebraicGeometry.Stack.QuotientAtlas.arrowSelfSquare`: the square above, in the 2-category of
  categories fibred in groupoids, with apex the arrow space, first leg `s`, second leg `t` and
  filler the canonical 2-arrow of Stacks 044S.
* `AlgebraicGeometry.Stack.QuotientAtlas.arrowSelfSquareToArrowSpace`: the universe-lowering
  equivalence out of the apex of the square.
* `AlgebraicGeometry.Stack.QuotientAtlas.presentationOfRepresentable`: a presentation of a
  groupoid in algebraic spaces from the representability of `π`.

## Main results

* `AlgebraicGeometry.Stack.QuotientAtlas.isTwoFibreProduct_arrowSelfSquare`: **Stacks 04M9** for
  the cospan `(π, π)`, in categories fibred in groupoids.
* `AlgebraicGeometry.Stack.QuotientAtlas.relativeProperty_of_prop_source`: every property of
  morphisms of algebraic spaces stable under base change and local at the target for the fppf
  topology passes from `s` to `π`.
* `AlgebraicGeometry.Stack.QuotientAtlas.isFlat_relativeProperty`,
  `AlgebraicGeometry.Stack.QuotientAtlas.isLocallyOfFinitePresentation_relativeProperty` and
  `AlgebraicGeometry.Stack.QuotientAtlas.isSurjective_relativeProperty`: the three conclusions
  of **Stacks 06FH**.
* `AlgebraicGeometry.Stack.QuotientAtlas.surjective_flat_lfp_quotientStackProjectionHom`: the same
  three, named as the relative property of Stacks 03YK at a given witness of representability.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04SK](https://stacks.math.columbia.edu/tag/04SK)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 04TB](https://stacks.math.columbia.edu/tag/04TB)
* [Stacks Project, Tag 04WZ](https://stacks.math.columbia.edu/tag/04WZ)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 06FH](https://stacks.math.columbia.edu/tag/06FH)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.QuotientAtlas

universe u t

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The arrow space of a groupoid in algebraic spaces, as a category fibred in groupoids in the
morphism universe of the quotient stack. -/
def liftedArrowSpace (G : GroupoidInAlgebraicSpaces C S hS B) :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver C S hS) :=
  CatFiberedInGroupoids.mk (liftedFibredCategory G.arrows)
    (isFiberedInGroupoids_uliftHom _ (fibredCategory C S hS G.arrows.obj).property)

/-- The source-target square of a groupoid over its quotient stack, in the 2-category of
categories fibred in groupoids. -/
noncomputable def arrowSelfSquare (G : GroupoidInAlgebraicSpaces C S hS B) :
    Bicategory.TwoCommSq (quotientStackProjectionHom G) (quotientStackProjectionHom G) := by
  let α := liftedQuotientStackTwoArrow G
  haveI (x : (liftedFibredCategory G.arrows).obj) : IsIso (α.app x) := by
    have hα := α.isHomLift' x
    have hcart := (isFiberedInGroupoids_quotientStack G).isStronglyCartesian_homLift
      (𝟙 ((liftedFibredCategory G.arrows).p.obj x)) (α.app x)
    let := hcart
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso
      (p := (quotientStack G).p)
      (f := 𝟙 ((liftedFibredCategory G.arrows).p.obj x)) (α.app x)
  let β :
      (BasedFunctor.comp (liftedAssociatedMap G.source)
        (liftedQuotientStackProjection G)).toFunctor ≅
      (BasedFunctor.comp (liftedAssociatedMap G.target)
        (liftedQuotientStackProjection G)).toFunctor :=
    NatIso.ofComponents (fun x ↦ asIso (α.app x))
      (by intro x y f; exact α.naturality f)
  let γ := BasedNatIso.mkNatIso β (fun x ↦ α.isHomLift' x)
  exact {
    pt := liftedArrowSpace G
    fst := Bicategory.InducedBicategory.mkHom (liftedAssociatedMap G.source)
    snd := Bicategory.InducedBicategory.mkHom (liftedAssociatedMap G.target)
    iso := Bicategory.InducedBicategory.isoMk γ }

/-- **Stacks 04M9 for the cospan `(π, π)`, in categories fibred in groupoids.** The square
`AlgebraicGeometry.Stack.QuotientAtlas.arrowSelfSquare` is a 2-fibre product: the arrow space `R`
of the groupoid *is* `S_U ×_{[U/R]} S_U`, with first leg the source map `s`. -/
noncomputable def isTwoFibreProduct_arrowSelfSquare
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Bicategory.IsTwoFibreProduct (arrowSelfSquare G) :=
  Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (isTwoFibreProduct_quotientStackProjectionSelfSquare G)
    (CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _
      (arrowSelfSquare G))
    (isEquivalence_arrowToRelativeProduct G)

/-- The comparison of the apex of `AlgebraicGeometry.Stack.QuotientAtlas.arrowSelfSquare` with the
fibred category of the arrow space. -/
def arrowSelfSquareToArrowSpace (G : GroupoidInAlgebraicSpaces C S hS B) :
    (arrowSelfSquare G).pt.val ⥤ᵇ (fibredCategory C S hS G.arrows.obj).val :=
  liftedFibredCategoryDown G.arrows

/-- `AlgebraicGeometry.Stack.QuotientAtlas.arrowSelfSquareToArrowSpace` is an equivalence. -/
instance isEquivalence_arrowSelfSquareToArrowSpace
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Functor.IsEquivalence (arrowSelfSquareToArrowSpace G).toFunctor :=
  (ULiftHom.equiv (C := (fibredCategory C S hS G.arrows.obj).val.obj)).isEquivalence_inverse

/-- `AlgebraicGeometry.Stack.objectSpaceLiftDown` is an equivalence. -/
instance isEquivalence_objectSpaceLiftDown
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    Functor.IsEquivalence (objectSpaceLiftDown G).toFunctor :=
  (ULiftHom.equiv (C := (fibredCategory C S hS G.objects.obj).val.obj)).isEquivalence_inverse

/-- **Every relative property of the source map passes to the quotient-stack projection.** Let
`G = (U, R, s, t, c)` be a groupoid in algebraic spaces over `S` and let `P` be a property of
morphisms of algebraic spaces over `S` stable under base change and local at the target for the
fppf topology. If `s` has `P`, then the canonical projection `π : S_U ⟶ [U/R]` of Stacks 044R
satisfies the condition of Stacks 03YK at `P`: every algebraic space representing a base change of
`π` along a scheme-valued point of `[U/R]` has structural morphism with `P`. -/
theorem relativeProperty_of_prop_source
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (P : MorphismProperty (AlgebraicSpaces C S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} C S hS)]
    (hP : P G.source) :
    RelativeProperty.{u, u + 1, u + 1} C S hS P (quotientStackProjectionHom G) := by
  refine relativeProperty_quotientStackProjectionHom_of_representingMap.{u, t} C S hS G P
    (arrowSelfSquare G) (isTwoFibreProduct_arrowSelfSquare G)
    (associatedMap C S hS G.source.hom).1
    (isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace C S hS
      (associatedMap C S hS G.source.hom).1
      (isRepresentableByAlgebraicSpace_fibredCategory C S hS _ G.arrows.property)
      (isRepresentableByAlgebraicSpace_fibredCategory C S hS _ G.objects.property))
    (arrowSelfSquareToArrowSpace G) (objectSpaceLiftDown G) (Iso.refl _)
    G.arrows.obj G.objects.obj G.arrows.property G.objects.property
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) ?_
  rwa [representingMap_associatedMap]

/-- **Every relative property of the source map passes to the representable quotient-stack
projection.** Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over `S` and let `P` be a
property of morphisms of algebraic spaces over `S` stable under base change and local at the target
for the fppf topology. If `s` has `P` and the canonical projection `π : S_U ⟶ [U/R]` of Stacks 044R
is representable, then `π` has `P` in the relative sense of Stacks 03YK. -/
theorem hasRelativeProperty_of_prop_source
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (P : MorphismProperty (AlgebraicSpaces C S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} C S hS)]
    (hpi : IsRepresentableByAlgebraicSpaces C S hS (quotientStackProjectionHom G).hom)
    (hP : P G.source) :
    HasRelativeProperty.{u, u + 1, u + 1, max u t} C S hS P
      (quotientStackProjectionHom G) hpi :=
  relativeProperty_of_prop_source.{u, t} G P hP

/-! ### A presentation from the representability of the projection alone -/

/-- **A presentation of a groupoid in algebraic spaces from the representability of its
projection.** The `AlgebraicGeometry.Stack.QuotientAtlas.Presentation` of `G` whose square is
`AlgebraicGeometry.Stack.QuotientAtlas.arrowSelfSquare`, given the representability of
`π : S_U ⟶ [U/R]`. -/
noncomputable def presentationOfRepresentable (G : GroupoidInAlgebraicSpaces C S hS B)
    (hpi : IsRepresentableByAlgebraicSpaces C S hS (quotientStackProjectionHom G).hom) :
    Presentation G where
  representable := hpi
  square := arrowSelfSquare G
  isTwoFibreProduct := isTwoFibreProduct_arrowSelfSquare G
  fstRepresentable :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u + 1, u + 1} C S hS _ _ _
      (quotientStackProjectionHom G) (quotientStackProjectionHom G) (arrowSelfSquare G)
      (isTwoFibreProduct_arrowSelfSquare G) hpi
  arrowStack := fibredCategory C S hS G.arrows.obj
  objectStack := fibredCategory C S hS G.objects.obj
  leg := (associatedMap C S hS G.source.hom).1
  legRepresentable :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace C S hS
      (associatedMap C S hS G.source.hom).1
      (isRepresentableByAlgebraicSpace_fibredCategory C S hS _ G.arrows.property)
      (isRepresentableByAlgebraicSpace_fibredCategory C S hS _ G.objects.property)
  toArrowStack := arrowSelfSquareToArrowSpace G
  toObjectStack := objectSpaceLiftDown G
  isEquivalence_toArrowStack := isEquivalence_arrowSelfSquareToArrowSpace G
  isEquivalence_toObjectStack := isEquivalence_objectSpaceLiftDown G
  comm := Iso.refl _
  arrowsEquivalence := StacksRepresentableCFG.EquivalenceOver.refl _
  objectsEquivalence := StacksRepresentableCFG.EquivalenceOver.refl _
  leg_eq := by rw [representingMap_associatedMap]; rfl

/-! ### Stacks 06FH -/

/-- **The quotient-stack projection is flat.** Let `G = (U, R, s, t, c)` be a groupoid in algebraic
spaces over a scheme `S` of a big fppf site and assume its source and target maps `s`, `t` are flat
and locally of finite presentation. Then the canonical projection `π : S_U ⟶ [U/R]` of Stacks 044R
is flat in the sense of Stacks 03YK: every algebraic space representing a base change of `π` along
a scheme-valued point of `[U/R]` has flat structural morphism. -/
theorem isFlat_relativeProperty (G : GroupoidInAlgebraicSpaces C S hS B)
    (hsflat : Space.IsFlat C S hS G.source.hom)
    (_htflat : Space.IsFlat C S hS G.target.hom)
    (_hslfp : Space.IsLocallyOfFinitePresentation C S hS G.source.hom)
    (_htlfp : Space.IsLocallyOfFinitePresentation C S hS G.target.hom) :
    RelativeProperty.{u, u + 1, u + 1} C S hS
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (f : X ⟶ Y) => Space.IsFlat C S hS f.hom)
      (quotientStackProjectionHom G) :=
  relativeProperty_of_prop_source.{u, u} G _ hsflat

/-- **The quotient-stack projection is locally of finite presentation.** Let `G = (U, R, s, t, c)`
be a groupoid in algebraic spaces over a scheme `S` of a big fppf site and assume its source and
target maps `s`, `t` are flat and locally of finite presentation. Then the canonical projection
`π : S_U ⟶ [U/R]` of Stacks 044R is locally of finite presentation in the sense of Stacks 03YK:
every algebraic space representing a base change of `π` along a scheme-valued point of `[U/R]` has
structural morphism locally of finite presentation. -/
theorem isLocallyOfFinitePresentation_relativeProperty (G : GroupoidInAlgebraicSpaces C S hS B)
    (_hsflat : Space.IsFlat C S hS G.source.hom)
    (_htflat : Space.IsFlat C S hS G.target.hom)
    (hslfp : Space.IsLocallyOfFinitePresentation C S hS G.source.hom)
    (_htlfp : Space.IsLocallyOfFinitePresentation C S hS G.target.hom) :
    RelativeProperty.{u, u + 1, u + 1} C S hS
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (f : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation C S hS f.hom)
      (quotientStackProjectionHom G) :=
  relativeProperty_of_prop_source.{u, u} G _ hslfp

/-- **The quotient-stack projection is surjective.** Let `G = (U, R, s, t, c)` be a groupoid in
algebraic spaces over a scheme `S` of a big fppf site and assume its source and target maps `s`,
`t` are flat and locally of finite presentation. Then the canonical projection `π : S_U ⟶ [U/R]` of
Stacks 044R is surjective in the sense of Stacks 03YK: every algebraic space representing a base
change of `π` along a scheme-valued point of `[U/R]` has surjective structural morphism. -/
theorem isSurjective_relativeProperty (G : GroupoidInAlgebraicSpaces C S hS B)
    (_hsflat : Space.IsFlat C S hS G.source.hom)
    (_htflat : Space.IsFlat C S hS G.target.hom)
    (_hslfp : Space.IsLocallyOfFinitePresentation C S hS G.source.hom)
    (_htlfp : Space.IsLocallyOfFinitePresentation C S hS G.target.hom) :
    RelativeProperty.{u, u + 1, u + 1} C S hS
      (Space.surjectiveMorphismProperty C S hS)
      (quotientStackProjectionHom G) :=
  relativeProperty_of_prop_source.{u, u} G _ (isSurjective_source G)

/-- **Stacks 06FH, all three conclusions.** Let `G = (U, R, s, t, c)` be a groupoid in algebraic
spaces over `S` whose source and target are flat and locally of finite presentation, and let
`π : S_U ⟶ [U/R]` be the canonical projection of Stacks 044R, assumed representable. Then `π` is
surjective, flat and locally of finite presentation in the relative sense of Stacks 03YK. -/
theorem surjective_flat_lfp_quotientStackProjectionHom
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (hsflat : Space.IsFlat C S hS G.source.hom)
    (htflat : Space.IsFlat C S hS G.target.hom)
    (hslfp : Space.IsLocallyOfFinitePresentation C S hS G.source.hom)
    (htlfp : Space.IsLocallyOfFinitePresentation C S hS G.target.hom)
    (hpi : IsRepresentableByAlgebraicSpaces C S hS (quotientStackProjectionHom G).hom) :
    HasRelativeProperty.{u, u + 1, u + 1, u} C S hS
        (Space.surjectiveMorphismProperty C S hS) (quotientStackProjectionHom G) hpi ∧
      HasRelativeProperty.{u, u + 1, u + 1, u} C S hS
        (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (f : X ⟶ Y) => Space.IsFlat C S hS f.hom)
        (quotientStackProjectionHom G) hpi ∧
      HasRelativeProperty.{u, u + 1, u + 1, u} C S hS
        (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (f : X ⟶ Y) =>
          Space.IsLocallyOfFinitePresentation C S hS f.hom)
        (quotientStackProjectionHom G) hpi :=
  ⟨isSurjective_relativeProperty G hsflat htflat hslfp htlfp,
    isFlat_relativeProperty G hsflat htflat hslfp htlfp,
    isLocallyOfFinitePresentation_relativeProperty G hsflat htflat hslfp htlfp⟩

end AlgebraicGeometry.Stack.QuotientAtlas

end
