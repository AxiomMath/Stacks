module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Completion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Quasi-compactness for a morphism of completions

Let `S` be a scheme contained in a big fppf site `B`, let `f : X' ⟶ X` be a morphism of
algebraic spaces over `S` and let `T` be a set of points of `X`. **Stacks 0GDE** says that if
`f` is quasi-compact then so is the induced morphism of completions
`f_{/T} : X'_{/|f|⁻¹ T} ⟶ X_{/T}`.

## Main results

* `AlgebraicGeometry.FormalSpace.isQuasiCompact_completionSheafMap`: **Stacks 0GDE**, with
  quasi-compactness of `f_{/T}` in the form of Bootstrap, Definition 03XZ.
* `AlgebraicGeometry.FormalSpace.isQuasiCompact_completionSheafMap_of_agreesOnAlgebraicSpaces`:
  the same with quasi-compactness read as `AlgebraicGeometry.FormalSpace.IsQuasiCompact`, the
  form of Stacks 0AJC, granted the agreement of the two notions of a quasi-compact space on an
  algebraic space.

## Implementation notes

The completion square of Stacks 0APV,
`AlgebraicGeometry.Space.isPullback_completionSheafMap`, exhibits `f_{/T}` as a base change of
the universe lift of `f`, so the Bootstrap condition of Stacks 03XZ for a property invariant
under isomorphism descends from that lift by
`AlgebraicGeometry.Space.hasPropertyULift_of_isPullback`, exactly as it does for the étale
property in `StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionEtale` and for the conjuncts
of properness in `StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionProper`. The
identification of the ambient sheaves of the square with the universe lifts themselves is the
one already used for representability in
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpacesULift_completionMap`.

What remains is that the universe lift of `f` satisfies the Bootstrap condition for
quasi-compactness. A base change of that lift along a universe-lifted scheme-valued point of
its target is the lift of a base change of `f` in the value universe of the site, where
quasi-compactness holds by Stacks 03HF,
`AlgebraicGeometry.Space.IsQuasiCompact.of_isPullback`; quasi-compactness then transfers to
the universe lift by `AlgebraicGeometry.Space.isQuasiCompactULift_whiskerRight_iff`. No
étale-local analysis of `f` is needed, so neither reductions nor thickenings enter — in
contrast to the source's proof, which identifies the morphism of reductions of the two
completions with the morphism of reduced induced structures on `|f|⁻¹ T` and `T` and runs the
argument there.

The quasi-compactness delivered is the Bootstrap one: `f_{/T}` is representable by algebraic
spaces and each of its base changes along a scheme-valued point of its target is a
quasi-compact morphism of algebraic spaces. For a morphism representable by algebraic spaces
that is the quasi-compactness of Stacks 0AJC,
`AlgebraicGeometry.FormalSpace.IsQuasiCompact`, by Stacks 0AM2,
`AlgebraicGeometry.FormalSpace.isQuasiCompact_iff_hasPropertyULift`; but the proof of that
equivalence rests on the agreement of the two notions of a quasi-compact space on an algebraic
space, `AlgebraicGeometry.FormalSpace.QuasiCompactSpaceAgreesOnAlgebraicSpaces`, which this
library does not carry — the direction needed here asks for an *affine formal* algebraic space
mapping étale and surjectively onto a quasi-compact algebraic space, where the affine étale
atlas of Stacks 03H6 supplies only an affine scheme in the site, and recognising that as an
affine formal algebraic space is a further step. So that agreement is the hypothesis of
`isQuasiCompact_completionSheafMap_of_agreesOnAlgebraicSpaces`, which states the conclusion in
the form of Stacks 0AJC.

Closedness of `T` is not used: it is what makes the two completions formal algebraic spaces,
which neither the Bootstrap condition nor the condition of Stacks 0AJC refers to, so the
statements are proved for an arbitrary set of points, as are the results of
`StacksFrontier.AlgebraicGeometry.FormalSpace.Completion`.

## References

* [Stacks Project, Tag 0GDE](https://stacks.math.columbia.edu/tag/0GDE)
* [Stacks Project, Tag 0APV](https://stacks.math.columbia.edu/tag/0APV)
* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03HF](https://stacks.math.columbia.edu/tag/03HF)
* [Stacks Project, Tag 0AJC](https://stacks.math.columbia.edu/tag/0AJC)
* [Stacks Project, Tag 0AM2](https://stacks.math.columbia.edu/tag/0AM2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/- Instance search for pullbacks of presheaves on `BigFppfOver B S hS` times out under Lean
v4.35.0; supply the functor-category instance. -/
local instance (priority := high) : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

local instance (priority := high) {Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ W)
    (g : Z ⟶ W) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit (cospan f g)

/-! ### Transferring quasi-compactness to a universe lift -/

/-- The universe lift of a quasi-compact morphism of algebraic spaces over `S` satisfies the
Bootstrap condition of Stacks 03XZ for quasi-compactness: a base change of the lift along a
universe-lifted scheme-valued point of its target is the lift of a base change of the morphism
itself, which is quasi-compact by Stacks 03HF. -/
private theorem hasPropertyULift_whiskerRight_of_isQuasiCompact
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (hf : Space.IsQuasiCompact B S hS f)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (Functor.whiskerRight f uliftFunctor.{u + 1})) :
    Space.HasPropertyULift.{u + 1} B S hS
      (Space.quasiCompactPropertyULift.{u + 1} B S hS)
      (Functor.whiskerRight f uliftFunctor.{u + 1}) hrep := by
  let C := BigFppfOver B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1}
  intro U ξ
  obtain ⟨ξ₀, hξ₀⟩ := H.map_surjective (ξ : H.obj (yoneda.obj U) ⟶ H.obj X)
  have hq : Space.IsQuasiCompact B S hS (pullback.fst ξ₀ f) :=
    Space.IsQuasiCompact.of_isPullback B S hS (IsPullback.of_hasPullback ξ₀ f).flip hf
  have hql : Space.IsQuasiCompactULift.{u + 1} B S hS
      (Functor.whiskerRight (pullback.fst ξ₀ f) uliftFunctor.{u + 1}) :=
    (Space.isQuasiCompactULift_whiskerRight_iff B S hS (pullback.fst ξ₀ f)).mpr hq
  have hsq : IsPullback (H.map (pullback.fst ξ₀ f)) (H.map (pullback.snd ξ₀ f)) ξ
      (Functor.whiskerRight f uliftFunctor.{u + 1}) := by
    rw [← hξ₀]
    exact (IsPullback.of_hasPullback ξ₀ f).map H
  have heq : hsq.isoPullback.inv ≫ H.map (pullback.fst ξ₀ f) =
      pullback.fst ξ (Functor.whiskerRight f uliftFunctor.{u + 1}) :=
    (Iso.inv_comp_eq hsq.isoPullback).mpr hsq.isoPullback_hom_fst.symm
  exact heq ▸ Space.isQuasiCompactULift_precomp.{u + 1} B S hS hsq.isoPullback.symm _ hql

/-! ### Stacks 0GDE -/

/-- **Stacks 0GDE.** Let `f : X' ⟶ X` be a morphism of algebraic spaces over `S` and let `T`
be a set of points of `X`. If `f` is quasi-compact, then the induced morphism of completions
`f_{/T} : X'_{/|f|⁻¹ T} ⟶ X_{/T}` is quasi-compact: it is representable by algebraic spaces
and each of its base changes along a scheme-valued point of its target is a quasi-compact
morphism of algebraic spaces. -/
@[stacks 0GDE "quasi-compactness of `f_{/T}` in the form of Bootstrap, Definition 03XZ: \
`f_{/T}` is representable by algebraic spaces and each of its base changes along a \
scheme-valued point of its target is a quasi-compact morphism of algebraic spaces. For a \
morphism representable by algebraic spaces this is the quasi-compactness of Stacks 0AJC by \
Stacks 0AM2, whose proof needs the agreement of the two notions of a quasi-compact space on \
an algebraic space, `QuasiCompactSpaceAgreesOnAlgebraicSpaces`, which this library does not \
carry; `isQuasiCompact_completionSheafMap_of_agreesOnAlgebraicSpaces` is the conclusion in \
the form of Stacks 0AJC granted that agreement"]
theorem isQuasiCompact_completionSheafMap
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hf : Space.IsQuasiCompact B S hS f) :
    ∃ hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.completionSheafMap B S hS f T).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (Space.quasiCompactPropertyULift.{u + 1} B S hS)
        (Space.completionSheafMap B S hS f T).hom hrep := by
  let C := BigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1}
  have hlarge : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (H.map f) := by
    apply (Space.isRepresentableByAlgebraicSpacesULift_whiskerRight_iff B S hS f).mpr
    intro U ξ
    exact isAlgebraicSpace_pullback B S hS ξ f (isAlgebraicSpace_yoneda B S hS U) hX' hX
  have hprop := hasPropertyULift_whiskerRight_of_isQuasiCompact B S hS f hf hlarge
  have hX'large : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (H.obj X') :=
    (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS X').mpr hX'
  have hXlarge : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (H.obj X) :=
    (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS X).mpr hX
  let eX' : H.obj X' ≅ (Space.sheafifiedULift B S hS X').obj := J.isoSheafify hX'large.isSheaf
  let eX : H.obj X ≅ (Space.sheafifiedULift B S hS X).obj := J.isoSheafify hXlarge.isSheaf
  have hpb := (Space.isPullback_completionSheafMap B S hS f T).map
    (sheafToPresheaf J (Type (u + 1)))
  have hcomm : (Space.sheafifiedULiftMap B S hS f).hom ≫ eX.inv = eX'.inv ≫ H.map f := by
    have hn' : H.map f ≫ eX.hom = eX'.hom ≫ (Space.sheafifiedULiftMap B S hS f).hom := by
      change (Functor.whiskerRight f uliftFunctor.{u + 1}) ≫
          J.toSheafify (X ⋙ uliftFunctor.{u + 1}) =
        J.toSheafify (X' ⋙ uliftFunctor.{u + 1}) ≫
          J.sheafifyMap (Functor.whiskerRight f uliftFunctor.{u + 1})
      exact J.toSheafify_naturality _
    calc
      (Space.sheafifiedULiftMap B S hS f).hom ≫ eX.inv =
          eX'.inv ≫ (eX'.hom ≫ (Space.sheafifiedULiftMap B S hS f).hom) ≫ eX.inv := by
            simp [Category.assoc]
      _ = eX'.inv ≫ (H.map f ≫ eX.hom) ≫ eX.inv := by rw [hn']
      _ = eX'.inv ≫ H.map f := by simp [Category.assoc]
  have hp : IsPullback
      ((Space.completionSheafInclusion B S hS X'
        (Space.pointsMap B S hS X' f ⁻¹' T)).hom ≫ eX'.inv)
      (Space.completionSheafMap B S hS f T).hom
      (H.map f)
      ((Space.completionSheafInclusion B S hS X T).hom ≫ eX.inv) :=
    IsPullback.of_iso hpb (Iso.refl _) eX'.symm (Iso.refl _) eX.symm
      (by simp) (by simp) hcomm (by simp)
  exact ⟨Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _ hp hlarge,
    Space.hasPropertyULift_of_isPullback B S hS hp hlarge hprop⟩

/-! ### The conclusion in the form of Stacks 0AJC -/

/-- **Stacks 0GDE** with quasi-compactness of `f_{/T}` read as
`AlgebraicGeometry.FormalSpace.IsQuasiCompact`, the form of Stacks 0AJC — every fibre product
of `f_{/T}` with an affine scheme over `S` in the site mapping to its target is a
quasi-compact formal algebraic space over `S` — granted the agreement of the two notions of a
quasi-compact space on an algebraic space as the hypothesis `hagree`. That fibre product is an
algebraic space because `f_{/T}` is representable by algebraic spaces, and it is a
quasi-compact one because the Bootstrap condition makes the projection to the affine scheme a
quasi-compact morphism and an affine scheme in the site is a quasi-compact algebraic space; so
`hagree` turns it into a quasi-compact formal algebraic space. -/
theorem isQuasiCompact_completionSheafMap_of_agreesOnAlgebraicSpaces
    (hagree : QuasiCompactSpaceAgreesOnAlgebraicSpaces B S hS)
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hf : Space.IsQuasiCompact B S hS f) :
    IsQuasiCompact B S hS (Space.completionSheafMap B S hS f T) := by
  obtain ⟨hrep, hprop⟩ := isQuasiCompact_completionSheafMap B S hS hX' hX f T hf
  intro T₀ hT₀ g W p q sq
  have hsq : IsPullback p.hom q.hom g.hom (Space.completionSheafMap B S hS f T).hom :=
    sq.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  refine (hagree W (Space.isAlgebraicSpaceULift_of_iso B S hS hsq.isoPullback.symm
    (hrep T₀ g.hom))).mpr ?_
  have hT₀qc : Space.IsQuasiCompactSpaceULift.{u + 1} B S hS
      ((uliftYoneda.{u + 1}).obj T₀) :=
    (Space.isQuasiCompactSpaceULift_comp_uliftFunctor_iff B S hS (yoneda.obj T₀)).mpr
      (Space.isQuasiCompactSpace_yoneda_obj B S hS
        (@Scheme.compactSpace_of_isAffine ((BigFppfOver.toScheme B S hS).obj T₀) hT₀))
  refine Space.isQuasiCompactSpaceULift_of_iso B S hS hsq.isoPullback.symm ?_
  refine Space.isQuasiCompactSpaceULift_of_iso B S hS
    (IsPullback.of_id_snd (f := pullback.fst g.hom
      (Space.completionSheafMap B S hS f T).hom)).isoPullback.symm ?_
  exact hprop T₀ g.hom _ (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS T₀)
    hT₀qc (𝟙 _)

end AlgebraicGeometry.FormalSpace

end
