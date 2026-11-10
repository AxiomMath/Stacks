module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Completion

/-!
# Closed immersions for a morphism of completions

Let `S` be a scheme contained in a big fppf site `B`, let `f : X' ⟶ X` be a morphism of
algebraic spaces over `S` and let `T` be a set of points of `X`. **Stacks 0GDC** says that if
`f` is a closed immersion then so is the induced morphism of completions
`f_{/T} : X'_{/|f|⁻¹ T} ⟶ X_{/T}`.

## Main results

* `AlgebraicGeometry.FormalSpace.isClosedImmersion_completionSheafMap`: **Stacks 0GDC**.

## Implementation notes

A closed immersion of algebraic spaces over `S`, `AlgebraicGeometry.Space.IsClosedImmersion`
of Tag 02YU, is the relative closed-immersion property along `CategoryTheory.yoneda`, while a
closed immersion of formal algebraic spaces,
`AlgebraicGeometry.FormalSpace.IsClosedImmersion` of Tag 0ANP, is the relative
closed-immersion property along `CategoryTheory.uliftYoneda` together with representability
by algebraic spaces. So the whole proof is carried by one property: being represented by a
closed immersion of the site, tested against the universe-lifted scheme-valued points.

That property is stable under base change, which is the content of Stacks 02YW here: closed
immersions of schemes are stable under base change and the structure functor of the big fppf
site of `S` preserves fibre products, so the same holds for the relative property along a
Yoneda embedding. And the property holds for the universe lift of `f`, because a relative
property along `CategoryTheory.yoneda` composed with the lifting functor is the relative
property along `CategoryTheory.uliftYoneda`, the lifting functor being fully faithful and
preserving fibre products — this is `relative_map` below, the direction of the comparison
that is needed here.

The completion square of Stacks 0APV,
`AlgebraicGeometry.Space.isPullback_completionSheafMap`, then exhibits `f_{/T}` as a base
change of that universe lift, so one application of stability under base change transports
the property to `f_{/T}` itself and a second one transports it to each of its base changes
along a scheme-valued point of `X_{/T}`, which is what the Tag 0ANP condition asks for. The
identification of the ambient sheaves of the completion square with the universe lifts
themselves is the one already used for representability in
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpacesULift_completionMap`, which also
supplies the representability half of the conclusion.

Closedness of `T` is not used: it is what makes the two completions formal algebraic spaces,
which the condition of Stacks 0ANP does not refer to, so the statement is proved for an
arbitrary set of points, as are the results of
`StacksFrontier.AlgebraicGeometry.FormalSpace.Completion` and of
`StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionLocallyFiniteType`.

## References

* [Stacks Project, Tag 0GDC](https://stacks.math.columbia.edu/tag/0GDC)
* [Stacks Project, Tag 0ANP](https://stacks.math.columbia.edu/tag/0ANP)
* [Stacks Project, Tag 0APV](https://stacks.math.columbia.edu/tag/0APV)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 02YW](https://stacks.math.columbia.edu/tag/02YW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A relative morphism property along a functor `i` transfers to the image of the morphism
under a fully faithful functor `H` preserving fibre products, read relatively to `i ⋙ H`: the
base changes tested by the new condition are images of the ones tested by the old. -/
private theorem relative_map
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (i : C ⥤ D) (H : D ⥤ E) [H.Full] [H.Faithful]
    [PreservesLimitsOfShape WalkingCospan H]
    (P : MorphismProperty C) {X Y : D} (f : X ⟶ Y) (hf : P.relative i f) :
    P.relative (i ⋙ H) (H.map f) := by
  refine ⟨?_, ?_⟩
  · intro U g
    obtain ⟨g', rfl⟩ := H.map_surjective g
    obtain ⟨V, p, q, hp⟩ := hf.rep g'
    exact ⟨V, p, H.map q, hp.map H⟩
  intro U V g q p hp
  obtain ⟨g', rfl⟩ := H.map_surjective g
  obtain ⟨q', rfl⟩ := H.map_surjective q
  exact hf.property g' q' p (hp.of_map H (H.map_injective (by simpa using hp.w)))

/-- **Stacks 0GDC.** Let `f : X' ⟶ X` be a morphism of algebraic spaces over `S` and let `T`
be a set of points of `X`. If `f` is a closed immersion, then the induced morphism of
completions `X'_{/|f|⁻¹ T} ⟶ X_{/T}` is a closed immersion of formal algebraic spaces: it is
representable by algebraic spaces and each of its base changes along a scheme-valued point of
its target is a closed immersion. -/
@[stacks 0GDC]
theorem isClosedImmersion_completionSheafMap
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hf : Space.IsClosedImmersion B S hS f) :
    IsClosedImmersion B S hS (Space.completionSheafMap B S hS f T) := by
  let C := BigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1}
  let R := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let Q := R.relative (uliftYoneda.{u + 1})
  have hQ : Q (H.map f) := relative_map yoneda H R f hf
  have hlarge {Y} (hY : IsAlgebraicSpace B S hS Y) :
      Space.IsAlgebraicSpaceULift.{u + 1} B S hS (H.obj Y) :=
    (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS Y).mpr hY
  let eX' : H.obj X' ≅ (Space.sheafifiedULift B S hS X').obj := J.isoSheafify (hlarge hX').isSheaf
  let eX : H.obj X ≅ (Space.sheafifiedULift B S hS X).obj := J.isoSheafify (hlarge hX).isSheaf
  have hcomm : (Space.sheafifiedULiftMap B S hS f).hom ≫ eX.inv = eX'.inv ≫ H.map f := by
    have hn' : H.map f ≫ eX.hom = eX'.hom ≫ (Space.sheafifiedULiftMap B S hS f).hom := by
      change (Functor.whiskerRight f uliftFunctor.{u + 1}) ≫
          J.toSheafify (X ⋙ uliftFunctor.{u + 1}) =
        J.toSheafify (X' ⋙ uliftFunctor.{u + 1}) ≫
          J.sheafifyMap (Functor.whiskerRight f uliftFunctor.{u + 1})
      exact J.toSheafify_naturality _
    rw [Iso.comp_inv_eq, Category.assoc, hn', Iso.inv_hom_id_assoc]
  have hp : IsPullback
      ((Space.completionSheafInclusion B S hS X'
        (Space.pointsMap B S hS X' f ⁻¹' T)).hom ≫ eX'.inv)
      (Space.completionSheafMap B S hS f T).hom
      (H.map f)
      ((Space.completionSheafInclusion B S hS X T).hom ≫ eX.inv) :=
    IsPullback.of_iso ((Space.isPullback_completionSheafMap B S hS f T).map
        (sheafToPresheaf J (Type (u + 1)))) (Iso.refl _) eX'.symm (Iso.refl _) eX.symm
      (by simp) (by simp) hcomm (by simp)
  exact ⟨Space.isRepresentableByAlgebraicSpacesULift_completionMap B S hS hX' hX f T,
    fun U ξ => (MorphismProperty.relative_isStableUnderBaseChange R).of_isPullback
      (IsPullback.of_hasPullback ξ (Space.completionSheafMap B S hS f T).hom).flip
      ((MorphismProperty.relative_isStableUnderBaseChange R).of_isPullback hp hQ)⟩

end AlgebraicGeometry.FormalSpace

end
