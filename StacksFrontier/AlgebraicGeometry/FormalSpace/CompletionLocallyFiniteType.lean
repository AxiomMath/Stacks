module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Completion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties

/-!
# Local finite type for a morphism of completions

Let `S` be a scheme contained in a big fppf site `B`, let `f : X' ⟶ X` be a morphism of
algebraic spaces over `S` and let `T` be a set of points of `X`. **Stacks 0AQ9** says that if
`f` is locally of finite type then so is the induced morphism of completions
`f_{/T} : X'_{/|f|⁻¹ T} ⟶ X_{/T}`.

## Main results

* `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_completionSheafMap`: **Stacks 0AQ9**.

## Implementation notes

The completion square of Stacks 0APV,
`AlgebraicGeometry.Space.isPullback_completionSheafMap`, exhibits `f_{/T}` as a base change of
the universe lift of `f`, so the statement is Stacks 0AQ5 — closure of local finite type under
base change, `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType.of_isPullback` — once the
universe lift of `f` is known to be locally of finite type as a morphism of fppf sheaves. The
identification of the ambient sheaves of that square with the universe lifts themselves is the
one already used for representability in
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpacesULift_completionMap`: `X` and `X'`
being algebraic spaces, their universe lifts are already sheaves.

Local finite type of the universe lift of `f` in the bootstrap sense of Stacks 03XZ is the
condition on the base changes of that lift along the universe-lifted scheme-valued points of
its target. Such a point is itself a universe lift, the lifting functor being fully faithful,
and the lifting functor preserves fibre products, so the base change is the universe lift of a
base change of `f` in the value universe of the site; there it is locally of finite type by
Stacks 03XH, and the two conditions agree on a universe lift.

Closedness of `T` is not used: it is what makes the two completions formal algebraic spaces,
which the condition of Stacks 0AM4 does not refer to, so the statement is proved for an
arbitrary set of points, as are the results of
`StacksFrontier.AlgebraicGeometry.FormalSpace.Completion`.

## References

* [Stacks Project, Tag 0AQ9](https://stacks.math.columbia.edu/tag/0AQ9)
* [Stacks Project, Tag 0APV](https://stacks.math.columbia.edu/tag/0APV)
* [Stacks Project, Tag 0AQ5](https://stacks.math.columbia.edu/tag/0AQ5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The universe lift of a morphism of algebraic spaces over `S` which is locally of finite
type is locally of finite type in the bootstrap sense of Stacks 03XZ: a base change of the
lift along a universe-lifted scheme-valued point of its target is the lift of a base change
of the morphism itself, which is locally of finite type by Stacks 03XH. -/
private theorem hasPropertyULift_whiskerRight_of_isLocallyOfFiniteType
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (hf : Space.IsLocallyOfFiniteType B S hS f)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (Functor.whiskerRight f uliftFunctor.{u + 1})) :
    Space.HasPropertyULift.{u + 1} B S hS
      (Space.locallyOfFiniteTypePropertyULift.{u + 1} B S hS)
      (Functor.whiskerRight f uliftFunctor.{u + 1}) hrep := by
  let C := BigFppfOver B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1}
  intro U ξ
  show Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS
    (pullback.fst ξ (Functor.whiskerRight f uliftFunctor.{u + 1}))
  obtain ⟨ξ₀, hξ₀⟩ := H.map_surjective (ξ : H.obj (yoneda.obj U) ⟶ H.obj X)
  -- The base change of `f` along `ξ₀`, in the value universe of the site.
  let A : AlgebraicSpaces B S hS := ⟨X', hX'⟩
  let Z : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Uₐ : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let fA : A ⟶ Z := ObjectProperty.homMk f
  let ξA : Uₐ ⟶ Z := ObjectProperty.homMk ξ₀
  let q : AlgebraicSpaces.fiberProduct B S hS ξA fA ⟶ Uₐ :=
    ObjectProperty.homMk (pullback.fst ξA.hom fA.hom)
  have hq : Space.IsLocallyOfFiniteType B S hS q.hom :=
    (Space.isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS ξA fA).flip hf
  have hqlift : Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS
      (Functor.whiskerRight (pullback.fst ξ₀ f) uliftFunctor.{u + 1}) :=
    (Space.isLocallyOfFiniteTypeULift_whiskerRight_iff B S hS (pullback.fst ξ₀ f)).mpr hq
  -- The lifted square is cartesian, so its vertex is the lift of the small fibre product.
  have hsq : IsPullback (H.map (pullback.fst ξ₀ f)) (H.map (pullback.snd ξ₀ f)) ξ
      (Functor.whiskerRight f uliftFunctor.{u + 1}) := by
    rw [← hξ₀]
    exact (IsPullback.of_hasPullback ξ₀ f).map H
  have h := Space.holdsOnEveryEtaleChartULift_precomp.{u + 1} B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u}) hsq.isoPullback.inv
    (Functor.whiskerRight (pullback.fst ξ₀ f) uliftFunctor.{u + 1}) hqlift
  have heq := (Iso.inv_comp_eq hsq.isoPullback).mpr hsq.isoPullback_hom_fst.symm
  exact heq ▸ h

/-- **Stacks 0AQ9.** Let `f : X' ⟶ X` be a morphism of algebraic spaces over `S` and let `T`
be a set of points of `X`. If `f` is locally of finite type, then the induced morphism of
completions `X'_{/|f|⁻¹ T} ⟶ X_{/T}` is locally of finite type. -/
@[stacks 0AQ9]
theorem isLocallyOfFiniteType_completionSheafMap
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hf : Space.IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFiniteType B S hS (Space.completionSheafMap B S hS f T) := by
  let C := BigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1}
  have hlarge : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (H.map f) :=
    (Space.isRepresentableByAlgebraicSpacesULift_whiskerRight_iff B S hS f).mpr fun U ξ =>
      isAlgebraicSpace_pullback B S hS ξ f (isAlgebraicSpace_yoneda B S hS U) hX' hX
  let eX' : H.obj X' ≅ (Space.sheafifiedULift B S hS X').obj :=
    J.isoSheafify ((Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS X').mpr hX').isSheaf
  let eX : H.obj X ≅ (Space.sheafifiedULift B S hS X).obj :=
    J.isoSheafify ((Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS X).mpr hX).isSheaf
  have hn' : H.map f ≫ eX.hom = eX'.hom ≫ (Space.sheafifiedULiftMap B S hS f).hom := by
    show (Functor.whiskerRight f uliftFunctor.{u + 1}) ≫
        J.toSheafify (X ⋙ uliftFunctor.{u + 1}) =
      J.toSheafify (X' ⋙ uliftFunctor.{u + 1}) ≫
        J.sheafifyMap (Functor.whiskerRight f uliftFunctor.{u + 1})
    exact J.toSheafify_naturality _
  have hcomm : (Space.sheafifiedULiftMap B S hS f).hom ≫ eX.inv = eX'.inv ≫ H.map f := by
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
  exact ⟨Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _ hp hlarge,
    Space.hasPropertyULift_of_isPullback B S hS hp hlarge
      (hasPropertyULift_whiskerRight_of_isLocallyOfFiniteType B S hS hX' hX f hf hlarge)⟩

end AlgebraicGeometry.FormalSpace

end
