module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionModificationAtlasBound
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionLift
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothEtaleDescent

/-!
# Smoothness of a morphism out of a completion descends along étale surjections

Let `S` be a scheme contained in a big fppf site `B`, let `i : U ⟶ V` be a morphism of the site,
`Z` a set of points of `V` and `g : V_{/Z} ⟶ W` representable by algebraic spaces. Given an étale
surjective `h : U' ⟶ U`, an étale `ψ : W' ⟶ W` and a smooth `G' : U'_{/Z'} ⟶ W'` (`Z'` the inverse
image of `Z` in `U'`) with `G' ≫ ψ` the restriction of `g` to `U'`, the restriction of `g` to the
completion of `U` is smooth: the completion of `h` is a base change of `h` (Stacks 0APV), hence
surjective and étale after every represented base change, and smoothness descends along it.

## Main results

* `AlgebraicGeometry.FormalSpace.relative_completionSheafMap_yoneda_map`: the completion of a
  morphism of the site has every base-change stable property of the morphism, after every
  represented base change.
* `AlgebraicGeometry.FormalSpace.hasPropertyULift_isSmoothULift_completionSheafMap_of_etale_cover`:
  the descent statement above.

## References

* [Stacks Project, Tag 0APV](https://stacks.math.columbia.edu/tag/0APV)
* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The completion of a morphism of the site is a base change of it.** For `h : U' ⟶ U` and
a base-change stable property `P` of `h`, the morphism of completions `U'_{/h⁻¹T} ⟶ U_{/T}` has
`P` after every represented base change (Stacks 0APV). -/
theorem relative_completionSheafMap_yoneda_map (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {U' U : BigFppfOver B S hS} (h : U' ⟶ U)
    (hP : P ((BigFppfOver.toScheme B S hS).map h)) (T : Set (Space.points B S hS (yoneda.obj U))) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).relative
      (uliftYoneda.{u + 1}) (Space.completionSheafMap B S hS (yoneda.map h) T).hom := by
  let C := BigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1}
  let f := yoneda.map h
  have hX'large : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (H.obj (yoneda.obj U')) :=
    (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS _).mpr
      (isAlgebraicSpace_yoneda B S hS U')
  have hXlarge : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (H.obj (yoneda.obj U)) :=
    (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS _).mpr
      (isAlgebraicSpace_yoneda B S hS U)
  let eX' : H.obj (yoneda.obj U') ≅ (Space.sheafifiedULift B S hS (yoneda.obj U')).obj :=
    J.isoSheafify hX'large.isSheaf
  let eX : H.obj (yoneda.obj U) ≅ (Space.sheafifiedULift B S hS (yoneda.obj U)).obj :=
    J.isoSheafify hXlarge.isSheaf
  have hcomm : (Space.sheafifiedULiftMap B S hS f).hom ≫ eX.inv = eX'.inv ≫ H.map f := by
    have hn' : H.map f ≫ eX.hom = eX'.hom ≫ (Space.sheafifiedULiftMap B S hS f).hom := by
      show (Functor.whiskerRight f uliftFunctor.{u + 1}) ≫
          J.toSheafify (yoneda.obj U ⋙ uliftFunctor.{u + 1}) =
        J.toSheafify (yoneda.obj U' ⋙ uliftFunctor.{u + 1}) ≫
          J.sheafifyMap (Functor.whiskerRight f uliftFunctor.{u + 1})
      exact J.toSheafify_naturality _
    rw [Iso.comp_inv_eq, Category.assoc, hn', Iso.inv_hom_id_assoc]
  have hp : IsPullback
      ((Space.completionSheafInclusion B S hS (yoneda.obj U')
        (Space.pointsMap B S hS (yoneda.obj U') f ⁻¹' T)).hom ≫ eX'.inv)
      (Space.completionSheafMap B S hS f T).hom
      (H.map f)
      ((Space.completionSheafInclusion B S hS (yoneda.obj U) T).hom ≫ eX.inv) :=
    IsPullback.of_iso ((Space.isPullback_completionSheafMap B S hS f T).map
      (sheafToPresheaf J (Type (u + 1)))) (Iso.refl _) eX'.symm (Iso.refl _) eX.symm
      (by simp) (by simp) hcomm (by simp)
  exact Space.relative_of_isPullback B S hS hp.flip
    (Space.relative_uliftYoneda_map B S hS P h hP)

/-- Smoothness of a morphism of fppf sheaves is unchanged by precomposing with an isomorphism. -/
theorem exists_hasPropertyULift_isSmoothULift_iso_comp {X X' W : FppfSheaf B S hS} (e : X' ≅ X)
    (G : X ⟶ W) (hG : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS G.hom)
    (hsm : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ a ↦ Space.IsSmoothULift.{u + 1} B S hS a.hom) G.hom hG) :
    ∃ hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (e.hom ≫ G).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ a ↦ Space.IsSmoothULift.{u + 1} B S hS a.hom) (e.hom ≫ G).hom hrep := by
  have : IsIso e.hom.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).mapIso e).hom)
  have sq : IsPullback e.hom.hom (e.hom ≫ G).hom G.hom (𝟙 W.obj) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; rfl⟩
  exact ⟨_, Space.hasPropertyULift_of_isPullback B S hS
    (P := Space.smoothPropertyULift.{u + 1} B S hS) sq hG hsm⟩

/-- **Smoothness of a restriction of `g : V_{/Z} ⟶ W` descends along an étale surjection.** Let
`i : U ⟶ V` and `h : U' ⟶ U` be morphisms of the site with `h` étale and surjective, `ψ : W' ⟶ W`
representable étale and `G'` a smooth morphism from the completion of `U'` to `W'` with
`G' ≫ ψ` the restriction of `g` to `U'`. Then the restriction of `g` to `U_{/i⁻¹Z}` is
smooth. -/
theorem exists_hasPropertyULift_isSmoothULift_completionSheafMap_of_etale_cover
    {U' U V : BigFppfOver B S hS} (i : U ⟶ V) (h : U' ⟶ U)
    (hE : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map h))
    (hSurj : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map h))
    (Z : Set (Space.points B S hS (yoneda.obj V))) {W W' : FppfSheaf B S hS}
    (g : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ W)
    (hg : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g.hom)
    (ψ : W' ⟶ W) (hψ : IsRepresentableEtale B S hS ψ)
    (G' : Space.completionSheaf B S hS (yoneda.obj U')
      (Space.pointsMap B S hS (yoneda.obj U') (yoneda.map h) ⁻¹'
        (Space.pointsMap B S hS (yoneda.obj U) (yoneda.map i) ⁻¹' Z)) ⟶ W')
    (hG' : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS G'.hom)
    (hsm : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ a ↦ Space.IsSmoothULift.{u + 1} B S hS a.hom) G'.hom hG')
    (w : G' ≫ ψ = Space.completionSheafMap B S hS (yoneda.map h)
      (Space.pointsMap B S hS (yoneda.obj U) (yoneda.map i) ⁻¹' Z) ≫
        Space.completionSheafMap B S hS (yoneda.map i) Z ≫ g) :
    ∃ hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.completionSheafMap B S hS (yoneda.map i) Z ≫ g).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ a ↦ Space.IsSmoothULift.{u + 1} B S hS a.hom)
        (Space.completionSheafMap B S hS (yoneda.map i) Z ≫ g).hom hrep := by
  have hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (Space.completionSheafMap B S hS (yoneda.map i) Z ≫ g).hom :=
    Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _
      (Space.isRepresentableByAlgebraicSpacesULift_completionMap B S hS
        (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _) (yoneda.map i) Z) hg
  exact ⟨hrep, Space.hasPropertyULift_isSmoothULift_of_etale_cover B S hS
    (Space.completionSheafMap B S hS (yoneda.map h)
      (Space.pointsMap B S hS (yoneda.obj U) (yoneda.map i) ⁻¹' Z)).hom
    (Space.completionSheafMap B S hS (yoneda.map i) Z ≫ g).hom G'.hom ψ.hom
    (congrArg (·.hom) w).symm
    (relative_completionSheafMap_yoneda_map B S hS _ h hE _)
    (relative_completionSheafMap_yoneda_map B S hS _ h hSurj _) hrep hG' hsm hψ.1 hψ.2⟩

end AlgebraicGeometry.FormalSpace
