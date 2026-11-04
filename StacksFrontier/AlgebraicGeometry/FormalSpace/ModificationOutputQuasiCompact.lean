module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedProperLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedProperTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineNoetherianEtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardAffineGeometry
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismUniquenessAlongClosedSubset
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae03KM
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlgebraicSpaceAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Dilatations
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionDiagonalRigSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianValuativeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveLocusOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# Finite-type modifications with proper completion: quasi-compactness and separation

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a locally Noetherian algebraic
space over `S`, let `T ⊆ |X|` be a closed subset with open complement `U`, and let
`f : X' ⟶ X` be a morphism of algebraic spaces which is locally of finite type and an
isomorphism over `U`. If the completion `f_{/T} : X'_{/T'} ⟶ X_{/T}` is proper, then `f` is
quasi-compact and quasi-separated, and a valuative square for `f` whose bottom edge lies over `U`,
or over `T`, has exactly one dotted arrow. If `f` is proper, a rig-étale morphism over `X_{/T}`
isomorphic to `f_{/T}` is a formal modification.

## Main results

* `AlgebraicGeometry.FormalSpace.isProper_pullback_snd_of_isProper_completionSheafMap`: if
  `f_{/T}` is proper, the base change of `f` along a scheme all of whose points lie over `T` is
  proper.
* `AlgebraicGeometry.FormalSpace.isQuasiCompact_of_isProper_completionSheafMap`: if `f_{/T}` is
  proper, `f` is quasi-compact.
* `AlgebraicGeometry.FormalSpace.isQuasiSeparated_of_isProper_completionSheafMap`: if `f_{/T}` is
  proper, `f` is quasi-separated.
* `AlgebraicGeometry.FormalSpace.unique_lift_of_range_subset_compl` and
  `AlgebraicGeometry.FormalSpace.unique_lift_of_range_subset`: a valuative square whose bottom
  edge avoids `T`, respectively lies over `T`, has exactly one dotted arrow.
* `AlgebraicGeometry.FormalSpace.isFormalModification_of_isProper_of_iso`: if `f` is proper, a
  rig-étale morphism over `X_{/T}` isomorphic to `f_{/T}` is a formal modification.

## References

* [Stacks Project, Tag 0ARU](https://stacks.math.columbia.edu/tag/0ARU)
* [Stacks Project, Tag 0ARV](https://stacks.math.columbia.edu/tag/0ARV)
* [Stacks Project, Tag 0ARW](https://stacks.math.columbia.edu/tag/0ARW)
* [Stacks Project, Tag 0ARX](https://stacks.math.columbia.edu/tag/0ARX)
* [Stacks Project, Tag 0GDM](https://stacks.math.columbia.edu/tag/0GDM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The base change of `f` along a point over `T` is a base change of `f_{/T}`.** Let
`f : X' ⟶ X` be a morphism of algebraic spaces and `T` a set of points of `X`. A morphism
`v : V ⟶ X` from a scheme of the site whose points all lie in `T` is a point `ξ` of the
completion `X_{/T}`, and the base change of `f_{/T}` along `ξ` is, up to isomorphism over `V`,
the universe lift of the base change `X' ×_X V ⟶ V` of `f`. -/
theorem exists_iso_pullback_completionSheafMap
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (V : BigFppfOver B S hS) (v : yoneda.obj V ⟶ X)
    (hv : Space.HasImageIn B S hS X T V (yonedaEquiv v)) :
    ∃ (ξ : (uliftYoneda.{u + 1}).obj V ⟶ (Space.completionSheaf B S hS X T).obj)
      (e : pullback ξ (Space.completionSheafMap B S hS f T).hom ≅
        pullback f v ⋙ uliftFunctor.{u + 1}),
      e.hom ≫ Functor.whiskerRight (pullback.snd f v) uliftFunctor.{u + 1} =
        pullback.fst ξ (Space.completionSheafMap B S hS f T).hom := by
  let C := BigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1}
  let x : (Space.completionSubfunctor B S hS X T).toFunctor.obj (Opposite.op V) :=
    ⟨ULift.up (yonedaEquiv v), hv⟩
  let ξ₀ : (uliftYoneda.{u + 1}).obj V ⟶ (Space.completionSubfunctor B S hS X T).toFunctor :=
    uliftYonedaEquiv.symm x
  let ξ : (uliftYoneda.{u + 1}).obj V ⟶ (Space.completionSheaf B S hS X T).obj :=
    ξ₀ ≫ J.toSheafify _
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
      show (Functor.whiskerRight f uliftFunctor.{u + 1}) ≫
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
  have hξ : ξ ≫ (Space.completionSheafInclusion B S hS X T).hom ≫ eX.inv = H.map v := by
    have h1 : ξ ≫ (Space.completionSheafInclusion B S hS X T).hom =
        ξ₀ ≫ (Space.completionSubfunctor B S hS X T).ι ≫ eX.hom := by
      show (ξ₀ ≫ J.toSheafify _) ≫ J.sheafifyMap (Space.completionSubfunctor B S hS X T).ι =
        ξ₀ ≫ (Space.completionSubfunctor B S hS X T).ι ≫ J.toSheafify _
      rw [Category.assoc, J.toSheafify_naturality]
    rw [← Category.assoc, h1, Category.assoc, Category.assoc, eX.hom_inv_id]
    show ξ₀ ≫ (Space.completionSubfunctor B S hS X T).ι = H.map v
    rw [show ξ₀ = uliftYonedaEquiv.symm x from rfl, uliftYonedaEquiv_symm_comp]
    apply uliftYonedaEquiv.symm_apply_eq.mpr
    show ULift.up (yonedaEquiv v) = _
    simp [uliftYonedaEquiv, yonedaEquiv, H]
    rfl
  have hbig := ((IsPullback.of_hasPullback ξ
    (Space.completionSheafMap B S hS f T).hom).flip.paste_horiz hp).flip
  rw [hξ] at hbig
  have hsmall := (IsPullback.of_hasPullback f v).flip.map H
  exact ⟨ξ, hbig.isoIsPullback _ _ hsmall, hbig.isoIsPullback_hom_fst _ _ hsmall⟩

/-- **Properness over the closed set, read off a proper completion.** Let `f : X' ⟶ X` be a
morphism of algebraic spaces whose completion `f_{/T} : X'_{/T'} ⟶ X_{/T}` along a set `T` of
points of `X` is proper. Then the base change of `f` along every morphism `v : V ⟶ X` from a
scheme of the site whose points all lie in `T` is a proper morphism of algebraic spaces. -/
theorem isProper_pullback_snd_of_isProper_completionSheafMap
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hg : IsProper B S hS (Space.completionSheafMap B S hS f T))
    (V : BigFppfOver B S hS) (v : yoneda.obj V ⟶ X)
    (hv : Space.HasImageIn B S hS X T V (yonedaEquiv v)) :
    Space.IsProper B S hS (pullback.snd f v) := by
  obtain ⟨hrep, hprop⟩ := hg
  obtain ⟨ξ, e, he⟩ := exists_iso_pullback_completionSheafMap hX' hX f T V v hv
  have hpbX : IsAlgebraicSpace B S hS (pullback f v) :=
    isAlgebraicSpace_pullback B S hS f v hX' (isAlgebraicSpace_yoneda B S hS V) hX
  have hPbs : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback f v ⋙ uliftFunctor.{u + 1}) :=
    (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS _).mpr hpbX
  have hfinal : Space.IsProperULift.{u + 1} B S hS
      (Functor.whiskerRight (pullback.snd f v) uliftFunctor.{u + 1}) := by
    have heq : Functor.whiskerRight (pullback.snd f v) uliftFunctor.{u + 1} =
        e.inv ≫ pullback.fst ξ (Space.completionSheafMap B S hS f T).hom :=
      (e.inv_hom_id_assoc _).symm.trans (congrArg (e.inv ≫ ·) he)
    exact (congrArg (Space.IsProperULift.{u + 1} B S hS) heq).mpr
      (Space.isProperULift_precomp.{u + 1} B S hS e.symm
        (pullback.fst ξ (Space.completionSheafMap B S hS f T).hom) hPbs (hrep V ξ)
        (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS V) (hprop V ξ))
  exact (Space.isProperULift_whiskerRight_iff.{u + 1} B S hS _).mp hfinal

end AlgebraicGeometry.FormalSpace

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-- The inverse image of a closed set `T` of points of an algebraic space `Y` under a morphism
`w : W ⟶ Y` from an affine scheme is covered by an affine scheme `V ⟶ W` all of whose points lie
over `T`. -/
theorem exists_affine_cover_preimage {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (points B S hS Y)) (hT : IsClosed T) (W : BigFppfOver B S hS)
    (w : yoneda.obj W ⟶ Y) (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)) :
    ∃ (V : BigFppfOver B S hS) (j : V ⟶ W),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      Set.range (pointsMap B S hS (yoneda.obj V) (yoneda.map j ≫ w)) ⊆ T ∧
      pointsMap B S hS (yoneda.obj W) w ⁻¹' T ⊆
        Set.range (pointsMap B S hS (yoneda.obj V) (yoneda.map j)) := by
  have hWsp := isAlgebraicSpace_yoneda B S hS W
  let TW := pointsMap B S hS (yoneda.obj W) w ⁻¹' T
  have hTW : IsClosed TW := hT.preimage (continuous_pointsMap B S hS w)
  let Z := reducedClosedSubspace B S hS (yoneda.obj W) hWsp TW hTW
  have hZ := isClosedSubspace_reducedClosedSubspace B S hS (yoneda.obj W) hWsp TW hTW
  have hZrange := range_pointsMap_ι_reducedClosedSubspace B S hS (yoneda.obj W) hWsp TW hTW
  have hWqc : IsQuasiCompactSpace B S hS (yoneda.obj W) :=
    isQuasiCompactSpace_yoneda_of_isAffine B S hS W hW
  have hZqc : IsQuasiCompactSpace B S hS Z.toFunctor :=
    isQuasiCompactSpace_of_isClosedImmersion B S hS hWqc Z.ι hZ.2
  obtain ⟨V, c, hV, hcs, -⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Z.toFunctor hZ.1).1 hZqc
  have hcsurj : Function.Surjective (pointsMap B S hS (yoneda.obj V) c) :=
    isSurjective_of_presheafSurjective B S hS c hcs
  let j : V ⟶ W := yoneda.preimage (c ≫ Z.ι)
  have hj : yoneda.map j = c ≫ Z.ι := yoneda.map_preimage _
  have hrange : Set.range (pointsMap B S hS (yoneda.obj V) (yoneda.map j)) = TW := by
    rw [hj, pointsMap_comp, Set.range_comp, hcsurj.range_eq, Set.image_univ, hZrange]
  refine ⟨V, j, hV, ?_, hrange.symm.subset⟩
  rintro _ ⟨v, rfl⟩
  rw [pointsMap_comp_apply]
  have : pointsMap B S hS (yoneda.obj V) (yoneda.map j) v ∈ TW := hrange ▸ ⟨v, rfl⟩
  exact this

/-- **Quasi-compactness from the part over an open and the part over its closed complement.**
Let `φ : Y' ⟶ Y` be a morphism of algebraic spaces and `T` a closed set of points of `Y`. Assume
given a quasi-compact `k : Y_U ⟶ Y` whose image contains every point outside `T`, along which the
base change of `φ` is quasi-compact, and assume that the base change of `φ` along every morphism
from an affine scheme with image in `T` has quasi-compact source. Then `φ` is quasi-compact. -/
theorem isQuasiCompact_of_openPart_of_closedPart {Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y) (φ : Y' ⟶ Y)
    (T : Set (points B S hS Y)) (hT : IsClosed T)
    {YU Y'U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hYU : IsAlgebraicSpace B S hS YU)
    (k : YU ⟶ Y) (hk : IsQuasiCompact B S hS k)
    (hkcov : ∀ y, y ∉ T → y ∈ Set.range (pointsMap B S hS YU k))
    (a : Y'U ⟶ Y') (b : Y'U ⟶ YU) (sq : IsPullback a b φ k) (hb : IsQuasiCompact B S hS b)
    (hclosed : ∀ (V : BigFppfOver B S hS) (v : yoneda.obj V ⟶ Y),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      Set.range (pointsMap B S hS (yoneda.obj V) v) ⊆ T →
      IsQuasiCompactSpace B S hS (pullback φ v)) :
    IsQuasiCompact B S hS φ := by
  refine isQuasiCompact_of_isQuasiCompactSpace_pullback_affine' B S hS φ hY' hY
    fun W g hW => ?_
  have hWsp := isAlgebraicSpace_yoneda B S hS W
  have hWqc : IsQuasiCompactSpace B S hS (yoneda.obj W) :=
    isQuasiCompactSpace_yoneda_of_isAffine B S hS W hW
  have hP : IsAlgebraicSpace B S hS (pullback φ g) :=
    isAlgebraicSpace_pullback B S hS φ g hY' hWsp hY
  have hY'U : IsAlgebraicSpace B S hS Y'U :=
    (isAlgebraicSpace_pullback B S hS φ k hY' hYU hY).of_iso sq.isoPullback.symm
  let Q := pullback g k
  have hQ : IsAlgebraicSpace B S hS Q := isAlgebraicSpace_pullback B S hS g k hWsp hYU hY
  have hQqc : IsQuasiCompactSpace B S hS Q := hk _ hWsp hWqc g
  let A₁ := pullback (pullback.fst φ g) a
  have hA₁ : IsAlgebraicSpace B S hS A₁ :=
    isAlgebraicSpace_pullback B S hS _ a hP hY'U hY'
  have hA₁sq : IsPullback (pullback.snd (pullback.fst φ g) a)
      (pullback.lift (pullback.fst _ a ≫ pullback.snd φ g) (pullback.snd _ a ≫ b) (by
        rw [Category.assoc, ← pullback.condition, ← Category.assoc, pullback.condition,
          Category.assoc, sq.w, Category.assoc]) : A₁ ⟶ Q) b (pullback.snd g k) := by
    refine IsPullback.of_bot ?_ (pullback.lift_snd _ _ _).symm
      (IsPullback.of_hasPullback g k).flip
    have h1 := (IsPullback.of_hasPullback (pullback.fst φ g) a).flip.paste_vert
      (IsPullback.of_hasPullback φ g)
    have h2 : IsPullback (pullback.snd (pullback.fst φ g) a)
        (pullback.fst (pullback.fst φ g) a ≫ pullback.snd φ g) (a ≫ φ) g := h1.flip.flip
    rw [sq.w] at h2
    convert h2.flip.flip using 1
    · exact pullback.lift_fst _ _ _
  have hA₁qc : IsQuasiCompactSpace B S hS A₁ :=
    isQuasiCompactSpace_of_iso B S hS hA₁sq.flip.isoPullback.symm
      (hb Q hQ hQqc (pullback.snd g k))
  obtain ⟨V, j, hV, hVT, hVcov⟩ := exists_affine_cover_preimage T hT W g hW
  let A₂ := pullback (pullback.snd φ g) (yoneda.map j)
  have hA₂qc : IsQuasiCompactSpace B S hS A₂ :=
    isQuasiCompactSpace_of_iso B S hS (pullbackLeftPullbackSndIso φ g (yoneda.map j)).symm
      (hclosed V (yoneda.map j ≫ g) hV hVT)
  have hA₂ : IsAlgebraicSpace B S hS A₂ :=
    isAlgebraicSpace_pullback B S hS _ _ hP (isAlgebraicSpace_yoneda B S hS V) hWsp
  refine (isQuasiCompactSpace_iff_compactSpace_points B S hS _ hP).2 ⟨?_⟩
  have hcov : (Set.univ : Set (points B S hS (pullback φ g))) =
      Set.range (pointsMap B S hS A₁ (pullback.fst _ a)) ∪
        Set.range (pointsMap B S hS A₂ (pullback.fst _ _)) := by
    refine (Set.eq_univ_of_forall fun p => ?_).symm
    by_cases hp : pointsMap B S hS _ (pullback.fst φ g ≫ φ) p ∈ T
    · right
      have hz : pointsMap B S hS _ (pullback.snd φ g) p ∈ pointsMap B S hS _ g ⁻¹' T := by
        rw [Set.mem_preimage, ← pointsMap_comp_apply, ← pullback.condition]
        exact hp
      obtain ⟨v, hv⟩ := hVcov hz
      obtain ⟨x, hx, -⟩ := exists_point_of_isPullback_presheaf B S hS
        (IsPullback.of_hasPullback (pullback.snd φ g) (yoneda.map j)) p v hv.symm
      exact ⟨x, hx⟩
    · left
      obtain ⟨yU, hyU⟩ := hkcov _ hp
      rw [pointsMap_comp_apply] at hyU
      obtain ⟨y', hy', -⟩ := exists_point_of_isPullback_presheaf B S hS sq _ yU hyU.symm
      obtain ⟨x, hx, -⟩ := exists_point_of_isPullback_presheaf B S hS
        (IsPullback.of_hasPullback (pullback.fst φ g) a) p y' hy'.symm
      exact ⟨x, hx⟩
  rw [hcov]
  have _ := compactSpace_points_of_isQuasiCompactSpace B S hS hA₁ hA₁qc
  have _ := compactSpace_points_of_isQuasiCompactSpace B S hS hA₂ hA₂qc
  exact (isCompact_range (continuous_pointsMap B S hS _)).union
    (isCompact_range (continuous_pointsMap B S hS _))

/-- A morphism from a quasi-compact algebraic space to an affine scheme is quasi-compact. -/
theorem isQuasiCompact_of_isQuasiCompactSpace_of_isAffine {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hFqc : IsQuasiCompactSpace B S hS F)
    (W : BigFppfOver B S hS) (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (k : F ⟶ yoneda.obj W) : IsQuasiCompact B S hS k := by
  obtain ⟨U, a, hU, has, -⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS F hF).1 hFqc
  have hk : IsQuasiCompact B S hS (a ≫ k) := by
    rw [← yoneda.map_preimage (a ≫ k)]
    exact isQuasiCompact_yoneda_of_isAffine B S hS _ hU hW
  exact isQuasiCompact_of_comp_surjective B S hS (isAlgebraicSpace_yoneda B S hS U) hF
    (isAlgebraicSpace_yoneda B S hS W) a (a ≫ k) k rfl
    (isSurjective_of_presheafSurjective B S hS a has) hk

/-- The inclusion of an open subspace of a locally Noetherian algebraic space is
quasi-compact. -/
theorem isQuasiCompact_ι_openSubspaceOfPoints_of_hasEtaleLocalProperty
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X
      (fun T : Scheme.{u} ↦ _root_.AlgebraicGeometry.IsLocallyNoetherian T))
    (W : Set (points B S hS X)) (hW : IsOpen W) :
    IsQuasiCompact B S hS (openSubspaceOfPoints B S hS X W).ι := by
  obtain ⟨I, A, hA, a, φ, hAN, -, hφe, hcov⟩ :=
    exists_spec_isLocallyNoetherian_etale_covering_family B S hS hX hN
  have hO := isOpenSubspace_openSubspaceOfPoints B S hS hX W hW
  refine isQuasiCompact_of_isEtaleCovering B S hS hO.1 hX _
    (Gi := fun i ↦ yoneda.obj (siteObject B S hS (hA i) (a i))) (g := φ)
    ⟨hX, fun i ↦ isAlgebraicSpace_yoneda B S hS _, hφe,
      Set.eq_univ_of_forall fun y ↦ by
        obtain ⟨i, hi⟩ := hcov y
        exact Set.mem_iUnion.2 ⟨i, hi⟩⟩ fun i ↦ ?_
  let V := siteObject B S hS (hA i) (a i)
  have hVsp := isAlgebraicSpace_yoneda B S hS V
  have hP : IsAlgebraicSpace B S hS (pullback (φ i) (openSubspaceOfPoints B S hS X W).ι) :=
    isAlgebraicSpace_pullback B S hS _ _ hVsp hO.1 hX
  have himm : IsImmersion B S hS (pullback.fst (φ i) (openSubspaceOfPoints B S hS X W).ι) :=
    isImmersion_of_isOpenImmersion B S hS
      ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
        (IsPullback.of_hasPullback (φ i) (openSubspaceOfPoints B S hS X W).ι).flip hO.2)
  have hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := by
    show IsAffine (Spec (A i)); infer_instance
  have : IsNoetherianRing (A i) := hAN i
  have hSN : TopologicalSpace.NoetherianSpace ((BigFppfOver.toScheme B S hS).obj V) := by
    show TopologicalSpace.NoetherianSpace (Spec (A i)); infer_instance
  have hVN : TopologicalSpace.NoetherianSpace (points B S hS (yoneda.obj V)) :=
    (schemePointsHomeomorph B S hS V).isEmbedding.isInducing.noetherianSpace
  have hPN : TopologicalSpace.NoetherianSpace (points B S hS
      (pullback (φ i) (openSubspaceOfPoints B S hS X W).ι)) :=
    (isEmbedding_pointsMap_of_isImmersion B S hS hVsp _ himm).isInducing.noetherianSpace
  have hPqc : IsQuasiCompactSpace B S hS
      (pullback (φ i) (openSubspaceOfPoints B S hS X W).ι) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS _ hP).2
        (TopologicalSpace.NoetherianSpace.compactSpace _)
  exact isQuasiCompact_of_isQuasiCompactSpace_of_isAffine hP hPqc V hVaff _

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

/-- A morphism from a scheme of the site whose points all lie in `T` is a point with image in
`T`. -/
private theorem hasImageIn_of_range_subset {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : Set (Space.points B S hS X)} {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ X)
    (h : Set.range (Space.pointsMap B S hS (yoneda.obj V) v) ⊆ T) :
    Space.HasImageIn B S hS X T V (yonedaEquiv v) := by
  rwa [Space.hasImageIn_iff_range_subset, Equiv.symm_apply_apply]

/-- With a proper completion `f_{/T}`, the base change of `f` along a morphism from an affine
scheme with image in `T` has quasi-compact source. -/
theorem isQuasiCompactSpace_pullback_of_isProper_completionSheafMap
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hg : IsProper B S hS (Space.completionSheafMap B S hS f T))
    (V : BigFppfOver B S hS) (v : yoneda.obj V ⟶ X)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hvT : Set.range (Space.pointsMap B S hS (yoneda.obj V) v) ⊆ T) :
    Space.IsQuasiCompactSpace B S hS (pullback f v) := by
  have hprop := isProper_pullback_snd_of_isProper_completionSheafMap hX' hX f T hg V v
    (hasImageIn_of_range_subset v hvT)
  exact Space.isQuasiCompactSpace_source_of_isQuasiCompact B S hS
    (isAlgebraicSpace_yoneda B S hS V) (Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS V hV)
    hprop.2.1.2

/-- A morphism `f : X' ⟶ X` of algebraic spaces with `X` locally Noetherian which is an
isomorphism over the complement `U` of a closed set `T` and whose completion `f_{/T}` is proper
is quasi-compact. -/
theorem isQuasiCompact_of_isProper_completionSheafMap
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hN : Space.HasEtaleLocalProperty B S hS X
      (fun T : Scheme.{u} ↦ _root_.AlgebraicGeometry.IsLocallyNoetherian T))
    (f : X' ⟶ X) (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hfU : IsIso (pullback.snd f (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    (hg : IsProper B S hS (Space.completionSheafMap B S hS f T)) :
    Space.IsQuasiCompact B S hS f := by
  have hO := Space.isOpenSubspace_openSubspaceOfPoints B S hS hX Tᶜ hT.isOpen_compl
  refine Space.isQuasiCompact_of_openPart_of_closedPart hX' hX f T hT hO.1
    (Space.openSubspaceOfPoints B S hS X Tᶜ).ι
    (Space.isQuasiCompact_ι_openSubspaceOfPoints_of_hasEtaleLocalProperty hX hN Tᶜ
      hT.isOpen_compl) (fun y hy ↦ ?_) _ _ (IsPullback.of_hasPullback _ _)
    (Space.isQuasiCompact_of_isIso B S hS _) fun V v hV hvT ↦
      isQuasiCompactSpace_pullback_of_isProper_completionSheafMap hX' hX f T hg V v hV hvT
  rwa [Space.range_pointsMap_ι_openSubspaceOfPoints]

/-- An algebraic space locally of finite type over a locally Noetherian algebraic space is
locally Noetherian, in the atlas form `AlgebraicGeometry.Space.HasEtaleLocalProperty`. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType
    {Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    (hX : IsAlgebraicSpace B S hS X) (h : Z ⟶ X) (hh : Space.IsLocallyOfFiniteType B S hS h)
    (hN : Space.HasEtaleLocalProperty B S hS X
      (fun T : Scheme.{u} ↦ _root_.AlgebraicGeometry.IsLocallyNoetherian T)) :
    Space.HasEtaleLocalProperty B S hS Z
      (fun T : Scheme.{u} ↦ _root_.AlgebraicGeometry.IsLocallyNoetherian T) := by
  have hXN : Space.IsLocallyNoetherian B S hS X := fun W q hq ↦
    (Space.exists_atlas_iff_forall_etale B S hS X _ hX).mp hN W q
      ((Space.isEtale_iff_presheaf_of_yoneda B S hS q).1 hq)
  have hZN := isLocallyNoetherian_of_isLocallyOfFiniteType hZ hX h hh hXN
  exact (Space.exists_atlas_iff_forall_etale B S hS Z _ hZ).mpr fun W q hq ↦
    hZN W q ((Space.isEtale_iff_presheaf_of_yoneda B S hS q).2 hq)

/-- **Quasi-separatedness from separatedness over the closed set.** A morphism `f : X' ⟶ X` of
algebraic spaces, locally of finite type, with `X` locally Noetherian, which is an isomorphism
over the complement `U` of a closed set `T` and whose base change along every morphism from an
affine scheme with image in `T` is separated, is quasi-separated. -/
theorem isQuasiSeparated_of_isSeparated_pullback_snd
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hN : Space.HasEtaleLocalProperty B S hS X
      (fun T : Scheme.{u} ↦ _root_.AlgebraicGeometry.IsLocallyNoetherian T))
    (f : X' ⟶ X) (hf : Space.IsLocallyOfFiniteType B S hS f)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hfU : IsIso (pullback.snd f (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    (hsepT : ∀ (V : BigFppfOver B S hS) (w : yoneda.obj V ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      Set.range (Space.pointsMap B S hS (yoneda.obj V) w) ⊆ T →
      Space.IsSeparated B S hS (pullback.snd f w)) :
    Space.IsQuasiSeparated B S hS f := by
  let P := pullback f f
  have hP : IsAlgebraicSpace B S hS P := isAlgebraicSpace_pullback B S hS f f hX' hX' hX
  let π : P ⟶ X := pullback.fst f f ≫ f
  have hπ : pullback.snd f f ≫ f = π := pullback.condition.symm
  let TP := Space.pointsMap B S hS P π ⁻¹' T
  have hTP : IsClosed TP := hT.preimage (Space.continuous_pointsMap B S hS π)
  have hX'N := hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType hX' hX f hf hN
  have hPN := hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType hP hX'
    (pullback.fst f f)
    (Space.IsLocallyOfFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback f f) hX' hX hf)
    hX'N
  let O := Space.openSubspaceOfPoints B S hS P TPᶜ
  have hO := Space.isOpenSubspace_openSubspaceOfPoints B S hS hP TPᶜ hTP.isOpen_compl
  have hagree : O.ι ≫ pullback.fst f f = O.ι ≫ pullback.snd f f :=
    Space.comp_eq_openComplement_of_comp_eq B S hS hfU rfl hπ
  have hfac : O.ι = (O.ι ≫ pullback.fst f f) ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · simp
    · simp [hagree]
  have hb : IsIso (pullback.snd (pullback.diagonal f) O.ι) := by
    have : IsSplitEpi (pullback.snd (pullback.diagonal f) O.ι) :=
      ⟨⟨pullback.lift (O.ι ≫ pullback.fst f f) (𝟙 _) (by rw [Category.id_comp, ← hfac]),
        pullback.lift_snd _ _ _⟩⟩
    exact isIso_of_mono_of_isSplitEpi _
  refine Space.isQuasiCompact_of_openPart_of_closedPart hX' hP (pullback.diagonal f) TP hTP
    hO.1 O.ι (Space.isQuasiCompact_ι_openSubspaceOfPoints_of_hasEtaleLocalProperty hP hPN TPᶜ
      hTP.isOpen_compl) (fun y hy ↦ ?_) _ _ (IsPullback.of_hasPullback _ _)
    (Space.isQuasiCompact_of_isIso B S hS _) fun V v hV hvT ↦ ?_
  · rwa [Space.range_pointsMap_ι_openSubspaceOfPoints]
  let w : yoneda.obj V ⟶ X := v ≫ π
  have hwT : Set.range (Space.pointsMap B S hS (yoneda.obj V) w) ⊆ T := by
    rintro _ ⟨x, rfl⟩
    rw [Space.pointsMap_comp_apply]
    exact hvT ⟨x, rfl⟩
  have hsep : Space.IsSeparated B S hS (pullback.snd f w) := hsepT V w hV hwT
  let σ₁ : yoneda.obj V ⟶ pullback f w :=
    pullback.lift (v ≫ pullback.fst f f) (𝟙 _) (by simp [w, π])
  let σ₂ : yoneda.obj V ⟶ pullback f w :=
    pullback.lift (v ≫ pullback.snd f f) (𝟙 _) (by simp [w, ← hπ])
  let σ : yoneda.obj V ⟶ pullback (pullback.snd f w) (pullback.snd f w) :=
    pullback.lift σ₁ σ₂ (by simp only [σ₁, σ₂, pullback.lift_snd])
  have hsq0 := isPullback_diagonal_pullback_snd f w
  have hσ : σ ≫ pullback.map (pullback.snd f w) (pullback.snd f w) f f
      (pullback.fst f w) (pullback.fst f w) w pullback.condition.symm
      pullback.condition.symm = v := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      simp only [σ, σ₁, σ₂, pullback.lift_fst_assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd]
      simp only [σ, σ₁, σ₂, pullback.lift_snd_assoc, pullback.lift_fst]
  have hbig := (IsPullback.of_hasPullback (pullback.diagonal (pullback.snd f w)) σ).paste_horiz
    hsq0
  rw [hσ] at hbig
  have hci : Space.IsClosedImmersion B S hS
      (pullback.snd (pullback.diagonal (pullback.snd f w)) σ) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback (pullback.diagonal (pullback.snd f w)) σ) hsep
  exact Space.isQuasiCompactSpace_of_iso B S hS hbig.isoPullback
    (Space.isQuasiCompactSpace_of_isClosedImmersion B S hS
      (Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS V hV) _ hci)

/-- A morphism `f : X' ⟶ X` of algebraic spaces, locally of finite type, with `X` locally
Noetherian, which is an isomorphism over the complement `U` of a closed set `T` and whose
completion `f_{/T}` is proper, is quasi-separated. -/
theorem isQuasiSeparated_of_isProper_completionSheafMap
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hN : Space.HasEtaleLocalProperty B S hS X
      (fun T : Scheme.{u} ↦ _root_.AlgebraicGeometry.IsLocallyNoetherian T))
    (f : X' ⟶ X) (hf : Space.IsLocallyOfFiniteType B S hS f)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hfU : IsIso (pullback.snd f (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    (hg : IsProper B S hS (Space.completionSheafMap B S hS f T)) :
    Space.IsQuasiSeparated B S hS f :=
  isQuasiSeparated_of_isSeparated_pullback_snd hX' hX hN f hf T hT hfU fun V w _ hwT ↦
    (isProper_pullback_snd_of_isProper_completionSheafMap hX' hX f T hg V w
      (hasImageIn_of_range_subset w hwT)).1

/-! ### Formal modifications and isomorphisms of the source -/

/-- Properness of a morphism of formal algebraic spaces is unchanged by precomposing with an
isomorphism. -/
theorem isProper_isIso_comp {W' W Y : FppfSheaf B S hS} (i : W' ⟶ W) [IsIso i] (h : W ⟶ Y)
    (hh : IsProper B S hS h) : IsProper B S hS (i ≫ h) :=
  IsProper.of_isPullback B S hS (IsPullback.of_vert_isIso (fst := i ≫ h) (snd := i)
    (f := 𝟙 Y) (g := h) ⟨by simp⟩) hh

/-- Rig-surjectivity of the relative diagonal is unchanged by precomposing with an
isomorphism. -/
theorem isRigSurjective_diagonal_isIso_comp {W' W Y : FppfSheaf B S hS} (i : W' ⟶ W) [IsIso i]
    (h : W ⟶ Y) (hh : IsRigSurjective B S hS (pullback.diagonal h)) :
    IsRigSurjective B S hS (pullback.diagonal (i ≫ h)) := by
  let m := pullback.map (i ≫ h) (i ≫ h) h h i i (𝟙 Y) (by simp) (by simp)
  have hm : pullback.diagonal (i ≫ h) ≫ m = i ≫ pullback.diagonal h := by
    apply pullback.hom_ext <;> simp [m]
  have hd : pullback.diagonal (i ≫ h) = i ≫ pullback.diagonal h ≫ inv m := by
    rw [← Category.assoc, ← hm, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hd]
  exact IsRigSurjective.isIso_comp i _
    (IsRigSurjective.comp_isIso _ (inv m) hh)

/-- Being a formal modification is unchanged by precomposing with an isomorphism. -/
theorem isFormalModification_isIso_comp {W' W Y : FppfSheaf B S hS} (i : W' ⟶ W) [IsIso i]
    (h : W ⟶ Y) (hW' : IsLocallyNoetherian B S hS W') (hY : IsLocallyNoetherian B S hS Y)
    (hproper : IsProper B S hS h) (hetale : IsRigEtale B S hS (i ≫ h))
    (hsurj : IsRigSurjective B S hS h)
    (hdiag : IsRigSurjective B S hS (pullback.diagonal h)) :
    IsFormalModification B S hS (i ≫ h) where
  isLocallyNoetherian_source := hW'
  isLocallyNoetherian_target := hY
  isProper := isProper_isIso_comp i h hproper
  isRigEtale := hetale
  isRigSurjective := IsRigSurjective.isIso_comp i h hsurj
  isRigSurjective_diagonal := isRigSurjective_diagonal_isIso_comp i h hdiag

/-- The canonical map to the preimage of the open complement of `T` is an isomorphism when the base
change of `f` along that open subspace is. -/
private theorem isIso_fromPreimage_openSubspaceOfPoints {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hfU : IsIso (pullback.snd f (Space.openSubspaceOfPoints B S hS X Tᶜ).ι)) :
    IsIso ((Space.openSubspaceOfPoints B S hS X Tᶜ).fromPreimage f) := by
  rw [← (Subfunctor.isPullback_fromPreimage (Space.openSubspaceOfPoints B S hS X Tᶜ)
    f).flip.flip.flip.isoPullback_hom_snd]
  infer_instance

/-- Let `X` be a locally Noetherian algebraic space, `T ⊆ |X|` a closed subset and `M` a
finite-type modification of `X` along the complement of `T` which is proper. Then a rig-étale
morphism over the completion `X_{/T}` isomorphic to the completion of `M` is a formal
modification. -/
theorem isFormalModification_of_isProper_of_iso
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXN : Space.IsLocallyNoetherian B S hS X)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (M : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ))
    (P : RigEtaleOverCompletion B S hS X T)
    (e : (Space.completionOverFunctor B S hS T).obj M.obj ≅ P.obj)
    (hf : Space.IsProper B S hS M.obj.hom) :
    IsFormalModification B S hS P.obj.hom := by
  have hX' : IsAlgebraicSpace B S hS M.obj.left := M.property.1.1
  have hfU : IsIso (pullback.snd M.obj.hom (Space.openSubspaceOfPoints B S hS X Tᶜ).ι) :=
    M.property.1.2
  have hfrom := isIso_fromPreimage_openSubspaceOfPoints M.obj.hom T hfU
  have hP : P.obj.hom = e.inv.left ≫ Space.completionSheafMap B S hS M.obj.hom T :=
    (Over.w e.inv).symm
  have : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv
  rw [hP]
  refine isFormalModification_isIso_comp e.inv.left _ P.property.2.1
    (isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian hX hXN T hT)
    (isProper_completionSheafMap B S hS hX' hX _ T hf) (hP ▸ P.property.2.2)
    (isRigSurjective_completionSheafMap hX' hX _ T hT hf
      (Space.pointsMap_surjective_of_isIso B S hS _))
    (isRigSurjective_diagonal_completionSheafMap hX' hX _ T hT hf.1 inferInstance)

/-- The completion `f_{/T} : X'_{/T'} ⟶ X_{/T}` of a proper morphism `f : X' ⟶ X` of algebraic
spaces over a locally Noetherian `X`, which is an isomorphism over the complement of a closed
`T ⊆ |X|`, is a formal modification as soon as it is rig-étale. -/
theorem isFormalModification_completionSheafMap_of_isRigEtale
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hXN : Space.IsLocallyNoetherian B S hS X) (f : X' ⟶ X)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T) (hf : Space.IsProper B S hS f)
    (hfU : IsIso (pullback.snd f (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    (hrig : IsRigEtale B S hS (Space.completionSheafMap B S hS f T)) :
    IsFormalModification B S hS (Space.completionSheafMap B S hS f T) := by
  have := isIso_fromPreimage_openSubspaceOfPoints f T hfU
  exact
    { isLocallyNoetherian_source :=
        isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian hX'
          (isLocallyNoetherian_of_isLocallyOfFiniteType hX' hX f hf.2.1.1 hXN) _
          (hT.preimage (Space.continuous_pointsMap B S hS f))
      isLocallyNoetherian_target :=
        isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian hX hXN T hT
      isProper := isProper_completionSheafMap B S hS hX' hX f T hf
      isRigEtale := hrig
      isRigSurjective := isRigSurjective_completionSheafMap hX' hX f T hT hf
        (Space.pointsMap_surjective_of_isIso B S hS _)
      isRigSurjective_diagonal :=
        isRigSurjective_diagonal_completionSheafMap hX' hX f T hT hf.1 inferInstance }

/-! ### Valuative squares lying over the complement of `T` or over `T` -/

/-- Two morphisms into `X'` agreeing after `f` and landing over an open `O` along which `f`
has invertible base change are equal. -/
theorem eq_of_comp_eq_of_isIso_pullback_snd {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X' ⟶ X} {O : Subfunctor X} (hfU : IsIso (pullback.snd f O.ι))
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a b : Z ⟶ X') (k : Z ⟶ O.toFunctor)
    (ha : a ≫ f = k ≫ O.ι) (hb : b ≫ f = k ≫ O.ι) : a = b := by
  have hl : ∀ (c : Z ⟶ X') (hc : c ≫ f = k ≫ O.ι),
      pullback.lift c k hc = k ≫ inv (pullback.snd f O.ι) := fun c hc ↦ by
    rw [← cancel_mono (pullback.snd f O.ι), pullback.lift_snd, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id]
  rw [← pullback.lift_fst a k ha, ← pullback.lift_fst b k hb, hl a ha, hl b hb]

/-- A valuative square for a morphism which is an isomorphism over the complement of `T`, whose
bottom edge avoids `T`, has exactly one dotted arrow. -/
theorem unique_lift_of_range_subset_compl {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X' ⟶ X} {T : Set (Space.points B S hS X)}
    (hfU : IsIso (pullback.snd f (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    (q : Space.ValuativeSquare f)
    (hq : Set.range (Space.pointsMap B S hS _ q.special) ⊆ Tᶜ) :
    Nonempty q.Lift ∧ Subsingleton q.Lift := by
  let O := Space.openSubspaceOfPoints B S hS X Tᶜ
  obtain ⟨k, hk⟩ := (Space.exists_factor_openSubspaceOfPoints_iff B S hS Tᶜ q.special).2 hq
  let jK := yoneda.map (Over.homMk
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K))) :
      B.obj q.field_mem ⟶ B.obj q.ring_mem) :
    siteObject B S hS q.field_mem (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) ⟶
    siteObject B S hS q.ring_mem q.base)
  let m := k ≫ inv (pullback.snd f O.ι) ≫ pullback.fst f O.ι
  have hm : m ≫ f = k ≫ O.ι := by
    simp only [m, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  refine ⟨⟨⟨m, ?_, hm.trans hk⟩⟩, ⟨fun l₁ l₂ ↦ ?_⟩⟩
  · refine eq_of_comp_eq_of_isIso_pullback_snd hfU _ _ (jK ≫ k) ?_ ?_
    · rw [Category.assoc, hm, Category.assoc]
    · rw [q.comm, Category.assoc, hk]
  · have h := eq_of_comp_eq_of_isIso_pullback_snd hfU l₁.map l₂.map k
      (l₁.special_comm.trans hk.symm) (l₂.special_comm.trans hk.symm)
    cases l₁; cases l₂
    cases h
    rfl

/-- A valuative square for a morphism with proper completion along `T`, whose bottom edge lies
over `T`, has exactly one dotted arrow. -/
theorem unique_lift_of_range_subset {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    {f : X' ⟶ X} {T : Set (Space.points B S hS X)}
    (hg : IsProper B S hS (Space.completionSheafMap B S hS f T))
    (q : Space.ValuativeSquare f)
    (hq : Set.range (Space.pointsMap B S hS _ q.special) ⊆ T) :
    Nonempty q.Lift ∧ Subsingleton q.Lift := by
  let V := siteObject B S hS q.ring_mem q.base
  have hprop := isProper_pullback_snd_of_isProper_completionSheafMap hX' hX f T hg V
    q.special (hasImageIn_of_range_subset q.special hq)
  have hPsp : IsAlgebraicSpace B S hS (pullback f q.special) :=
    isAlgebraicSpace_pullback B S hS f q.special hX' (isAlgebraicSpace_yoneda B S hS V) hX
  let jK := yoneda.map (Over.homMk
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K))) :
      B.obj q.field_mem ⟶ B.obj q.ring_mem) :
    siteObject B S hS q.field_mem (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) ⟶
    siteObject B S hS q.ring_mem q.base)
  let q' : Space.ValuativeSquare (pullback.snd f q.special) :=
    { R := q.R, K := q.K, ring_mem := q.ring_mem, field_mem := q.field_mem, base := q.base
      generic := pullback.lift q.generic jK q.comm
      special := 𝟙 _
      comm := by rw [pullback.lift_snd, Category.comp_id] }
  obtain ⟨⟨l'⟩, huniq⟩ := (Space.isProper_iff_forall_unique_lift_of_isFiniteType_of_isQuasiSeparated
    hPsp (isAlgebraicSpace_yoneda B S hS V) _ hprop.2.1
    (Space.isQuasiSeparated_of_isSeparated B S hS hprop.1)).1 hprop q'
  let toLift (l : q.Lift) : q'.Lift :=
    { map := pullback.lift l.map (𝟙 _) (by rw [l.special_comm, Category.id_comp])
      generic_comm := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, l.generic_comm]
          exact (pullback.lift_fst _ _ _).symm
        · rw [Category.assoc, pullback.lift_snd, Category.comp_id]
          exact (pullback.lift_snd _ _ _).symm
      special_comm := pullback.lift_snd _ _ _ }
  refine ⟨⟨⟨l'.map ≫ pullback.fst _ _, ?_, ?_⟩⟩, ⟨fun l₁ l₂ ↦ ?_⟩⟩
  · have := congrArg (· ≫ pullback.fst f q.special) l'.generic_comm
    simp only [Category.assoc] at this
    exact this.trans (pullback.lift_fst _ _ _)
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    show (l'.map ≫ pullback.snd f q.special) ≫ q.special = q.special
    rw [l'.special_comm, Category.id_comp]
  · have h := congrArg (fun l : q'.Lift ↦ l.map ≫ pullback.fst f q.special)
      (huniq.elim (toLift l₁) (toLift l₂))
    change pullback.lift l₁.map _ _ ≫ _ = pullback.lift l₂.map _ _ ≫ _ at h
    rw [pullback.lift_fst, pullback.lift_fst] at h
    cases l₁; cases l₂
    cases h
    rfl

end AlgebraicGeometry.FormalSpace

end
