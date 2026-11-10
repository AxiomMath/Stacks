module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Completion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPointsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange

/-!
# Properness for a morphism of completions

Let `S` be a scheme contained in a big fppf site `B`, let `f : X' ⟶ X` be a morphism of
algebraic spaces over `S` and let `T` be a set of points of `X`. If `f` is proper then so is
the induced morphism of completions `f_{/T} : X'_{/|f|⁻¹ T} ⟶ X_{/T}`.

## Main results

* `AlgebraicGeometry.FormalSpace.isProper_completionSheafMap`: if `f` is proper, then `f_{/T}`
  is proper.
* `AlgebraicGeometry.FormalSpace.isSeparatedAndFiniteType_completionSheafMap`: if `f` is proper,
  then `f_{/T}` is representable by algebraic spaces and its base changes along scheme-valued
  points of its target are separated and of finite type.
* `AlgebraicGeometry.FormalSpace.isProper_completionSheafMap_of_universallyClosedULift`: if `f`
  is proper, then `f_{/T}` is proper, assuming that universal closedness passes to universe
  lifts.

## References

* [Stacks Project, Tag 0GDD](https://stacks.math.columbia.edu/tag/0GDD)
* [Stacks Project, Tag 0AQ9](https://stacks.math.columbia.edu/tag/0AQ9)
* [Stacks Project, Tag 0APV](https://stacks.math.columbia.edu/tag/0APV)
* [Stacks Project, Tag 0AM6](https://stacks.math.columbia.edu/tag/0AM6)
* [Stacks Project, Tag 04WP](https://stacks.math.columbia.edu/tag/04WP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- `inferInstance` searches for limits in the presheaf category on the big fppf site
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_CompletionProper :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_CompletionProper
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
-- `inferInstance` searches for limits in the presheaf category on the big fppf site
/-- Pullbacks of large-valued presheaves on the big fppf site over `S`. -/
local instance hasPullbacks_presheafULift_CompletionProper :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) := inferInstance

local instance (priority := high) hasPullback_presheafULift_CompletionProper
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Transferring the conjuncts of properness to a universe lift -/

/-- The universe lift of a separated morphism of presheaves of `Type u` is separated. -/
private theorem isSeparatedULift_whiskerRight_of_isSeparated
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : F ⟶ G)
    (hq : Space.IsSeparated B S hS q) :
    Space.IsSeparatedULift.{u + 1} B S hS
      (Functor.whiskerRight q uliftFunctor.{u + 1}) := by
  let C := BigFppfOver B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1}
  let R := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have hdiag : pullback.diagonal (H.map q) =
      H.map (pullback.diagonal q) ≫ (PreservesPullback.iso H q q).hom := by
    apply pullback.hom_ext <;> simp [← H.map_comp]
  have h : R.relative (yoneda ⋙ H) (H.map (pullback.diagonal q)) :=
    (Space.relative_comp_map_iff yoneda H R (pullback.diagonal q)).mpr hq
  change R.relative (uliftYoneda.{u + 1}) (pullback.diagonal (H.map q))
  rw [hdiag]
  exact MorphismProperty.RespectsIso.postcomp (R.relative (uliftYoneda.{u + 1}))
    (PreservesPullback.iso H q q).hom _ h

/-- Separatedness of a morphism of large-valued presheaves is unchanged by precomposing with
an isomorphism. -/
private theorem isSeparatedULift_precomp
    {F G K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (e : F ⟶ G) [IsIso e] (f : G ⟶ K)
    (hf : Space.IsSeparatedULift.{u + 1} B S hS f) :
    Space.IsSeparatedULift.{u + 1} B S hS (e ≫ f) :=
  MorphismProperty.RespectsIso.precomp
    ((MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1})).diagonal e f hf

/-- A base change of a proper morphism `f` along a morphism from a representable presheaf lifts
to a proper pullback along `ξ₀` whose universe lift is the pullback along the lift of `ξ₀`. -/
private theorem exists_isProper_pullback_fst_and_iso_whiskerRight
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (hf : Space.IsProper B S hS f) (U : BigFppfOver B S hS)
    (ξ : yoneda.obj U ⋙ uliftFunctor.{u + 1} ⟶ X ⋙ uliftFunctor.{u + 1}) :
    ∃ (ξ₀ : yoneda.obj U ⟶ X) (_ : Space.IsProper B S hS (pullback.fst ξ₀ f))
      (e : pullback ξ (Functor.whiskerRight f uliftFunctor.{u + 1}) ≅
        pullback ξ₀ f ⋙ uliftFunctor.{u + 1}),
      e.hom ≫ Functor.whiskerRight (pullback.fst ξ₀ f) uliftFunctor.{u + 1} =
        pullback.fst ξ (Functor.whiskerRight f uliftFunctor.{u + 1}) := by
  let H := (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
    uliftFunctor.{u + 1}
  obtain ⟨ξ₀, hξ₀⟩ := H.map_surjective ξ
  let A : AlgebraicSpaces B S hS := ⟨X', hX'⟩
  let Z : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Uₐ : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let fA : A ⟶ Z := ObjectProperty.homMk f
  let ξA : Uₐ ⟶ Z := ObjectProperty.homMk ξ₀
  let q : AlgebraicSpaces.fiberProduct B S hS ξA fA ⟶ Uₐ :=
    ObjectProperty.homMk (pullback.fst ξA.hom fA.hom)
  have hsq : IsPullback (H.map (pullback.fst ξ₀ f)) (H.map (pullback.snd ξ₀ f)) ξ
      (Functor.whiskerRight f uliftFunctor.{u + 1}) := by
    rw [← hξ₀]
    exact (IsPullback.of_hasPullback ξ₀ f).map H
  exact ⟨ξ₀, (Space.isProper_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS ξA fA).flip hf, hsq.isoPullback.symm,
    (Iso.inv_comp_eq hsq.isoPullback).mpr hsq.isoPullback_hom_fst.symm⟩

/-- The universe lift of a proper morphism of algebraic spaces over `S` satisfies the Bootstrap
condition of Stacks 03XZ for being separated and of finite type. -/
private theorem hasPropertyULift_whiskerRight_of_isSeparated_isFiniteType
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (hf : Space.IsProper B S hS f)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (Functor.whiskerRight f uliftFunctor.{u + 1})) :
    Space.HasPropertyULift.{u + 1} B S hS
      (Space.separatedPropertyULift.{u + 1} B S hS ⊓
        Space.finiteTypePropertyULift.{u + 1} B S hS)
      (Functor.whiskerRight f uliftFunctor.{u + 1}) hrep := by
  intro U ξ
  obtain ⟨ξ₀, hq, e, he⟩ := exists_isProper_pullback_fst_and_iso_whiskerRight B S hS hX' hX f hf U ξ
  have hqsepl : Space.IsSeparatedULift.{u + 1} B S hS
      (Functor.whiskerRight (pullback.fst ξ₀ f) uliftFunctor.{u + 1}) :=
    isSeparatedULift_whiskerRight_of_isSeparated B S hS (pullback.fst ξ₀ f) hq.1
  have hqftl : Space.IsFiniteTypeULift.{u + 1} B S hS
      (Functor.whiskerRight (pullback.fst ξ₀ f) uliftFunctor.{u + 1}) :=
    (Space.isFiniteTypeULift_whiskerRight_iff B S hS (pullback.fst ξ₀ f)).mpr hq.2.1
  exact ⟨he ▸ isSeparatedULift_precomp B S hS e.hom _ hqsepl,
    he ▸ Space.holdsOnEveryEtaleChartULift_precomp.{u + 1} B S hS
      (@AlgebraicGeometry.LocallyOfFiniteType.{u}) e.hom _ hqftl.1,
    he ▸ Space.isQuasiCompactULift_precomp.{u + 1} B S hS e _ hqftl.2⟩

/-- The universe lift of a proper morphism of algebraic spaces over `S` satisfies the Bootstrap
condition of Stacks 03XZ for universal closedness, given that universal closedness of a morphism
of presheaves of `Type u` passes to its universe lift. -/
private theorem hasPropertyULift_whiskerRight_of_universallyClosed
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (hf : Space.IsProper B S hS f)
    (htransfer : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : F ⟶ G),
      Space.UniversallyClosed B S hS q →
      Space.UniversallyClosedULift.{u + 1} B S hS
        (Functor.whiskerRight q uliftFunctor.{u + 1}))
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (Functor.whiskerRight f uliftFunctor.{u + 1})) :
    Space.HasPropertyULift.{u + 1} B S hS
      (Space.universallyClosedPropertyULift.{u + 1} B S hS)
      (Functor.whiskerRight f uliftFunctor.{u + 1}) hrep := by
  intro U ξ
  obtain ⟨ξ₀, hq, e, he⟩ := exists_isProper_pullback_fst_and_iso_whiskerRight B S hS hX' hX f hf U ξ
  exact he ▸ Space.universallyClosedULift_precomp.{u + 1} B S hS e _
    (htransfer (pullback.fst ξ₀ f) hq.2.2)

/-! ### Descending the Bootstrap condition along the completion square -/

/-- Let `P` be a property invariant under isomorphism. If the universe lift of a morphism of
algebraic spaces over `S` satisfies the Bootstrap condition of Stacks 03XZ for `P`, then the
induced morphism of completions is representable by algebraic spaces and satisfies it too. -/
private theorem hasPropertyULift_completionSheafMap_of_whiskerRight
    (P : MorphismProperty (Space.AlgebraicSpacesULift.{u + 1} B S hS)) [P.RespectsIso]
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hP : ∀ hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Functor.whiskerRight f uliftFunctor.{u + 1}),
      Space.HasPropertyULift.{u + 1} B S hS P
        (Functor.whiskerRight f uliftFunctor.{u + 1}) hrep) :
    ∃ hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.completionSheafMap B S hS f T).hom,
      Space.HasPropertyULift.{u + 1} B S hS P
        (Space.completionSheafMap B S hS f T).hom hrep := by
  let C := BigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1}
  have hlarge : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (H.map f) := by
    apply (Space.isRepresentableByAlgebraicSpacesULift_whiskerRight_iff B S hS f).mpr
    intro U ξ
    exact isAlgebraicSpace_pullback B S hS ξ f (isAlgebraicSpace_yoneda B S hS U) hX' hX
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
    Space.hasPropertyULift_of_isPullback B S hS hp hlarge (hP hlarge)⟩

/-! ### Stacks 0GDD -/

/-- Let `f : X' ⟶ X` be a morphism of algebraic spaces over `S` and let `T` be a set of points
of `X`. If `f` is proper, then the induced morphism of completions `X'_{/|f|⁻¹ T} ⟶ X_{/T}` is
representable by algebraic spaces and each of its base changes along a scheme-valued point of
its target is separated and of finite type. -/
@[ega "I 10.13.6" "special case"]
theorem isSeparatedAndFiniteType_completionSheafMap
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hf : Space.IsProper B S hS f) :
    ∃ hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.completionSheafMap B S hS f T).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (Space.separatedPropertyULift.{u + 1} B S hS ⊓
          Space.finiteTypePropertyULift.{u + 1} B S hS)
        (Space.completionSheafMap B S hS f T).hom hrep :=
  hasPropertyULift_completionSheafMap_of_whiskerRight B S hS _ hX' hX f T
    (fun hrep ↦ hasPropertyULift_whiskerRight_of_isSeparated_isFiniteType B S hS hX' hX f
      hf hrep)

/-- Let `f : X' ⟶ X` be a morphism of algebraic spaces over `S` and let `T` be a set of points
of `X`. Assume `htransfer`: universal closedness of a morphism of presheaves of `Type u` passes
to its universe lift. If `f` is proper, then the induced morphism of completions
`X'_{/|f|⁻¹ T} ⟶ X_{/T}` is proper. -/
theorem isProper_completionSheafMap_of_universallyClosedULift
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hf : Space.IsProper B S hS f)
    (htransfer : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : F ⟶ G),
      Space.UniversallyClosed B S hS q →
      Space.UniversallyClosedULift.{u + 1} B S hS
        (Functor.whiskerRight q uliftFunctor.{u + 1})) :
    IsProper B S hS (Space.completionSheafMap B S hS f T) := by
  refine hasPropertyULift_completionSheafMap_of_whiskerRight B S hS
    (Space.properPropertyULift.{u + 1} B S hS) hX' hX f T (fun hrep U ξ ↦ ?_)
  have h1 := hasPropertyULift_whiskerRight_of_isSeparated_isFiniteType
    B S hS hX' hX f hf hrep U ξ
  have h2 := hasPropertyULift_whiskerRight_of_universallyClosed
    B S hS hX' hX f hf htransfer hrep U ξ
  exact ⟨h1.1, h1.2, h2⟩

/-- Let `f : X' ⟶ X` be a morphism of algebraic spaces over `S` and let `T` be a set of points
of `X`. If `f` is proper, then the induced morphism of completions
`X'_{/|f|⁻¹ T} ⟶ X_{/T}` is proper. -/
@[stacks 0GDD]
theorem isProper_completionSheafMap
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hf : Space.IsProper B S hS f) :
    IsProper B S hS (Space.completionSheafMap B S hS f T) :=
  isProper_completionSheafMap_of_universallyClosedULift B S hS hX' hX f T hf
    fun q hq ↦
      Space.universallyClosedULift_whiskerRight_of_universallyClosed.{u + 1} B S hS q hq

end AlgebraicGeometry.FormalSpace

end
