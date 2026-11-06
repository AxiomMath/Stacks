module

public import StacksFrontier.AlgebraicGeometry.Quot.TestSchemeTotalPresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverFromAffineChartsAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison

/-!
# Being an algebraic space affine and of finite presentation is local on the base

Let `Y` be an algebraic space and `R` a functor on the test schemes over `Y`, with values in
`Type (u + 1)` as the representability statements of the `Quot` chapter have them.  If `R` is an
fppf sheaf over `Y` (`AlgebraicGeometry.Space.IsFppfSheafOver`) and its restriction to every
affine test scheme `V` over `Y` is an algebraic space affine and of finite presentation over `V`,
then `R` is an algebraic space affine and of finite presentation over `Y`.  This is the step of
the proof of Stacks 0DLC, part (3), that the source refers to Stacks 04U0, 03WG and 0410.

## Main definitions

* `AlgebraicGeometry.Space.AffineFinitePresentationOfAffineTestSchemes`: the statement, as a
  proposition.
* `AlgebraicGeometry.Space.shrinkFunctor`: a functor with essentially small values, made
  `Type u`-valued.

## Main results

* `AlgebraicGeometry.Space.small_obj_of_isFppfSheafOver`: such an `R` has essentially small
  values.

## Implementation notes

The values of `R` are first shrunk to `Type u` (they are essentially small: over an affine test
scheme by the hypothesis, in general because `R` is separated for the cover by affine opens).  The
total presheaf of the shrunk functor is an fppf sheaf over `Y` whose base change to every affine
open of an atlas of `Y` is an affine scheme, of size bounded by that of the atlas; Stacks 03I2
for affine morphisms (`AlgebraicGeometry.Space.isAlgebraicSpace_and_presheaf_isAffineHom_of_atlas`)
makes it an algebraic space affine over `Y`, and being locally of finite presentation is read on
the affine test schemes (Stacks 0410).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (B S hS) in
/-- **Step (G) of the proof of Stacks 0DLC, part (3)**: an fppf sheaf over an algebraic space
`Y` whose restriction to every affine test scheme `V` over `Y` is an algebraic space affine and of
finite presentation over `V` is an algebraic space affine and of finite presentation over `Y`.
In the source this is Stacks 04U0, 03WG and 0410. -/
def AffineFinitePresentationOfAffineTestSchemes : Prop :=
  ∀ (Y : AlgebraicSpaces B S hS) (R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)), IsFppfSheafOver R →
    (∀ V : SchemesOver Y, IsAffine ((BigFppfOver.toScheme B S hS).obj V.left) →
      IsAffineFinitePresentationAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj V.left)
        ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS) V.hom).op ⋙ R)) →
    IsAffineFinitePresentationAlgebraicSpaceOver Y R

variable {Y : AlgebraicSpaces B S hS}

/-! ### Shrinking the values -/

section Shrink

variable (R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)) [∀ T, Small.{u} (R.obj T)]

/-- A functor on the test schemes with essentially small values, with its values replaced by
`Type u`-valued models. -/
def shrinkFunctor : (SchemesOver Y)ᵒᵖ ⥤ Type u where
  obj T := Shrink.{u} (R.obj T)
  map f := ↾fun x => equivShrink _ (R.map f ((equivShrink _).symm x))
  map_id T := ConcreteCategory.hom_ext _ _ fun x => by simp
  map_comp f g := ConcreteCategory.hom_ext _ _ fun x => by simp

/-- The universe lift of `AlgebraicGeometry.Space.shrinkFunctor` is the functor itself. -/
def shrinkFunctorULiftIso : shrinkFunctor R ⋙ uliftFunctor.{u + 1, u} ≅ R :=
  NatIso.ofComponents (fun T => Equiv.toIso (Equiv.ulift.trans (equivShrink _).symm))
    (fun f => ConcreteCategory.hom_ext _ _ fun x => by
      change (equivShrink _).symm (equivShrink _ (R.map f ((equivShrink _).symm x.down))) =
        R.map f ((equivShrink _).symm x.down)
      simp)

end Shrink

/-! ### Smallness -/

/-- The test scheme over the algebraic space of a test scheme `V` given by `V` itself. -/
abbrev selfTestScheme (V : SchemesOver Y) : SchemesOver ((schemeSpaceFunctor B S hS).obj V.left) :=
  CostructuredArrow.mk (Y := V.left) (𝟙 ((schemeSpaceFunctor B S hS).obj V.left))

/-- The test scheme `V` over itself, read as a test scheme over `Y`, is `V`. -/
def selfTestSchemeMapIso (V : SchemesOver Y) :
    (CostructuredArrow.map (S := schemeSpaceFunctor B S hS) V.hom).obj (selfTestScheme V) ≅ V :=
  CostructuredArrow.isoMk (Iso.refl _) (by simp)

/-- Over an affine test scheme, the value of a functor which is an algebraic space over every
affine test scheme is essentially small. -/
theorem small_obj_of_isAffine (R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1))
    (hloc : ∀ V : SchemesOver Y, IsAffine ((BigFppfOver.toScheme B S hS).obj V.left) →
      IsAffineFinitePresentationAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj V.left)
        ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS) V.hom).op ⋙ R))
    (V : SchemesOver Y) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V.left)) :
    Small.{u} (R.obj (Opposite.op V)) := by
  obtain ⟨H, p, -, -, ⟨c⟩⟩ := hloc V hV
  let e : R.obj (Opposite.op V) ≃ ULift.{u + 1} (spacePointsOverObj p (selfTestScheme V)) :=
    (R.mapIso (selfTestSchemeMapIso V).op).toEquiv.trans (c.app (Opposite.op _)).toEquiv.symm
  exact small_map e

/-- **The values of an fppf sheaf over `Y` which is an algebraic space over every affine test
scheme are essentially small**: over an affine test scheme by hypothesis, and in general because
the sheaf is separated for the cover by affine opens. -/
theorem small_obj_of_isFppfSheafOver (R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1))
    (hR : IsFppfSheafOver R)
    (hloc : ∀ V : SchemesOver Y, IsAffine ((BigFppfOver.toScheme B S hS).obj V.left) →
      IsAffineFinitePresentationAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj V.left)
        ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS) V.hom).op ⋙ R))
    (T : (SchemesOver Y)ᵒᵖ) : Small.{u} (R.obj T) := by
  let C := BigFppfOver.affineSubordinateCover B S hS T.unop.left
  have : ∀ i (y : Y.1.obj (Opposite.op (C.X i))),
      Small.{u} (R.obj (Opposite.op (pointTestScheme (C.X i) y))) :=
    fun i y => small_obj_of_isAffine R hloc _ i.down.1.2
  let toTotal : R.obj T → (totalPresheaf R).obj (Opposite.op T.unop.left) := fun r =>
    ⟨testPoint T.unop, R.map (pointTestSchemeIso T.unop).hom.op r⟩
  let Φ : R.obj T → ∀ i, (totalPresheaf R).obj (Opposite.op (C.X i)) :=
    fun r i => (totalPresheaf R).map (C.f i).op (toTotal r)
  have hsep : Presieve.IsSeparatedFor (totalPresheaf R) C.sieve₀.arrows :=
    ((isSheaf_iff_isSheaf_of_type _ _).1 hR _
      (BigFppfOver.mem_topology_sieve₀_affineSubordinateCover B S hS _)).isSeparatedFor
  have hinj : Function.Injective Φ := by
    intro r₁ r₂ h
    have ht : toTotal r₁ = toTotal r₂ := by
      refine hsep.ext ?_
      rintro V' _ ⟨_, k, _, ⟨i⟩, rfl⟩
      rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
      exact congrArg _ (congrFun h i)
    exact (FunctorToTypes.map_map_eq_self_of_comp_eq_id R
        (pointTestSchemeIso T.unop).op.hom_inv_id r₁).symm.trans
      ((congrArg (R.map (pointTestSchemeIso T.unop).inv.op)
        (eq_of_heq (Sigma.mk.inj_iff.1 ht).2)).trans
        (FunctorToTypes.map_map_eq_self_of_comp_eq_id R
          (pointTestSchemeIso T.unop).op.hom_inv_id r₂))
  have : ∀ i, Small.{u} ((totalPresheaf R).obj (Opposite.op (C.X i))) := fun i =>
    small_sigma (fun y : Y.1.obj (Opposite.op (C.X i)) =>
      R.obj (Opposite.op (pointTestScheme (C.X i) y)))
  have : Small.{u} C.I₀ := small_ulift _
  exact small_of_injective hinj

/-! ### The affine squares -/

/-- Being locally of finite presentation passes to base changes of presheaves which are
algebraic spaces (Stacks 03XR). -/
theorem isLocallyOfFinitePresentation_of_isPullback {P X Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) (hX : IsAlgebraicSpace B S hS X)
    (hZ : IsAlgebraicSpace B S hS Z) (hW : IsAlgebraicSpace B S hS W) {fst : P ⟶ X}
    {snd : P ⟶ Z} {f : X ⟶ W} {g : Z ⟶ W} (h : IsPullback fst snd f g)
    (hf : IsLocallyOfFinitePresentation B S hS f) :
    IsLocallyOfFinitePresentation B S hS snd := by
  have h' : IsPullback (ObjectProperty.homMk fst : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk snd : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W, hW⟩)
      (ObjectProperty.homMk g : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W, hW⟩) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) h
  exact (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback h' hf

/-- **The affine square over an affine test scheme.**  If the restriction of a `Type u`-valued
functor `R` to an affine test scheme `V` over `Y` is (up to universe lift) an algebraic space
affine and of finite presentation over `V`, then the base change of the total presheaf of `R`
along `V ⟶ Y` is an affine scheme `W`, locally of finite presentation over `V`. -/
theorem exists_isPullback_totalProj (R : (SchemesOver Y)ᵒᵖ ⥤ Type u) (V : SchemesOver Y)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V.left))
    (h : IsAffineFinitePresentationAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj V.left)
      (restrictTestScheme R V ⋙ uliftFunctor.{u + 1, u})) :
    ∃ (W : BigAffineFppf B S hS)
      (P : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ⟶ totalPresheaf R)
      (q : (BigAffineFppf.inclusion B S hS).obj W ⟶ V.left),
      IsPullback P (yoneda.map q) (totalProj R) V.hom.hom ∧
        IsLocallyOfFinitePresentation B S hS (yoneda.map q) := by
  obtain ⟨H, p, hpa, hpfp, ⟨c⟩⟩ := h
  let c' : spacePointsOver p ≅ restrictTestScheme R V :=
    ((Functor.FullyFaithful.ofFullyFaithful uliftFunctor.{u + 1, u}).whiskeringRight _).preimageIso
      c
  let e : totalPresheaf (restrictTestScheme R V) ≅ H.1 :=
    (totalPresheafIso c').symm ≪≫ totalPresheafSpacePointsOverIso p
  have he : e.hom ≫ p.hom = totalProj (restrictTestScheme R V) := by
    show totalPresheafMap c'.inv ≫ (totalPresheafSpacePointsOverIso p).hom ≫ p.hom = _
    rw [totalPresheafSpacePointsOverIso_hom_comp, totalPresheafMap_totalProj]
  have h₀ : IsPullback e.inv p.hom (totalProj (restrictTestScheme R V)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [← he, Iso.inv_hom_id_assoc, Category.comp_id]⟩
  have h₁ : IsPullback (e.inv ≫ totalPresheafRestrict R V) p.hom (totalProj R) V.hom.hom := by
    simpa only [Category.id_comp] using h₀.paste_horiz (isPullback_totalPresheafRestrict R V)
  obtain ⟨W, p', q, hW⟩ := hpa ⟨V.left, hV⟩ (𝟙 ((schemeSpaceFunctor B S hS).obj V.left).1)
  let q' : (BigAffineFppf.inclusion B S hS).obj W ⟶ V.left := q
  have hW' : IsPullback p' (yoneda.map q') p.hom (𝟙 ((schemeSpaceFunctor B S hS).obj V.left).1) :=
    hW
  refine ⟨W, p' ≫ e.inv ≫ totalPresheafRestrict R V, q', ?_, ?_⟩
  · exact (hW'.paste_horiz h₁).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  · exact isLocallyOfFinitePresentation_of_isPullback (isAlgebraicSpace_yoneda B S hS _) H.2
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _) hW' hpfp.1

/-! ### Step (G) -/

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_AffineFinitePresentationGluing
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Step (G) of the proof of Stacks 0DLC, part (3)**: being an algebraic space affine and of
finite presentation over `Y` can be checked on the affine test schemes over `Y`, for an fppf sheaf
over `Y`. -/
theorem affineFinitePresentationOfAffineTestSchemes :
    AffineFinitePresentationOfAffineTestSchemes B S hS := by
  intro Y R hR hloc
  have := small_obj_of_isFppfSheafOver R hR hloc
  let R' := shrinkFunctor R
  let eR := shrinkFunctorULiftIso R
  have hR' : IsFppfSheafOver R' :=
    IsFppfSheafOver.of_uliftFunctor ((Presheaf.isSheaf_of_iso_iff (totalPresheafIso eR)).2 hR)
  have hsq := fun (V : BigFppfOver B S hS) (g : ((schemeSpaceFunctor B S hS).obj V).1 ⟶ Y.1)
      (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) =>
    exists_isPullback_totalProj R' (CostructuredArrow.mk (ObjectProperty.homMk g)) hV
      ((hloc _ hV).of_iso (Functor.isoWhiskerLeft (CostructuredArrow.map
        (S := schemeSpaceFunctor B S hS) _).op eR).symm)
  obtain ⟨U, a, hs, he⟩ := Y.2.exists_atlas
  obtain ⟨hGalg, hπpre⟩ := isAlgebraicSpace_and_presheaf_isAffineHom_of_atlas B S hS Y.2 hR'
    (totalProj R') hs he (μ := ((BigFppfOver.toScheme B S hS).obj U).size) U.left.property
    (fun V u hu hV => by
      obtain ⟨W, P, q, hpb, hlfp⟩ := hsq V (yoneda.map u ≫ a) hV
      refine ⟨(BigAffineFppf.inclusion B S hS).obj W, P, q, hpb, W.property, ?_⟩
      have : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q) :=
        (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
          LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget q).1 hlfp
      have : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map u) := hu
      have : IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((BigAffineFppf.inclusion B S hS).obj W)) := W.property
      exact Scheme.size_le_of_locallyOfFiniteType
        ((BigFppfOver.toScheme B S hS).map q ≫ (BigFppfOver.toScheme B S hS).map u))
  have hπ : IsAffineHom B S hS (totalProj R') := isAffineHom_of_presheaf hπpre
  have hlfp : IsLocallyOfFinitePresentation B S hS (totalProj R') := by
    refine ((isLocallyOfFinitePresentation_tfae B S hS hGalg Y.2 (totalProj R')).out 1 4).2
      fun W g hW => ?_
    obtain ⟨W₁, P, q, hpb, hq⟩ := hsq W g hW
    have h₁ : IsPullback (pullback.snd g (totalProj R')) (pullback.fst g (totalProj R'))
        (totalProj R') g := (IsPullback.of_hasPullback g (totalProj R')).flip
    have h₂ : IsPullback (h₁.isoIsPullback _ _ hpb).hom (pullback.fst g (totalProj R'))
        (yoneda.map q) (𝟙 _) :=
      IsPullback.of_horiz_isIso
        ⟨(h₁.isoIsPullback_hom_snd _ _ hpb).trans (Category.comp_id _).symm⟩
    exact isLocallyOfFinitePresentation_of_isPullback
      (isAlgebraicSpace_pullback B S hS g (totalProj R') (isAlgebraicSpace_yoneda B S hS W) hGalg
        Y.2)
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS W)
      (isAlgebraicSpace_yoneda B S hS W) h₂ hq
  exact ⟨⟨totalPresheaf R', hGalg⟩, ObjectProperty.homMk (totalProj R'), hπ,
    ⟨hlfp, isQuasiCompact_of_isAffineHom' B S hS _ hGalg Y.2 hπ,
      isQuasiSeparated_of_isAffineHom B S hS _ hGalg Y.2 hπ⟩,
    ⟨Functor.isoWhiskerRight (spacePointsOverTotalProjIso R' hGalg) uliftFunctor.{u + 1, u} ≪≫ eR⟩⟩

end AlgebraicGeometry.Space

end
