module

public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentSituationMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae03KM
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentabilityCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom

/-!
# Descending a morphism into the base change along a presentation of the global functions

In the proof of Stacks 07SQ a stage `X₀` of the descent situation of Stacks 084R is mapped to
the spectrum of a presentation `C = A[x₁, …, xₙ]/(g₁, …, gₙ)` of a `u`-model `A` of its ring of
global functions, and the morphism whose descent is wanted is one from an étale affine chart of
`X₀` into the base change

`X₀ ×_{Spec A} Spec C`.

This file discharges the hypotheses that
`AlgebraicGeometry.Space.DescentSituation.morphismDescentSystem` asks of that data, and assembles
the morphism descent system of Stacks 084W from it.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.morphismDescentSystemOfSpecMap`: the morphism descent
  system of Stacks 084W attached to an étale chart of the chosen stage of a descent situation and
  a morphism from it, over the stage, into the base change of the stage along the spectrum of a
  ring map of finite presentation.
* `AlgebraicGeometry.Space.DescentSituation.morphismDescentSystemOfPresentation`: the same at the
  spectrum of the structure homomorphism of a polynomial presentation, which is the situation of
  display 70.5.10.1 of the proof of Stacks 07SQ.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_pullback_fst_schemePointsMap_Spec_map` and
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_pullback_fst_schemePointsMap_Spec_map`:
  the base change of a presheaf along the spectrum of a ring map of finite presentation is affine
  and locally of finite presentation over it. No algebraicity is needed for these.
* `AlgebraicGeometry.Space.isAlgebraicSpace_pullback_schemePointsMap_Spec_map` and
  `AlgebraicGeometry.Space.isFinitePresentation_pullback_fst_schemePointsMap_Spec_map`: the base
  change of an algebraic space is an algebraic space, and is of finite presentation over it.
* `AlgebraicGeometry.Space.isFinitePresentation_etaleChart`: an étale chart of a quasi-separated
  algebraic space whose total scheme is quasi-compact and quasi-separated is of finite
  presentation.

## Implementation notes

*Why the base change needs no algebraicity for the first two statements.* Both come from the
relatively representable form `AlgebraicGeometry.Space.presheaf_inverseImage_schemePointsMap`,
which is stable under base change by `CategoryTheory.MorphismProperty.relative` being so, and
then from the two readings of that form: Stacks 03WG, condition (1) implies condition (2), for
affineness, and the implication of Stacks 03MJ for the chart condition. Quasi-compactness and
quasi-separatedness, by contrast, are deduced from affineness and that deduction asks its source
and target to be algebraic spaces — which the base change is, by Stacks 02YS, because it is
representable by objects of the site.

*What the morphism descent system does not assume.* Quasi-compactness and quasi-separatedness of
the two algebraic spaces over the stage are not hypotheses: finite presentation over the stage
transports both, the stage itself being quasi-compact and quasi-separated in a descent situation.
This is the reduction already made in
`AlgebraicGeometry.Space.DescentSituation.morphismDescentSystem`.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_descentSituationGlobalFunctionsDescent :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_descentSituationGlobalFunctionsDescent
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Base change along a point of a presheaf -/

/-- The base change of the spectrum of a ring map along a point of an arbitrary presheaf, in the
relatively representable form: the property of scheme morphisms transported along the base change
of `AlgebraicGeometry.Space.presheaf_inverseImage_schemePointsMap`. -/
theorem presheaf_inverseImage_pullback_fst_schemePointsMap (Q : MorphismProperty Scheme.{u})
    [Q.IsStableUnderBaseChange] {T T' : Scheme.{u}} (f : T ⟶ T')
    [AlgebraicGeometry.IsAffineHom f] [LocallyOfFiniteType f] (hf : Q f)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F ⟶ schemePoints B S hS T') :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf
      (pullback.fst p (schemePointsMap B S hS f)) := by
  have _ := BigFppfOver.isStableUnderBaseChange_inverseImage B S hS Q
  exact (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
      (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS))).of_isPullback
    (IsPullback.of_hasPullback p (schemePointsMap B S hS f)).flip
    (presheaf_inverseImage_schemePointsMap B S hS Q f hf)

/-- The base change along a point of the spectrum of a finite type ring map is affine, in the
relatively representable form. -/
private theorem presheaf_isAffineHom_pullback_fst_schemePointsMap_Spec_map
    {R R' : CommRingCat.{u}} (φ : R ⟶ R') (hφ : RingHom.FiniteType φ.hom)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F ⟶ schemePoints B S hS (Spec R)) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.IsAffineHom.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (pullback.fst p (schemePointsMap B S hS (Spec.map φ))) := by
  have _ : LocallyOfFiniteType (Spec.map φ) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType.{u})).mpr hφ
  exact presheaf_inverseImage_pullback_fst_schemePointsMap B S hS
    (@AlgebraicGeometry.IsAffineHom.{u}) (Spec.map φ) inferInstance p

/-- **The base change of a presheaf along the spectrum of a ring map of finite type is affine
over it.** -/
theorem isAffineHom_pullback_fst_schemePointsMap_Spec_map {R R' : CommRingCat.{u}} (φ : R ⟶ R')
    (hφ : RingHom.FiniteType φ.hom) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : F ⟶ schemePoints B S hS (Spec R)) :
    IsAffineHom B S hS (pullback.fst p (schemePointsMap B S hS (Spec.map φ))) :=
  isAffineHom_of_presheaf (presheaf_isAffineHom_pullback_fst_schemePointsMap_Spec_map B S hS φ hφ p)

/-- **The base change of a presheaf along the spectrum of a ring map of finite presentation is
locally of finite presentation over it.** -/
theorem isLocallyOfFinitePresentation_pullback_fst_schemePointsMap_Spec_map
    {R R' : CommRingCat.{u}} (φ : R ⟶ R') (hφ : RingHom.FinitePresentation φ.hom)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F ⟶ schemePoints B S hS (Spec R)) :
    IsLocallyOfFinitePresentation B S hS
      (pullback.fst p (schemePointsMap B S hS (Spec.map φ))) := by
  have hlfp : LocallyOfFinitePresentation (Spec.map φ) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation.{u})).mpr hφ
  refine presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp B S hS _
    (fun i q hi hq => ?_) _
    (presheaf_inverseImage_pullback_fst_schemePointsMap B S hS
      (@LocallyOfFinitePresentation.{u}) (Spec.map φ) hlfp p)
  have _ : Etale i := hi
  have _ : LocallyOfFinitePresentation q := hq
  infer_instance

/-- **The base change of an algebraic space along the spectrum of a ring map of finite type is an
algebraic space.** The base change is representable by objects of the site, hence by algebraic
spaces, so Stacks 02YS applies. -/
theorem isAlgebraicSpace_pullback_schemePointsMap_Spec_map {R R' : CommRingCat.{u}} (φ : R ⟶ R')
    (hφ : RingHom.FiniteType φ.hom) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (p : F ⟶ schemePoints B S hS (Spec R)) :
    IsAlgebraicSpace B S hS (pullback p (schemePointsMap B S hS (Spec.map φ))) := by
  exact AlgebraicGeometry.isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces B S hS
    (pullback.fst p (schemePointsMap B S hS (Spec.map φ)))
    (IsRepresentableByAlgebraicSpaces.of_relativelyRepresentable
      (presheaf_isAffineHom_pullback_fst_schemePointsMap_Spec_map B S hS φ hφ p).rep)
    hF

/-- **The base change of an algebraic space along the spectrum of a ring map of finite
presentation is of finite presentation over it.** The chart condition is the base change of the
chart condition; quasi-compactness and quasi-separatedness come from affineness, both the base
change and the algebraic space being algebraic spaces. -/
theorem isFinitePresentation_pullback_fst_schemePointsMap_Spec_map {R R' : CommRingCat.{u}}
    (φ : R ⟶ R') (hφ : RingHom.FinitePresentation φ.hom)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (p : F ⟶ schemePoints B S hS (Spec R)) :
    IsFinitePresentation B S hS (pullback.fst p (schemePointsMap B S hS (Spec.map φ))) := by
  have hft := RingHom.FiniteType.of_finitePresentation hφ
  have hPB := isAlgebraicSpace_pullback_schemePointsMap_Spec_map B S hS φ hft hF p
  have haff := isAffineHom_pullback_fst_schemePointsMap_Spec_map B S hS φ hft p
  exact ⟨isLocallyOfFinitePresentation_pullback_fst_schemePointsMap_Spec_map B S hS φ hφ p,
    isQuasiCompact_of_isAffineHom' B S hS _ hPB hF haff,
    isQuasiSeparated_of_isAffineHom B S hS _ hPB hF haff⟩

/-! ### An étale chart of a quasi-separated algebraic space -/

/-- **An étale chart of a quasi-separated algebraic space with quasi-compact quasi-separated
total scheme is of finite presentation.** Étale morphisms of schemes are locally of finite
presentation, so the chart condition is Stacks 03XP read on the atlas; quasi-compactness is
Stacks 073B, part (1), and quasi-separatedness is Stacks 073B, part (2), a quasi-separated
scheme being a quasi-separated algebraic space by Stacks 03JX. -/
theorem isFinitePresentation_etaleChart (hZ : B.Contains (⊤_ Scheme.{u}))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hFqs : IsAbsolutelyQuasiSeparated B S hS hZ F) {U : BigFppfOver B S hS}
    (hUqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj U))
    (hUqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U))
    {a : yoneda.obj U ⟶ F} (ha : IsEtale B S hS a) :
    IsFinitePresentation B S hS a :=
  ⟨isLocallyOfFinitePresentation_atlas B S hS hF ha,
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hF hFqs
      (isQuasiCompactSpace_yoneda B S hS U hUqc) a,
    isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ
      (isAlgebraicSpace_yoneda B S hS U)
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS (yoneda.obj U) hZ
        ⟨U, hUqs, ⟨Functor.RepresentableBy.yoneda U⟩⟩) a⟩

/-! ### The morphism descent system of Stacks 07SQ -/

namespace DescentSituation

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)

/-- **The morphism descent system of the proof of Stacks 07SQ.** Let `D` be a descent situation,
let `φ : R ⟶ R'` present `R'` as a finitely presented `R`-algebra, let
`p : X₀ ⟶ Spec R` be a morphism from the chosen stage of `D` to the functor of points of
`Spec R`, let `U` be an object of the site with quasi-compact quasi-separated total scheme and
`a : U ⟶ X₀` an étale chart of the stage, and let `f₀` be a morphism over the stage from that
chart to the base change `X₀ ×_{Spec R} Spec R'`. Then `f₀` is a morphism descent system in the
sense of Stacks 084W, so the descent results of
`AlgebraicGeometry.Space.MorphismDescentSystem` — Stacks 084S among them — apply to it.

With `R` a `u`-model of the ring of global functions of the stage, `R'` the presentation
`AlgebraicGeometry.Space.presentationAlgebra` and `p` the canonical morphism of
`AlgebraicGeometry.Space.exists_specMap_of_globalHom`, this is the situation of display
70.5.10.1 in the proof of Stacks 07SQ, read at the chosen stage. -/
noncomputable def morphismDescentSystemOfSpecMap (hI : #I < B.cutoff.ord.cof)
    {R R' : CommRingCat.{u}} (φ : R ⟶ R') (hφ : RingHom.FinitePresentation φ.hom)
    (p : D.system.obj (op D.base) ⟶ schemePoints B S hS (Spec R))
    {U : BigFppfOver B S hS}
    (hUqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj U))
    (hUqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U))
    {a : yoneda.obj U ⟶ D.system.obj (op D.base)} (ha : IsEtale B S hS a)
    (f₀ : Over.mk a ⟶ Over.mk (pullback.fst p (schemePointsMap B S hS (Spec.map φ)))) :
    MorphismDescentSystem B S hS hZ I :=
  D.morphismDescentSystem hI (Over.mk a)
    (Over.mk (pullback.fst p (schemePointsMap B S hS (Spec.map φ))))
    (isAlgebraicSpace_yoneda B S hS U)
    (isAlgebraicSpace_pullback_schemePointsMap_Spec_map B S hS φ
      (RingHom.FiniteType.of_finitePresentation hφ) (D.algebraicSpace D.base) p)
    (isFinitePresentation_etaleChart B S hS hZ (D.algebraicSpace D.base)
      (D.quasiSeparated D.base) hUqc hUqs ha)
    (isFinitePresentation_pullback_fst_schemePointsMap_Spec_map B S hS φ hφ
      (D.algebraicSpace D.base) p)
    f₀

/-- **The morphism descent system of display 70.5.10.1 of the proof of Stacks 07SQ.** This is
`AlgebraicGeometry.Space.DescentSituation.morphismDescentSystemOfSpecMap` at the spectrum of the
structure homomorphism of a presentation `A[x₁, …, xₙ]/(g₁, …, gₙ)`, which is of finite
presentation by `AlgebraicGeometry.Space.finitePresentation_presentationStructureHom`.

With `A` a `u`-model of the ring of global functions of the stage and `p` the canonical morphism
of `AlgebraicGeometry.Space.exists_specMap_of_globalHom`, the two verticals of the base change
are the left vertical and the bottom edge of the square of Stacks 084U. -/
noncomputable def morphismDescentSystemOfPresentation (hI : #I < B.cutoff.ord.cof)
    {A : Type u} [CommRing A] {n : ℕ} (g : Fin n → MvPolynomial (Fin n) A)
    (p : D.system.obj (op D.base) ⟶ schemePoints B S hS (Spec (CommRingCat.of A)))
    {U : BigFppfOver B S hS}
    (hUqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj U))
    (hUqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U))
    {a : yoneda.obj U ⟶ D.system.obj (op D.base)} (ha : IsEtale B S hS a)
    (f₀ : Over.mk a ⟶ Over.mk (pullback.fst p (schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g)))))) :
    MorphismDescentSystem B S hS hZ I :=
  D.morphismDescentSystemOfSpecMap hI (CommRingCat.ofHom (presentationStructureHom g))
    (finitePresentation_presentationStructureHom g) p hUqc hUqs ha f₀

/-- **The situation of Stacks 084W of the proof of Stacks 07SQ.** This is
`AlgebraicGeometry.Space.DescentSituation.morphismDescentSystemOfSpecMap` as a situation in the
sense of `AlgebraicGeometry.Space.MorphismDescentSituation`, which asks nothing of the size of
the index. -/
noncomputable def morphismDescentSituationOfSpecMap
    {R R' : CommRingCat.{u}} (φ : R ⟶ R') (hφ : RingHom.FinitePresentation φ.hom)
    (p : D.system.obj (op D.base) ⟶ schemePoints B S hS (Spec R))
    {U : BigFppfOver B S hS}
    (hUqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj U))
    (hUqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U))
    {a : yoneda.obj U ⟶ D.system.obj (op D.base)} (ha : IsEtale B S hS a)
    (f₀ : Over.mk a ⟶ Over.mk (pullback.fst p (schemePointsMap B S hS (Spec.map φ)))) :
    MorphismDescentSituation B S hS hZ I :=
  D.morphismDescentSituation (Over.mk a)
    (Over.mk (pullback.fst p (schemePointsMap B S hS (Spec.map φ))))
    (isAlgebraicSpace_yoneda B S hS U)
    (isAlgebraicSpace_pullback_schemePointsMap_Spec_map B S hS φ
      (RingHom.FiniteType.of_finitePresentation hφ) (D.algebraicSpace D.base) p)
    (isFinitePresentation_etaleChart B S hS hZ (D.algebraicSpace D.base)
      (D.quasiSeparated D.base) hUqc hUqs ha)
    (isFinitePresentation_pullback_fst_schemePointsMap_Spec_map B S hS φ hφ
      (D.algebraicSpace D.base) p)
    f₀

/-- **The situation of Stacks 084W of display 70.5.10.1 of the proof of Stacks 07SQ.** This is
`AlgebraicGeometry.Space.DescentSituation.morphismDescentSystemOfPresentation` as a situation in
the sense of `AlgebraicGeometry.Space.MorphismDescentSituation`, which asks nothing of the size
of the index. -/
noncomputable def morphismDescentSituationOfPresentation
    {A : Type u} [CommRing A] {n : ℕ} (g : Fin n → MvPolynomial (Fin n) A)
    (p : D.system.obj (op D.base) ⟶ schemePoints B S hS (Spec (CommRingCat.of A)))
    {U : BigFppfOver B S hS}
    (hUqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj U))
    (hUqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U))
    {a : yoneda.obj U ⟶ D.system.obj (op D.base)} (ha : IsEtale B S hS a)
    (f₀ : Over.mk a ⟶ Over.mk (pullback.fst p (schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom g)))))) :
    MorphismDescentSituation B S hS hZ I :=
  D.morphismDescentSituationOfSpecMap (CommRingCat.ofHom (presentationStructureHom g))
    (finitePresentation_presentationStructureHom g) p hUqc hUqs ha f₀

end DescentSituation

end AlgebraicGeometry.Space

end
