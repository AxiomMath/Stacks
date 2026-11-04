module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackCompositionCanonicalAgreement
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectColimitHeld
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional

/-!
# Full faithfulness in Stacks 0DKW, from Stacks 0DKV

In Situation 0DKU the comparison out of the colimit of the categories of `Yᵢ`-perfect objects is
full and faithful (clauses (4) and (5) of Stacks 0DKW,
`AlgebraicGeometry.Space.RelativeDescentSituation.RelativelyPerfectFullyFaithful`).  The source
reads this off Stacks 0DKV applied with the stage `i` as the chosen stage: the situation
reindexed at `i` is again a Situation 0DKU, and two `Yᵢ`-perfect objects are pseudo-coherent,
lie in `D_QCoh` (Stacks 08JL) and locally have finite Tor dimension over `Yᵢ`.  Both 0DKV
and 0DKW are stated for a situation whose limit is a limit of schemes on affine charts
(`AlgebraicGeometry.Space.RelativeDescentSituation.IsSchemeLimit`), and the reindexed situation
inherits this (`AlgebraicGeometry.Space.RelativeDescentSituation.IsSchemeLimitAtStages`,
internal, not yet proved here).

Stacks 0DKV is not yet proved here and is carried here as the labelled hypothesis
`AlgebraicGeometry.Space.RelativeDescentSituation.HomDescentOfPseudoCoherent`, in the elementary
form `HomDescent` of `RelativelyPerfectHomDescent.lean` at the canonical
pseudofunctoriality datum `AlgebraicGeometry.Space.DerivedPullbackComposition.canonical`.  The
statement of Stacks 0DKW reads morphisms through the comparison triangles of
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`; fullness compares the two through
`AlgebraicGeometry.Space.DerivedPullbackComposition.canonical_iso_eq_triangle_symm`.
Faithfulness needs no comparison: the map induced by a factorisation carries `Lg^*ψ` to `Lk^*ψ`
for any pseudofunctoriality datum.

Nothing here is registered.

## Main definitions

* `AlgebraicGeometry.Space.RelativeDescentSituation.atStage`: Situation 0DKU with the chosen
  stage moved to a later stage.
* `AlgebraicGeometry.Space.RelativeDescentSituation.HomDescentOfPseudoCoherent`: Stacks 0DKV,
  as a proposition (not yet proved here).
* `AlgebraicGeometry.Space.RelativeDescentSituation.IsSchemeLimitAtStages`: the reindexed
  situations are limits of schemes (internal, pending).

## Main results

* `AlgebraicGeometry.Space.RelativeDescentSituation.isStagePerfect_hyps`: a `Yᵢ`-perfect object
  satisfies the hypotheses of Stacks 0DKV at the stage `i`.
* `AlgebraicGeometry.Space.DerivedPullbackComposition.factorHom_pullbackMap` and
  `factorHom_eq_conjHom`: the maps on derived homomorphisms induced by a factorisation.
* `AlgebraicGeometry.Space.RelativeDescentSituation.relativelyPerfectFullyFaithful_of_homDescent`:
  clauses (4) and (5) of Stacks 0DKW from Stacks 0DKV.

## References

* [Stacks Project, Tag 0DKW](https://stacks.math.columbia.edu/tag/0DKW)
* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Tag 0DKU](https://stacks.math.columbia.edu/tag/0DKU)
* [Stacks Project, Tag 0DKN](https://stacks.math.columbia.edu/tag/0DKN)
* [Stacks Project, Tag 08JL](https://stacks.math.columbia.edu/tag/08JL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u v

namespace CategoryTheory.Functor

variable {C D₁ D₂ : Type*} [Category* C] [Category* D₁] [Category* D₂]

/-- Conjugation by `e : P₂ ≅ P₁ ⋙ L`, read through the components of the inverse comparison. -/
theorem conjHom_eq_symm_app_inv_comp {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂}
    (e : P₂ ≅ P₁ ⋙ L) (M N : C) (α : P₁.obj M ⟶ P₁.obj N) :
    conjHom e α = (e.symm.app M).inv ≫ L.map α ≫ (e.symm.app N).hom :=
  rfl

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The second half of `Y`-perfectness (Stacks 0DKN) along a flat morphism `f : X ⟶ Y` locally
of finite presentation: `E`, read in `D(f⁻¹𝒪_Y)` through restriction of scalars, locally has
finite Tor dimension.  Elaborated at a variable morphism, as
`AlgebraicGeometry.Space.RelativeDescentSituation.IsPerfectAlong` is. -/
abbrev HasLocallyFiniteTorDimensionAlong {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (E : derivedModules B S hS X) : Prop :=
  Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
    (canonicalSliceDerivedTensorProduct B S hS f) ((derivedScalarRestriction B S hS f).obj E)

/-- An object of `D(𝒪_X)` lies in `D_QCoh(𝒪_X)`: its cohomology sheaves are quasi-coherent. -/
abbrev IsInQuasicoherentDerived (X : AlgebraicSpaces B S hS) (E : derivedModules B S hS X) :
    Prop :=
  DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) E

namespace RelativeDescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I)

/-- A `Yᵢ`-perfect object is pseudo-coherent, lies in `D_QCoh` (Stacks 08JL), and locally has
finite Tor dimension over `Yᵢ`. -/
theorem isStagePerfect_hyps (i : D.LaterIndex) (E : derivedModules B S hS (D.stageSource i))
    (hE : D.IsStagePerfect i E) :
    IsPseudoCoherentObject E ∧ IsInQuasicoherentDerived (D.stageSource i) E ∧
      HasLocallyFiniteTorDimensionAlong (D.stageStructure i) E :=
  ⟨hE.1, derivedCategoryB_of_isPseudoCoherent_unconditional B S hS _ _ E hE.1, hE.2⟩

/-- **Situation 0DKU with the chosen stage moved to a later stage `i`.**  The inverse system and
its limit are unchanged, the flat finitely presented space over the new chosen stage is
`Xᵢ ⟶ Yᵢ`, and the base changes at the stages `j ≥ i` and at the limit are those of `D`, with
the transitions `f_{ji}` and the projection `fᵢ` as the projections to the new initial space.
It mirrors `AlgebraicGeometry.Space.RelativeDescentSituation.reindex`, to be deduplicated
against it. -/
abbrev atStage (i : D.LaterIndex) : RelativeDescentSituation B S hS hZ I where
  Y := D.Y
  limitCone := D.limitCone
  isLimit := D.isLimit
  stage_isAlgebraicSpace := D.stage_isAlgebraicSpace
  limit_isAlgebraicSpace := D.limit_isAlgebraicSpace
  stage_isQuasiCompact := D.stage_isQuasiCompact
  stage_isQuasiSeparated := D.stage_isQuasiSeparated
  transition_isAffine := D.transition_isAffine
  i₀ := i.1
  X₀ := D.Xᵢ i.1 i.2
  p₀ := D.toYᵢ i.1 i.2
  initial_isAlgebraicSpace := D.stageX_isAlgebraicSpace i.1 i.2
  initial_isFlat := D.isFlat_stageStructure i
  initial_isFinitePresentation :=
    (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
      (D.isPullback_stageStructure i).flip D.initial_isFinitePresentation
  Xᵢ j hj := D.Xᵢ j (i.2.trans hj)
  stageX_isAlgebraicSpace j _hj := D.stageX_isAlgebraicSpace j _
  toX₀ j hj := D.fᵢⱼ i.1 j i.2 _ hj
  toYᵢ j _hj := D.toYᵢ j _
  stage_isPullback j hj :=
    ((D.isPullback_sourceTransition (j := ⟨j, i.2.trans hj⟩) hj).map
      (ObjectProperty.ι _)).flip
  fᵢⱼ j k _hj _hk hjk := D.fᵢⱼ j k _ _ hjk
  fᵢⱼ_toYᵢ j k _hj _hk hjk := D.fᵢⱼ_toYᵢ j k _ _ hjk
  fᵢⱼ_toX₀ _j _k hj _hk hjk := D.transition_comp_transition i.2 _ _ hj hjk
  X := D.X
  X_isAlgebraicSpace := D.X_isAlgebraicSpace
  toInitial := D.fᵢ i.1 i.2
  toLimit := D.toLimit
  limit_isPullback := ((D.isPullback_sourceProjection i).map (ObjectProperty.ι _)).flip
  fᵢ j _hj := D.fᵢ j _
  fᵢ_toYᵢ j _hj := D.fᵢ_toYᵢ j _
  fᵢ_toX₀ _j hj := D.projection_comp_transition i.2 _ hj

/-- **The limit of the situation reindexed at a later stage is again a limit of schemes on
affine charts** (internal, pending).  It mirrors
`AlgebraicGeometry.Space.RelativeDescentSituation.isSchemeLimit_reindex`, stated for
`reindex`, which is `atStage` field by field; to be discharged by it. -/
def IsSchemeLimitAtStages : Prop :=
  D.IsSchemeLimit → ∀ i : D.LaterIndex, (D.atStage i).IsSchemeLimit

variable (B S hS hZ I) in
/-- **Stacks 0DKV, not yet proved here.**  In Situation 0DKU, whose limit is a limit of
schemes on affine charts (`AlgebraicGeometry.Space.RelativeDescentSituation.IsSchemeLimit`, the
source's setting; without it the statement fails), let `K₀` and `L₀` be objects of
`D(𝒪_{X₀})`, with `K₀` pseudo-coherent and `L₀` in `D_QCoh(𝒪_{X₀})` locally of finite Tor
dimension as an object of `D((X₀ ⟶ Y₀)⁻¹𝒪_{Y₀})`.  Then
`colim_{i ≥ 0} Hom_{D(𝒪_{Xᵢ})}(Kᵢ, Lᵢ) ⟶ Hom_{D(𝒪_X)}(K, L)` is bijective, in the elementary
form `AlgebraicGeometry.Space.RelativeDescentSituation.HomDescent` of
`RelativelyPerfectHomDescent.lean`, read with the canonical pseudofunctoriality datum
`AlgebraicGeometry.Space.DerivedPullbackComposition.canonical`. -/
def HomDescentOfPseudoCoherent : Prop :=
  ∀ D : RelativeDescentSituation B S hS hZ I, D.IsSchemeLimit →
    ∀ K₀ L₀ : derivedModules B S hS D.initialSource,
      IsPseudoCoherentObject K₀ → IsInQuasicoherentDerived D.initialSource L₀ →
        HasLocallyFiniteTorDimensionAlong D.initialStructure L₀ →
          D.HomDescent (DerivedPullbackComposition.canonical B S hS) K₀ L₀

end RelativeDescentSituation

namespace DerivedPullbackComposition

variable (P : DerivedPullbackComposition B S hS) {X Y Z : AlgebraicSpaces B S hS}

/-- `AlgebraicGeometry.Space.DerivedPullbackComposition.factorHom` written out. -/
theorem factorHom_eq_comp (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (χ : (smallEtaleDerivedModulePullback B S hS g).obj K ⟶
      (smallEtaleDerivedModulePullback B S hS g).obj L) :
    P.factorHom f g k h K L χ = ((P.iso f g k h).app K).inv ≫
      (smallEtaleDerivedModulePullback B S hS f).map χ ≫ ((P.iso f g k h).app L).hom :=
  rfl

/-- The map on derived homomorphisms induced by a factorisation `f ≫ g = k` carries `Lg^*ψ` to
`Lk^*ψ`, by naturality of the identification `Lg^* ⋙ Lf^* ≅ Lk^*`. -/
theorem factorHom_pullbackMap (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    {K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))}
    (ψ : K ⟶ L) :
    P.factorHom f g k h K L ((smallEtaleDerivedModulePullback B S hS g).map ψ) =
      (smallEtaleDerivedModulePullback B S hS k).map ψ :=
  (P.factorHom_eq_comp f g k h K L _).trans
    ((Iso.inv_comp_eq ((P.iso f g k h).app K)).2 ((P.iso f g k h).hom.naturality ψ))

/-- When the identification attached to a factorisation is the inverse of the comparison
triangle of `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`, the induced map on derived
homomorphisms is conjugation by that triangle. -/
theorem factorHom_eq_conjHom (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (hP : P.iso f g k h = ((smallEtaleDerivedPullbackData B S hS).triangle h).symm)
    (K L : derivedModules B S hS Z)
    (χ : ((smallEtaleDerivedPullbackData B S hS).pull g).obj K ⟶
      ((smallEtaleDerivedPullbackData B S hS).pull g).obj L) :
    P.factorHom f g k h K L χ =
      Functor.conjHom ((smallEtaleDerivedPullbackData B S hS).triangle h) χ := by
  refine (P.factorHom_eq_comp f g k h K L χ).trans ?_
  rw [hP]
  exact Functor.conjHom_eq_symm_app_inv_comp _ K L χ |>.symm

end DerivedPullbackComposition

namespace RelativeDescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I)

/-- Stacks 0DKV at the stage `i` applies to two `Yᵢ`-perfect objects. -/
private theorem homDescent_atStage_of_isStagePerfect
    (h0DKV : HomDescentOfPseudoCoherent B S hS hZ I) (hstages : D.IsSchemeLimitAtStages)
    (hD : D.IsSchemeLimit) (i : D.LaterIndex) {E E' : derivedModules B S hS (D.stageSource i)}
    (hE : D.IsStagePerfect i E) (hE' : D.IsStagePerfect i E') :
    (D.atStage i).HomDescent (DerivedPullbackComposition.canonical B S hS) E E' := by
  obtain ⟨hK, -, -⟩ := D.isStagePerfect_hyps i E hE
  obtain ⟨-, hL, hL'⟩ := D.isStagePerfect_hyps i E' hE'
  exact h0DKV (D.atStage i) (hstages hD i) E E' hK hL hL'

/-- **Fullness and faithfulness in Stacks 0DKW (clauses (4) and (5)), from Stacks 0DKV**
(`h0DKV`, not yet proved here) applied to the situation reindexed at the stage `i`, the two
`Yᵢ`-perfect objects being pseudo-coherent, in `D_QCoh` (Stacks 08JL) and locally of finite Tor
dimension over `Yᵢ`; the reindexed situation is a limit of schemes by `hstages` (internal,
not yet proved here).  Fullness reads the canonical datum's maps to the
limit through the comparison triangles of the statement
(`AlgebraicGeometry.Space.DerivedPullbackComposition.canonical_iso_eq_triangle_symm`). -/
theorem relativelyPerfectFullyFaithful_of_homDescent
    (h0DKV : HomDescentOfPseudoCoherent B S hS hZ I) (hstages : D.IsSchemeLimitAtStages) :
    D.RelativelyPerfectFullyFaithful := by
  intro hD
  refine ⟨fun i E E' hE hE' φ => ?_, fun i E E' hE hE' ψ ψ' hψ => ?_⟩
  · obtain ⟨j, χ, hχ⟩ := (D.homDescent_atStage_of_isStagePerfect h0DKV hstages hD i hE hE').1 φ
    refine ⟨⟨j.1, i.2.trans j.2⟩, j.2, χ, ?_⟩
    rw [← hχ]
    exact (DerivedPullbackComposition.canonical B S hS).factorHom_eq_conjHom _ _ _ _
      (DerivedPullbackComposition.canonical_iso_eq_triangle_symm _ _ _ _) E E' χ
  · have pm := @DerivedPullbackComposition.factorHom_pullbackMap B S hS
      (DerivedPullbackComposition.canonical B S hS)
    obtain ⟨j, hij, hj⟩ := (D.homDescent_atStage_of_isStagePerfect h0DKV hstages hD i hE hE').2
      ⟨i.1, le_refl _⟩
      ((smallEtaleDerivedModulePullback B S hS
        ((D.atStage i).stageToInitial ⟨i.1, le_refl _⟩)).map ψ)
      ((smallEtaleDerivedModulePullback B S hS
        ((D.atStage i).stageToInitial ⟨i.1, le_refl _⟩)).map ψ')
      ((pm _ _ _ _ ψ).trans (hψ.trans (pm _ _ _ _ ψ').symm))
    exact ⟨⟨j.1, i.2.trans j.2⟩, j.2,
      (pm _ _ _ _ ψ).symm.trans (hj.trans (pm _ _ _ _ ψ'))⟩

end RelativeDescentSituation

end AlgebraicGeometry.Space

end
