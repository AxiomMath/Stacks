module

public import StacksFrontier.AlgebraicGeometry.Quot.StableModelExistence.Acyclic
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.SpecialFibreIso.Injectivity
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SurjectivityAfterBaseChange
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.VanishingNeighbourhood
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ContractExceptionalComponentCohomology
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ModelSituation
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelMappingProperty
public import StacksFrontier.AlgebraicGeometry.F6Rank136.AtWorstNodalRelativeDimensionOne

/-!
# The special fibre of a sequence of contractions of exceptional curves

Let `R` be a discrete valuation ring with fraction field `K` and residue field `κ`, and let
`Y = Yₙ → Yₙ₋₁ → ⋯ → Y₀` be a sequence of contractions of exceptional curves of the first kind
between regular proper models of a smooth projective curve `C` over `K`. This file proves the
step of the proof of [Stacks, Tag 0E97] which says that the induced morphism of special fibres
`Y_κ ⟶ Y₀,κ` satisfies `𝒪 = c_*𝒪` and `Rⁱc_*𝒪 = 0` for `i > 0`.

The source's argument, for one contraction `b : Y_{i+1} ⟶ Y_i` with special fibre
`c : Y_{i+1,κ} ⟶ Y_{i,κ}`:

* `b` is the blowup of a regular point of dimension two, so `𝒪 = b_*𝒪` and `R¹b_*𝒪 = 0`
  ([Stacks, Tag 0AGS]; `AlgebraicGeometry.IsContractionOfExceptionalCurve.isIso_c` and
  `AlgebraicGeometry.IsContractionOfExceptionalCurve.isZero_rightDerived_pushforward_unit`);
* the fibres of `b` have dimension at most one, hence `H¹` of the structure sheaf of every fibre
  vanishes ([Stacks, Tag 0E7F]), so `R¹` of the structure sheaf vanishes after every base change
  near every point ([Stacks, Tag 0E7G]), which gives `R¹c_*𝒪 = 0`, and `𝒪 ⟶ c_*𝒪` is surjective
  ([Stacks, Tag 0E7I]);
* `𝒪 ⟶ c_*𝒪` is injective: a function vanishing on the special fibre of `Y_{i+1}` is divisible
  by the uniformizer, `Y_{i+1}` being flat over `R`
  (`Stacks.Models.RegularProperModelSituation.mono_unitToPushforwardUnit_specialFiberMap`; the
  source argues with the reducedness of `Y_{i,κ}` instead);
* `Rⁱc_*𝒪 = 0` for `i ≥ 2` because the fibres of `c` are curves ([Stacks, Tag 0E7D]).

The sequence is then handled by induction, composing along it
(`AlgebraicGeometry.ContractionUniquenessComplete.isStructurallyAcyclic_specialMap_comp`).

## Main results

* `Stacks.Models.RegularProperModelSituation.isStructurallyAcyclic_specialFiberMap`: for a
  proper morphism `c` out of a regular proper model with `𝒪 = c_*𝒪` and `R¹c_*𝒪 = 0`, the special
  fibre of `c` is structurally acyclic.
* `Stacks.Models.isStructurallyAcyclic_specialMap_of_isContractionOfExceptionalCurve`: one
  contraction.
* `Stacks.Models.ExceptionalContractionSequence.acyc_specialMap`: a sequence of contractions.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.TopDegreeBaseChange Stacks.Models.SpecialFibreIso

universe u

namespace Stacks.Models

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **Structural acyclicity descends to the special fibre.** Let `c : X ⟶ Y` be a proper morphism
over `Spec R` out of a regular proper model with `𝒪_Y = c_*𝒪_X` and `R¹c_*𝒪_X = 0`. Then the
special fibre `c_κ : X_κ ⟶ Y_κ` has `𝒪_{Y_κ} = c_{κ*}𝒪_{X_κ}` and `Rⁱc_{κ*}𝒪_{X_κ} = 0` for
`i > 0`.

The fibres of `c` lie in the fibres of `X ⟶ Spec R`, so have dimension at most one, and their
first cohomology vanishes ([Stacks, Tag 0E7F]). Surjectivity of `𝒪 ⟶ c_κ*𝒪` is
[Stacks, Tag 0E7I], injectivity holds as `X` is flat over `R`, `R¹c_κ*𝒪 = 0` is
[Stacks, Tag 0E7G] at every point of `Y_κ`, and the higher `Rⁱ` vanish because the fibres of `c_κ`
lie in the curve `X_κ` ([Stacks, Tag 0E7D]). -/
theorem isStructurallyAcyclic_specialFiberMap {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of S.R))
    (c : S.X ⟶ Y) (hc : c ≫ pY = S.X_to_R) [IsProper c]
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    (hR : IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
      (SheafOfModules.unit S.X.ringCatSheaf))) :
    (S.specialFiberMap pY c hc).IsStructurallyAcyclic := by
  set j := pullback.fst pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))
  set cs := S.specialFiberMap pY c hc
  have sq : IsPullback S.specialFiberι cs c j :=
    isPullback_pullbackMap _ _ _ hc _ (by rw [Category.comp_id, hc]) (by simp)
  have hdim := S.topologicalKrullDim_fiber_le_one pY c hc
  have hfib : ∀ y : Y, IsZero (firstCohomologyStructureSheaf (c.fiber y)) := fun y =>
    isZero_firstCohomologyStructureSheaf_fiber_of_isZero_firstDirectImage c y (hdim y)
      ((isZero_firstDirectImageStructureSheaf_iff c).2 hR)
  -- `𝒪_{Y_κ} ⟶ c_κ*𝒪_{X_κ}` is an isomorphism
  have : IsIso (C := Y.Modules) (Scheme.Modules.unitToPushforwardUnit c) := hO
  have hepi : Epi (Scheme.Modules.unitToPushforwardUnit cs) := by
    rw [← sq.isoPullback_hom_snd]
    exact epi_unitToPushforwardUnit_iso_comp _ _
      (epi_unitToPushforwardUnit_of_baseChange c hdim hfib inferInstance j)
  have hmono : Mono (Scheme.Modules.unitToPushforwardUnit cs) :=
    S.mono_unitToPushforwardUnit_specialFiberMap pY c hc hO
  have hiso : IsIso (Scheme.Modules.unitToPushforwardUnit cs) := isIso_of_mono_of_epi _
  -- the special fibre is proper, with fibres of dimension at most one
  have : IsProper cs := MorphismProperty.of_isPullback sq ‹IsProper c›
  have hdims : ∀ y, topologicalKrullDim (cs.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) := fun y =>
    ((cs.fiberι y).isEmbedding.isInducing.topologicalKrullDim_le).trans
      (S.toRegularModelSituation.topologicalKrullDim_specialFiber S.nonempty_specialFiber).le
  -- `R¹c_κ*𝒪 = 0`, stalk by stalk
  have h1 : IsZero (firstDirectImageStructureSheaf cs) := by
    refine isZero_of_forall_isZero_stalk _ fun y => ?_
    obtain ⟨V, hyV, -, huniv⟩ :=
      exists_isOpen_isZero_restrict_firstDirectImage_of_isPullback_of_isZero_cohomologyOne_fiber
        c (j y) (hdim _) (hfib _)
    let W := j ⁻¹ᵁ V
    have hsq : IsPullback ((cs ⁻¹ᵁ W).ι ≫ S.specialFiberι) (cs ∣_ W) c (W.ι ≫ j) :=
      (isPullback_morphismRestrict cs W).flip.paste_horiz sq
    have hz := huniv hsq (by rintro _ ⟨w, rfl⟩; exact w.2)
    exact
      AlgebraicGeometry.SchemeHigherDirectImage.isZero_stalk_of_isZero_rightDerivedPlus_restrict
        cs W y hyV _ (p := 1) zero_le_one (IsZero.of_iso hz (Functor.mapIso _
          ((Scheme.Modules.restrictFunctorIsoPullback (cs ⁻¹ᵁ W).ι).app _ ≪≫
            Scheme.Modules.pullbackUnitIso (cs ⁻¹ᵁ W).ι)))
  exact Scheme.Hom.isStructurallyAcyclic_of_isZero_rightDerived_one cs hdims hiso
    ((isZero_firstDirectImageStructureSheaf_iff cs).1 h1)

end RegularProperModelSituation

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The special fibre of the contraction of an exceptional curve is structurally acyclic.** Let
`b : Y ⟶ Y'` be a contraction of an exceptional curve of the first kind over `Spec R`, with `Y` a
regular proper model of `C` and `Y'` proper over `R`. Then `b_κ : Y_κ ⟶ Y'_κ` has
`𝒪 = b_κ*𝒪` and `Rⁱb_κ*𝒪 = 0` for `i > 0`. -/
theorem isStructurallyAcyclic_specialMap_of_isContractionOfExceptionalCurve
    {C Y Y' : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c]
    (hproj : Stacks.HProjective.IsHProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] (q : Y ⟶ Spec (.of R))
    (eY : C ≅ pullback q (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hmod : IsModel c q eY) [IsProper q] (hreg : IsRegular Y) {p' : Y' ⟶ Spec (.of R)}
    [IsProper p'] {D : Y.IdealSheafData} {b : Y ⟶ Y'} (hb : IsContractionOfExceptionalCurve D b)
    (hbp : b ≫ p' = q) :
    (ContractionUniquenessComplete.specialMap q p' b hbp).IsStructurallyAcyclic := by
  have : IsProper (b ≫ p') := by
    rw [hbp]
    infer_instance
  have : IsProper b := IsProper.of_comp b p'
  have hO : IsIso (SheafOfModules.unitToPushforwardObjUnit b.toRingCatSheafHom) :=
    (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_unitToPushforwardObjUnit
      b).1 hb.isIso_c
  let S := regularProperModelSituation c hproj q eY hmod hreg
  have : IsProper (show S.X ⟶ Y' from b) := ‹IsProper b›
  exact S.isStructurallyAcyclic_specialFiberMap p' b hbp hO
    (hb.isZero_rightDerived_pushforward_unit 1 le_rfl)

/-- The induction behind `Stacks.Models.ExceptionalContractionSequence.acyc_specialMap`, with the
hypotheses on the source after the sequence. -/
theorem ExceptionalContractionSequence.acyc_specialMap_aux {C X Y : Scheme.{u}}
    {c : C ⟶ Spec (.of K)} [IsCurve K c] [Smooth c] (hproj : Stacks.HProjective.IsHProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] {q : Y ⟶ Spec (.of R)}
    {p : X ⟶ Spec (.of R)} {g : Y ⟶ X} (hs : ExceptionalContractionSequence c q p g) :
    ∀ (eY : C ≅ pullback q (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      IsModel c q eY → IsProper q → IsRegular Y →
      (ContractionUniquenessComplete.specialMap q p g
        (comp_eq_of_exceptionalContractionSequence hs)).IsStructurallyAcyclic := by
  induction hs with
  | refl p => exact fun _ _ _ _ => Scheme.Hom.isStructurallyAcyclic_of_isIso _
  | @step X X' Y p p' q g b D k _ eE hE hb hbp e' hmod' hproper' hreg' rest ih =>
    intro eY hmod hprop hreg
    have := hprop
    have := hproper'
    have := ContractionUniquenessComplete.isProper_specialMap p p' b hbp
    have : CompactSpace ↥(pullback p' (ContractionUniquenessComplete.closedPoint R)) :=
      QuasiCompact.compactSpace_of_compactSpace
        (pullback.snd p' (ContractionUniquenessComplete.closedPoint R))
    exact ContractionUniquenessComplete.isStructurallyAcyclic_specialMap_comp p p' q b g hbp
      (comp_eq_of_exceptionalContractionSequence rest)
      (isStructurallyAcyclic_specialMap_of_isContractionOfExceptionalCurve c hproj p eY hmod hreg
        hb hbp)
      (ih e' hmod' hproper' hreg')

/-- **[Stacks, Tag 0E97], the contractions of exceptional curves.** Let `Y = Yₙ → ⋯ → Y₀ = X` be a
sequence of contractions of exceptional curves of the first kind between regular proper models of
`C`, with composite `g`. Then the special fibre `g_κ : Y_κ ⟶ X_κ` has `𝒪 = g_κ*𝒪` and
`Rⁱg_κ*𝒪 = 0` for `i > 0`. -/
theorem ExceptionalContractionSequence.acyc_specialMap {C X Y : Scheme.{u}}
    {c : C ⟶ Spec (.of K)} [IsCurve K c] [Smooth c] {q : Y ⟶ Spec (.of R)}
    {p : X ⟶ Spec (.of R)} {g : Y ⟶ X} (hs : ExceptionalContractionSequence c q p g)
    [IsProper q] (_hnod : IsAtWorstNodalOfRelativeDimensionOne q)
    (hproj : Stacks.HProjective.IsHProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)]
    (eY : C ≅ pullback q (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hmod : IsModel c q eY) (hreg : IsRegular Y) :
    (ContractionUniquenessComplete.specialMap q p g
      (comp_eq_of_exceptionalContractionSequence hs)).IsStructurallyAcyclic :=
  hs.acyc_specialMap_aux hproj eY hmod inferInstance hreg

end Stacks.Models

end
