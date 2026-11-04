module

public import StacksFrontier.AlgebraicGeometry.DeRham.FormsDirectImageBaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupEtaleChartTransfer
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsGlobalSections
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.IsomorphismLimit
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Corner
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsExtension
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateExceptionalFormsDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateExceptionalProjectiveBundle
import StacksCore.Tactic.StacksAttribute

/-!
# Blowing up a smooth centre: direct images of differential forms

Let `f : X ⟶ S` be smooth, let `i : Z ⟶ X` be a closed immersion with `Z` smooth over `S`, and let
`b : X' ⟶ X` be the blowing up of `X` along `Z`.  This file carries the étale-local reduction of
[Stacks, Tag 0FUU] to the coordinate model of Section 50.16, following the source's proof.  The
charts are `Stacks.DeRham.BlowupEtaleChart`, which come from [Stacks, Tag 0FUE].  Invertibility of
a map of modules is local on the target.  On a chart the situation is the étale base change of
the coordinate model, so the comparison maps transfer by
`Stacks.DeRham.isIso_formsDirectImageComparison_of_isPullback`.  Off the centre the blowing-up
morphism is an isomorphism.

## Main results

* `Stacks.DeRham.BlowupEtaleChart.isIso_formsDirectImageComparison_restrict`: clause (1) on a
  chart, from clause (1) for the coordinate model.
* `Stacks.DeRham.isIso_formsDirectImageComparison_blowUpToBase_of_coordinate`: clause (1) for a
  centre with empty interior, from clause (1) of [Stacks, Tag 0FUR] for every coordinate model
  with `1 ≤ n`.
* `Stacks.DeRham.isIso_formsDirectImageComparison_blowUpToBase`: **[Stacks, Tag 0FUU], clause
  (1)**, corrected: for a centre with empty interior.
* `Stacks.DeRham.BlowupEtaleChart.isPullback_exceptionalOverCentreMap`: on a chart, the part of
  the exceptional divisor over the centre is the base change of the coordinate exceptional
  divisor.
* `Stacks.DeRham.isIso_formsDirectImageComparison_exceptionalDivisorToCentre`: **[Stacks, Tag
  0FUU], clause (2)**, corrected: for a centre with empty interior.

## The correction

Clauses (1) and (2) are false as stated when the centre contains a non-empty open subset of `X`.
The counterexample is
`Stacks.DeRham.exists_smooth_not_isIso_formsDirectImageComparison_blowUpToBase` in
`StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsDirectImageCodimensionZero`.  Both clauses are
proved under the hypothesis `interior (Set.range i.base) = ∅`.  Clause (3) needs no correction.

## References

* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 0FUE](https://stacks.math.columbia.edu/tag/0FUE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom

universe u

namespace Stacks.DeRham

variable {S X Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}

/-- **The exceptional divisor is the inverse image of the centre**: the square formed by the
inclusion of the exceptional divisor, its structure morphism to the centre, the blowing-up
morphism and `i` is cartesian. -/
@[sga "6 0 6.Lemma3" "cartesian square of j", sga "6 VII 3.7" "more general"]
theorem isPullback_exceptionalDivisorToCentre (i : Z ⟶ X) [IsClosedImmersion i] :
    IsPullback (exceptionalIdeal i.ker).subschemeι (exceptionalDivisorToCentre i)
      (blowUpToBase i.ker) i :=
  AlgebraicGeometry.isPullback_of_isClosedImmersion _ _ _ _
    (exceptionalDivisorToCentre_comp i).symm
    (by rw [Scheme.IdealSheafData.ker_subschemeι])

attribute [local instance] Stacks.MoreMorphisms.coordinateEmbedding_isClosedImmersion

/-- The structure morphism of the exceptional divisor of the coordinate blowup to its centre is
quasi-compact. -/
instance quasiCompact_exceptionalDivisorToCentre_coordinate (R : Type u) [CommRing R] (m n : ℕ) :
    QuasiCompact (exceptionalDivisorToCentre (Stacks.MoreMorphisms.coordinateEmbedding R m n)) :=
  MorphismProperty.of_isPullback (P := @QuasiCompact)
    (isPullback_exceptionalDivisorToCentre (Stacks.MoreMorphisms.coordinateEmbedding R m n))
    (quasiCompact_coordinateBlowupToAmbient R m n)

/-- The structure morphism of the exceptional divisor of the coordinate blowup to its centre is
quasi-separated. -/
instance quasiSeparated_exceptionalDivisorToCentre_coordinate (R : Type u) [CommRing R]
    (m n : ℕ) :
    QuasiSeparated (exceptionalDivisorToCentre (Stacks.MoreMorphisms.coordinateEmbedding R m n)) :=
  MorphismProperty.of_isPullback (P := @QuasiSeparated)
    (isPullback_exceptionalDivisorToCentre (Stacks.MoreMorphisms.coordinateEmbedding R m n))
    (quasiSeparated_coordinateBlowupToAmbient R m n)

namespace BlowupEtaleChart

variable (c : BlowupEtaleChart f i)

attribute [local instance] BlowupEtaleChart.commRing BlowupEtaleChart.etale
  BlowupEtaleChart.isOpenImmersion_base

/-- **Clause (1) on a chart.**  If the comparison map `Ω^a ⟶ b_*Ω^a` of the coordinate model is
invertible, so is that of the blowup restricted over the chart.  It is first transferred along the
étale chart map, as forms over `Spec R`, and then the base is changed to `S` along the open
immersion `Spec R ⟶ S`. -/
theorem isIso_formsDirectImageComparison_restrict (a : ℕ)
    (hcoord : IsIso (formsDirectImageComparison (coordinateBlowupToAmbient c.R c.m c.n)
      (coordinateAmbientToBase c.R c.m c.n) (a : ℤ))) :
    IsIso (formsDirectImageComparison (blowUpToBase i.ker ∣_ c.U) (c.U.ι ≫ f) (a : ℤ)) := by
  have hs : c.g ≫ coordinateAmbientToBase c.R c.m c.n =
      (c.g ≫ coordinateAmbientToBase c.R c.m c.n) ≫ 𝟙 _ := by simp
  have : IsIso (relativeDifferentialFormsMap c.g (coordinateAmbientToBase c.R c.m c.n)
      (c.g ≫ coordinateAmbientToBase c.R c.m c.n) (𝟙 _) hs (a : ℤ)) :=
    isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ _
  have : IsIso (relativeDifferentialFormsMap c.blowupMap
      (coordinateBlowupToAmbient c.R c.m c.n ≫ coordinateAmbientToBase c.R c.m c.n)
      ((blowUpToBase i.ker ∣_ c.U) ≫ c.g ≫ coordinateAmbientToBase c.R c.m c.n) (𝟙 _)
      (forms_square_comm_aux _ _ _ _ c.isPullback_blowupMap.flip.w _ _ _ hs) (a : ℤ)) :=
    isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ _
  have hR := isIso_formsDirectImageComparison_of_isPullback
    (coordinateAmbientToBase c.R c.m c.n) (c.g ≫ coordinateAmbientToBase c.R c.m c.n) (𝟙 _) hs
    c.isPullback_blowupMap.flip a hcoord
  have hs' : 𝟙 c.U.toScheme ≫ c.U.ι ≫ f =
      (c.g ≫ coordinateAmbientToBase c.R c.m c.n) ≫ c.base := by
    rw [Category.id_comp, Category.assoc, c.comm]
  have w : 𝟙 _ ≫ (blowUpToBase i.ker ∣_ c.U) = (blowUpToBase i.ker ∣_ c.U) ≫ 𝟙 _ := by simp
  have : IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app
      (relativeDifferentialForms ((blowUpToBase i.ker ∣_ c.U) ≫ c.U.ι ≫ f) (a : ℤ))) :=
    Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isIso w _
  have : IsIso (relativeDifferentialFormsMap (𝟙 c.U.toScheme) (c.U.ι ≫ f)
      (c.g ≫ coordinateAmbientToBase c.R c.m c.n) c.base hs' (a : ℤ)) :=
    isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ _
  have : IsIso (relativeDifferentialFormsMap (𝟙 _) ((blowUpToBase i.ker ∣_ c.U) ≫ c.U.ι ≫ f)
      ((blowUpToBase i.ker ∣_ c.U) ≫ c.g ≫ coordinateAmbientToBase c.R c.m c.n) c.base
      (forms_square_comm_aux _ _ _ _ w _ _ _ hs') (a : ℤ)) :=
    isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ _
  have h1 := (isIso_formsDirectImageComparison_of_baseChange (c.U.ι ≫ f)
    (c.g ≫ coordinateAmbientToBase c.R c.m c.n) c.base hs' w (a : ℤ)).2 hR
  exact (NatIso.isIso_map_iff (Scheme.Modules.pullbackId _) _).1 h1

/-- The part of the exceptional divisor over `i ⁻¹ᵁ c.U`, mapped to `X` through the blowup, agrees
with its map to `X` through the restricted centre `i ∣_ c.U`. -/
theorem exceptionalOverCentre_comm_aux [IsClosedImmersion i] :
    ((exceptionalDivisorToCentre i ⁻¹ᵁ (i ⁻¹ᵁ c.U)).ι ≫ (exceptionalIdeal i.ker).subschemeι) ≫
        blowUpToBase i.ker =
      ((exceptionalDivisorToCentre i ∣_ (i ⁻¹ᵁ c.U)) ≫ (i ∣_ c.U)) ≫ c.U.ι := by
  simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc]
  rw [exceptionalDivisorToCentre_comp]

/-- `blowupMap`, with its target written as the blowup of the kernel of the coordinate closed
immersion. -/
noncomputable def blowupMap' :
    (blowUpToBase i.ker ⁻¹ᵁ c.U).toScheme ⟶
      blowUp (Stacks.MoreMorphisms.coordinateEmbedding c.R c.m c.n).ker :=
  c.blowupMap

/-- The blowup restricted over the chart is the base change of the coordinate blowup along `c.g`,
with the chart map written as `blowupMap'`. -/
theorem isPullback_blowupMap' :
    IsPullback (blowUpToBase i.ker ∣_ c.U) c.blowupMap' c.g
      (blowUpToBase (Stacks.MoreMorphisms.coordinateEmbedding c.R c.m c.n).ker) :=
  c.isPullback_blowupMap

/-- On a chart, the part of the exceptional divisor over the centre of the chart, mapped to the
coordinate exceptional divisor. -/
noncomputable def exceptionalOverCentreMap [IsClosedImmersion i] :
    (exceptionalDivisorToCentre i ⁻¹ᵁ (i ⁻¹ᵁ c.U)).toScheme ⟶
      exceptionalDivisor (Stacks.MoreMorphisms.coordinateEmbedding c.R c.m c.n).ker :=
  have := Stacks.MoreMorphisms.coordinateEmbedding_isClosedImmersion c.R c.m c.n
  IsPullback.lift
    (isPullback_exceptionalDivisorToCentre (Stacks.MoreMorphisms.coordinateEmbedding c.R c.m c.n))
    ((isPullback_morphismRestrict (blowUpToBase i.ker) c.U).flip.lift
        ((exceptionalDivisorToCentre i ⁻¹ᵁ (i ⁻¹ᵁ c.U)).ι ≫ (exceptionalIdeal i.ker).subschemeι)
        ((exceptionalDivisorToCentre i ∣_ (i ⁻¹ᵁ c.U)) ≫ (i ∣_ c.U))
        c.exceptionalOverCentre_comm_aux ≫ c.blowupMap')
    ((exceptionalDivisorToCentre i ∣_ (i ⁻¹ᵁ c.U)) ≫ c.centreMap)
    (by
      rw [Category.assoc, ← c.isPullback_blowupMap'.w, ← Category.assoc, IsPullback.lift_snd,
        Category.assoc, Category.assoc, c.centreMap_comm])

/-- **On a chart, the exceptional divisor over the centre of the chart is the base change of the
coordinate exceptional divisor along `centreMap`.** -/
theorem isPullback_exceptionalOverCentreMap [IsClosedImmersion i] :
    IsPullback c.exceptionalOverCentreMap (exceptionalDivisorToCentre i ∣_ (i ⁻¹ᵁ c.U))
      (exceptionalDivisorToCentre (Stacks.MoreMorphisms.coordinateEmbedding c.R c.m c.n))
      c.centreMap := by
  have := Stacks.MoreMorphisms.coordinateEmbedding_isClosedImmersion c.R c.m c.n
  have S2 := (isPullback_morphismRestrict (blowUpToBase i.ker) c.U).flip
  have Q0 := IsPullback.paste_horiz
    (isPullback_morphismRestrict (exceptionalDivisorToCentre i) (i ⁻¹ᵁ c.U)).flip
    (isPullback_exceptionalDivisorToCentre i)
  have e1 : (exceptionalDivisorToCentre i ⁻¹ᵁ (i ⁻¹ᵁ c.U)).ι ≫ (exceptionalIdeal i.ker).subschemeι =
      S2.lift _ _ c.exceptionalOverCentre_comm_aux ≫ (blowUpToBase i.ker ⁻¹ᵁ c.U).ι :=
    (S2.lift_fst _ _ _).symm
  have e2 : (i ⁻¹ᵁ c.U).ι ≫ i = (i ∣_ c.U) ≫ c.U.ι := (morphismRestrict_ι i c.U).symm
  rw [e1, e2] at Q0
  have Q1 := Q0.of_right (S2.lift_snd _ _ _) S2
  have Q2 := Q1.paste_horiz c.isPullback_blowupMap'.flip
  have S6 := isPullback_exceptionalDivisorToCentre
    (Stacks.MoreMorphisms.coordinateEmbedding c.R c.m c.n)
  have e3 : S2.lift _ _ c.exceptionalOverCentre_comm_aux ≫ c.blowupMap' =
      c.exceptionalOverCentreMap ≫
        (exceptionalIdeal (Stacks.MoreMorphisms.coordinateEmbedding c.R c.m c.n).ker).subschemeι :=
    (S6.lift_fst _ _ _).symm
  have e4 : (i ∣_ c.U) ≫ c.g =
      c.centreMap ≫ Stacks.MoreMorphisms.coordinateEmbedding c.R c.m c.n :=
    c.centreMap_comm.symm
  rw [e3, e4] at Q2
  exact Q2.of_right (S6.lift_snd _ _ _) S6

/-- **Clause (2) on a chart.**  If the comparison map `Ω^a ⟶ p_*Ω^a` of the coordinate model is
invertible, so is that of the exceptional divisor restricted over the centre of the chart. -/
theorem isIso_formsDirectImageComparison_exceptionalDivisorToCentre_restrict
    [IsClosedImmersion i] (a : ℕ)
    (hcoord : IsIso (formsDirectImageComparison
      (exceptionalDivisorToCentre (Stacks.MoreMorphisms.coordinateEmbedding c.R c.m c.n))
      (Stacks.MoreMorphisms.coordinateEmbedding c.R c.m c.n ≫ coordinateAmbientToBase c.R c.m c.n)
      (a : ℤ))) :
    IsIso (formsDirectImageComparison (exceptionalDivisorToCentre i ∣_ (i ⁻¹ᵁ c.U))
      ((i ⁻¹ᵁ c.U).ι ≫ i ≫ f) (a : ℤ)) := by
  have := Stacks.MoreMorphisms.coordinateEmbedding_isClosedImmersion c.R c.m c.n
  have H := c.isPullback_exceptionalOverCentreMap
  have : Etale c.exceptionalOverCentreMap := MorphismProperty.of_isPullback H.flip inferInstance
  set q := Stacks.MoreMorphisms.coordinateEmbedding c.R c.m c.n ≫
    coordinateAmbientToBase c.R c.m c.n
  have hs : c.centreMap ≫ q = (c.centreMap ≫ q) ≫ 𝟙 _ := by simp
  have : IsIso (relativeDifferentialFormsMap c.centreMap q (c.centreMap ≫ q) (𝟙 _) hs (a : ℤ)) :=
    isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ _
  have : IsIso (relativeDifferentialFormsMap c.exceptionalOverCentreMap
      (exceptionalDivisorToCentre (Stacks.MoreMorphisms.coordinateEmbedding c.R c.m c.n) ≫ q)
      ((exceptionalDivisorToCentre i ∣_ (i ⁻¹ᵁ c.U)) ≫ c.centreMap ≫ q) (𝟙 _)
      (forms_square_comm_aux _ _ _ _ H.w _ _ _ hs) (a : ℤ)) :=
    isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ _
  have hR := isIso_formsDirectImageComparison_of_isPullback q (c.centreMap ≫ q) (𝟙 _) hs H a
    hcoord
  have hbase : (i ⁻¹ᵁ c.U).ι ≫ i ≫ f = (c.centreMap ≫ q) ≫ c.base := by
    rw [Category.assoc, Category.assoc, ← Category.assoc c.centreMap, c.centreMap_comm,
      Category.assoc, c.comm, ← Category.assoc (i ∣_ c.U), morphismRestrict_ι, Category.assoc]
  rw [hbase]
  exact isIso_formsDirectImageComparison_comp_etale _ _ _ _ hR

end BlowupEtaleChart

/-- Off the centre, the blowing-up morphism is an isomorphism. -/
theorem isIso_blowUpToBase_restrict_compl_range [IsClosedImmersion i] :
    IsIso (blowUpToBase i.ker ∣_
      (⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : X.Opens)) := by
  refine isIso_blowUpToBase_restrict_of_subset_compl_support i.ker _ ?_
  intro x hx
  have : (i.ker.support : Set X) = Set.range i.base := by
    rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
  rw [Set.mem_compl_iff, this]
  exact hx

/-- A morphism of modules that is invertible after pulling back to a neighbourhood of every point is
invertible. -/
private theorem isIso_of_forall_exists_isIso_pullback_ι {Y : Scheme.{u}} {M N : Y.Modules}
    (φ : M ⟶ N) (hloc : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
      IsIso ((Scheme.Modules.pullback V.ι).map φ)) : IsIso φ := by
  choose V hyV hV using hloc
  refine Scheme.Modules.isIso_of_isIso_pullback_ι V ?_ _ hV
  exact top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyV y⟩

/-- **Clause (1) of [Stacks, Tag 0FUU], reduced to the coordinate model.**  Let `f` be smooth and
let `i` be a closed immersion of a scheme smooth over `S` whose image has empty interior.  Suppose
the comparison `Ω^a_{X/S} ⟶ b_*Ω^a_{L/S}` is invertible for every coordinate model
`𝐀^m_R ⊆ 𝐀^{m+n}_R` with `1 ≤ n`.  Then `Ω^a_{X/S} ⟶ b_*Ω^a_{X'/S}` is invertible. -/
theorem isIso_formsDirectImageComparison_blowUpToBase_of_coordinate [IsClosedImmersion i]
    [Smooth f] [Smooth (i ≫ f)] (hint : interior (Set.range i.base) = ∅) (a : ℕ)
    (hcoord : ∀ (R : Type u) [CommRing R] (m n : ℕ), 1 ≤ n →
      IsIso (formsDirectImageComparison (coordinateBlowupToAmbient R m n)
        (coordinateAmbientToBase R m n) (a : ℤ))) :
    IsIso (formsDirectImageComparison (blowUpToBase i.ker) f (a : ℤ)) := by
  classical
  refine isIso_of_forall_exists_isIso_pullback_ι _ fun x => ?_
  by_cases hx : x ∈ Set.range i.base
  · obtain ⟨z, rfl⟩ := hx
    obtain ⟨c, hzc, -⟩ := exists_blowupEtaleChart f i z ⊤ trivial
    let _ := c.commRing
    exact ⟨c.U, hzc, isIso_pullback_ι_formsDirectImageComparison _ f c.U (a : ℤ)
      (c.isIso_formsDirectImageComparison_restrict a
        (hcoord c.R c.m c.n (c.one_le_n hint hzc)))⟩
  · let W : X.Opens :=
      ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    have := isIso_blowUpToBase_restrict_compl_range (i := i)
    exact ⟨W, hx, isIso_pullback_ι_formsDirectImageComparison _ f W (a : ℤ)
      (isIso_formsDirectImageComparison_of_isIso _ _ _)⟩

/-- **[Stacks, Tag 0FUU], clause (1), in corrected form.**  Let `f : X ⟶ S` be smooth, let
`i : Z ⟶ X` be a closed immersion with `Z` smooth over `S` and with image of empty interior in
`X`, and let `b : X' ⟶ X` be the blowing up of `X` along `Z`.  Then for every `a ≥ 0` the
canonical map `Ω^a_{X/S} ⟶ b_*Ω^a_{X'/S}` is an isomorphism.

The hypothesis on the interior is a correction of the source.  The source states the clause for
every closed immersion of schemes smooth over `S`, and it is false when `Z` contains a non-empty
open subset of `X`: for `S = X = Z = Spec k` the blowup is empty, and `𝒪_X ⟶ 0` is not an
isomorphism (`Stacks.DeRham.exists_smooth_not_isIso_formsDirectImage`).  The proof is the
source's: the étale-local reduction to the coordinate model ([Stacks, Tag 0FUE]), with clause (1)
of [Stacks, Tag 0FUR] there.  Empty interior is exactly what makes the codimension `n ≥ 1` on
every chart. -/
@[stacks 0FUU "corrected form, clause (1): Ω^a_{X/S} ⟶ b_*Ω^a_{X'/S} is an isomorphism for every \
a ≥ 0, for f smooth and i a closed immersion of a scheme smooth over S whose image has EMPTY \
INTERIOR in X. The interior hypothesis is a correction: as stated (any closed immersion of \
S-smooth schemes) the clause is false when Z contains a nonempty open of X — for S = X = Z = \
Spec k the blowup is empty and 𝒪_X ⟶ 0 is not an isomorphism (counterexample \
Stacks.DeRham.exists_smooth_not_isIso_formsDirectImage, untagged). The blowup is \
AlgebraicGeometry.blowUpToBase i.ker"]
theorem isIso_formsDirectImageComparison_blowUpToBase [IsClosedImmersion i] [Smooth f]
    [Smooth (i ≫ f)] (hint : interior (Set.range i.base) = ∅) (a : ℕ) :
    IsIso (formsDirectImageComparison (blowUpToBase i.ker) f (a : ℤ)) :=
  isIso_formsDirectImageComparison_blowUpToBase_of_coordinate hint a
    fun R _ m n hn => isIso_coordinateBlowupFormsDirectImage R m n hn a

/-- **[Stacks, Tag 0FUU], clause (2), in corrected form.**  Let `f : X ⟶ S` be smooth, let
`i : Z ⟶ X` be a closed immersion with `Z` smooth over `S` and with image of empty interior in
`X`, let `E` be the exceptional divisor of the blowing up of `X` along `Z`, and let `p : E ⟶ Z`
be its structure morphism.  Then for every `a ≥ 0` the canonical map
`Ω^a_{Z/S} ⟶ p_*Ω^a_{E/S}` is an isomorphism.

As in clause (1), the hypothesis on the interior corrects the source: for `S = X = Z = Spec k`
the exceptional divisor is empty and `𝒪_Z ⟶ 0` is not an isomorphism
(`Stacks.DeRham.exists_smooth_not_isIso_formsDirectImageComparison_blowUpToBase`).  The proof is
the étale-local reduction of the source to clause (2) of [Stacks, Tag 0FUR], on the exceptional
divisor of the coordinate model. -/
@[stacks 0FUU "corrected form, clause (2): Ω^a_{Z/S} ⟶ p_*Ω^a_{E/S} is an isomorphism for every \
a ≥ 0, for f smooth and i a closed immersion of a scheme smooth over S whose image has EMPTY \
INTERIOR in X; E is the exceptional divisor of AlgebraicGeometry.blowUpToBase i.ker and p is \
AlgebraicGeometry.exceptionalDivisorToCentre i. The interior hypothesis is a correction: as stated \
the clause is false when Z contains a nonempty open of X — for S = X = Z = Spec k, E is empty and \
𝒪_Z ⟶ 0 is not an isomorphism (counterexample \
Stacks.DeRham.exists_smooth_not_isIso_formsDirectImageComparison_blowUpToBase, untagged)"]
theorem isIso_formsDirectImageComparison_exceptionalDivisorToCentre [IsClosedImmersion i]
    [Smooth f] [Smooth (i ≫ f)] (hint : interior (Set.range i.base) = ∅) (a : ℕ) :
    IsIso (formsDirectImageComparison (exceptionalDivisorToCentre i) (i ≫ f) (a : ℤ)) := by
  refine isIso_of_forall_exists_isIso_pullback_ι _ fun z => ?_
  obtain ⟨c, hzc, -⟩ := exists_blowupEtaleChart f i z ⊤ trivial
  let _ := c.commRing
  exact ⟨i ⁻¹ᵁ c.U, hzc, isIso_pullback_ι_formsDirectImageComparison _ (i ≫ f) _ (a : ℤ)
    (c.isIso_formsDirectImageComparison_exceptionalDivisorToCentre_restrict a
      (isIso_coordinateExceptionalFormsDirectImage c.R c.m c.n (c.one_le_n hint hzc) a))⟩

end Stacks.DeRham
