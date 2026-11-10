module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsDerivedReduction
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreForms
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsDirectImageCodimensionZero
import StacksCore.Tactic.StacksAttribute

/-!
# Blowing up a smooth centre: the derived comparison of Stacks 0FUU clause (3)

Let `f : X ⟶ S` be smooth, let `i : Z ⟶ X` be a closed immersion with `Z` smooth over `S`, let
`b : X' ⟶ X` be the blowing up of `X` along `Z`, `j : E ⟶ X'` its exceptional divisor and
`p : E ⟶ Z` the structure morphism.  Clause (3) of [Stacks, Tag 0FUU] says that
`Rb_*Ω^a_{X'/S} ⟶ i_*Rp_*Ω^a_{E/S}` is an isomorphism on cohomology sheaves in degrees `≥ 1`.
This file reduces it, following the source, to the coordinate model of Section 50.16, where it is
clause (3) of [Stacks, Tag 0FUR].

By `Stacks.DeRham.isIso_homology_formsDerivedSquareComparison_iff`, the comparison in degree `q`
is `H^q(Rb_*(Ω^a_{X'/S} ⟶ j_*Ω^a_{E/S}))`.  This is checked locally on `X`:

* over a chart of [Stacks, Tag 0FUE] it is the étale base change of the coordinate model, by flat
  base change of `H^q(Rb_*(-))` (natural in the module) and the base-change square for the
  restriction of forms;
* off the centre `b` is an isomorphism, hence affine, and both sides vanish in positive degree;
* on a chart with `n = 0` the coordinate blowup is empty, and again both sides vanish.

No hypothesis on the interior of the centre is needed for clause (3).

## Main results

* `Stacks.DeRham.quasiCompact_blowUpToBase`: the blowing up of a smooth centre is quasi-compact.
* `Stacks.DeRham.BlowupEtaleChart.isIso_formsRestrictionHomology_restrict`: clause (3) on a chart.
* `Stacks.DeRham.isIso_homology_blowupFormsDerivedComparison_of_coordinate`: clause (3), from
  clause (3) of [Stacks, Tag 0FUR] for every coordinate model with `1 ≤ n`.

## References

* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.DeRham

/-- A morphism out of an empty scheme is affine. -/
theorem isAffineHom_of_isEmpty {X Y : Scheme.{u}} (g : X ⟶ Y) [IsEmpty X] : IsAffineHom g :=
  ⟨fun U _ => by
    have : IsEmpty (g ⁻¹ᵁ U).toScheme := ⟨fun x => isEmptyElim x.1⟩
    exact isAffine_of_isEmpty⟩

/-- Along an affine morphism the higher direct images of a quasi-coherent module vanish. -/
theorem isZero_homology_derivedPushforward_single {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsAffineHom g] (F : X.Modules) [F.IsQuasicoherent] {q : ℤ} (hq : q ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor Y.Modules q).obj
      ((schemeDerivedPushforward g).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F))) := by
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor Y.Modules q).mapIso
    (asIso (pushforwardSingleToDerived g F))).symm
  rcases lt_or_gt_of_ne hq with hq | hq
  · exact DerivedCategory.isZero_of_isGE _ 0 q hq
  · exact DerivedCategory.isZero_of_isLE _ 0 q hq

/-- For an affine morphism `b`, the map `formsRestrictionHomology b j p a q` is an isomorphism in
every positive degree `q`, both sides being zero. -/
theorem isIso_formsRestrictionHomology_of_isAffineHom {S X Y E : Scheme.{u}} (b : Y ⟶ X)
    [IsAffineHom b] (j : E ⟶ Y) [QuasiCompact j] [QuasiSeparated j] (p : Y ⟶ S) (a : ℕ)
    {q : ℤ} (hq : 1 ≤ q) : IsIso (formsRestrictionHomology b j p a q) := by
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms p a
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms (j ≫ p) a
  have : ((Scheme.Modules.pushforward j).obj
      (relativeDifferentialForms (j ≫ p) (a : ℤ))).IsQuasicoherent :=
    AlgebraicGeometry.ProperCoherentFiniteType.isQuasicoherent_pushforward j _ inferInstance
  exact ⟨⟨0, (isZero_homology_derivedPushforward_single b _ (by omega)).eq_of_src _ _,
    (isZero_homology_derivedPushforward_single b _ (by omega)).eq_of_src _ _⟩⟩

/-- **Restriction of `H^q(Rb_*(Ω^a ⟶ j_*Ω^a))` to an open of the target.**  For `b`
quasi-compact and quasi-separated, the restriction to `V` of the map for `b` is invertible as soon
as the map for `b ∣_ V` is. -/
theorem isIso_pullback_ι_formsRestrictionHomology {S X Y E : Scheme.{u}} (b : Y ⟶ X)
    [QuasiCompact b] [QuasiSeparated b] (j : E ⟶ Y) [QuasiCompact j] [QuasiSeparated j]
    (p : Y ⟶ S) (V : X.Opens) (a : ℕ) (q : ℤ)
    (h : IsIso (formsRestrictionHomology (b ∣_ V) (j ∣_ (b ⁻¹ᵁ V)) ((b ⁻¹ᵁ V).ι ≫ p) a q)) :
    IsIso ((Scheme.Modules.pullback V.ι).map (formsRestrictionHomology b j p a q)) := by
  have w := Stacks.AlgebraicGeometry.AffineBaseChange.restrictSquare j (b ⁻¹ᵁ V)
  have : IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app
      (relativeDifferentialForms (j ≫ p) (a : ℤ))) :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare j _ _
  have hs : (b ⁻¹ᵁ V).ι ≫ p = ((b ⁻¹ᵁ V).ι ≫ p) ≫ 𝟙 S := by simp
  have : IsIso (relativeDifferentialFormsMap (b ⁻¹ᵁ V).ι p ((b ⁻¹ᵁ V).ι ≫ p) (𝟙 S) hs (a : ℤ)) :=
    isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ _
  have : IsIso (relativeDifferentialFormsMap (j ⁻¹ᵁ (b ⁻¹ᵁ V)).ι (j ≫ p)
      ((j ∣_ (b ⁻¹ᵁ V)) ≫ (b ⁻¹ᵁ V).ι ≫ p) (𝟙 S)
      (forms_square_comm_aux j (j ∣_ (b ⁻¹ᵁ V)) (b ⁻¹ᵁ V).ι (j ⁻¹ᵁ (b ⁻¹ᵁ V)).ι w p
        ((b ⁻¹ᵁ V).ι ≫ p) (𝟙 S) hs) (a : ℤ)) :=
    isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ _
  exact (isIso_formsRestrictionHomology_iff (isPullback_morphismRestrict b V).flip w p
    ((b ⁻¹ᵁ V).ι ≫ p) (𝟙 S) hs a q).2 h

/-- **Changing the base of the forms along an étale morphism**, for
`H^q(Rb_*(Ω^a ⟶ j_*Ω^a))`. -/
theorem isIso_formsRestrictionHomology_comp_etale {S S₁ X Y E : Scheme.{u}} (b : Y ⟶ X)
    [QuasiCompact b] [QuasiSeparated b] (j : E ⟶ Y) [QuasiCompact j] [QuasiSeparated j]
    (p₁ : Y ⟶ S₁) (s : S₁ ⟶ S) [Etale s] (a : ℕ) (q : ℤ)
    (h : IsIso (formsRestrictionHomology b j p₁ a q)) :
    IsIso (formsRestrictionHomology b j (p₁ ≫ s) a q) := by
  have w : 𝟙 E ≫ j = j ≫ 𝟙 Y := by simp
  have : IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app
      (relativeDifferentialForms (j ≫ p₁ ≫ s) (a : ℤ))) :=
    Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isIso w _
  have hs : 𝟙 Y ≫ p₁ ≫ s = p₁ ≫ s := Category.id_comp _
  have : IsIso (relativeDifferentialFormsMap (𝟙 Y) (p₁ ≫ s) p₁ s hs (a : ℤ)) :=
    isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ _
  have : IsIso (relativeDifferentialFormsMap (𝟙 E) (j ≫ p₁ ≫ s) (j ≫ p₁) s
      (forms_square_comm_aux j j (𝟙 Y) (𝟙 E) w (p₁ ≫ s) p₁ s hs) (a : ℤ)) :=
    isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ _
  have h1 := (isIso_formsRestrictionHomology_iff (IsPullback.of_id_fst (f := b)) w (p₁ ≫ s) p₁ s
    hs a q).2 h
  exact (NatIso.isIso_map_iff (Scheme.Modules.pullbackId _) _).1 h1

variable {S X Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}

/-- A property of opens of `X` that holds on every blowup chart and on the complement of the
centre holds on a family of opens covering `X`. -/
private theorem exists_iSup_eq_top_forall_of_chart [IsClosedImmersion i] [Smooth f]
    [Smooth (i ≫ f)] (P : X.Opens → Prop) (hchart : ∀ c : BlowupEtaleChart f i, P c.U)
    (hcompl : P ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩) :
    ∃ V : X → X.Opens, ⨆ x, V x = ⊤ ∧ ∀ x, P (V x) := by
  classical
  have hloc : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ P V := by
    intro x
    by_cases hx : x ∈ Set.range i.base
    · obtain ⟨z, rfl⟩ := hx
      obtain ⟨c, hzc, -⟩ := exists_blowupEtaleChart f i z ⊤ trivial
      exact ⟨c.U, hzc, hchart c⟩
    · exact ⟨_, hx, hcompl⟩
  choose V hxV hV using hloc
  exact ⟨V, top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxV x⟩, hV⟩

/-- **The blowing up of a smooth centre is quasi-compact**: over a chart it is the base change of
the coordinate blowup, and off the centre it is an isomorphism. -/
theorem quasiCompact_blowUpToBase [IsClosedImmersion i] [Smooth f] [Smooth (i ≫ f)] :
    QuasiCompact (blowUpToBase i.ker) := by
  obtain ⟨V, hV, hVq⟩ := exists_iSup_eq_top_forall_of_chart (f := f) (i := i)
    (fun V => QuasiCompact (blowUpToBase i.ker ∣_ V))
    (fun c => by
      let := c.commRing
      exact MorphismProperty.of_isPullback (P := @QuasiCompact)
        c.isPullback_blowupMap.flip inferInstance)
    (by
      have := isIso_blowUpToBase_restrict_compl_range (i := i)
      infer_instance)
  let inst :=
    AlgebraicGeometry.instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  have : IsZariskiLocalAtTarget @QuasiCompact :=
    @HasAffineProperty.instIsZariskiLocalAtTarget @QuasiCompact _ inst
  exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := @QuasiCompact) V hV hVq

/-- The coordinate model with `n = 0` blows up the zero ideal, so the blowup is empty and its
structure morphism is affine. -/
theorem isAffineHom_coordinateBlowupToAmbient_zero (R : Type u) [CommRing R] (m : ℕ) :
    IsAffineHom (coordinateBlowupToAmbient R m 0) := by
  have : IsEmpty (coordinateBlowup R m 0) := by
    change IsEmpty (blowUp (Stacks.MoreMorphisms.coordinateIdeal R m 0))
    rw [Stacks.MoreMorphisms.coordinateIdeal_zero]
    exact isEmpty_blowUp_bot' _
  exact isAffineHom_of_isEmpty _

attribute [local instance] Stacks.MoreMorphisms.coordinateEmbedding_isClosedImmersion in
/-- Clause (3) for the coordinate model with `n = 0`, where both sides vanish. -/
theorem isIso_formsRestrictionHomology_coordinate_zero (R : Type u) [CommRing R] (m a : ℕ)
    {q : ℤ} (hq : 1 ≤ q) :
    IsIso (formsRestrictionHomology (coordinateBlowupToAmbient R m 0) (coordinateExceptionalι R m 0)
      (coordinateBlowupToAmbient R m 0 ≫ coordinateAmbientToBase R m 0) a q) :=
  have := isAffineHom_coordinateBlowupToAmbient_zero R m
  isIso_formsRestrictionHomology_of_isAffineHom _ _ _ a hq

namespace BlowupEtaleChart

variable (c : BlowupEtaleChart f i)

/-- **Clause (3) on a chart.**  Suppose `H^q(Rb_*(Ω^a ⟶ j_*Ω^a))` is invertible for the
coordinate model.  Then it is invertible for the blowup restricted over the chart.  It is first
transferred along the étale chart map, as forms over `Spec R`, and then the base is changed to
`S`. -/
theorem isIso_formsRestrictionHomology_restrict [IsClosedImmersion i] (a : ℕ) (q : ℤ)
    (hcoord : IsIso (formsRestrictionHomology (coordinateBlowupToAmbient c.R c.m c.n)
      (coordinateExceptionalι c.R c.m c.n)
      (coordinateBlowupToAmbient c.R c.m c.n ≫ coordinateAmbientToBase c.R c.m c.n) a q)) :
    IsIso (formsRestrictionHomology (blowUpToBase i.ker ∣_ c.U)
      ((exceptionalIdeal i.ker).subschemeι ∣_ (blowUpToBase i.ker ⁻¹ᵁ c.U))
      ((blowUpToBase i.ker ⁻¹ᵁ c.U).ι ≫ blowUpToBase i.ker ≫ f) a q) := by
  let := c.commRing
  have := c.etale
  have := c.isOpenImmersion_base
  have := c.isPullback_blowupMap.flip
  have : QuasiCompact (blowUpToBase i.ker ∣_ c.U) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) c.isPullback_blowupMap.flip inferInstance
  have : QuasiSeparated (blowUpToBase i.ker ∣_ c.U) :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) c.isPullback_blowupMap.flip inferInstance
  have hqc := Scheme.Hom.isQuasicoherent_relativeDifferentialForms
    (coordinateExceptionalι c.R c.m c.n ≫ coordinateBlowupToAmbient c.R c.m c.n ≫
      coordinateAmbientToBase c.R c.m c.n) a
  have : IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
      c.exceptionalMap_comm).app (relativeDifferentialForms (coordinateExceptionalι c.R c.m c.n ≫
        coordinateBlowupToAmbient c.R c.m c.n ≫ coordinateAmbientToBase c.R c.m c.n) (a : ℤ))) :=
    Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
      c.isPullback_exceptionalMap.flip _
  set pR := coordinateBlowupToAmbient c.R c.m c.n ≫ coordinateAmbientToBase c.R c.m c.n
  have hs : c.blowupMap ≫ pR =
      ((blowUpToBase i.ker ∣_ c.U) ≫ c.g ≫ coordinateAmbientToBase c.R c.m c.n) ≫ 𝟙 _ := by
    rw [Category.comp_id, ← Category.assoc, ← c.blowupMap_comm, Category.assoc]
  have : IsIso (relativeDifferentialFormsMap c.blowupMap pR
      ((blowUpToBase i.ker ∣_ c.U) ≫ c.g ≫ coordinateAmbientToBase c.R c.m c.n) (𝟙 _) hs
      (a : ℤ)) :=
    isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ _
  have : IsIso (relativeDifferentialFormsMap c.exceptionalMap
      (coordinateExceptionalι c.R c.m c.n ≫ pR)
      (((exceptionalIdeal i.ker).subschemeι ∣_ (blowUpToBase i.ker ⁻¹ᵁ c.U)) ≫
        (blowUpToBase i.ker ∣_ c.U) ≫ c.g ≫ coordinateAmbientToBase c.R c.m c.n) (𝟙 _)
      (forms_square_comm_aux _ _ _ _ c.exceptionalMap_comm _ _ _ hs) (a : ℤ)) :=
    isIso_relativeDifferentialFormsMap_of_etale _ _ _ _ _ _
  have hR := (isIso_formsRestrictionHomology_iff c.isPullback_blowupMap.flip c.exceptionalMap_comm
    pR _ (𝟙 _) hs a q).1 (Functor.map_isIso _ _)
  have hS := isIso_formsRestrictionHomology_comp_etale _ _ _ c.base a q hR
  have hp : ((blowUpToBase i.ker ∣_ c.U) ≫ c.g ≫ coordinateAmbientToBase c.R c.m c.n) ≫ c.base =
      (blowUpToBase i.ker ⁻¹ᵁ c.U).ι ≫ blowUpToBase i.ker ≫ f := by
    rw [Category.assoc, Category.assoc, c.comm, ← Category.assoc, morphismRestrict_ι,
      Category.assoc]
  rw [hp] at hS
  exact hS

end BlowupEtaleChart

/-- **Clause (3) of [Stacks, Tag 0FUU], reduced to the coordinate model.**  For `f` smooth, `i` a
closed immersion of a scheme smooth over `S` and `q ≥ 1`, suppose `H^q(Rb_*(Ω^a ⟶ j_*Ω^a))` is
invertible for every coordinate model with `1 ≤ n`.  Then the comparison
`Rb_*Ω^a_{X'/S} ⟶ i_*Rp_*Ω^a_{E/S}` is invertible on `H^q`. -/
theorem isIso_homology_blowupFormsDerivedComparison_of_coordinate [IsClosedImmersion i]
    [Smooth f] [Smooth (i ≫ f)] (a : ℕ) {q : ℤ} (hq : 1 ≤ q)
    (hcoord : ∀ (R : Type u) [CommRing R] (m n : ℕ), 1 ≤ n →
      IsIso (formsRestrictionHomology (coordinateBlowupToAmbient R m n)
        (coordinateExceptionalι R m n)
        (coordinateBlowupToAmbient R m n ≫ coordinateAmbientToBase R m n) a q)) :
    IsIso ((DerivedCategory.homologyFunctor X.Modules q).map
      (blowupFormsDerivedComparison f i (a : ℤ))) := by
  classical
  have hcoord' : ∀ (R : Type u) [CommRing R] (m n : ℕ),
      IsIso (formsRestrictionHomology (coordinateBlowupToAmbient R m n)
        (coordinateExceptionalι R m n)
        (coordinateBlowupToAmbient R m n ≫ coordinateAmbientToBase R m n) a q) := by
    intro R _ m n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact isIso_formsRestrictionHomology_coordinate_zero R m a hq
    · exact hcoord R m n hn
  have := quasiCompact_blowUpToBase (f := f) (i := i)
  have : QuasiSeparated (blowUpToBase i.ker) :=
    have := Stacks.AlgebraicGeometry.BlowUpSeparatedInput.isSeparated_blowUpToBase i.ker
    inferInstance
  unfold blowupFormsDerivedComparison
  rw [isIso_homology_formsDerivedSquareComparison_iff]
  obtain ⟨V, hV, hVi⟩ := exists_iSup_eq_top_forall_of_chart (f := f) (i := i)
    (fun V => IsIso ((Scheme.Modules.pullback V.ι).map (formsRestrictionHomology
      (blowUpToBase i.ker) (exceptionalIdeal i.ker).subschemeι (blowUpToBase i.ker ≫ f) a q)))
    (fun c => by
      let := c.commRing
      exact isIso_pullback_ι_formsRestrictionHomology _ _ _ c.U a q
        (c.isIso_formsRestrictionHomology_restrict a q (hcoord' c.R c.m c.n)))
    (by
      have := isIso_blowUpToBase_restrict_compl_range (i := i)
      exact isIso_pullback_ι_formsRestrictionHomology _ _ _ _ a q
        (isIso_formsRestrictionHomology_of_isAffineHom _ _ _ a hq))
  exact Scheme.Modules.isIso_of_isIso_pullback_ι V hV _ hVi

end Stacks.DeRham
