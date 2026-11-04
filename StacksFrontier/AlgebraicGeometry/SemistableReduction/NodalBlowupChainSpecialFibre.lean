module

public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyStructureSheafCohomology
public import StacksFrontier.AlgebraicGeometry.Models.PointBlowupStructureSheaf
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NodalBlowupHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NodalResolution
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafBaseChangeReduced
public import StacksFrontier.Topology.Dimension.Krull

/-!
# The special fibre of a resolution of a nodal family by point blowups

Let `R` be a discrete valuation ring and `f : X ⟶ Spec R` at-worst-nodal of relative dimension
one, with `X` regular away from the special fibre, and let `h : W ⟶ X` be a chain of blowups in
singular closed points as in [Stacks, Tag 0CDE]. Then `𝒪_X = h_*𝒪_W`, and on special fibres
`hₛ : Wₛ ⟶ Xₛ` satisfies `𝒪_{Xₛ} = hₛ,*𝒪_{Wₛ}` and `Rⁱhₛ,*𝒪_{Wₛ} = 0` for `i > 0`. This is the
claim of the proof of [Stacks, Tag 0E97] for the morphisms `X_{i+1,s} ⟶ X_{i,s}`.

Each blowup `b` is in a point with an étale nodal chart of exponent `n ≥ 2`, so
`R^q b_*𝒪 = 0` for `q > 0`; `𝒪 = b_*𝒪` as the special fibre is reduced; the fibres of `b` have
dimension at most one. On special fibres the conclusions follow from [Stacks, Tag 0E7I],
[Stacks, Tag 0E7F], [Stacks, Tag 0E7G] and [Stacks, Tag 0E7H]
(`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_unitToPushforwardObjUnit_of_isPullback`,
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_rightDerived_of_isPullback`), and they
compose along the chain by the Leray spectral sequence.

## Main results

* `Stacks.SemistableReduction.isReduced_fiber_of_isAtWorstNodal` and
  `Stacks.SemistableReduction.topologicalKrullDim_fiber_le_one_of_isAtWorstNodal`: fibres of a
  nodal family are reduced, of dimension at most one.
* `Stacks.SemistableReduction.isIso_unitToPushforwardObjUnit_comp_of_acyclic` and
  `Stacks.SemistableReduction.isZero_rightDerived_comp_of_acyclic`: acyclicity composes.
* `Stacks.SemistableReduction.NodalBlowupChain.specialFibre`: the chain on special fibres.

## References

* [Stacks Project, Tag 0E97](https://stacks.math.columbia.edu/tag/0E97)
* [Stacks Project, Tag 0CDE](https://stacks.math.columbia.edu/tag/0CDE)
* [Stacks Project, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace IsLocalRing

universe u

namespace Stacks.SemistableReduction

attribute [local instance 2000] HasDerivedCategory.standard

/-! ### Fibres of nodal families -/

/-- The fibres of an at-worst-nodal morphism of relative dimension one are reduced. -/
theorem isReduced_fiber_of_isAtWorstNodal {X S : Scheme.{u}} (q : X ⟶ S)
    (hq : IsAtWorstNodalOfRelativeDimensionOne q) (s : S) : IsReduced (q.fiber s) := by
  obtain ⟨-, hlfp, h⟩ := (Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff q).mpr hq
  have : LocallyOfFinitePresentation q := hlfp
  by_cases hne : Nonempty (q.fiber s)
  · let : (q.fiber s).Over (Spec (.of (S.residueField s))) := ⟨q.fiberToSpecResidueField s⟩
    have : LocallyOfFiniteType (q.fiber s ↘ Spec (.of (S.residueField s))) :=
      inferInstanceAs (LocallyOfFiniteType (q.fiberToSpecResidueField s))
    exact Stacks.Curves.isReduced_of_hasAtWorstNodalSingularities _ _ (h s hne).2.2
  · have : IsEmpty (q.fiber s) := not_nonempty_iff.mp hne
    exact @isReduced_of_isReduced_stalk _ fun x => isEmptyElim x

/-- The fibres of an at-worst-nodal morphism of relative dimension one have dimension at most
one. -/
theorem topologicalKrullDim_fiber_le_one_of_isAtWorstNodal {X S : Scheme.{u}} (q : X ⟶ S)
    (hq : IsAtWorstNodalOfRelativeDimensionOne q) (s : S) :
    topologicalKrullDim (q.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  obtain ⟨-, -, h⟩ := (Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff q).mpr hq
  by_cases hne : Nonempty (q.fiber s)
  · rw [(h s hne).2.1]
    rfl
  · have : IsEmpty (q.fiber s) := not_nonempty_iff.mp hne
    rw [(topologicalKrullDim_eq_bot_iff_isEmpty _).mpr inferInstance]
    exact bot_le

/-! ### Acyclicity composes -/

/-- `𝒪 = (c₁ ≫ c₂)_*𝒪` when `𝒪 = c₁*𝒪` and `𝒪 = c₂*𝒪`. -/
theorem isIso_unitToPushforwardObjUnit_comp_of_acyclic {X Y Z : Scheme.{u}} (c₁ : X ⟶ Y)
    (c₂ : Y ⟶ Z) (h₁ : IsIso (SheafOfModules.unitToPushforwardObjUnit c₁.toRingCatSheafHom))
    (h₂ : IsIso (SheafOfModules.unitToPushforwardObjUnit c₂.toRingCatSheafHom)) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit (c₁ ≫ c₂).toRingCatSheafHom) :=
  Stacks.Curves.StableModel.isIso_unitToPushforwardObjUnit_comp c₁ c₂ h₁ h₂

/-- `Rⁱ(c₁ ≫ c₂)_*𝒪 = 0` for `i > 0` when `c₁` and `c₂` are acyclic for `𝒪`. -/
theorem isZero_rightDerived_comp_of_acyclic {X Y Z : Scheme.{u}} (c₁ : X ⟶ Y) (c₂ : Y ⟶ Z)
    [QuasiCompact c₁] [QuasiSeparated c₁] [CompactSpace Y]
    (h₁ : IsIso (SheafOfModules.unitToPushforwardObjUnit c₁.toRingCatSheafHom))
    (hR₁ : ∀ i : ℕ, 0 < i → IsZero (((Scheme.Modules.pushforward c₁).rightDerived i).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    (hR₂ : ∀ i : ℕ, 0 < i → IsZero (((Scheme.Modules.pushforward c₂).rightDerived i).obj
      (SheafOfModules.unit Y.ringCatSheaf))) (i : ℕ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward (c₁ ≫ c₂)).rightDerived i).obj
      (SheafOfModules.unit X.ringCatSheaf)) :=
  (hR₂ i hi).of_iso (Stacks.Curves.StableModel.rightDerivedCompUnitIso c₁ c₂ h₁ hR₁ i)

/-- `𝒪 = e_*𝒪` and `Rⁱe_*𝒪 = 0` for `i > 0`, for an isomorphism `e`. -/
theorem isZero_rightDerived_of_isIso {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (i : ℕ)
    (hi : 0 < i) : IsZero (((Scheme.Modules.pushforward e).rightDerived i).obj
      (SheafOfModules.unit X.ringCatSheaf)) :=
  Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward e _ i hi

/-! ### The chain of blowups on special fibres -/

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **[Stacks, Tag 0CDE] on special fibres.** Let `f : X ⟶ Spec R` be at-worst-nodal of relative
dimension one with `X` quasi-compact and regular away from the special fibre, let `Xₛ` be the
special fibre (a cartesian square over `Spec κ ⟶ Spec R`) and let `h : W ⟶ X` be a chain of
blowups in singular closed points. Then `W` is regular away from its special fibre,
`𝒪_X = h_*𝒪_W`, and for every cartesian square `Wₛ ⟶ W`, `hₛ : Wₛ ⟶ Xₛ` over `h` and
`Xₛ ⟶ X`, `𝒪_{Xₛ} = hₛ,*𝒪_{Wₛ}` and `Rⁱhₛ,*𝒪_{Wₛ} = 0` for `i > 0`. -/
theorem NodalBlowupChain.specialFibre {X : Scheme.{u}} [CompactSpace X]
    {f : X ⟶ Spec (.of R)} (hf : IsAtWorstNodalOfRelativeDimensionOne f)
    (hgen : ∀ y : X, ¬ IsRegularLocalRing (X.presheaf.stalk y) → f.base y = closedPoint R)
    {Xs : Scheme.{u}} {jX : Xs ⟶ X}
    {gX : Xs ⟶ Spec ((Spec (.of R)).residueField (closedPoint R))}
    (hXs : IsPullback jX gX f ((Spec (.of R)).fromSpecResidueField (closedPoint R)))
    {W : Scheme.{u}} {h : W ⟶ X} (hc : NodalBlowupChain f W h) :
    (∀ y : W, ¬ IsRegularLocalRing (W.presheaf.stalk y) → (h ≫ f).base y = closedPoint R) ∧
    IsIso (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) ∧
    ∀ {Ws : Scheme.{u}} {g : Ws ⟶ W} {hs : Ws ⟶ Xs}, IsPullback g hs h jX →
      IsIso (SheafOfModules.unitToPushforwardObjUnit hs.toRingCatSheafHom) ∧
      ∀ i : ℕ, 0 < i → IsZero (((Scheme.Modules.pushforward hs).rightDerived i).obj
        (SheafOfModules.unit Ws.ringCatSheaf)) := by
  have hlfp : LocallyOfFinitePresentation f := locallyOfFinitePresentation hf.1.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : QuasiCompact jX := MorphismProperty.of_isPullback hXs.flip inferInstance
  have : CompactSpace Xs := QuasiCompact.compactSpace_of_compactSpace jX
  induction hc with
  | refl =>
    refine ⟨by simpa using hgen,
      Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_unitToPushforwardObjUnit_of_isIso _,
      fun {Ws g hs} sq => ?_⟩
    have : IsIso hs := sq.flip.isIso_fst_of_isIso
    exact ⟨Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_unitToPushforwardObjUnit_of_isIso _,
      isZero_rightDerived_of_isIso hs⟩
  | @step W h hh w hw hsing hnodal ih =>
    obtain ⟨hgenW, hOW, hsW⟩ := ih
    have hfW : IsAtWorstNodalOfRelativeDimensionOne (h ≫ f) :=
      hh.isAtWorstNodalOfRelativeDimensionOne hf
    have : LocallyOfFinitePresentation (h ≫ f) := locallyOfFinitePresentation hfW.1.1
    have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (h ≫ f)
    have : IsProper h := hh.isProper
    have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace h
    set I := Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)
    set b := blowUpToBase I
    obtain ⟨n, ⟨c⟩⟩ := nonempty_nodalChartAt_of_not_isRegularLocalRing (h ≫ f) hfW hgenW w hsing
    have hn := c.two_le_of_not_isRegularLocalRing hsing
    have hR : ∀ q : ℕ, 0 < q → IsZero (((Scheme.Modules.pushforward b).rightDerivedPlus q).obj
        (SheafOfModules.unit (blowUp I).ringCatSheaf)) := fun q hq =>
      isZero_rightDerivedPlus_pushforward_blowUp_of_nodalChartAt hw c hn q hq
    have : Flat (h ≫ f) := flat hfW.1.1
    have : Flat (b ≫ h ≫ f) := flat hnodal.1.1
    have hred := isReduced_fiber_of_isAtWorstNodal (h ≫ f) hfW (closedPoint R)
    have hpw : (h ≫ f) w = closedPoint R := hgenW w hsing
    have hOb : IsIso (SheafOfModules.unitToPushforwardObjUnit b.toRingCatSheafHom) :=
      Stacks.Models.isIso_unitToPushforwardObjUnit_blowUpToBase_point (h ≫ f) w hw hpw
    have : Surjective b := Stacks.Models.surjective_blowUpToBase_point (h ≫ f) w hw hpw
    have : IsProper b := inferInstance
    refine ⟨fun y hy => ?_, isIso_unitToPushforwardObjUnit_comp_of_acyclic b h hOb hOW,
      fun {Ws' g' hs'} sq' => ?_⟩
    · rw [Category.assoc, Scheme.Hom.comp_apply]
      by_cases hyx : b.base y = w
      · rw [hyx]
        exact hpw
      · exact hgenW _ (by rwa [← isRegularLocalRing_stalk_blowUp_iff_of_ne hw y hyx])
    · let t := IsPullback.of_hasPullback h jX
      obtain ⟨hOs, hRs⟩ := hsW t
      let l : Ws' ⟶ pullback h jX := pullback.lift (g' ≫ b) hs' (by
        rw [Category.assoc, sq'.w])
      have hl : l ≫ pullback.snd h jX = hs' := pullback.lift_snd _ _ _
      have sqb : IsPullback g' l b (pullback.fst h jX) :=
        IsPullback.of_bot (by rw [hl]; exact sq') (pullback.lift_fst _ _ _).symm t
      have hfib : IsPullback (pullback.fst h jX) (pullback.snd h jX ≫ gX) (h ≫ f)
          ((Spec (.of R)).fromSpecResidueField (closedPoint R)) := t.paste_vert hXs
      have : IsReduced (pullback h jX) :=
        @isReduced_of_isOpenImmersion _ _ hfib.isoPullback.hom _ hred
      have : Surjective l := MorphismProperty.of_isPullback sqb inferInstance
      have : IsProper l := MorphismProperty.of_isPullback sqb inferInstance
      have : IsProper (pullback.snd h jX) :=
        MorphismProperty.of_isPullback t inferInstance
      have : CompactSpace (pullback h jX : Scheme.{u}) :=
        QuasiCompact.compactSpace_of_compactSpace (pullback.snd h jX)
      have hdim : ∀ y, topologicalKrullDim (b.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) := fun y =>
        (Stacks.AlgebraicGeometry.TopDegreeBaseChange.topologicalKrullDim_fiber_le_fiber_comp
          b (h ≫ f) y).trans
          (topologicalKrullDim_fiber_le_one_of_isAtWorstNodal _ hnodal _)
      have hR1 :
          IsZero (Stacks.AlgebraicGeometry.TopDegreeBaseChange.firstDirectImageStructureSheaf b) :=
        hR 1 one_pos
      have hOl :=
        Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_unitToPushforwardObjUnit_of_isPullback
          b sqb hdim hR1 (h0 := by
            have : IsIso (Scheme.Modules.unitToPushforwardUnit b) := hOb
            infer_instance)
      have hRl :=
        Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_rightDerived_of_isPullback
          b sqb hdim hR1
      rw [← hl]
      exact ⟨isIso_unitToPushforwardObjUnit_comp_of_acyclic l _ hOl hOs,
        isZero_rightDerived_comp_of_acyclic l _ hOl hRl hRs⟩

end Stacks.SemistableReduction

end
