module

public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.NagataInputs
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.StrictTransformOpenSubscheme
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AlmostBlowUp.IsomorphismAwayFromCenter
public import StacksCore.Tactic.StacksAttribute

/-!
# Dominating a compactification by a proper extension

Let `S` be a quasi-compact and quasi-separated scheme, let `f : U ⟶ S` be separated and of
finite type and let `V ⊆ U` be a quasi-compact open subscheme. Given a compactification
`V ⊆ Y` of `V` over `S`, a `V`-admissible blowup `Y' ⟶ Y` makes the inclusion `V ⟶ U` extend
to a proper morphism from an open subscheme `V' ⊆ Y'` containing the copy of `V`.

## Main results

* `AlgebraicGeometry.exists_isAdmissibleBlowup_properExtension` gives the blowup, the larger
  open subscheme and the proper extension.

## Implementation notes

The compactification is `AlgebraicGeometry.CompactificationOf`, the category of open immersions
of a fixed `S`-scheme into schemes proper over `S`.

The argument is the one of [Stacks, Tag 0F3Z]. The graph of the inclusion `V ⟶ U` inside
`Y ×_S U` is a section of the first projection over the interior `W = V ⊆ Y`; replacing
`Y ×_S U` by the scheme-theoretic image `a` of that section makes the projection `q : a ⟶ Y`
an isomorphism over `W` ([Stacks, Tag 0CNG]). By [Stacks, Tag 081S] a `W`-admissible blowup
`b : Y' ⟶ Y` puts the strict transform of `a` inside `Y'` as an open subscheme `V'`; that open
subscheme contains the canonical copy of `W`, because away from the centre everything in the
base change avoids the inverse image of the exceptional divisor, and it maps properly to `U`
because the strict transform is closed in `a ×_Y Y'` and both `q` and `b` are proper.

The conclusion `Set.range (e ≫ V'.ι).base = b ⁻¹ᵁ W` says that the copy of `V` inside `V'` is
exactly the inverse image of the interior of the compactification, which is what the induction
of [Stacks, Tag 0F40] consumes; the final equation `p ≫ f = V'.ι ≫ b ≫ j.toBase` says that the
proper extension lies over `S`.

## References

* [Stacks Project, Tag 0F3Z](https://stacks.math.columbia.edu/tag/0F3Z)
* [Stacks Project, Tag 081S](https://stacks.math.columbia.edu/tag/081S)
* [Stacks Project, Tag 0CNG](https://stacks.math.columbia.edu/tag/0CNG)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0F3Z.** After a `V`-admissible blowup `b : Y' ⟶ Y` of a
compactification `j` of a quasi-compact open subscheme `V` of `U`, the blowup contains an open
subscheme `V'` which maps properly to `U`, extending the inclusion of `V`, and whose copy of `V`
is exactly the inverse image of the interior of the compactification. -/
@[stacks 0F3Z]
theorem exists_isAdmissibleBlowup_properExtension
    {S U : Scheme.{u}} (f : U ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (V : U.Opens) [QuasiCompact V.ι]
    (j : CompactificationOf (Over.mk (V.ι ≫ f))) :
    ∃ (Y' : Scheme.{u}) (b : Y' ⟶ j.space) (V' : Y'.Opens)
      (e : V.toScheme ⟶ V'.toScheme) (p : V'.toScheme ⟶ U),
      Stacks.Blowup.IsAdmissibleBlowup j.immersion.opensRange b ∧
        IsOpenImmersion e ∧
        Set.range (e ≫ V'.ι).base =
          (b ⁻¹ᵁ j.immersion.opensRange : Y'.Opens) ∧
        e ≫ V'.ι ≫ b = j.immersion ∧
        IsProper p ∧
        e ≫ p = V.ι ∧ p ≫ f = V'.ι ≫ b ≫ j.toBase := by
  classical
  let W : j.space.Opens := j.immersion.opensRange
  have : CompactSpace U := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : QuasiSeparatedSpace U := quasiSeparatedSpace_of_quasiSeparated f
  have : CompactSpace V.toScheme :=
    (quasiCompact_iff_compactSpace V.ι).mp inferInstance
  have : QuasiSeparatedSpace j.space :=
    quasiSeparatedSpace_of_quasiSeparated j.toBase
  have : CompactSpace j.space :=
    (quasiCompact_iff_compactSpace j.toBase).mp inferInstance
  have hWcompact : IsCompact (W : Set j.space) := by
    show IsCompact (j.immersion.opensRange : Set j.space)
    rw [← Scheme.Hom.image_top_eq_opensRange j.immersion]
    simpa using (isCompact_univ : IsCompact (Set.univ : Set V.toScheme)).image
      j.immersion.continuous
  let eW : W.toScheme ≅ V.toScheme :=
    IsOpenImmersion.isoOfRangeEq W.ι j.immersion (by
      simp [W, Scheme.Hom.coe_opensRange])
  have heW : eW.hom ≫ j.immersion = W.ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac W.ι j.immersion (by
      simp [W, Scheme.Hom.coe_opensRange])
  have hcomm : j.immersion ≫ j.toBase = V.ι ≫ f := by
    simp [CompactificationOf.immersion, CompactificationOf.toBase]
  let s : W.toScheme ⟶ pullback j.toBase f :=
    pullback.lift (eW.hom ≫ j.immersion) (eW.hom ≫ V.ι)
      (by simpa only [Category.assoc] using congrArg (eW.hom ≫ ·) hcomm)
  have hs : s ≫ pullback.fst j.toBase f = W.ι := by
    show pullback.lift (eW.hom ≫ j.immersion) (eW.hom ≫ V.ι) _ ≫
      pullback.fst j.toBase f = W.ι
    rw [pullback.lift_fst, heW]
  have hs2 : s ≫ pullback.snd j.toBase f = eW.hom ≫ V.ι := pullback.lift_snd _ _ _
  let a := s.image
  let q : a ⟶ j.space := s.imageι ≫ pullback.fst j.toBase f
  have : IsIso (q ∣_ W) :=
    isIso_morphismRestrict_imageι_comp_of_section (pullback.fst j.toBase f) W
      (hWcompact.isRetrocompact W.2) s hs
  obtain ⟨I, hfp, hdisj, hopen⟩ :=
    strictTransformOpenImmersion_of_isIso_morphismRestrict q W hWcompact
  let B : Scheme := blowUp I
  let b : B ⟶ j.space := blowUpToBase I
  let PB : Scheme.{u} := Stacks.StrictTransform.baseChange q b
  let E : Set PB := Stacks.StrictTransform.exceptionalPreimage q b (exceptionalIdeal I)
  let T : PB.IdealSheafData := Stacks.StrictTransform.ideal q b (exceptionalIdeal I)
  let c : T.subscheme ⟶ PB := T.subschemeι
  let p₁ : PB ⟶ a := pullback.fst q b
  let p₂ : PB ⟶ B := pullback.snd q b
  let k : T.subscheme ⟶ B := c ≫ p₂
  have : IsOpenImmersion k := hopen
  let C : j.space.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩
  have hWC : W ≤ C := by
    intro x hx
    show x ∉ I.support
    exact fun hxI => (Set.disjoint_left.mp hdisj) hx hxI
  have : IsIso (b ∣_ C) := isIso_blowUp_restrict_compl_support I
  have : IsIso (b ∣_ W) := Stacks.RestrictIso.isIso_morphismRestrict_of_le b hWC inferInstance
  let Wb : B.Opens := b ⁻¹ᵁ W
  let eBW : Wb.toScheme ≅ W.toScheme := asIso (b ∣_ W)
  have : IsIso (p₂ ∣_ Wb) := isIso_morphismRestrict_pullback_snd_preimage q b W
  let eP : (p₂ ⁻¹ᵁ Wb).toScheme ≅ Wb.toScheme := asIso (p₂ ∣_ Wb)
  let r : W.toScheme ⟶ B := eBW.inv ≫ Wb.ι
  let g₀ : W.toScheme ⟶ PB := eBW.inv ≫ eP.inv ≫ (p₂ ⁻¹ᵁ Wb).ι
  have hg₀p₂ : g₀ ≫ p₂ = r := by
    simp [g₀, r, eP, Category.assoc, ← morphismRestrict_ι]
  have hr_b : r ≫ b = W.ι := by
    show eBW.inv ≫ (b ⁻¹ᵁ W).ι ≫ b = W.ι
    rw [← morphismRestrict_ι]
    simp [eBW]
  have hg₀b : g₀ ≫ p₂ ≫ b = W.ι := by rw [← Category.assoc, hg₀p₂, hr_b]
  have hg₀q : g₀ ≫ p₁ ≫ q = W.ι := by
    rw [show p₁ ≫ q = p₂ ≫ b from pullback.condition, hg₀b]
  have hEclosed : IsClosed E :=
    (exceptionalIdeal I).support.isClosed.preimage p₂.continuous
  let P₀ : PB.Opens := ⟨Eᶜ, hEclosed.isOpen_compl⟩
  have hg₀range : Set.range g₀.base ⊆ Set.range P₀.ι.base := by
    intro z hz
    obtain ⟨w, rfl⟩ := hz
    have hbase : b.base (p₂.base (g₀.base w)) = W.ι.base w :=
      congrArg (fun m : W.toScheme ⟶ j.space => m.base w) hg₀b
    have hnot : b.base (p₂.base (g₀.base w)) ∉ I.support := by
      intro hI
      have hW : b.base (p₂.base (g₀.base w)) ∈ (W : Set j.space) := by
        rw [hbase]
        exact w.2
      exact (Set.disjoint_left.mp hdisj) hW hI
    have hnotExc : p₂.base (g₀.base w) ∉ (exceptionalIdeal I).support := by
      show p₂.base (g₀.base w) ∉ (I.comap b).support
      rw [Scheme.IdealSheafData.support_comap I b]
      exact hnot
    exact ⟨⟨g₀.base w, hnotExc⟩, rfl⟩
  let gbar : W.toScheme ⟶ P₀.toScheme := IsOpenImmersion.lift P₀.ι g₀ hg₀range
  have hgbar : gbar ≫ P₀.ι = g₀ := IsOpenImmersion.lift_fac _ _ _
  have : IsIso (c ∣_ P₀) :=
    (isIso_restrict_iff_le_supportedSectionsIdeal E hEclosed T).2 le_rfl
  let cPre : T.subscheme.Opens := c ⁻¹ᵁ P₀
  let uC : P₀.toScheme ⟶ T.subscheme := (asIso (c ∣_ P₀)).inv ≫ cPre.ι
  have huCc : uC ≫ c = P₀.ι := by
    dsimp [uC]
    rw [Category.assoc, ← morphismRestrict_ι]
    simp
  let eWT : W.toScheme ⟶ T.subscheme := gbar ≫ uC
  have heWTc : eWT ≫ c = g₀ := by
    dsimp [eWT]
    rw [Category.assoc, huCc, hgbar]
  let W' : B.Opens := Scheme.Hom.opensRange k
  let eT : W'.toScheme ≅ T.subscheme :=
    IsOpenImmersion.isoOfRangeEq W'.ι k (by simp [W', Scheme.Hom.coe_opensRange])
  let eV : V.toScheme ⟶ W'.toScheme := eW.inv ≫ eWT ≫ eT.inv
  let pT : T.subscheme ⟶ U :=
    c ≫ p₁ ≫ s.imageι ≫ pullback.snd j.toBase f
  let p : W'.toScheme ⟶ U := eT.hom ≫ pT
  have heWTk : eWT ≫ k = r := by
    dsimp [k]
    rw [← Category.assoc, heWTc, hg₀p₂]
  have hfac : eV ≫ W'.ι = eW.inv ≫ r := by
    dsimp [eV]
    rw [← heWTk]
    simp [eT]
  have hrange_r : Set.range r.base = (Wb : Set B) := by
    have hsurj : Function.Surjective eBW.inv.base := fun x => ⟨eBW.hom.base x, by simp⟩
    rw [show r.base = Wb.ι.base ∘ eBW.inv.base by
      simp [r, Scheme.Hom.comp_base]]
    rw [hsurj.range_comp]
    simp
  have hrange_e : Set.range (eV ≫ W'.ι).base = (Wb : Set B) := by
    have hsurj : Function.Surjective eW.inv.base := fun x => ⟨eW.hom.base x, by simp⟩
    rw [hfac, Scheme.Hom.comp_base, TopCat.coe_comp, hsurj.range_comp, hrange_r]
  have hIft : I.IsFiniteType := (finitePresentation_subschemeι_iff_isFiniteType I).mp hfp
  have : IsProper b := isProper_blowUpToBase_of_fg I hIft
  have : IsProper j.toBase := inferInstance
  have : IsProper (s.imageι ≫ pullback.snd j.toBase f) := inferInstance
  have : IsProper pT := by
    dsimp [pT, c, p₁]
    infer_instance
  have : IsProper p := by
    dsimp [p]
    infer_instance
  refine ⟨B, b, W', eV, p, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Stacks.Blowup.isAdmissibleBlowup_iff W b).mpr ⟨I, hfp, hdisj, Iso.refl B, by simp [b]⟩
  · infer_instance
  · simpa [Wb, W, Scheme.Hom.coe_opensRange] using hrange_e
  · rw [← Category.assoc, hfac, Category.assoc, hr_b, ← heW, Iso.inv_hom_id_assoc]
  · infer_instance
  · have hsimageq : s.toImage ≫ q = W.ι := by
      simp only [q, ← Category.assoc, Scheme.Hom.toImage_imageι, hs]
    have : IsIso (pullback.snd q W.ι) :=
      (isIso_morphismRestrict_iff_isIso_pullback_snd q W).1 inferInstance
    have himage : g₀ ≫ p₁ = s.toImage := by
      have ht : pullback.lift s.toImage (𝟙 W.toScheme) (by simpa using hsimageq) =
          pullback.lift (g₀ ≫ p₁) (𝟙 W.toScheme) (by simpa using hg₀q) := by
        refine (cancel_mono (pullback.snd q W.ι)).1 ?_
        rw [pullback.lift_snd, pullback.lift_snd]
      have hfst := congrArg (fun m : W.toScheme ⟶ pullback q W.ι =>
        m ≫ pullback.fst q W.ι) ht
      simpa only [pullback.lift_fst] using hfst.symm
    have hpT : eWT ≫ pT = eW.hom ≫ V.ι := by
      have h1 : eWT ≫ pT = (eWT ≫ c) ≫ p₁ ≫ s.imageι ≫ pullback.snd j.toBase f := by
        simp [pT]
      rw [h1, heWTc, ← Category.assoc g₀ p₁, himage,
        ← Category.assoc s.toImage s.imageι, Scheme.Hom.toImage_imageι]
      exact hs2
    have hcompose : eV ≫ p = eW.inv ≫ eWT ≫ pT := by simp [eV, p]
    rw [hcompose, hpT]
    simp
  · have hbase : pT ≫ f = k ≫ b ≫ j.toBase := by
      dsimp [pT, k, q]
      calc
        c ≫ p₁ ≫ s.imageι ≫ pullback.snd j.toBase f ≫ f =
            c ≫ p₁ ≫ s.imageι ≫ pullback.fst j.toBase f ≫ j.toBase := by
              simp only [pullback.condition]
        _ = c ≫ p₁ ≫ q ≫ j.toBase := rfl
        _ = c ≫ p₂ ≫ b ≫ j.toBase := by
              simpa only [Category.assoc] using
                congrArg (fun t : PB ⟶ j.space => c ≫ t ≫ j.toBase)
                  (pullback.condition : p₁ ≫ q = p₂ ≫ b)
    have hW' : eT.hom ≫ k = W'.ι :=
      IsOpenImmersion.isoOfRangeEq_hom_fac W'.ι k (by simp [W', Scheme.Hom.coe_opensRange])
    simp only [p, ← hW', Category.assoc, hbase]

end AlgebraicGeometry

end
