module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessAndStrictTransformImageUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismClosedImmersionLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperLimitOfFinitePresentationEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImagePartialSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionAfterAdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformProperties

/-!
# A proper extension of an étale morphism after an admissible blowup of a compactification

Let `T` be a quasi-compact and quasi-separated algebraic space over a scheme `S`, let `U` be an
algebraic space separated and of finite type over `T`, and let `f : V ⟶ U` be an étale
morphism. Suppose `V` has a compactification over `T`: a quasi-compact open immersion
`j : V ⟶ Y` into an algebraic space `Y` proper over `T`. Then there are a `V`-admissible blowup
`b : Y' ⟶ Y` and an open subspace `V'` of `Y'` containing the inverse image of `V` such that
`f` extends to a proper morphism `V' ⟶ U`. This is [Stacks, Tag 0F4A].

The argument is the source's. Let `Z ⊆ Y ×_T U` be the scheme-theoretic image of the graph
`(j, f) : V ⟶ Y ×_T U`. Since `U ⟶ T` is separated, so is the projection `Y ×_T U ⟶ Y`, and
`Z ⟶ Y` is an isomorphism over `V` (Stacks 0CP3); it is moreover separated and of finite type.
So Stacks 087F, in the form corrected by a separatedness hypothesis, gives a `V`-admissible
blowup `b : Y' ⟶ Y` for which the strict transform `Z'` of `Z` maps isomorphically onto an
open subspace `V'` of `Y'`. The lift of the graph to `(Y ×_T U) ×_Y Y'` factors through `Z'`
(the first half of Stacks 0F49), which places `V` inside `V'`; and `Z' ⟶ U` is proper, being a
closed immersion followed by base changes of the proper morphisms `b` and `Y ⟶ T`, so
`V' ≅ Z' ⟶ U` is the required proper extension.

## Main results

* `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_isProper_extension_of_isEtale`: Stacks
  0F4A, from the corrected form of Stacks 087F
  (`AlgebraicGeometry.Space.exists_isBlowupAlong_isOpenImmersion_strictTransformSpaceToBlowUp`).

## Implementation notes

The compactification is given by its data: the quasi-compact open immersion `j : V ⟶ Y` and the
proper morphism `p : Y ⟶ T` with `j ≫ p = f ≫ g`. The open subspace `V ⊆ Y` of the source is the
range of `j`. "`V ⊆ V' ⊆ Y'`" is the morphism `e : V ⟶ V'` whose composite with the inclusion of
`V'` has range the inverse image of `V` in `Y'` and lies over `j`; "`V ⟶ U` extends" is
`e ≫ q = f`.

Stacks 087F as published asks only that `X ⟶ B` be of finite type, and is false at that
generality; it is used here with `X ⟶ B` also separated, which holds in the application since
`Z ⟶ Y` is a closed immersion followed by a base change of the separated morphism `U ⟶ T`. Its
"`f⁻¹(U) ⟶ U` is an isomorphism" is read, as in Stacks 0879, on the fibre product.

## References

* [Stacks Project, Tag 0F4A](https://stacks.math.columbia.edu/tag/0F4A)
* [Stacks Project, Tag 087F](https://stacks.math.columbia.edu/tag/087F)
* [Stacks Project, Tag 0F49](https://stacks.math.columbia.edu/tag/0F49)
* [Stacks Project, Tag 0CP3](https://stacks.math.columbia.edu/tag/0CP3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The inverse image of an open subspace under a blowup avoiding it, as the range of a
lift.** Let `b : Y' ⟶ Y` be the blowup of `Y` in a closed subspace `Zc` and let `j : V ⟶ Y` be a
morphism whose image avoids `Zc`. Then `j` lifts uniquely through `b`, and the range of the lift
is the inverse image under `b` of the range of `j`; this is Stacks 085T part (1), that `b` is an
isomorphism over the complement of `Zc`. -/
theorem exists_lift_range_eq_preimage_of_isBlowupAlong {Y Y' : AlgebraicSpaces B S hS}
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    {Zc : ClosedSubspaces B S hS Y.1} {b : Y' ⟶ Y} (hbl : IsBlowupAlong B S hS Zc b)
    (j : V ⟶ Y.1)
    (hdisj : Disjoint (subspacePointSet B S hS Y.1 (Subfunctor.range j))
      (subspacePointSet B S hS Y.1 Zc.1)) :
    ∃ jl : V ⟶ Y'.1, jl ≫ b.hom = j ∧
      Subfunctor.range jl = (Subfunctor.range j).preimage b.hom := by
  set O := openComplementOfClosedSubspace B S hS Y Zc
  have hiso := isIso_fromPreimage_openComplement hbl
  -- `j` factors through the complement of the centre.
  obtain ⟨k, hk⟩ := (factorsThrough_openSubspace_iff_points B S hS Y.2 hV O.1 O.2 j).2 (by
    rintro _ ⟨v, rfl⟩
    have hmem : pointsMap B S hS V j v ∈ subspacePointSet B S hS Y.1 (Subfunctor.range j) :=
      ⟨pointsMap B S hS V (Subfunctor.toRange j) v, by
        rw [← pointsMap_comp_apply, Subfunctor.toRange_ι]⟩
    show _ ∈ subspacePointSet B S hS Y.1 O.1
    rw [subspacePointSet_openComplement]
    exact fun h => Set.disjoint_left.1 hdisj hmem h)
  set jl : V ⟶ Y'.1 := k ≫ inv (O.1.fromPreimage b.hom) ≫ (O.1.preimage b.hom).ι with hjl
  have hjlb : jl ≫ b.hom = j := by
    rw [hjl, Category.assoc, Category.assoc, ← Subfunctor.fromPreimage_ι, IsIso.inv_hom_id_assoc,
      hk]
  refine ⟨jl, hjlb, le_antisymm ?_ ?_⟩
  · rintro W _ ⟨v, rfl⟩
    exact ⟨v, (CategoryTheory.congr_fun (NatTrans.congr_app hjlb W) v).symm⟩
  · rintro W y ⟨v, hv⟩
    have hyO : b.hom.app W y ∈ O.1.obj W := by
      rw [← hv, ← CategoryTheory.congr_fun (NatTrans.congr_app hk W) v]
      exact (k.app W v).2
    have hfp : (O.1.fromPreimage b.hom).app W ⟨y, hyO⟩ = k.app W v := by
      apply Subtype.ext
      show b.hom.app W y = (k ≫ O.1.ι).app W v
      rw [hk, hv]
    refine ⟨v, ?_⟩
    show (k ≫ inv (O.1.fromPreimage b.hom) ≫ (O.1.preimage b.hom).ι).app W v = y
    simp only [NatTrans.comp_app, types_comp_apply]
    rw [← hfp]
    have := Iso.hom_inv_id_app_apply (asIso (O.1.fromPreimage b.hom)) W ⟨y, hyO⟩
    rw [asIso_hom, asIso_inv] at this
    rw [this]
    rfl

/-- Let `T` be a quasi-compact and quasi-separated algebraic space over `S`, let `g : U ⟶ T` be
separated and of finite type, and let `f : V ⟶ U` be étale. Suppose `V` has a compactification
over `T`: a quasi-compact open immersion `j : V ⟶ Y` into an algebraic space `Y` with
`p : Y ⟶ T` proper and `j ≫ p = f ≫ g`. Then there are a `V`-admissible blowup `b : Y' ⟶ Y` and
an open subspace `V' ⊆ Y'` containing `V` — a morphism `e : V ⟶ V'` lying over `j` whose image
in `Y'` is the inverse image of `V` — such that `f` extends to a proper morphism `q : V' ⟶ U`
over `T`. -/
@[stacks 0F4A]
theorem exists_isAdmissibleBlowup_isProper_extension_of_isEtale
    (hZ : B.Contains (⊤_ Scheme.{u})) {T U V Y : AlgebraicSpaces B S hS}
    (hTqc : IsQuasiCompactSpace B S hS T.1) (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ T.1)
    (g : U.1 ⟶ T.1) (hgft : IsFiniteType B S hS g) (hgsep : IsSeparated B S hS g)
    (f : V.1 ⟶ U.1) (_hf : IsEtale B S hS f)
    (j : V.1 ⟶ Y.1) (p : Y.1 ⟶ T.1) (hj : IsOpenImmersion B S hS j)
    (hjqc : IsQuasiCompact B S hS j) (hp : IsProper B S hS p) (hcomm : j ≫ p = f ≫ g) :
    ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ Y),
      IsAdmissibleBlowup B S hS
        ⟨Subfunctor.range j, isOpenSubspace_subfunctorRange B S hS V.2 hj⟩ b ∧
      ∃ (V' : OpenSubspaces B S hS Y'.1) (e : V.1 ⟶ V'.1.toFunctor) (q : V'.1.toFunctor ⟶ U.1),
        Subfunctor.range (e ≫ V'.1.ι) = (Subfunctor.range j).preimage b.hom ∧
          e ≫ V'.1.ι ≫ b.hom = j ∧ IsProper B S hS q ∧ e ≫ q = f ∧
            q ≫ g = V'.1.ι ≫ b.hom ≫ p := by
  classical
  have _ : Mono j := mono_of_presheaf_isOpenImmersion hj
  set Vo : OpenSubspaces B S hS Y.1 :=
    ⟨Subfunctor.range j, isOpenSubspace_subfunctorRange B S hS V.2 hj⟩ with hVo
  let pB : Y ⟶ T := ObjectProperty.homMk p
  let gB : U ⟶ T := ObjectProperty.homMk g
  let P := AlgebraicSpaces.fiberProduct B S hS pB gB
  let fstB : P ⟶ Y := fiberProductFirst B S hS pB gB
  let sndB : P ⟶ U := ObjectProperty.homMk (pullback.snd p g)
  let γ : V ⟶ P := ObjectProperty.homMk (pullback.lift j f hcomm)
  have hγfst : γ.hom ≫ fstB.hom = j := pullback.lift_fst _ _ _
  have hγsnd : γ.hom ≫ sndB.hom = f := pullback.lift_snd _ _ _
  -- `Y` is quasi-compact and quasi-separated.
  have hYqc : IsQuasiCompactSpace B S hS Y.1 :=
    (hp.isFiniteType.2 T.1 T.2 hTqc (𝟙 T.1)).of_iso B S hS (asIso (pullback.snd (𝟙 T.1) p))
  have hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ Y.2 hTqs
      (isQuasiSeparated_of_isSeparated B S hS hp.isSeparated)
  -- `V ⊆ Y` is quasi-compact.
  have hVqc : IsQuasiCompactSpace B S hS V.1 :=
    (hjqc Y.1 Y.2 hYqc (𝟙 Y.1)).of_iso B S hS (asIso (pullback.snd (𝟙 Y.1) j))
  have hVoqc : IsQuasiCompactSpace B S hS Vo.1.toFunctor :=
    hVqc.of_iso B S hS (asIso (Subfunctor.toRange j))
  have hVoι : IsQuasiCompact B S hS Vo.1.ι :=
    (isQuasiCompact_iff_isQuasiCompactSpace_openSubspace B S hS hZ Y hYqc hYqs Vo).2 hVoqc
  -- The projection `Y ×_T U ⟶ Y` is separated and of finite type.
  have hfstsep : IsSeparated B S hS fstB.hom :=
    isSeparated_pullback_fst_of_snd B S hS g p (isSeparated_pullback B S hS g p hgsep)
  have hfstft : IsFiniteType B S hS fstB.hom :=
    IsFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback p g) U.2 T.2 hgft
  -- The scheme-theoretic image `Z` of the graph, and Stacks 0CP3.
  let Z := schemeTheoreticImage B S hS γ.hom P.2
  have hZι : toSchemeTheoreticImage B S hS γ.hom ≫ Z.1.ι = γ.hom :=
    toSchemeTheoreticImage_ι B S hS γ.hom
  let s : Vo.1.toFunctor ⟶ P.1 := inv (Subfunctor.toRange j) ≫ γ.hom
  have hs : s ≫ fstB.hom = Vo.1.ι := by
    show (inv (Subfunctor.toRange j) ≫ γ.hom) ≫ fstB.hom = (Subfunctor.range j).ι
    rw [Category.assoc, hγfst]
    exact (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι j).symm
  have hsrange : Subfunctor.range s = Subfunctor.range γ.hom := by
    refine le_antisymm (Subfunctor.range_comp_le _ _) ?_
    rw [show γ.hom = Subfunctor.toRange j ≫ s by
      show γ.hom = Subfunctor.toRange j ≫ inv (Subfunctor.toRange j) ≫ γ.hom
      rw [IsIso.hom_inv_id_assoc]]
    exact Subfunctor.range_comp_le _ _
  have hsimage : schemeTheoreticImageSubfunctor B S hS s =
      schemeTheoreticImageSubfunctor B S hS γ.hom := by
    simp only [schemeTheoreticImageSubfunctor, hsrange]
  have h0CP3 := isIso_pullback_snd_schemeTheoreticImageSubfunctor_comp_of_section B S hS P.2 Y.2
    fstB.hom hfstsep Vo.1 Vo.2 hVoι s hs
  rw [hsimage] at h0CP3
  -- `Z ⟶ Y` is separated and of finite type.
  have hzYsep : IsSeparated B S hS (closedSubspaceFirst B S hS pB gB Z).hom :=
    isSeparated_comp B S hS _ _ (isSeparated_of_isClosedImmersion B S hS _ Z.2.2) hfstsep
  have hzYft : IsFiniteType B S hS (closedSubspaceFirst B S hS pB gB Z).hom :=
    isFiniteType_comp' B S hS _ _ P.2 Y.2 (isFiniteType_of_isClosedImmersion B S hS _ Z.2.2)
      hfstft
  -- Stacks 087F.
  obtain ⟨Y', b, Zc, hfp, hdisj, hbl, -, hopen⟩ :=
    exists_isBlowupAlong_isOpenImmersion_strictTransformSpaceToBlowUp hZ
      (closedSubspaceFirst B S hS pB gB Z) Vo hYqc hYqs hVoqc hzYft hzYsep h0CP3
      (fun g hX hY hf hqc hqs =>
        exists_integralFiniteSystem_isClosedImmersion_of_isFinite g hX hY hf hqc hqs)
      (fun f hX hY hft hsep hqc hqs => by
        obtain ⟨X', i, f', hX', hi, hf'sep, hf'fp, hif⟩ :=
          exists_isClosedImmersion_isSeparated_isFinitePresentation_of_isFiniteType B S hS hX hY f
            hft hsep hqc hqs
        exact ⟨X', f', i, hX', hf'sep, hf'fp, hi, hif⟩)
  have hbp : IsProper B S hS b.hom :=
    isProper_of_isBlowupAlong_of_isFinitePresentation B S hS Zc b hfp hbl
  -- The lift of `j` to the blowup.
  obtain ⟨jl, hjlb, hjlrange⟩ := exists_lift_range_eq_preimage_of_isBlowupAlong V.2 hbl j hdisj
  let v' : V.1 ⟶ (strictTransformPullback B S hS fstB b).1 :=
    pullback.lift γ.hom jl (by rw [hjlb]; exact hγfst)
  have hv'fst : v' ≫ pullback.fst fstB.hom b.hom = γ.hom := pullback.lift_fst _ _ _
  have hv'snd : v' ≫ (strictTransformPullbackToBlowUp B S hS fstB b).hom = jl :=
    pullback.lift_snd _ _ _
  have hvU : Subfunctor.range (γ.hom ≫ fstB.hom) ≤ Vo.1 := by
    rw [hγfst]
  -- The lift factors through the strict transform (the first half of Stacks 0F49).
  obtain ⟨w₀, hw₁, hw₂, hw₃⟩ := exists_lift_strictTransformPullback B S hS pB gB Vo Zc b hdisj Z
    γ (toSchemeTheoreticImage B S hS γ.hom) hZι v' hv'fst hvU
  have hle := hw₃.trans (preimage_openComplement_le_strictTransform_of_isBlowupAlong B S hS
    (closedSubspaceFirst B S hS pB gB Z) b Zc hbl)
  let St := strictTransform B S hS (closedSubspaceFirst B S hS pB gB Z) b (Zc.1.preimage b.hom)
  let w : V.1 ⟶ St.1.toFunctor := Subfunctor.lift w₀ hle
  have hwι : w ≫ St.1.ι = w₀ := Subfunctor.lift_ι _ _
  have hamb : strictTransformToAmbient B S hS pB gB b Z ≫
      (strictTransformPullbackToBlowUp B S hS fstB b).hom =
      (strictTransformPullbackToBlowUp B S hS (closedSubspaceFirst B S hS pB gB Z) b).hom :=
    pullback.lift_snd _ _ _
  have hw₀snd : w₀ ≫
      (strictTransformPullbackToBlowUp B S hS (closedSubspaceFirst B S hS pB gB Z) b).hom = jl := by
    rw [← hamb, ← Category.assoc, hw₁, hv'snd]
  -- The open subspace `V'` and the proper extension.
  let σ := strictTransformSpaceToBlowUp B S hS (closedSubspaceFirst B S hS pB gB Z) b
    (Zc.1.preimage b.hom)
  have _ : Mono σ.hom := mono_of_presheaf_isOpenImmersion hopen
  have hSt' : IsAlgebraicSpace B S hS St.1.toFunctor := St.2.1
  let V' : OpenSubspaces B S hS Y'.1 :=
    ⟨Subfunctor.range σ.hom, isOpenSubspace_subfunctorRange B S hS hSt' hopen⟩
  have hwσ : w ≫ σ.hom = jl := by
    show w ≫ St.1.ι ≫
      (strictTransformPullbackToBlowUp B S hS (closedSubspaceFirst B S hS pB gB Z) b).hom = jl
    rw [← Category.assoc, hwι, hw₀snd]
  have hwe : (w ≫ Subfunctor.toRange σ.hom) ≫ V'.1.ι = jl := by
    rw [Category.assoc]
    show w ≫ Subfunctor.toRange σ.hom ≫ (Subfunctor.range σ.hom).ι = jl
    rw [Subfunctor.toRange_ι, hwσ]
  refine ⟨Y', b, isAdmissibleBlowup_of_isBlowupAlong hfp hdisj hbl, V',
    w ≫ Subfunctor.toRange σ.hom,
    inv (Subfunctor.toRange σ.hom) ≫ St.1.ι ≫
      (strictTransformPullbackToSource B S hS (closedSubspaceFirst B S hS pB gB Z) b).hom ≫
        Z.1.ι ≫ sndB.hom, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hwe, hjlrange]
  · rw [← Category.assoc, hwe, hjlb]
  · have hPb := (strictTransformPullback B S hS (closedSubspaceFirst B S hS pB gB Z) b).2
    have hZsp : IsAlgebraicSpace B S hS Z.1.toFunctor := Z.2.1
    refine isProper_comp' B S hS _ _ hSt' U.2 (isProper_of_isIso B S hS _) ?_
    refine isProper_comp' B S hS _ _ hPb U.2
      (isProper_of_isClosedImmersion B S hS hSt' hPb _ St.2.2) ?_
    refine isProper_comp' B S hS _ _ hZsp U.2
      (isProper_pullback_fst B S hS Y'.2 Y.2 hZsp b.hom _ hbp) ?_
    refine isProper_comp' B S hS _ _ P.2 U.2
      (isProper_of_isClosedImmersion B S hS hZsp P.2 _ Z.2.2) ?_
    exact (isProper_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS pB gB) hp
  · rw [Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc w, hwι, ← Category.assoc, hw₂]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ sndB.hom) hZι).trans hγsnd)
  · have h1 : sndB.hom ≫ g = fstB.hom ≫ p := pullback.condition.symm
    have h2 : (strictTransformPullbackToSource B S hS (closedSubspaceFirst B S hS pB gB Z) b).hom ≫
        Z.1.ι ≫ fstB.hom =
        (strictTransformPullbackToBlowUp B S hS (closedSubspaceFirst B S hS pB gB Z) b).hom ≫
          b.hom := pullback.condition
    have h3 : (Subfunctor.range σ.hom).ι = inv (Subfunctor.toRange σ.hom) ≫ σ.hom := by
      rw [IsIso.eq_inv_comp, Subfunctor.toRange_ι]
    show (inv (Subfunctor.toRange σ.hom) ≫ St.1.ι ≫
      (strictTransformPullbackToSource B S hS (closedSubspaceFirst B S hS pB gB Z) b).hom ≫
        Z.1.ι ≫ sndB.hom) ≫ g = (Subfunctor.range σ.hom).ι ≫ b.hom ≫ p
    rw [h3]
    simp only [Category.assoc, h1]
    rw [reassoc_of% h2]
    rfl

end AlgebraicGeometry.Space

end
