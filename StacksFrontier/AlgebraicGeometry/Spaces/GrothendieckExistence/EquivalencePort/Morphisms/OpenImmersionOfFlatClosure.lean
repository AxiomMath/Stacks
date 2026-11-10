module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.OpenImmersionFromDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImagePartialSection
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Morphisms.SchemeTheoreticImageRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ImmersionSchemeTheoreticallyDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Thickenings.SchemeChartLift

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# The closure of a graph which is flat over a scheme is open in it

Let `f : X ⟶ S` be a separated morphism locally of finite type from an algebraic space, let
`u : D ⟶ X` be a quasi-compact open immersion from a scheme and `j : D ⟶ Z` an open immersion
into a scheme `Z` over `S`, quasi-compact and scheme-theoretically dominant. Let
`T ⊆ X ×_S Z` be the scheme-theoretic image of `(u, j) : D ⟶ X ×_S Z`.

If on one surjective étale chart `a : V ⟶ X` the scheme-theoretic image of
`D ×_X V ⟶ V ×_S Z` is a represented closed subspace flat over `Z`, then the projection
`T ⟶ Z` is an open immersion (Stacks 0879): it is separated and locally of finite type, flat by
the chart, and an isomorphism over the scheme-theoretically dense open `D` by Stacks 0CP3.

## Main results

* `AlgebraicGeometry.Space.C1573.isOpenImmersion_schemeTheoreticImage_of_flat_chart`: the statement
  above.

## References

* [Stacks Project, Tag 0879](https://stacks.math.columbia.edu/tag/0879)
* [Stacks Project, Tag 0CP3](https://stacks.math.columbia.edu/tag/0CP3)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The chart `V ×_S Z ⟶ X ×_S Z` of the product, induced by a chart `a : V ⟶ X`, is a base
change of `a`. -/
theorem C1573.isPullback_pullbackMap_chart {X₁ V Z₁ Y₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X₁ ⟶ Y₁) (gZ : Z₁ ⟶ Y₁) (a : V ⟶ X₁) :
    IsPullback (pullback.map (a ≫ f) gZ f gZ a (𝟙 _) (𝟙 _) (by simp) (by simp))
      (pullback.fst (a ≫ f) gZ) (pullback.fst f gZ) a := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback f gZ).flip
  have : pullback.map (a ≫ f) gZ f gZ a (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ pullback.snd f gZ =
      pullback.snd (a ≫ f) gZ := by simp
  rw [this]
  exact (IsPullback.of_hasPullback (a ≫ f) gZ).flip

/-- **The chart of the closure of a graph.** Let `β : VZ ⟶ X ×_S Z` be a represented chart of
the product which is a base change of a surjective étale chart `a : V ⟶ X`, and let `k` be a
represented closed subspace of `VZ` whose range is the scheme-theoretic image of the base change
of `(u, j)` along `β`. Then `k` is the inverse image of the closure `T`, and the induced
`χ : T₀ ⟶ T` is a surjective étale chart of `T`. -/
theorem C1573.exists_chart_schemeTheoreticImage (X : AlgebraicSpaces B S hS)
    (f : X.1 ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))))
    {D Z V VZ T₀ : BigFppfOver B S hS} (gZ : yoneda.obj Z ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))))
    (s : yoneda.obj D ⟶ pullback f gZ) (hs : IsQuasiCompact B S hS s)
    (a : yoneda.obj V ⟶ X.1)
    (hasurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haet : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (β : yoneda.obj VZ ⟶ pullback f gZ) (prV : VZ ⟶ V)
    (hβ : IsPullback β (yoneda.map prV) (pullback.fst f gZ) a)
    (k : T₀ ⟶ VZ) [Mono k]
    (hk : Subfunctor.range (yoneda.map k) =
      schemeTheoreticImageSubfunctor B S hS (pullback.snd s β)) :
    ∃ χ : yoneda.obj T₀ ⟶ (schemeTheoreticImageSubfunctor B S hS s).toFunctor,
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf χ ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf χ ∧
      χ ≫ (schemeTheoreticImageSubfunctor B S hS s).ι = yoneda.map k ≫ β ∧
      IsPullback χ (yoneda.map (k ≫ prV))
        ((schemeTheoreticImageSubfunctor B S hS s).ι ≫ pullback.fst f gZ) a := by
  set T := schemeTheoreticImageSubfunctor B S hS s with hTdef
  have hY := isAlgebraicSpace_yoneda B S hS (Over.mk (𝟙 (B.obj hS)))
  have hZa := isAlgebraicSpace_yoneda B S hS Z
  have hXZ : IsAlgebraicSpace B S hS (pullback f gZ) :=
    isAlgebraicSpace_pullback B S hS f gZ X.2 hZa hY
  set QE := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS) with hQE
  set QS := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS) with hQS
  have hQEbc : QE.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hQSbc : QS.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hβE : QE.presheaf β := hQEbc.of_isPullback hβ.flip haet
  have hβS : QS.presheaf β := hQSbc.of_isPullback hβ.flip hasurj
  have hβet : IsEtale B S hS β := isEtale_of_presheaf_etale B S hS hβE
  -- Stacks 082Z: the inverse image of `T` in the chart is the range of `k`
  have hpre : T.preimage β = Subfunctor.range (yoneda.map k) := by
    rw [hk, hTdef]
    exact (schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact' B S hS s β
      (isAlgebraicSpace_yoneda B S hS D) hXZ (isAlgebraicSpace_yoneda B S hS VZ) hs hβet).symm
  have hsqT := Subfunctor.isPullback_preimage β T
  have hfpE : QE.presheaf (T.fromPreimage β) := hQEbc.of_isPullback hsqT.flip hβE
  have hfpS : QS.presheaf (T.fromPreimage β) := hQSbc.of_isPullback hsqT.flip hβS
  have : Mono (yoneda.map k) := inferInstance
  set e : yoneda.obj T₀ ⟶ (T.preimage β).toFunctor :=
    Subfunctor.toRange (yoneda.map k) ≫ Subfunctor.homOfLe hpre.ge with hedef
  have heι : e ≫ (T.preimage β).ι = yoneda.map k := by
    rw [hedef, Category.assoc, Subfunctor.homOfLe_ι, Subfunctor.toRange_ι]
  have hiso2 : IsIso (Subfunctor.homOfLe hpre.ge) :=
    ⟨Subfunctor.homOfLe hpre.le, by rw [← cancel_mono (Subfunctor.range (yoneda.map k)).ι]; simp,
      by rw [← cancel_mono (T.preimage β).ι]; simp⟩
  have : IsIso e := by rw [hedef]; infer_instance
  refine ⟨e ≫ T.fromPreimage β, (MorphismProperty.RespectsIso.precomp _ e _) hfpE,
    (MorphismProperty.RespectsIso.precomp _ e _) hfpS, ?_, ?_⟩
  · rw [Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc, heι]
  · have h1 : IsPullback e (yoneda.map k) (T.preimage β).ι (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, heι]⟩
    have h2 := h1.paste_horiz hsqT
    rw [Category.id_comp] at h2
    have h3 := h2.paste_vert hβ
    rwa [← yoneda.map_comp] at h3

/-- **The closure of a graph which is flat over a scheme on one chart is open in it.** -/
theorem C1573.isOpenImmersion_schemeTheoreticImage_of_flat_chart (X : AlgebraicSpaces B S hS)
    (f : X.1 ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))))
    (hsep : IsSeparated B S hS f) (hlft : IsLocallyOfFiniteType B S hS f)
    {D Z V VZ T₀ : BigFppfOver B S hS} (gZ : yoneda.obj Z ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))))
    (u : yoneda.obj D ⟶ X.1) (j : D ⟶ Z)
    (hj : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j))
    (hjqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map j))
    (hjdom : IsSchemeTheoreticallyDominant ((BigFppfOver.toScheme B S hS).map j))
    (hs : IsQuasiCompact B S hS (pullback.lift u (yoneda.map j)
      ((isTerminal_yoneda_obj_base B S hS).hom_ext _ _) :
        yoneda.obj D ⟶ pullback f gZ))
    (a : yoneda.obj V ⟶ X.1)
    (hasurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haet : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (β : yoneda.obj VZ ⟶ pullback f gZ) (prV : VZ ⟶ V) (prZ : VZ ⟶ Z)
    (hβ : IsPullback β (yoneda.map prV) (pullback.fst f gZ) a)
    (hβZ : β ≫ pullback.snd f gZ = yoneda.map prZ)
    (k : T₀ ⟶ VZ) [Mono k]
    (hk : Subfunctor.range (yoneda.map k) = schemeTheoreticImageSubfunctor B S hS
      (pullback.snd (pullback.lift u (yoneda.map j)
          ((isTerminal_yoneda_obj_base B S hS).hom_ext _ _) :
            yoneda.obj D ⟶ pullback f gZ) β))
    (hflat : AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map (k ≫ prZ))) :
    IsOpenImmersion B S hS ((schemeTheoreticImageSubfunctor B S hS (pullback.lift u (yoneda.map j)
      ((isTerminal_yoneda_obj_base B S hS).hom_ext _ _) :
        yoneda.obj D ⟶ pullback f gZ)).ι ≫ pullback.snd f gZ) := by
  set s : yoneda.obj D ⟶ pullback f gZ :=
    pullback.lift u (yoneda.map j) ((isTerminal_yoneda_obj_base B S hS).hom_ext _ _) with hsdef
  set T := schemeTheoreticImageSubfunctor B S hS s with hTdef
  have hY := isAlgebraicSpace_yoneda B S hS (Over.mk (𝟙 (B.obj hS)))
  have hZa := isAlgebraicSpace_yoneda B S hS Z
  have hXZ : IsAlgebraicSpace B S hS (pullback f gZ) :=
    isAlgebraicSpace_pullback B S hS f gZ X.2 hZa hY
  have hTc : IsClosedSubspace B S hS T :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS s hXZ
  -- the open `D ⊆ Z` and the section over it
  set W : Subfunctor (yoneda.obj Z) := Subfunctor.range (yoneda.map j) with hWdef
  have hjo : IsOpenImmersion B S hS (yoneda.map j) := isOpenImmersion_yoneda_map B S hS j hj
  have hW : IsOpenSubspace B S hS W := isOpenSubspace_range_of_isOpenImmersion D (yoneda.map j) hjo
  set eW := rangeIsoOfIsOpenImmersion D (yoneda.map j) hjo with heW
  have heWι : eW.hom ≫ W.ι = yoneda.map j := Subfunctor.toRange_ι _
  set s' : W.toFunctor ⟶ pullback f gZ := eW.inv ≫ s with hs'def
  have hs' : s' ≫ pullback.snd f gZ = W.ι := by
    rw [hs'def, Category.assoc, pullback.lift_snd]
    exact (Iso.inv_comp_eq _).2 heWι.symm
  have hrange : Subfunctor.range s' = Subfunctor.range s := by
    have : Epi eW.inv := IsIso.epi_of_iso eW.inv
    rw [hs'def, Subfunctor.range_comp, Subfunctor.range_eq_top, Subfunctor.image_top]
  have hTs' : schemeTheoreticImageSubfunctor B S hS s' = T :=
    schemeTheoreticImageSubfunctor_congr_range' B S hS s' s hXZ hrange
  have hWqc : IsQuasiCompact B S hS W.ι := by
    have h1 : IsQuasiCompact B S hS (yoneda.map j) := isQuasiCompact_yoneda_map B S hS j hjqc
    have h2 : eW.inv ≫ yoneda.map j = W.ι ≫ 𝟙 _ := by
      rw [Category.comp_id]; exact (Iso.inv_comp_eq _).2 heWι.symm
    exact isQuasiCompact_of_isPullback B S hS
      (IsPullback.of_horiz_isIso (fst := eW.inv) (snd := W.ι) (f := yoneda.map j)
        (g := 𝟙 _) ⟨h2⟩) h1
  -- Stacks 0CP3: the projection is an isomorphism over `D`
  have hsepZ : IsSeparated B S hS (pullback.snd f gZ) := isSeparated_pullback B S hS f gZ hsep
  have hiso : IsIso (pullback.snd (T.ι ≫ pullback.snd f gZ) W.ι) := by
    have h := isIso_pullback_snd_schemeTheoreticImageSubfunctor_comp_of_section B S hS hXZ hZa
      (pullback.snd f gZ) hsepZ W hW hWqc s' hs'
    rwa [hTs'] at h
  -- density of `D` in `Z`
  have hWdense : IsSchemeTheoreticallyDense B S hS W := by
    have : Mono (yoneda.map j) := mono_of_presheaf_isOpenImmersion hjo
    exact @isSchemeTheoreticallyDense_range_of_qc_or_reduced B S hS (yoneda.obj Z) (yoneda.obj D)
      (isAlgebraicSpace_yoneda B S hS D) hZa (yoneda.map j) this
      (.inl (isQuasiCompact_yoneda_map B S hS j hjqc))
      (schemeTheoreticImageSubfunctor_eq_top_of_isSchemeTheoreticallyDominant B S hS j hjdom)
  -- separated and locally of finite type
  have hTsep : IsSeparated B S hS (T.ι ≫ pullback.snd f gZ) :=
    isSeparated_comp B S hS _ _ (isSeparated_of_isClosedImmersion B S hS _ hTc.2) hsepZ
  have hlftZ : IsLocallyOfFiniteType B S hS (pullback.snd f gZ) :=
    IsLocallyOfFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback f gZ).flip X.2 hY hlft
  have hTlft : IsLocallyOfFiniteType B S hS (T.ι ≫ pullback.snd f gZ) :=
    isLocallyOfFiniteType_comp B S hS hTc.1 hXZ hZa _ _
      (isLocallyOfFiniteType_of_isClosedImmersion B S hS _ hTc.2) hlftZ
  -- flatness, on the chart
  have hTflat : IsFlat B S hS (T.ι ≫ pullback.snd f gZ) := by
    set QE := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) with hQE
    set QS := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) with hQS
    obtain ⟨χ, hχE, hχS, hχι, -⟩ := exists_chart_schemeTheoreticImage X f gZ s hs a hasurj
      haet β prV hβ k hk
    have hidE : QE.presheaf (𝟙 (yoneda.obj Z)) := by
      have _ : MorphismProperty.ContainsIdentities (@Etale.{u} : MorphismProperty Scheme.{u}) :=
        MorphismProperty.IsMultiplicative.toContainsIdentities
      have _ : MorphismProperty.ContainsIdentities QE :=
        MorphismProperty.ContainsIdentities.inverseImage (BigFppfOver.toScheme B S hS)
      have _ : MorphismProperty.RespectsIso QE :=
        MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme B S hS)
      exact MorphismProperty.presheaf_of_isIso _ (𝟙 (yoneda.obj Z))
    have hcomm : yoneda.map (k ≫ prZ) ≫ 𝟙 _ = χ ≫ (T.ι ≫ pullback.snd f gZ) := by
      rw [Category.comp_id, ← Category.assoc, hχι, Category.assoc, hβZ, yoneda.map_comp]
    exact holdsOnEveryEtaleChart_of_surjectiveChart B S hS _
      AlgebraicGeometry.isEtaleLocalOnSourceAndTarget_flat
      ⟨T₀, Z, χ, 𝟙 _, _, hχE, hidE, hχS, hcomm, hflat⟩
  exact isOpenImmersion_of_isIso_pullback_snd B S hS hTc.1 hZa _ W hW hTsep hTlft hTflat hiso
    hWqc hWdense

end AlgebraicGeometry.Space

end
