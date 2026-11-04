module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationSquareGeometry
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# Approximation on the affine member of an elementary distinguished square

Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces with `V`
affine and `U ×_X V` quasi-compact, and let `T ⊆ |X|` be closed with quasi-compact open
complement.  Set `T' = T ∖ |U|`.  This file provides the integer `r'` of the base case of the
proof of Stacks 08HN: approximation holds on `V` for every triple `(j^{-1}T', E, m)` with `E`
`(m - r')`-pseudo-coherent and `Hⁱ(E)` supported on `j^{-1}T'` for `i ≥ m - r'`.

The source takes `r'` to be the number of affines needed to cover `V ∖ j^{-1}T'` and applies the
first assertion of Stacks 08HM; we apply instead the second assertion of Stacks 08EQ to the affine
scheme `V₀` with `V ≅ h_{V₀}`, at the closed set `Z₀` corresponding to `j^{-1}T'`.  Its complement
is quasi-compact, being the union of the parts lying over `X ∖ T` and over `U`: the first is
quasi-compact because `X ∖ T ⟶ X` is quasi-compact (Stacks 03HF), the second is the image of
`U ×_X V`, which is quasi-compact by hypothesis.  This is the source's observation that
`V ∖ j^{-1}(T')` is quasi-compact.

## Main results

* `AlgebraicGeometry.Space.exists_approximation_edsEtale`

## References

* [Stacks Project, Tag 08HN](https://stacks.math.columbia.edu/tag/08HN)
* [Stacks Project, Tag 08HM](https://stacks.math.columbia.edu/tag/08HM)
* [Stacks Project, Tag 08EQ](https://stacks.math.columbia.edu/tag/08EQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

attribute [local instance] pointTopology

variable {W : AlgebraicSpaces B S hS} {Ve : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : Ve ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **The base case of Stacks 08HN on the affine member.**  For `T ⊆ |X|` closed with
quasi-compact open complement there is an integer `r` such that approximation holds on `V` for
every triple `(j^{-1}(T ∖ |U|), E, m)` with `E` `(m - r)`-pseudo-coherent and `Hⁱ(E)` supported on
`j^{-1}(T ∖ |U|)` for `i ≥ m - r`. -/
theorem exists_approximation_edsEtale (hVaff : IsAffineSpace B S hS Ve)
    (hUVqc : IsQuasiCompactSpace B S hS (edsInter B S hS hsq).1)
    (T : Set (points B S hS W.1)) (hT : IsClosed T)
    (hTqc : IsQuasiCompact B S hS
      ((openSubspacesOrderIso B S hS W.1 W.2).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι) :
    ∃ r : ℤ, ∀ (E : QuasicoherentDerivedCategory.{u, u} B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2) (m : ℤ),
      (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2).IsPseudoCoherentFrom E.obj (m - r) →
      (∀ i : ℤ, m - r ≤ i →
        supportOfSheaf B S hS (edsEtale B S hS hsq).1
          ((SheafOfModules.toSheaf
              ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
                (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2).O))).obj
            ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
              (edsEtale B S hS hsq).2) i).obj E.obj)) ⊆
          pointsMap B S hS (edsEtale B S hS hsq).1 (edsEtaleHom B S hS hsq).hom ⁻¹'
            (T ∩ edsComplementPoints B S hS Uo)) →
      ApproximationHolds B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
        (pointsMap B S hS (edsEtale B S hS hsq).1 (edsEtaleHom B S hS hsq).hom ⁻¹'
          (T ∩ edsComplementPoints B S hS Uo)) E m := by
  obtain ⟨V₀, hV₀, O, hO, eV, eI, hcomm⟩ := exists_eds_represented B S hS hsq hVaff hUVqc
  have := hV₀
  set Z := pointsMap B S hS (edsEtale B S hS hsq).1 (edsEtaleHom B S hS hsq).hom ⁻¹'
    (T ∩ edsComplementPoints B S hS Uo) with hZdef
  set Zh := pointsMap B S hS (yoneda.obj V₀) eV.inv.hom ⁻¹' Z with hZhdef
  have hZcl : IsClosed Z :=
    (hT.inter hsq.isClosedComplement).preimage (continuous_pointsMap B S hS _)
  have hZhcl : IsClosed Zh := hZcl.preimage (continuous_pointsMap B S hS _)
  have hZ₀cl : IsClosed (schemePointsHomeomorph B S hS V₀ '' Zh) :=
    (schemePointsHomeomorph B S hS V₀).isClosed_image.2 hZhcl
  have hZhc : IsCompact Zhᶜ := by
    have hsplit : Zhᶜ = pointsMap B S hS (yoneda.obj V₀)
          (eV.inv.hom ≫ (edsEtaleHom B S hS hsq).hom) ⁻¹' Tᶜ ∪
        pointsMap B S hS (yoneda.obj V₀) (eV.inv.hom ≫ (edsEtaleHom B S hS hsq).hom) ⁻¹'
          Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) := by
      rw [hZhdef, hZdef, ← Set.preimage_comp, ← pointsMap_comp, ← Set.preimage_compl,
        ← Set.preimage_union, Set.compl_inter, edsComplementPoints, compl_compl]
    rw [hsplit]
    refine IsCompact.union ?_ ?_
    · let G := (openSubspacesOrderIso B S hS W.1 W.2).symm ⟨Tᶜ, hT.isOpen_compl⟩
      have h₁ := isCompact_preimage_range_of_isQuasiCompact B S hS W.2
        (isAlgebraicSpace_yoneda B S hS V₀) (isQuasiCompactSpace_yoneda_of_isAffine B S hS V₀ hV₀)
        (eV.inv.hom ≫ (edsEtaleHom B S hS hsq).hom) G.1 G.2 hTqc
      rwa [range_openSubspacesOrderIso_symm B S hS W.1 W.2 T hT] at h₁
    · have := compactSpace_points_of_isQuasiCompactSpace B S hS (edsInter B S hS hsq).2 hUVqc
      have hset : pointsMap B S hS (yoneda.obj V₀) (eV.inv.hom ≫ (edsEtaleHom B S hS hsq).hom) ⁻¹'
          Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) =
          Set.range (pointsMap B S hS (edsInter B S hS hsq).1
            ((edsSnd B S hS hsq).hom ≫ eV.hom.hom)) := by
        have hc := pullback.condition (f := (edsOpenHom B S hS hsq).hom)
          (g := (edsEtaleHom B S hS hsq).hom)
        ext p
        constructor
        · rintro ⟨w, hw⟩
          obtain ⟨v, -, hv₂⟩ := exists_points_of_isPullback B S hS
            (IsPullback.of_hasPullback (edsOpenHom B S hS hsq).hom (edsEtaleHom B S hS hsq).hom) w
            (pointsMap B S hS (yoneda.obj V₀) eV.inv.hom p)
            (hw.trans (pointsMap_comp_apply B S hS _ _ p))
          exact ⟨v, (pointsMap_comp_apply B S hS _ _ v).trans
            ((congrArg (pointsMap B S hS _ eV.hom.hom) hv₂).trans
              (pointsMap_inv_pointsMap_hom B S hS eV.symm p))⟩
        · rintro ⟨v, rfl⟩
          refine ⟨pointsMap B S hS (edsInter B S hS hsq).1
            (pullback.fst (edsOpenHom B S hS hsq).hom (edsEtaleHom B S hS hsq).hom) v, ?_⟩
          refine (pointsMap_apply_comm B S hS hc v).trans ?_
          rw [pointsMap_comp_apply, pointsMap_comp_apply]
          exact congrArg _ (pointsMap_inv_pointsMap_hom B S hS eV _).symm
      rw [hset]
      exact isCompact_range (continuous_pointsMap B S hS _)
  have hZ₀c : IsCompact (schemePointsHomeomorph B S hS V₀ '' Zh)ᶜ := by
    rw [← Set.image_compl_eq (schemePointsHomeomorph B S hS V₀).bijective]
    exact hZhc.image (schemePointsHomeomorph B S hS V₀).continuous
  obtain ⟨r, hr⟩ := PerfectApproximation.approximationByPerfectComplexes_of_isAffine _ _ hZ₀cl
    (hZ₀c.isRetrocompact hZ₀cl.isOpen_compl)
  refine ⟨r, fun E m hpc hsupp => approximationHolds_of_iso B S hS eV Z E m ?_⟩
  have hsupp' : ∀ i : ℤ, m - r ≤ i →
      supportOfSheaf B S hS (yoneda.obj V₀) ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS (yoneda.obj V₀)
          (isAlgebraicSpace_yoneda B S hS V₀)) i).obj (isoQcohTransport B S hS eV E).obj)) ⊆
        Zh := fun i hi p hp =>
    hsupp i hi ((Set.ext_iff.1 (supportOfSheaf_homology_isoQcohTransport B S hS eV E i) p).1 hp)
  obtain ⟨E₀, hqc₀, ⟨eE⟩⟩ := exists_representedDerivedAssociatedModule_iso B S hS V₀
    (isoQcohTransport B S hS eV E).obj (isoQcohTransport B S hS eV E).property
  obtain ⟨K, hK, ⟨f⟩⟩ := isPseudoCoherentFrom_isoQcohTransport B S hS eV E (m - r) hpc
  exact approximationHolds_of_approximationHolds_scheme B S hS V₀ Zh _ m E₀ eE
    (hr E₀ m hqc₀ (isPseudoCoherentFrom_of_representedDerivedAssociatedModule B S hS V₀ E₀ (m - r)
      ⟨K, hK, ⟨f ≪≫ eE.symm⟩⟩) fun i x hi hx =>
        isZero_stalk_homology_of_supportOfSheaf_subset B S hS V₀ _ E₀ eE hqc₀ Zh i
          (hsupp' i hi) x hx)

end AlgebraicGeometry.Space
