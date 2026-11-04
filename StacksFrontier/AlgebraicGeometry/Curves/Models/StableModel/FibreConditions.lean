module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.Reduction
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.FamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Curves.IsNode
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.NodalSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.AutomaticProperties
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesStable
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.Glueing.FibreTransport

/-!
# Fibrewise conditions for a model over a discrete valuation ring

Let `R` be a discrete valuation ring with fraction field `K` and residue field `k`, and let
`p : Y ⟶ Spec R` be a proper model of a smooth projective curve `C` over `K` with `H⁰(C, 𝒪) = K`
and genus `g ≥ 2`, whose special fibre `Y_k` is isomorphic over `k` to a proper nodal curve `Y₀`
of dimension one with `H⁰(Y₀, 𝒪) = k`, genus `g`, and neither rational tails nor rational bridges.
Then `p` is at-worst-nodal of relative dimension one (the fibrewise criterion of
[Stacks, Tag 0C59]) and both of its fibres are stable curves of genus `g`. The fibre at a point of
`Spec R` is compared with the generic fibre `C`, respectively the special fibre `Y₀`, through the
identification of the residue field of `Spec R` at that point with `K`, respectively `k`; the
generic fibre, smooth with `H⁰ = K`, is irreducible and so has neither rational tails nor rational
bridges.

## Main results

* `Stacks.Models.fibre_conditions_of_iso_pullback`: the fibre conditions at the image of a
  field-valued point inducing an isomorphism of residue fields, read off from a scheme isomorphic
  to the base change along that point.
* `Stacks.Models.eq_specMap_algebraMap_fraction_or_residueField`: the two points of `Spec R`.
* `Stacks.Models.isAtWorstNodal_and_isStableFibreOfGenus_of_fibres`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models

/-- **The fibre conditions at the image of a field-valued point.** Let `p : Y ⟶ S`, let
`j : Spec F ⟶ S` be a field-valued point inducing an isomorphism of residue fields at its image
`t`, and let `v : V ⟶ Spec F` be isomorphic over `F` to the base change of `p` along `j`. If `V`
is proper of dimension one over `F` with `H⁰(V, 𝒪) = F`, at-worst-nodal singularities, genus `g`,
genus at least two and neither rational tails nor rational bridges, then the fibre of `p` over `t`
is equidimensional of dimension one with at-worst-nodal singularities over `κ(t)`, and is a stable
curve of genus `g`. -/
theorem fibre_conditions_of_iso_pullback {Y S V : Scheme.{u}} (p : Y ⟶ S) {F : Type u} [Field F]
    (j : Spec (.of F) ⟶ S) [IsIso (S.descResidueField (Scheme.stalkClosedPointTo j))]
    (v : V ⟶ Spec (.of F)) (ε : V ≅ pullback p j) (hε : ε.hom ≫ pullback.snd p j = v)
    [IsProper v] (hdim : topologicalKrullDim V = 1)
    (hΓ : IsIso ((Scheme.ΓSpecIso (.of F)).inv ≫ v.appTop))
    (hnodal : letI : V.Over (Spec (.of F)) := ⟨v⟩;
      Stacks.Curves.HasAtWorstNodalSingularities F V)
    (g : ℕ) (hst : HasGenusTwoNoRationalTailNoRationalBridge F v) (hgen : genus v = g) :
    (letI : (p.fiber (j (IsLocalRing.closedPoint F))).Over
        (Spec (.of (S.residueField (j (IsLocalRing.closedPoint F))))) :=
        ⟨p.fiberToSpecResidueField _⟩;
      TopologicalSpace.Equidimensional (p.fiber (j (IsLocalRing.closedPoint F))) ∧
        topologicalKrullDim (p.fiber (j (IsLocalRing.closedPoint F))) = (1 : WithBot ℕ∞) ∧
          Stacks.Curves.HasAtWorstNodalSingularities
            (S.residueField (j (IsLocalRing.closedPoint F)))
            (p.fiber (j (IsLocalRing.closedPoint F)))) ∧
      IsStableFibreOfGenus g p (j (IsLocalRing.closedPoint F)) := by
  obtain ⟨E, -, hE⟩ := exists_iso_fiber_pullback_of_isIso_descResidueField p j
  set φ := S.descResidueField (Scheme.stalkClosedPointTo j)
  have hφ : IsIso φ := inferInstanceAs (IsIso (S.descResidueField (Scheme.stalkClosedPointTo j)))
  -- the fibre is isomorphic to `V`, over the isomorphism of fields `φ`
  have hw : (ε.hom ≫ E.inv) ≫ p.fiberToSpecResidueField _ = v ≫ Spec.map φ := by
    rw [← hE, ← hε]
    simp
  have hw' : (E.hom ≫ ε.inv) ≫ v ≫ Spec.map φ = p.fiberToSpecResidueField _ := by
    rw [← hE, ← hε]
    simp
  have hhomeo := Scheme.homeoOfIso (E ≪≫ ε.symm)
  have hequi : TopologicalSpace.Equidimensional V :=
    have := hΓ
    equidimensional_of_isIso_globalSections_of_dimension_one F v hdim
  refine ⟨⟨hequi.of_homeomorph hhomeo, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [IsHomeomorph.topologicalKrullDim_eq _ hhomeo.isHomeomorph, hdim]
  · exact @Stacks.Curves.hasAtWorstNodalSingularities_of_isIso _ _ _ _ _ _ v _ _ hdim
      (E.hom ≫ ε.inv) _ φ hφ hw' hnodal
  · exact @isIso_ΓSpecIso_inv_comp_appTop_of_iso _ _ _ _ φ hφ _ _ _ v (ε.hom ≫ E.inv) _ hw hΓ
  · exact @HasGenusTwoNoRationalTailNoRationalBridge.of_iso _ _ _ _ φ hφ _ _ _ v
      (ε.hom ≫ E.inv) _ hw hst
  · exact (@genus_eq_of_iso _ _ _ _ φ hφ _ _ _ v (ε.hom ≫ E.inv) _ hw _).trans hgen

/-- **The two points of the spectrum of a discrete valuation ring.** Every point of `Spec R` is
the image of `Spec K` (the generic point) or of `Spec k` (the closed point). -/
theorem eq_specMap_algebraMap_fraction_or_residueField (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (t : Spec (.of R)) :
    t = (Spec.map (CommRingCat.ofHom (algebraMap R K))) (IsLocalRing.closedPoint K) ∨
      t = (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))))
        (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) := by
  have hker (L : Type u) [Field L] [Algebra R L] :
      ((Spec.map (CommRingCat.ofHom (algebraMap R L))) (IsLocalRing.closedPoint L)).asIdeal =
        RingHom.ker (algebraMap R L) := by
    change Ideal.comap (algebraMap R L) (IsLocalRing.maximalIdeal L) = _
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  obtain ht | ht := em (t.asIdeal = ⊥)
  · exact Or.inl (PrimeSpectrum.ext (ht.trans ((hker K).trans
      ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K))).symm))
  · exact Or.inr (PrimeSpectrum.ext ((IsLocalRing.eq_maximalIdeal (t.isPrime.isMaximal ht)).trans
      ((hker (IsLocalRing.ResidueField R)).trans IsLocalRing.ker_residue).symm))

/-- **The fibrewise criterion for a stable model over a discrete valuation ring.** -/
theorem isAtWorstNodal_and_isStableFibreOfGenus_of_fibres
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {C Y Y₀ : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c]
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] (hg : 2 ≤ genus c)
    (p : Y ⟶ Spec (.of R)) [IsProper p]
    (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (hmod : IsModel c p e)
    (g₀ : Y₀ ⟶ Spec (.of (IsLocalRing.ResidueField R)))
    (e₀ : pullback p (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))) ≅
      Y₀)
    (he₀ : e₀.hom ≫ g₀ = pullback.snd _ _) (hproper₀ : IsProper g₀)
    (hdim₀ : topologicalKrullDim Y₀ = 1)
    (hglobal₀ : IsIso ((Scheme.ΓSpecIso (.of (IsLocalRing.ResidueField R))).inv ≫ g₀.appTop))
    (hnodal₀ : letI : Y₀.Over (Spec (.of (IsLocalRing.ResidueField R))) := ⟨g₀⟩;
      Stacks.Curves.HasAtWorstNodalSingularities (IsLocalRing.ResidueField R) Y₀)
    (hgenus₀ : genus g₀ = genus c)
    (hstable₀ : HasGenusTwoNoRationalTailNoRationalBridge (IsLocalRing.ResidueField R) g₀) :
    IsAtWorstNodalOfRelativeDimensionOne p ∧ ∀ s, IsStableFibreOfGenus (genus c) p s := by
  obtain ⟨hflat, hlft, -, hc⟩ := hmod
  have := hflat
  have := hlft
  have := isIso_descResidueField_algebraMap_of_isFractionRing R K
  have := isIso_descResidueField_of_surjective (algebraMap R (IsLocalRing.ResidueField R))
    IsLocalRing.residue_surjective
  -- the generic fibre `C`
  have : IsProper c := by
    rw [← hc]
    infer_instance
  have hΓC : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop) := inferInstance
  have hC := fibre_conditions_of_iso_pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))) c
    e hc (IsCurve.topologicalKrullDim_eq_one (f := c)) hΓC
    (by
      let : C.Over (Spec (.of K)) := ⟨c⟩
      have : Smooth (C ↘ Spec (.of K)) := inferInstanceAs (Smooth c)
      exact Stacks.Curves.hasAtWorstNodalSingularities_of_smooth K C) (genus c)
    (by
      let : C.Over (Spec (.of K)) := ⟨c⟩
      have : IsProper (C ↘ Spec (.of K)) := inferInstanceAs (IsProper c)
      have : IrreducibleSpace C := irreducibleSpace_of_smooth_of_isIso_appTop K c hΓC
      exact ⟨hg, fun D => not_isRationalTail_of_irreducibleSpace K C D,
        inferInstanceAs (IsProper c), fun D => not_isRationalBridge_of_irreducibleSpace K C D⟩)
    rfl
  -- the special fibre `Y₀`
  have hk := fibre_conditions_of_iso_pullback p
    (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))) g₀ e₀.symm
    (by rw [Iso.symm_hom, ← he₀, Iso.inv_hom_id_assoc]) hdim₀ hglobal₀ hnodal₀ (genus c)
    hstable₀ hgenus₀
  refine ⟨(Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff p).1
    ⟨hflat, inferInstance, fun t _ => ?_⟩, fun t => ?_⟩ <;>
  rcases eq_specMap_algebraMap_fraction_or_residueField R K t with rfl | rfl
  exacts [hC.1, hk.1, hC.2, hk.2]

end Stacks.Models

end
