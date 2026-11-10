module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NodalResolution
public import StacksFrontier.AlgebraicGeometry.Curves.Models.Reduction
public import StacksFrontier.AlgebraicGeometry.RestrictIso
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-!
# A curve with semistable reduction has a regular nodal proper model

Let `R` be a discrete valuation ring with fraction field `K` and let `C` be a smooth projective
curve over `K` with `H⁰(C, 𝒪_C) = K`. If `C` has a proper model `X` over `R` which is
at-worst-nodal of relative dimension one, then it has one whose total space is moreover regular:
resolve `X` by blowups at its singular points ([Stacks, Tag 0CDE]). This is the first step of the
proof of (1) ⇒ (2) in [Stacks, Tag 0CDG].

The singular points of `X` lie in the special fibre, because the generic fibre is `C`, which is
smooth over `K`, hence regular. So the blowups are isomorphisms over the generic fibre, and the
resolution is again a model of `C`.

## Main results

* `Stacks.Models.exists_isModel_comp_of_isIso_morphismRestrict` — a morphism to a model of `C`
  which is an isomorphism over the generic fibre, and whose composite to `Spec R` is flat, locally
  of finite type and quasi-compact, is again a model of `C`.
* `Stacks.Models.isRegularLocalRing_stalk_of_isModel` — the total space of a model of a smooth
  curve is regular at every point of the generic fibre.
* `Stacks.Models.exists_isModel_isProper_isRegular_isAtWorstNodal` — a curve with semistable
  reduction has a regular proper model which is at-worst-nodal of relative dimension one.

## References

* [Stacks Project, Tag 0CDG](https://stacks.math.columbia.edu/tag/0CDG)
* [Stacks Project, Tag 0CDE](https://stacks.math.columbia.edu/tag/0CDE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace IsLocalRing

universe u

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

attribute [local instance] genericFiberSpec_isOpenImmersion

/-- **A modification which is an isomorphism over the generic fibre preserves models.** Let
`p : X ⟶ Spec R` be a model of `C` and `b : Y ⟶ X` a morphism which is an isomorphism over the
generic fibre `p⁻¹(Spec K)`, with `b ≫ p` flat, locally of finite type and quasi-compact. Then
`b ≫ p` is a model of `C`, the identification of its generic fibre with `C` being the given one
followed by `b` over the generic fibre. -/
public theorem exists_isModel_comp_of_isIso_morphismRestrict {C X Y : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) (p : X ⟶ Spec (.of R))
    (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hmod : IsModel c p e) (b : Y ⟶ X)
    (hb : IsIso (b ∣_ (p ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (algebraMap R K))).opensRange)))
    [Flat (b ≫ p)] [LocallyOfFiniteType (b ≫ p)] [QuasiCompact (b ≫ p)] :
    ∃ e' : C ≅ pullback (b ≫ p) (Spec.map (CommRingCat.ofHom (algebraMap R K))),
      IsModel c (b ≫ p) e' := by
  obtain ⟨-, -, -, hc⟩ := hmod
  let ι := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let V : X.Opens := p ⁻¹ᵁ ι.opensRange
  let eg : pullback p ι ≅ V.toScheme :=
    IsOpenImmersion.isoOfRangeEq (pullback.fst p ι) V.ι (by
      rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.range_ι])
  let ep : pullback (b ≫ p) ι ≅ (b ⁻¹ᵁ V).toScheme :=
    IsOpenImmersion.isoOfRangeEq (pullback.fst (b ≫ p) ι) (b ⁻¹ᵁ V).ι (by
      rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.range_ι]
      rfl)
  let m : pullback (b ≫ p) ι ⟶ pullback p ι :=
    pullback.map (b ≫ p) ι p ι b (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hm : m = ep.hom ≫ (b ∣_ V) ≫ eg.inv := by
    rw [← cancel_mono (pullback.fst p ι)]
    simp [m, ep, eg, morphismRestrict_ι]
  have : IsIso m := by
    rw [hm]
    infer_instance
  refine ⟨e ≪≫ (asIso m).symm, inferInstance, inferInstance, inferInstance, ?_⟩
  have hms : inv m ≫ pullback.snd (b ≫ p) ι = pullback.snd p ι := by
    rw [IsIso.inv_comp_eq]
    simp [m]
  rw [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, hms]
  exact hc

/-- The points of `Spec R` other than the closed point are in the image of the generic fibre
`Spec K ⟶ Spec R`. -/
private theorem mem_range_genericFiberSpec (s : Spec (.of R)) (hs : s ≠ closedPoint R) :
    s ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R K))).base := by
  have h0 : s.asIdeal = ⊥ := by
    by_contra h0
    exact hs (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
      (Ring.DimensionLEOne.maximalOfPrime h0 s.isPrime)))
  refine ⟨closedPoint K, PrimeSpectrum.ext ?_⟩
  change Ideal.comap (algebraMap R K) (maximalIdeal K) = s.asIdeal
  rw [h0, IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R K)

/-- **The total space of a model of a smooth curve is regular along the generic fibre**: the
generic fibre is an open subscheme isomorphic to the curve, which is smooth over a field, hence
regular. -/
public theorem isRegularLocalRing_stalk_of_isModel {C X : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [Smooth c] (p : X ⟶ Spec (.of R))
    (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (y : X) (hy : y ∈ p ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (algebraMap R K))).opensRange) :
    IsRegularLocalRing (X.presheaf.stalk y) := by
  let ι := Spec.map (CommRingCat.ofHom (algebraMap R K))
  obtain ⟨z, hz⟩ : y ∈ Set.range (pullback.fst p ι).base := by
    rwa [IsOpenImmersion.range_pullbackFst]
  have hz' : IsRegularLocalRing ((pullback p ι).presheaf.stalk z) := by
    have hz₀ : e.hom.base (e.inv.base z) = z := by
      rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
      rfl
    rw [← hz₀]
    exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion e.hom _).mp
      ((isRegular_of_smooth_over_field c).isRegularLocalRing_stalk _)
  rw [← hz]
  exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion (pullback.fst p ι) z).mp hz'

/-- **A curve with semistable reduction has a regular proper model which is at-worst-nodal of
relative dimension one.** Resolve a proper at-worst-nodal model by blowups at its singular points
([Stacks, Tag 0CDE]); the singular points lie in the special fibre, so the blowups are
isomorphisms over the generic fibre and the result is again a model. This is the first step of
the proof of (1) ⇒ (2) in [Stacks, Tag 0CDG]. -/
public theorem exists_isModel_isProper_isRegular_isAtWorstNodal {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c] (hc : IsProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)]
    (h : HasSemistableReduction R c hc) :
    ∃ (X : Scheme.{u}) (p : X ⟶ Spec (.of R))
      (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      IsModel c p e ∧ IsProper p ∧ IsRegular X ∧ IsAtWorstNodalOfRelativeDimensionOne p := by
  obtain ⟨X, p, e, hmod, hprop, hnod⟩ := h
  have : IsProper p := hprop
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hgen : ∀ y : X, p.base y ≠ closedPoint R → IsRegularLocalRing (X.presheaf.stalk y) :=
    fun y hy ↦ isRegularLocalRing_stalk_of_isModel c p e y (mem_range_genericFiberSpec _ hy)
  obtain ⟨Y, h, hchain, hreg⟩ :=
    Stacks.SemistableReduction.exists_nodalBlowupChain_isRegular_of_isRegularLocalRing p hnod hgen
  have hnod' := hchain.isAtWorstNodalOfRelativeDimensionOne hnod
  have : IsProper h := hchain.isProper
  have : Flat (h ≫ p) := flat hnod'.1.1
  obtain ⟨e', he'⟩ := exists_isModel_comp_of_isIso_morphismRestrict c p e hmod h
    (hchain.isIso_morphismRestrict _ (isRegularLocalRing_stalk_of_isModel c p e))
  exact ⟨Y, h ≫ p, e', he', inferInstance, hreg, hnod'⟩

end Stacks.Models

end
