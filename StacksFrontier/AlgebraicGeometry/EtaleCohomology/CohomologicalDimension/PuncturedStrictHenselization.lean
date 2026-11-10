module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.OpenImmersionHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.PuncturedLocalRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.EtaleLocalRingBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.SpecializationMorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedGeometricStalkSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionInverseImage
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.NormalLocalExactSequence
public import StacksFrontier.RingTheory.LocalRing.ResidueFieldTranscendence
public import StacksFrontier.RingTheory.NoetherNormalization.Basic

/-!
# Higher direct images along the complement of a divisor in an affine chart

Let `j : X ⟶ Y` be a quasi-compact open immersion and let `Spec R ⟶ Y` be an affine open chart,
with `R` a normal domain of finite transcendence degree `d` over a field `K`, in which `X` is the
basic open `D(t)`. Let `s` be a geometric point of `Y` lying over a point `y'` of the chart with
`t ∈ y'`, and let `a ≤ trdeg_K(R/y')`. Then `R^qj_*𝓕` has vanishing stalk at `s` for every torsion
abelian sheaf `𝓕` and every `q > d - a`, provided Stacks 0F0V is known in dimension at most
`d - a - 1`. This is Interlude I of the proof of Stacks 0F0V.

By Stacks 03Q9 the stalk is `H^q(X ×_Y Spec(𝒪^{sh}_{Y,s}), p⁻¹𝓕)`. The canonical morphism
`Spec(𝒪^{sh}_{Y,s}) ⟶ Y` is the spectrum of the composite `φ : R ⟶ R_{y'} ≅ 𝒪_{Y,y} ⟶ 𝒪^{sh}_{Y,s}`
followed by the chart, so the base change of `j` is `Spec(𝒪^{sh}_{Y,s})_{φ(t)}`. The ring
`𝒪^{sh}_{Y,s}` is a strictly henselian normal domain, algebraic over `R` (Stacks 06DI, a
henselization being ind-étale), so its transcendence degree over `K` is `d`; its residue field
contains `R/y'`, and `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_spec_away_le` bounds
the cohomological dimension of the localization.

## Main results

* `AlgebraicGeometry.chartToEtaleLocalRing`: the ring map `φ`.
* `AlgebraicGeometry.spec_chartToEtaleLocalRing_comp`: `Spec(φ)` followed by the chart is the
  canonical morphism from the strict henselization.

## References

* [Stacks Project, Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 06DI](https://stacks.math.columbia.edu/tag/06DI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

-- In this import closure two global instances make unrelated searches time out: every
-- `IsIntegral Y` goal is sent through `IsVariety.toIsIntegral` over all fields and morphisms, and
-- `Stacks.Chow.isIso_stalkMap_of_isDominant_of_isPreimmersion` matches every `IsIso` of a stalk
-- map and asks for `IsIntegral`. Neither is used here.
attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral
  Stacks.Chow.isIso_stalkMap_of_isDominant_of_isPreimmersion

/-- The Krull dimension of a nontrivial finite type algebra over a field bounds below its
transcendence degree, by Noether normalization. -/
private theorem natCast_le_trdeg_of_le_ringKrullDim {K T : Type u} [Field K] [CommRing T]
    [Nontrivial T] [Algebra K T] [Algebra.FiniteType K T] (a : ℕ)
    (h : (a : WithBot ℕ∞) ≤ ringKrullDim T) :
    (a : Cardinal) ≤ Algebra.trdeg K T := by
  obtain ⟨k, ν, hk, hν, -⟩ := noether_normalization_global (k := K) (T := T)
  have h' := lift_trdeg_le_of_injective ν hν
  simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin, Cardinal.lift_natCast,
    Cardinal.lift_id] at h'
  rw [← hk] at h
  exact (Nat.cast_le.mpr (by exact_mod_cast h)).trans h'

section Chart

variable (B : BigEtaleSite.{u}) {Y : Scheme.{u}} (hS : B.Contains Y) {R : CommRingCat.{u}}
  (ιV : Spec R ⟶ Y) [IsOpenImmersion ιV] (s : GeometricPoint Y) (y' : Spec R)
  (hy : ιV y' = s.hom (IsLocalRing.closedPoint s.residueField))

/-- The identification of the stalk of an affine chart at `y'` with the stalk of `Y` at the image
`s` of a geometric point, when the two points agree. -/
def affineChartStalkIso :
    (Spec R).presheaf.stalk y' ≅
      Y.presheaf.stalk (s.hom (IsLocalRing.closedPoint s.residueField)) :=
  (asIso (ιV.stalkMap y')).symm ≪≫ Y.presheaf.stalkCongr (Inseparable.of_eq hy)

/-- The ring map from the coordinate ring of an affine chart `Spec R ⟶ Y` to the étale local ring
of `Y` at a geometric point lying over the point `y'` of the chart: localization at `y'`, the
identification with the stalk of `Y`, and the map to the strict henselization. -/
def chartToEtaleLocalRing : R →+* ↥(etaleLocalRing B Y hS s) :=
  (structureSheafStalkFromLocalRing B Y hS s).comp
    (((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ y' trivial ≫
      (affineChartStalkIso ιV s y' hy).hom).hom)

/-- **The canonical morphism from the strict henselization factors through an affine chart.** -/
theorem spec_chartToEtaleLocalRing_comp :
    Spec.map (CommRingCat.ofHom (chartToEtaleLocalRing B hS ιV s y' hy)) ≫ ιV =
      strictHenselizationToBase B Y hS s := by
  have h3 : Y.fromSpecStalk (ιV y') =
      Spec.map (asIso (ιV.stalkMap y')).inv ≫ (Spec R).fromSpecStalk y' ≫ ιV := by
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk ιV (x := y'), ← Category.assoc, ← Spec.map_comp,
      asIso_inv, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  have hφ : CommRingCat.ofHom (chartToEtaleLocalRing B hS ιV s y' hy) =
      ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ y' trivial) ≫
        (asIso (ιV.stalkMap y')).inv ≫
        Y.presheaf.stalkSpecializes (Inseparable.of_eq hy).ge ≫
          CommRingCat.ofHom (structureSheafStalkFromLocalRing B Y hS s) := rfl
  rw [hφ, strictHenselizationToBase,
    ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := Y) (Inseparable.of_eq hy).ge, h3,
    Spec.fromSpecStalk_eq]
  simp only [Spec.map_comp, Category.assoc]
  conv_rhs => rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- The ring map `φ` contracts the maximal ideal of the étale local ring to the prime `y'`. -/
theorem comap_chartToEtaleLocalRing_maximalIdeal :
    (maximalIdeal ↥(etaleLocalRing B Y hS s)).comap (chartToEtaleLocalRing B hS ιV s y' hy) =
      y'.asIdeal := by
  have h := congrArg (fun g : strictHenselization B Y hS s ⟶ Y =>
    g (IsLocalRing.closedPoint ↥(etaleLocalRing B Y hS s)))
    (spec_chartToEtaleLocalRing_comp B hS ιV s y' hy)
  simp only [strictHenselizationToBase_closedPoint, ← hy] at h
  exact congrArg PrimeSpectrum.asIdeal (ιV.isOpenEmbedding.injective h)

/-- The base change of `j` to the strict henselization has image the basic open of `φ(t)`, when
`j` is the basic open `D(t)` in the chart. -/
private theorem range_strictHenselizationBaseChangeToStrictHenselization_of_chart {X : Scheme.{u}}
    (j : X ⟶ Y) (t : R) (ht : ∀ p : Spec R, ιV p ∈ Set.range j ↔ t ∉ p.asIdeal) :
    Set.range (strictHenselizationBaseChangeToStrictHenselization B hS j s) =
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap ↥(etaleLocalRing B Y hS s)
        (Localization.Away (chartToEtaleLocalRing B hS ιV s y' hy t))))) := by
  change Set.range (pullback.snd j (strictHenselizationToBase B Y hS s)) = _
  rw [Scheme.Pullback.range_snd]
  ext p
  simp only [Set.mem_preimage]
  rw [← spec_chartToEtaleLocalRing_comp B hS ιV s y' hy, Scheme.Hom.comp_apply, ht]
  change t ∉ (PrimeSpectrum.comap (chartToEtaleLocalRing B hS ιV s y' hy) p).asIdeal ↔
    p ∈ Set.range (PrimeSpectrum.comap (algebraMap ↥(etaleLocalRing B Y hS s)
      (Localization.Away (chartToEtaleLocalRing B hS ιV s y' hy t))))
  rw [PrimeSpectrum.localization_away_comap_range (Localization.Away _)
    (chartToEtaleLocalRing B hS ιV s y' hy t)]
  rfl

variable [IsDomain R] [IsIntegrallyClosed R]

/-- The `R`-algebra structure on the stalk of `Spec R` at `y'`. -/
local instance : Algebra R ((Spec R).presheaf.stalk y') :=
  (StructureSheaf.toStalk R y').hom.toAlgebra

/-- The stalk of `Spec R` at `y'` is the localization of `R` at the prime `y'`. -/
local instance : IsLocalization.AtPrime ((Spec R).presheaf.stalk y') y'.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk R y'

include ιV y' hy in
/-- The local ring of `Y` at the image of `y'` is a normal domain, being a localization of the
normal domain `R`. -/
theorem isDomain_and_isIntegrallyClosed_stalk_of_chart :
    IsDomain (Y.presheaf.stalk (s.hom (IsLocalRing.closedPoint s.residueField))) ∧
      IsIntegrallyClosed (Y.presheaf.stalk (s.hom (IsLocalRing.closedPoint s.residueField))) := by
  let e := (affineChartStalkIso ιV s y' hy).commRingCatIsoToRingEquiv
  have hle : y'.asIdeal.primeCompl ≤ nonZeroDivisors R :=
    y'.asIdeal.primeCompl_le_nonZeroDivisors
  have : IsDomain ((Spec R).presheaf.stalk y') :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := y'.asIdeal.primeCompl) _ hle
  have : IsIntegrallyClosed ((Spec R).presheaf.stalk y') :=
    isIntegrallyClosed_of_isLocalization _ _ hle
  exact ⟨e.symm.injective.isDomain _, IsIntegrallyClosed.of_equiv e⟩

include ιV y' hy in
/-- **The étale local ring of a normal chart is a normal domain** (Stacks 06DI): the local ring of
`Y` at the image of the point is a localization of the normal domain `R`. -/
theorem isDomain_and_isIntegrallyClosed_etaleLocalRing_of_chart :
    IsDomain ↥(etaleLocalRing B Y hS s) ∧ IsIntegrallyClosed ↥(etaleLocalRing B Y hS s) := by
  obtain ⟨_, _⟩ := isDomain_and_isIntegrallyClosed_stalk_of_chart ιV s y' hy
  exact isDomain_and_isIntegrallyClosed_of_isHenselization
    (Y.presheaf.stalk (s.hom (IsLocalRing.closedPoint s.residueField))) ↥(etaleLocalRing B Y hS s)
    (ResidueField ↥(etaleLocalRing B Y hS s))

/-- **The ring map `φ` is injective and the étale local ring is algebraic over `R`**: it is the
composite of a localization of a domain, an isomorphism, and a henselization, which is
faithfully flat and algebraic. -/
theorem injective_and_isAlgebraic_chartToEtaleLocalRing :
    Function.Injective (chartToEtaleLocalRing B hS ιV s y' hy) ∧
      letI := (chartToEtaleLocalRing B hS ιV s y' hy).toAlgebra
      Algebra.IsAlgebraic R ↥(etaleLocalRing B Y hS s) := by
  obtain ⟨_, _⟩ := isDomain_and_isIntegrallyClosed_stalk_of_chart ιV s y' hy
  let S := Y.presheaf.stalk (s.hom (IsLocalRing.closedPoint s.residueField))
  let O := ↥(etaleLocalRing B Y hS s)
  let e := (affineChartStalkIso ιV s y' hy).commRingCatIsoToRingEquiv
  have : Module.FaithfullyFlat S O :=
    IsLocalRing.IsHenselization.faithfullyFlat (L := ResidueField O)
  have hφ : chartToEtaleLocalRing B hS ιV s y' hy =
      (algebraMap S O).comp ((e : (Spec R).presheaf.stalk y' →+* S).comp
        (algebraMap R ((Spec R).presheaf.stalk y'))) := rfl
  refine ⟨?_, ?_⟩
  · rw [hφ]
    exact (FaithfulSMul.algebraMap_injective S O).comp
      (e.injective.comp (IsLocalization.injective _ y'.asIdeal.primeCompl_le_nonZeroDivisors))
  · let := (chartToEtaleLocalRing B hS ιV s y' hy).toAlgebra
    let : Algebra R S := ((e : (Spec R).presheaf.stalk y' →+* S).comp
      (algebraMap R ((Spec R).presheaf.stalk y'))).toAlgebra
    have : IsScalarTower R S O := .of_algebraMap_eq' hφ
    have hRS : Algebra.IsAlgebraic R S := by
      have := IsLocalization.isAlgebraic (R := R) (S := (Spec R).presheaf.stalk y')
        y'.asIdeal.primeCompl
      refine ⟨fun x => ?_⟩
      obtain ⟨x, rfl⟩ := e.surjective x
      let f : (Spec R).presheaf.stalk y' →ₐ[R] S :=
        { (e : (Spec R).presheaf.stalk y' →+* S) with commutes' := fun _ => rfl }
      exact (Algebra.IsAlgebraic.isAlgebraic x).algHom f
    have hSO : Algebra.IsAlgebraic S O :=
      isAlgebraic_of_isHenselization S O (ResidueField O) (FractionRing S)
    exact Algebra.IsAlgebraic.trans R S O

end Chart

section Interlude

open Stacks.EtaleCohomology AlgebraicGeometry.Scheme

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

/-- **Interlude I of the proof of Stacks 0F0V.** Let `j : X ⟶ Y` be a quasi-compact open immersion
and `ιV : Spec R ⟶ Y` an affine open chart, `R` a normal domain over a field `K` with
`trdeg_K(R) ≤ d` and `R` of finite type, in which `X` is the basic open `D(t)`, `t ≠ 0`. Let `s` be
a geometric point of `Y` over a point `y'` of the chart with `t ∈ y'`, and suppose `a ≤ dim(R/y')`
and `d ≤ a + 1 + m`. If Stacks 0F0V holds in dimension at most `m` (`hIH`), then for every torsion
abelian sheaf `𝓕` on `X_ét` and every `q > m + 1` the stalk of `R^qj_*𝓕` at `s` vanishes.

The stalk formula for higher direct images (Stacks 03Q9) enters as
`AlgebraicGeometry.isZero_stalk_rightDerived_iff_subsingleton_sheafH`. -/
public theorem isZero_stalk_rightDerived_smallEtalePushforwardAb_of_chart
    {K : Type u} [Field K] {R : CommRingCat.{u}} [IsDomain R] [IsIntegrallyClosed R]
    [Algebra K R] [Algebra.FiniteType K R] (d : ℕ) (hR : Algebra.trdeg K R ≤ d)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    (ιV : Spec R ⟶ Y) [IsOpenImmersion ιV] (t : R) (ht0 : t ≠ 0)
    (ht : ∀ p : Spec R, ιV p ∈ Set.range j ↔ t ∉ p.asIdeal)
    (s : GeometricPoint Y) (y' : Spec R)
    (hy : ιV y' = s.hom (IsLocalRing.closedPoint s.residueField))
    (hty : t ∈ y'.asIdeal) (a m : ℕ)
    (ha' : (a : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ y'.asIdeal)) (hd : d ≤ a + 1 + m)
    (hIH : ∀ ⦃E : Type u⦄ [Field E] ⦃Z : Scheme.{u}⦄ [IsAffine Z] (g : Z ⟶ Spec (.of E))
      [LocallyOfFiniteType g], topologicalKrullDim Z ≤ m →
        etaleCohomologicalDimension Z ≤ m + etaleCohomologicalDimension (Spec (.of E)))
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (q : ℕ) (hq : m + 1 < q) :
    IsZero ((smallEtaleStalkAb s.hom).obj
      (((smallEtalePushforwardAb j).rightDerived q).obj F)) := by
  let B := BigEtaleSite.containing Y
  have hS : B.Contains Y := BigEtaleSite.contains_containing _
  refine (isZero_stalk_rightDerived_iff_subsingleton_sheafH B hS j s F q).2 ?_
  let O := ↥(etaleLocalRing B Y hS s)
  let φ := chartToEtaleLocalRing B hS ιV s y' hy
  obtain ⟨hdom, -⟩ := isDomain_and_isIntegrallyClosed_etaleLocalRing_of_chart B hS ιV s y' hy
  obtain ⟨hφinj, hφalg⟩ := injective_and_isAlgebraic_chartToEtaleLocalRing B hS ιV s y' hy
  let : Algebra R O := φ.toAlgebra
  let : Algebra K O := (φ.comp (algebraMap K R)).toAlgebra
  have : IsScalarTower K R O := .of_algebraMap_eq' rfl
  -- the transcendence degree of the étale local ring
  have htrO : Algebra.trdeg K O ≤ a + 1 + m := by
    have : FaithfulSMul R O := (faithfulSMul_iff_algebraMap_injective R O).2 hφinj
    have : FaithfulSMul K R := (faithfulSMul_iff_algebraMap_injective K R).2
      (algebraMap K R).injective
    rw [← trdeg_add_eq (A := O) K R, @trdeg_eq_zero _ _ _ _ _ hφalg, add_zero]
    exact hR.trans (by exact_mod_cast hd)
  -- a field of transcendence degree at least `a` inside the étale local ring
  obtain ⟨Fl, _, _, ψ, hψ⟩ := IsLocalRing.exists_algHom_field_trdeg_residueField_le K O
  have hFa : (a : Cardinal) ≤ Algebra.trdeg K Fl := by
    have hcomap := comap_chartToEtaleLocalRing_maximalIdeal B hS ιV s y' hy
    let ρ₀ : R →ₐ[K] ResidueField O :=
      { toRingHom := (residue O).comp φ, commutes' := fun _ => rfl }
    have hρ₀ : ∀ r ∈ y'.asIdeal, ρ₀ r = 0 := fun r hr =>
      (residue_eq_zero_iff _).2 (by rwa [← hcomap] at hr)
    let ρ := Ideal.Quotient.liftₐ y'.asIdeal ρ₀ hρ₀
    have hρ : Function.Injective ρ := RingHom.lift_injective_of_ker_le_ideal y'.asIdeal
      (f := (residue O).comp φ) hρ₀ fun r hr => by
        rw [← hcomap]; exact (residue_eq_zero_iff _).1 hr
    -- Noether normalization: `R/y'` is finite over a polynomial ring `K[t₁, …, tₖ] ⊆ R/y'`, so
    -- `dim(R/y') = k ≤ trdeg_K(R/y')`
    exact (natCast_le_trdeg_of_le_ringKrullDim a ha').trans
      ((trdeg_le_of_injective ρ hρ).trans hψ)
  -- the local equation of the divisor
  let f := φ t
  have hf : f ∈ maximalIdeal O := by
    rwa [← comap_chartToEtaleLocalRing_maximalIdeal B hS ιV s y' hy] at hty
  have hf0 : f ≠ 0 := fun h => ht0 (hφinj (h.trans (map_zero φ).symm))
  have hcd := Scheme.etaleCohomologicalDimension_spec_away_le ψ a m hFa htrO f hf hf0 hIH
  -- the base change of `j` to the strict henselization is `Spec O_f`
  let e := IsOpenImmersion.isoOfRangeEq
    (strictHenselizationBaseChangeToStrictHenselization B hS j s)
    (Spec.map (CommRingCat.ofHom (algebraMap O (Localization.Away f))))
    (range_strictHenselizationBaseChangeToStrictHenselization_of_chart B hS ιV s y' hy j t ht)
  let G := (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS j s)).obj F
  have hG : Stacks.Torsion.torsionSheafProperty _ G :=
    Stacks.Torsion.torsionSheafProperty_of_iso _
      ((smallEtalePullbackAbIsoEtaleAbelianInverseImage
        (strictHenselizationBaseChangeToSource B hS j s)).app F).symm
      (torsionSheafProperty_etaleAbelianInverseImage.{u, 0} _ F hF)
  exact (sheafHSmallEtalePushforwardAddEquiv e.hom G q).toEquiv.subsingleton_congr.2
    (isEtaleCohomologyBound_etaleCohomologicalDimension _ _
      (torsionSheafProperty_smallEtaleDirectImageAb.{0} e.hom G hG) q
      (lt_of_le_of_lt hcd (by exact_mod_cast hq)))

end Interlude

end AlgebraicGeometry

end
