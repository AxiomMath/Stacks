module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.NonFlatLocusFibreDimension
public import StacksFrontier.AlgebraicGeometry.HProjective.Basic
public import StacksFrontier.AlgebraicGeometry.Models.Basic
public import StacksFrontier.AlgebraicGeometry.Models.Normalization
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.Formula
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionDominant
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenaryExamples
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ClosedPointResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.JTwoStandardClasses
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.FlatAndRelativeDimension
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ImpliedProperties.LocalDomain
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanTheorem
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.Models
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.SingularLocusFinite
public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.GeometricallyRegularNormal

/-!
# Resolutions of models of curves, and regular proper models of smooth projective curves

Let `R` be a discrete valuation ring with fraction field `K`. This file proves the existence half
of [Stacks, Tag 0C2U]: a model over `R` of a smooth curve over `K` has a resolution of
singularities. Together with the scheme-theoretic image construction of Tag 0C2S this gives a
regular, integral, proper model of every smooth projective curve over `K`, which is everything in
the proof of [Stacks, Tag 0C2W] preceding the contraction of exceptional curves of the first kind
(Tag 0CD9).

Along the way the total space `X` of a model of a curve is studied: it is integral and
Noetherian, of dimension at most two, and of dimension exactly two as soon as its special fibre is
nonempty.

## Main results

* `Stacks.Models.isModel_projectiveSpaceOver`: `ℙⁿ_R` is a model of `ℙⁿ_K`.
* `Stacks.Models.isIntegral_of_isModel`, `Stacks.Models.isNoetherian_of_isModel`: the total space
  of a model of an integral scheme is integral; that of any model is Noetherian.
* `Stacks.Models.topologicalKrullDim_le_two_of_isModel`,
  `Stacks.Models.ringKrullDim_stalk_le_two_of_isModel`: the total space of a model of a curve,
  and each of its local rings, has dimension at most two.
* `Stacks.Models.topologicalKrullDim_eq_two_of_isModel`: it has dimension two if its special
  fibre is nonempty.
* `Stacks.Models.exists_isResolution_of_isModel`: **Tag 0C2U**, existence of a resolution of
  singularities of a model of a smooth curve.
* `Stacks.Models.exists_isModel_isProper_isRegular`: a smooth projective curve over `K` has a
  regular, integral model which is proper over `R`.

## Implementation notes

The total space of a model is reduced because its generic fibre is reduced and
scheme-theoretically dense, and irreducible because flatness makes the structure morphism
generalizing, so that every point specializes from a point of the irreducible generic fibre.

The upper bound on the dimension is Tag 0BAG: `dim X` is at most `dim Spec R = 1` plus the
transcendence degree of the residue field extension at the generic point of `X`, which is the
dimension one of the fibre over the generic point of `Spec R`, that is of the curve. The lower
bound uses the dimension formula of Tag 02JU, `Spec R` being universally catenary (Tag 02JB): at a
closed point `x` of `X` in the special fibre the residue field is finite over the residue field of
`R`, so `dim 𝒪_{X,x} = 1 + trdeg`, and the transcendence degree of the function field extension
is one by the same formula at the generic point.

For the resolution, if the special fibre is empty then `X` is its generic fibre, the smooth curve
itself, and the identity is a resolution. Otherwise `X` is a two-dimensional integral Noetherian
scheme and condition (4) of Lipman's theorem (Tag 0BGP) is checked as in the source: finiteness
of the normalization and normality of its completed local rings are Tag 0C2T, whose
geometric-normality hypothesis comes from smoothness (Tag 056T), and the singular locus of the
normalization is finite because `R` is J-2 (Tag 07PJ), so that this locus is closed in a normal
Noetherian scheme of dimension at most two, where singular points are closed. The conclusion
packages the integrality and Noetherianity of `X` with the resolution, as
`AlgebraicGeometry.IsResolution` is only defined over an integral Noetherian scheme.

## References

* [Stacks Project, Tag 0C2U](https://stacks.math.columbia.edu/tag/0C2U)
* [Stacks Project, Tag 0C2W](https://stacks.math.columbia.edu/tag/0C2W)
* [Stacks Project, Tag 0C2S](https://stacks.math.columbia.edu/tag/0C2S)
* [Stacks Project, Tag 0C2T](https://stacks.math.columbia.edu/tag/0C2T)
* [Stacks Project, Tag 0BGP](https://stacks.math.columbia.edu/tag/0BGP)
* [Stacks Project, Tag 0BAG](https://stacks.math.columbia.edu/tag/0BAG)
* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

namespace Stacks.Models

universe u

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- A scheme of finite type and quasi-compact over a Noetherian scheme is Noetherian. -/
private theorem isNoetherian_of_locallyOfFiniteType_of_quasiCompact {X Y : Scheme.{u}}
    [IsNoetherian Y] (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] : IsNoetherian X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact ⟨⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- Projective space `ℙⁿ_R` over a discrete valuation ring, together with the identification of
its generic fibre with `ℙⁿ_K` given by base change, is a model of `ℙⁿ_K`. -/
theorem isModel_projectiveSpaceOver (n : ℕ) :
    IsModel (projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K))
      (projectiveSpaceOver n (Spec (.of R)) ↘ Spec (.of R))
      (projectiveSpaceOverBaseChangeIso n
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))).symm := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  rw [Iso.symm_hom, Iso.inv_comp_eq, projectiveSpaceOverBaseChangeIso_hom_over]

/-! ### The total space of a model -/

section TotalSpace

variable {C X : Scheme.{u}}

/-- The total space of a model of an integral scheme is integral. It is reduced because the
generic fibre is reduced and scheme-theoretically dense, flatness making the base change of the
scheme-theoretically dominant morphism `Spec K ⟶ Spec R` scheme-theoretically dominant; it is
irreducible because, flatness making the structure morphism generalizing, every point specializes
from a point of the irreducible generic fibre. -/
theorem isIntegral_of_isModel (c : C ⟶ Spec (.of K)) [IsIntegral C] (p : X ⟶ Spec (.of R))
    (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hX : IsModel c p e) : IsIntegral X := by
  let i₀ := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let j := pullback.fst p i₀
  have : Flat p := hX.1
  have : IsOpenImmersion i₀ := genericFiberSpec_isOpenImmersion
  have : IsIntegral (pullback p i₀) := IsIntegral.of_isIso e.hom
  have : IsDominant i₀ := by
    rw [isDominant_iff]
    exact (IsOpenImmersion.isOpen_range i₀).dense (Set.range_nonempty _)
  have : IsSchemeTheoreticallyDominant i₀ := .of_isDominant i₀
  have : IsReduced X := IsSchemeTheoreticallyDominant.isReduced j
  have hdense : closure (Set.range j) = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun x => ?_
    obtain ⟨z, hzx, hz⟩ := Flat.generalizingMap p (genericPoint_specializes (p x))
    have hzj : z ∈ Set.range j := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨genericPoint _, (map_genericPoint_of_isDominant i₀).trans hz.symm⟩
    exact hzx.mem_closed isClosed_closure (subset_closure hzj)
  have hirr := (IrreducibleSpace.isIrreducible_univ (pullback p i₀ : Scheme.{u})).image j
    j.continuous.continuousOn
  rw [Set.image_univ] at hirr
  have huniv : IsIrreducible (Set.univ : Set X) := hdense ▸ hirr.closure
  have : IrreducibleSpace X := (irreducibleSpace_def X).mpr huniv
  exact isIntegral_of_irreducibleSpace_of_isReduced X

omit [IsFractionRing R K] in
/-- The total space of a model is Noetherian: it is of finite type over the Noetherian scheme
`Spec R`. -/
theorem isNoetherian_of_isModel (c : C ⟶ Spec (.of K)) (p : X ⟶ Spec (.of R))
    (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hX : IsModel c p e) : IsNoetherian X := by
  have : LocallyOfFiniteType p := hX.2.1
  have : QuasiCompact p := hX.2.2.1
  exact isNoetherian_of_locallyOfFiniteType_of_quasiCompact p

/-- The fibre of a model of a curve over the generic point of `Spec R` is one-dimensional: it is
homeomorphic to the generic fibre, which is the curve. -/
private theorem topologicalKrullDim_fiber_eq_one (c : C ⟶ Spec (.of K)) [IsCurve K c]
    (p : X ⟶ Spec (.of R))
    (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))) (s : Spec (.of R))
    (hs : s ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    topologicalKrullDim (p.fiber s) = 1 := by
  let i₀ := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let j := pullback.fst p i₀
  have : IsOpenImmersion i₀ := genericFiberSpec_isOpenImmersion
  have hrange : Set.range i₀ = {s} := by
    obtain ⟨t, rfl⟩ := hs
    ext y
    refine ⟨?_, fun hy => ⟨t, hy.symm⟩⟩
    rintro ⟨t', rfl⟩
    rw [Subsingleton.elim t' t]
    rfl
  have hpre : p ⁻¹' {s} = Set.range j := by
    rw [Scheme.Pullback.range_fst, hrange]
  rw [(p.fiberHomeo s).isHomeomorph.topologicalKrullDim_eq, hpre,
    ← j.isOpenEmbedding.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq,
    ← (TopCat.homeoOfIso (asIso e.hom.base)).isHomeomorph.topologicalKrullDim_eq]
  exact IsCurve.topologicalKrullDim_eq_one (k := K) (f := c)

/-- In a model of a curve the structure morphism sends the generic point to a point of the
generic fibre of `Spec R`, and the residue field extension there has transcendence degree one. -/
private theorem residueFieldTranscendenceDegree_genericPoint_eq_one (c : C ⟶ Spec (.of K))
    [IsCurve K c] (p : X ⟶ Spec (.of R)) [IsIntegral X] [LocallyOfFiniteType p]
    (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    p (genericPoint X) ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R K))) ∧
      residueFieldTranscendenceDegree p (genericPoint X) = 1 := by
  let i₀ := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let j := pullback.fst p i₀
  have : IsOpenImmersion i₀ := genericFiberSpec_isOpenImmersion
  have hη : genericPoint X ∈ Set.range j := by
    rw [(genericPoint_spec X).mem_open_set_iff (IsOpenImmersion.isOpen_range j),
      Set.univ_inter]
    obtain ⟨z⟩ := (inferInstance : Nonempty C)
    exact ⟨j (e.hom z), e.hom z, rfl⟩
  have hs : p (genericPoint X) ∈ Set.range i₀ := by
    rw [Scheme.Pullback.range_fst] at hη
    exact hη
  refine ⟨hs, ?_⟩
  have h := toENat_trdeg_eq_topologicalKrullDim_fiber p (genericPoint X)
    p.isGenericPoint_asFiber_genericPoint
  rw [topologicalKrullDim_fiber_eq_one c p e _ hs] at h
  exact_mod_cast h

variable (c : C ⟶ Spec (.of K)) [IsCurve K c] (p : X ⟶ Spec (.of R))
  (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))

/-- **The total space of a model of a curve has dimension at most two.** By Tag 0BAG its
dimension is at most the dimension one of `Spec R` plus the transcendence degree of the residue
field extension at its generic point, which is the dimension one of the generic fibre. -/
theorem topologicalKrullDim_le_two_of_isModel (hX : IsModel c p e) :
    topologicalKrullDim X ≤ 2 := by
  have : IsIntegral X := isIntegral_of_isModel c p e hX
  have : LocallyOfFiniteType p := hX.2.1
  have hR : topologicalKrullDim (Spec (.of R)) = 1 := by
    show topologicalKrullDim (PrimeSpectrum R) = 1
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      IsDiscreteValuationRing.ringKrullDim_eq_one]
  have hsup : (⨆ ξ : genericPoints X, residueFieldTranscendenceDegree p ξ.1) ≤ 1 := by
    refine iSup_le fun ξ => ?_
    obtain ⟨ξ, hξ⟩ := ξ
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hξ
    subst hξ
    exact (residueFieldTranscendenceDegree_genericPoint_eq_one c p e).2.le
  calc topologicalKrullDim X
      ≤ topologicalKrullDim (Spec (.of R)) +
        ((⨆ ξ : genericPoints X, residueFieldTranscendenceDegree p ξ.1 : ℕ∞) : WithBot ℕ∞) :=
        topologicalKrullDim_le_add_iSup_residueFieldTrdeg p
    _ ≤ 1 + ((1 : ℕ∞) : WithBot ℕ∞) := by
        rw [hR]
        gcongr
        exact_mod_cast hsup
    _ = 2 := rfl

/-- **The local rings of the total space of a model of a curve have dimension at most two.** -/
theorem ringKrullDim_stalk_le_two_of_isModel (hX : IsModel c p e) (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ 2 :=
  (ringKrullDim_stalk_le_topologicalKrullDim x).trans
    (topologicalKrullDim_le_two_of_isModel c p e hX)

/-- **A model of a curve with nonempty special fibre is two-dimensional.** At a closed point `x`
of the total space lying over the closed point of `Spec R` the residue field is finite over the
residue field of `R`, so the dimension formula (Tag 02JU, `Spec R` being universally catenary)
gives `dim 𝒪_{X,x} = dim R + trdeg_{R} X = 1 + 1`; the transcendence degree of the function field
extension is read off from the same formula at the generic point. -/
theorem topologicalKrullDim_eq_two_of_isModel (hX : IsModel c p e)
    (hk : ∃ x : X, p x ∉ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    topologicalKrullDim X = 2 := by
  let i₀ := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have : IsOpenImmersion i₀ := genericFiberSpec_isOpenImmersion
  have : IsIntegral X := isIntegral_of_isModel c p e hX
  have : IsNoetherian X := isNoetherian_of_isModel c p e hX
  have : LocallyOfFiniteType p := hX.2.1
  have : Flat p := hX.1
  have : IsDominant p := by
    rw [isDominant_iff, denseRange_iff_closure_range, ← Set.univ_subset_iff]
    intro s _
    obtain ⟨z, -, hz⟩ := Flat.generalizingMap p (genericPoint_specializes (p (genericPoint X)))
    exact (genericPoint_specializes s).mem_closed isClosed_closure (subset_closure ⟨z, hz⟩)
  have hUC : Scheme.IsUniversallyCatenary (Spec (.of R)) :=
    Scheme.isUniversallyCatenary_of_locallyOfFiniteType_over_dimOneDomain R
      (IsDiscreteValuationRing.ringKrullDim_eq_one R) (𝟙 _)
  -- A closed point of the total space in the special fibre.
  obtain ⟨x, hx, hxc⟩ := IsClosed.exists_closed_singleton
    ((IsOpenImmersion.isOpen_range i₀).isClosed_compl.preimage p.continuous) hk
  -- The dimension formula at `x` and at the generic point.
  have hfx := ringKrullDim_stalk_add_trdeg_residueField_eq p hUC x
  have hfη := ringKrullDim_stalk_add_trdeg_residueField_eq p hUC (genericPoint X)
  obtain ⟨hsη, htη⟩ := residueFieldTranscendenceDegree_genericPoint_eq_one c p e
  -- The residue field at `x` is algebraic over that of `p x`.
  have htx : (Cardinal.toNat (@Algebra.trdeg ((Spec (.of R)).residueField (p x))
      (X.residueField x) _ _ (p.residueFieldMap x).hom.toAlgebra)) = 0 := by
    let := (p.residueFieldMap x).hom.toAlgebra
    have := finite_residueField_of_isClosed p hxc
    rw [trdeg_eq_zero, map_zero]
  have htη' : (Cardinal.toNat (@Algebra.trdeg ((Spec (.of R)).residueField (p (genericPoint X)))
      (X.residueField (genericPoint X)) _ _
        (p.residueFieldMap (genericPoint X)).hom.toAlgebra)) = 1 := by
    let := (p.residueFieldMap (genericPoint X)).hom.toAlgebra
    have h1 : Algebra.trdeg ((Spec (.of R)).residueField (p (genericPoint X)))
        (X.residueField (genericPoint X)) = 1 := Cardinal.toENat_eq_one.mp htη
    rw [h1, map_one]
  -- The local rings of `Spec R`: a field at the generic point, a discrete valuation ring at the
  -- closed point.
  have hstalk : ∀ s : Spec (.of R),
      ringKrullDim ((Spec (.of R)).presheaf.stalk s) = (s.asIdeal.height : WithBot ℕ∞) := by
    intro s
    have := s.isPrime
    let : Algebra R ((Spec (.of R)).presheaf.stalk s) :=
      StructureSheaf.stalkAlgebra (CommRingCat.of R) s
    have : IsLocalization.AtPrime ((Spec (.of R)).presheaf.stalk s) s.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk (CommRingCat.of R) s
    exact IsLocalization.AtPrime.ringKrullDim_eq_height s.asIdeal _
  have hrange : ∀ s : Spec (.of R), s ∈ Set.range i₀ ↔ s.asIdeal = ⊥ := by
    intro s
    constructor
    · rintro ⟨t, rfl⟩
      have := t.isPrime
      show Ideal.comap (algebraMap R K) t.asIdeal = ⊥
      rw [Ideal.eq_bot_of_prime t.asIdeal]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
    · intro hs
      refine ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩
      show Ideal.comap (algebraMap R K) ⊥ = s.asIdeal
      rw [hs]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
  have hη0 : ringKrullDim (X.presheaf.stalk (genericPoint X)) = 0 :=
    ringKrullDim_eq_zero_of_field X.functionField
  have hpη0 : ringKrullDim ((Spec (.of R)).presheaf.stalk (p (genericPoint X))) = 0 := by
    rw [hstalk, (hrange _).mp hsη, Ideal.height_bot]
    rfl
  have hpx1 : ringKrullDim ((Spec (.of R)).presheaf.stalk (p x)) = 1 := by
    have : Ring.KrullDimLE 1 R :=
      Ring.krullDimLE_iff.mpr (IsDiscreteValuationRing.ringKrullDim_eq_one R).le
    have hne : (p x).asIdeal ≠ ⊥ := fun h => hx ((hrange _).mpr h)
    have hmax : (p x).asIdeal = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal ((p x).isPrime.isMaximal_of_ne_bot hne)
    rw [hstalk, hmax, IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
      IsDiscreteValuationRing.ringKrullDim_eq_one]
  dsimp only at hfx hfη
  rw [htx, hpx1, Nat.cast_zero, add_zero] at hfx
  rw [htη', hη0, hpη0, zero_add, zero_add, Nat.cast_one] at hfη
  rw [← hfη] at hfx
  refine le_antisymm (topologicalKrullDim_le_two_of_isModel c p e hX) ?_
  calc (2 : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x) := by
        rw [hfx]
        rfl
    _ ≤ topologicalKrullDim X := ringKrullDim_stalk_le_topologicalKrullDim x

end TotalSpace

/-! ### Existence of a resolution -/

/-- A two-dimensional model of a smooth curve has a resolution of singularities. Condition (4)
of Lipman's theorem holds: the normalization is finite and has normal completed local rings by
Tag 0C2T, and it has finitely many singular points because it is a normal Noetherian scheme of
dimension at most two whose regular locus is open, `R` being J-2 (Tag 07PJ). -/
theorem exists_isResolution_of_isModel_of_topologicalKrullDim_eq_two {C X : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [Smooth c] [IsCurve K c] (p : X ⟶ Spec (.of R)) [IsIntegral X]
    [IsNoetherian X] (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hX : IsModel c p e) (hdim : topologicalKrullDim X = 2) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsResolution f := by
  have hgn := isGeometricallyNormal_of_smooth c
  let hfin := finite_irreducibleComponents_of_isCompact X
  have hν : IsFinite (Scheme.normalization X hfin) :=
    isFinite_normalization_of_isModel c hgn p e hX hfin
  refine ((tfae_exists_isAlteration_isRegular X hdim).out 4 2).mp ?_
  refine ⟨hfin, hν, ?_, fun y _ => isNormalRing_adicCompletion_stalk_normalization_of_isModel
    c hgn p e hX hfin y⟩
  let ν := Scheme.normalization X hfin
  have : LocallyOfFiniteType p := hX.2.1
  have : IsNoetherian (X.normalizationScheme hfin) :=
    isNoetherian_of_locallyOfFiniteType_of_quasiCompact ν
  have : IsNormal (X.normalizationScheme hfin) := Scheme.isNormal_normalizationScheme X hfin
  have hdimν : topologicalKrullDim (X.normalizationScheme hfin) ≤ 2 :=
    hdim ▸ topologicalKrullDim_le_of_isIntegralHom ν
  have hJ2 : Scheme.IsJ2 (X.normalizationScheme hfin) :=
    Scheme.isJ2_of_locallyOfFiniteType_over_localRing_of_dim_one R
      (IsDiscreteValuationRing.ringKrullDim_eq_one R) (ν ≫ p)
  exact finite_singularLocus_of_isJ2 _ hdimν hJ2

/-- **Stacks Project, Tag 0C2U (existence of a resolution).** Let `X` be a model over a discrete
valuation ring `R` of a smooth curve `C` over the fraction field `K`. Then `X` is integral and
Noetherian, and there exists a resolution of singularities of `X`.

If the special fibre of `X` is empty, `X` is its generic fibre, which is the smooth curve `C`, and
the identity is a resolution. Otherwise `X` is two-dimensional and Lipman's theorem applies, see
`exists_isResolution_of_isModel_of_topologicalKrullDim_eq_two`. -/
@[stacks 0C2U "existence of a resolution"]
theorem exists_isResolution_of_isModel {C X : Scheme.{u}} (c : C ⟶ Spec (.of K)) [Smooth c]
    [IsCurve K c] (p : X ⟶ Spec (.of R))
    (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hX : IsModel c p e) :
    ∃ (_ : IsIntegral X) (_ : IsNoetherian X) (Y : Scheme.{u}) (f : Y ⟶ X), IsResolution f := by
  have hI : IsIntegral X := isIntegral_of_isModel c p e hX
  have hN : IsNoetherian X := isNoetherian_of_isModel c p e hX
  refine ⟨hI, hN, ?_⟩
  let i₀ := Spec.map (CommRingCat.ofHom (algebraMap R K))
  by_cases hk : ∃ x : X, p x ∉ Set.range i₀
  · exact exists_isResolution_of_isModel_of_topologicalKrullDim_eq_two c p e hX
      (topologicalKrullDim_eq_two_of_isModel c p e hX hk)
  · simp only [not_exists, not_not] at hk
    let j := pullback.fst p i₀
    have : IsOpenImmersion i₀ := genericFiberSpec_isOpenImmersion
    have hrange : j.opensRange = ⊤ := by
      refine top_unique fun x _ => ?_
      show x ∈ Set.range j
      rw [Scheme.Pullback.range_fst]
      exact hk x
    have : IsIso j := isIso_of_isOpenImmersion_of_opensRange_eq_top j hrange
    have hreg : IsRegular X :=
      IsRegular.of_iso ((asIso j).symm ≪≫ e.symm) (isRegular_of_smooth_over_field c)
    have hbir : IsBirational (𝟙 X) := by
      refine ⟨?_, fun x _ => ?_⟩
      · simpa using Set.bijOn_id (genericPoints X)
      · simp only [Scheme.Hom.stalkMap]
        infer_instance
    exact ⟨X, 𝟙 X, ⟨hbir, inferInstance, hI⟩, hreg⟩

/-- **A smooth projective curve has a regular proper model.** Let `R` be a discrete valuation
ring with fraction field `K` and let `C` be a smooth projective curve over `K`. There is a
regular integral scheme `X`, proper over `R`, which is a model of `C`.

This is the part of the proof of [Stacks, Tag 0C2W] preceding the contraction of exceptional
curves: the scheme-theoretic image `X₀` of `C` in `ℙⁿ_R` is a model of `C` by Tag 0C2S, proper
over `R` as it is closed in `ℙⁿ_R`; a resolution of singularities of `X₀` exists and is again a
model of `C` by Tag 0C2U, and it is proper over `R` as a composition of proper morphisms. -/
theorem exists_isModel_isProper_isRegular {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsCurve K c]
    [Smooth c] (hproj : Stacks.HProjective.IsHProjective c) :
    ∃ (X : Scheme.{u}) (p : X ⟶ Spec (.of R))
      (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      IsModel c p e ∧ IsProper p ∧ IsRegular X ∧ IsIntegral X := by
  obtain ⟨n, ι, hι, hιc⟩ := hproj
  let i₀ := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let pR := projectiveSpaceOver n (Spec (.of R)) ↘ Spec (.of R)
  let vK := projectiveSpaceOver n (Spec (.of K)) ↘ Spec (.of K)
  let eP := (projectiveSpaceOverBaseChangeIso n i₀).symm
  have hP : IsModel vK pR eP := isModel_projectiveSpaceOver n
  obtain ⟨e₀, he₀⟩ := schemeTheoreticImage_isModel c vK ι hιc pR eP hP
  let g := ι ≫ eP.hom ≫ pullback.fst pR i₀
  let p := g.imageι ≫ pR
  have : IsProper p := by
    have := isProper_projectiveSpaceOver n (Spec (.of R))
    exact inferInstanceAs (IsProper (g.imageι ≫ pR))
  obtain ⟨_, _, Y, f, hf⟩ := exists_isResolution_of_isModel c p e₀ he₀
  obtain ⟨eY, heY⟩ := isModel_comp_of_isResolution c p e₀ he₀ f hf
  have : IsProper f := hf.1.2.1
  exact ⟨Y, f ≫ p, eY, heY, inferInstance, hf.2, hf.1.2.2⟩

end Stacks.Models

end
