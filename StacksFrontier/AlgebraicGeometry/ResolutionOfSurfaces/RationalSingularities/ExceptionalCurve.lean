module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.KrullDimension.Module
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalDifferentials
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Integral
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorQuotient
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Serre
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.DimensionDrop
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SerreCondition
public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.DimensionOne
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.GeneralDimensionFormula
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.Depth
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.Topology.Sober.Generization
import StacksCore.Tactic.StacksAttribute

/-!
# The exceptional curve of the blowup of a surface singularity at its closed point

Let `(A, 𝔪, κ)` be a two-dimensional Noetherian local domain, let `X` be the blowup of `Spec(A)`
in `𝔪` and let `E ⊆ X` be the exceptional divisor. Then `E` is a proper curve over `κ`, and it is
Cohen–Macaulay as soon as `X` is normal. In Situation [Stacks, Tag 0B4W] the blowup is normal
([Stacks, Tag 0B4Z]), and clause (1) of [Stacks, Tag 0B63] is assembled from these results in
`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/RationalSingularities/ExceptionalCurveCohenMacaulay.lean`.

## Main definitions

* `AlgebraicGeometry.exceptionalDivisorToCentre`: the structure morphism of the exceptional
  divisor of a blowup over the centre of the blowup; for the blowup at the closed point of a
  local ring this is the morphism `E ⟶ Spec(κ)`.

## Main results

* `AlgebraicGeometry.isProper_exceptionalDivisorToCentre_residuePoint`: `E` is proper over `κ`.
* `AlgebraicGeometry.topologicalKrullDim_exceptionalDivisor_residuePoint`: `E` has dimension one.
* `AlgebraicGeometry.isCohenMacaulay_exceptionalDivisor_residuePoint`: `E` is Cohen–Macaulay.

## Implementation notes

The centre of the blowup is the closed point `Spec(κ) ⟶ Spec(A)`, which is
`Stacks.Blowup.residuePoint`; its ideal sheaf is `𝔪` by `Stacks.Blowup.ker_residuePoint`, and
`AlgebraicGeometry.ker_residuePoint_eq_ofIdealTop_map` restates that at the spelling in which
`StacksFrontier/AlgebraicGeometry/Surfaces/BlowUpNormality.lean` discusses normality of the blowup.
The morphism `E ⟶ Spec(κ)` is `AlgebraicGeometry.exceptionalDivisorToCentre`: the composite
`E ⟶ X ⟶ Spec(A)` kills the ideal of the centre, so it factors through the closed immersion
cutting the centre out. `Stacks.Blowup.exceptionalToCentre` is the same construction for the
parallel blowup `Stacks.Blowup.blowUp` of
`StacksFrontier/AlgebraicGeometry/Blowup/ReesSheafData.lean`,
which is a different scheme from `AlgebraicGeometry.blowUp` and is not identified with it
anywhere, so it cannot be used with the properness, integrality and effective-Cartier results
about the latter.

Properness and the dimension need neither normality of `A` nor the rational-singularity
hypothesis of [Stacks, Tag 0B4W]: properness holds over any Noetherian local ring, and the
dimension computation only uses that `A` is a two-dimensional Noetherian local domain. The
dimension is at most one by the dimension formula [Stacks, Tag 02JU] on the blowup — which is
birational onto `Spec(A)`, since it is an isomorphism away from the closed point — together with
the dimension drop at an effective Cartier divisor [Stacks, Tag 056N]. It is at least one because
a point of `E` lying over the closed point has codimension two in `X`, whereas the generic point
of its irreducible component in `E` has codimension one by [Stacks, Tag 0BCN]; the two are
therefore distinct and give a chain of length one.

`AlgebraicGeometry.isCohenMacaulay_exceptionalDivisor_residuePoint` takes the normality of the
blowup as the hypothesis `hnormal`, because it is stated for any two-dimensional Noetherian local
domain. In Situation [Stacks, Tag 0B4W] that normality is [Stacks, Tag 0B4Z],
`AlgebraicGeometry.isNormal_blowUp_maximalIdeal_rationalSingularitySituation` in
`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/RationalSingularities/BlowUpNormal.lean`.
Normality is the only input to Cohen–Macaulayness beyond the dimension: Serre's criterion
[Stacks, Tag 0B3S] gives `(S₁)` for an effective Cartier divisor on a normal scheme, and in
dimension at most one `(S₁)` is Cohen–Macaulayness.

## References

* [Stacks Project, Tag 0B63](https://stacks.math.columbia.edu/tag/0B63)
* [Stacks Project, Tag 0B4Z](https://stacks.math.columbia.edu/tag/0B4Z)
* [Stacks Project, Tag 0B3S](https://stacks.math.columbia.edu/tag/0B3S)
* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU)
* [Stacks Project, Tag 0BCN](https://stacks.math.columbia.edu/tag/0BCN)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order

universe u

namespace AlgebraicGeometry

/-! ### The structure morphism of the exceptional divisor over the centre -/

section Centre

variable {S Z : Scheme.{u}} (p : Z ⟶ S)

/-- The ideal of the centre of a blowup is below the kernel of the structure morphism of the
exceptional divisor over the base. -/
theorem ker_le_ker_exceptionalDivisorι :
    p.ker ≤ ((exceptionalIdeal p.ker).subschemeι ≫ blowUpToBase p.ker).ker := by
  rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι]
  exact Scheme.IdealSheafData.le_map_comap _ _

variable [IsClosedImmersion p]

/-- **The structure morphism of the exceptional divisor over the centre of a blowup.** The
composite `E ⟶ X ⟶ S` kills the ideal of the centre, so it factors uniquely through the closed
immersion `p : Z ⟶ S` cutting the centre out. -/
def exceptionalDivisorToCentre : exceptionalDivisor p.ker ⟶ Z :=
  IsClosedImmersion.lift p ((exceptionalIdeal p.ker).subschemeι ≫ blowUpToBase p.ker)
    (ker_le_ker_exceptionalDivisorι p)

/-- The structure morphism over the centre is compatible with the blowup morphism. -/
theorem exceptionalDivisorToCentre_comp :
    exceptionalDivisorToCentre p ≫ p =
      (exceptionalIdeal p.ker).subschemeι ≫ blowUpToBase p.ker :=
  IsClosedImmersion.lift_fac p _ (ker_le_ker_exceptionalDivisorι p)

end Centre

/-! ### The centre is the closed point -/

section ResiduePoint

open Stacks.Blowup

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The ideal sheaf of the closed point of `Spec(A)` is the one generated over the whole space by
the image of `𝔪`, which is the spelling in which normality of the blowup is discussed. -/
theorem ker_residuePoint_eq_ofIdealTop_map :
    (residuePoint A).ker = Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (IsLocalRing.maximalIdeal A)) := by
  rw [ker_residuePoint, Ideal.comap_hom_eq_map_inv]

/-- The support of the ideal sheaf of the closed point is the closed point. -/
theorem supportSet_ker_residuePoint :
    (residuePoint A).ker.supportSet = {IsLocalRing.closedPoint A} := by
  have hid : (Scheme.ΓSpecIso (.of A)).hom.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom =
      RingHom.id A := by
    have h := congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso (.of A)).inv_hom_id
    rw [CommRingCat.hom_comp] at h
    simpa using h
  have hcomp : Ideal.comap (Scheme.ΓSpecIso (.of A)).inv.hom
      (Ideal.comap (Scheme.ΓSpecIso (.of A)).hom.hom (IsLocalRing.maximalIdeal A)) =
      IsLocalRing.maximalIdeal A := by
    rw [Ideal.comap_comap, hid, Ideal.comap_id]
  change ((residuePoint A).ker.support : Set (Spec (.of A))) = _
  rw [ker_residuePoint, Scheme.IdealSheafData.coe_support_ofIdealTop, Spec_zeroLocus,
    ← Ideal.coe_comap, hcomp]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨(PrimeSpectrum.mem_zeroLocus _ _).2 (le_refl _),
    fun x hx => PrimeSpectrum.ext ?_⟩
  exact ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le x.isPrime.ne_top
    ((PrimeSpectrum.mem_zeroLocus _ _).1 hx)).symm

/-- The maximal ideal of a local ring of positive dimension is nonzero. -/
theorem maximalIdeal_ne_bot_of_dimension_two (hdim : ringKrullDim A = 2) :
    IsLocalRing.maximalIdeal A ≠ ⊥ := by
  intro hm
  have hd : ((IsLocalRing.maximalIdeal A).height : WithBot ℕ∞) = 2 := by
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdim]
  rw [hm] at hd
  norm_num at hd

/-- The ideal sheaf of the closed point of a two-dimensional local ring is nonzero. -/
theorem ker_residuePoint_ne_bot (hdim : ringKrullDim A = 2) :
    (residuePoint A).ker ≠ ⊥ := by
  intro hbot
  refine maximalIdeal_ne_bot_of_dimension_two A hdim ?_
  have h := congrArg (fun J : (Spec (.of A)).IdealSheafData =>
    J.ideal ⟨⊤, isAffineOpen_top (Spec (.of A))⟩) hbot
  rw [ker_residuePoint] at h
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal, Scheme.IdealSheafData.ideal_bot] at h
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (.of A)).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (C := CommRingCat) (Scheme.ΓSpecIso (.of A)).hom).2
  have hcm : Ideal.comap (Scheme.ΓSpecIso (.of A)).hom.hom (IsLocalRing.maximalIdeal A) = ⊥ := by
    simpa using h
  calc IsLocalRing.maximalIdeal A
      = Ideal.map (Scheme.ΓSpecIso (.of A)).hom.hom
        (Ideal.comap (Scheme.ΓSpecIso (.of A)).hom.hom (IsLocalRing.maximalIdeal A)) :=
        (Ideal.map_comap_of_surjective _ hsurj _).symm
    _ = ⊥ := by rw [hcm, Ideal.map_bot]

end ResiduePoint

/-! ### Properness -/

open Stacks.Blowup in
/-- **[Stacks, Tag 0B63] clause (1), properness.** The exceptional divisor of the blowup of the
spectrum of a Noetherian local ring in its maximal ideal is proper over the residue field. -/
@[stacks 0B63 "clause (1): the exceptional curve is proper over the residue field"]
theorem isProper_exceptionalDivisorToCentre_residuePoint (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] :
    IsProper (exceptionalDivisorToCentre (residuePoint A)) := by
  have h : IsProper (exceptionalDivisorToCentre (residuePoint A) ≫ residuePoint A) := by
    rw [exceptionalDivisorToCentre_comp]
    infer_instance
  exact IsProper.of_comp _ (residuePoint A)

/-! ### Dimension -/

section Dimension

/-- A dimension below two is a dimension below one. -/
private theorem dim_le_one_of_lt_two {d : WithBot ℕ∞} (hd : d < 2) : d ≤ 1 := by
  cases d with
  | bot => exact bot_le
  | coe d =>
    cases d with
    | top => norm_num at hd
    | coe n =>
      have hn : n < 2 := by simpa using hd
      exact_mod_cast (show n ≤ 1 by omega)

/-- The local dimension at a point is at most the global dimension. -/
private theorem topologicalKrullDimAt_le_global {Y : Type*} [TopologicalSpace Y] (y : Y) :
    topologicalKrullDimAt Y y ≤ topologicalKrullDim Y := by
  change (⨅ U : {U : Set Y // y ∈ U ∧ IsOpen U}, topologicalKrullDim (↥U.1)) ≤ _
  exact (iInf_le _ ⟨Set.univ, ⟨Set.mem_univ y, isOpen_univ⟩⟩).trans
    (topologicalKrullDim_subspace_le Y Set.univ)

/-- A stalk map transported along an equality of its base point stays an isomorphism. -/
private theorem isIso_cast_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (y : Y) (h : f x = y) (hh : IsIso (f.stalkMap x)) :
    IsIso (CommRingCat.ofHom ((h ▸ f.stalkMap x).hom)) := by
  cases h
  simpa using hh

/-- A chain of two proper specializations into `x` forces the local ring at `x` to have dimension
at least two. -/
private theorem ringKrullDim_stalk_ge_two_of_specialization_chain
    {X : Scheme.{u}} [IsLocallyNoetherian X] {x₀ x₁ x₂ : X}
    (h₀₁ : x₀ ⤳ x₁) (h₁₂ : x₁ ⤳ x₂) (hne₀₁ : x₀ ≠ x₁) (hne₁₂ : x₁ ≠ x₂) :
    2 ≤ ringKrullDim (X.presheaf.stalk x₂) := by
  obtain ⟨U, hU, hx₂U, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x₂ ∈ (⊤ : X.Opens) from trivial)
  have hx₁U : x₁ ∈ U := (specializes_iff_forall_open.mp h₁₂) U U.2 hx₂U
  have hx₀U : x₀ ∈ U := (specializes_iff_forall_open.mp h₀₁) U U.2 hx₁U
  let p₀ := hU.primeIdealOf ⟨x₀, hx₀U⟩
  let p₁ := hU.primeIdealOf ⟨x₁, hx₁U⟩
  let p₂ := hU.primeIdealOf ⟨x₂, hx₂U⟩
  have hlt : ∀ (a b : X) (ha : a ∈ U) (hb : b ∈ U), a ⤳ b → a ≠ b →
      hU.primeIdealOf ⟨a, ha⟩ < hU.primeIdealOf ⟨b, hb⟩ := by
    intro a b ha hb hab hne
    refine lt_of_le_of_ne ((PrimeSpectrum.le_iff_specializes _ _).2 ?_) (fun he => ?_)
    · exact ((subtype_specializes_iff ⟨a, ha⟩ ⟨b, hb⟩).2 hab).map hU.isoSpec.hom.continuous
    · refine hne ?_
      have := congrArg (fun q : PrimeSpectrum Γ(X, U) => hU.fromSpec q) he
      simpa [hU.fromSpec_primeIdealOf] using this
  have hp₀₁ : p₀ < p₁ := hlt _ _ hx₀U hx₁U h₀₁ hne₀₁
  have hp₁₂ : p₁ < p₂ := hlt _ _ hx₁U hx₂U h₁₂ hne₁₂
  have hheight : 2 ≤ p₂.asIdeal.height := by
    have h₁ := Ideal.height_add_one_le_of_lt_of_isPrime hp₀₁
    have h₂ := Ideal.height_add_one_le_of_lt_of_isPrime hp₁₂
    have h₁' : (1 : ℕ∞) ≤ p₁.asIdeal.height := by
      calc (1 : ℕ∞) = 0 + 1 := by simp
        _ ≤ p₀.asIdeal.height + 1 := by
            simp
        _ ≤ p₁.asIdeal.height := h₁
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ p₁.asIdeal.height + 1 := by simpa [add_comm] using add_le_add_right h₁' (1 : ℕ∞)
      _ ≤ p₂.asIdeal.height := h₂
  let := X.presheaf.algebra_section_stalk ⟨x₂, hx₂U⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x₂) p₂.asIdeal :=
    hU.isLocalization_stalk ⟨x₂, hx₂U⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p₂.asIdeal]
  exact WithBot.coe_le_coe.mpr hheight

open Stacks.Blowup in
/-- **[Stacks, Tag 0B63] clause (1), the dimension.** The exceptional divisor of the blowup of
the spectrum of a two-dimensional Noetherian local domain in its maximal ideal is a curve. -/
@[stacks 0B63 "clause (1): the exceptional curve has dimension one"]
theorem topologicalKrullDim_exceptionalDivisor_residuePoint (A : Type u) [CommRing A]
    [IsLocalRing A] [IsDomain A] [IsNoetherianRing A] (hdim : ringKrullDim A = 2) :
    topologicalKrullDim (exceptionalDivisor (residuePoint A).ker) = 1 := by
  classical
  let I : (Spec (.of A)).IdealSheafData := (residuePoint A).ker
  let f : blowUp I ⟶ Spec (.of A) := blowUpToBase I
  let U : (Spec (.of A)).Opens := ⟨I.supportSetᶜ, I.support.isClosed.isOpen_compl⟩
  let V : (blowUp I).Opens := f ⁻¹ᵁ U
  have hsupport : I.supportSet = {IsLocalRing.closedPoint A} := supportSet_ker_residuePoint A
  have hgenNe : genericPoint (Spec (.of A)) ≠ IsLocalRing.closedPoint A := by
    intro h
    refine maximalIdeal_ne_bot_of_dimension_two A hdim ?_
    have hbot : genericPoint (Spec (.of A)) = (⊥ : PrimeSpectrum A) :=
      genericPoint_eq_bot_of_affine (.of A)
    have h' : (IsLocalRing.closedPoint A : PrimeSpectrum A) = (⊥ : PrimeSpectrum A) := by
      rw [← h, hbot]
    simpa [IsLocalRing.closedPoint] using congrArg PrimeSpectrum.asIdeal h'
  have hIne : I ≠ ⊥ := ker_residuePoint_ne_bot A hdim
  have : IsIntegral (blowUp I) := isIntegral_blowUp I hIne
  have hgenU : genericPoint (Spec (.of A)) ∈ U := by
    change genericPoint (Spec (.of A)) ∉ I.supportSet
    rw [hsupport]
    exact fun h => hgenNe h
  have hIso : IsIso (f ∣_ U) := isIso_blowUp_restrict_compl_support I
  have : Nonempty U.toScheme := ⟨⟨genericPoint (Spec (.of A)), hgenU⟩⟩
  have hgenUeq : U.ι (genericPoint U.toScheme) = genericPoint (Spec (.of A)) :=
    genericPoint_eq_of_isOpenImmersion U.ι
  have : Nonempty V.toScheme := ⟨(asIso (f ∣_ U)).inv (genericPoint U.toScheme)⟩
  have hgenVeq : V.ι (genericPoint V.toScheme) = genericPoint (blowUp I) :=
    genericPoint_eq_of_isOpenImmersion V.ι
  have hgenRest : (f ∣_ U) (genericPoint V.toScheme) = genericPoint U.toScheme :=
    genericPoint_eq_of_isOpenImmersion (f ∣_ U)
  have hpoint : (f ∣_ U) ≫ U.ι = V.ι ≫ f := morphismRestrict_ι f U
  have hgen : f (genericPoint (blowUp I)) = genericPoint (Spec (.of A)) := by
    have hpt : U.ι ((f ∣_ U) (genericPoint V.toScheme)) = f (V.ι (genericPoint V.toScheme)) :=
      congrArg (fun g : V.toScheme ⟶ Spec (.of A) => g (genericPoint V.toScheme)) hpoint
    calc f (genericPoint (blowUp I)) = f (V.ι (genericPoint V.toScheme)) :=
          congrArg f hgenVeq.symm
      _ = U.ι ((f ∣_ U) (genericPoint V.toScheme)) := hpt.symm
      _ = U.ι (genericPoint U.toScheme) := congrArg U.ι hgenRest
      _ = genericPoint (Spec (.of A)) := hgenUeq
  have : IsProper f := isProper_blowUpToBase I
  have : LocallyOfFiniteType f := ‹IsProper f›.toLocallyOfFiniteType
  have : IsDominant f := ((tfae_isDominant_of_isIntegral f).out 1 2).mpr hgen
  have hstalk : IsIso (f.stalkMap (genericPoint (blowUp I))) := by
    let z : V.toScheme := genericPoint V.toScheme
    have hstalkV : IsIso ((f ∣_ U).stalkMap z) :=
      ((isIso_iff_isIso_stalkMap (f ∣_ U)).mp hIso).2 _
    have hstalkAt : IsIso (f.stalkMap z.1) := by
      rw [← Arrow.isIso_iff_isIso_of_isIso (morphismRestrictStalkMap f U z).hom]
      exact hstalkV
    have hz : z.1 = genericPoint (blowUp I) := by
      change V.ι (genericPoint V.toScheme) = _
      exact hgenVeq
    exact hz ▸ hstalkAt
  have : IsIso (CommRingCat.ofHom (dominantFunctionFieldMap f)) := by
    simpa [dominantFunctionFieldMap] using
      isIso_cast_stalkMap f (genericPoint (blowUp I)) (genericPoint (Spec (.of A))) hgen hstalk
  let : Algebra (Spec (.of A)).functionField (blowUp I).functionField :=
    (dominantFunctionFieldMap f).toAlgebra
  have htrdeg : Algebra.trdeg (Spec (.of A)).functionField (blowUp I).functionField = 0 := by
    rw [trdeg_eq_zero_iff, Algebra.isAlgebraic_def]
    intro x
    have hsurj : Function.Surjective (dominantFunctionFieldMap f) :=
      (ConcreteCategory.bijective_of_isIso
        (CommRingCat.ofHom (dominantFunctionFieldMap f))).2
    obtain ⟨a, ha⟩ := hsurj x
    refine ⟨Polynomial.X - Polynomial.C a, Polynomial.X_sub_C_ne_zero a, ?_⟩
    rw [← ha]
    simp only [Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [show algebraMap (Spec (.of A)).functionField (blowUp I).functionField a =
      dominantFunctionFieldMap f a from rfl]
    simp
  have hlocalDim : ∀ x : blowUp I, ringKrullDim ((blowUp I).presheaf.stalk x) ≤ 2 := by
    intro x
    let := (f.residueFieldMap x).hom.toAlgebra
    have hformula := localDimension_add_trdeg_le f x
    have hres : (0 : WithBot ℕ∞) ≤
        (Cardinal.toENat (Algebra.trdeg ((Spec (.of A)).residueField (f x))
          ((blowUp I).residueField x)) : WithBot ℕ∞) := by simp
    have hbase : ringKrullDim ((Spec (.of A)).presheaf.stalk (f x)) ≤ 2 := by
      let q : PrimeSpectrum A := f x
      have hdimSpec : ringKrullDim ((Spec (.of A)).presheaf.stalk (f x)) =
          (q.asIdeal.height : WithBot ℕ∞) := by
        rw [ringKrullDim_eq_of_ringEquiv
            (Spec.stalkIso (.of A) (f x)).commRingCatIsoToRingEquiv,
          IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal]
      rw [hdimSpec]
      calc ((q.asIdeal.height : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim A := by
            simpa only [ringKrullDim] using
              Ideal.height_le_ringKrullDim_of_ne_top q.isPrime.ne_top
        _ = 2 := hdim
    calc ringKrullDim ((blowUp I).presheaf.stalk x)
        ≤ ringKrullDim ((blowUp I).presheaf.stalk x) +
            (Cardinal.toENat (Algebra.trdeg ((Spec (.of A)).residueField (f x))
              ((blowUp I).residueField x)) : WithBot ℕ∞) := le_add_of_nonneg_right hres
      _ ≤ ringKrullDim ((Spec (.of A)).presheaf.stalk (f x)) +
            (Cardinal.toENat (Algebra.trdeg (Spec (.of A)).functionField
              (blowUp I).functionField) : WithBot ℕ∞) := hformula
      _ ≤ 2 := by simpa [htrdeg] using hbase
  have hdimBlow : topologicalKrullDim (blowUp I) ≤ 2 := by
    rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
    exact iSup_le hlocalDim
  have hdimle : topologicalKrullDim (exceptionalDivisor I) ≤ 1 := by
    rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
    refine iSup_le fun x => ?_
    rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
    have hambient : topologicalKrullDimAt (blowUp I) ((exceptionalIdeal I).subschemeι x) ≤ 2 :=
      (topologicalKrullDimAt_le_global _).trans hdimBlow
    have hfin : topologicalKrullDimAt (blowUp I) ((exceptionalIdeal I).subschemeι x) < ⊤ :=
      lt_of_le_of_lt hambient (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top 2))
    have hdrop := topologicalKrullDimAt_subscheme_lt (exceptionalIdeal I) inferInstance x hfin
    exact dim_le_one_of_lt_two (lt_of_lt_of_le hdrop hambient)
  -- the lower bound
  have hheightClosed : Order.height (IsLocalRing.closedPoint A : PrimeSpectrum A) = 2 := by
    calc Order.height (IsLocalRing.closedPoint A : PrimeSpectrum A)
        = (IsLocalRing.closedPoint A : PrimeSpectrum A).asIdeal.height :=
          (PrimeSpectrum.height_eq_orderHeight _).symm
      _ = 2 := by
          refine WithBot.coe_injective ?_
          rw [show (IsLocalRing.closedPoint A : PrimeSpectrum A).asIdeal =
            IsLocalRing.maximalIdeal A from rfl,
            IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdim]
          rfl
  obtain ⟨c, hcLast, hcLen⟩ :=
    Order.exists_series_of_le_height (IsLocalRing.closedPoint A : PrimeSpectrum A) (n := 2)
      (by rw [hheightClosed]; norm_num)
  let b : PrimeSpectrum A := c ⟨1, by rw [hcLen]; omega⟩
  have hstep₀ : c ⟨0, by rw [hcLen]; omega⟩ < b := by
    simpa [b, Fin.castSucc, Fin.succ, hcLen] using c.step ⟨0, by rw [hcLen]; omega⟩
  have hbClosed : b < (IsLocalRing.closedPoint A : PrimeSpectrum A) := by
    have hstep := c.step ⟨1, by rw [hcLen]; omega⟩
    have hidx : (⟨1, by rw [hcLen]; omega⟩ : Fin c.length).succ = Fin.last c.length := by
      apply Fin.ext
      simp [hcLen]
    rw [hidx] at hstep
    change c (⟨1, by rw [hcLen]; omega⟩ : Fin c.length).castSucc < c.last at hstep
    rw [hcLast] at hstep
    simpa [b, hcLen] using hstep
  have hbU : b ∈ U := by
    change b ∉ I.supportSet
    rw [hsupport]
    exact fun h => ne_of_lt hbClosed h
  let y : blowUp I := V.ι (((f ∣_ U).homeomorph).symm ⟨b, hbU⟩)
  have hfy : f y = b := by
    have hsq : U.ι ((f ∣_ U) (((f ∣_ U).homeomorph).symm ⟨b, hbU⟩)) = f y :=
      congrArg (fun g : V.toScheme ⟶ Spec (.of A) =>
        g (((f ∣_ U).homeomorph).symm ⟨b, hbU⟩)) hpoint
    rw [show (f ∣_ U) (((f ∣_ U).homeomorph).symm ⟨b, hbU⟩) = ⟨b, hbU⟩ from
      Homeomorph.apply_symm_apply (f ∣_ U).homeomorph ⟨b, hbU⟩] at hsq
    exact hsq.symm
  have hyImage : b ∈ f '' closure ({y} : Set (blowUp I)) := ⟨y, subset_closure rfl, hfy⟩
  have hclosureImage : closure ({b} : Set (Spec (.of A))) ⊆
      f '' closure ({y} : Set (blowUp I)) :=
    closure_minimal (Set.singleton_subset_iff.mpr hyImage)
      (f.isClosedMap _ isClosed_closure)
  obtain ⟨x, hxClosure, hfx⟩ := hclosureImage (specializes_iff_mem_closure.mp
    ((PrimeSpectrum.le_iff_specializes b (IsLocalRing.closedPoint A)).mp hbClosed.le))
  have hyx : y ⤳ x := specializes_iff_mem_closure.mpr hxClosure
  have hgenericY : genericPoint (blowUp I) ⤳ y := genericPoint_specializes y
  have hneGenericY : genericPoint (blowUp I) ≠ y := by
    intro he
    have hmap := congrArg f he
    rw [hgen, hfy] at hmap
    rw [show b = (⊥ : PrimeSpectrum A) from
      hmap.symm.trans (genericPoint_eq_bot_of_affine (.of A))] at hstep₀
    exact (not_lt_of_ge bot_le) hstep₀
  have hneyx : y ≠ x := by
    intro he
    have hmap := congrArg f he
    rw [hfy, hfx] at hmap
    exact (ne_of_lt hbClosed) hmap
  have : IsLocallyNoetherian (blowUp I) := LocallyOfFiniteType.isLocallyNoetherian f
  have hdimx : 2 ≤ ringKrullDim ((blowUp I).presheaf.stalk x) :=
    ringKrullDim_stalk_ge_two_of_specialization_chain hgenericY hyx hneGenericY hneyx
  have hxSupport : x ∈ ((exceptionalIdeal I).support : Set (blowUp I)) := by
    rw [show exceptionalIdeal I = I.comap f from rfl, Scheme.IdealSheafData.support_comap]
    change f x ∈ I.supportSet
    rw [hsupport]
    exact hfx
  have hxRange : x ∈ Set.range (exceptionalIdeal I).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hxSupport
  obtain ⟨ξ, hxξ⟩ := hxRange
  let cE : irreducibleComponents (exceptionalDivisor I) :=
    ⟨irreducibleComponent ξ, irreducibleComponent_mem_irreducibleComponents ξ⟩
  let η : exceptionalDivisor I := genericPoints.ofComponent cE
  have hη : IsGenericPoint η (cE : Set (exceptionalDivisor I)) :=
    genericPoints.isGenericPoint_ofComponent cE
  have hηξ : η ⤳ ξ := hη.specializes mem_irreducibleComponent
  have hηξ_ne : η ≠ ξ := by
    intro he
    have hcartier := ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor
      (exceptionalIdeal I) inferInstance η ⟨cE, hη⟩
    have hηx : (exceptionalIdeal I).subschemeι η = x :=
      (congrArg (exceptionalIdeal I).subschemeι he).trans hxξ
    rw [← hηx, hcartier] at hdimx
    norm_num at hdimx
  have hdimge : (1 : WithBot ℕ∞) ≤ topologicalKrullDim (exceptionalDivisor I) := by
    have hmem : ξ ∈ closure ({η} : Set (exceptionalDivisor I)) :=
      specializes_iff_mem_closure.mp hηξ
    have hstrict : closure ({ξ} : Set (exceptionalDivisor I)) ⊂
        closure ({η} : Set (exceptionalDivisor I)) := by
      refine ⟨closure_minimal (Set.singleton_subset_iff.mpr hmem) isClosed_closure, fun hsub => ?_⟩
      exact hηξ_ne ((hηξ.antisymm (specializes_iff_mem_closure.mpr
        (hsub (subset_closure rfl)))).eq)
    let Zξ : IrreducibleCloseds (exceptionalDivisor I) :=
      ⟨closure {ξ}, isIrreducible_singleton.closure, isClosed_closure⟩
    let Zη : IrreducibleCloseds (exceptionalDivisor I) :=
      ⟨closure {η}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hlt : Zξ < Zη := by
      refine lt_of_le_of_ne hstrict.1 fun hEq => hstrict.2 (le_of_eq ?_)
      exact (congrArg (fun Z : IrreducibleCloseds (exceptionalDivisor I) =>
        (Z : Set (exceptionalDivisor I))) hEq).symm
    have hkd : (1 : WithBot ℕ∞) ≤
        Order.krullDim (IrreducibleCloseds (exceptionalDivisor I)) :=
      Order.one_le_krullDim_iff.mpr ⟨Zξ, Zη, hlt⟩
    exact hkd
  exact le_antisymm hdimle hdimge

end Dimension

/-! ### Cohen–Macaulayness -/


/-- Serre's condition `(S₁)` for a locally Noetherian scheme is Serre's condition `(S₁)` for its
structure sheaf read as a module over itself. -/
private theorem sheafHasPropertySk_one_of_hasPropertySk_one (X : Scheme.{u})
    [IsLocallyNoetherian X] (h : HasPropertySk X 1) :
    SheafHasPropertySk X (SheafOfModules.unit X.ringCatSheaf) 1 := by
  refine Stacks.AlgebraicGeometry.ReflexiveModules.sheafHasPropertySk_of_forall _ 1 fun x => ?_
  have e := structureSheafStalkLinearEquiv X x
  have hx := h x
  rw [← Module.supportDim_self_eq_ringKrullDim, ← Module.supportDim_eq_of_equiv e,
    ← Module.depth_eq_depth_of_linearEquiv
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) e] at hx
  exact hx

open Stacks.Blowup in
/-- The exceptional divisor of the blowup of the spectrum of a two-dimensional Noetherian local
domain in its maximal ideal is Cohen–Macaulay whenever the blowup is normal.

In Situation [Stacks, Tag 0B4W] the blowup is normal by [Stacks, Tag 0B4Z]
(`AlgebraicGeometry.isNormal_blowUp_maximalIdeal_rationalSingularitySituation`), and clause (1)
of [Stacks, Tag 0B63] in full is
`AlgebraicGeometry.isProper_and_topologicalKrullDim_eq_one_and_isCohenMacaulay_exceptionalDivisor`.
-/
theorem isCohenMacaulay_exceptionalDivisor_residuePoint (A : Type u) [CommRing A]
    [IsLocalRing A] [IsDomain A] [IsNoetherianRing A] (hdim : ringKrullDim A = 2)
    (hnormal : IsNormal (blowUp (residuePoint A).ker)) :
    IsCohenMacaulay (exceptionalDivisor (residuePoint A).ker) := by
  have := hnormal
  have : IsProper (blowUpToBase (residuePoint A).ker) :=
    isProper_blowUpToBase (residuePoint A).ker
  have : IsLocallyNoetherian (blowUp (residuePoint A).ker) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase (residuePoint A).ker)
  have : IsLocallyNoetherian (exceptionalDivisor (residuePoint A).ker) :=
    LocallyOfFiniteType.isLocallyNoetherian (exceptionalIdeal (residuePoint A).ker).subschemeι
  have hsk : HasPropertySk (exceptionalDivisor (residuePoint A).ker) 1 :=
    isNormal_effectiveCartierDivisor_hasPropertySk_one _
      (exceptionalIdeal (residuePoint A).ker) inferInstance
  have hdimE : topologicalKrullDim (exceptionalDivisor (residuePoint A).ker) ≤ 1 :=
    le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint A hdim)
  refine (isCohenMacaulay_iff_hasNoEmbeddedPoints_of_topologicalKrullDim_le_one _ hdimE).mpr ?_
  have hsheaf := sheafHasPropertySk_one_of_hasPropertySk_one
    (exceptionalDivisor (residuePoint A).ker) hsk
  simpa only [HasNoEmbeddedPoints, IsEmbeddedPoint] using
    (hasNoEmbeddedAssociatedPoints_iff_hasPropertySk_one
      (exceptionalDivisor (residuePoint A).ker) _).symm.mp hsheaf

end AlgebraicGeometry

end

end
