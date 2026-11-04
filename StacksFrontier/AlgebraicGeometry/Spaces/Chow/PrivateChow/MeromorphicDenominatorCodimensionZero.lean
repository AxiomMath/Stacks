module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.MeromorphicDenominatorLength

/-!
# The quotients by the ideal of denominators vanish at points of codimension zero

Let `X` be a decent, locally Noetherian algebraic space, `ℒ` an invertible module and `t` a
regular meromorphic section of `ℒ` with ideal of denominators `𝓘`. At a point `ξ` of `|X|` whose
local ring has dimension zero the two quotients `𝒪_X / 𝓘` and `ℒ / t 𝓘` have length zero. On an
affine chart trivializing `ℒ` with chart ratio `c = p / q`, the denominator `q` lies in `𝓘` and the
numerator `p = q c` in `c 𝓘`, both nonzerodivisors of the chart; their images in the Artinian local
ring at a point over `ξ` are units.

## Main results

* `AlgebraicGeometry.Space.geometricLength_meromorphicQuotients_eq_zero_of_localRingDimension_eq_zero`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open scoped nonZeroDivisors

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)
  (hN : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
  (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
  (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
  (L : Modules.{u, u} B S hS X.1 X.2) (hL : IsInvertibleModule X L)
  (t : MeromorphicSection.{u, u} B S hS X.1 X.2 L)
  (ht : IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 L t)

include hN hwa hfin ht in
/-- **At a point of codimension zero both quotients by the ideal of denominators have length
zero.** -/
theorem geometricLength_meromorphicQuotients_eq_zero_of_localRingDimension_eq_zero
    (xbar : GeometricPoint B S hS X.1) (hx : localRingDimension B S hS xbar.image = 0) :
    haveI : Fact (HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y)) :=
      ⟨hN⟩
    geometricLength B S hS X xbar (meromorphicNumeratorQuotient B S hS X L t
        (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL)) = 0 ∧
      geometricLength B S hS X xbar (meromorphicDenominatorQuotient B S hS X L t
        (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL)) = 0 := by
  have hL' := Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL
  have : Fact (HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y)) :=
    ⟨hN⟩
  obtain ⟨V, hV, v, e, hc, hf, -, -, -, hv, hcu, -⟩ :=
    exists_affine_chart_isUnit_chartRatio B S hS X hwa hfin L L hL hL t ht t ht xbar.image
  have hu : chartSchemeToPoints B S hS X.1 V v = xbar.image := hv
  -- coherence of the two quotients
  have hIc := isCoherent_meromorphicDenominatorIdeal B S hS X L t hL' hwa hfin
  have hLc : IsCoherent B S hS X.1 X.2 L :=
    { __ := isQuasicoherentOnSite_of_isInvertible B S hS X L hL'
      __ := isCoherentOnSite_of_isInvertible L hL }
  have hQ₁ : IsCoherent B S hS X.1 X.2 (meromorphicDenominatorQuotient B S hS X L t hL') :=
    isCoherent_cokernel B S hS X.1 X.2 hIc inferInstance _
  have hQ₂ : IsCoherent B S hS X.1 X.2 (meromorphicNumeratorQuotient B S hS X L t hL') :=
    isCoherent_cokernel B S hS X.1 X.2 hIc hLc _
  -- the local ring of the chart at `v`, a localization of the ring of the chart
  have : IsAffine (chartScheme V) := hV
  let : Algebra Γ(chartScheme V, ⊤) ((chartScheme V).presheaf.stalk v) :=
    ((chartScheme V).presheaf.germ ⊤ v trivial).hom.toAlgebra
  have hU : IsAffineOpen (⊤ : (chartScheme V).Opens) := isAffineOpen_top _
  have hloc₀ : IsLocalization.AtPrime ((chartScheme V).presheaf.stalk v)
      (hU.primeIdealOf ⟨v, trivial⟩).asIdeal :=
    hU.isLocalization_stalk ⟨v, trivial⟩
  have hP : (hU.primeIdealOf ⟨v, trivial⟩).asIdeal = chartPrimeAt B S hS X.2 V v :=
    (IsLocalization.AtPrime.under_maximalIdeal ((chartScheme V).presheaf.stalk v) _).symm
  have hSm : (hU.primeIdealOf ⟨v, trivial⟩).asIdeal.primeCompl =
      (chartPrimeAt B S hS X.2 V v).primeCompl :=
    Submonoid.ext fun a => not_congr
      (Iff.of_eq (congrArg (fun I : Ideal Γ(chartScheme V, ⊤) => a ∈ I) hP))
  let : Algebra (chartRing B S hS X.1 X.2 V) ((chartScheme V).presheaf.stalk v) :=
    ((chartScheme V).presheaf.germ ⊤ v trivial).hom.toAlgebra
  have : IsLocalization (chartPrimeAt B S hS X.2 V v).primeCompl
      ((chartScheme V).presheaf.stalk v) := by
    have h := hloc₀
    rwa [IsLocalization.AtPrime, hSm] at h
  have hK := isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin V hV
  have := isLocallyNoetherian_chartScheme B S hS X hN V
  -- the local ring at `v` has dimension zero, hence is Artinian
  have hdim := localRingDimension_eq_of_chartPoint B S hS X.2 V.obj.left V.obj.hom V.property v _
    (chartPoint_chartSchemeToPoints B S hS X V v)
  rw [hu, hx] at hdim
  have : Ring.KrullDimLE 0 ((chartScheme V).presheaf.stalk v) :=
    Ring.krullDimLE_iff.mpr (by
      show ringKrullDim (((BigFppfOver.toScheme B S hS).obj V.obj.left).presheaf.stalk v) ≤ _
      rw [← hdim]; exact_mod_cast le_rfl)
  have : IsArtinianRing ((chartScheme V).presheaf.stalk v) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let : Algebra (chartRing B S hS X.1 X.2 V)
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)) :=
    ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op V)).hom.toAlgebra
  have : IsFractionRing (chartRing B S hS X.1 X.2 V)
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)) := hK
  let c : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V) :=
    chartRatio B S hS X.1 X.2 L V e hc hf t
  obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.mk'_surjective (chartRing B S hS X.1 X.2 V)⁰ c
  have hpq' : algebraMap _ ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)) p =
      algebraMap _ ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V))
        (q : chartRing B S hS X.1 X.2 V) * c := by
    rw [← hpq, mul_comm]
    exact (IsLocalization.mk'_spec _ p q).symm
  have hqI : (q : chartRing B S hS X.1 X.2 V) ∈ meromorphicDenominatorIdealAt B S hS X L t V :=
    (isMeromorphicDenominator_iff_of_free B S hS X L t V e hc hf q).2 ⟨p, hpq'⟩
  have hpJ : p ∈ meromorphicNumeratorIdealAt B S hS X L t V e hc hf := ⟨q, hqI, hpq'⟩
  have hp0 : p ∈ (chartRing B S hS X.1 X.2 V)⁰ := by
    have hunit :
        IsUnit (algebraMap _ ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)) p) := by
      rw [hpq']
      exact (IsLocalization.map_units _ q).mul hcu
    refine mem_nonZeroDivisors_iff_right.2 fun r hr => ?_
    have h : algebraMap _ ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)) r *
        algebraMap _ ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)) p = 0 := by
      rw [← map_mul, hr, map_zero]
    exact IsFractionRing.injective (chartRing B S hS X.1 X.2 V)
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V))
      ((hunit.mul_left_eq_zero).1 h ▸ (map_zero _).symm)
  have hunit : ∀ a ∈ (chartRing B S hS X.1 X.2 V)⁰,
      IsUnit (algebraMap (chartRing B S hS X.1 X.2 V) ((chartScheme V).presheaf.stalk v) a) :=
    fun a ha => IsArtinianRing.isUnit_of_mem_nonZeroDivisors
      ((chartScheme V).nonZeroDivisors_le_comap_germ_top v ha)
  have key : ∀ (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
      (J : Ideal (chartRing B S hS X.1 X.2 V))
      (eJ : F.val.obj (op V) ≃ₗ[chartRing B S hS X.1 X.2 V] chartRing B S hS X.1 X.2 V ⧸ J)
      (a : chartRing B S hS X.1 X.2 V), a ∈ J → a ∈ (chartRing B S hS X.1 X.2 V)⁰ →
      geometricLength B S hS X xbar F = 0 := by
    intro F _ J eJ a haJ ha
    rw [geometricLength_eq_length_localizedModule_chartPrimeAt B S hS X F xbar V hV v hu,
      Module.length_localizedModule_eq_length_quotient_map _ ((chartScheme V).presheaf.stalk v) _
        eJ,
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ haJ) (hunit a ha),
      Module.length_eq_zero_iff]
    infer_instance
  exact ⟨key _ _ (meromorphicNumeratorQuotientSectionsEquiv B S hS X L t hL' hwa hfin V e hc hf ht
    hV) p hpJ hp0, key _ _ (meromorphicDenominatorQuotientSectionsEquiv B S hS X L t hL' hwa hfin V
    hV) q hqI q.2⟩

end AlgebraicGeometry.Space

end
