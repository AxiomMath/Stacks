module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.SectionOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.Chart
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.LocalizedQuotientLength
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.MeromorphicDenominatorQuotients
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.OrderOfVanishingIdealIndex
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeNonAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentChartStalkLocalization

/-!
# The order of vanishing of a meromorphic section as a difference of lengths

Let `X` be a decent, locally Noetherian, integral algebraic space, `ℒ` an invertible module and
`t` a regular meromorphic section of `ℒ` with ideal of denominators `𝓘`. At the generic point `ξ`
of a prime divisor `Z ⊆ X`,

`ord_{Z, ℒ}(t) = length_ξ(ℒ / t 𝓘) - length_ξ(𝒪_X / 𝓘)`,

the lengths taken at a geometric point over `ξ`.

## Main results

* `AlgebraicGeometry.Space.toNat_geometricLength_numeratorQuotient_sub_eq_orderOfVanishingSection`:
  the order of vanishing of `t` along `Z` is `length_ξ(ℒ / t 𝓘) - length_ξ(𝒪_X / 𝓘)`.
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
  (X : AlgebraicSpaces B S hS) (hdec : IsDecentSpace B S hS X.1)
  (hInt : IsIntegralSpace B S hS X.1)
  (hN : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
  (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
  (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
  (L : Modules.{u, u} B S hS X.1 X.2) (hL : IsInvertibleModule X L)
  (t : MeromorphicSection.{u, u} B S hS X.1 X.2 L)
  (ht : IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 L t)

include hInt hN hwa hfin ht in
/-- Let `t` be a regular meromorphic section of an invertible module `ℒ` on a decent, locally
Noetherian, integral algebraic space `X`, with ideal of denominators `𝓘`, and let `xbar` be a
geometric point over the generic point of a prime divisor `Z`. Then the order of vanishing of `t`
along `Z` is the length of `ℒ / t 𝓘` at `xbar` minus the length of `𝒪_X / 𝓘` at `xbar`. -/
theorem toNat_geometricLength_numeratorQuotient_sub_eq_orderOfVanishingSection
    (Z : PrimeDivisor B S hS X.1) (xbar : GeometricPoint B S hS X.1)
    (hx : xbar.image = Z.genericPoint B S hS X.1) :
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Nontrivial ↥(W.genericHenselianLocalRing B S hS X.2 hdec) := fun W =>
      W.nontrivial_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS X.2 hdec) := fun W =>
      W.isNoetherianRing_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    haveI : ∀ W : PrimeDivisor B S hS X.1,
        Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS X.2 hdec) := fun W =>
      W.krullDimLE_genericHenselianLocalRing B S hS X.2 hdec hInt hN
    haveI : Fact (HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y)) :=
      ⟨hN⟩
    ((geometricLength B S hS X xbar (meromorphicNumeratorQuotient B S hS X L t
        (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL))).toNat : ℤ) -
      ((geometricLength B S hS X xbar (meromorphicDenominatorQuotient B S hS X L t
        (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL))).toNat : ℤ) =
      orderOfVanishingSection.{u, u} B S hS X.2 hdec Z L t
        (Z.canonicalLocalRatio B S hS X.2 hdec L hL hInt hN) := by
  have hL' := Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL
  have : Fact (HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y)) :=
    ⟨hN⟩
  obtain ⟨V, hV, v, e, hc, hf, -, -, -, hv, hcu, -⟩ :=
    exists_affine_chart_isUnit_chartRatio B S hS X hwa hfin L L hL hL t ht t ht
      (Z.genericPoint B S hS X.1)
  have hu : chartSchemeToPoints B S hS X.1 V v = xbar.image := hv.trans hx.symm
  have hIc := isCoherent_meromorphicDenominatorIdeal B S hS X L t hL' hwa hfin
  have hLc : IsCoherent B S hS X.1 X.2 L :=
    { __ := isQuasicoherentOnSite_of_isInvertible B S hS X L hL'
      __ := isCoherentOnSite_of_isInvertible L hL }
  have hQ₁ : IsCoherent B S hS X.1 X.2 (meromorphicDenominatorQuotient B S hS X L t hL') :=
    isCoherent_cokernel B S hS X.1 X.2 hIc inferInstance _
  have hQ₂ : IsCoherent B S hS X.1 X.2 (meromorphicNumeratorQuotient B S hS X L t hL') :=
    isCoherent_cokernel B S hS X.1 X.2 hIc hLc _
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
    rw [IsLocalization.AtPrime, hSm] at h
    exact h
  have h₁ := geometricLength_eq_length_localizedModule_chartPrimeAt B S hS X
    (meromorphicDenominatorQuotient B S hS X L t hL') xbar V hV v hu
  rw [Module.length_localizedModule_eq_length_quotient_map _ ((chartScheme V).presheaf.stalk v) _
    (meromorphicDenominatorQuotientSectionsEquiv B S hS X L t hL' hwa hfin V hV)] at h₁
  have h₂ := geometricLength_eq_length_localizedModule_chartPrimeAt B S hS X
    (meromorphicNumeratorQuotient B S hS X L t hL') xbar V hV v hu
  rw [Module.length_localizedModule_eq_length_quotient_map _ ((chartScheme V).presheaf.stalk v) _
    (meromorphicNumeratorQuotientSectionsEquiv B S hS X L t hL' hwa hfin V e hc hf ht hV)] at h₂
  rw [h₁, h₂]
  have hK := isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin V hV
  have := isLocallyNoetherian_chartScheme B S hS X hN V
  have : Ring.KrullDimLE 1 ((chartScheme V).presheaf.stalk v) :=
    Z.krullDimLE_chartStalk B S hS X.2 hdec V v hv
  have hc' : IsUnit (chartPointMeromorphicMap B S hS X V hV hK v
      (chartRatio B S hS X.1 X.2 L V e hc hf t)) := hcu.map _
  rw [Z.orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt B S hS hdec hInt hN hwa hfin
    L hL t ht V hV e hc hf v hv hc']
  let : Algebra (chartRing B S hS X.1 X.2 V)
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)) :=
    ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op V)).hom.toAlgebra
  let c : (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V) :=
    chartRatio B S hS X.1 X.2 L V e hc hf t
  have hI : ∀ a, a ∈ meromorphicDenominatorIdealAt B S hS X L t V ↔
      ∃ y : chartRing B S hS X.1 X.2 V,
        algebraMap _ ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)) y =
          algebraMap _ ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)) a * c :=
    fun a => isMeromorphicDenominator_iff_of_free B S hS X L t V e hc hf a
  have hJ' : ∀ y, y ∈ meromorphicNumeratorIdealAt B S hS X L t V e hc hf ↔
      ∃ a ∈ meromorphicDenominatorIdealAt B S hS X L t V,
        algebraMap _ ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)) y =
          algebraMap _ ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)) a * c :=
    fun y => Iff.rfl
  have hq : ∃ q ∈ meromorphicDenominatorIdealAt B S hS X L t V,
      algebraMap (chartRing B S hS X.1 X.2 V) ((chartScheme V).presheaf.stalk v) q ∈
        ((chartScheme V).presheaf.stalk v)⁰ := by
    have : IsFractionRing (chartRing B S hS X.1 X.2 V)
        ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)) := hK
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.mk'_surjective (chartRing B S hS X.1 X.2 V)⁰ c
    refine ⟨q, (hI q).2 ⟨p, ?_⟩, (chartScheme V).nonZeroDivisors_le_comap_germ_top v q.2⟩
    rw [← hpq, mul_comm]
    exact (IsLocalization.mk'_spec _ p q).symm
  exact Ring.toNat_length_quotient_map_sub_eq_ordTotalFracInt
    ((chartScheme V).presheaf.stalk v) (chartPrimeAt B S hS X.2 V v).primeCompl
    (chartPointMeromorphicMap B S hS X V hV hK v)
    (fun a => chartPointMeromorphicMap_algebraMap B S hS X V hV hK v a)
    c hc' _ _ hI hJ' hq

end AlgebraicGeometry.Space

end
