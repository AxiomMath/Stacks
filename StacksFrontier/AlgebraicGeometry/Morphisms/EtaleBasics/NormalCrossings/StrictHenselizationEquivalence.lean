module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.StrictHenselization
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.StrictHenselizationChart
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.JTwo
public import StacksFrontier.AlgebraicGeometry.Nagata
public import StacksFrontier.AlgebraicGeometry.SchemeJTwoLocal.JTwoTFAE
public import StacksFrontier.RingTheory.NormalCrossingsChart.NagataBranchShrink
public import StacksFrontier.RingTheory.Nagata.FiniteType
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Normal crossings divisors are recognized by their strict henselizations

Let `X` be a locally Noetherian scheme which is J-2 or Nagata and let `D ⊂ X` be a closed
subscheme. Then `D` is a normal crossings divisor exactly when, for every point `p` of `D`, the
pullback of `D` to the spectrum of the strict henselization `𝒪^{sh}_{X, p}` is a strict normal
crossings divisor.

## Main definitions

* `Stacks.Divisors.ChartShrink`: on every étale `R`-algebra, the locus where a principal quotient
  is a normal domain contains a Zariski neighbourhood of any point where that quotient is a
  regular local ring.

## Main results

* `Stacks.Divisors.chartShrink_of_isJ2`: the ring of an affine open of a locally Noetherian J-2
  scheme satisfies `ChartShrink`.
* `Stacks.Divisors.chartShrink_of_isNagataRing`: a Nagata ring satisfies `ChartShrink`.
* `Stacks.Divisors.isNormalCrossingsDivisor_iff_isStrictNormalCrossingsAtStrictHenselizations`:
  on a locally Noetherian scheme which is J-2 or Nagata, a closed subscheme is a normal crossings
  divisor if and only if its pullback to the strict henselization at each of its points is a
  strict normal crossings divisor.

## References

* [Stacks Project, Tag 0CBS](https://stacks.math.columbia.edu/tag/0CBS)
* [Stacks Project, Tag 0CBR](https://stacks.math.columbia.edu/tag/0CBR)
* [Stacks Project, Tag 07R3](https://stacks.math.columbia.edu/tag/07R3)
* [Stacks Project, Tag 033T](https://stacks.math.columbia.edu/tag/033T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Stacks.Divisors

/-- A ring `R` satisfies `ChartShrink` if for every étale `R`-algebra `B`, every `y ∈ B` and every
prime `q` of `B` containing `y` at which `B ⧸ (y)` is a regular local ring, there is `t ∉ q` such
that `B ⧸ (y)` is a normal domain at every prime containing `y` and not containing `t`. -/
public abbrev ChartShrink (R : Type u) [CommRing R] : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra R B], Algebra.Etale R B →
    ∀ (y : B) (q : PrimeSpectrum B) (hy : y ∈ q.asIdeal),
      IsRegularLocalRing (Localization.AtPrime
        (Stacks.NormalCrossingsChart.quotPoint y q hy).asIdeal) →
      ∃ t ∉ q.asIdeal, ∀ (q' : PrimeSpectrum B) (hy' : y ∈ q'.asIdeal), t ∉ q'.asIdeal →
        IsDomain (Localization.AtPrime
          (Stacks.NormalCrossingsChart.quotPoint y q' hy').asIdeal) ∧
        IsIntegrallyClosed (Localization.AtPrime
          (Stacks.NormalCrossingsChart.quotPoint y q' hy').asIdeal)

/-- A regular local ring is a normal domain. -/
@[ega "0 17.1.3"]
private theorem isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (A : Type u) [CommRing A]
    (h : IsRegularLocalRing A) : IsDomain A ∧ IsIntegrallyClosed A := by
  have := h
  have : IsDomain A := IsRegularLocalRing.isDomain A
  have := IsRegularLocalRing.uniqueFactorizationMonoid A
  exact ⟨inferInstance, inferInstance⟩

/-- If `X` is a locally Noetherian J-2 scheme and `ι : Spec R ⟶ X` is an open immersion, then `R`
satisfies `ChartShrink`. -/
public theorem chartShrink_of_isJ2 {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : AlgebraicGeometry.Scheme.IsJ2 X) (R : CommRingCat.{u}) (ι : Spec R ⟶ X)
    [IsOpenImmersion ι] : ChartShrink (R : Type u) := by
  intro B _ _ hBet y q hy hreg
  have := hBet
  have hJ1 : IsJ1 (B ⧸ (Ideal.span {y} : Ideal B)) := by
    have hcl : AlgebraicGeometry.IsClosedImmersion
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span {y} : Ideal B)))) :=
      AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hspecet : AlgebraicGeometry.Etale
        (Spec.map (CommRingCat.ofHom (algebraMap (R : Type u) B))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hBet)
    have hopen := hX.isOpen_regularLocus
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {y} : Ideal B))) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap (R : Type u) B)) ≫ ι))
    exact (AlgebraicGeometry.Scheme.isOpen_regularLocus_spec_iff
      (B ⧸ (Ideal.span {y} : Ideal B))).mp hopen
  obtain ⟨t, htq, ht⟩ :=
    Stacks.NormalCrossingsChart.exists_notMem_forall_isRegularLocalRing_quotient_of_isJ1 y hJ1 q hy
      (Localization.AtPrime q.asIdeal)
      ((Stacks.NormalCrossingsChart.isRegularLocalRing_quotient_iff_atPrime y q hy
        (Localization.AtPrime q.asIdeal)).mpr hreg)
  exact ⟨t, htq, fun q' hy' htq' => isDomain_and_isIntegrallyClosed_of_isRegularLocalRing _ <|
    (Stacks.NormalCrossingsChart.isRegularLocalRing_quotient_iff_atPrime y q' hy'
      (Localization.AtPrime q'.asIdeal)).mp (ht q' htq' hy' (Localization.AtPrime q'.asIdeal))⟩

/-- A Nagata ring satisfies `ChartShrink`. -/
public theorem chartShrink_of_isNagataRing {R : Type u} [CommRing R] (hR : IsNagataRing R) :
    ChartShrink R := by
  intro B _ _ hBet y q hy hreg
  have := hBet
  have : IsNoetherianRing R := hR.isNoetherianRing
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  have htfae : IsNagataRing R ↔
      ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.FiniteType R S], IsNagataRing S :=
    isNagataRing_tfae.out 1 2
  exact exists_notMem_forall_isDomain_and_isIntegrallyClosed_quotient_of_isNagataRing
    (htfae.mp hR B) y q hy hreg

/-- Let `X` be a locally Noetherian scheme and `D ⊂ X` a closed
subscheme. If `X` is J-2 or Nagata, then `D` is a normal crossings divisor in `X` if and only if
for every point `p` of `D` the pullback of `D` to the spectrum of the strict henselization
`𝒪^{sh}_{X, p}` is a strict normal crossings divisor. -/
@[stacks 0CBS]
public theorem isNormalCrossingsDivisor_iff_isStrictNormalCrossingsAtStrictHenselizations
    {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData)
    (hX : AlgebraicGeometry.Scheme.IsJ2 X ∨ IsNagataScheme X) :
    IsNormalCrossingsDivisor D ↔ IsStrictNormalCrossingsAtStrictHenselizations D := by
  refine ⟨fun hDnc x hx L _ _ _ Ash _ _ _ _ =>
    isStrictNormalCrossingsDivisor_comap_fromSpecStalk_of_isNormalCrossingsDivisor D hDnc x hx
      L Ash, fun hD => ?_⟩
  refine ⟨isEffectiveCartierDivisor_of_isStrictNormalCrossingsAtStrictHenselizations D hD,
    fun y => ?_⟩
  have hp : D.subschemeι y ∈ D.support :=
    (Scheme.IdealSheafData.range_subschemeι (I := D)).le ⟨y, rfl⟩
  obtain ⟨V, hpV, hshrink⟩ : ∃ (V : X.affineOpens) (_ : D.subschemeι y ∈ V.1),
      ChartShrink (Γ(X, V.1) : Type u) := by
    cases hX with
    | inl hJ2 =>
      obtain ⟨V, hpV⟩ := exists_affineOpens_mem (D.subschemeι y)
      have := V.2.isOpenImmersion_fromSpec
      exact ⟨V, hpV, chartShrink_of_isJ2 hJ2 Γ(X, V.1) V.2.fromSpec⟩
    | inr hNag =>
      obtain ⟨V, hpV, hNagR⟩ := hNag (D.subschemeι y)
      exact ⟨V, hpV, chartShrink_of_isNagataRing hNagR⟩
  have : IsNoetherianRing (Γ(X, V.1) : Type u) := IsLocallyNoetherian.component_noetherian V
  have := V.2.isOpenImmersion_fromSpec
  let algRA : Algebra (Γ(X, V.1) : Type u) (X.presheaf.stalk (D.subschemeι y)) :=
    X.presheaf.algebra_section_stalk ⟨D.subschemeι y, hpV⟩
  have hlocA : IsLocalization.AtPrime (X.presheaf.stalk (D.subschemeι y))
      (V.2.primeIdealOf ⟨D.subschemeι y, hpV⟩).asIdeal :=
    V.2.isLocalization_stalk ⟨D.subschemeι y, hpV⟩
  obtain ⟨U, g, hU, hg, ⟨u, hgu⟩, hfac⟩ :=
    exists_etale_chart_forall_normal_factorization D hD (D.subschemeι y) hp Γ(X, V.1)
      V.2.fromSpec (V.2.primeIdealOf ⟨D.subschemeι y, hpV⟩)
      (V.2.fromSpec_primeIdealOf ⟨D.subschemeι y, hpV⟩)
      (X.presheaf.germ V.1 (D.subschemeι y) hpV) rfl
      (V.2.fromSpecStalk_eq_fromSpecStalk hpV).symm hshrink
  have := hg
  have := hU
  exact ⟨U, g, hU, hg, ⟨u, hgu⟩,
    isStrictNormalCrossingsDivisor_comap_of_etale_of_forall_normal_factorization g D hD hfac⟩

end Stacks.Divisors

end
