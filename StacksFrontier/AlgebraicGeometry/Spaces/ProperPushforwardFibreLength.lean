module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPrimeAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubmoduleColimitNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageCartesianChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryChartFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicPullbackWeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFiniteAffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentChartStalkLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion
public import StacksFrontier.RingTheory.Length.FibreLengthSum

/-!
# The length of a direct image at a point with finite fibre

Let `g : Z ⟶ Y` be a proper morphism of decent algebraic spaces over `S`, with `Y` locally
Noetherian, let `G` be a coherent `𝒪_Z`-module and let `η ∈ |Y|` be a point whose fibre
`g⁻¹(η)` is finite. Assume that no point of `Supp(G)` maps to a strict generalization of `η`.
Then the length of `g_*G` at a geometric point over `η` is

`∑_{z ∈ g⁻¹(η)} length_z(G) · [κ(z) : κ(η)]`.

This is the local computation behind Stacks 0EP3 (and, for schemes, Stacks 02R6).

## Main results

* `AlgebraicGeometry.Space.continuous_chartSchemeToPoints`: the map from the points of the
  scheme of an étale chart to the points of the space is continuous.
* `AlgebraicGeometry.Space.geometricLength_modulePushforward_toNat_eq_finsum`: the formula above.

## Implementation notes

The proof is carried out on one étale chart. Because `g⁻¹(η)` is finite, `g` is finite over a
neighbourhood of `η`, and an elementary étale neighbourhood `V = Spec A` of `η` in it has a
single point `e` over `η` with the same residue field; the base change `U = Z ×_Y V = Spec B` is
then affine and finite over `V`
(`AlgebraicGeometry.Space.exists_finite_affine_chartDiagram`). The length at a geometric point
over `η` is the length over `A_e` of the localized sections `(g_*G)(V)_e`
(`AlgebraicGeometry.Space.geometricLength_eq_length_localizedModule_chartPrimeAt`); those sections
are `G(U)`, because the base change is represented by `U`
(`AlgebraicGeometry.Space.bijective_modulePushforwardCounitApp_of_isPullback`); the length of
`G(U)_e` over `A_e` is the sum over the primes of `B` above `e` of the residue degree times the
local length (`Stacks.Length.length_localizedModule_eq_finsum_fibre`, Stacks 02M0); and those
primes are the points of `U` over `e`, which are in bijection with `g⁻¹(η)` with the same residue
degrees (`AlgebraicGeometry.Space.bijOn_chartSchemeToPoints_fibre`,
`AlgebraicGeometry.Space.primeResidueDegree_chartPrime_eq_finrank`). The hypothesis on
generalizations is what makes `G(U)_e` of finite length: every prime of its support lies over
`e`.

## References

* [Stacks Project, Tag 0EP3](https://stacks.math.columbia.edu/tag/0EP3)
* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
* [Stacks Project, Tag 02M0](https://stacks.math.columbia.edu/tag/02M0)
* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 0A4Y](https://stacks.math.columbia.edu/tag/0A4Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The map from the points of the scheme of an étale chart to the points of the space is
continuous. -/
theorem continuous_chartSchemeToPoints {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : SmallEtale B S hS F) : Continuous (chartSchemeToPoints B S hS F U) := by
  have h : chartSchemeToPoints B S hS F U = pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS F).obj U)) U.obj.hom ∘
        (schemePointsHomeomorph B S hS ((SmallEtale.toOver B S hS F).obj U)).symm := by
    funext x
    exact chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS F U x
  rw [h]
  exact (continuous_pointsMap B S hS _).comp (Homeomorph.continuous_symm _)

/-- **The length of a direct image at a point with finite fibre.** Let `g : Z ⟶ Y` be a proper
morphism of decent algebraic spaces with `Y` locally Noetherian, `G` a coherent `𝒪_Z`-module and
`η ∈ |Y|` a point with finite fibre such that no point of `Supp(G)` maps to a strict
generalization of `η`. Then at a geometric point `ȳ` over `η`

`length_ȳ(g_*G) = ∑_{z ∈ g⁻¹(η)} length_z(G) · [κ(z) : κ(η)]`. -/
theorem geometricLength_modulePushforward_toNat_eq_finsum {Z Y : AlgebraicSpaces B S hS}
    (hZdec : IsDecentSpace B S hS Z.1) (hYdec : IsDecentSpace B S hS Y.1)
    (hYLN : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (g : Z ⟶ Y) (hg : IsProper B S hS g.hom)
    (G : Modules.{u, u} B S hS Z.1 Z.2) [IsCoherent B S hS Z.1 Z.2 G]
    (η : points B S hS Y.1)
    (hfin : {z : points B S hS Z.1 | pointsMap B S hS Z.1 g.hom z = η}.Finite)
    (hmax : ∀ z ∈ supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf _).obj G),
      η ∈ closure {pointsMap B S hS Z.1 g.hom z} → pointsMap B S hS Z.1 g.hom z = η)
    (ybar : GeometricPoint B S hS Y.1) (hybar : ybar.LiesOver η)
    (γ : points B S hS Z.1 → GeometricPoint B S hS Z.1) (hγ : ∀ z, (γ z).LiesOver z) :
    (geometricLength B S hS Y ybar ((modulePushforward B S hS g).obj G)).toNat =
      ∑ᶠ z ∈ {z : points B S hS Z.1 | pointsMap B S hS Z.1 g.hom z = η},
        (geometricLength B S hS Z (γ z) G).toNat *
          residueFieldDegreeAt B S hS Y.2 hZdec hYdec g.hom z := by
  classical
  obtain ⟨d, e, hd, hVaff, hUaff, hfinite, he, huniq, hmono⟩ :=
    exists_finite_affine_chartDiagram B S hS hZdec hYdec g hg η hfin
  have : G.IsQuasicoherentOnSite := inferInstance
  have hM : ((modulePushforward B S hS g).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS g hg.2.1.2
      (isQuasiSeparated_of_isSeparated B S hS hg.1) G inferInstance
  -- the rings and the module
  set r := (BigFppfOver.toScheme B S hS).map d.g with hr
  let A := chartRing B S hS Y.1 Y.2 d.V
  let Bₗ := chartRing B S hS Z.1 Z.2 d.U
  let φ : A →+* Bₗ := (chartDiagramPullback B S hS g d).hom
  let : Algebra A Bₗ := φ.toAlgebra
  let N := G.val.obj (op d.U)
  let : Module A N := Module.compHom N φ
  have : IsScalarTower A Bₗ N := ⟨fun a b n => mul_smul (φ a) b n⟩
  set p := chartPrimeAt B S hS Y.2 d.V e with hp
  -- step 1: the length at ybar is the length of the localized sections over the chart
  have h1 := geometricLength_eq_length_localizedModule_chartPrimeAt B S hS Y
    ((modulePushforward B S hS g).obj G) ybar d.V hVaff e (he.trans hybar.symm)
  -- step 2: transport along the bijection from the sections of `g_*G` over `V` to `G(U)`
  let M := ((modulePushforward B S hS g).obj G).val.obj (op d.V)
  let E₀ : M →ₗ[A] N :=
    { toFun := modulePushforwardCounitApp B S hS g G d
      map_add' := modulePushforwardCounitApp_add B S hS g G d
      map_smul' := fun a x => modulePushforwardCounitApp_smul B S hS g G d a x }
  let E : M ≃ₗ[A] N := LinearEquiv.ofBijective E₀
    (bijective_modulePushforwardCounitApp_of_isPullback B S hS g G d hd)
  have h2 : Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M) =
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl N) :=
    ((IsLocalizedModule.linearEquiv p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M)
      (LocalizedModule.mkLinearMap p.primeCompl N ∘ₗ E.toLinearMap)).extendScalarsOfIsLocalization
        p.primeCompl (Localization.AtPrime p)).length_eq
  -- step 3: the length of the localized sections as a sum over the primes of `B` above `p`
  have : _root_.AlgebraicGeometry.IsFinite r := hfinite
  have : IsAffine (chartScheme d.V) := hVaff
  have : IsAffine (chartScheme d.U) := hUaff
  have : Module.Finite A Bₗ := (Scheme.Hom.finite_appTop r : φ.Finite)
  have : IsNoetherianRing A := isNoetherianRing_chartRing_of_isAffine (hX := Y.2) hYLN hVaff
  have : Module.Finite Bₗ N :=
    moduleFinite_sections_of_isCoherent B S hS Z.1 Z.2 G inferInstance hUaff
  have hcomap : ∀ x, (chartPrimeAt B S hS Z.2 d.U x).comap (algebraMap A Bₗ) =
      chartPrimeAt B S hS Y.2 d.V (r.base x) := fun x => comap_chartPrimeAt B S hS g d x
  have hfibre : ∀ x, r.base x = e →
      (chartPrimeAt B S hS Z.2 d.U x).comap (algebraMap A Bₗ) = p := fun x hx => by
    rw [hcomap x, hx]
  have hbijU := bijective_chartPrimeAt B S hS Z.2 d.U hUaff
  have hbijV := bijective_chartPrimeAt B S hS Y.2 d.V hVaff
  have hsupp : ∀ Q : PrimeSpectrum Bₗ, Q ∈ Module.support Bₗ N →
      Q.asIdeal.comap (algebraMap A Bₗ) ≤ p → Q.asIdeal.comap (algebraMap A Bₗ) = p := by
    intro Q hQs hQle
    obtain ⟨x, rfl⟩ := hbijU.2 Q
    set z := chartSchemeToPoints B S hS Z.1 d.U x with hz
    have hlen := geometricLength_eq_length_localizedModule_chartPrimeAt B S hS Z G (γ z) d.U hUaff
      x (hγ z).symm
    have hnt : Nontrivial (LocalizedModule (chartPrimeAt B S hS Z.2 d.U x).primeCompl N) :=
      Module.mem_support_iff.mp hQs
    have hne : geometricLength B S hS Z (γ z) G ≠ 0 := by
      rw [hlen]
      intro h0
      exact not_subsingleton _ (Module.length_eq_zero_iff.mp h0)
    have hzS : z ∈ supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf _).obj G) := by
      refine (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk_of_liesOver B S hS Z G
        (γ z) z (hγ z)).mpr ?_
      by_contra hc
      exact hne (Module.length_eq_zero_iff.mpr (not_nontrivial_iff_subsingleton.mp hc))
    change (chartPrimeAt B S hS Z.2 d.U x).comap (algebraMap A Bₗ) ≤ p at hQle
    rw [hcomap x] at hQle
    have hsp : r.base x ⤳ e := (chartPrimeAt_le_chartPrime_iff B S hS Y.2 d.V hVaff _ _).mp hQle
    have hsp' : pointsMap B S hS Z.1 g.hom z ⤳ η := by
      have := hsp.map (continuous_chartSchemeToPoints B S hS d.V)
      rwa [he, chartSchemeToPoints_map_chartDiagram B S hS d x] at this
    have hgz := hmax z hzS (specializes_iff_mem_closure.mp hsp')
    have hrx : r.base x = e := huniq _ ((chartSchemeToPoints_map_chartDiagram B S hS d x).trans hgz)
    exact hfibre x hrx
  have h3 := Stacks.Length.length_localizedModule_eq_finsum_fibre p N hsupp
  have htop := Stacks.Length.length_localizedModule_ne_top_of_fibre p N hsupp
  -- step 4: primes of `Γ(U)` over `p` are the points of `U` over `e`
  set sU := {x : chartScheme d.U | r.base x = e} with hsU
  set fib := {z : points B S hS Z.1 | pointsMap B S hS Z.1 g.hom z = η} with hfib
  let Qof : chartScheme d.U → PrimeSpectrum Bₗ := fun x =>
    ⟨chartPrimeAt B S hS Z.2 d.U x, inferInstance⟩
  let T : PrimeSpectrum Bₗ → ℕ∞ := fun Q =>
    (Stacks.Length.primeResidueDegree (algebraMap A Bₗ) p Q.asIdeal : ℕ∞) *
      Module.length (Localization.AtPrime Q.asIdeal) (LocalizedModule Q.asIdeal.primeCompl N)
  have h4 : ∑ᶠ x ∈ sU, T (Qof x) =
      ∑ᶠ Q ∈ {Q : PrimeSpectrum Bₗ | Q.asIdeal.comap (algebraMap A Bₗ) = p}, T Q := by
    refine finsum_mem_eq_of_bijOn Qof ⟨fun x hx => ?_, hbijU.1.injOn, fun Q hQ => ?_⟩
      (fun x _ => rfl)
    · exact hfibre x hx
    · obtain ⟨x, rfl⟩ := hbijU.2 Q
      refine ⟨x, ?_, rfl⟩
      exact hbijV.1 (PrimeSpectrum.ext ((hcomap x).symm.trans hQ))
  -- step 5: points of `U` over `e` are the points of the fibre of `g` over `η`
  let degZ : points B S hS Z.1 → ℕ := fun z =>
    let := (residueFieldHom B S hS Z.1 Y.1 Y.2 hZdec hYdec g.hom z).toAlgebra
    Module.finrank (residueField B S hS Y.1 hYdec (pointsMap B S hS Z.1 g.hom z))
      (residueField B S hS Z.1 hZdec z)
  have h5 : ∑ᶠ x ∈ sU, T (Qof x) =
      ∑ᶠ z ∈ fib, (degZ z : ℕ∞) * geometricLength B S hS Z (γ z) G := by
    refine finsum_mem_eq_of_bijOn (chartSchemeToPoints B S hS Z.1 d.U)
      (bijOn_chartSchemeToPoints_fibre B S hS g d hd η e he huniq hmono)
      (fun x hx => ?_)
    have hdeg := primeResidueDegree_chartPrime_eq_finrank B S hS hZdec hYdec g d hd η e he huniq
      hmono x hx
    have hlen := geometricLength_eq_length_localizedModule_chartPrimeAt B S hS Z G
      (γ (chartSchemeToPoints B S hS Z.1 d.U x)) d.U hUaff x (hγ _).symm
    change (Stacks.Length.primeResidueDegree (chartDiagramPullback B S hS g d).hom
        (chartPrimeAt B S hS Y.2 d.V e) (chartPrimeAt B S hS Z.2 d.U x) : ℕ∞) * _ = _
    rw [hdeg, hlen]
  have hmain : geometricLength B S hS Y ybar ((modulePushforward B S hS g).obj G) =
      ∑ᶠ z ∈ fib, (degZ z : ℕ∞) * geometricLength B S hS Z (γ z) G := by
    rw [h1, h2, h3, ← h4, h5]
  -- step 6: pass to natural numbers
  have htop' : (∑ᶠ z ∈ fib, (degZ z : ℕ∞) * geometricLength B S hS Z (γ z) G) ≠ ⊤ := by
    rwa [← hmain, h1, h2]
  rw [hmain]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at htop' ⊢
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hterm : ∀ z ∈ hfin.toFinset, (degZ z : ℕ∞) * geometricLength B S hS Z (γ z) G ≠ ⊤ :=
    fun z hz => ne_top_of_le_ne_top htop'
      (Finset.single_le_sum (f := fun z => (degZ z : ℕ∞) * geometricLength B S hS Z (γ z) G)
        (fun _ _ => zero_le) hz)
  rw [ENat.toNat_sum hterm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [ENat.toNat_mul, ENat.toNat_natCast, mul_comm]
  rfl

end AlgebraicGeometry.Space

end
