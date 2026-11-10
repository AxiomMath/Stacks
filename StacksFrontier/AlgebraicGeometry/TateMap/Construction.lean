module

public import StacksFrontier.AlgebraicGeometry.TateMap.DetNLSheaf
public import StacksFrontier.AlgebraicGeometry.TateMap.DualizingRestriction
public import StacksFrontier.AlgebraicGeometry.TateMap.Objects
public import StacksFrontier.AlgebraicGeometry.TateMap.Rule
public import StacksFrontier.RingTheory.TateMap.ClaimFinal
public import StacksFrontier.RingTheory.TateMap.ClassificationSyntomic

/-!
# Construction of the Tate map

Let `f : Y ⟶ X` be a locally quasi-finite syntomic morphism with `X` locally Noetherian. This
file constructs the Tate map `c_{Y/X} : det(NL_{Y/X}) ≅ ω_{Y/X}` of Stacks, Proposition 0FKD,
following the source's proof: around every point, `f` is on an affine chart a chart base change
of a quasi-finite basic chart of the universal family (a *classified chart*); the Tate map of
the universal chart, which is the unique isomorphism carrying `δ` to `τ` there, pulls back to an
isomorphism on the classified chart, these local isomorphisms glue by the Claim of the source
(`Stacks.TateMap.tateOf_eq_tateOf`), and the glued isomorphism carries `δ(NL_{Y/X})` to
`τ_{Y/X}`.

## Main definitions

* `AlgebraicGeometry.TateMap.ClassifiedChart`: a principal open of an affine chart of `f`
  together with a classification by a quasi-finite basic chart of the universal family.
* `AlgebraicGeometry.TateMap.tateIso`: the Tate map `det(NL_{Y/X}) ≅ ω_{Y/X}`.

## Main results

* `AlgebraicGeometry.TateMap.chartValue_restrict` and
  `AlgebraicGeometry.TateMap.chartValue_restrict_source`: the chart values of any isomorphism
  `det(NL_{Y/X}) ≅ ω_{Y/X}` on principal-open restriction squares are pullbacks.
* `AlgebraicGeometry.TateMap.exists_classified_basicOpen`: the classified charts form a basis.
* `AlgebraicGeometry.TateMap.chartValue_tateIso`: the chart value of the Tate map on a classified
  chart is the pullback of the Tate map of the universal chart.
* `AlgebraicGeometry.TateMap.tateIso_deltaNL`: the Tate map carries `δ(NL_{Y/X})` to `τ_{Y/X}`.

## References

* [Stacks Project, Tag 0FKD](https://stacks.math.columbia.edu/tag/0FKD)
* [Stacks Project, Tag 0FKA](https://stacks.math.columbia.edu/tag/0FKA)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped TensorProduct

open Stacks.Discriminant Stacks.AlgebraicGeometry.QuasicoherentBaseChange Stacks.TateMap

universe u

namespace AlgebraicGeometry.TateMap

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f : Y ⟶ X) (hf : IsQuasiFiniteSyntomic f)

omit [IsLocallyNoetherian X] in
/-- The chart identification of `det(NL_{Y/X})` on a principal-open restriction square, with the
two opens given by equations. -/
theorem detNLChartEquiv_restrict_of_eq (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (U₀ : X.affineOpens) (V₀ : Y.affineOpens) (a : Γ(X, U.1))
    (b : Γ(Y, V.1)) (ha : U₀.1 = X.basicOpen a) (hb : V₀.1 = Y.basicOpen b) (hU₀ : U₀.1 ≤ U.1)
    (hV₀ : V₀.1 ≤ V.1) (hV₀U₀ : V₀.1 ≤ f ⁻¹ᵁ U₀.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : Algebra Γ(X, U₀.1) Γ(Y, V₀.1) := (f.appLE U₀ V₀ hV₀U₀).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(X, U₀.1) := (X.presheaf.map (homOfLE hU₀).op).hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y, V₀.1) := (Y.presheaf.map (homOfLE hV₀).op).hom.toAlgebra
    haveI := algebra_syntomic_appLE hf.2 U V hVU
    haveI := algebra_syntomic_appLE hf.2 U₀ V₀ hV₀U₀
    ∀ (D : Stacks.TateMap.ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X, U₀.1) Γ(Y, V₀.1))
      (t : Γ(detNL f hf, V.1)),
      detNLChartEquiv f hf U₀ V₀ hV₀U₀ ((detNL f hf).presheaf.map (homOfLE hV₀).op t) =
        Stacks.TateMap.detNLBaseChange D ((1 : Γ(Y, V₀.1)) ⊗ₜ detNLChartEquiv f hf U V hVU t) := by
  obtain ⟨U₀, hU₀'⟩ := U₀
  obtain ⟨V₀, hV₀'⟩ := V₀
  simp only at ha hb
  subst ha hb
  exact detNLChartEquiv_restrict f hf U V hVU a b hV₀U₀

/-- The chart identifications of `ω_{Y/X}` on a principal-open restriction square, with the two
opens given by equations. -/
theorem localEquiv_restrict_of_eq (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (U₀ : X.affineOpens) (V₀ : Y.affineOpens) (a : Γ(X, U.1))
    (b : Γ(Y, V.1)) (ha : U₀.1 = X.basicOpen a) (hb : V₀.1 = Y.basicOpen b) (hU₀ : U₀.1 ≤ U.1)
    (hV₀ : V₀.1 ≤ V.1) (hV₀U₀ : V₀.1 ≤ f ⁻¹ᵁ U₀.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : Algebra Γ(X, U₀.1) Γ(Y, V₀.1) := (f.appLE U₀ V₀ hV₀U₀).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(X, U₀.1) := (X.presheaf.map (homOfLE hU₀).op).hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y, V₀.1) := (Y.presheaf.map (homOfLE hV₀).op).hom.toAlgebra
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    letI : IsNoetherianRing Γ(X, U₀.1) := IsLocallyNoetherian.component_noetherian U₀
    haveI := algebra_syntomic_appLE hf.2 U V hVU
    haveI := isLocallyNoetherian_source f hf
    haveI := hf.1
    ∀ (D : Stacks.TateMap.ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X, U₀.1) Γ(Y, V₀.1))
      (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
      (G : FiniteOpenFactorization.{u, u, u} Γ(X, U₀.1) Γ(Y, V₀.1)) (t : Γ(omega f hf, V.1)),
      (omegaData f hf).localEquiv U₀ V₀ hV₀U₀ G ((omega f hf).presheaf.map (homOfLE hV₀).op t) =
        Stacks.TateMap.omegaBaseChange D F G
          ((1 : Γ(Y, V₀.1)) ⊗ₜ (omegaData f hf).localEquiv U V hVU F t) := by
  have := isLocallyNoetherian_source f hf
  have := hf.1
  have : Flat f := AlgebraicGeometry.flat hf.2
  obtain ⟨U₀, hU₀'⟩ := U₀
  obtain ⟨V₀, hV₀'⟩ := V₀
  simp only at ha hb
  subst ha hb
  exact Stacks.TateMap.localEquiv_restrict_eq_omegaBaseChange (omegaData f hf) U V hVU a b hV₀U₀

/-- A morphism of sheaves of modules commutes with restriction of sections. -/
private theorem hom_app_restrict {M N : Y.Modules} (φ : M ⟶ N) {W W' : Y.Opens} (h : W' ≤ W)
    (s : Γ(M, W)) :
    φ.app W' (M.presheaf.map (homOfLE h).op s) = N.presheaf.map (homOfLE h).op (φ.app W s) :=
  congr($(φ.mapPresheaf.naturality (homOfLE h).op) s)

/-- **Chart values of an isomorphism `det(NL_{Y/X}) ≅ ω_{Y/X}` on a principal-open restriction
square are pullbacks.** -/
theorem chartValue_restrict (c : detNL f hf ≅ omega f hf) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (U₀ : X.affineOpens) (V₀ : Y.affineOpens)
    (a : Γ(X, U.1)) (b : Γ(Y, V.1)) (ha : U₀.1 = X.basicOpen a) (hb : V₀.1 = Y.basicOpen b)
    (hU₀ : U₀.1 ≤ U.1) (hV₀ : V₀.1 ≤ V.1) (hV₀U₀ : V₀.1 ≤ f ⁻¹ᵁ U₀.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : Algebra Γ(X, U₀.1) Γ(Y, V₀.1) := (f.appLE U₀ V₀ hV₀U₀).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(X, U₀.1) := (X.presheaf.map (homOfLE hU₀).op).hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y, V₀.1) := (Y.presheaf.map (homOfLE hV₀).op).hom.toAlgebra
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    letI : IsNoetherianRing Γ(X, U₀.1) := IsLocallyNoetherian.component_noetherian U₀
    haveI := algebra_syntomic_appLE hf.2 U V hVU
    haveI := algebra_syntomic_appLE hf.2 U₀ V₀ hV₀U₀
    ∀ (D : Stacks.TateMap.ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X, U₀.1) Γ(Y, V₀.1))
      (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
      (G : FiniteOpenFactorization.{u, u, u} Γ(X, U₀.1) Γ(Y, V₀.1)),
      chartValue c U₀ V₀ hV₀U₀ G = Stacks.TateMap.pullbackTate D (chartValue c U V hVU F) G := by
  intro D F G
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra Γ(X, U₀.1) Γ(Y, V₀.1) := (f.appLE U₀ V₀ hV₀U₀).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(X, U₀.1) := (X.presheaf.map (homOfLE hU₀).op).hom.toAlgebra
  let : Algebra Γ(Y, V.1) Γ(Y, V₀.1) := (Y.presheaf.map (homOfLE hV₀).op).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(X, U₀.1) := IsLocallyNoetherian.component_noetherian U₀
  have := algebra_syntomic_appLE hf.2 U V hVU
  have := algebra_syntomic_appLE hf.2 U₀ V₀ hV₀U₀
  have := isLocallyNoetherian_source f hf
  have := hf.1
  refine Stacks.TateMap.eq_pullbackTate D _ G _ fun x ↦ ?_
  obtain ⟨t, rfl⟩ := (detNLChartEquiv f hf U V hVU).surjective x
  rw [← detNLChartEquiv_restrict_of_eq f hf U V hVU U₀ V₀ a b ha hb hU₀ hV₀ hV₀U₀ D t]
  simp only [chartValue, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    sectionsLinearEquiv_of_iso_apply]
  rw [hom_app_restrict c.hom hV₀ t]
  exact localEquiv_restrict_of_eq f hf U V hVU U₀ V₀ a b ha hb hU₀ hV₀ hV₀U₀ D F G _

/-- `chartValue_restrict_source` for an algebra structure of `Γ(X, U)` over itself equal to the
restriction along `U ≤ U`. -/
private theorem chartValue_restrict_source_aux (c : detNL f hf ≅ omega f hf)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (b : Γ(Y, V.1))
    {inst : Algebra Γ(X, U.1) Γ(X, U.1)}
    (hinst : inst = (X.presheaf.map (homOfLE (le_refl U.1)).op).hom.toAlgebra) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(Y, Y.basicOpen b) :=
      (f.appLE U (Y.basicOpen b) ((Y.basicOpen_le b).trans hVU)).hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y, Y.basicOpen b) :=
      (Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op).hom.toAlgebra
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    haveI := algebra_syntomic_appLE hf.2 U V hVU
    haveI := algebra_syntomic_appLE hf.2 U ⟨Y.basicOpen b, V.2.basicOpen b⟩
      ((Y.basicOpen_le b).trans hVU)
    ∀ (D : Stacks.TateMap.ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X, U.1) Γ(Y, Y.basicOpen b))
      (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
      (G : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, Y.basicOpen b)),
      chartValue c U ⟨Y.basicOpen b, V.2.basicOpen b⟩ ((Y.basicOpen_le b).trans hVU) G =
        Stacks.TateMap.pullbackTate D (chartValue c U V hVU F) G := by
  subst hinst
  exact chartValue_restrict f hf c U V hVU U ⟨Y.basicOpen b, V.2.basicOpen b⟩ 1 b
    (X.basicOpen_one).symm rfl le_rfl (Y.basicOpen_le b) ((Y.basicOpen_le b).trans hVU)

/-- **Chart values on a source-only restriction square are pullbacks.** For an affine chart
`(U, V)` and `b ∈ Γ(Y, V)`, the chart value on `(U, D(b))` is the pullback of the chart value on
`(U, V)` along any chart base change datum of the square with the identity of `Γ(X, U)`. -/
theorem chartValue_restrict_source (c : detNL f hf ≅ omega f hf) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (b : Γ(Y, V.1)) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(Y, Y.basicOpen b) :=
      (f.appLE U (Y.basicOpen b) ((Y.basicOpen_le b).trans hVU)).hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y, Y.basicOpen b) :=
      (Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op).hom.toAlgebra
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    haveI := algebra_syntomic_appLE hf.2 U V hVU
    haveI := algebra_syntomic_appLE hf.2 U ⟨Y.basicOpen b, V.2.basicOpen b⟩
      ((Y.basicOpen_le b).trans hVU)
    ∀ (D : Stacks.TateMap.ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X, U.1) Γ(Y, Y.basicOpen b))
      (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
      (G : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, Y.basicOpen b)),
      chartValue c U ⟨Y.basicOpen b, V.2.basicOpen b⟩ ((Y.basicOpen_le b).trans hVU) G =
        Stacks.TateMap.pullbackTate D (chartValue c U V hVU F) G :=
  chartValue_restrict_source_aux f hf c U V hVU b (inst := Algebra.id _)
    (presheaf_map_toAlgebra_eq_id _).symm

include hf in
omit [IsLocallyNoetherian X] in
/-- **Classified principal opens form a basis.** For an affine chart `(U, V)` of `f`, a point
`y ∈ V` and a principal open `D(b₀) ∋ y` of `V`, there is a smaller principal open `D(b) ∋ y` of
`V` such that `Γ(X, U) → Γ(Y, D(b))` is a chart base change of a quasi-finite basic chart of the
universal family. -/
theorem exists_classified_basicOpen (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (y : Y) (hyV : y ∈ V.1) (b₀ : Γ(Y, V.1))
    (hy : y ∈ Y.basicOpen b₀) :
    ∃ b : Γ(Y, V.1), y ∈ Y.basicOpen b ∧ Y.basicOpen b ≤ Y.basicOpen b₀ ∧
      ∃ (n d : ℕ) (_ : NeZero d) (k : MvPolynomial (Fin n) (univBase.{u} n d))
        (_ : Algebra.QuasiFinite (univBase.{u} n d) (univChart n d k))
        (_ : Algebra (univBase.{u} n d) Γ(X, U.1))
        (_ : Algebra (univChart n d k) Γ(Y, Y.basicOpen b)),
        letI : Algebra Γ(X, U.1) Γ(Y, Y.basicOpen b) :=
          (f.appLE U (Y.basicOpen b) ((Y.basicOpen_le b).trans hVU)).hom.toAlgebra
        Nonempty (ChartBaseChange (univBase.{u} n d) (univChart n d k) Γ(X, U.1)
          Γ(Y, Y.basicOpen b)) := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  have := algebra_syntomic_appLE hf.2 U V hVU
  have := AlgebraicGeometry.quasiFinite_appLE hf.1 U V hVU
  let q := V.2.primeIdealOf ⟨y, hyV⟩
  have key (b : Γ(Y, V.1)) : y ∈ Y.basicOpen b ↔ b ∉ q.asIdeal := by
    have h : V.2.fromSpec q = y := V.2.fromSpec_primeIdealOf ⟨y, hyV⟩
    rw [← PrimeSpectrum.mem_basicOpen, ← V.2.fromSpec_preimage_basicOpen, ← h]
    exact Iff.rfl
  obtain ⟨b, hbq, ⟨c, hc⟩, n, d, hd, k, φ, hqf, H⟩ :=
    exists_classification_of_syntomic (A := Γ(X, U.1)) (B := Γ(Y, V.1)) q.asIdeal b₀
      ((key b₀).1 hy)
  refine ⟨b, (key b).2 hbq, ?_, n, d, hd, k, hqf, φ.toAlgebra, ?_⟩
  · rw [hc, Scheme.basicOpen_mul]
    exact inf_le_left
  let : Algebra Γ(Y, V.1) Γ(Y, Y.basicOpen b) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(Y, Y.basicOpen b) :=
    (f.appLE U (Y.basicOpen b) ((Y.basicOpen_le b).trans hVU)).hom.toAlgebra
  have : IsScalarTower Γ(X, U.1) Γ(Y, V.1) Γ(Y, Y.basicOpen b) :=
    IsScalarTower.of_algebraMap_eq' (by
      change (f.appLE U (Y.basicOpen b) ((Y.basicOpen_le b).trans hVU)).hom =
        ((Y.presheaf.map (homOfLE (Y.basicOpen_le b)).op).hom).comp (f.appLE U V hVU).hom
      rw [← CommRingCat.hom_comp, ← f.appLE_map hVU (homOfLE (Y.basicOpen_le b)).op])
  have : IsLocalization.Away b Γ(Y, Y.basicOpen b) := V.2.isLocalization_basicOpen b
  exact H Γ(Y, Y.basicOpen b)

/-- The isomorphism of sections over an affine chart `(U, V)` induced by an isomorphism
`φ : det(NL_{B/A}) ≅ ω_{B/A}`, through the chart identifications. -/
def chartSections (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (F : letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
      FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
    (φ : letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
      haveI := algebra_syntomic_appLE hf.2 U V hVU
      Stacks.TateMap.detNL Γ(X, U.1) Γ(Y, V.1) ≃ₗ[Γ(Y, V.1)] dualizingModule F) :
    Γ(detNL f hf, V.1) ≃ₗ[Γ(Y, V.1)] Γ(omega f hf, V.1) :=
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  haveI := algebra_syntomic_appLE hf.2 U V hVU
  letI := isLocallyNoetherian_source f hf
  letI := hf.1
  detNLChartEquiv f hf U V hVU ≪≫ₗ φ ≪≫ₗ ((omegaData f hf).localEquiv U V hVU F).symm

/-- An isomorphism `c` acting on the sections over `V` as `chartSections φ` has chart value `φ`. -/
theorem chartValue_eq_of_app (c : detNL f hf ≅ omega f hf) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (F : letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
      FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
    (φ : letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
      haveI := algebra_syntomic_appLE hf.2 U V hVU
      Stacks.TateMap.detNL Γ(X, U.1) Γ(Y, V.1) ≃ₗ[Γ(Y, V.1)] dualizingModule F)
    (h : ∀ s, c.hom.app V.1 s = chartSections f hf U V hVU F φ s) :
    chartValue c U V hVU F = φ := by
  refine LinearEquiv.ext fun x ↦ ?_
  simp only [chartValue, LinearEquiv.trans_apply, sectionsLinearEquiv_of_iso_apply, h,
    chartSections, LinearEquiv.apply_symm_apply]

/-- **Restricting the sections isomorphism of a chart to a principal-open restriction square
pulls back the chart isomorphism.** -/
theorem chartSections_restrict (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (U₀ : X.affineOpens) (V₀ : Y.affineOpens) (a : Γ(X, U.1)) (b : Γ(Y, V.1))
    (ha : U₀.1 = X.basicOpen a) (hb : V₀.1 = Y.basicOpen b) (hU₀ : U₀.1 ≤ U.1)
    (hV₀ : V₀.1 ≤ V.1) (hV₀U₀ : V₀.1 ≤ f ⁻¹ᵁ U₀.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : Algebra Γ(X, U₀.1) Γ(Y, V₀.1) := (f.appLE U₀ V₀ hV₀U₀).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(X, U₀.1) := (X.presheaf.map (homOfLE hU₀).op).hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y, V₀.1) := (Y.presheaf.map (homOfLE hV₀).op).hom.toAlgebra
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    letI : IsNoetherianRing Γ(X, U₀.1) := IsLocallyNoetherian.component_noetherian U₀
    haveI := algebra_syntomic_appLE hf.2 U V hVU
    haveI := algebra_syntomic_appLE hf.2 U₀ V₀ hV₀U₀
    ∀ (D : Stacks.TateMap.ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X, U₀.1) Γ(Y, V₀.1))
      (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
      (G : FiniteOpenFactorization.{u, u, u} Γ(X, U₀.1) Γ(Y, V₀.1))
      (φ : Stacks.TateMap.detNL Γ(X, U.1) Γ(Y, V.1) ≃ₗ[Γ(Y, V.1)] dualizingModule F)
      (s : Γ(detNL f hf, V.1)),
      (omega f hf).presheaf.map (homOfLE hV₀).op (chartSections f hf U V hVU F φ s) =
        chartSections f hf U₀ V₀ hV₀U₀ G (Stacks.TateMap.pullbackTate D φ G)
          ((detNL f hf).presheaf.map (homOfLE hV₀).op s) := by
  intro D F G φ s
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra Γ(X, U₀.1) Γ(Y, V₀.1) := (f.appLE U₀ V₀ hV₀U₀).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(X, U₀.1) := (X.presheaf.map (homOfLE hU₀).op).hom.toAlgebra
  let : Algebra Γ(Y, V.1) Γ(Y, V₀.1) := (Y.presheaf.map (homOfLE hV₀).op).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(X, U₀.1) := IsLocallyNoetherian.component_noetherian U₀
  have := algebra_syntomic_appLE hf.2 U V hVU
  have := algebra_syntomic_appLE hf.2 U₀ V₀ hV₀U₀
  have := isLocallyNoetherian_source f hf
  have := hf.1
  apply ((omegaData f hf).localEquiv U₀ V₀ hV₀U₀ G).injective
  rw [localEquiv_restrict_of_eq f hf U V hVU U₀ V₀ a b ha hb hU₀ hV₀ hV₀U₀ D F G]
  simp only [chartSections, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [detNLChartEquiv_restrict_of_eq f hf U V hVU U₀ V₀ a b ha hb hU₀ hV₀ hV₀U₀ D s,
    Stacks.TateMap.pullbackTate_detNLBaseChange_one_tmul]

/-- The chart value does not depend on the factorization computing `ω_{B/A}`. -/
theorem chartValue_natural (c : detNL f hf ≅ omega f hf) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (F G : letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
      FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1)) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    chartValue c U V hVU F ≪≫ₗ dualizingModuleEquiv F G = chartValue c U V hVU G := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have := isLocallyNoetherian_source f hf
  have := hf.1
  refine LinearEquiv.ext fun x ↦ ?_
  simp only [chartValue, LinearEquiv.trans_apply]
  exact ((omegaData f hf).localEquiv_natural U V hVU F G _).symm

/-- A **classified chart** of `f`: a principal open `D(b)` of an affine open `V` of `Y` lying over
an affine open `U` of `X`, together with a classification of `Γ(X, U) → Γ(Y, D(b))`: a chart base
change from a quasi-finite basic chart of the universal family. -/
structure ClassifiedChart where
  /-- The affine open of the base. -/
  base : X.affineOpens
  /-- The affine open of the source in which the chart is a principal open. -/
  chart : Y.affineOpens
  /-- The source chart lies over the base. -/
  le : chart.1 ≤ f ⁻¹ᵁ base.1
  /-- The function cutting out the principal open. -/
  b : Γ(Y, chart.1)
  /-- The number of variables of the universal chart. -/
  n : ℕ
  /-- The degree bound of the universal chart. -/
  d : ℕ
  /-- The degree bound is positive. -/
  neZero : NeZero d
  /-- The localizing polynomial of the universal chart. -/
  k : MvPolynomial (Fin n) (univBase.{u} n d)
  /-- The universal chart is quasi-finite. -/
  quasiFinite : Algebra.QuasiFinite (univBase.{u} n d) (univChart n d k)
  /-- The map of bases. -/
  instR : Algebra (univBase.{u} n d) Γ(X, base.1)
  /-- The map of sources. -/
  instC : Algebra (univChart n d k) Γ(Y, Y.basicOpen b)
  /-- The classification. -/
  data : letI : Algebra Γ(X, base.1) Γ(Y, Y.basicOpen b) :=
      (f.appLE base (Y.basicOpen b) ((Y.basicOpen_le b).trans le)).hom.toAlgebra
    @ChartBaseChange (univBase.{u} n d) (univChart n d k) Γ(X, base.1) Γ(Y, Y.basicOpen b) _ _ _ _
      _ instR _ instC

namespace ClassifiedChart

variable {f}

/-- The principal open of a classified chart, as an affine open. -/
abbrev source (κ : ClassifiedChart f) : Y.affineOpens :=
  ⟨Y.basicOpen κ.b, κ.chart.2.basicOpen κ.b⟩

omit [IsLocallyNoetherian X] in
/-- The principal open of a classified chart lies over its base. -/
theorem source_le (κ : ClassifiedChart f) : κ.source.1 ≤ f ⁻¹ᵁ κ.base.1 :=
  (Y.basicOpen_le κ.b).trans κ.le

end ClassifiedChart

/-- A finite-open factorization of the chart ring map of a classified chart. -/
def classifiedFact (κ : ClassifiedChart f) :
    letI : Algebra Γ(X, κ.base.1) Γ(Y, κ.source.1) :=
      (f.appLE κ.base κ.source κ.source_le).hom.toAlgebra
    FiniteOpenFactorization.{u, u, u} Γ(X, κ.base.1) Γ(Y, κ.source.1) :=
  haveI := hf.1
  haveI := locallyOfFiniteType f hf
  (nonempty_relativeDualizingChartFactorization f κ.base κ.source κ.source_le).some

/-- The Tate map of a classified chart: the pullback of the Tate map of its universal chart. -/
def classifiedTate (κ : ClassifiedChart f) :
    letI : Algebra Γ(X, κ.base.1) Γ(Y, κ.source.1) :=
      (f.appLE κ.base κ.source κ.source_le).hom.toAlgebra
    haveI := algebra_syntomic_appLE hf.2 κ.base κ.source κ.source_le
    Stacks.TateMap.detNL Γ(X, κ.base.1) Γ(Y, κ.source.1) ≃ₗ[Γ(Y, κ.source.1)]
      dualizingModule (classifiedFact f hf κ) :=
  letI : Algebra Γ(X, κ.base.1) Γ(Y, κ.source.1) :=
    (f.appLE κ.base κ.source κ.source_le).hom.toAlgebra
  haveI := algebra_syntomic_appLE hf.2 κ.base κ.source κ.source_le
  haveI : IsNoetherianRing Γ(X, κ.base.1) := IsLocallyNoetherian.component_noetherian κ.base
  haveI := κ.neZero
  haveI := κ.quasiFinite
  tateOf κ.k κ.instR κ.instC κ.data (classifiedFact f hf κ)

/-- The isomorphism of sections over a classified chart given by its Tate map. -/
def classifiedEquiv (κ : ClassifiedChart f) :
    Γ(detNL f hf, κ.source.1) ≃ₗ[Γ(Y, κ.source.1)] Γ(omega f hf, κ.source.1) :=
  chartSections f hf κ.base κ.source κ.source_le (classifiedFact f hf κ) (classifiedTate f hf κ)

include hf in
omit [IsLocallyNoetherian X] in
/-- **The classified charts form a basis of the topology of `Y`.** -/
theorem exists_classifiedChart (W : Y.Opens) (x : Y) (hx : x ∈ W) :
    ∃ κ : ClassifiedChart f, x ∈ κ.source.1 ∧ κ.source.1 ≤ W := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := f.base x) (U := ⊤) (by simp)
  obtain ⟨V, hV, hxV, hVW⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := x) (U := W ⊓ f ⁻¹ᵁ U) ⟨hx, hxU⟩
  obtain ⟨b, hxb, hb1, n, d, hd, k, hqf, instR, instC, ⟨D⟩⟩ :=
    exists_classified_basicOpen f hf ⟨U, hU⟩ ⟨V, hV⟩ (hVW.trans inf_le_right) x hxV 1
      (by rwa [Scheme.basicOpen_one])
  exact ⟨⟨⟨U, hU⟩, ⟨V, hV⟩, hVW.trans inf_le_right, b, n, d, hd, k, hqf, instR, instC, D⟩, hxb,
    hb1.trans ((Scheme.basicOpen_one (X := Y) (U := V)).le.trans (hVW.trans inf_le_left))⟩

/-- Restriction of sections along two nested opens is restriction along the composite. -/
private theorem presheaf_map_map {M : Y.Modules} {W W' W'' : Y.Opens} (h₁ : W' ≤ W)
    (h₂ : W'' ≤ W') (s : Γ(M, W)) :
    M.presheaf.map (homOfLE h₂).op (M.presheaf.map (homOfLE h₁).op s) =
      M.presheaf.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The ring map `R → S → T` makes `T` an `R`-algebra such that `R → S → T` is a scalar tower. -/
private theorem isScalarTower_comp_toAlgebra {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] (iR : Algebra R S) [Algebra S T] :
    letI : Algebra R T := ((algebraMap S T).comp (@algebraMap _ _ _ _ iR)).toAlgebra
    @IsScalarTower R S T iR.toSMul Algebra.toSMul Algebra.toSMul :=
  @IsScalarTower.of_algebraMap_eq' _ _ _ _ _ _ iR _
    ((algebraMap S T).comp (@algebraMap _ _ _ _ iR)).toAlgebra rfl

/-- **The Claim on a common chart**: the pullbacks of the Tate maps of two classified charts to a
common affine chart agree. -/
theorem pullbackTate_classifiedTate_eq (κ l : ClassifiedChart f) (U₀ : X.affineOpens)
    (V₀ : Y.affineOpens) (hU₀l : U₀.1 ≤ l.base.1) (hV₀l : V₀.1 ≤ l.source.1)
    (hU₀κ : U₀.1 ≤ κ.base.1) (hV₀κ : V₀.1 ≤ κ.source.1) (hV₀U₀ : V₀.1 ≤ f ⁻¹ᵁ U₀.1) :
    letI : Algebra Γ(X, U₀.1) Γ(Y, V₀.1) := (f.appLE U₀ V₀ hV₀U₀).hom.toAlgebra
    letI : Algebra Γ(X, l.base.1) Γ(Y, l.source.1) :=
      (f.appLE l.base l.source l.source_le).hom.toAlgebra
    letI : Algebra Γ(X, κ.base.1) Γ(Y, κ.source.1) :=
      (f.appLE κ.base κ.source κ.source_le).hom.toAlgebra
    letI : Algebra Γ(X, l.base.1) Γ(X, U₀.1) := (X.presheaf.map (homOfLE hU₀l).op).hom.toAlgebra
    letI : Algebra Γ(Y, l.source.1) Γ(Y, V₀.1) :=
      (Y.presheaf.map (homOfLE hV₀l).op).hom.toAlgebra
    letI : Algebra Γ(X, κ.base.1) Γ(X, U₀.1) := (X.presheaf.map (homOfLE hU₀κ).op).hom.toAlgebra
    letI : Algebra Γ(Y, κ.source.1) Γ(Y, V₀.1) :=
      (Y.presheaf.map (homOfLE hV₀κ).op).hom.toAlgebra
    haveI := algebra_syntomic_appLE hf.2 U₀ V₀ hV₀U₀
    haveI := algebra_syntomic_appLE hf.2 l.base l.source l.source_le
    haveI := algebra_syntomic_appLE hf.2 κ.base κ.source κ.source_le
    haveI : IsNoetherianRing Γ(X, U₀.1) := IsLocallyNoetherian.component_noetherian U₀
    haveI : IsNoetherianRing Γ(X, l.base.1) := IsLocallyNoetherian.component_noetherian l.base
    haveI : IsNoetherianRing Γ(X, κ.base.1) := IsLocallyNoetherian.component_noetherian κ.base
    ∀ (Dl : ChartBaseChange Γ(X, l.base.1) Γ(Y, l.source.1) Γ(X, U₀.1) Γ(Y, V₀.1))
      (Dκ : ChartBaseChange Γ(X, κ.base.1) Γ(Y, κ.source.1) Γ(X, U₀.1) Γ(Y, V₀.1))
      (G₀ : FiniteOpenFactorization.{u, u, u} Γ(X, U₀.1) Γ(Y, V₀.1)),
      pullbackTate Dl (classifiedTate f hf l) G₀ = pullbackTate Dκ (classifiedTate f hf κ) G₀ := by
  intro Dl Dκ G₀
  let : Algebra Γ(X, U₀.1) Γ(Y, V₀.1) := (f.appLE U₀ V₀ hV₀U₀).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U₀.1) := IsLocallyNoetherian.component_noetherian U₀
  have := algebra_syntomic_appLE hf.2 U₀ V₀ hV₀U₀
  have := AlgebraicGeometry.quasiFinite_appLE hf.1 U₀ V₀ hV₀U₀
  let : Algebra Γ(X, l.base.1) Γ(Y, l.source.1) :=
    (f.appLE l.base l.source l.source_le).hom.toAlgebra
  let : Algebra Γ(X, κ.base.1) Γ(Y, κ.source.1) :=
    (f.appLE κ.base κ.source κ.source_le).hom.toAlgebra
  let : Algebra Γ(X, l.base.1) Γ(X, U₀.1) := (X.presheaf.map (homOfLE hU₀l).op).hom.toAlgebra
  let : Algebra Γ(Y, l.source.1) Γ(Y, V₀.1) := (Y.presheaf.map (homOfLE hV₀l).op).hom.toAlgebra
  let : Algebra Γ(X, κ.base.1) Γ(X, U₀.1) := (X.presheaf.map (homOfLE hU₀κ).op).hom.toAlgebra
  let : Algebra Γ(Y, κ.source.1) Γ(Y, V₀.1) := (Y.presheaf.map (homOfLE hV₀κ).op).hom.toAlgebra
  have := algebra_syntomic_appLE hf.2 l.base l.source l.source_le
  have := algebra_syntomic_appLE hf.2 κ.base κ.source κ.source_le
  have : IsNoetherianRing Γ(X, l.base.1) := IsLocallyNoetherian.component_noetherian l.base
  have : IsNoetherianRing Γ(X, κ.base.1) := IsLocallyNoetherian.component_noetherian κ.base
  have := l.neZero
  have := l.quasiFinite
  have := κ.neZero
  have := κ.quasiFinite
  change pullbackTate Dl (tateOf l.k l.instR l.instC l.data (classifiedFact f hf l)) G₀ =
    pullbackTate Dκ (tateOf κ.k κ.instR κ.instC κ.data (classifiedFact f hf κ)) G₀
  let iRl : Algebra (univBase.{u} l.n l.d) Γ(X, U₀.1) :=
    ((algebraMap Γ(X, l.base.1) Γ(X, U₀.1)).comp (@algebraMap _ _ _ _ l.instR)).toAlgebra
  let iCl : Algebra (univChart l.n l.d l.k) Γ(Y, V₀.1) :=
    ((algebraMap Γ(Y, l.source.1) Γ(Y, V₀.1)).comp (@algebraMap _ _ _ _ l.instC)).toAlgebra
  have := isScalarTower_comp_toAlgebra l.instR (T := Γ(X, U₀.1)) (S := Γ(X, l.base.1))
  have := isScalarTower_comp_toAlgebra l.instC (T := Γ(Y, V₀.1)) (S := Γ(Y, l.source.1))
  let iRκ : Algebra (univBase.{u} κ.n κ.d) Γ(X, U₀.1) :=
    ((algebraMap Γ(X, κ.base.1) Γ(X, U₀.1)).comp (@algebraMap _ _ _ _ κ.instR)).toAlgebra
  let iCκ : Algebra (univChart κ.n κ.d κ.k) Γ(Y, V₀.1) :=
    ((algebraMap Γ(Y, κ.source.1) Γ(Y, V₀.1)).comp (@algebraMap _ _ _ _ κ.instC)).toAlgebra
  have := isScalarTower_comp_toAlgebra κ.instR (T := Γ(X, U₀.1)) (S := Γ(X, κ.base.1))
  have := isScalarTower_comp_toAlgebra κ.instC (T := Γ(Y, V₀.1)) (S := Γ(Y, κ.source.1))
  let := l.instR
  let := l.instC
  let := κ.instR
  let := κ.instC
  rw [tateOf_pullbackTate l.k l.instR l.instC l.data Dl (Dl.comp l.data),
    tateOf_pullbackTate κ.k κ.instR κ.instC κ.data Dκ (Dκ.comp κ.data)]
  have := isLocallyNoetherian_source f hf
  have : IsNoetherianRing Γ(Y, V₀.1) := IsLocallyNoetherian.component_noetherian V₀
  exact tateOf_eq_tateOf _ _ _ _ _ _ _ _ G₀

/-- **The Tate maps of two classified charts agree on their overlap**, by the Claim. -/
theorem classifiedEquiv_restrict (κ l : ClassifiedChart f) (h : l.source.1 ≤ κ.source.1)
    (s : Γ(detNL f hf, κ.source.1)) :
    classifiedEquiv f hf l ((detNL f hf).presheaf.map (homOfLE h).op s) =
      (omega f hf).presheaf.map (homOfLE h).op (classifiedEquiv f hf κ s) := by
  refine (Scheme.Modules.isSheaf (omega f hf)).section_ext fun y hy ↦ ?_
  obtain ⟨a₁, a₂, b₁, b₂, ha, hb, hyb, hba, hbW⟩ := exists_common_basicOpen f κ.base l.base
    κ.source l.source κ.source_le l.source_le y (h hy) hy l.source.1 hy
  let U₀ : X.affineOpens := ⟨X.basicOpen a₁, κ.base.2.basicOpen a₁⟩
  let V₀ : Y.affineOpens := ⟨Y.basicOpen b₁, κ.source.2.basicOpen b₁⟩
  have hV₀l : V₀.1 ≤ l.source.1 := hbW
  have hV₀κ : V₀.1 ≤ κ.source.1 := hbW.trans h
  have hU₀l : U₀.1 ≤ l.base.1 := by
    change X.basicOpen a₁ ≤ _
    rw [ha]
    exact X.basicOpen_le a₂
  have hV₀U₀ : V₀.1 ≤ f ⁻¹ᵁ U₀.1 := hba
  refine ⟨V₀.1, hV₀l, hyb, ?_⟩
  let : Algebra Γ(X, U₀.1) Γ(Y, V₀.1) := (f.appLE U₀ V₀ hV₀U₀).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U₀.1) := IsLocallyNoetherian.component_noetherian U₀
  have := algebra_syntomic_appLE hf.2 U₀ V₀ hV₀U₀
  have := AlgebraicGeometry.quasiFinite_appLE hf.1 U₀ V₀ hV₀U₀
  have := hf.1
  have := locallyOfFiniteType f hf
  let G₀ := (nonempty_relativeDualizingChartFactorization f U₀ V₀ hV₀U₀).some
  let Dl := chartBaseChangeBasicOpen f l.base l.source l.source_le U₀.1 V₀.1 a₂ b₂ ha hb hU₀l
    hV₀l hV₀U₀
  let Dκ := chartBaseChangeBasicOpen f κ.base κ.source κ.source_le U₀.1 V₀.1 a₁ b₁ rfl rfl
    (X.basicOpen_le a₁) hV₀κ hV₀U₀
  have hl := chartSections_restrict f hf l.base l.source l.source_le U₀ V₀ a₂ b₂ ha hb hU₀l
    hV₀l hV₀U₀ Dl (classifiedFact f hf l) G₀ (classifiedTate f hf l)
    ((detNL f hf).presheaf.map (homOfLE h).op s)
  have hκ := chartSections_restrict f hf κ.base κ.source κ.source_le U₀ V₀ a₁ b₁ rfl rfl
    (X.basicOpen_le a₁) hV₀κ hV₀U₀ Dκ (classifiedFact f hf κ) G₀ (classifiedTate f hf κ) s
  change (omega f hf).presheaf.map (homOfLE hV₀l).op
      (chartSections f hf l.base l.source l.source_le (classifiedFact f hf l)
        (classifiedTate f hf l) _) = (omega f hf).presheaf.map (homOfLE hV₀l).op
      ((omega f hf).presheaf.map (homOfLE h).op
        (chartSections f hf κ.base κ.source κ.source_le (classifiedFact f hf κ)
          (classifiedTate f hf κ) s))
  rw [hl, presheaf_map_map (M := detNL f hf), presheaf_map_map (M := omega f hf), hκ]
  congr 1
  exact congrArg (chartSections f hf U₀ V₀ hV₀U₀ G₀) (pullbackTate_classifiedTate_eq f hf κ l U₀ V₀
    hU₀l hV₀l (X.basicOpen_le a₁) hV₀κ hV₀U₀ Dl Dκ G₀)

/-- **The Tate map exists on sections**: an isomorphism `det(NL_{Y/X}) ≅ ω_{Y/X}` acting on the
sections over every classified chart by the Tate map of that chart. -/
theorem exists_tateIso :
    ∃ c : detNL f hf ≅ omega f hf, ∀ (κ : ClassifiedChart f) (s : Γ(detNL f hf, κ.source.1)),
      c.hom.app κ.source.1 s = classifiedEquiv f hf κ s :=
  exists_iso_of_basis (fun κ : ClassifiedChart f ↦ κ.source.1)
    (fun V x hx ↦ exists_classifiedChart f hf V x hx) (classifiedEquiv f hf)
    (fun κ l h s ↦ classifiedEquiv_restrict f hf κ l h s)

/-- **The Tate map** `c_{Y/X} : det(NL_{Y/X}) ≅ ω_{Y/X}` of a locally quasi-finite syntomic
morphism with locally Noetherian target: glued from the pullbacks of the Tate maps of the
universal family along classifications. -/
def tateIso : detNL f hf ≅ omega f hf :=
  (exists_tateIso f hf).choose

/-- The Tate map acts on the sections over a classified chart by its Tate map. -/
theorem tateIso_app (κ : ClassifiedChart f) (s : Γ(detNL f hf, κ.source.1)) :
    (tateIso f hf).hom.app κ.source.1 s = classifiedEquiv f hf κ s :=
  (exists_tateIso f hf).choose_spec κ s

/-- **The chart value of the Tate map on a classified chart** is the pullback of the Tate map of
the universal chart along the classification. -/
theorem chartValue_tateIso (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (b : Γ(Y, V.1)) {n d : ℕ} [NeZero d] (k : MvPolynomial (Fin n) (univBase.{u} n d))
    [Algebra.QuasiFinite (univBase.{u} n d) (univChart n d k)]
    (instR : Algebra (univBase.{u} n d) Γ(X, U.1))
    (instC : Algebra (univChart n d k) Γ(Y, Y.basicOpen b))
    (D : letI : Algebra Γ(X, U.1) Γ(Y, Y.basicOpen b) :=
        (f.appLE U (Y.basicOpen b) ((Y.basicOpen_le b).trans hVU)).hom.toAlgebra
      @ChartBaseChange (univBase.{u} n d) (univChart n d k) Γ(X, U.1) Γ(Y, Y.basicOpen b) _ _ _ _
        _ instR _ instC)
    (G : letI : Algebra Γ(X, U.1) Γ(Y, Y.basicOpen b) :=
        (f.appLE U (Y.basicOpen b) ((Y.basicOpen_le b).trans hVU)).hom.toAlgebra
      FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, Y.basicOpen b)) :
    letI : Algebra Γ(X, U.1) Γ(Y, Y.basicOpen b) :=
      (f.appLE U (Y.basicOpen b) ((Y.basicOpen_le b).trans hVU)).hom.toAlgebra
    haveI := algebra_syntomic_appLE hf.2 U ⟨Y.basicOpen b, V.2.basicOpen b⟩
      ((Y.basicOpen_le b).trans hVU)
    haveI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    chartValue (tateIso f hf) U ⟨Y.basicOpen b, V.2.basicOpen b⟩ ((Y.basicOpen_le b).trans hVU)
      G = tateOf k instR instC D G := by
  let : Algebra Γ(X, U.1) Γ(Y, Y.basicOpen b) :=
    (f.appLE U (Y.basicOpen b) ((Y.basicOpen_le b).trans hVU)).hom.toAlgebra
  have := algebra_syntomic_appLE hf.2 U ⟨Y.basicOpen b, V.2.basicOpen b⟩
    ((Y.basicOpen_le b).trans hVU)
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let κ : ClassifiedChart f :=
    ⟨U, V, hVU, b, n, d, inferInstance, k, inferInstance, instR, instC, D⟩
  have h₁ : chartValue (tateIso f hf) U κ.source κ.source_le (classifiedFact f hf κ) =
      classifiedTate f hf κ :=
    chartValue_eq_of_app f hf _ U κ.source κ.source_le _ _ (tateIso_app f hf κ)
  rw [← chartValue_natural f hf (tateIso f hf) U κ.source κ.source_le (classifiedFact f hf κ) G]
  change chartValue (tateIso f hf) U κ.source κ.source_le (classifiedFact f hf κ) ≪≫ₗ _ = _
  rw [h₁]
  exact pullbackTate_natural_right D _ (classifiedFact f hf κ) G

/-- **Clause (1): the Tate map carries `δ(NL_{Y/X})` to `τ_{Y/X}`.** -/
theorem tateIso_deltaNL : (tateIso f hf).hom.app ⊤ (deltaNL f hf) = tau f hf := by
  refine (Scheme.Modules.isSheaf (omega f hf)).section_ext fun y _ ↦ ?_
  obtain ⟨κ, hyκ, -⟩ := exists_classifiedChart f hf ⊤ y trivial
  refine ⟨κ.source.1, le_top, hyκ, ?_⟩
  rw [← hom_app_restrict, tateIso_app]
  let : Algebra Γ(X, κ.base.1) Γ(Y, κ.source.1) :=
    (f.appLE κ.base κ.source κ.source_le).hom.toAlgebra
  have := algebra_syntomic_appLE hf.2 κ.base κ.source κ.source_le
  have := AlgebraicGeometry.quasiFinite_appLE hf.1 κ.base κ.source κ.source_le
  have : IsNoetherianRing Γ(X, κ.base.1) := IsLocallyNoetherian.component_noetherian κ.base
  have := isLocallyNoetherian_source f hf
  have : IsNoetherianRing Γ(Y, κ.source.1) := IsLocallyNoetherian.component_noetherian κ.source
  have := hf.1
  have : Flat f := AlgebraicGeometry.flat hf.2
  have := κ.neZero
  have := κ.quasiFinite
  apply ((omegaData f hf).localEquiv κ.base κ.source κ.source_le (classifiedFact f hf κ)).injective
  simp only [classifiedEquiv, chartSections, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [detNLChartEquiv_deltaNL]
  exact (tateOf_deltaNL κ.k κ.instR κ.instC κ.data (classifiedFact f hf κ)).trans
    (localEquiv_relativeTraceSection (omegaData f hf) κ.base κ.source κ.source_le
      (classifiedFact f hf κ)).symm

end AlgebraicGeometry.TateMap

end
