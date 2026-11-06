module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.WeierstrassModel
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicFromSections

/-!
# The Weierstrass model of a section ring is the morphism given by its three sections

Let `X` be a scheme over a field `k`, `L` an ample invertible module and `s₀, s₁, s₂` global
sections of `L` whose nonvanishing opens cover `X` and whose ratios satisfy the Weierstrass cubic
of `C` on every chart. Then the three sections, read in degree one of the section ring
`Γ_*(X, L)`, satisfy the cubic there, and when they present `Γ_*(X, L)` as `k[x, y, z]/(F)` the
morphism `X ⟶ projOf C` of the presentation (`AlgebraicGeometry.GenusOne.weierstrassModelHom`)
is the morphism given by the sections
(`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.cubicHomOfSections`).
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.GradedSections (powSections sectionRing)
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (secOf)
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (twistOneSection)
open Stacks.ProjectiveFromSections (nvCover)
open AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

universe u

namespace AlgebraicGeometry.GenusOne

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

attribute [local instance] Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.sectionAlgebra
  MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- A global section of `L`, as a homogeneous element of degree one of `Γ_*(X, L)`. -/
abbrev degOneElt (t : Γ(L, ⊤)) : sectionRing L :=
  DirectSum.of (powSections L) 1 (secOf L (twistOneSection L t))

/-- **The nonvanishing open of the degree-one element of a section is that of the section.** -/
theorem nvOpen_secOf_twistOneSection (t : Γ(L, ⊤)) :
    Stacks.AmpleFiniteAvoidance.nvOpen L (secOf L (twistOneSection L t)) =
      Stacks.ProjectiveFromSections.nvOpen L t := by
  rw [Stacks.AmpleFiniteAvoidance.nvOpen,
    Stacks.AlgebraicGeometry.ProjChartFromRatios.globalSection_secOf,
    Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.nonvanishingOpen_twistOneSection]

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- The left unitor `L ^⊗ 1 ≅ L` carries the restriction of a section read in `L ^⊗ 1` to the
restriction of the section. -/
theorem unitorPow_hom_app_resTop (W : X.Opens) (t : Γ(L, ⊤)) :
    (Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).hom.app W
        (Stacks.TensorPowerTrivialize.resTop (natTensorPow L 1) (twistOneSection L t) W) =
      Stacks.ProjectiveFromSections.resT W t := by
  rw [← Stacks.AlgebraicGeometry.ProjSectionsUnique.map_app
    (Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).hom (le_top : W ≤ ⊤)
    (twistOneSection L t),
    Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.unitorPow_app_twistOneSection]

variable {L} {s : Fin 3 → Γ(L, ⊤)}

/-- **The section-ring ratio of `sⱼ` by `sᵢ` is the ratio `sⱼ / sᵢ` of the sections**: both are
the unique function multiplying `sᵢ` to `sⱼ` on `X_{sᵢ}`, and the left unitor moves one
identity to the other. -/
theorem ratio_secOf_twistOneSection (i j : Fin 3) :
    Stacks.SectionRingChartMap.ratio L (secOf L (twistOneSection L (s i)))
        (nvOpen_secOf_twistOneSection L (s i)).ge (secOf L (twistOneSection L (s j))) =
      Stacks.ProjectiveFromSections.ratio s i j := by
  refine Stacks.SectionRingChartMap.ratio_unique L _ _ _ _ ?_
  rw [Stacks.AlgebraicGeometry.ProjChartFromRatios.globalSection_secOf,
    Stacks.AlgebraicGeometry.ProjChartFromRatios.globalSection_secOf]
  have hinv : ∀ z : Γ(natTensorPow L 1, nvCover s i),
      (Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).inv.app _
        ((Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).hom.app _ z) = z := by
    intro z
    rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id,
      Scheme.Modules.Hom.id_app]
    rfl
  have hval : (Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).hom.app _
        (Stacks.TensorPowerTrivialize.resTop (natTensorPow L 1) (twistOneSection L (s j))
          (nvCover s i)) =
      (Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).hom.app _
        (Stacks.ProjectiveFromSections.ratio s i j •
          Stacks.TensorPowerTrivialize.resTop (natTensorPow L 1) (twistOneSection L (s i))
            (nvCover s i)) := by
    rw [Scheme.Modules.Hom.app_smul, unitorPow_hom_app_resTop, unitorPow_hom_app_resTop]
    exact (Stacks.ProjectiveFromSections.ratio_smul s i j).symm
  have h := congrArg
    ((Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).inv.app (nvCover s i)) hval
  rwa [hinv, hinv] at h

/-- **The chart family at `sᵢ` on the degree-one element of `sⱼ` is the ratio `sⱼ / sᵢ`.** -/
theorem chartFamily_one_degOneElt (i j : Fin 3) :
    Stacks.SectionRingChartMap.chartFamily L (secOf L (twistOneSection L (s i)))
        (nvOpen_secOf_twistOneSection L (s i)).ge 1 (degOneElt L (s j)) =
      Stacks.ProjectiveFromSections.ratio s i j := by
  have hz : degOneElt L (s j) ∈ Stacks.AmpleFiniteAvoidance.grading L (1 * 1) :=
    Stacks.ExternalGrading.of_mem_summand 1 _
  have hof : DirectSum.of (powSections L) (1 * 1)
      (Stacks.SectionExtension.powSec L (secOf L (twistOneSection L (s i))) 1) =
      DirectSum.of (powSections L) 1 (secOf L (twistOneSection L (s i))) := by
    rw [Stacks.SectionRingChartMap.of_powSec_eq_pow, pow_one]
  rw [Stacks.SectionRingChartMap.chartFamily_apply,
    Stacks.SectionRingChartMap.numMapR_of_mul L _ _ 1 le_rfl _ hz,
    Stacks.SectionRingChartMap.numMapR_def,
    Stacks.SectionRingChartMap.ratioR_congr L (by norm_num : 1 * 1 = 1) _ _ _
      (nvOpen_secOf_twistOneSection L (s i)).ge hof,
    Stacks.SectionRingChartMap.ratioR_of, ratio_secOf_twistOneSection]

/-- **The chart family on a power.** For `e` of degree one, the `n`-th member of the chart family
at `sᵢ` sends `eⁿ` to the `n`-th power of the value of the first member on `e`. -/
theorem chartFamily_pow (i : Fin 3) {e : sectionRing L}
    (he : e ∈ Stacks.AmpleFiniteAvoidance.grading L 1) (n : ℕ) :
    Stacks.SectionRingChartMap.chartFamily L (secOf L (twistOneSection L (s i)))
        (nvOpen_secOf_twistOneSection L (s i)).ge n (e ^ n) =
      Stacks.SectionRingChartMap.chartFamily L (secOf L (twistOneSection L (s i)))
        (nvOpen_secOf_twistOneSection L (s i)).ge 1 e ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact Stacks.SectionRingChartMap.chartFamily_one L _ _
  | succ n ih =>
    rw [pow_succ, pow_succ, Stacks.SectionRingChartMap.chartFamily_mul L _ _ n 1 _ _
      (by simpa using SetLike.pow_mem_graded n he) (by simpa using he), ih]

/-- A product of powers of degree-one elements of sections lies in the matching graded piece. -/
private theorem prod_pow_degOneElt_mem_grading (S : Finset (Fin 3)) (m : Fin 3 → ℕ) :
    ∏ j ∈ S, degOneElt L (s j) ^ m j ∈
      Stacks.AmpleFiniteAvoidance.grading L ((∑ j ∈ S, m j) * 1) := by
  have he : ∀ j, degOneElt L (s j) ∈ Stacks.AmpleFiniteAvoidance.grading L 1 :=
    fun j => Stacks.ExternalGrading.of_mem_summand 1 _
  rw [mul_one]
  exact SetLike.prod_mem_graded _ _ _ fun j _ => by simpa using SetLike.pow_mem_graded (m j) (he j)

/-- **The chart family on a product of powers of degree-one elements.** -/
theorem chartFamily_prod (i : Fin 3) (S : Finset (Fin 3)) (m : Fin 3 → ℕ) :
    Stacks.SectionRingChartMap.chartFamily L (secOf L (twistOneSection L (s i)))
        (nvOpen_secOf_twistOneSection L (s i)).ge (∑ j ∈ S, m j)
          (∏ j ∈ S, degOneElt L (s j) ^ m j) =
      ∏ j ∈ S, Stacks.ProjectiveFromSections.ratio s i j ^ m j := by
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty, Finset.prod_empty]
    exact Stacks.SectionRingChartMap.chartFamily_one L _ _
  | insert j S hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, Finset.prod_insert hj,
      Stacks.SectionRingChartMap.chartFamily_mul L _ _ (m j) _ _ _
        (by simpa using prod_pow_degOneElt_mem_grading (s := s) (L := L) {j} m)
        (prod_pow_degOneElt_mem_grading S m), ih,
      chartFamily_pow i (Stacks.ExternalGrading.of_mem_summand 1 _), chartFamily_one_degOneElt]

/-- Restricting a function on `X` to `V` and reading it on the open subscheme `V` is the map of
global sections of the inclusion `V ⟶ X`. -/
theorem map_topIso_inv_eq_ι_appTop (V : X.Opens) :
    X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ V.topIso.inv = V.ι.appTop := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
  exact (X.presheaf.map_comp _ _).symm

section General

variable {σ τ : Type u} {A B : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
  [GradedRing 𝒜] [GradedRing ℬ]

/-- **A chart of `Proj ℬ` followed by `Proj` of a graded map is a chart of `Proj 𝒜`**, with the
ring maps out of the two degree-zero localizations compared on fractions: if `f a = b` and `ρ`,
`ρ'` agree on `f p / bⁿ` and `p / aⁿ`, then `Spec ρ` followed by the chart at `b` and `Proj f` is
`Spec ρ'` followed by the chart at `a`. -/
theorem SpecMap_awayι_comp_map (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜))
    {d : ℕ} (hd : 0 < d) {a : A} {b : B} (ha : a ∈ 𝒜 d) (hb : b ∈ ℬ d) (hab : f a = b)
    {R : Type u} [CommRing R] (ρ : HomogeneousLocalization.Away ℬ b →+* R)
    (ρ' : HomogeneousLocalization.Away 𝒜 a →+* R)
    (h : ∀ (n : ℕ) (p : A) (hp : p ∈ 𝒜 (n • d)),
      ρ (HomogeneousLocalization.Away.mk ℬ hb n (f p) (f.map_mem hp)) =
        ρ' (HomogeneousLocalization.Away.mk 𝒜 ha n p hp)) :
    Spec.map (CommRingCat.ofHom ρ) ≫ Proj.awayι ℬ b hb hd ≫ Proj.map f hf =
      Spec.map (CommRingCat.ofHom ρ') ≫ Proj.awayι 𝒜 a ha hd := by
  subst hab
  have hρ : ρ.comp (HomogeneousLocalization.Away.map f a) = ρ' :=
    Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext 𝒜 ha fun n p hp => by
      rw [RingHom.comp_apply, HomogeneousLocalization.Away.map_mk]
      exact h n p hp
  rw [Proj.awayι_comp_map f hf hd a ha, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, hρ]

/-- **The morphism to `Proj` of a ring map sending a homogeneous element to `1` factors through
its chart**, over an arbitrary scheme: through `Y ⟶ Spec Γ(Y, ⊤)` and `Spec` of the ring map
`p / tⁿ ↦ κ p`. -/
theorem fromOfGlobalSections_eq_toSpecΓ_comp {Y : Scheme.{u}} (κ : A →+* Γ(Y, ⊤)) {t : A}
    {d : ℕ} (hd : t ∈ 𝒜 d) (h0d : 0 < d) (h : κ t = 1)
    (hκ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map κ = ⊤) :
    Proj.fromOfGlobalSections 𝒜 κ hκ = Y.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom ((Localization.awayLift κ t (h ▸ isUnit_one)).comp
        (algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t)))) ≫
          Proj.awayι 𝒜 t hd h0d := by
  have hκ' : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
      ((Scheme.ΓSpecIso (CommRingCat.of Γ(Y, ⊤))).inv.hom.comp κ) = ⊤ := by
    rw [← Ideal.map_map, hκ, Ideal.map_top]
  rw [← fromOfGlobalSections_eq_SpecMap_awayι 𝒜 κ hd h0d h hκ',
    comp_fromOfGlobalSections 𝒜 Y.toSpecΓ _ hκ' (by rw [← Ideal.map_map, hκ', Ideal.map_top])]
  congr 1
  rw [Scheme.toSpecΓ_appTop, ← RingHom.comp_assoc, ← CommRingCat.hom_comp]
  show κ = (CommRingCat.Hom.hom ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv ≫
    (Scheme.ΓSpecIso Γ(Y, ⊤)).hom)).comp κ
  rw [Iso.inv_hom_id, CommRingCat.hom_id, RingHom.id_comp]

end General

variable (k : Type u) [Field k] [X.Over (Spec (.of k))] {C : WeierstrassCurve k}

/-- **The chart family at `sᵢ` on a constant**, read on the chart, is the constant. -/
theorem chartFamily_zero_algebraMap (i : Fin 3) (c : k) :
    (nvCover s i).topIso.inv (Stacks.SectionRingChartMap.chartFamily L
        (secOf L (twistOneSection L (s i))) (nvOpen_secOf_twistOneSection L (s i)).ge 0
          (algebraMap k (sectionRing L) c)) =
      openBase (X ↘ Spec (.of k)) (nvCover s i) c := by
  have hx : algebraMap k (sectionRing L) c ∈ Stacks.AmpleFiniteAvoidance.grading L (0 • 1) :=
    algebraMap_mem_grading_zero L k c
  rw [← Stacks.SectionRingChartMap.chartRingMap_mk L _ _ 0 _ hx]
  have hmk : HomogeneousLocalization.Away.mk (Stacks.AmpleFiniteAvoidance.grading L)
        (Stacks.ExternalGrading.of_mem_summand 1 (secOf L (twistOneSection L (s i)))) 0 _ hx =
      HomogeneousLocalization.fromZeroRingHom (Stacks.AmpleFiniteAvoidance.grading L)
        (Submonoid.powers (degOneElt L (s i)))
          ⟨_, algebraMap_mem_grading_zero L k c⟩ := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk]
    show Localization.mk _ 1 = _
    congr 1
  rw [hmk, ← Stacks.SectionRingChartOpen.map_chartRingMap L _ le_rfl _
      (nvOpen_secOf_twistOneSection L (s i)).ge,
    Stacks.SectionRingProjMorphism.ToSpecZero.chartRingMap_fromZero]
  have hdeg : (⟨_, algebraMap_mem_grading_zero L k c⟩ : Stacks.AmpleFiniteAvoidance.grading L 0) =
      ⟨Stacks.AlgebraicGeometry.GradedSectionRingMap.degreeZeroHom L
        (Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.baseRingHom k X c), ⟨_, rfl⟩⟩ :=
    Subtype.ext rfl
  rw [hdeg, degZeroRingHom_degreeZeroHom, openBase, Scheme.Hom.comp_appTop,
    ← map_topIso_inv_eq_ι_appTop, ← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
    ← Category.assoc, ← Functor.map_comp]
  rfl

/-- **The chart family at `sᵢ` on the image of a homogeneous polynomial is the polynomial
evaluated at the ratios**: for `P` homogeneous of degree `n`, the `n`-th member of the chart
family sends `P(s₀, s₁, s₂)` to `P(s₀/sᵢ, s₁/sᵢ, s₂/sᵢ)`. -/
theorem topIso_inv_chartFamily_aeval (i : Fin 3) {n : ℕ} {P : MvPolynomial (Fin 3) k}
    (hP : P.IsHomogeneous n) :
    (nvCover s i).topIso.inv (Stacks.SectionRingChartMap.chartFamily L
        (secOf L (twistOneSection L (s i))) (nvOpen_secOf_twistOneSection L (s i)).ge n
          (MvPolynomial.aeval (fun j => degOneElt L (s j)) P)) =
      chartPolyHom (X ↘ Spec (.of k)) s i P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : m.degree = n := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hm) (hP.coeff_eq_zero hne)
  have hprod : (m.prod fun j e => degOneElt L (s j) ^ e) ∈
      Stacks.AmpleFiniteAvoidance.grading L (m.degree * 1) :=
    prod_pow_degOneElt_mem_grading (s := s) (L := L) m.support m
  have hmul := Stacks.SectionRingChartMap.chartFamily_mul L (secOf L (twistOneSection L (s i)))
    (nvOpen_secOf_twistOneSection L (s i)).ge 0 _ _ _ (algebraMap_mem_grading_zero L k
      (P.coeff m)) hprod
  rw [zero_add] at hmul
  rw [MvPolynomial.aeval_monomial, ← hdeg, hmul, map_mul, chartFamily_zero_algebraMap,
    show (m.prod fun j e => degOneElt L (s j) ^ e) = ∏ j ∈ m.support, degOneElt L (s j) ^ m j
      from rfl, show Finsupp.degree m = ∑ j ∈ m.support, m j from rfl, chartFamily_prod,
    chartPolyHom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, Finsupp.prod, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_pow]
  rfl

/-- The chart family of the image of a homogeneous polynomial, read through `topIso.hom`. -/
private theorem chartFamily_aeval_eq_topIso_hom (i : Fin 3) {n : ℕ} {P : MvPolynomial (Fin 3) k}
    (hP : P.IsHomogeneous n) :
    Stacks.SectionRingChartMap.chartFamily L (secOf L (twistOneSection L (s i)))
        (nvOpen_secOf_twistOneSection L (s i)).ge n
          (MvPolynomial.aeval (fun j => degOneElt L (s j)) P) =
      (nvCover s i).topIso.hom (chartPolyHom (X ↘ Spec (.of k)) s i P) := by
  rw [← topIso_inv_chartFamily_aeval k i hP, Iso.inv_hom_id_apply]

/-- **A degree-three element of the section ring vanishing on every chart is zero.** If its
member of the chart family vanishes on the nonvanishing open of each `sᵢ`, and these opens cover
`X`, the section of `L ^⊗ 3` it names restricts to zero on each of them. -/
theorem eq_zero_of_chartFamily_eq_zero (hcov : IsOpenCover (nvCover s)) {x : sectionRing L}
    (hx : x ∈ Stacks.AmpleFiniteAvoidance.grading L 3)
    (h : ∀ i, Stacks.SectionRingChartMap.chartFamily L (secOf L (twistOneSection L (s i)))
      (nvOpen_secOf_twistOneSection L (s i)).ge 3 x = 0) : x = 0 := by
  obtain ⟨t, rfl⟩ := hx
  have hres : ∀ i, Stacks.TensorPowerTrivialize.resTop (natTensorPow L 3)
      (Stacks.SectionProduct.globalSection X _ t) (nvCover s i) = 0 := by
    intro i
    have hz : DirectSum.of (powSections L) 3 t ∈ Stacks.AmpleFiniteAvoidance.grading L (1 * 3) :=
      Stacks.ExternalGrading.of_mem_summand 3 t
    have h0 := h i
    rw [Stacks.SectionRingChartMap.chartFamily_apply,
      Stacks.SectionRingChartMap.numMapR_of_mul L _ _ 3 (by norm_num) _ hz] at h0
    have h1 := Stacks.SectionRingChartMap.numMapR_of L (secOf L (twistOneSection L (s i)))
      (nvOpen_secOf_twistOneSection L (s i)).ge 3 (by norm_num) t
    rw [h1] at h0
    have h2 := Stacks.SectionRingChartMap.numMap_smul_resTop L (secOf L (twistOneSection L (s i)))
      (nvOpen_secOf_twistOneSection L (s i)).ge 3 (by norm_num)
      (Stacks.SectionProduct.globalSection X _ t)
    rw [h0, zero_smul] at h2
    exact h2.symm
  have hglob : Stacks.SectionProduct.globalSection X (natTensorPow L 3) t = 0 := by
    let F : TopCat.Sheaf AddCommGrpCat X :=
      ⟨(natTensorPow L 3).presheaf, (natTensorPow L 3).isSheaf⟩
    refine F.eq_of_locally_eq' (nvCover s) ⊤ (fun i => homOfLE le_top) hcov.ge _ 0 fun i => ?_
    rw [map_zero]
    exact hres i
  rw [← Stacks.AlgebraicGeometry.ProjChartFromRatios.secOf_globalSection L t, hglob]
  exact (congrArg _ ((Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
    (natTensorPow L 3)).symm.map_zero)).trans (map_zero _)

/-- **The sections satisfy the cubic in the section ring**: if the ratios of `s₀, s₁, s₂`
satisfy the Weierstrass cubic of `C` on every chart and the charts cover `X`, then
`F(s₀, s₁, s₂) = 0` in degree three of `Γ_*(X, L)`. -/
theorem aeval_cubicOf_eq_zero (hrel : SatisfiesCubic C (X ↘ Spec (.of k)) s)
    (hcov : IsOpenCover (nvCover s)) :
    MvPolynomial.aeval (fun j => degOneElt L (s j)) (cubicOf C) = 0 := by
  have hP : (cubicOf C).IsHomogeneous 3 :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).mp (cubicOf_mem C)
  refine eq_zero_of_chartFamily_eq_zero hcov
    (aeval_mem_of_isHomogeneous (Stacks.AmpleFiniteAvoidance.grading L)
      (algebraMap_mem_grading_zero L k) (fun j => Stacks.ExternalGrading.of_mem_summand 1 _) hP)
    fun i => ?_
  rw [chartFamily_aeval_eq_topIso_hom k i hP, hrel i, map_zero]


/-- **The Weierstrass model is the morphism given by the sections.** -/
theorem weierstrassModelHom_eq_cubicHomOfSections (hL : Stacks.Ample.IsAmple X L)
    (hker : RingHom.ker (MvPolynomial.aeval (fun j => degOneElt L (s j)) :
      MvPolynomial (Fin 3) k →ₐ[k] sectionRing L) = Ideal.span {C.toProjective.polynomial})
    (hv : ∀ i, (MvPolynomial.aeval (fun j => degOneElt L (s j)) :
      MvPolynomial (Fin 3) k →ₐ[k] sectionRing L) (MvPolynomial.X i) ∈
        Stacks.AmpleFiniteAvoidance.grading L 1)
    (hsurj : Function.Surjective (MvPolynomial.aeval (fun j => degOneElt L (s j)) :
      MvPolynomial (Fin 3) k →ₐ[k] sectionRing L))
    (hrel : SatisfiesCubic C (X ↘ Spec (.of k)) s) (hcov : IsOpenCover (nvCover s)) :
    weierstrassModelHom L k hL C _ hker hv hsurj = cubicHomOfSections hrel hcov := by
  refine (X.openCoverOfIsOpenCover (nvCover s) hcov).hom_ext _ _ fun (i : Fin 3) => ?_
  show (nvCover s i).ι ≫ weierstrassModelHom L k hL C _ hker hv hsurj =
    (nvCover s i).ι ≫ cubicHomOfSections hrel hcov
  rw [ι_cubicHomOfSections]
  have hV := (nvOpen_secOf_twistOneSection L (s i)).ge
  have hψ : HomogeneousIdeal.irrelevant (Stacks.AmpleFiniteAvoidance.grading L) ≤
      HomogeneousIdeal.map (weierstrassGradedHom (Stacks.AmpleFiniteAvoidance.grading L) C _ hker
        (algebraMap_mem_grading_zero L k) hv) (HomogeneousIdeal.irrelevant (gradingOf C)) :=
    Proj.irrelevant_le_map_of_surjective _ (bijective_weierstrassRingHom C _ hker hsurj).2
  have h1 : chartRingHom hrel i (coordOf C i) = 1 := by
    show chartRingHom hrel i (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 1
    rw [chartRingHom_mk, chartPolyHom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X,
      Stacks.ProjectiveFromSections.chartRatio_self]
  have hab : weierstrassGradedHom (Stacks.AmpleFiniteAvoidance.grading L) C _ hker
      (algebraMap_mem_grading_zero L k) hv (coordVar C i) =
        DirectSum.of (powSections L) 1 (secOf L (twistOneSection L (s i))) :=
    MvPolynomial.aeval_X _ i
  have hρ : ∀ (n : ℕ) (p : coordRingOf C) (hp : p ∈ gradingOf C (n • 1)),
      Stacks.SectionRingChartMap.chartRingMap L (secOf L (twistOneSection L (s i))) hV
        (HomogeneousLocalization.Away.mk (Stacks.AmpleFiniteAvoidance.grading L)
          (Stacks.ExternalGrading.of_mem_summand 1 _) n
          (weierstrassGradedHom (Stacks.AmpleFiniteAvoidance.grading L) C _ hker
            (algebraMap_mem_grading_zero L k) hv p)
          ((weierstrassGradedHom (Stacks.AmpleFiniteAvoidance.grading L) C _ hker
            (algebraMap_mem_grading_zero L k) hv).map_mem hp)) =
      ((nvCover s i).topIso.hom.hom.comp (awayLiftOf C (chartRingHom hrel i) i h1))
        (HomogeneousLocalization.Away.mk (gradingOf C) (coordVar_mem C i) n p hp) := by
    intro n p hp
    obtain ⟨P, hP, rfl⟩ := (Stacks.HomogeneousIdeal.mem_quotientGrading_iff _ p).mp hp
    rw [Stacks.SectionRingChartMap.chartRingMap_mk, RingHom.comp_apply, awayLiftOf_mk,
      chartRingHom_mk]
    have hP' : P.IsHomogeneous n := by
      simpa using (MvPolynomial.mem_homogeneousSubmodule _ _).mp hP
    exact chartFamily_aeval_eq_topIso_hom k i hP'
  have hT : (nvCover s i).toSpecΓ =
      (nvCover s i).toScheme.toSpecΓ ≫ Spec.map (nvCover s i).topIso.inv :=
    Scheme.Hom.ext' rfl
  have hring : CommRingCat.ofHom ((nvCover s i).topIso.hom.hom.comp
      (awayLiftOf C (chartRingHom hrel i) i h1)) ≫ (nvCover s i).topIso.inv =
      CommRingCat.ofHom ((Localization.awayLift (chartRingHom hrel i) (coordVar C i)
        (h1 ▸ isUnit_one)).comp (algebraMap (HomogeneousLocalization.Away (gradingOf C)
          (coordVar C i)) (Localization.Away (coordVar C i)))) := by
    rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
    rfl
  show (nvCover s i).ι ≫ Stacks.SectionRingProjMorphism.projHomOfIsAmple L hL ≫
      Proj.map (weierstrassGradedHom (Stacks.AmpleFiniteAvoidance.grading L) C _ hker
        (algebraMap_mem_grading_zero L k) hv) hψ =
    Proj.fromOfGlobalSections (gradingOf C) (chartRingHom hrel i) (chartRingHom_irrelevant hrel i)
  rw [← Scheme.homOfLE_ι X hV, Category.assoc,
    ← Category.assoc (Stacks.AmpleFiniteAvoidance.nvOpen L (secOf L (twistOneSection L (s i)))).ι,
    Stacks.SectionRingProjImmersion.ι_comp_projHomOfIsAmple L hL _ one_pos, ← Category.assoc,
    ← Stacks.SectionRingChartOpen.chartHomOn_self,
    Stacks.SectionRingChartOpen.homOfLE_chartHomOn L _ one_pos le_rfl hV hV,
    Stacks.SectionRingChartOpen.chartHomOn_val, Category.assoc, Category.assoc,
    SpecMap_awayι_comp_map _ hψ one_pos (coordVar_mem C i)
      (Stacks.ExternalGrading.of_mem_summand 1 _) hab _ _ hρ,
    fromOfGlobalSections_eq_toSpecΓ_comp (chartRingHom hrel i) (coordVar_mem C i) one_pos h1, hT,
    Category.assoc, ← Spec.map_comp_assoc, hring]

end AlgebraicGeometry.GenusOne

end
