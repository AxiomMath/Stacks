module

public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesZeroSectionsComp
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicFromSectionsField
public import StacksFrontier.AlgebraicGeometry.Morphisms.ClosedFibreNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionPullbackZero

/-!
# The sections `s x, y, s³` generate `O(0)^{⊗ 3}` near a fibre

Let `(E, f, 0)` be a pointed family over `Spec A`, proper and smooth of relative dimension one,
whose fibre at a prime `p` is a curve of genus one, and let `x`, `y` be sections of `O(0)^{⊗ 2}`,
`O(0)^{⊗ 3}` whose restrictions to the fibre are not multiples of the canonical section `s`.
Then there is `r ∉ p` such that after any base change `A ⟶ B` inverting `r`, and any rescaling
of `x` and `y` by a unit of `B`, the three sections `s x, y, s³` of `O(0)^{⊗ 3}` have
nonvanishing opens covering the total space.

On the fibre `y` does not vanish at the zero point, its order there being zero, and `s³`
vanishes nowhere else; so the three nonvanishing opens on `E` contain the fibre over `p`, hence a
whole neighbourhood `f⁻¹ D(r)` of it, because `f` is closed.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.exists_isOpenCover_nvCover`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.TensorPowers (natTensorPow)
open Stacks.Divisors
open Stacks.SectionProduct (globalSection)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (mulSections secOf globalSection_secOf
  secOf_globalSection mulSections_globalSection)
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (twistOneSection)
open Stacks.ProjectiveFromSections (nvCover div div_smul resT eq_of_smul_eq_smul)
open Stacks.StalkOrder (stalkOrd)
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u

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

namespace AlgebraicGeometry.GenusOne

section Nonvanishing

variable {X : Scheme.{u}} {M : X.Modules} [Stacks.Ample.IsInvertibleModule X M]

/-- **A section of order zero at `x` does not vanish at `x`.** -/
theorem mem_nonvanishingOpen_of_stalkOrd_eq_zero {x : X} [IsDomain (X.presheaf.stalk x)]
    [IsDiscreteValuationRing (X.presheaf.stalk x)] (t : Γ(M, ⊤))
    (h : stalkOrd M x ((M.presheaf.Γgerm x).hom t) = 0) : x ∈ nonvanishingOpen X M t := by
  obtain ⟨g, hg, hfree⟩ := Stacks.StalkOrder.exists_generator M x
  obtain ⟨r, hr⟩ := hg ((M.presheaf.Γgerm x).hom t)
  rw [hr, Stacks.StalkOrder.stalkOrd_smul_generator hg hfree] at h
  have hu : IsUnit r := (IsDiscreteValuationRing.addVal_eq_zero_iff).mp h
  refine (Stacks.SectionProduct.mem_nonvanishingLocus_iff_generates M t x).mpr fun w => ?_
  obtain ⟨c, rfl⟩ := hg w
  exact ⟨c * ↑hu.unit⁻¹, by rw [hr, smul_smul, mul_assoc, IsUnit.val_inv_mul, mul_one]⟩

/-- **Multiplying by a unit does not change the nonvanishing open.** -/
theorem nonvanishingOpen_smul_of_isUnit {c : Γ(X, ⊤)} (hc : IsUnit c) (t : Γ(M, ⊤)) :
    nonvanishingOpen X M (c • t) = nonvanishingOpen X M t := by
  ext x
  show x ∈ Stacks.Ample.nonvanishingLocus M (c • t) ↔ x ∈ Stacks.Ample.nonvanishingLocus M t
  rw [Stacks.SectionProduct.mem_nonvanishingLocus_iff_generates,
    Stacks.SectionProduct.mem_nonvanishingLocus_iff_generates, Stacks.ModuleStalk.Γgerm_smul]
  have hu : IsUnit ((X.presheaf.Γgerm x).hom c) := hc.map _
  refine ⟨fun h w => ?_, fun h w => ?_⟩
  · obtain ⟨r, hr⟩ := h w
    exact ⟨r * (X.presheaf.Γgerm x).hom c, by rw [hr, smul_smul]⟩
  · obtain ⟨r, hr⟩ := h w
    exact ⟨r * ↑hu.unit⁻¹, by rw [hr, smul_smul, mul_assoc, IsUnit.val_inv_mul, mul_one]⟩

/-- **The nonvanishing open of a product is the intersection of the nonvanishing opens.** -/
theorem nonvanishingOpen_mulSections {n m : ℕ} (a : Γ(natTensorPow M n, ⊤))
    (b : Γ(natTensorPow M m, ⊤)) :
    nonvanishingOpen X (natTensorPow M (n + m)) (mulSections M a b) =
      nonvanishingOpen X (natTensorPow M n) a ⊓ nonvanishingOpen X (natTensorPow M m) b := by
  have h := Stacks.SectionRingChartMap.nvOpen_mul M (secOf M a) (secOf M b)
  unfold Stacks.AmpleFiniteAvoidance.nvOpen at h
  rwa [← mulSections_globalSection, globalSection_secOf, globalSection_secOf] at h

/-- **The nonvanishing open of a transported section is the preimage of the nonvanishing
open.** -/
theorem nonvanishingOpen_transportSection {Y : Scheme.{u}} (j : Y ⟶ X) {M' : Y.Modules}
    [Stacks.Ample.IsInvertibleModule Y M'] (e : (Scheme.Modules.pullback j).obj M ≅ M') (n : ℕ)
    (t : Γ(natTensorPow M n, ⊤)) :
    nonvanishingOpen Y (natTensorPow M' n)
        (Stacks.AlgebraicGeometry.ProjChartRatioPullback.transportSection j e n t) =
      j ⁻¹ᵁ nonvanishingOpen X (natTensorPow M n) t := by
  rw [← Stacks.AlgebraicGeometry.ProjChartRatioPullback.nonvanishingOpen_pullSection]
  exact Opens.ext (Stacks.Ample.nonvanishingLocus_congr
    (Stacks.AmplePullbackPart1.natTensorPowCongr e n) _)

/-- A morphism into an open subscheme reads a function on the open through `appLE`. -/
theorem appTop_topIso_inv {Y : Scheme.{u}} {U : X.Opens} (σ₁ : Y ⟶ U.toScheme) (f : Γ(X, U)) :
    σ₁.appTop (U.topIso.inv f) = (σ₁ ≫ U.ι).appLE U ⊤ (by simp) f := by
  have happ : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    simp only [Scheme.Hom.appLE, Scheme.Opens.ι_app_self, Scheme.Opens.topIso_inv]
    exact (X.presheaf.map_comp _ _).symm.trans
      (congrArg X.presheaf.map (Subsingleton.elim _ _))
  have h2 : U.ι.appLE U ⊤ U.ι_preimage_self.ge ≫ σ₁.appTop = (σ₁ ≫ U.ι).appLE U ⊤ (by simp) := by
    rw [← AlgebraicGeometry.appLE_top_top_eq_appTop σ₁ (by simp)]
    exact Scheme.Hom.appLE_comp_appLE σ₁ U.ι _ _ _ _ _
  rw [← happ]
  exact ConcreteCategory.congr_hom h2 f

/-- **A ratio by a section nonvanishing along a morphism, of a section killed by that morphism,
is killed by it.** If `z : Y ⟶ X` lands in `X_u` through `σ₁` and the pullback of `w` along `z`
is zero, then `σ₁` kills the ratio `w / u` on `X_u`. -/
theorem appTop_div_eq_zero {Y : Scheme.{u}} (u w : Γ(M, ⊤))
    (σ₁ : Y ⟶ (nonvanishingOpen X M u).toScheme)
    (hw : pullbackSectionHom (σ₁ ≫ (nonvanishingOpen X M u).ι) M ⊤ ⊤ (by simp) w = 0) :
    σ₁.appTop ((nonvanishingOpen X M u).topIso.inv
      (div u le_rfl
        (resT _ w))) = 0 := by
  set f := div u le_rfl (resT (nonvanishingOpen X M u) w)
  have hf : f • resT (nonvanishingOpen X M u) u = resT (nonvanishingOpen X M u) w :=
    div_smul u le_rfl _
  have hU : (⊤ : Y.Opens) ≤ (σ₁ ≫ (nonvanishingOpen X M u).ι) ⁻¹ᵁ (nonvanishingOpen X M u) := by
    intro y _
    show (σ₁ ≫ (nonvanishingOpen X M u).ι) y ∈ (nonvanishingOpen X M u)
    rw [Scheme.Hom.comp_apply]
    exact (σ₁ y).2
  have h1 := congrArg
    (pullbackSectionHom (σ₁ ≫ (nonvanishingOpen X M u).ι) M (nonvanishingOpen X M u) ⊤ hU) hf
  have e1 := pullbackSectionHom_map (σ₁ ≫ (nonvanishingOpen X M u).ι) M ⊤
    (nonvanishingOpen X M u) le_top ⊤ hU (by simp) u
  have e2 := pullbackSectionHom_map (σ₁ ≫ (nonvanishingOpen X M u).ι) M ⊤
    (nonvanishingOpen X M u) le_top ⊤ hU (by simp) w
  rw [pullbackSectionHom_smul] at h1
  change _ • pullbackSectionHom _ M _ ⊤ hU (M.val.map _ u) =
    pullbackSectionHom _ M _ ⊤ hU (M.val.map _ w) at h1
  rw [e1, e2, hw] at h1
  set Pu := pullbackSectionHom (σ₁ ≫ (nonvanishingOpen X M u).ι) M ⊤ ⊤ (by simp) u with hPu
  have hnv : (⊤ : Y.Opens) ≤ nonvanishingOpen Y
      ((Scheme.Modules.pullback (σ₁ ≫ (nonvanishingOpen X M u).ι)).obj M) Pu := by
    intro y _
    show y ∈ Stacks.Ample.nonvanishingLocus _ Pu
    rw [hPu, Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackSectionHom_top]
    refine (Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff
      (σ₁ ≫ (nonvanishingOpen X M u).ι) M u y).mpr (hU (show y ∈ (⊤ : Y.Opens) from trivial))
  have hres : resT (⊤ : Y.Opens) Pu = Pu := by
    show ((Scheme.Modules.pullback (σ₁ ≫ (nonvanishingOpen X M u).ι)).obj M).presheaf.map
      (homOfLE le_top).op Pu = Pu
    rw [show (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op = 𝟙 _ from rfl,
      CategoryTheory.Functor.map_id]
    rfl
  have hc := eq_of_smul_eq_smul Pu hnv
    (a := (σ₁ ≫ (nonvanishingOpen X M u).ι).appLE (nonvanishingOpen X M u) ⊤ hU f) (b := 0)
    (by rw [hres, h1, zero_smul])
  rwa [appTop_topIso_inv]

/-- **The ratio `s_k / s_i` on the chart of `s_i` is killed by a morphism killing `s_k`.** -/
theorem appTop_chartRatio_eq_zero {Y : Scheme.{u}} {n : ℕ} (s : Fin (n + 1) → Γ(M, ⊤))
    (i k : Fin (n + 1)) (σ₁ : Y ⟶ (nvCover s i).toScheme)
    (hw : pullbackSectionHom (σ₁ ≫ (nvCover s i).ι) M ⊤ ⊤ (by simp) (s k) = 0) :
    σ₁.appTop (Stacks.ProjectiveFromSections.chartRatio s i k) = 0 :=
  appTop_div_eq_zero (s i) (s k) σ₁ hw

end Nonvanishing

section Fibre

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  (h0 : Module.finrank k (structureSheafCohomology (X ↘ Spec (.of k)) 0) = 1)
  (hg : genus (X ↘ Spec (.of k)) = 1) (p : Spec (.of k) ⟶ X) (hp : p ≫ (X ↘ Spec (.of k)) = 𝟙 _)
  [IsEffectiveCartierDivisor (Scheme.IdealSheafData.vanishingIdeal
    (⟨{point p}, isClosed_point (X ↘ Spec (.of k)) p hp⟩ : Closeds X) ^ 1)]

include h0 hg in
/-- **A section of `𝒪_X(3p)` not divisible by `s` does not vanish at `p`.** -/
theorem point_mem_nonvanishingOpen {y : Γ(natTensorPow (pointDivisorSheaf p hp 1) 3, ⊤)}
    (hy : ∀ t : Γ(natTensorPow (pointDivisorSheaf p hp 1) 2, ⊤),
      mulSections _ (pointSectionOne p hp) t ≠ y) :
    point p ∈ nonvanishingOpen X (natTensorPow (pointDivisorSheaf p hp 1) 3) y := by
  have := isIntegral (X ↘ Spec (.of k)) h0
  have := isDiscreteValuationRing_stalk (X ↘ Spec (.of k)) h0 p hp
  have h := ord_ringElt_eq_zero h0 hg p hp (n := 2) y hy
  change ringOrd _ (point p) _ = _ at h
  rw [ringOrd_of] at h
  unfold Stacks.StalkOrder.sectionOrd Stacks.StalkOrder.sectionGerm at h
  rw [globalSection_secOf] at h
  exact mem_nonvanishingOpen_of_stalkOrd_eq_zero y h

end Fibre

end AlgebraicGeometry.GenusOne

namespace AlgebraicGeometry.ModuliEllipticCurves.PointedFamily

section Field

variable {k : Type u} [Field k] (F : PointedFamily (Spec (.of k))) [IsProper F.map]
  [SmoothOfRelativeDimension 1 F.map]
  (h0 : Module.finrank k (structureSheafCohomology F.map 0) = 1) (h1 : genus F.map = 1)

include h0 h1 in
/-- The fibre statement for an invertible module equal to `𝒪(0(Spec k))`. -/
theorem zero_mem_nonvanishingOpen_of_eq
    [IsEffectiveCartierDivisor (Scheme.IdealSheafData.vanishingIdeal
      (⟨{GenusOne.point F.zero}, GenusOne.isClosed_point F.map F.zero F.zero_map⟩ :
        Closeds F.total) ^ 1)]
    (L : F.total.Modules) [Stacks.Ample.IsInvertibleModule F.total L]
    (hL : L = modulesInvertibleSheaf (Scheme.IdealSheafData.vanishingIdeal
      (⟨{GenusOne.point F.zero}, GenusOne.isClosed_point F.map F.zero F.zero_map⟩ :
        Closeds F.total) ^ 1))
    (σ : Γ(natTensorPow L 1, ⊤)) (hσ : HEq σ (globalSection F.total _
      (GenusOne.pointSection (GenusOne.isClosed_point F.map F.zero F.zero_map) 1)))
    {y : Γ(natTensorPow L 3, ⊤)} (hy : y ∉ Set.range (mulSections L (m := 2) σ)) :
    F.zero (IsLocalRing.closedPoint k) ∈ nonvanishingOpen F.total (natTensorPow L 3) y ∧
      ∀ q : F.total, q ∈ nonvanishingOpen F.total (natTensorPow L 3) y ∨
        q ∈ nonvanishingOpen F.total (natTensorPow L 3) (cube L σ) := by
  subst hL
  obtain rfl := eq_of_heq hσ
  let : F.total.Over (Spec (.of k)) := ⟨F.map⟩
  have : IsProper (F.total ↘ Spec (.of k)) := ‹IsProper F.map›
  have : SmoothOfRelativeDimension 1 (F.total ↘ Spec (.of k)) := ‹_›
  have h := GenusOne.point_mem_nonvanishingOpen h0 h1 F.zero F.zero_map
    (fun t ht => hy ⟨t, ht⟩)
  refine ⟨h, fun q => ?_⟩
  by_cases hq : q = GenusOne.point F.zero
  · rw [hq]
    exact Or.inl h
  · exact Or.inr (GenusOne.mem_nonvanishingOpen_cube F.zero F.zero_map q hq)

include h0 h1 in
/-- **On an elliptic curve over a field, a section `y` of `O(0)^{⊗ 3}` not divisible by `s`
does not vanish at the zero point, and `y` and `s³` have no common zero.** -/
theorem zero_mem_nonvanishingOpen {y : Γ(natTensorPow F.zeroSheaf 3, ⊤)}
    (hy : y ∉ Set.range (mulSections F.zeroSheaf (m := 2) F.zeroSection)) :
    F.zero (IsLocalRing.closedPoint k) ∈ nonvanishingOpen F.total (natTensorPow F.zeroSheaf 3) y ∧
      ∀ q : F.total, q ∈ nonvanishingOpen F.total (natTensorPow F.zeroSheaf 3) y ∨
        q ∈ nonvanishingOpen F.total (natTensorPow F.zeroSheaf 3)
          (cube F.zeroSheaf F.zeroSection) := by
  let : F.total.Over (Spec (.of k)) := ⟨F.map⟩
  have : IsProper (F.total ↘ Spec (.of k)) := ‹IsProper F.map›
  have : SmoothOfRelativeDimension 1 (F.total ↘ Spec (.of k)) := ‹_›
  have := GenusOne.isEffectiveCartierDivisor_pow F.map h0 F.zero F.zero_map 1
  exact F.zero_mem_nonvanishingOpen_of_eq h0 h1 F.zeroSheaf
    (congrArg invertibleSheaf' F.zeroDivisor_eq_pointDivisor) F.zeroSection
    (by
      have key : ∀ (D D' : F.total.IdealSheafData), D = D' →
          HEq (twistOneSection (invertibleSheaf' D) ((canonicalSection' D).val (op ⊤)))
            (twistOneSection (invertibleSheaf' D') ((canonicalSection' D').val (op ⊤))) := by
        rintro D _ rfl
        rfl
      exact (key _ _ F.zeroDivisor_eq_pointDivisor).trans
        (heq_of_eq (GenusOne.globalSection_pointSection _ 1).symm)) hy

end Field

section Restriction

variable {S T : Scheme.{u}} (E : PointedFamily S) [IsSeparated E.map]
  [SmoothOfRelativeDimension 1 E.map]

/-- `O(0)` of a pulled-back family is invertible, with the total space spelled as the pullback
(instance search does not see through `PointedFamily.total` of `PointedFamily.pullback`). -/
instance isInvertibleModule_zeroSheaf_pullback (g : T ⟶ S) :
    Stacks.Ample.IsInvertibleModule (Limits.pullback E.map g) (E.pullback g).zeroSheaf :=
  isInvertibleModule_zeroSheaf (E.pullback g)

/-- **The nonvanishing open of a restricted section is the preimage of the nonvanishing open.** -/
theorem nonvanishingOpen_restrictSection (g : T ⟶ S) (n : ℕ)
    (t : Γ(natTensorPow E.zeroSheaf n, ⊤)) :
    nonvanishingOpen (E.pullback g).total (natTensorPow (E.pullback g).zeroSheaf n)
        (E.restrictSection g n t) =
      Limits.pullback.fst E.map g ⁻¹ᵁ nonvanishingOpen E.total (natTensorPow E.zeroSheaf n) t :=
  GenusOne.nonvanishingOpen_transportSection _ _ n t

/-- **Restriction carries `s³` to `s³`.** -/
theorem restrictSection_cube_zeroSection (g : T ⟶ S) :
    E.restrictSection g 3 (cube E.zeroSheaf E.zeroSection) =
      cube (E.pullback g).zeroSheaf (E.pullback g).zeroSection := by
  rw [cube, sq, cube, sq]
  show E.restrictSection g ((1 + 1) + 1) _ = _
  rw [restrictSection_mulSections, restrictSection_mulSections, restrictSection_zeroSection]

/-- **The nonvanishing open of `s³` of a restricted family is the preimage of that of `s³`.** -/
private theorem nonvanishingOpen_cube_pullback (g : T ⟶ S) :
    nonvanishingOpen (E.pullback g).total (natTensorPow (E.pullback g).zeroSheaf 3)
        (cube _ (E.pullback g).zeroSection) =
      Limits.pullback.fst E.map g ⁻¹ᵁ
        nonvanishingOpen E.total (natTensorPow E.zeroSheaf 3) (cube E.zeroSheaf E.zeroSection) := by
  rw [← restrictSection_cube_zeroSection, nonvanishingOpen_restrictSection]

/-- **The canonical section of `O(0)` vanishes along the zero section.** -/
theorem pullSection_zero_zeroSection :
    Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullSection E.zero E.zeroSheaf 1
      E.zeroSection = 0 := by
  unfold zeroSection
  refine (Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullSection_twistOneSection _ _ _).trans
    ?_
  show twistOneSection _ (pullbackSectionHom E.zero (invertibleSheaf' E.zeroDivisor) ⊤ ⊤ _
    ((canonicalSection' E.zeroDivisor).val (op ⊤))) = 0
  rw [Stacks.Divisors.pullbackSectionHom_canonicalSection_eq_zero E.zeroDivisor E.zero le_rfl]
  exact map_zero _

/-- A section whose pullback along the zero section, read in a tensor power, is zero has zero
pullback. -/
theorem pullbackSectionHom_zero_eq_zero {n : ℕ} {w : Γ(natTensorPow E.zeroSheaf n, ⊤)}
    (h : Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullSection E.zero E.zeroSheaf n w = 0) :
    pullbackSectionHom E.zero (natTensorPow E.zeroSheaf n) ⊤ ⊤ (by simp) w = 0 := by
  unfold Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullSection at h
  have := congrArg (fun b =>
    (Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullbackNatTensorPowIso
    E.zero E.zeroSheaf n).hom.app ⊤ b) h
  simp only [map_zero] at this
  rwa [Stacks.AlgebraicGeometry.ProjVeroneseRestrict.hom_app_inv_app] at this

/-- A product with a factor whose pullback along the zero section vanishes has zero pullback. -/
private theorem pullbackSectionHom_zero_mulSections_eq_zero {n m : ℕ}
    (a : Γ(natTensorPow E.zeroSheaf n, ⊤)) (b : Γ(natTensorPow E.zeroSheaf m, ⊤))
    (h : Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullSection E.zero E.zeroSheaf n a = 0 ∨
      Stacks.AlgebraicGeometry.ProjChartRatioPullback.pullSection E.zero E.zeroSheaf m b = 0) :
    pullbackSectionHom E.zero (natTensorPow E.zeroSheaf (n + m)) ⊤ ⊤ (by simp)
      (mulSections E.zeroSheaf a b) = 0 := by
  refine E.pullbackSectionHom_zero_eq_zero ?_
  rw [Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.pullSection_mulSections]
  apply GenusOne.ringElt_injective
  rw [GenusOne.ringElt_mulSections, GenusOne.ringElt_zero]
  rcases h with h | h <;> simp [h, GenusOne.ringElt_zero]

/-- **Multiples of the canonical section vanish along the zero section.** -/
theorem pullbackSectionHom_zero_mulSections_zeroSection {m : ℕ}
    (t : Γ(natTensorPow E.zeroSheaf m, ⊤)) :
    pullbackSectionHom E.zero (natTensorPow E.zeroSheaf (1 + m)) ⊤ ⊤ (by simp)
      (mulSections E.zeroSheaf E.zeroSection t) = 0 :=
  E.pullbackSectionHom_zero_mulSections_eq_zero _ _ (Or.inl (pullSection_zero_zeroSection E))

/-- **`s³` vanishes along the zero section.** -/
theorem pullbackSectionHom_zero_cube :
    pullbackSectionHom E.zero (natTensorPow E.zeroSheaf 3) ⊤ ⊤ (by simp)
      (cube E.zeroSheaf E.zeroSection) = 0 := by
  rw [cube, sq]
  show pullbackSectionHom E.zero (natTensorPow E.zeroSheaf ((1 + 1) + 1)) ⊤ ⊤ _ _ = 0
  exact E.pullbackSectionHom_zero_mulSections_eq_zero _ _
    (Or.inr (pullSection_zero_zeroSection E))

end Restriction

section Affine

/-- The point of `Spec A` under the closed point of `Spec κ(p)` is `p`. -/
theorem SpecMap_algebraMap_residueField_closedPoint {A : Type u} [CommRing A] (p : Ideal A)
    [p.IsPrime] :
    ((Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)))
      (IsLocalRing.closedPoint p.ResidueField)).asIdeal = p := by
  show Ideal.comap (algebraMap A p.ResidueField)
    (IsLocalRing.maximalIdeal p.ResidueField) = p
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot,
    Ideal.ker_algebraMap_residueField]

/-- **`Spec B ⟶ Spec A` lands in `D(a)` when `a` becomes a unit in `B`.** -/
theorem SpecMap_preimage_basicOpen_eq_top {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {a : A} (hu : IsUnit (φ a)) :
    Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ
      (Spec (CommRingCat.of A)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = ⊤ := by
  rw [Scheme.preimage_basicOpen]
  apply Scheme.basicOpen_of_isUnit
  have h := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  have hu' : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (φ a)) := hu.map _
  rwa [h] at hu'

/-- **A function nonvanishing at the closed point of `Spec κ(p)` does not lie in `p`.** -/
private theorem ΓSpecIso_hom_notMem_of_mem_basicOpen {A : Type u} [CommRing A] (p : Ideal A)
    [p.IsPrime] {r : Γ(Spec (CommRingCat.of A), ⊤)}
    (h : Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))
      (IsLocalRing.closedPoint p.ResidueField) ∈ (Spec (CommRingCat.of A)).basicOpen r) :
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom r ∉ p := by
  rw [← (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id_apply r, basicOpen_eq_of_affine] at h
  have := (PrimeSpectrum.mem_basicOpen _ _).mp h
  rwa [SpecMap_algebraMap_residueField_closedPoint] at this

/-- **`Spec B ⟶ Spec A` lands in `D(r)` when `r` becomes a unit in `B`.** -/
private theorem SpecMap_preimage_basicOpen_eq_top_of_isUnit {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {r : Γ(Spec (CommRingCat.of A), ⊤)}
    (hu : IsUnit (φ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom r))) :
    Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ (Spec (CommRingCat.of A)).basicOpen r = ⊤ := by
  rw [← (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id_apply r]
  exact SpecMap_preimage_basicOpen_eq_top φ hu

/-- **Rescaling `y` by a unit of `B` does not change its nonvanishing open after base change.** -/
private theorem nonvanishingOpen_smul_restrictSection {A B : Type u} [CommRing A] [CommRing B]
    (E : PointedFamily (Spec (.of A))) [IsProper E.map] [SmoothOfRelativeDimension 1 E.map]
    (g : Spec (.of B) ⟶ Spec (.of A)) (v : Bˣ) (y : Γ(natTensorPow E.zeroSheaf 3, ⊤)) :
    letI := Stacks.Cech.sectionsModule (E.pullback g).map
      (natTensorPow (E.pullback g).zeroSheaf 3) ⊤
    nonvanishingOpen (E.pullback g).total (natTensorPow (E.pullback g).zeroSheaf 3)
        ((Stacks.Cech.baseRingHom (E.pullback g).map ⊤).hom (v : B) •
          E.restrictSection g 3 y) =
      Limits.pullback.fst E.map g ⁻¹ᵁ nonvanishingOpen E.total (natTensorPow E.zeroSheaf 3) y := by
  rw [GenusOne.nonvanishingOpen_smul_of_isUnit ((Units.isUnit v).map _),
    nonvanishingOpen_restrictSection]

/-- **Near a fibre of genus one, `y` and `s³` generate `O(0)^{⊗ 3}`.** Let `E` be a pointed family
over `Spec A`, proper and smooth of relative dimension one, whose fibre at the prime `p` is a curve
of genus one, and `y` a section of `O(0)^{⊗ 3}` whose restriction to the fibre is not a multiple
of `s`. There is `r ∉ p` such that after any base change `A ⟶ B` inverting `r`, and rescaling by
a unit of `B`, the nonvanishing opens of `s x, y, s³` cover the total space. -/
theorem exists_isOpenCover_nvCover {A : Type u} [CommRing A] (E : PointedFamily (Spec (.of A)))
    [IsProper E.map] [SmoothOfRelativeDimension 1 E.map] (p : Ideal A) [p.IsPrime]
    (h0 : Module.finrank p.ResidueField (structureSheafCohomology
      (E.pullback (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)))).map 0) = 1)
    (h1 : genus (E.pullback (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)))).map = 1)
    (x : Γ(natTensorPow E.zeroSheaf 2, ⊤)) {y : Γ(natTensorPow E.zeroSheaf 3, ⊤)}
    (hy : E.restrictSection (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))) 3 y ∉
      Set.range (mulSections
        (E.pullback (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)))).zeroSheaf
        (m := 2)
        (E.pullback (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)))).zeroSection)) :
    ∃ r : A, r ∉ p ∧ ∀ {B : Type u} [CommRing B] (φ : A →+* B), IsUnit (φ r) → ∀ v : Bˣ,
      letI := Stacks.Cech.sectionsModule (E.pullback (Spec.map (CommRingCat.ofHom φ))).map
        (natTensorPow (E.pullback (Spec.map (CommRingCat.ofHom φ))).zeroSheaf 2) ⊤
      letI := Stacks.Cech.sectionsModule (E.pullback (Spec.map (CommRingCat.ofHom φ))).map
        (natTensorPow (E.pullback (Spec.map (CommRingCat.ofHom φ))).zeroSheaf 3) ⊤
      IsOpenCover (nvCover (![mulSections _
          (E.pullback (Spec.map (CommRingCat.ofHom φ))).zeroSection
          ((v : B) • E.restrictSection (Spec.map (CommRingCat.ofHom φ)) 2 x),
        (v : B) • E.restrictSection (Spec.map (CommRingCat.ofHom φ)) 3 y,
        cube _ (E.pullback (Spec.map (CommRingCat.ofHom φ))).zeroSection] :
          Fin 3 → Γ(natTensorPow (E.pullback (Spec.map (CommRingCat.ofHom φ))).zeroSheaf 3,
            ⊤))) := by
  set gp := Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))
  set V := nonvanishingOpen E.total (natTensorPow E.zeroSheaf 3) y ⊔
    nonvanishingOpen E.total (natTensorPow E.zeroSheaf 3) (cube E.zeroSheaf E.zeroSection)
  obtain ⟨-, hcov⟩ := (E.pullback gp).zero_mem_nonvanishingOpen h0 h1 hy
  have hfib : ∀ e : E.total, E.map e = gp (IsLocalRing.closedPoint p.ResidueField) → e ∈ V := by
    intro e he
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback e _ he
    rcases hcov z with h | h
    · rw [nonvanishingOpen_restrictSection] at h
      exact Or.inl (hz ▸ h)
    · rw [nonvanishingOpen_cube_pullback] at h
      exact Or.inr (hz ▸ h)
  obtain ⟨r₁, hpt, hle⟩ := exists_mem_basicOpen_preimage_le E.map V _ hfib
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom r₁,
    ΓSpecIso_hom_notMem_of_mem_basicOpen p hpt, fun {B} _ φ hu v => ?_⟩
  have htop := SpecMap_preimage_basicOpen_eq_top_of_isUnit φ hu
  set g := Spec.map (CommRingCat.ofHom φ)
  unfold IsOpenCover
  rw [eq_top_iff]
  intro z _
  rw [Opens.mem_iSup]
  have hz : E.map (Limits.pullback.fst E.map g z) ∈ (Spec (CommRingCat.of A)).basicOpen r₁ := by
    have h := congrArg (fun f => f z) (Limits.pullback.condition (f := E.map) (g := g))
    simp only [Scheme.Hom.comp_apply] at h
    rw [h]
    exact htop.ge (show Limits.pullback.snd E.map g z ∈ (⊤ : (Spec (CommRingCat.of B)).Opens)
      from trivial)
  rcases hle hz with h | h
  · exact ⟨1, (nonvanishingOpen_smul_restrictSection E g v y).ge h⟩
  · exact ⟨2, (nonvanishingOpen_cube_pullback E g).ge h⟩

/-- **Near a fibre of genus one, the zero section lies in the chart of `y`, where `s x / y` and
`s³ / y` vanish along it.** With the hypotheses of `exists_isOpenCover_nvCover`, there is `r ∉ p`
such that after any base change `A ⟶ B` inverting `r`, and rescaling by a unit of `B`, the zero
section factors through the nonvanishing open of `y`, and there the ratios `s x / y` and
`s³ / y` pull back to zero. -/
theorem exists_zero_lift_nvCover {A : Type u} [CommRing A] (E : PointedFamily (Spec (.of A)))
    [IsProper E.map] [SmoothOfRelativeDimension 1 E.map] (p : Ideal A) [p.IsPrime]
    (h0 : Module.finrank p.ResidueField (structureSheafCohomology
      (E.pullback (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)))).map 0) = 1)
    (h1 : genus (E.pullback (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)))).map = 1)
    (x : Γ(natTensorPow E.zeroSheaf 2, ⊤)) {y : Γ(natTensorPow E.zeroSheaf 3, ⊤)}
    (hy : E.restrictSection (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))) 3 y ∉
      Set.range (mulSections
        (E.pullback (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)))).zeroSheaf
        (m := 2)
        (E.pullback (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)))).zeroSection)) :
    ∃ r : A, r ∉ p ∧ ∀ {B : Type u} [CommRing B] (φ : A →+* B), IsUnit (φ r) → ∀ v : Bˣ,
      letI := Stacks.Cech.sectionsModule (E.pullback (Spec.map (CommRingCat.ofHom φ))).map
        (natTensorPow (E.pullback (Spec.map (CommRingCat.ofHom φ))).zeroSheaf 2) ⊤
      letI := Stacks.Cech.sectionsModule (E.pullback (Spec.map (CommRingCat.ofHom φ))).map
        (natTensorPow (E.pullback (Spec.map (CommRingCat.ofHom φ))).zeroSheaf 3) ⊤
      let s : Fin 3 → Γ(natTensorPow (E.pullback (Spec.map (CommRingCat.ofHom φ))).zeroSheaf 3,
          ⊤) := ![mulSections _ (E.pullback (Spec.map (CommRingCat.ofHom φ))).zeroSection
          ((v : B) • E.restrictSection (Spec.map (CommRingCat.ofHom φ)) 2 x),
        (v : B) • E.restrictSection (Spec.map (CommRingCat.ofHom φ)) 3 y,
        cube _ (E.pullback (Spec.map (CommRingCat.ofHom φ))).zeroSection]
      ∃ σ₁ : Spec (.of B) ⟶ (nvCover s 1).toScheme,
        σ₁ ≫ (nvCover s 1).ι = (E.pullback (Spec.map (CommRingCat.ofHom φ))).zero ∧
          σ₁.appTop (Stacks.ProjectiveFromSections.chartRatio s 1 0) = 0 ∧
          σ₁.appTop (Stacks.ProjectiveFromSections.chartRatio s 1 2) = 0 := by
  set gp := Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))
  set N := nonvanishingOpen E.total (natTensorPow E.zeroSheaf 3) y
  obtain ⟨hz0, -⟩ := (E.pullback gp).zero_mem_nonvanishingOpen h0 h1 hy
  rw [nonvanishingOpen_restrictSection] at hz0
  have hzero : ∀ {T : Scheme.{u}} (g : T ⟶ Spec (.of A)) (t : T),
      Limits.pullback.fst E.map g ((E.pullback g).zero t) = E.zero (g t) := fun {T} g t => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    exact congrArg (fun f : T ⟶ E.total => f t)
      (Limits.pullback.lift_fst (g ≫ E.zero) (𝟙 T) _)
  have hpt : gp (IsLocalRing.closedPoint p.ResidueField) ∈ E.zero ⁻¹ᵁ N := by
    change Limits.pullback.fst E.map gp ((E.pullback gp).zero _) ∈ N at hz0
    exact (congrArg (· ∈ N) (hzero gp _)).mp hz0
  obtain ⟨_, ⟨r₂, rfl⟩, hpt₂, hle₂⟩ := Opens.isBasis_iff_nbhd.mp
    (isBasis_basicOpen (Spec (CommRingCat.of A))) hpt
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom r₂,
    ΓSpecIso_hom_notMem_of_mem_basicOpen p hpt₂, fun {B} _ φ hu v => ?_⟩
  have htop := SpecMap_preimage_basicOpen_eq_top_of_isUnit φ hu
  set g := Spec.map (CommRingCat.ofHom φ)
  refine ⟨IsOpenImmersion.lift _ (E.pullback g).zero ?hr, IsOpenImmersion.lift_fac _ _ _, ?_, ?_⟩
  case hr =>
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    refine (nonvanishingOpen_smul_restrictSection E g v y).ge ?_
    show Limits.pullback.fst E.map g ((E.pullback g).zero t) ∈ N
    rw [hzero]
    exact hle₂ (htop.ge (show t ∈ (⊤ : (Spec (CommRingCat.of B)).Opens) from trivial))
  · refine GenusOne.appTop_chartRatio_eq_zero _ 1 0 _ ?_
    rw [IsOpenImmersion.lift_fac]
    exact (E.pullback g).pullbackSectionHom_zero_mulSections_zeroSection (m := 2)
      ((Stacks.Cech.baseRingHom (E.pullback g).map ⊤).hom (v : B) • E.restrictSection g 2 x)
  · refine GenusOne.appTop_chartRatio_eq_zero _ 1 2 _ ?_
    rw [IsOpenImmersion.lift_fac]
    exact (E.pullback g).pullbackSectionHom_zero_cube

end Affine

end AlgebraicGeometry.ModuliEllipticCurves.PointedFamily

end
