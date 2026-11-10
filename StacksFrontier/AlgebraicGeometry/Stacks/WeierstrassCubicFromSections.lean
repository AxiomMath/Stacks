module

public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassFamily
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicIso
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassFamilyElliptic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsomorphismOnFibre
public import StacksFrontier.AlgebraicGeometry.AmplePowers.Basic
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Consumers
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Basic
public import StacksFrontier.AlgebraicGeometry.VanishingSystemImmersion.Restriction

/-!
# The morphism to a plane Weierstrass cubic given by three sections of an invertible module
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open HomogeneousLocalization
open Stacks.ProjGlobalSectionsAppTop

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

section General

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : Scheme.{u}}

/-- **The morphism to `Proj` of a ring map is blind to a scaling of the ring map by a unit in
each degree.** If `f₁ p = uⁿ · f₂ p` for every `p` of degree `n`, with `u` a unit, the two ring
maps define the same morphism `Y ⟶ Proj 𝒜`. -/
theorem fromOfGlobalSections_eq_of_unit (f₁ f₂ : A →+* Γ(Y, ⊤)) (u : Γ(Y, ⊤)ˣ)
    (h : ∀ (n : ℕ) (p : A), p ∈ 𝒜 n → f₁ p = (u : Γ(Y, ⊤)) ^ n * f₂ p)
    (hf₁ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f₁ = ⊤)
    (hf₂ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f₂ = ⊤) :
    Proj.fromOfGlobalSections 𝒜 f₁ hf₁ = Proj.fromOfGlobalSections 𝒜 f₂ hf₂ := by
  refine (Proj.openCoverOfMapIrrelevantEqTop 𝒜 f₂ hf₂).hom_ext _ _ fun c => ?_
  obtain ⟨d, t, h0d, hd⟩ := c
  have heq : Y.basicOpen (f₁ t) = Y.basicOpen (f₂ t) := by
    rw [h d t hd, Scheme.basicOpen_mul, Y.basicOpen_of_isUnit (u.isUnit.pow d), top_inf_eq]
  have key : Y.homOfLE heq.ge ≫ Proj.toBasicOpenOfGlobalSections 𝒜 f₁ rfl h0d hd =
      Proj.toBasicOpenOfGlobalSections 𝒜 f₂ rfl h0d hd :=
    toBasicOpenOfGlobalSections_eq_of_projAwayHom 𝒜 f₁ f₂ h0d hd heq.ge
      (projAwayHom_comp_of_scaling 𝒜 f₁ f₂ ((u : Γ(Y, ⊤)) ^ d) hd heq.ge (h d t hd)
        fun k p hp => by rw [h _ p hp, smul_eq_mul, ← pow_mul, mul_comm d k])
  change (Y.basicOpen (f₂ t)).ι ≫ _ = (Y.basicOpen (f₂ t)).ι ≫ _
  rw [ι_comp_fromOfGlobalSections 𝒜 f₂ hf₂ h0d hd, ← key, Category.assoc,
    ← ι_comp_fromOfGlobalSections 𝒜 f₁ hf₁ h0d hd, ← Category.assoc, Scheme.homOfLE_ι]

/-- **The morphism to `Proj` of a ring map is natural in the source scheme.** -/
theorem comp_fromOfGlobalSections {Y' : Scheme.{u}} (g : Y' ⟶ Y) (f : A →+* Γ(Y, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hgf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (g.appTop.hom.comp f) = ⊤) :
    g ≫ Proj.fromOfGlobalSections 𝒜 f hf =
      Proj.fromOfGlobalSections 𝒜 (g.appTop.hom.comp f) hgf := by
  set f' := g.appTop.hom.comp f with hf'
  refine (Proj.openCoverOfMapIrrelevantEqTop 𝒜 f' hgf).hom_ext _ _ fun c => ?_
  obtain ⟨d, t, h0d, hd⟩ := c
  have he : Y'.basicOpen (f' t) = g ⁻¹ᵁ Y.basicOpen (f t) := by
    rw [hf', RingHom.comp_apply, Scheme.preimage_basicOpen]
    rfl
  have hstep : (g.appLE (Y.basicOpen (f t)) (Y'.basicOpen (f' t)) he.le).hom
        (resTop (Y.basicOpen (f t)) (f t)) = resTop (Y'.basicOpen (f' t)) (f' t) := by
    rw [appLE_resTop]; rfl
  have hψ : (g.appLE (Y.basicOpen (f t)) (Y'.basicOpen (f' t)) he.le).hom.comp
      (projAwayHom 𝒜 f) = projAwayHom 𝒜 f' := by
    refine away_ringHom_ext 𝒜 hd fun k p hp => ?_
    have hv : resTop (Y.basicOpen (f t)) (f t) * resTopBasicOpenInv (f t) = 1 :=
      (isUnit_resTop_basicOpen _).unit.mul_inv
    have hv' : resTop (Y'.basicOpen (f' t)) (f' t) *
        (g.appLE _ _ he.le).hom (resTopBasicOpenInv (f t)) = 1 := by
      rw [← hstep, ← map_mul, hv, map_one]
    change (g.appLE _ _ he.le).hom (projAwayHom 𝒜 f (Away.mk 𝒜 hd k p hp)) =
      projAwayHom 𝒜 f' (Away.mk 𝒜 hd k p hp)
    rw [projAwayHom_apply_mk_of_mul_eq_one 𝒜 f hd k p hp hv,
      projAwayHom_apply_mk_of_mul_eq_one 𝒜 f' hd k p hp hv', map_mul, map_pow, appLE_resTop]
    rfl
  have key := toBasicOpenOfGlobalSections_eq_of_projAwayHom_resLE 𝒜 g f f' h0d hd he.le hψ
  change (Y'.basicOpen (f' t)).ι ≫ g ≫ _ = (Y'.basicOpen (f' t)).ι ≫ _
  rw [ι_comp_fromOfGlobalSections 𝒜 f' hgf h0d hd, ← key, Category.assoc,
    ← ι_comp_fromOfGlobalSections 𝒜 f hf h0d hd, ← Category.assoc (g.resLE _ _ _),
    Scheme.Hom.resLE_comp_ι, Category.assoc]


end General

section Cubic

open Stacks.ProjectiveFromSections

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] (C : WeierstrassCurve R) {X : Scheme.{u}}
  (π : X ⟶ Spec (.of R)) {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
  (s : Fin 3 → Γ(L, ⊤))

/-- The class of the variable `x`, `y` or `z` in the homogeneous coordinate ring of the cubic. -/
abbrev coordVar (k : Fin 3) : coordRingOf C :=
  Ideal.Quotient.mk (cubicIdealOf C).toIdeal (MvPolynomial.X k)

/-- Each coordinate variable is homogeneous of degree `1`. -/
theorem coordVar_mem (k : Fin 3) : coordVar C k ∈ gradingOf C 1 :=
  Stacks.HomogeneousIdeal.mk_mem_quotientGrading _
    (by rw [MvPolynomial.mem_homogeneousSubmodule]; exact MvPolynomial.isHomogeneous_X _ _)

/-- The ring map `R ⟶ Γ(V, 𝒪)` of an open `V` of a scheme over `Spec R`. -/
def openBase (V : X.Opens) : R →+* Γ(V.toScheme, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ (V.ι ≫ π).appTop).hom

/-- The structure ring maps of opens are compatible with restriction. -/
theorem homOfLE_appTop_comp_openBase {V W : X.Opens} (h : V ≤ W) :
    (X.homOfLE h).appTop.hom.comp (openBase π W) = openBase π V := by
  rw [openBase, openBase, ← CommRingCat.hom_comp, Category.assoc, ← Scheme.Hom.comp_appTop,
    ← Category.assoc, Scheme.homOfLE_ι]

/-- The ring map `R[x, y, z] ⟶ Γ(X_{sᵢ}, 𝒪)` sending `x, y, z` to `s₀/sᵢ, s₁/sᵢ, s₂/sᵢ`. -/
def chartPolyHom (i : Fin 3) : MvPolynomial (Fin 3) R →+* Γ((nvCover s i).toScheme, ⊤) :=
  MvPolynomial.eval₂Hom (openBase π (nvCover s i)) (chartRatio s i)

/-- The ratios of the three sections satisfy the Weierstrass cubic of `C` on every chart. -/
def SatisfiesCubic : Prop := ∀ i : Fin 3, chartPolyHom π s i (cubicOf C) = 0

variable {C π s}

/-- The ring map `R[x, y, z]/(F) ⟶ Γ(X_{sᵢ}, 𝒪)` of the `i`-th chart. -/
def chartRingHom (hrel : SatisfiesCubic C π s) (i : Fin 3) :
    coordRingOf C →+* Γ((nvCover s i).toScheme, ⊤) :=
  Ideal.Quotient.lift _ (chartPolyHom π s i) fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hrel i, mul_zero]

/-- On the class of a polynomial `P`, the chart ring map is evaluation of `P` at the ratios. -/
@[simp]
theorem chartRingHom_mk (hrel : SatisfiesCubic C π s) (i : Fin 3) (P : MvPolynomial (Fin 3) R) :
    chartRingHom hrel i (Ideal.Quotient.mk _ P) = chartPolyHom π s i P :=
  rfl

/-- The irrelevant ideal generates the unit ideal under the `i`-th chart ring map. -/
theorem chartRingHom_irrelevant (hrel : SatisfiesCubic C π s) (i : Fin 3) :
    (HomogeneousIdeal.irrelevant (gradingOf C)).toIdeal.map (chartRingHom hrel i) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h1 : chartRingHom hrel i (coordVar C i) = 1 := by
    change chartRingHom hrel i (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 1
    rw [chartRingHom_mk, chartPolyHom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X,
      chartRatio_self]
  exact h1 ▸ Ideal.mem_map_of_mem _
    (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos (coordVar_mem C i))

/-- **The morphism `X_{sᵢ} ⟶ projOf C` of the `i`-th chart.** -/
def cubicChartHom (hrel : SatisfiesCubic C π s) (i : Fin 3) :
    (nvCover s i).toScheme ⟶ projOf C :=
  Proj.fromOfGlobalSections (gradingOf C) (chartRingHom hrel i) (chartRingHom_irrelevant hrel i)

/-- Precomposing a chart morphism with a morphism `g` whose ring map intertwines the chart
polynomial maps gives the chart morphism of the other sections. -/
private theorem comp_cubicChartHom_of_comp_chartPolyHom {X' : Scheme.{u}} {π' : X' ⟶ Spec (.of R)}
    {L' : X'.Modules} [Stacks.Ample.IsInvertibleModule X' L'] {s' : Fin 3 → Γ(L', ⊤)}
    (hrel : SatisfiesCubic C π s) (hrel' : SatisfiesCubic C π' s') (i : Fin 3)
    (g : (nvCover s' i).toScheme ⟶ (nvCover s i).toScheme)
    (h : g.appTop.hom.comp (chartPolyHom π s i) = chartPolyHom π' s' i) :
    g ≫ cubicChartHom hrel i = cubicChartHom hrel' i := by
  have hring : g.appTop.hom.comp (chartRingHom hrel i) = chartRingHom hrel' i := by
    refine Ideal.Quotient.ringHom_ext ?_
    rw [RingHom.comp_assoc]
    exact h
  have hirr : (HomogeneousIdeal.irrelevant (gradingOf C)).toIdeal.map
      (g.appTop.hom.comp (chartRingHom hrel i)) = ⊤ := by
    rw [hring]; exact chartRingHom_irrelevant _ i
  refine (comp_fromOfGlobalSections (gradingOf C) g _ _ hirr).trans ?_
  change Proj.fromOfGlobalSections _ _ hirr = Proj.fromOfGlobalSections _ _ _
  congr 1

/-- On an overlap the two chart ring maps differ by the transition unit in each degree. -/
theorem chartRingHom_scaling (hrel : SatisfiesCubic C π s) (i j : Fin 3) (n : ℕ)
    (p : coordRingOf C) (hp : p ∈ gradingOf C n) :
    (X.homOfLE (inf_le_left : nvCover s i ⊓ nvCover s j ≤ nvCover s i)).appTop.hom
        (chartRingHom hrel i p) =
      ((chartTransUnit s i j : Γ((nvCover s i ⊓ nvCover s j : X.Opens).toScheme, ⊤))) ^ n *
        (X.homOfLE (inf_le_right : nvCover s i ⊓ nvCover s j ≤ nvCover s j)).appTop.hom
          (chartRingHom hrel j p) := by
  obtain ⟨P, hP, rfl⟩ := (Stacks.HomogeneousIdeal.mem_quotientGrading_iff _ p).mp hp
  rw [chartRingHom_mk, chartRingHom_mk, chartPolyHom, chartPolyHom, ← RingHom.comp_apply,
    ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom, MvPolynomial.comp_eval₂Hom,
    homOfLE_appTop_comp_openBase, homOfLE_appTop_comp_openBase, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.coe_eval₂Hom]
  have hfun : (fun k =>
      (X.homOfLE (inf_le_left : nvCover s i ⊓ nvCover s j ≤ nvCover s i)).appTop.hom
        (chartRatio s i k)) = fun k => (chartTransUnit s i j : Γ((nvCover s i ⊓ nvCover s j :
        X.Opens).toScheme, ⊤)) *
      (X.homOfLE (inf_le_right : nvCover s i ⊓ nvCover s j ≤ nvCover s j)).appTop.hom
        (chartRatio s j k) := funext fun k => chartRatio_agree s i j k
  change MvPolynomial.eval₂ _ (fun k => _) P = _
  rw [hfun]
  exact eval₂_of_isHomogeneous _ _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hP)

/-- **The chart morphisms agree on the overlaps.** -/
theorem cubicChartHom_agree (hrel : SatisfiesCubic C π s) (i j : Fin 3) :
    X.homOfLE (inf_le_left : nvCover s i ⊓ nvCover s j ≤ nvCover s i) ≫ cubicChartHom hrel i =
      X.homOfLE (inf_le_right : nvCover s i ⊓ nvCover s j ≤ nvCover s j) ≫
        cubicChartHom hrel j := by
  have hirr : ∀ {k : Fin 3} (h : nvCover s i ⊓ nvCover s j ≤ nvCover s k),
      (HomogeneousIdeal.irrelevant (gradingOf C)).toIdeal.map
        ((X.homOfLE h).appTop.hom.comp (chartRingHom hrel k)) = ⊤ := fun _ => by
    rw [← Ideal.map_map, chartRingHom_irrelevant, Ideal.map_top]
  exact (comp_fromOfGlobalSections (gradingOf C) _ _ _ (hirr inf_le_left)).trans
    ((fromOfGlobalSections_eq_of_unit (gradingOf C) _ _ (chartTransUnit s i j)
      (fun n p hp => chartRingHom_scaling hrel i j n p hp) _ _).trans
      (comp_fromOfGlobalSections (gradingOf C) _ _ _ (hirr inf_le_right)).symm)

/-- **The morphism `X ⟶ projOf C` given by three sections of an invertible module** whose
nonvanishing opens cover `X` and whose ratios satisfy the Weierstrass cubic of `C`: on the
`i`-th chart it is `cubicChartHom`. -/
def cubicHomOfSections (hrel : SatisfiesCubic C π s) (hcov : IsOpenCover (nvCover s)) :
    X ⟶ projOf C :=
  (X.openCoverOfIsOpenCover (nvCover s) hcov).glueMorphisms (cubicChartHom hrel) fun i j => by
    change pullback.fst (nvCover s i).ι (nvCover s j).ι ≫ cubicChartHom hrel i =
      pullback.snd (nvCover s i).ι (nvCover s j).ι ≫ cubicChartHom hrel j
    rw [← cancel_epi (isPullback_opens_inf (nvCover s i) (nvCover s j)).isoPullback.hom,
      ← Category.assoc, ← Category.assoc,
      (isPullback_opens_inf (nvCover s i) (nvCover s j)).isoPullback_hom_fst,
      (isPullback_opens_inf (nvCover s i) (nvCover s j)).isoPullback_hom_snd]
    exact cubicChartHom_agree hrel i j

/-- **On the `i`-th chart the glued morphism is the chart morphism.** -/
theorem ι_cubicHomOfSections (hrel : SatisfiesCubic C π s) (hcov : IsOpenCover (nvCover s))
    (i : Fin 3) : (nvCover s i).ι ≫ cubicHomOfSections hrel hcov = cubicChartHom hrel i :=
  (X.openCoverOfIsOpenCover (nvCover s) hcov).ι_glueMorphisms _ _ i

/-- A morphism to an affine scheme is the morphism of its ring map on global sections. -/
theorem eq_toSpecΓ_comp_SpecMap {Y : Scheme.{u}} {S : CommRingCat.{u}} (g : Y ⟶ Spec S) :
    g = Y.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso S).inv ≫ g.appTop) := by
  have h := Scheme.toSpecΓ_naturality g =≫ Spec.map (Scheme.ΓSpecIso S).inv
  rw [Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id, Category.assoc,
    ← Spec.map_comp] at h
  exact h

/-- **The morphism given by the sections lies over `Spec R`.** -/
theorem cubicHomOfSections_projectionOf (hrel : SatisfiesCubic C π s)
    (hcov : IsOpenCover (nvCover s)) : cubicHomOfSections hrel hcov ≫ projectionOf C = π := by
  refine (X.openCoverOfIsOpenCover (nvCover s) hcov).hom_ext _ _ fun (i : Fin 3) => ?_
  change (nvCover s i).ι ≫ cubicHomOfSections hrel hcov ≫ projectionOf C = (nvCover s i).ι ≫ π
  rw [← Category.assoc, ι_cubicHomOfSections]
  have hring : ((chartRingHom hrel i).comp (algebraMap (gradingOf C 0) (coordRingOf C))).comp
      (toGradingZeroOf C) = openBase π (nvCover s i) := by
    ext a
    simp [toGradingZeroOf, chartPolyHom]
  change Proj.fromOfGlobalSections (gradingOf C) (chartRingHom hrel i)
      (chartRingHom_irrelevant hrel i) ≫ Proj.toSpecZero (gradingOf C) ≫
      Spec.map (CommRingCat.ofHom (toGradingZeroOf C)) = _
  rw [Proj.fromOfGlobalSections_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    hring, openBase, CommRingCat.ofHom_hom]
  exact (eq_toSpecΓ_comp_SpecMap _).symm

/-! ### Naturality in the source -/

section Pullback

variable (s) {Y : Scheme.{u}} (g : Y ⟶ X)
  [Stacks.Ample.IsInvertibleModule Y ((Scheme.Modules.pullback g).obj L)]

/-- The pulled-back sections. -/
abbrev pullbackFamily : Fin 3 → Γ((Scheme.Modules.pullback g).obj L, ⊤) :=
  fun k => pullbackGlobalSections g L (s k)

/-- The nonvanishing locus of a pulled-back section is the preimage of the nonvanishing locus. -/
theorem nvCover_pullbackFamily (i : Fin 3) :
    nvCover (pullbackFamily s g) i = g ⁻¹ᵁ nvCover s i :=
  Stacks.RatioPullback.nvOpen_pullbackGlobalSections g L (s i)

/-- The restriction of `g` to the `i`-th charts. -/
abbrev chartRestrict (i : Fin 3) :
    (nvCover (pullbackFamily s g) i).toScheme ⟶ (nvCover s i).toScheme :=
  g.resLE (nvCover s i) (nvCover (pullbackFamily s g) i) (nvCover_pullbackFamily s g i).le

/-- Restriction along `g` carries the ratios of the sections to the ratios of the pulled-back
sections. -/
theorem chartRestrict_appTop_chartRatio (i k : Fin 3) :
    (chartRestrict s g i).appTop (chartRatio s i k) = chartRatio (pullbackFamily s g) i k := by
  have h := CategoryTheory.ConcreteCategory.congr_hom (topIso_inv_resLE_appTop g
    (nvCover_pullbackFamily s g i).le) (ratio s i k)
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at h
  rw [chartRatio, chartRatio, h, ← Stacks.RatioPullback.resO_ratio_pullbackGlobalSections g L s i k
    le_rfl (nvCover_pullbackFamily s g i).le]
  congr 1
  change (Y.presheaf.map (𝟙 _)) _ = _
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- Restriction along `g` is compatible with the structure ring maps from `R`. -/
theorem chartRestrict_appTop_openBase (i : Fin 3) :
    (chartRestrict s g i).appTop.hom.comp (openBase π (nvCover s i)) =
      openBase (g ≫ π) (nvCover (pullbackFamily s g) i) := by
  rw [openBase, openBase, ← CommRingCat.hom_comp, Category.assoc, ← Scheme.Hom.comp_appTop,
    ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]

/-- Restriction along `g` carries the `i`-th chart polynomial map of the sections to that of the
pulled-back sections. -/
theorem chartRestrict_comp_chartPolyHom (i : Fin 3) :
    (chartRestrict s g i).appTop.hom.comp (chartPolyHom π s i) =
      chartPolyHom (g ≫ π) (pullbackFamily s g) i := by
  rw [chartPolyHom, chartPolyHom, MvPolynomial.comp_eval₂Hom, chartRestrict_appTop_openBase]
  congr 1
  funext k
  exact chartRestrict_appTop_chartRatio s g i k

variable {s g}

/-- The pulled-back sections satisfy the cubic. -/
theorem satisfiesCubic_pullbackFamily (hrel : SatisfiesCubic C π s) :
    SatisfiesCubic C (g ≫ π) (pullbackFamily s g) := fun i => by
  rw [← chartRestrict_comp_chartPolyHom s g i, RingHom.comp_apply, hrel i, map_zero]

/-- The nonvanishing opens of the pulled-back sections cover the source. -/
theorem isOpenCover_pullbackFamily (hcov : IsOpenCover (nvCover s)) :
    IsOpenCover (nvCover (pullbackFamily s g)) := by
  refine eq_top_iff.2 fun y _ => ?_
  have hy : g y ∈ (⨆ i, nvCover s i) := by
    rw [show (⨆ i, nvCover s i) = ⊤ from hcov]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
  rw [nvCover_pullbackFamily]
  exact hi

/-- **The morphism given by the sections is natural in the source scheme.** -/
theorem comp_cubicHomOfSections (hrel : SatisfiesCubic C π s) (hcov : IsOpenCover (nvCover s)) :
    g ≫ cubicHomOfSections hrel hcov =
      cubicHomOfSections (satisfiesCubic_pullbackFamily (g := g) hrel)
        (isOpenCover_pullbackFamily (g := g) hcov) := by
  refine (Y.openCoverOfIsOpenCover _ (isOpenCover_pullbackFamily (g := g) hcov)).hom_ext _ _
    fun (i : Fin 3) => ?_
  change (nvCover (pullbackFamily s g) i).ι ≫ g ≫ cubicHomOfSections hrel hcov =
    (nvCover (pullbackFamily s g) i).ι ≫ cubicHomOfSections _ _
  rw [ι_cubicHomOfSections, ← Category.assoc, ← Scheme.Hom.resLE_comp_ι g
    (nvCover_pullbackFamily s g i).le, Category.assoc, ι_cubicHomOfSections]
  exact comp_cubicChartHom_of_comp_chartPolyHom hrel _ i _ (chartRestrict_comp_chartPolyHom s g i)

end Pullback

/-! ### Change of the base ring -/

section MapBase

variable {S : Type u} [CommRing S] (φ : R →+* S)

/-- **The morphism of a ring map out of the coordinate ring of `C.map φ`, followed by
`projOf (C.map φ) ⟶ projOf C`, is the morphism of the composite ring map.** -/
theorem fromOfGlobalSections_comp_mapMap {Y : Scheme.{u}} (f : coordRingOf (C.map φ) →+* Γ(Y, ⊤))
    (hf : (HomogeneousIdeal.irrelevant (gradingOf (C.map φ))).toIdeal.map f = ⊤)
    (hfφ : (HomogeneousIdeal.irrelevant (gradingOf C)).toIdeal.map
      (f.comp (mapHom C φ : coordRingOf C →+* coordRingOf (C.map φ))) = ⊤) :
    Proj.fromOfGlobalSections (gradingOf (C.map φ)) f hf ≫ mapMap C φ =
      Proj.fromOfGlobalSections (gradingOf C)
        (f.comp (mapHom C φ : coordRingOf C →+* coordRingOf (C.map φ))) hfφ := by
  refine (Proj.openCoverOfMapIrrelevantEqTop (gradingOf C) _ hfφ).hom_ext _ _ fun c => ?_
  obtain ⟨d, t, h0d, hd⟩ := c
  have hφt : mapHom C φ t ∈ gradingOf (C.map φ) d := (mapHom C φ).2 hd
  change (Y.basicOpen (f (mapHom C φ t))).ι ≫ Proj.fromOfGlobalSections (gradingOf (C.map φ)) f hf ≫
      Proj.map (mapHom C φ) (irrelevant_le_map_mapHom C φ) =
    (Y.basicOpen (f (mapHom C φ t))).ι ≫ Proj.fromOfGlobalSections (gradingOf C) _ hfφ
  refine Eq.trans ?_ (ι_comp_fromOfGlobalSections (gradingOf C) _ hfφ h0d hd).symm
  rw [← Category.assoc, ι_comp_fromOfGlobalSections _ f hf h0d hφt]
  simp only [Proj.toBasicOpenOfGlobalSections, Category.assoc, Proj.basicOpenIsoSpec_inv_ι]
  rw [Proj.awayι_comp_map (hs := hd), ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  have hmem : ∀ x ∈ Submonoid.powers t,
      x ∈ Submonoid.comap (f.comp (mapHom C φ : coordRingOf C →+* coordRingOf (C.map φ)))
        (Submonoid.powers (f (mapHom C φ t))) := by
    rintro _ ⟨n, rfl⟩; exact ⟨n, by simp⟩
  have hmem' : ∀ x ∈ Submonoid.powers (mapHom C φ t),
      x ∈ Submonoid.comap f (Submonoid.powers (f (mapHom C φ t))) := by
    rintro _ ⟨n, rfl⟩; exact ⟨n, by simp⟩
  have key : ((IsLocalization.map (Localization.Away (f (mapHom C φ t))) f hmem').comp
        (algebraMap (Away (gradingOf (C.map φ)) (mapHom C φ t))
          (Localization.Away (mapHom C φ t)))).comp (Away.map (mapHom C φ) t) =
      (IsLocalization.map (Localization.Away (f (mapHom C φ t)))
        (f.comp (mapHom C φ : coordRingOf C →+* coordRingOf (C.map φ))) hmem).comp
          (algebraMap (Away (gradingOf C) t) (Localization.Away t)) := by
    refine RingHom.ext fun z => ?_
    obtain ⟨k, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (gradingOf C) hd z
    simp only [RingHom.comp_apply, HomogeneousLocalization.Away.map_mk,
      HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
      Localization.mk_eq_mk', IsLocalization.map_mk']
    congr 1
    exact Subtype.ext (by simp [map_pow])
  congr 4
  exact congrArg Spec.map (congrArg CommRingCat.ofHom key)

/-- The chart polynomial maps over `π'` and over `π = π' ≫ Spec φ` agree on polynomials over `R`. -/
private theorem chartPolyHom_comp_map_aux (π' : X ⟶ Spec (.of S))
    (hπ : π' ≫ Spec.map (CommRingCat.ofHom φ) = π) (i : Fin 3) :
    (chartPolyHom π' s i).comp (MvPolynomial.map φ) = chartPolyHom π s i := by
  have hbase : (openBase π' (nvCover s i)).comp φ = openBase π (nvCover s i) := by
    have h : CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (.of S)).inv ≫
        ((nvCover s i).ι ≫ π').appTop =
        (Scheme.ΓSpecIso (.of R)).inv ≫ ((nvCover s i).ι ≫ π).appTop := by
      rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
        ← Scheme.Hom.comp_appTop, Category.assoc, hπ]
    have h' := congrArg CommRingCat.Hom.hom h
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h'
    exact h'
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun k => ?_)
  · rw [RingHom.comp_apply, MvPolynomial.map_C, chartPolyHom, chartPolyHom,
      MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ← hbase, RingHom.comp_apply]
  · rw [RingHom.comp_apply, MvPolynomial.map_X, chartPolyHom, chartPolyHom,
      MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']

/-- **Change of the base ring.** If `X ⟶ Spec R` factors through `Spec S ⟶ Spec R`, the morphism
of the sections to the plane cubic of `C.map φ`, followed by `projOf (C.map φ) ⟶ projOf C`, is the
morphism of the same sections to the plane cubic of `C`. -/
theorem cubicHomOfSections_comp_mapMap (π' : X ⟶ Spec (.of S))
    (hπ : π' ≫ Spec.map (CommRingCat.ofHom φ) = π) (hrel : SatisfiesCubic C π s)
    (hrel' : SatisfiesCubic (C.map φ) π' s) (hcov : IsOpenCover (nvCover s)) :
    cubicHomOfSections hrel' hcov ≫ mapMap C φ = cubicHomOfSections hrel hcov := by
  refine (X.openCoverOfIsOpenCover (nvCover s) hcov).hom_ext _ _ fun (i : Fin 3) => ?_
  change (nvCover s i).ι ≫ cubicHomOfSections hrel' hcov ≫ mapMap C φ =
    (nvCover s i).ι ≫ cubicHomOfSections hrel hcov
  rw [← Category.assoc, ι_cubicHomOfSections, ι_cubicHomOfSections]
  have hring : (chartRingHom hrel' i).comp
      (mapHom C φ : coordRingOf C →+* coordRingOf (C.map φ)) = chartRingHom hrel i :=
    Ideal.Quotient.ringHom_ext (chartPolyHom_comp_map_aux φ π' hπ i)
  have hirr : (HomogeneousIdeal.irrelevant (gradingOf C)).toIdeal.map ((chartRingHom hrel' i).comp
      (mapHom C φ : coordRingOf C →+* coordRingOf (C.map φ))) = ⊤ := by
    rw [hring]; exact chartRingHom_irrelevant hrel i
  refine (fromOfGlobalSections_comp_mapMap (C := C) φ _ (chartRingHom_irrelevant hrel' i)
    hirr).trans ?_
  change Proj.fromOfGlobalSections _ _ hirr = Proj.fromOfGlobalSections _ _ _
  congr 1

/-- The chart ring maps of `C.map φ` over `π'` and of `C` over `π = π' ≫ Spec φ` agree on the
polynomials over `R`. -/
theorem chartPolyHom_comp_map (π' : X ⟶ Spec (.of S))
    (hπ : π' ≫ Spec.map (CommRingCat.ofHom φ) = π) (i : Fin 3) :
    (chartPolyHom π' s i).comp (MvPolynomial.map φ) = chartPolyHom π s i :=
  chartPolyHom_comp_map_aux φ π' hπ i

/-- The sections satisfy the cubic of `C.map φ` over `π'` as soon as they satisfy the cubic of
`C` over `π' ≫ Spec φ`. -/
theorem satisfiesCubic_map (π' : X ⟶ Spec (.of S))
    (hπ : π' ≫ Spec.map (CommRingCat.ofHom φ) = π) (hrel : SatisfiesCubic C π s) :
    SatisfiesCubic (C.map φ) π' s := fun i => by
  rw [cubicOf_map, ← RingHom.comp_apply, chartPolyHom_comp_map φ π' hπ i]
  exact hrel i

/-- **The fibre of the morphism given by the sections.** Pulled back along `Spec S ⟶ Spec R`,
the morphism `X ⟶ projOf C` becomes, through the identification of the pullback of `projOf C`
with `projOf (C.map φ)`, the morphism given by the pulled-back sections; so it is an isomorphism
as soon as that one is. -/
theorem isIso_pullbackLift_cubicHomOfSections (t : Spec (.of S) ⟶ Spec (.of R))
    (ht : Spec.map (CommRingCat.ofHom φ) = t) (hrel : SatisfiesCubic C π s)
    (hcov : IsOpenCover (nvCover s))
    [Stacks.Ample.IsInvertibleModule (Limits.pullback π t)
      ((Scheme.Modules.pullback (Limits.pullback.fst π t)).obj L)]
    (hiso : IsIso (cubicHomOfSections
      (satisfiesCubic_map φ (Limits.pullback.snd π t)
        (ht ▸ Limits.pullback.condition.symm)
        (satisfiesCubic_pullbackFamily (g := Limits.pullback.fst π t) hrel))
      (isOpenCover_pullbackFamily (g := Limits.pullback.fst π t) hcov))) :
    IsIso (Limits.pullback.lift
      (Limits.pullback.fst π t ≫ cubicHomOfSections hrel hcov)
      (Limits.pullback.snd π t)
      (by rw [Category.assoc, cubicHomOfSections_projectionOf, Limits.pullback.condition]) :
      Limits.pullback π t ⟶
        Limits.pullback (projectionOf C) t) := by
  subst ht
  set g := Limits.pullback.fst π (Spec.map (CommRingCat.ofHom φ))
  set π' := Limits.pullback.snd π (Spec.map (CommRingCat.ofHom φ))
  have hrel₁ := satisfiesCubic_pullbackFamily (g := g) hrel
  have hcov₁ := isOpenCover_pullbackFamily (g := g) hcov
  have hrel' := satisfiesCubic_map φ π' Limits.pullback.condition.symm hrel₁
  have heq : Limits.pullback.lift (g ≫ cubicHomOfSections hrel hcov) π'
      (by rw [Category.assoc, cubicHomOfSections_projectionOf, Limits.pullback.condition]) =
      cubicHomOfSections hrel' hcov₁ ≫ (isPullback_mapMap C φ).isoPullback.hom := by
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [Limits.pullback.lift_fst, Category.assoc, IsPullback.isoPullback_hom_fst,
        cubicHomOfSections_comp_mapMap φ π' Limits.pullback.condition.symm hrel₁ hrel' hcov₁,
        comp_cubicHomOfSections]
    · rw [Limits.pullback.lift_snd, Category.assoc, IsPullback.isoPullback_hom_snd,
        cubicHomOfSections_projectionOf]
  rw [heq]
  infer_instance

/-- **The morphism given by the sections is an isomorphism near a point where it is one on the
fibre.** Over a Noetherian ring, for `X` proper and flat over `Spec R`, if the morphism of the
sections pulled back to the fibre at `x` is an isomorphism, then the morphism `X ⟶ projOf C` is
an isomorphism over an open neighbourhood of `x` (Stacks 0G0Q). -/
theorem exists_isIso_overPullback_cubicHomOfSections [IsNoetherianRing R] [IsProper π] [Flat π]
    (hrel : SatisfiesCubic C π s) (hcov : IsOpenCover (nvCover s)) (x : Spec (.of R))
    [Stacks.Ample.IsInvertibleModule
      (Limits.pullback π ((Spec (.of R)).fromSpecResidueField x))
      ((Scheme.Modules.pullback (Limits.pullback.fst π
        ((Spec (.of R)).fromSpecResidueField x))).obj L)]
    (hiso : IsIso (cubicHomOfSections
      (satisfiesCubic_map (residueMapOf x) (Limits.pullback.snd π
          ((Spec (.of R)).fromSpecResidueField x))
        ((SpecMap_residueMapOf x) ▸ Limits.pullback.condition.symm)
        (satisfiesCubic_pullbackFamily (g := Limits.pullback.fst π
          ((Spec (.of R)).fromSpecResidueField x)) hrel))
      (isOpenCover_pullbackFamily (g := Limits.pullback.fst π
        ((Spec (.of R)).fromSpecResidueField x)) hcov))) :
    ∃ U : (Spec (.of R)).Opens, x ∈ U ∧
      IsIso ((Over.pullback U.ι).map (Over.homMk (U := Over.mk π) (V := Over.mk (projectionOf C))
        (cubicHomOfSections hrel hcov) (cubicHomOfSections_projectionOf hrel hcov))).left := by
  have hP : IsProper (Over.mk (projectionOf C)).hom := isProper_projectionOf C
  have hfib := isIso_pullbackLift_cubicHomOfSections (residueMapOf x)
    ((Spec (.of R)).fromSpecResidueField x) (SpecMap_residueMapOf x) hrel hcov hiso
  have : IsIso ((Over.pullback ((Spec (.of R)).fromSpecResidueField x)).map
      (Over.homMk (U := Over.mk π) (V := Over.mk (projectionOf C))
        (cubicHomOfSections hrel hcov) (cubicHomOfSections_projectionOf hrel hcov))).left := hfib
  have : IsProper (Over.mk π).hom := ‹IsProper π›
  have : Flat (Over.mk π).hom := ‹Flat π›
  exact exists_isIso_baseChange_of_isIso_fiber _ x

end MapBase

/-! ### Invariance under an isomorphism of the invertible module -/

section ModuleIso

variable {L' : X.Modules} [Stacks.Ample.IsInvertibleModule X L'] (e : L ≅ L')

/-- An isomorphism of modules preserves the nonvanishing open of a section. -/
theorem nvOpen_iso (t : Γ(L, ⊤)) : nvOpen L' (e.hom.app ⊤ t) = nvOpen L t :=
  TopologicalSpace.Opens.ext (Stacks.Ample.nonvanishingLocus_congr e t)

omit [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X L'] in
/-- An isomorphism of modules commutes with restriction of sections. -/
theorem app_resT (W : X.Opens) (t : Γ(L, ⊤)) :
    e.hom.app W (resT W t) = resT W (e.hom.app ⊤ t) :=
  PresheafOfModules.naturality_apply e.hom.val (homOfLE (le_top : W ≤ ⊤)).op t

/-- An isomorphism of modules preserves ratios of sections. -/
theorem div_iso (t a : Γ(L, ⊤)) {W : X.Opens} (hW : W ≤ nvOpen L t)
    (hW' : W ≤ nvOpen L' (e.hom.app ⊤ t)) :
    div (e.hom.app ⊤ t) hW' (resT W (e.hom.app ⊤ a)) = div t hW (resT W a) := by
  refine (eq_div _ hW' ?_).symm
  have h := congrArg (e.hom.app W) (div_smul t hW (resT W a))
  rwa [Scheme.Modules.Hom.app_smul, app_resT, app_resT] at h

variable {s' : Fin 3 → Γ(L', ⊤)} (hs : ∀ k, s' k = e.hom.app ⊤ (s k))

include hs in
/-- The transported sections have the same nonvanishing loci as the sections. -/
theorem nvCover_iso (i : Fin 3) : nvCover s' i = nvCover s i := by
  rw [nvCover, hs i, nvOpen_iso]

include hs in
/-- The ratios of the transported sections are the ratios of the sections. -/
theorem homOfLE_appTop_chartRatio_iso (i k : Fin 3) :
    (X.homOfLE (nvCover_iso e hs i).le).appTop (chartRatio s i k) = chartRatio s' i k := by
  rw [chartRatio, chartRatio, homOfLE_appTop_topIso_inv]
  congr 1
  rw [ratio, ratio, Stacks.TwistPullbackPinned.resO_div, resM_resT]
  have hs' : s' = fun k => e.hom.app ⊤ (s k) := funext hs
  subst hs'
  exact (div_iso e (s i) (s k) _ le_rfl).symm

/-- The restriction of the structure ring maps carries the chart polynomial map of the sections
to that of the transported sections. -/
private theorem homOfLE_appTop_comp_chartPolyHom_iso (i : Fin 3) :
    (X.homOfLE (nvCover_iso e hs i).le).appTop.hom.comp (chartPolyHom π s i) =
      chartPolyHom π s' i := by
  rw [chartPolyHom, chartPolyHom, MvPolynomial.comp_eval₂Hom, homOfLE_appTop_comp_openBase]
  congr 1
  funext k
  exact homOfLE_appTop_chartRatio_iso e hs i k

include hs in
/-- If the sections satisfy the cubic, so do the transported sections. -/
theorem satisfiesCubic_iso (hrel : SatisfiesCubic C π s) : SatisfiesCubic C π s' := fun i => by
  rw [← homOfLE_appTop_comp_chartPolyHom_iso e hs i, RingHom.comp_apply, hrel i, map_zero]

include hs in
/-- If the nonvanishing loci of the sections cover `X`, so do those of the transported sections.
-/
theorem isOpenCover_iso (hcov : IsOpenCover (nvCover s)) : IsOpenCover (nvCover s') := by
  have h : nvCover s' = nvCover s := funext (nvCover_iso e hs)
  rw [h]; exact hcov

include hs in
/-- **The morphism given by sections does not change under an isomorphism of the invertible
module carrying the sections to each other.** -/
theorem cubicHomOfSections_iso (hrel : SatisfiesCubic C π s) (hcov : IsOpenCover (nvCover s)) :
    cubicHomOfSections (satisfiesCubic_iso e hs hrel) (isOpenCover_iso e hs hcov) =
      cubicHomOfSections hrel hcov := by
  refine (X.openCoverOfIsOpenCover _ (isOpenCover_iso e hs hcov)).hom_ext _ _
    fun (i : Fin 3) => ?_
  change (nvCover s' i).ι ≫ _ = (nvCover s' i).ι ≫ _
  rw [ι_cubicHomOfSections, ← Scheme.homOfLE_ι X (nvCover_iso e hs i).le, Category.assoc,
    ι_cubicHomOfSections]
  exact (comp_cubicChartHom_of_comp_chartPolyHom hrel (satisfiesCubic_iso e hs hrel) i _
    (homOfLE_appTop_comp_chartPolyHom_iso e hs i)).symm

end ModuleIso

end Cubic

end AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

end
