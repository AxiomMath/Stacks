module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperSmoothCurveSpecialization.RestrictionBijectiveCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperSmoothCurveSpecialization.SectionKummerClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.RootOfUnityTwistOverRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveFirstCohomologyCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveFirstCohomologyPairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointsVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FinitePointsCohomology
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothSectionHenselian
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothFiberDimensionLocallyConstant
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.FamilyGenusConstant
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerSymmetricPower
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed
public import StacksFrontier.Topology.Dimension.DimensionLEOne

/-!
# Restriction of `H^*(-, ℤ/ℓ)` to the geometric fibres of a smooth proper family of curves over a
strictly henselian base

Let `R` be a strictly henselian local ring, `ℓ` a prime invertible in `R`, and
`p : Y ⟶ Spec R` proper and smooth with geometrically connected fibres of dimension at most one.
Let `i : Z_s ⟶ Y` be the geometric fibre over a geometric point over the closed point and
`h : Z_t ⟶ Y` the geometric fibre over an arbitrary geometric point. If restriction along `i` is
bijective on `H^*(-, ℤ/ℓ)` (proper base change), so is restriction along `h`.

The family is smooth of relative dimension zero or one
(`AlgebraicGeometry.smoothOfRelativeDimension_zero_or_one`). In relative dimension zero the
fibres are finite over algebraically closed fields and have no cohomology in positive degrees
([Stacks, Tag 09AY]). In relative dimension one the fibres are smooth proper curves and
`Stacks.EtaleCohomology.CurveFamily.bijective_constantExtRestriction_of_curves` applies:

* `H^q` of a curve vanishes for `q ≥ 3` and `H²` has `ℓ` elements;
* `H¹` of a curve of genus `g` has `ℓ^{2g}` elements, and the genus of the geometric fibres is
  constant (`AlgebraicGeometry.genus_eq_of_isPullback_of_smooth_of_isProper`);
* the cup product on `H¹(Z_s)` is nondegenerate;
* `p` has a section `σ` (`AlgebraicGeometry.exists_section_of_smooth_of_strictlyHenselian`), and
  the Kummer class of `𝒪_Y(σ)` in `H²(Y, μ_ℓ) = H²(Y, ℤ/ℓ)` restricts to a class of trace one on
  `Z_t` (`Stacks.EtaleCohomology.CurveFamily.smoothProperCurveTrace_pullback_kummerClass`), the
  identification `μ_ℓ = ℤ/ℓ` over `R` being compatible with restriction
  (`Stacks.EtaleCohomology.OverRing.rootsOfUnityPullbackMap_extForgetSheafH`).

## Main results

* `Stacks.EtaleCohomology.CurveFamily.bijective_constantExtRestriction_of_strictlyHenselian`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.CurveFamily

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- An integer invertible in a ring is invertible in every field-valued point of its spectrum. -/
theorem isUnit_natCast_of_spec {R K : Type u} [CommRing R] [Field K]
    (x : Spec (.of K) ⟶ Spec (.of R)) {ℓ : ℕ} (hℓ : IsUnit (ℓ : R)) : IsUnit (ℓ : K) := by
  simpa using hℓ.map (Spec.preimage x).hom

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R))

/-- The geometric fibres of a proper smooth family of relative dimension `n` with geometrically
connected fibres are proper, smooth, connected and integral. -/
private theorem isProper_and_smooth_and_isIntegral_of_isPullback [IsProper p]
    [GeometricallyConnected p] (n : ℕ) [SmoothOfRelativeDimension n p]
    {K : Type u} [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ Spec (.of R))
    {Z : Scheme.{u}} {h : Z ⟶ Y} {g : Z ⟶ Spec (.of K)} (sq : IsPullback h g p x) :
    IsProper g ∧ SmoothOfRelativeDimension n g ∧ Smooth g ∧ ConnectedSpace Z ∧ IsIntegral Z := by
  have : IsProper g := MorphismProperty.of_isPullback sq inferInstance
  have : SmoothOfRelativeDimension n g :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
    MorphismProperty.of_isPullback sq inferInstance
  have : Smooth g := SmoothOfRelativeDimension.smooth n g
  have : GeometricallyConnected g := MorphismProperty.of_isPullback sq inferInstance
  have : ConnectedSpace Z := GeometricallyConnected.connectedSpace_of_subsingleton g
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    Stacks.Chow.isIntegral_of_connectedSpace_of_smooth g⟩

/-- **The geometric fibres of a smooth proper family of relative dimension one with
geometrically connected fibres are smooth proper curves.** -/
theorem isCurve_of_isPullback [IsProper p] [GeometricallyConnected p]
    [SmoothOfRelativeDimension 1 p]
    {K : Type u} [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ Spec (.of R))
    {Z : Scheme.{u}} {h : Z ⟶ Y} {g : Z ⟶ Spec (.of K)} (sq : IsPullback h g p x) :
    IsCurve K g ∧ Smooth g ∧ IsProper g ∧ ConnectedSpace Z := by
  obtain ⟨_, _, _, _, _⟩ := isProper_and_smooth_and_isIntegral_of_isPullback p 1 x sq
  have : GeometricallyIrreducible g :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed K Z g
  exact ⟨Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one g, inferInstance, inferInstance,
    inferInstance⟩

/-- **A class of `H²(Y, ℤ/ℓ)` which survives on every geometric fibre**: the Kummer class of the
divisor of a section, read in `ℤ/ℓ` coefficients through `μ_ℓ ≅ ℤ/ℓ` over `R`, has nonzero
restriction to the geometric fibre `Z`, its trace there being one. -/
theorem exists_constantExtRestriction_two_ne_zero [StrictlyHenselianLocalRing R] [IsProper p]
    [GeometricallyConnected p] [SmoothOfRelativeDimension 1 p] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : R)) {K : Type u} [Field K] [IsAlgClosed K]
    (x : Spec (.of K) ⟶ Spec (.of R)) {Z : Scheme.{u}} {h : Z ⟶ Y} {g : Z ⟶ Spec (.of K)}
    (sq : IsPullback h g p x) :
    ∃ c : H ℓ Y 2, constantExtRestriction (ZMod ℓ) h 2 c ≠ 0 := by
  have hℓ0 : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  obtain ⟨hcurve, hsm, hpr, hconn⟩ := isCurve_of_isPullback p x sq
  -- a section
  obtain ⟨y, hy⟩ := p.surjective (IsLocalRing.closedPoint R)
  obtain ⟨σ, hσ⟩ := exists_section_of_smooth_of_strictlyHenselian R p ⟨y, hy⟩
  -- separated roots of unity
  obtain ⟨ζ, hζ, hsep⟩ :=
    Stacks.Kummer.OverRing.exists_separated_root_of_henselianLocalRing R hℓ
  let ιY := Stacks.EtaleCohomology.OverRing.etaleModuleConstantUnderlyingIso hζ hℓ0 hsep hℓ p
  let E : H ℓ Y 2 → Sheaf.H.{u + 1} (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} Y ℓ) 2 := fun e =>
    Sheaf.H.map ιY.hom 2 (extForgetSheafH (ZMod ℓ) Y _ 2 e)
  have hE : Function.Surjective E := by
    have h1 := (extForgetSheafH_bijective (ZMod ℓ) Y 2
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod ℓ) Y.smallEtaleTopology)).2
    intro z
    obtain ⟨w, hw⟩ := h1 (Sheaf.H.map ιY.inv 2 z)
    refine ⟨w, ?_⟩
    show Sheaf.H.map ιY.hom 2 (extForgetSheafH (ZMod ℓ) Y _ 2 w) = z
    rw [hw, ← Sheaf.H.map_comp_apply, ιY.inv_hom_id, Sheaf.H.map_id_apply]
  obtain ⟨e, he⟩ := hE (kummerClass p σ hσ hℓ0 hℓ)
  refine ⟨e, fun h0 => ?_⟩
  have hg : h ≫ p = (g ≫ x) ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
    rw [sq.w, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  have htw := Stacks.EtaleCohomology.OverRing.rootsOfUnityPullbackMap_extForgetSheafH hζ hℓ0
    hsep hℓ p (g ≫ x) h (RingHom.id R) 1 hg (by simp) e
  rw [h0, map_zero, map_zero, smul_zero] at htw
  change Stacks.EtaleCohomology.rootsOfUnityPullbackMap.{u, 0, u + 1} h ℓ 2 (E e) = 0 at htw
  rw [he] at htw
  have htr := smoothProperCurveTrace_pullback_kummerClass p σ hσ x sq hℓ0 hℓ
    (isUnit_natCast_of_spec x hℓ)
  have htw' : Stacks.EtaleCohomology.rootsOfUnityPullbackMap.{u, u + 1, u + 1} h ℓ 2
      (kummerClass p σ hσ hℓ0 hℓ) = 0 := htw
  rw [htw', map_zero] at htr
  exact zero_ne_one htr

/-- **The spectrum of a local ring is connected**: every point specializes to the closed point,
so the closures of the points are connected sets through a common point and cover. -/
theorem preconnectedSpace_spec_of_isLocalRing (A : Type u) [CommRing A] [IsLocalRing A] :
    PreconnectedSpace (Spec (.of A)) := by
  constructor
  have hU : (Set.univ : Set (Spec (.of A))) =
      ⋃₀ Set.range (fun y : Spec (.of A) => closure ({y} : Set (Spec (.of A)))) := by
    ext y
    simp only [Set.mem_univ, Set.sUnion_range, Set.mem_iUnion, true_iff]
    exact ⟨y, subset_closure rfl⟩
  rw [hU]
  refine isPreconnected_sUnion (IsLocalRing.closedPoint A) _ ?_ ?_
  · rintro _ ⟨y, rfl⟩
    exact specializes_iff_mem_closure.1 (IsLocalRing.specializes_closedPoint y)
  · rintro _ ⟨y, rfl⟩
    exact isPreconnected_singleton.closure

/-- **Restriction of `H^*(-, ℤ/ℓ)` to the geometric fibres of a smooth proper family of curves over
a strictly henselian base, in relative dimension one.** If restriction to the fibre `Z_s` is
bijective in every degree, so is restriction to the fibre `Z_t`. -/
theorem bijective_constantExtRestriction_of_smoothOfRelativeDimension_one
    [StrictlyHenselianLocalRing R] [IsProper p] [GeometricallyConnected p]
    [SmoothOfRelativeDimension 1 p] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : R))
    {Ks Kt : Type u} [Field Ks] [IsAlgClosed Ks] [Field Kt] [IsAlgClosed Kt]
    (xs : Spec (.of Ks) ⟶ Spec (.of R)) (xt : Spec (.of Kt) ⟶ Spec (.of R))
    {Zs Zt : Scheme.{u}} {i : Zs ⟶ Y} {gs : Zs ⟶ Spec (.of Ks)} (sqs : IsPullback i gs p xs)
    {h : Zt ⟶ Y} {gt : Zt ⟶ Spec (.of Kt)} (sqt : IsPullback h gt p xt)
    (hi : ∀ q, Function.Bijective (constantExtRestriction (ZMod ℓ) i q)) (q : ℕ) :
    Function.Bijective (constantExtRestriction (ZMod ℓ) h q) := by
  obtain ⟨hcs, hss, hps, hconns⟩ := isCurve_of_isPullback p xs sqs
  obtain ⟨hct, hst, hpt, hconnt⟩ := isCurve_of_isPullback p xt sqt
  have := preconnectedSpace_spec_of_isLocalRing R
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have hℓs := isUnit_natCast_of_spec xs hℓ
  have hℓt := isUnit_natCast_of_spec xt hℓ
  have hdiv : ∀ {K : Type u} [Field K] [IsAlgClosed K] {Z : Scheme.{u}} (g : Z ⟶ Spec (.of K))
      [IsCurve K g] [Smooth g] [IsProper g], IsUnit (ℓ : K) → ∀ L : Stacks.Picard.ofScheme Z,
        Stacks.Picard.picardDegree g (IsCurve.topologicalKrullDim_eq_one (f := g)).le L = 0 →
          ∃ M : Stacks.Picard.ofScheme Z, ℓ • M = L :=
    fun g _ _ _ hu L hL => Stacks.Picard.exists_nsmul_eq_of_picardDegree_eq_zero g _ hu L hL
  have hs1 := Stacks.Kummer.natCard_ext_one_constantModuleSheaf_of_smoothProperCurve gs hℓs
  have ht1 := Stacks.Kummer.natCard_ext_one_constantModuleSheaf_of_smoothProperCurve gt hℓt
  have : Finite (H ℓ Zs 1) := Nat.finite_of_card_ne_zero (by
    show Nat.card (H ℓ Zs 1) ≠ 0
    rw [show Nat.card (H ℓ Zs 1) = ℓ ^ (2 * genus gs) from hs1]
    exact pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)
  have hgenus : genus gs = genus gt :=
    genus_eq_of_isPullback_of_smooth_of_isProper p xs xt i gs sqs h gt sqt
      (IsCurve.topologicalKrullDim_eq_one (f := gs)).le
      (IsCurve.topologicalKrullDim_eq_one (f := gt)).le
  exact bijective_constantExtRestriction_of_curves hi
    (Stacks.Kummer.subsingleton_ext_constantModuleSheaf_of_smoothCurve gs hℓs)
    (Stacks.Kummer.subsingleton_ext_constantModuleSheaf_of_smoothCurve gt hℓt)
    (Stacks.Kummer.natCard_ext_two_constantModuleSheaf_of_smoothProperCurve gs hℓs
      (hdiv gs hℓs))
    (Stacks.Kummer.natCard_ext_two_constantModuleSheaf_of_smoothProperCurve gt hℓt
      (hdiv gt hℓt))
    (exists_constantExtRestriction_two_ne_zero p hℓ xt sqt)
    (by
      show Nat.card (H ℓ Zs 1) = Nat.card (H ℓ Zt 1)
      rw [show Nat.card (H ℓ Zs 1) = ℓ ^ (2 * genus gs) from hs1,
        show Nat.card (H ℓ Zt 1) = ℓ ^ (2 * genus gt) from ht1, hgenus])
    (Stacks.EtaleCohomology.ExtensionTorsor.exists_comp_ne_zero_of_ne_zero gs hℓs)
    q

/-- **The geometric fibres of a smooth proper family of relative dimension zero with geometrically
connected fibres have no cohomology in positive degrees**: such a fibre is a finite scheme over an
algebraically closed field ([Stacks, Tag 09AY]). -/
theorem connectedSpace_and_subsingleton_of_smoothOfRelativeDimension_zero [IsProper p]
    [GeometricallyConnected p] [SmoothOfRelativeDimension 0 p] {ℓ : ℕ} [Fact ℓ.Prime]
    {K : Type u} [Field K] [IsAlgClosed K] (x : Spec (.of K) ⟶ Spec (.of R))
    {Z : Scheme.{u}} {h : Z ⟶ Y} {g : Z ⟶ Spec (.of K)} (sq : IsPullback h g p x) :
    ConnectedSpace Z ∧ ∀ q, 0 < q → Subsingleton (H ℓ Z q) := by
  obtain ⟨_, _, _, _, _⟩ := isProper_and_smooth_and_isIntegral_of_isPullback p 0 x sq
  have hdim : topologicalKrullDim Z = 0 := by
    exact_mod_cast topologicalKrullDim_eq_of_smoothOfRelativeDimension g 0
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType g
  have : Finite Z := Set.finite_univ_iff.1
    (Stacks.Topology.Dimension.finite_of_topologicalKrullDim_le_zero hdim.le)
  obtain ⟨hA, hcl, hsep⟩ :=
    Stacks.EtaleCohomology.isAffine_and_isClosed_and_isSepClosed_of_finite g
  refine ⟨inferInstance, fun q hq => ?_⟩
  have h09AY := AlgebraicGeometry.subsingleton_etaleCohomology_of_closed_points' Z hcl hsep
    ((etaleModuleUnderlyingAbelian Z (ZMod ℓ)).obj
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod ℓ) Z.smallEtaleTopology)) q hq
  exact (Equiv.ofBijective _ (extForgetSheafH_bijective (ZMod ℓ) Z q
    (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod ℓ)
      Z.smallEtaleTopology))).subsingleton

/-- **Restriction of `H^*(-, ℤ/ℓ)` to the geometric fibres of a smooth proper family over a
strictly henselian base.** Let `p : Y ⟶ Spec R` be proper and smooth with geometrically connected
fibres, the closed fibre of dimension at most one, `ℓ` a prime invertible in `R`, and `Z_s`,
`Z_t` the geometric fibres over two geometric points of `Spec R`. If restriction to `Z_s` is
bijective in every degree, so is restriction to `Z_t`. -/
theorem bijective_constantExtRestriction_of_strictlyHenselian
    [StrictlyHenselianLocalRing R] [IsProper p] [Smooth p] [GeometricallyConnected p]
    (hd : topologicalKrullDim (p.fiber (IsLocalRing.closedPoint R)) ≤ 1)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : R))
    {Ks Kt : Type u} [Field Ks] [IsAlgClosed Ks] [Field Kt] [IsAlgClosed Kt]
    (xs : Spec (.of Ks) ⟶ Spec (.of R)) (xt : Spec (.of Kt) ⟶ Spec (.of R))
    {Zs Zt : Scheme.{u}} {i : Zs ⟶ Y} {gs : Zs ⟶ Spec (.of Ks)} (sqs : IsPullback i gs p xs)
    {h : Zt ⟶ Y} {gt : Zt ⟶ Spec (.of Kt)} (sqt : IsPullback h gt p xt)
    (hi : ∀ q, Function.Bijective (constantExtRestriction (ZMod ℓ) i q)) (q : ℕ) :
    Function.Bijective (constantExtRestriction (ZMod ℓ) h q) := by
  rcases smoothOfRelativeDimension_zero_or_one p hd with h0 | h1
  · obtain ⟨hcs, hss⟩ := connectedSpace_and_subsingleton_of_smoothOfRelativeDimension_zero
      (ℓ := ℓ) p xs sqs
    obtain ⟨hct, hst⟩ := connectedSpace_and_subsingleton_of_smoothOfRelativeDimension_zero
      (ℓ := ℓ) p xt sqt
    exact bijective_constantExtRestriction_of_points hi hss hst q
  · exact bijective_constantExtRestriction_of_smoothOfRelativeDimension_one p hℓ xs xt sqs sqt hi q

end Stacks.EtaleCohomology.CurveFamily

end
