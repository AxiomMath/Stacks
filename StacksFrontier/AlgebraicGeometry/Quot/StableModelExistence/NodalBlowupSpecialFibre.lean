module

public import StacksFrontier.AlgebraicGeometry.Quot.StableModelExistence.NodalBlowupStep
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.SpecialFibreIso.Injectivity
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SurjectivityAfterBaseChange
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.VanishingNeighbourhood
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NodalResolution

/-!
# The special fibre of a chain of blowups of a nodal family at singular points

Let `R` be a discrete valuation ring with residue field `κ`, let `f : X ⟶ Spec R` be proper and
at-worst-nodal of relative dimension one with smooth generic fibre, and let
`h : Y = X_m ⟶ ⋯ ⟶ X_0 = X` be a chain of blowups in singular closed points through
at-worst-nodal families (Stacks 0CDE, `Stacks.SemistableReduction.NodalBlowupChain`). This file
proves the step of the proof of [Stacks, Tag 0E97] about the morphisms `X_{i+1,κ} ⟶ X_{i,κ}`:
the special fibre `h_κ : Y_κ ⟶ X_κ` satisfies `𝒪_{X_κ} = h_{κ*}𝒪_{Y_κ}` and
`Rⁱh_{κ*}𝒪_{Y_κ} = 0` for `i > 0`.

## The argument

The source checks property (*) étale locally on the special fibre and leaves the computation of
the special fibre of "`X₁ ⟶ X₀`" of [Stacks, Tag 0CDC] to the reader. Here the computation is
done on the total space and then passed to the special fibre, as the source does for the
contractions of exceptional curves:

* each blowup `b : X_{i+1} ⟶ X_i` has `𝒪 = b_*𝒪` and `Rⁱb_*𝒪 = 0` for `i > 0`
  (`Stacks.SemistableReduction.isStructurallyAcyclic_blowUpToBase_of_nodalChartAt`), so the
  composite `h` has too (Leray, `AlgebraicGeometry.Scheme.Hom.IsStructurallyAcyclic.comp`);
* for a proper morphism `c : X' ⟶ X` over `R` out of a scheme flat over `R` with curves as
  fibres, structural acyclicity of `c` passes to its special fibre
  (`Stacks.SemistableReduction.isStructurallyAcyclic_specialMap_of_flat`): the fibres of `c` have
  `H¹ = 0` ([Stacks, Tag 0E7F]), so `R¹` vanishes after every base change locally
  ([Stacks, Tag 0E7G]) and `𝒪 ⟶ c_*𝒪` stays surjective ([Stacks, Tag 0E7I]); it stays
  injective because a function vanishing on the special fibre of the flat `X'` is divisible by the
  uniformizer; and the higher `Rⁱ` vanish because the fibres are curves ([Stacks, Tag 0E7D]).

## Main results

* `Stacks.SemistableReduction.mono_unitToPushforwardUnit_specialMap`.
* `Stacks.SemistableReduction.isStructurallyAcyclic_specialMap_of_flat`.
* `Stacks.SemistableReduction.NodalBlowupChain.isStructurallyAcyclic_and`: the composite of a
  chain is structurally acyclic.
* `Stacks.SemistableReduction.NodalBlowupChain.isStructurallyAcyclic_specialMap`: **its special
  fibre is structurally acyclic.**
* `Stacks.SemistableReduction.NodalBlowupChain.acyc_specialMap`: the same in degrees zero and one.

## References

* [Stacks Project, Tag 0E97](https://stacks.math.columbia.edu/tag/0E97)
* [Stacks Project, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
* [Stacks Project, Tag 0E7F](https://stacks.math.columbia.edu/tag/0E7F)
* [Stacks Project, Tag 0E7G](https://stacks.math.columbia.edu/tag/0E7G)
* [Stacks Project, Tag 0E7I](https://stacks.math.columbia.edu/tag/0E7I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.TopDegreeBaseChange Stacks.Models.SpecialFibreIso
open ContractionUniquenessComplete

universe u

namespace Stacks.SemistableReduction

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-! ### Injectivity on the special fibre -/

section Injectivity

variable {X : Scheme.{u}} (q : X ⟶ Spec (.of R)) [Flat q] {π : R} (hπ : Irreducible π)

/-- The closed point `Spec κ ⟶ Spec R` is a closed immersion: `R ⟶ κ` is surjective. -/
theorem isClosedImmersion_closedPoint : IsClosedImmersion (closedPoint R) :=
  IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective

include hπ in
omit [IsDiscreteValuationRing R] in
/-- **A uniformizer is a nonzerodivisor on every affine open of a scheme flat over `R`.** -/
theorem eq_zero_of_chartHom_mul_eq_zero_of_isAffineOpen {V : X.Opens} (hV : IsAffineOpen V)
    {b : Γ(X, V)} (hb : (Stacks.Models.chartHom q V).hom π * b = 0) : b = 0 := by
  let φ := Stacks.Models.chartHom q V
  let : Algebra R Γ(X, V) := φ.hom.toAlgebra
  have hj : hV.fromSpec ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, V))) := by
    change hV.fromSpec ≫ q = Spec.map φ
    dsimp [φ, Stacks.Models.chartHom]
    rw [Spec.map_comp]
    simpa [Scheme.isoSpec_Spec_inv, IsAffineOpen.fromSpec_top] using
      (IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top (Spec (.of R))) hV
        (by simp)).symm
  have hnzd := Stacks.Models.map_mem_nonZeroDivisors_of_flat π
    (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero) q hV.fromSpec hj
  exact (mem_nonZeroDivisors_iff_right.mp hnzd) b (by rwa [mul_comm])

omit [IsDomain R] [IsDiscreteValuationRing R] [Flat q] in
/-- The restriction of the image of `r : R` in `Γ(X, W)` to `V ⊆ W` is its image in `Γ(X, V)`. -/
theorem map_chartHom_apply {V W : X.Opens} (i : V ≤ W) (r : R) :
    X.presheaf.map (homOfLE i).op ((Stacks.Models.chartHom q W).hom r) =
      (Stacks.Models.chartHom q V).hom r :=
  congrArg (fun φ : CommRingCat.of R ⟶ Γ(X, V) ↦ φ.hom r)
    (Stacks.Models.chartHom_comp_map q (homOfLE i).op)

include hπ in
omit [IsDiscreteValuationRing R] in
/-- **A uniformizer is a nonzerodivisor on every open of a scheme flat over `R`.** -/
theorem eq_zero_of_chartHom_mul_eq_zero {W : X.Opens} {b : Γ(X, W)}
    (hb : (Stacks.Models.chartHom q W).hom π * b = 0) : b = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf W b 0 fun x hx => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
  have hVW' : V ≤ W := hVW
  have hres : X.presheaf.map (homOfLE hVW').op b = 0 := by
    refine eq_zero_of_chartHom_mul_eq_zero_of_isAffineOpen q hπ hV ?_
    rw [← map_chartHom_apply q hVW', ← map_mul, hb, map_zero]
  change X.presheaf.germ W x hx b = X.presheaf.germ W x hx 0
  rw [← X.presheaf.germ_res_apply (homOfLE hVW') x hxV b, hres, map_zero, map_zero]

include hπ in
/-- **A function on an open of a flat `R`-scheme vanishing on the special fibre is divisible by
a uniformizer.** -/
theorem exists_eq_chartHom_mul {W : X.Opens} (s : Γ(X, W))
    (hs : (pullback.fst q (closedPoint R)).app W s = 0) :
    ∃ b : Γ(X, W), s = (Stacks.Models.chartHom q W).hom π * b := by
  have hloc : ∀ V : X.affineOpens, ∀ hVW : V.1 ≤ W, ∃ b : Γ(X, V.1),
      X.presheaf.map (homOfLE hVW).op s = (Stacks.Models.chartHom q V.1).hom π * b := by
    intro V hVW
    have hker : X.presheaf.map (homOfLE hVW).op s ∈
        RingHom.ker ((pullback.fst q (closedPoint R)).app V.1).hom := by
      rw [RingHom.mem_ker]
      refine (congrArg (fun φ => φ.hom s)
        ((pullback.fst q (closedPoint R)).naturality (homOfLE hVW).op)).trans ?_
      change (pullback q (closedPoint R)).presheaf.map _
        ((pullback.fst q (closedPoint R)).app W s) = 0
      rw [hs, map_zero]
    rw [← Scheme.Hom.ker_apply] at hker
    have hker' : X.presheaf.map (homOfLE hVW).op s ∈ (pullback.fst q (Spec.map
        (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))))).ker.ideal
          ⟨V.1, V.2⟩ := hker
    rw [Stacks.Models.specialFiberIdeal_ideal_eq_span
      (AlgEquiv.refl : IsLocalRing.ResidueField R ≃ₐ[R] IsLocalRing.ResidueField R) q hπ V.1
      V.2] at hker'
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hker'
    exact ⟨a, by rw [← ha, mul_comm]⟩
  choose b hb using hloc
  let ι := {V : X.affineOpens // V.1 ≤ W}
  let U : ι → X.Opens := fun i => i.1.1
  let sf : ∀ i : ι, Γ(X, U i) := fun i => b i.1 i.2
  have hcover : W ≤ iSup U := by
    intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
  have hrestr : ∀ (i : ι) {V' : X.Opens} (h : V' ≤ U i),
      (Stacks.Models.chartHom q V').hom π * X.presheaf.map (homOfLE h).op (sf i) =
        X.presheaf.map (homOfLE (h.trans i.2)).op s := by
    intro i V' h
    rw [← map_chartHom_apply q h, ← map_mul]
    change X.presheaf.map (homOfLE h).op ((Stacks.Models.chartHom q (U i)).hom π * b i.1 i.2) = _
    rw [← hb i.1 i.2, Stacks.Blowup.presheaf_map_map]
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 U sf := by
    intro i j
    have key : X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (sf i) =
        X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (sf j) := by
      refine sub_eq_zero.mp (eq_zero_of_chartHom_mul_eq_zero q hπ ?_)
      rw [mul_sub, sub_eq_zero]
      exact (hrestr i inf_le_left).trans (hrestr j inf_le_right).symm
    exact key
  obtain ⟨g, hg, -⟩ := X.sheaf.existsUnique_gluing' U W (fun i => homOfLE i.2) hcover sf
    hcompat
  let g' : Γ(X, W) := g
  have hg' : ∀ i : ι, X.presheaf.map (homOfLE i.2).op g' = sf i := hg
  refine ⟨g', X.sheaf.eq_of_locally_eq' U W (fun i => homOfLE i.2) hcover s
    ((Stacks.Models.chartHom q W).hom π * g') fun i => ?_⟩
  change X.presheaf.map (homOfLE i.2).op s =
    X.presheaf.map (homOfLE i.2).op ((Stacks.Models.chartHom q W).hom π * g')
  rw [map_mul, map_chartHom_apply, hg' i, hb i.1 i.2]

/-- A uniformizer vanishes on the special fibre of any scheme over `Spec R`. -/
theorem chartHom_comp_app_pullbackFst_closedPoint {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of R))
    (U : Y.Opens) {π : R} (hπ : Irreducible π) :
    (pullback.fst pY (closedPoint R)).app U ((Stacks.Models.chartHom pY U).hom π) = 0 := by
  refine (congrArg (fun φ => φ.hom π)
    (Stacks.Models.chartHom_comp_app (pullback.fst pY (closedPoint R)) pY U)).trans ?_
  rw [pullback.condition, Stacks.Models.chartHom_comp_specMap, CommRingCat.hom_comp,
    RingHom.comp_apply, CommRingCat.hom_ofHom,
    (IsLocalRing.residue_eq_zero_iff π).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit),
    map_zero]

omit [Flat q] in
/-- The special fibre `c_κ : X_κ ⟶ Y_κ` lies over `c` along the inclusions of the special
fibres. -/
theorem specialMap_fst {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of R)) (c : X ⟶ Y) (hc : c ≫ pY = q) :
    specialMap q pY c hc ≫ pullback.fst pY (closedPoint R) =
      pullback.fst q (closedPoint R) ≫ c :=
  pullback.lift_fst _ _ _

include hπ in
/-- **`c_κ^♯` is injective on the sections over `U ∩ Y_κ`, for `U ⊆ Y` affine.** -/
theorem injective_app_specialMap {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of R)) (c : X ⟶ Y)
    (hc : c ≫ pY = q) (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    (U : Y.Opens) (hU : IsAffineOpen U) :
    Function.Injective ((specialMap q pY c hc).app
      (pullback.fst pY (closedPoint R) ⁻¹ᵁ U)) := by
  have := isClosedImmersion_closedPoint (R := R)
  set j := pullback.fst pY (closedPoint R)
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, rfl⟩ := j.app_surjective U hU x
  have hι : (pullback.fst q (closedPoint R)).app (c ⁻¹ᵁ U) (c.app U a) = 0 := by
    refine (congrArg (fun φ => φ.hom a)
      (Scheme.Hom.congr_app (specialMap_fst q pY c hc).symm U)).trans ?_
    change (pullback q (closedPoint R)).presheaf.map _
      ((specialMap q pY c hc).app (j ⁻¹ᵁ U) (j.app U a)) = 0
    rw [hx, map_zero]
  obtain ⟨b, hb⟩ := exists_eq_chartHom_mul q hπ (c.app U a) hι
  have hbij : Function.Bijective (c.app U) := by
    have := Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit c hO U
    exact ConcreteCategory.bijective_of_isIso _
  obtain ⟨a', rfl⟩ := hbij.2 b
  have hπ' : c.app U ((Stacks.Models.chartHom pY U).hom π) =
      (Stacks.Models.chartHom q (c ⁻¹ᵁ U)).hom π :=
    (congrArg (fun φ => φ.hom π) (Stacks.Models.chartHom_comp_app c pY U)).trans (by rw [hc])
  have ha : a = (Stacks.Models.chartHom pY U).hom π * a' := hbij.1 (by rw [map_mul, hπ', hb])
  rw [ha, map_mul, chartHom_comp_app_pullbackFst_closedPoint pY U hπ, zero_mul]

/-- **`𝒪_{Y_κ} ⟶ c_{κ*}𝒪_{X_κ}` is a monomorphism** when `X` is flat over `R` and
`𝒪_Y = c_*𝒪_X`. -/
theorem mono_unitToPushforwardUnit_specialMap {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of R))
    (c : X ⟶ Y) (hc : c ≫ pY = q)
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom)) :
    Mono (Scheme.Modules.unitToPushforwardUnit (specialMap q pY c hc)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have := isClosedImmersion_closedPoint (R := R)
  set j := pullback.fst pY (closedPoint R)
  refine SheafOfModules.mono_of_injective_app_of_cover _ fun W => ?_
  refine ⟨{U : Y.affineOpens // j ⁻¹ᵁ U.1 ≤ W}, fun i => j ⁻¹ᵁ i.1.1, fun i => homOfLE i.2,
    ?_, fun i => injective_app_specialMap q hπ pY c hc hO i.1.1 i.1.2⟩
  intro x hx
  obtain ⟨W', hW', hWW'⟩ := (j.isEmbedding.isInducing.isOpen_iff).mp W.isOpen
  have hjx : j x ∈ W' := show x ∈ j ⁻¹' W' by rwa [hWW']
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW'⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hjx hW'
  have hle : j ⁻¹ᵁ U ≤ W := fun z hz ↦ by
    have : z ∈ j ⁻¹' W' := hUW' hz
    rwa [hWW'] at this
  exact ⟨j ⁻¹ᵁ U, homOfLE hle, Sieve.ofArrows_mk (I := {U : Y.affineOpens // j ⁻¹ᵁ U.1 ≤ W})
    (fun i => j ⁻¹ᵁ i.1.1) (fun i => homOfLE i.2) ⟨⟨U, hU⟩, hle⟩, hxU⟩

end Injectivity

/-! ### Passing to the special fibre -/

section SpecialFibre

/-- The closed point `Spec κ ⟶ Spec R` sends the point of `Spec κ` to the closed point. -/
theorem closedPoint_base_apply (w : Spec (.of (IsLocalRing.ResidueField R))) :
    (closedPoint R).base w = IsLocalRing.closedPoint R := by
  have hw : w.asIdeal = ⊥ := (Ideal.eq_bot_or_top w.asIdeal).resolve_right w.isPrime.ne_top
  apply PrimeSpectrum.ext
  change Ideal.comap (IsLocalRing.residue R) w.asIdeal = IsLocalRing.maximalIdeal R
  rw [hw, ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]

/-- **The special fibre of a scheme whose fibres over `R` have dimension at most one has dimension
at most one.** -/
theorem topologicalKrullDim_pullback_closedPoint_le {X : Scheme.{u}} (q : X ⟶ Spec (.of R))
    (hq : ∀ s, topologicalKrullDim (q.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim (pullback q (closedPoint R) : Scheme.{u}) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  have := isClosedImmersion_closedPoint (R := R)
  have hsub : Set.range (pullback.fst q (closedPoint R)) ⊆
      q ⁻¹' {IsLocalRing.closedPoint R} := by
    rintro _ ⟨z, rfl⟩
    simp only [Set.mem_preimage]
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply,
      closedPoint_base_apply]
    exact Set.mem_singleton_iff.2 rfl
  exact
    (Stacks.AlgebraicGeometry.FibreDimension.topologicalKrullDim_le_of_isInducing_of_range_subset
      (pullback.fst q (closedPoint R)).isEmbedding.isInducing hsub).trans
      ((IsHomeomorph.topologicalKrullDim_eq _
        (q.fiberHomeo (IsLocalRing.closedPoint R)).isHomeomorph).symm.le.trans (hq _))

/-- **Structural acyclicity descends to the special fibre.** Let `c : X ⟶ Y` be a proper
morphism over `Spec R`, with `X` flat over `R` and all fibres of `X ⟶ Spec R` of dimension at
most one. If `𝒪_Y = c_*𝒪_X` and `Rⁱc_*𝒪_X = 0` for `i > 0`, then the special fibre
`c_κ : X_κ ⟶ Y_κ` has `𝒪_{Y_κ} = c_{κ*}𝒪_{X_κ}` and `Rⁱc_{κ*}𝒪_{X_κ} = 0` for `i > 0`.

The fibres of `c` lie in the fibres of `X ⟶ Spec R`, so have dimension at most one, and their
first cohomology vanishes ([Stacks, Tag 0E7F]). Surjectivity of `𝒪 ⟶ c_κ*𝒪` is
[Stacks, Tag 0E7I], injectivity holds as `X` is flat over `R`, `R¹c_κ*𝒪 = 0` is
[Stacks, Tag 0E7G] at every point of `Y_κ`, and the higher `Rⁱ` vanish because the fibres of `c_κ`
lie in the curve `X_κ` ([Stacks, Tag 0E7D]). -/
theorem isStructurallyAcyclic_specialMap_of_flat {X Y : Scheme.{u}} (q : X ⟶ Spec (.of R))
    (pY : Y ⟶ Spec (.of R)) (c : X ⟶ Y) (hc : c ≫ pY = q) [IsProper c] [Flat q]
    (hq : ∀ s, topologicalKrullDim (q.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hac : c.IsStructurallyAcyclic) : (specialMap q pY c hc).IsStructurallyAcyclic := by
  set j := pullback.fst pY (closedPoint R)
  set cs := specialMap q pY c hc
  have sq : IsPullback (pullback.fst q (closedPoint R)) cs c j :=
    isPullback_pullbackMap _ _ _ hc _ (by rw [Category.comp_id, hc]) (by simp)
  have hdim : ∀ y : Y, topologicalKrullDim (c.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_fiber_le_one_of_comp c pY (by rwa [hc])
  obtain ⟨hO, hR⟩ := hac
  have hfib : ∀ y : Y, IsZero (firstCohomologyStructureSheaf (c.fiber y)) := fun y =>
    isZero_firstCohomologyStructureSheaf_fiber_of_isZero_firstDirectImage c y (hdim y)
      ((isZero_firstDirectImageStructureSheaf_iff c).2 (hR 1 one_pos))
  -- `𝒪_{Y_κ} ⟶ c_κ*𝒪_{X_κ}` is an isomorphism
  have : IsIso (C := Y.Modules) (Scheme.Modules.unitToPushforwardUnit c) := hO
  have hepi : Epi (Scheme.Modules.unitToPushforwardUnit cs) := by
    rw [← sq.isoPullback_hom_snd]
    exact epi_unitToPushforwardUnit_iso_comp _ _
      (epi_unitToPushforwardUnit_of_baseChange c hdim hfib inferInstance j)
  have hmono : Mono (Scheme.Modules.unitToPushforwardUnit cs) :=
    mono_unitToPushforwardUnit_specialMap q pY c hc hO
  have hiso : IsIso (Scheme.Modules.unitToPushforwardUnit cs) := isIso_of_mono_of_epi _
  -- the special fibre is proper, with fibres of dimension at most one
  have : IsProper cs := MorphismProperty.of_isPullback sq ‹IsProper c›
  have hdims : ∀ y, topologicalKrullDim (cs.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) := fun y =>
    ((cs.fiberι y).isEmbedding.isInducing.topologicalKrullDim_le).trans
      (topologicalKrullDim_pullback_closedPoint_le q hq)
  -- `R¹c_κ*𝒪 = 0`, stalk by stalk
  have h1 : IsZero (firstDirectImageStructureSheaf cs) := by
    refine isZero_of_forall_isZero_stalk _ fun y => ?_
    obtain ⟨V, hyV, -, huniv⟩ :=
      exists_isOpen_isZero_restrict_firstDirectImage_of_isPullback_of_isZero_cohomologyOne_fiber
        c (j y) (hdim _) (hfib _)
    let W := j ⁻¹ᵁ V
    have hsq : IsPullback ((cs ⁻¹ᵁ W).ι ≫ pullback.fst q (closedPoint R)) (cs ∣_ W) c
        (W.ι ≫ j) :=
      (isPullback_morphismRestrict cs W).flip.paste_horiz sq
    have hz := huniv hsq (by rintro _ ⟨w, rfl⟩; exact w.2)
    open Stacks.AlgebraicGeometry.SchemeHigherDirectImage in
    exact isZero_stalk_of_isZero_rightDerivedPlus_restrict
      cs W y hyV _ (p := 1) zero_le_one (IsZero.of_iso hz (Functor.mapIso _
        ((Scheme.Modules.restrictFunctorIsoPullback (cs ⁻¹ᵁ W).ι).app _ ≪≫
          Scheme.Modules.pullbackUnitIso (cs ⁻¹ᵁ W).ι)))
  exact Scheme.Hom.isStructurallyAcyclic_of_isZero_rightDerived_one cs hdims hiso
    ((isZero_firstDirectImageStructureSheaf_iff cs).1 h1)

end SpecialFibre

/-! ### The chain -/

section Chain

/-- If the generic fibre of `f` is smooth, `X` is regular at every point not over the closed
point. -/
theorem base_eq_closedPoint_of_not_isRegularLocalRing {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (hf : IsAtWorstNodalOfRelativeDimensionOne f)
    (hsm : Smooth (f.fiberToSpecResidueField (⊥ : PrimeSpectrum R))) (y : X)
    (hy : ¬ IsRegularLocalRing (X.presheaf.stalk y)) :
    f.base y = IsLocalRing.closedPoint R := by
  have hlfp : LocallyOfFinitePresentation f := locallyOfFinitePresentation hf.1.1
  by_contra hne
  apply hy
  have h0 : (f.base y).asIdeal = ⊥ := by
    by_contra h0
    exact hne (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
      (Ring.DimensionLEOne.maximalOfPrime h0 (f.base y).isPrime)))
  refine isRegularLocalRing_stalk_of_smoothAt f y
    (smoothAt_of_flat_of_smoothAt_fiber f
      ((isAtWorstNodalOfRelativeDimensionOne_iff_fibres f).mp hf).1 y ?_)
  rw [← (PrimeSpectrum.ext h0 : f.base y = (⊥ : PrimeSpectrum R))] at hsm
  exact (InfinitesimalLifting.smooth_iff_forall_smoothAt _).mp hsm _

/-- **The composite of a chain of blowups at singular points is structurally acyclic**, and
every singular point of its source lies over the closed point. -/
theorem NodalBlowupChain.isStructurallyAcyclic_and {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}
    [IsProper f] (hf : IsAtWorstNodalOfRelativeDimensionOne f)
    (hgen : ∀ y : X, ¬ IsRegularLocalRing (X.presheaf.stalk y) →
      f.base y = IsLocalRing.closedPoint R)
    {Y : Scheme.{u}} {h : Y ⟶ X} (hc : NodalBlowupChain f Y h) :
    h.IsStructurallyAcyclic ∧ ∀ y : Y, ¬ IsRegularLocalRing (Y.presheaf.stalk y) →
      (h ≫ f).base y = IsLocalRing.closedPoint R := by
  have : LocallyOfFinitePresentation f := locallyOfFinitePresentation hf.1.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  induction hc with
  | refl =>
    refine ⟨Scheme.Hom.isStructurallyAcyclic_of_isIso _, fun y hy => ?_⟩
    simpa using hgen y hy
  | @step W h hh w hw hsing hnodal ih =>
    obtain ⟨hac, hgenW⟩ := ih
    have hfW : IsAtWorstNodalOfRelativeDimensionOne (h ≫ f) :=
      hh.isAtWorstNodalOfRelativeDimensionOne hf
    obtain ⟨n, ⟨ch⟩⟩ := nonempty_nodalChartAt_of_not_isRegularLocalRing (h ≫ f) hfW hgenW w hsing
    have hb := isStructurallyAcyclic_blowUpToBase_of_nodalChartAt hfW hw ch
      (ch.two_le_of_not_isRegularLocalRing hsing)
    have : IsProper h := hh.isProper
    have : LocallyOfFinitePresentation (h ≫ f) := locallyOfFinitePresentation hfW.1.1
    have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (h ≫ f)
    have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (h ≫ f)
    refine ⟨hb.comp hac, fun y hy => ?_⟩
    set b := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))
    rw [Category.assoc, Scheme.Hom.comp_apply]
    by_cases hyw : b.base y = w
    · rw [hyw]
      exact hgenW w hsing
    · exact hgenW _ (fun hreg => hy ((isRegularLocalRing_stalk_blowUp_iff_of_ne hw y hyw).2 hreg))

/-- **[Stacks, Tag 0E97], the blowups at singular points.** Let `R` be a discrete valuation
ring, `f : X ⟶ Spec R` proper and at-worst-nodal of relative dimension one with smooth generic
fibre, and `h : Y ⟶ X` a chain of blowups in singular closed points through at-worst-nodal
families (Stacks 0CDE). Then the special fibre `h_κ : Y_κ ⟶ X_κ` satisfies
`𝒪_{X_κ} = h_{κ*}𝒪_{Y_κ}` and `Rⁱh_{κ*}𝒪_{Y_κ} = 0` for every `i > 0`. -/
theorem NodalBlowupChain.isStructurallyAcyclic_specialMap {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] (hf : IsAtWorstNodalOfRelativeDimensionOne f)
    (hsm : Smooth (f.fiberToSpecResidueField (⊥ : PrimeSpectrum R))) {Y : Scheme.{u}}
    {h : Y ⟶ X} (hc : NodalBlowupChain f Y h) :
    (specialMap (h ≫ f) f h rfl).IsStructurallyAcyclic := by
  have hfY := hc.isAtWorstNodalOfRelativeDimensionOne hf
  have : Flat (h ≫ f) := ((isAtWorstNodalOfRelativeDimensionOne_iff_fibres _).mp hfY).1
  have : LocallyOfFinitePresentation f := locallyOfFinitePresentation hf.1.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsProper h := hc.isProper
  exact isStructurallyAcyclic_specialMap_of_flat (h ≫ f) f h rfl
    (topologicalKrullDim_fiber_le_one_of_isAtWorstNodal _ hfY)
    (hc.isStructurallyAcyclic_and hf (base_eq_closedPoint_of_not_isRegularLocalRing f hf hsm)).1

/-- **[Stacks, Tag 0E97], the blowups at singular points, in degrees zero and one**: for the
special fibre `h_κ : Y_κ ⟶ X_κ` of a chain of blowups `h` of a proper at-worst-nodal family with
smooth generic fibre, `𝒪_{X_κ} = h_{κ*}𝒪_{Y_κ}` and `R¹h_{κ*}𝒪_{Y_κ} = 0`. -/
theorem NodalBlowupChain.acyc_specialMap {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (hf : IsAtWorstNodalOfRelativeDimensionOne f)
    (hsm : Smooth (f.fiberToSpecResidueField (⊥ : PrimeSpectrum R))) {Y : Scheme.{u}}
    {h : Y ⟶ X} (hc : NodalBlowupChain f Y h) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit
        (specialMap (h ≫ f) f h rfl).toRingCatSheafHom) ∧
      IsZero (((Scheme.Modules.pushforward (specialMap (h ≫ f) f h rfl)).rightDerived 1).obj
        (SheafOfModules.unit (pullback (h ≫ f) (closedPoint R)).ringCatSheaf)) :=
  have hs := hc.isStructurallyAcyclic_specialMap f hf hsm
  ⟨hs.1, hs.2 1 one_pos⟩

end Chain

end Stacks.SemistableReduction

end
