module

public import StacksFrontier.AlgebraicGeometry.PicardFibreTrivial.ThickeningLift
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkFormalFunctionsFrom02O8
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PrincipalPowerSubscheme
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatEquivalence
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CohomologyPresheafComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces

/-!
# Lifting a section from the closed fibre of a proper scheme over a Noetherian ring

Let `R` be a Noetherian ring, `g : X ⟶ Spec R` a proper morphism, `𝔪 ⊆ R` an ideal and
`i : Z ⟶ X` the closed immersion cut out by `𝔪 𝒪_X`. Assume `Z` has dimension at most one. For
a coherent `𝒪_X`-module `ℱ` with `H¹(Z, i^* ℱ) = 0`, every section of `i^* ℱ` over `Z` is the
restriction of a section of `ℱ` over `X`.

This is the step of the proof of [Stacks, Tag 0E24] which uses the theorem on formal functions:
by [Stacks, Tag 02OB] the images of `H⁰(X, ℱ / 𝔪 ᵏ ℱ)` and of `H⁰(X, ℱ)` in
`H⁰(X, ℱ / 𝔪 ℱ) = H⁰(Z, i^* ℱ)` agree for `k` large, and the first map is onto by
`Stacks.PicardFibreTrivial.surjective_rightDerived_zero_map_idealPowerQuotientDrop`. Its two
cohomological inputs are supplied here: `ℱ / 𝔪 ℱ` and `ℱ / 𝔪 ᵏ ℱ` are direct images from the
closed subschemes `Z` and `Z_k = X ×_{Spec R} Spec (R/𝔪 ᵏ)` by [Stacks, Tag 0EL1], cohomology
does not change along a closed immersion, and `Z_k` has the underlying space of `Z`, so it has
dimension at most one and its cohomology vanishes above degree one ([Stacks, Tag 02UZ]).

## Main results

* `Stacks.PicardFibreTrivial.isZero_coh_of_topologicalKrullDim_le`: Grothendieck vanishing on
  a Noetherian scheme, in the spelling of the theorem on formal functions.
* `Stacks.PicardFibreTrivial.surjective_unit_app_top_of_isProper`: the lifting statement.

## References

* [Stacks Project, Tag 0E24](https://stacks.math.columbia.edu/tag/0E24)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Algebraization Stacks.Cohomology.FormalFunctions

universe u

namespace Stacks.PicardFibreTrivial

/-- **Grothendieck vanishing on a Noetherian scheme** ([Stacks, Tag 02UZ]): the cohomology of
every module vanishes in degrees above the dimension. -/
theorem isZero_coh_of_topologicalKrullDim_le (W : Scheme.{u}) [IsNoetherian W] {d i : ℕ}
    (hdim : topologicalKrullDim W ≤ (d : WithBot ℕ∞)) (hi : d < i) (G : W.Modules) :
    IsZero ((coh W i).obj G) := by
  have hsub := (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top
    ((SheafOfModules.toSheaf W.ringCatSheaf).obj G) i).mp
    (Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le
      hdim hi _)
  have h :=
    (Stacks.Cohomology.ModuleComparison.isZero_rightDerivedSections_iff_isZero_cohomologyPresheaf
    (J := Opens.grothendieckTopology (W : Type u)) (R := W.ringCatSheaf)
    (U := (⊤ : Opens (W : Type u))) (n := i) (F := G)).mpr
    (@AddCommGrpCat.isZero_of_subsingleton _ hsub)
  exact ModuleCat.isZero_iff_subsingleton.mpr (AddCommGrpCat.subsingleton_of_isZero
    (h.of_iso ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
      W.ringCatSheaf ⊤ i).app G)))


attribute [local instance] Abelian.hasFiniteBiproducts

section Annihilation

variable {X Z : Scheme.{u}}

/-- **A global function vanishing on `Z` acts by zero on every direct image from `Z`.** -/
theorem globalSmul_pushforward_eq_zero (i : Z ⟶ X) (G : Z.Modules) (c : Γ(X, ⊤))
    (hc : i.appTop c = 0) : globalSmul c ((Scheme.Modules.pushforward i).obj G) = 0 := by
  ext U x
  rw [globalSmul_app]
  have h : i.app U (restrictTop c U) = 0 := by
    have hn := ConcreteCategory.congr_hom (i.naturality (homOfLE (le_top : U ≤ ⊤)).op) c
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hn
    change (i.app U) (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op c) = 0
    rw [hn]
    change (Z.presheaf.map _) (i.appTop c) = 0
    rw [hc, map_zero]
  change ((i.app U (restrictTop c U)) • (show Γ(G, i ⁻¹ᵁ U) from x) : Γ(G, i ⁻¹ᵁ U)) = 0
  rw [h, zero_smul]

/-- Acting by zero transports along an isomorphism. -/
theorem globalSmul_eq_zero_of_iso {M N : X.Modules} (e : M ≅ N) (c : Γ(X, ⊤))
    (h : globalSmul c N = 0) : globalSmul c M = 0 := by
  have hc := comp_globalSmul c e.hom
  rw [h, comp_zero] at hc
  rw [← cancel_mono e.hom, ← hc, zero_comp]

/-- **A submodule of a direct image along a closed immersion is annihilated by the ideal of
the closed subscheme**, section by section. -/
theorem smul_eq_zero_of_mono (i : Z ⟶ X) [IsClosedImmersion i] (M : X.Modules) (G : Z.Modules)
    (e : (Scheme.Modules.pushforward i).obj G ≅ M) (K : X.Modules) (ι : K ⟶ M) [Mono ι]
    (U : X.Opens) (b : Γ(X, U)) (hb : (i.app U).hom b = 0) (t : Γ(K, U)) : b • t = 0 := by
  have hM := (Stacks.ClosedImmersion.pushforward_essImage_iff i M).1 ⟨G, ⟨e⟩⟩
  have : Mono (C := _root_.SheafOfModules X.ringCatSheaf) ι := ‹Mono ι›
  refine Stacks.SheafOfModules.injective_val_app_of_mono (R := X.ringCatSheaf) ι (op U) ?_
  change ι.app U (b • t) = ι.app U 0
  rw [Scheme.Modules.Hom.app_smul, map_zero, hM U b hb]

/-- **Cohomology of a direct image along a closed immersion is that of the module upstairs**,
as far as vanishing goes. -/
theorem isZero_coh_pushforward_iff (i : Z ⟶ X) [IsClosedImmersion i] (G : Z.Modules) (p : ℕ) :
    IsZero ((coh X p).obj ((Scheme.Modules.pushforward i).obj G)) ↔ IsZero ((coh Z p).obj G) := by
  refine (Iso.isZero_iff
    (Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward i G p)).trans ?_
  simp only [ModuleCat.isZero_iff_subsingleton]
  rfl

/-- **`H²` vanishes on a submodule of a direct image from a Noetherian closed subscheme of
dimension at most one.** -/
theorem isZero_coh_two_of_mono (j : Z ⟶ X) [IsClosedImmersion j] [IsNoetherian Z]
    (hZ : topologicalKrullDim Z ≤ 1) (M : X.Modules) (G : Z.Modules)
    (e : (Scheme.Modules.pushforward j).obj G ≅ M) (K : X.Modules)
    (ι : K ⟶ M) [Mono ι] : IsZero ((coh X 2).obj K) := by
  have : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app K) :=
    Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero j K fun U b hb t =>
      smul_eq_zero_of_mono j M G e K ι U b hb t
  refine (Iso.isZero_iff ((coh X 2).mapIso
    (asIso ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app K)))).2 ?_
  exact (isZero_coh_pushforward_iff j _ 2).2
    (isZero_coh_of_topologicalKrullDim_le Z (d := 1) (by exact_mod_cast hZ) (by omega) _)

end Annihilation

section Lift

variable (R : Type u) [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (.of R))

/-- **A global function coming from an ideal `J` of the base vanishes on every scheme over
`X` whose map to `Spec R` factors through `Spec (R/J)`.** -/
theorem appTop_baseRingHom_eq_zero (J : Ideal R) {W : Scheme.{u}} (h : W ⟶ X)
    (w : W ⟶ Spec (.of (R ⧸ J)))
    (hw : h ≫ g = w ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) {x : R}
    (hx : x ∈ J) : h.appTop (baseRingHom R g x) = 0 := by
  have key : (Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop ≫ h.appTop =
      CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ (Scheme.ΓSpecIso (.of (R ⧸ J))).inv ≫
        w.appTop := by
    rw [← Scheme.Hom.comp_appTop, hw, Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  calc h.appTop (baseRingHom R g x)
      = ((Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop ≫ h.appTop) x := rfl
    _ = (CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ (Scheme.ΓSpecIso (.of (R ⧸ J))).inv ≫
          w.appTop) x := by rw [key]
    _ = 0 := by
      rw [CommRingCat.comp_apply]
      change ((Scheme.ΓSpecIso (.of (R ⧸ J))).inv ≫ w.appTop) (Ideal.Quotient.mk J x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]

variable [IsNoetherianRing R] [IsProper g]

/-- **A section of the restriction of a coherent module to the closed fibre lifts.** Let
`g : X ⟶ Spec R` be proper with `R` Noetherian, `𝔪 ⊆ R` an ideal and `i : Z ⟶ X` a closed
immersion with ideal sheaf `𝔪 𝒪_X`, with `Z` of dimension at most one. For a coherent
`𝒪_X`-module `ℱ` with `H¹(Z, i^* ℱ) = 0`, every section of `i^* ℱ` over `Z` is the image of a
section of `ℱ` over `X` under the unit of the adjunction `i^* ⊣ i_*`. -/
theorem surjective_unit_app_top_of_isProper (m : Ideal R) (F : X.Modules) [F.IsQuasicoherent]
    (hF : Stacks.SheafOfModules.IsCoherent F) {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (hi : i.ker = baseIdealSheaf R m g)
    (hi0 : ∀ x ∈ m, i.appTop (baseRingHom R g x) = 0)
    (hZ : topologicalKrullDim Z ≤ 1)
    (hH1 : IsZero ((coh Z 1).obj ((Scheme.Modules.pullback i).obj F))) :
    Function.Surjective (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F).app ⊤) := by
  classical
  set 𝓘 := baseIdealSheaf R m g with h𝓘
  -- Generators of `𝔪`.
  obtain ⟨r, gens, hgens⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (IsNoetherian.noetherian m)
  let a : Fin r → Γ(X, ⊤) := fun l => baseRingHom R g (gens l)
  have hJ : Ideal.span (Set.range a) = baseIdeal R m g := by
    rw [baseIdeal, ← hgens, Ideal.map_span, ← Set.range_comp]
    rfl
  have hgen : ∀ U : X.affineOpens,
      𝓘.ideal U ≤ Ideal.span (Set.range fun l => restrictTop (a l) U.1) := by
    intro U
    rw [h𝓘, baseIdealSheaf_ideal, ← hJ, Ideal.map_span, ← Set.range_comp]
    rfl
  -- The bound of [Stacks, Tag 02OB].
  obtain ⟨c, -, -, hrange⟩ := exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8 R g
    inferInstance m F hF 0 Stacks.FormalFunctions.isReesFinite_cohomologyIdealPowerSystem
  set k := 1 + c
  have hk : 1 ≤ k := Nat.le_add_right 1 c
  -- The thickening `Z_k = X ×_{Spec R} Spec (R/𝔪 ᵏ)`.
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (m ^ k)))
  have : IsClosedImmersion q := IsClosedImmersion.spec_of_quotient_mk (R := .of R) (m ^ k)
  let j := pullback.fst g q
  have hj : j.ker = 𝓘 ^ k := by
    rw [h𝓘, ← baseIdealSheaf_pow,
      Stacks.PuncturedSpectrumPicard.baseIdealSheaf_eq_ker_pullback_fst]
  have hj0 : ∀ x ∈ m ^ k, j.appTop (baseRingHom R g x) = 0 := fun x hx =>
    appTop_baseRingHom_eq_zero R g (m ^ k) j (pullback.snd g q) pullback.condition hx
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
  have : IsLocallyNoetherian (pullback g q) := isLocallyNoetherian_of_isClosedImmersion j
  have : CompactSpace ↑(pullback g q : Scheme.{u}) := QuasiCompact.compactSpace_of_compactSpace j
  have : IsNoetherian (pullback g q) := {}
  have hrng : Set.range j = Set.range i := by
    rw [← j.isClosedEmbedding.isClosed_range.closure_eq,
      ← i.isClosedEmbedding.isClosed_range.closure_eq, ← Scheme.Hom.support_ker,
      ← Scheme.Hom.support_ker, hj, hi, Scheme.IdealSheafData.support_pow _ _ (by omega)]
  have hdimk : topologicalKrullDim ↑(pullback g q : Scheme.{u}) ≤ 1 := by
    rw [IsHomeomorph.topologicalKrullDim_eq _
        j.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph, hrng,
      ← IsHomeomorph.topologicalKrullDim_eq _
        i.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph]
    exact hZ
  -- The two quotients as direct images, [Stacks, Tag 0EL1].
  have hi1 : i.ker = 𝓘 ^ 1 := by rw [pow_one, hi]
  let eQk := (idealQuotientPushforwardIso 𝓘 k F j hj).symm
  let eQ1 := (idealQuotientPushforwardIso 𝓘 1 F i hi1).symm
  -- A function vanishing on a closed subscheme `V(𝓘 ^ n)` kills the quotient `ℱ / 𝓘 ⁿ ℱ`.
  have hz : ∀ (n : ℕ) {W : Scheme.{u}} (v : W ⟶ X) [IsClosedImmersion v] (hv : v.ker = 𝓘 ^ n)
      (x : Γ(X, ⊤)), v.appTop x = 0 → globalSmul x (idealPowerQuotient 𝓘 n F) = 0 :=
    fun n W v _ hv x hx => globalSmul_eq_zero_of_iso (idealQuotientPushforwardIso 𝓘 n F v hv) x
      (globalSmul_pushforward_eq_zero v _ x hx)
  have hkill : ∀ x ∈ Ideal.span (Set.range a) ^ k,
      globalSmul x (idealPowerQuotient 𝓘 k F) = 0 := by
    intro x hx
    rw [hJ, ← baseIdeal_pow] at hx
    exact hz k j hj x ((Ideal.map_le_iff_le_comap (K := RingHom.ker j.appTop.hom)).2 hj0 hx)
  have h2 : ∀ (K : X.Modules) (ι : K ⟶ ⨁ fun _ : Fin r => idealPowerQuotient 𝓘 k F), Mono ι →
      IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived 2).obj K) := by
    intro K ι _
    exact isZero_coh_two_of_mono j hdimk _ (⨁ fun _ : Fin r => (Scheme.Modules.pullback j).obj F)
      ((Scheme.Modules.pushforward j).mapBiproduct _ ≪≫ biproduct.mapIso fun _ => eQk) K ι
  have h1 : IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived 1).obj
      (idealPowerQuotient 𝓘 1 F)) :=
    ((isZero_coh_pushforward_iff i _ 1).2 hH1).of_iso ((coh X 1).mapIso eQ1).symm
  have hsurj0 := surjective_rightDerived_zero_map_idealPowerQuotientDrop 𝓘 F a hgen
    (fun l => hz 1 i hi1 _ (hi0 _ (hgens ▸ Submodule.subset_span ⟨l, rfl⟩))) hk hkill h2 h1
  -- With [Stacks, Tag 02OB], `H⁰(X, ℱ) ⟶ H⁰(X, ℱ / 𝔪 ℱ)` is onto.
  have hπ0 : Function.Surjective
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived 0).map
        (quotπ 𝓘 F 1)).hom := by
    intro y
    have hy : y ∈ LinearMap.range _ := hsurj0 y
    rwa [hrange 1 k le_rfl] at hy
  -- On global sections.
  have hπ : Function.Surjective ((quotπ 𝓘 F 1).app ⊤) := by
    intro t
    let e0 := Stacks.Cohomology.FormalFunctions.moduleGlobalSectionsRightDerivedZeroIso X
    obtain ⟨z, hz⟩ := hπ0 ((e0.inv.app _).hom t)
    refine ⟨(e0.hom.app F).hom z, ?_⟩
    have hn : (e0.hom.app _).hom
          ((((AlgebraicGeometry.moduleGlobalSections X).rightDerived 0).map (quotπ 𝓘 F 1)).hom z) =
        (quotπ 𝓘 F 1).app ⊤ ((e0.hom.app F).hom z) :=
      ConcreteCategory.congr_hom (e0.hom.naturality (quotπ 𝓘 F 1)) z
    have hinv : (e0.hom.app _).hom ((e0.inv.app _).hom t) = t :=
      ConcreteCategory.congr_hom (e0.inv_hom_id_app (idealPowerQuotient 𝓘 1 F)) t
    exact hn.symm.trans ((congrArg (e0.hom.app _).hom hz).trans hinv)
  -- Through [Stacks, Tag 0EL1], this is the restriction to `Z`.
  have := isIso_idealQuotientPushforwardMap 𝓘 1 F i hi1
  intro e
  obtain ⟨s, hs⟩ := hπ ((inv (idealQuotientPushforwardMap 𝓘 1 F i hi1)).app ⊤ e)
  refine ⟨s, ?_⟩
  rw [← idealQuotientPushforwardMap_π 𝓘 1 F i hi1, comp_app_apply, hs, ← comp_app_apply,
    IsIso.inv_hom_id]
  rfl

end Lift

end Stacks.PicardFibreTrivial

end
