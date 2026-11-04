module

public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.BaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.Substitution
public import StacksFrontier.AlgebraicGeometry.StalkwiseGeneration.Pullback
public import StacksFrontier.AlgebraicGeometry.VanishingSystemImmersion.ChartProjection
public import StacksFrontier.AlgebraicGeometry.VanishingSystemImmersion.Restriction
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingLinearSystem

/-!
# The linear system of sections vanishing on a closed subscheme, on the complement

This file continues `StacksFrontier/AlgebraicGeometry/Variety/Bertini/VanishingLinearSystem.lean`
with the morphism the source of [Stacks, Tag 0FD5] speaks about: the canonical morphism of
[Stacks, Tag 0FCY] attached to the linear system `V_n` *restricted to the open complement*
`X ∖ Z`, where it generates.

## Main definitions

* `Stacks.SectionsVanishingOnSubscheme.restrictedPow`: `ℒ ^⊗ n` pulled back to `X ∖ Z`.
* `Stacks.SectionsVanishingOnSubscheme.restrictSection`: the restriction of a global section.

## Main results

* `Stacks.SectionsVanishingOnSubscheme.toProjectiveSpaceOfVanishingSections_eq`: **the morphism
  `Stacks.SectionsVanishingOnSubscheme.toProjectiveSpaceOfVanishingSections` of a basis of `V_n`
  is the canonical morphism `X ∖ Z ⟶ P(V_n)` of [Stacks, Tag 0FCY]**, namely
  `AlgebraicGeometry.toProjectiveSpaceOfModule` applied to the restricted linear system. The
  morphism the tag speaks about and the one the development glues are one morphism.
* `Stacks.SectionsVanishingOnSubscheme.isImmersion_toProjectiveSpaceOfVanishingSections`: the
  immersion clause of [Stacks, Tag 0FD5] at one degree.

## References

* [Stacks Project, Tag 0FD5](https://stacks.math.columbia.edu/tag/0FD5)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
open TopologicalSpace
open Stacks.Ample Stacks.ProjectiveFromSections

universe u

namespace Stacks.SectionsVanishingOnSubscheme

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive
attribute [local instance] Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj

/-! ### The restriction of the situation to the open complement -/

section Restrict

variable (k : Type u) [CommRing k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (I : X.IdealSheafData) {L : X.Modules} [IsInvertibleModule X L] {m : ℤ} {N : ℕ}

/-- `ℒ ^⊗ n` pulled back to the open complement `X ∖ Z`. -/
abbrev restrictedPow : (openComplement I).toScheme.Modules :=
  (Scheme.Modules.pullback (openComplement I).ι).obj (tensorPowModule X L m)

/-- The restriction to `X ∖ Z` of a global section of `ℒ ^⊗ n`. -/
abbrev restrictSection (s : Γ(tensorPowModule X L m, ⊤)) :
    Γ(restrictedPow I (L := L) (m := m), ⊤) :=
  pullbackGlobalSections (openComplement I).ι (tensorPowModule X L m) s

/-- **The nonvanishing open of a restricted section is the part of the nonvanishing open inside
`X ∖ Z`.** -/
theorem nvOpen_restrictSection (s : Γ(tensorPowModule X L m, ⊤)) :
    nvOpen (restrictedPow I (L := L) (m := m)) (restrictSection I s) =
      (openComplement I).ι ⁻¹ᵁ nvOpen (tensorPowModule X L m) s :=
  Stacks.RatioPullback.nvOpen_pullbackGlobalSections _ _ s

/-- A family of sections generates the restricted family if each point of `X ∖ Z` lies in the
nonvanishing open of a member. -/
private theorem generatesStalks_restrictSection {n : ℕ}
    (t : Fin (n + 1) → Γ(tensorPowModule X L m, ⊤))
    (h : ∀ x : (openComplement I).toScheme, ∃ i, (openComplement I).ι.base x ∈ nvCover t i) :
    GeneratesStalks (fun i => restrictSection I (t i)) := by
  refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ?_
  obtain ⟨i, hi⟩ := h x
  exact ⟨i, (nvOpen_restrictSection I (t i)).ge hi⟩

/-- The ratios of a family, restricted along `X ∖ Z`, are the ratios of the restricted family. -/
private theorem appLE_ratio_restrictSection {n : ℕ}
    (t : Fin (n + 1) → Γ(tensorPowModule X L m, ⊤)) (i j : Fin (n + 1))
    (hpre : nvCover (fun β => restrictSection I (t β)) i ≤ (openComplement I).ι ⁻¹ᵁ nvCover t i) :
    (openComplement I).ι.appLE (nvCover t i) (nvCover (fun β => restrictSection I (t β)) i) hpre
        (ratio t i j) = ratio (fun β => restrictSection I (t β)) i j := by
  have h := Stacks.RatioPullback.resO_ratio_pullbackGlobalSections (openComplement I).ι
    (tensorPowModule X L m) t i j (le_refl _) hpre
  rw [Stacks.ChartImmersionFinish.resO_self] at h
  exact h.symm

/-- A member of a basis of `V_n`, restricted to `X ∖ Z`. -/
def restrictedBasisSection (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L m))
    (i : Fin (N + 1)) : Γ(restrictedPow I (L := L) (m := m), ⊤) :=
  restrictSection I (basisSection k f b i)

/-- **The chart of `X ∖ Z` on which the `i`-th member of a basis of `V_n` does not vanish is the
nonvanishing open of the restricted basis section.** -/
theorem nvCover_restrictedBasisSection
    (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L m)) (i : Fin (N + 1)) :
    nvCover (restrictedBasisSection k f I b) i =
      chartOpen (basisSection k f b) (openComplement I) i :=
  nvOpen_restrictSection I (basisSection k f b i)

/-- **A basis of `V_n` restricted to `X ∖ Z` generates `ℒ ^⊗ n|_{X ∖ Z}`**, as soon as `V_n`
generates `ℒ ^⊗ n` off the closed subscheme. -/
theorem generatesStalks_restrictedBasisSection
    (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L m))
    (h : GeneratesOffSupport k f I L m) :
    GeneratesStalks (restrictedBasisSection k f I b) := by
  exact generatesStalks_restrictSection I (basisSection k f b) fun x =>
    exists_mem_nvCover_basisSection k f b h
      (show ((openComplement I).ι.base x : X) ∈ openComplement I from x.2)

/-- **The ratios of a basis of `V_n`, read on the `i`-th chart of `X ∖ Z`, are the ratios of the
restricted basis sections.** The comparison morphism from the chart to `X_{bᵢ}` is the restriction
`Scheme.Hom.resLE` of the inclusion of `X ∖ Z`, which acts on sections of the structure sheaf by
`AlgebraicGeometry.Scheme.Hom.appLE`, and the ratio commutes with pullback
(`Stacks.RatioPullback.resO_ratio_pullbackGlobalSections`). -/
theorem appTop_homOfLE_chartSection
    (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L m)) (i j : Fin (N + 1)) :
    ((openComplement I).toScheme.homOfLE
          (nvCover_restrictedBasisSection k f I b i).le).appTop
        (chartSection (basisSection k f b) (openComplement I) i j) =
      chartRatio (restrictedBasisSection k f I b) i j := by
  have hpre : nvCover (restrictedBasisSection k f I b) i ≤
      (openComplement I).ι ⁻¹ᵁ nvCover (basisSection k f b) i :=
    (nvCover_restrictedBasisSection k f I b i).le
  have hφ : (openComplement I).toScheme.homOfLE
        (nvCover_restrictedBasisSection k f I b i).le ≫
        chartMap (basisSection k f b) (openComplement I) i =
      (openComplement I).ι.resLE (nvCover (basisSection k f b) i)
        (nvCover (restrictedBasisSection k f I b) i) hpre := by
    rw [← cancel_mono (nvCover (basisSection k f b) i).ι, Scheme.Hom.resLE_comp_ι,
      Category.assoc, chartMap_ι, ← Category.assoc, Scheme.homOfLE_ι]
  have hratio : (openComplement I).ι.appLE (nvCover (basisSection k f b) i)
        (nvCover (restrictedBasisSection k f I b) i) hpre (ratio (basisSection k f b) i j) =
      ratio (restrictedBasisSection k f I b) i j := by
    exact appLE_ratio_restrictSection I (basisSection k f b) i j hpre
  have hres : ((openComplement I).ι.resLE (nvCover (basisSection k f b) i)
        (nvCover (restrictedBasisSection k f I b) i) hpre).appTop
        (chartRatio (basisSection k f b) i j) =
      chartRatio (restrictedBasisSection k f I b) i j := by
    have hmap : ((openComplement I).ι.resLE (nvCover (basisSection k f b) i)
          (nvCover (restrictedBasisSection k f I b) i) hpre).appTop =
        (nvCover (basisSection k f b) i).topIso.hom ≫
          (openComplement I).ι.appLE (nvCover (basisSection k f b) i)
            (nvCover (restrictedBasisSection k f I b) i) hpre ≫
          (nvCover (restrictedBasisSection k f I b) i).topIso.inv :=
      Scheme.Hom.resLE_app_top (openComplement I).ι hpre
    refine (CategoryTheory.ConcreteCategory.congr_hom hmap
      (chartRatio (basisSection k f b) i j)).trans ?_
    rw [chartRatio, chartRatio, CategoryTheory.ConcreteCategory.comp_apply,
      CategoryTheory.ConcreteCategory.comp_apply, CategoryTheory.Iso.inv_hom_id_apply, hratio]
  rw [chartSection, appTop_appTop, hφ, hres]

/-- **The morphism `X ∖ Z ⟶ ℙᴺ_ℤ` glued from the charts of a basis of `V_n` is the morphism of
[Stacks, Tag 01ND] attached to the restricted basis sections.** The two are glued over the same
cover of `X ∖ Z` by `Stacks.SectionsVanishingOnSubscheme.nvCover_restrictedBasisSection`, from the
same chart families by
`Stacks.SectionsVanishingOnSubscheme.appTop_homOfLE_chartSection`. -/
theorem toProjectiveSpaceAtUniverseOffSupport_eq
    (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L m))
    (h : GeneratesOffSupport k f I L m) :
    toProjectiveSpaceAtUniverseOffSupport k f b h =
      Stacks.ProjectiveFromSections.toProjectiveSpaceAtUniverse
        (restrictedBasisSection k f I b) (generatesStalks_restrictedBasisSection k f I b h) := by
  refine Scheme.hom_ext_of_forall _ _ fun x => ?_
  obtain ⟨i, hi⟩ := exists_mem_nvCover_of_generatesStalks (restrictedBasisSection k f I b)
    (generatesStalks_restrictedBasisSection k f I b h) x
  refine ⟨nvCover (restrictedBasisSection k f I b) i, hi, ?_⟩
  have hspan : Ideal.span (Set.range fun j =>
      ((openComplement I).toScheme.homOfLE
          (nvCover_restrictedBasisSection k f I b i).le).appTop
        (chartSection (basisSection k f b) (openComplement I) i j)) = ⊤ :=
    Stacks.SectionsToProjectiveSpace.span_range_comp _ _
      (span_range_chartSection (basisSection k f b) (openComplement I) i)
  rw [Stacks.ProjectiveFromSections.ι_toProjectiveSpaceAtUniverse,
    ← Scheme.homOfLE_ι (openComplement I).toScheme
      (nvCover_restrictedBasisSection k f I b i).le,
    Category.assoc, ι_toProjectiveSpaceAtUniverseOffSupport,
    Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality _ _ _ hspan]
  exact Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse_congr
    (funext fun j => appTop_homOfLE_chartSection k f I b i j) hspan
    (Stacks.ProjectiveFromSections.span_range_chartRatio _ i)

/-- **The morphism `X ∖ Z ⟶ ℙᴺ_k` glued from the charts of a basis of `V_n` is the morphism
`φ_{(ℒ ^⊗ n|_{X ∖ Z}, (b₀, …, b_N))}` of [Stacks, Tag 01ND] attached to the restricted basis
sections.** -/
theorem toProjectiveSpaceOverOffSupport_eq
    (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L m))
    (h : GeneratesOffSupport k f I L m) :
    toProjectiveSpaceOverOffSupport k f b h =
      toProjectiveSpaceOver (restrictedBasisSection k f I b)
        (generatesStalks_restrictedBasisSection k f I b h) ((openComplement I).ι ≫ f) := by
  rw [toProjectiveSpaceOverOffSupport, Stacks.ProjectiveFromSections.toProjectiveSpaceOver,
    toProjectiveSpaceAtUniverseOffSupport_eq]

/-- **The morphism `X ∖ Z ⟶ P(V_n)` attached to a basis of `V_n` is the canonical morphism of
[Stacks, Tag 0FCY]**, applied to the linear system `V_n` restricted to `X ∖ Z`.

`Stacks.SectionsVanishingOnSubscheme.toProjectiveSpaceOfVanishingSections` is built as the
morphism to `ℙᴺ_k` of the basis sections followed by the coordinate isomorphism `ℙᴺ_k ≅ P(V_n)`,
with the morphism to `ℙᴺ_k` glued over the charts of `X ∖ Z` cut out by the basis sections on `X`;
`AlgebraicGeometry.toProjectiveSpaceOfModule` is the same composite for the family of basis
sections *restricted* to `X ∖ Z`, which generates `ℒ ^⊗ n` there. The coordinate isomorphisms are
the same, and the two morphisms to `ℙᴺ_k` agree by
`Stacks.SectionsVanishingOnSubscheme.toProjectiveSpaceOverOffSupport_eq`. So the morphism the tag
speaks about, and the one this development glues, are one morphism. -/
theorem toProjectiveSpaceOfVanishingSections_eq
    (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L m))
    (h : GeneratesOffSupport k f I L m) :
    toProjectiveSpaceOfVanishingSections k f b h =
      AlgebraicGeometry.toProjectiveSpaceOfModule b (restrictedBasisSection k f I b)
        (generatesStalks_restrictedBasisSection k f I b h) ((openComplement I).ι ≫ f) := by
  rw [toProjectiveSpaceOfVanishingSections, AlgebraicGeometry.toProjectiveSpaceOfModule,
    toProjectiveSpaceOverOffSupport_eq]
  rfl

end Restrict

/-! ### The morphism of a generating family, restricted to an open subscheme -/

section Naturality

variable {X S : Scheme.{u}} {M : X.Modules} [IsInvertibleModule X M] {n : ℕ}

/-- **The morphism of [Stacks, Tag 01ND] restricted along an arbitrary morphism of schemes** is
the morphism of the pulled-back family. This is
`Stacks.ProjectiveFromSections.comp_toProjectiveSpaceAtUniverse` over a base, with the base
unchanged. -/
theorem comp_toProjectiveSpaceOver_self {Y : Scheme.{u}} (g : Y ⟶ X)
    (s : Fin (n + 1) → Γ(M, ⊤)) (hs : GeneratesStalks s) (f : X ⟶ S)
    (hs' : GeneratesStalks fun i => pullbackGlobalSections g M (s i)) :
    g ≫ toProjectiveSpaceOver s hs f =
      toProjectiveSpaceOver (fun i => pullbackGlobalSections g M (s i)) hs' (g ≫ f) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, toProjectiveSpaceOver_fst, toProjectiveSpaceOver_fst]
  · rw [Category.assoc,
      show toProjectiveSpaceOver s hs f ≫ pullback.snd (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
        toProjectiveSpaceAtUniverse s hs from toProjectiveSpaceOver_snd s hs f,
      show toProjectiveSpaceOver (fun i => pullbackGlobalSections g M (s i)) hs' (g ≫ f) ≫
          pullback.snd (terminal.from S)
            (terminal.from (projectiveSpaceAtUniverse.{u} n)) =
        toProjectiveSpaceAtUniverse _ hs' from toProjectiveSpaceOver_snd _ hs' _,
      comp_toProjectiveSpaceAtUniverse s hs g hs']

end Naturality

/-! ### Products of sections, and the sections of `V_n` they produce -/

section Product

variable {X : Scheme.{u}} {L : X.Modules} [IsInvertibleModule X L]

/-- **A section is nonzero where it does not vanish.** -/
theorem ne_zero_of_mem_nvOpen {M : X.Modules} [IsInvertibleModule X M] (s : Γ(M, ⊤)) {x : X}
    (hx : x ∈ nvOpen M s) : s ≠ 0 := by
  intro h
  rw [Stacks.NonvanishingSpelling.mem_nonvanishingOpen_iff, h, map_zero] at hx
  exact hx (Submodule.zero_mem _)

/-- **The product of a global section with a single global section of another power**, as the
product power family of [Stacks, Tag 01VS] with a one-member second family. -/
def prodWith {a b c : ℤ} (hc : a + b = c) {mm : ℕ}
    (t : Fin (mm + 1) → Γ(tensorPowModule X L a, ⊤)) (v : Γ(tensorPowModule X L b, ⊤))
    (α : Fin (mm + 1)) : Γ(tensorPowModule X L c, ⊤) :=
  Stacks.ProductFamilyTwist.prodPowFamily L hc t (fun _ : Fin 1 => v)
    (Stacks.ProductFamilyRatio.segreIdx mm 0 α 0)

/-- **The nonvanishing open of a product is the intersection of the two nonvanishing opens**
([Stacks, Tag 01CY]), after the two transports the product power family carries. -/
theorem nvOpen_prodWith {a b c : ℤ} (hc : a + b = c) {mm : ℕ}
    (t : Fin (mm + 1) → Γ(tensorPowModule X L a, ⊤)) (v : Γ(tensorPowModule X L b, ⊤))
    (α : Fin (mm + 1)) :
    nvOpen (tensorPowModule X L c) (prodWith hc t v α) =
      nvOpen (tensorPowModule X L a) (t α) ⊓ nvOpen (tensorPowModule X L b) v := by
  rw [show prodWith hc t v α = (Stacks.AmpleEventualGeneration.tensorPowAdd hc).hom.app ⊤
      (Stacks.ProductFamilyTwist.prodFamily t (fun _ : Fin 1 => v) (α, 0)) from
    Stacks.ProductFamilyRatio.prodPowFamily_segreIdx hc t _ α 0,
    show nvOpen (tensorPowModule X L c)
        ((Stacks.AmpleEventualGeneration.tensorPowAdd hc).hom.app ⊤
          (Stacks.ProductFamilyTwist.prodFamily t (fun _ : Fin 1 => v) (α, 0))) =
      nvOpen (tensorPowModule X L a ⊗ tensorPowModule X L b)
        (Stacks.ProductFamilyTwist.prodFamily t (fun _ : Fin 1 => v) (α, 0)) from
    TopologicalSpace.Opens.ext (Stacks.Ample.nonvanishingLocus_congr
      (Stacks.AmpleEventualGeneration.tensorPowAdd hc) _)]
  exact Stacks.ProductFamilyTwist.nvOpen_prodSection (t α) v

/-- **The coordinate ratios of the products along a fixed second factor are the coordinate ratios
of the first family**: `(t_{α'} v)/(t_α v) = t_{α'}/t_α`. -/
theorem ratio_prodWith {a b c : ℤ} (hc : a + b = c) {mm : ℕ}
    (t : Fin (mm + 1) → Γ(tensorPowModule X L a, ⊤)) (v : Γ(tensorPowModule X L b, ⊤))
    (α α' : Fin (mm + 1)) :
    ratio (prodWith hc t v) α α' =
      resO (Stacks.ProductFamilyRatio.nvCover_prodPowFamily_le_left hc t
        (fun _ : Fin 1 => v) α 0) (ratio t α α') :=
  Stacks.ProductFamilyRatio.ratio_prodPowFamily hc t (fun _ : Fin 1 => v) α 0 α'

/-- A product of global sections is the image of its second factor under a morphism of modules:
multiplication by the first factor. -/
theorem prodSection_eq_mulLeft_app {F G : X.Modules} (s : Γ(F, ⊤)) (w : Γ(G, ⊤)) :
    Stacks.ProductFamilyTwist.prodSection s w =
      (Stacks.TensorSectionNonvanishing.mulLeft
        (Stacks.ProductFamilyTwist.unitOfSection F s) G).app ⊤ w := by
  rw [Stacks.ProductFamilyTwist.prodSection,
    Stacks.TensorSectionNonvanishing.unitMul_eq_mulLeft,
    Stacks.SectionProduct.globalSection_comp,
    Stacks.ProductFamilyTwist.globalSection_unitOfSection]

/-- **A product one factor of which vanishes on the closed subscheme vanishes on it.** This is
the inclusion `V_{n₁} · Γ(X, ℒ ^⊗ n') ⊆ V_n` the source's proof uses: multiplication by a global
section is a morphism of modules, and the restriction to the closed subscheme is natural in the
module. -/
theorem prodWith_eq_mulLeft_app {a b c : ℤ} (hc : a + b = c) {mm : ℕ}
    (t : Fin (mm + 1) → Γ(tensorPowModule X L a, ⊤)) (v : Γ(tensorPowModule X L b, ⊤))
    (α : Fin (mm + 1)) :
    prodWith hc t v α =
      (Stacks.TensorSectionNonvanishing.mulLeft
          (Stacks.ProductFamilyTwist.unitOfSection (tensorPowModule X L a) (t α))
          (tensorPowModule X L b) ≫
        (Stacks.AmpleEventualGeneration.tensorPowAdd hc).hom).app ⊤ v := by
  have h1 : prodWith hc t v α = (Stacks.AmpleEventualGeneration.tensorPowAdd hc).hom.app ⊤
      (Stacks.ProductFamilyTwist.prodSection (t α) v) :=
    Stacks.ProductFamilyRatio.prodPowFamily_segreIdx hc t (fun _ : Fin 1 => v) α 0
  rw [h1, prodSection_eq_mulLeft_app]
  rfl

/-- **A product one factor of which vanishes on the closed subscheme vanishes on it.** This is
the inclusion `V_{n₁} · Γ(X, ℒ ^⊗ n') ⊆ V_n` the source's proof uses: multiplication by a global
section is a morphism of modules, and the restriction to the closed subscheme is natural in the
module. -/
theorem pullbackGlobalSections_prodWith_eq_zero (I : X.IdealSheafData) {a b c : ℤ}
    (hc : a + b = c) {mm : ℕ} (t : Fin (mm + 1) → Γ(tensorPowModule X L a, ⊤))
    (v : Γ(tensorPowModule X L b, ⊤))
    (hv : pullbackGlobalSections I.subschemeι (tensorPowModule X L b) v = 0)
    (α : Fin (mm + 1)) :
    pullbackGlobalSections I.subschemeι (tensorPowModule X L c) (prodWith hc t v α) = 0 := by
  rw [prodWith_eq_mulLeft_app,
    Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality
      I.subschemeι _ v, hv, map_zero]

end Product

/-! ### A basis beginning at a prescribed nonzero vector -/

section AdaptedBasis

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V] {N : ℕ}

/-- **Every nonzero vector is the zeroth member of a basis.** A nonzero vector of a vector space
with a basis indexed by `Fin (N + 1)` is linearly independent by itself, so it extends to a
basis; the index set of that basis is in bijection with `Fin (N + 1)`, and composing with a
transposition makes the bijection carry the vector to `0`.

This is what lets the chart of the source's section `s = s₁ ⊗ s'` be *a standard* chart of
`ℙᴺ_k`: the morphism attached to one basis is the morphism attached to another followed by the
coordinate change the two bases induce
(`Stacks.ProjectiveSpaceChartRatio.toPolynomialModel_comp_map_basisChangeGradedHom`), so a basis
may be chosen at each point separately. -/
theorem exists_basis_zero_eq (b : Module.Basis (Fin (N + 1)) k V) {w : V} (hw : w ≠ 0) :
    ∃ b' : Module.Basis (Fin (N + 1)) k V, b' 0 = w := by
  classical
  have hli : LinearIndepOn k id ({w} : Set V) := LinearIndepOn.singleton (by simpa using hw)
  have hmem : w ∈ hli.extend (Set.subset_univ ({w} : Set V)) :=
    Module.Basis.subset_extend hli rfl
  let B := Module.Basis.extend hli
  let e : (hli.extend (Set.subset_univ ({w} : Set V))) ≃ Fin (N + 1) := B.indexEquiv b
  let e' : (hli.extend (Set.subset_univ ({w} : Set V))) ≃ Fin (N + 1) :=
    e.trans (Equiv.swap (e ⟨w, hmem⟩) 0)
  refine ⟨B.reindex e', ?_⟩
  have h0 : e'.symm 0 = ⟨w, hmem⟩ := by
    rw [Equiv.symm_apply_eq]
    simp only [e', Equiv.trans_apply, Equiv.swap_apply_left]
  rw [Module.Basis.reindex_apply, h0]
  exact Module.Basis.extend_apply_self hli ⟨w, hmem⟩

end AdaptedBasis

/-! ### A linear form in the coordinates of one standard chart -/

section ChartLinearForm

open Stacks.ProjectiveSpaceChartRatio

variable (N : ℕ) (k : Type u) [CommRing k]

/-- The structure morphism over `Spec k` of the `i`-th standard chart of `ℙᴺ_{Spec k}`. -/
abbrev chartToBase (i : Fin (N + 1)) :
    (projectiveSpaceOver.standardChart N (Spec (.of k)) i).toScheme ⟶ Spec (.of k) :=
  (projectiveSpaceOver.standardChart N (Spec (.of k)) i).ι ≫
    pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} N))

/-- **A linear form in the chart coordinates of the `i`-th standard chart of `ℙᴺ_k`**: the
`k`-combination `∑ₗ cₗ (Tₗ/Tᵢ)`, a regular function on the chart. These are the members of the
projection family that the source's `s = s₁ ⊗ s'` produces: a product of a section vanishing on
`Z` with a section of a high power is a *vector* of `V_n` and not a basis vector of it. -/
def chartLinearForm (i : Fin (N + 1)) (c : Fin (N + 1) → k) :
    Γ((projectiveSpaceOver.standardChart N (Spec (.of k)) i).toScheme, ⊤) :=
  ∑ l, baseRingHom (chartToBase N k i) (c l) *
    Stacks.ProductFamilyRatio.chartCoordScheme N (Spec (.of k)) i l

variable {N k}
variable {Y : Scheme.{u}} {M : Y.Modules} [IsInvertibleModule Y M]

/-- **The chart ring map sends a linear form in the chart coordinates to the ratio of the
corresponding combination of the family.** This is `k`-linearity of a linear system read in the
trivialization `Pᵢ` (`Stacks.ProjectiveSpaceChartRatio.sum_mul_resO_ratio_smul`) together with
the chart dictionary (`Stacks.ChartDictionary.appLE_chartCoordOver`, in the `appTop` spelling of
`Stacks.ProductFamilyRatio.appTop_resLE_chartCoordScheme`). -/
theorem appTop_resLE_chartLinearForm (P : Fin (N + 1) → Γ(M, ⊤)) (g : Y ⟶ Spec (.of k))
    (q : Y ⟶ projectiveSpaceOver N (Spec (.of k)))
    (hqf : q ≫ pullback.fst (terminal.from (Spec (.of k)))
      (terminal.from (projectiveSpaceAtUniverse.{u} N)) = g)
    (i : Fin (N + 1))
    (hchart : (nvCover P i).ι ≫ q ≫
        projectiveSpaceOver.toIntegralAtUniverse N (Spec (.of k)) =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse (chartRatio P i)
        (span_range_chartRatio P i))
    (e : nvCover P i ≤ q ⁻¹ᵁ projectiveSpaceOver.standardChart N (Spec (.of k)) i)
    (c : Fin (N + 1) → k) :
    (q.resLE (projectiveSpaceOver.standardChart N (Spec (.of k)) i) (nvCover P i) e).appTop
        (chartLinearForm N k i c) =
      (nvCover P i).topIso.inv
        (div (P i) le_rfl
          (resT (nvCover P i) (∑ l, baseRingHom g (c l) • P l))) := by
  have hbase : q.resLE (projectiveSpaceOver.standardChart N (Spec (.of k)) i) (nvCover P i) e ≫
      chartToBase N k i = (nvCover P i).ι ≫ g := by
    rw [chartToBase, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hqf]
  have hcoeff : ∀ l : Fin (N + 1),
      (q.resLE (projectiveSpaceOver.standardChart N (Spec (.of k)) i) (nvCover P i) e).appTop
          (baseRingHom (chartToBase N k i) (c l)) =
        (nvCover P i).topIso.inv (resO (le_top : nvCover P i ≤ ⊤) (baseRingHom g (c l))) := by
    intro l
    rw [← baseRingHom_ι (nvCover P i) g (c l), ← hbase, ← baseRingHom_comp]
    rfl
  have hcoord : ∀ l : Fin (N + 1),
      (q.resLE (projectiveSpaceOver.standardChart N (Spec (.of k)) i) (nvCover P i) e).appTop
          (Stacks.ProductFamilyRatio.chartCoordScheme N (Spec (.of k)) i l) =
        (nvCover P i).topIso.inv (ratio P i l) := by
    intro l
    rw [Stacks.ProductFamilyRatio.appTop_resLE_chartCoordScheme P q i hchart e l]
    rfl
  have hdiv : div (P i) le_rfl (resT (nvCover P i) (∑ l, baseRingHom g (c l) • P l)) =
      ∑ l, resO (le_top : nvCover P i ≤ ⊤) (baseRingHom g (c l)) * ratio P i l := by
    refine (eq_div (P i) le_rfl ?_).symm
    have h := sum_mul_resO_ratio_smul P g (le_rfl : nvCover P i ≤ nvCover P i) c
    simpa only [Stacks.ChartImmersionFinish.resO_self] using h
  rw [chartLinearForm, map_sum, hdiv, map_sum]
  exact Finset.sum_congr rfl fun l _ => by
    rw [map_mul, hcoeff l, hcoord l, ← map_mul]

end ChartLinearForm

/-! ### Members of `V_n` as sections, and their coordinates in a basis -/

section Members

variable (k : Type u) [CommRing k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (I : X.IdealSheafData) (L : X.Modules) [IsInvertibleModule X L] (m : ℤ) {N : ℕ}

/-- **The members of `V_n` read as global sections of `ℒ ^⊗ n`**, as a family indexed by `V_n`
itself: the family whose germs `Stacks.SectionsVanishingOnSubscheme.GeneratesOffSupport` asks to
span. -/
def vanishingFamily : vanishingSections k f I L m → Γ(tensorPowModule X L m, ⊤) :=
  fun s => (s : Stacks.Bertini.globalSections k f (tensorPowModule X L m))

variable {k f I L m}

/-- A member of `V_n` restricts to zero on the closed subscheme, by definition of `V_n`. -/
theorem pullbackGlobalSections_vanishingFamily (s : vanishingSections k f I L m) :
    pullbackGlobalSections I.subschemeι (tensorPowModule X L m)
      (vanishingFamily k f I L m s) = 0 := s.2

/-- A global section of `ℒ ^⊗ n` restricting to zero on the closed subscheme, as a member of
`V_n`. -/
def toVanishing (s : Γ(tensorPowModule X L m, ⊤))
    (hs : pullbackGlobalSections I.subschemeι (tensorPowModule X L m) s = 0) :
    vanishingSections k f I L m :=
  ⟨(s : Stacks.Bertini.globalSections k f (tensorPowModule X L m)), hs⟩

/-- The section underlying `toVanishing s hs` is `s`. -/
@[simp] theorem vanishingFamily_toVanishing (s : Γ(tensorPowModule X L m, ⊤))
    (hs : pullbackGlobalSections I.subschemeι (tensorPowModule X L m) s = 0) :
    vanishingFamily k f I L m (toVanishing (k := k) (f := f) s hs) = s := rfl

/-- The sections of a basis of `V_n` are the members of `V_n` read as sections. -/
theorem basisSection_eq_vanishingFamily
    (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L m)) (i : Fin (N + 1)) :
    basisSection k f b i = vanishingFamily k f I L m (b i) := rfl

/-- **A member of `V_n` is the combination of a basis with its coordinates**, read on sections.
The coefficients act through the structure morphism of `X` over `k`. -/
theorem vanishingFamily_eq_sum_repr
    (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L m))
    (z : vanishingSections k f I L m) :
    vanishingFamily k f I L m z =
      ∑ l, Stacks.ProjectiveSpaceChartRatio.baseRingHom f (b.repr z l) •
        vanishingFamily k f I L m (b l) := by
  have h := congrArg (vanishingSections k f I L m).subtype (b.sum_repr z).symm
  rw [map_sum] at h
  simp only [map_smul, Submodule.subtype_apply] at h
  exact h

/-- **A member of `V_n`, restricted to `X ∖ Z`, is the combination of the restricted basis with
its coordinates.** The coefficients now act through the structure morphism of `X ∖ Z`. -/
theorem restrictSection_vanishingFamily_eq_sum_repr
    (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L m))
    (z : vanishingSections k f I L m) :
    restrictSection I (vanishingFamily k f I L m z) =
      ∑ l, Stacks.ProjectiveSpaceChartRatio.baseRingHom ((openComplement I).ι ≫ f)
        (b.repr z l) • restrictedBasisSection k f I b l := by
  rw [restrictSection, vanishingFamily_eq_sum_repr b z, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul,
    ← Stacks.ProjectiveSpaceChartRatio.baseRingHom_comp (openComplement I).ι f]
  rfl

end Members

/-! ### The ratios of the products, restricted to the complement -/

section ProductRatio

variable {X : Scheme.{u}} (I : X.IdealSheafData) {L : X.Modules} [IsInvertibleModule X L]

/-- **The coordinate ratios of the restricted products are the restricted coordinate ratios of
the first family.** This is `Stacks.SectionsVanishingOnSubscheme.ratio_prodWith` — the arithmetic
`(t_{α'} v)/(t_α v) = t_{α'}/t_α` of step 6 of [Stacks, Tag 01VS] — carried to `X ∖ Z` by
`Stacks.RatioPullback.resO_ratio_pullbackGlobalSections`. -/
theorem ratio_restrictSection_prodWith {a b c : ℤ} (hc : a + b = c) {mm : ℕ}
    (t : Fin (mm + 1) → Γ(tensorPowModule X L a, ⊤)) (v : Γ(tensorPowModule X L b, ⊤))
    (α α' : Fin (mm + 1))
    (hle : nvCover (fun β => restrictSection I (prodWith hc t v β)) α ≤
      nvCover (fun β => restrictSection I (t β)) α) :
    ratio (fun β => restrictSection I (prodWith hc t v β)) α α' =
      resO hle (ratio (fun β => restrictSection I (t β)) α α') := by
  have hWu : nvCover (fun β => restrictSection I (prodWith hc t v β)) α ≤
      (openComplement I).ι ⁻¹ᵁ nvCover (prodWith hc t v) α :=
    (nvOpen_restrictSection I (prodWith hc t v α)).le
  have hWt : nvCover (fun β => restrictSection I (prodWith hc t v β)) α ≤
      (openComplement I).ι ⁻¹ᵁ nvCover t α :=
    hle.trans (nvOpen_restrictSection I (t α)).le
  have h2 := Stacks.RatioPullback.resO_ratio_pullbackGlobalSections (openComplement I).ι
    (tensorPowModule X L a) t α α' hle hWt
  rw [← appLE_ratio_restrictSection I (prodWith hc t v) α α' hWu, h2, ratio_prodWith]
  exact CategoryTheory.ConcreteCategory.congr_hom
    (Scheme.Hom.map_appLE (openComplement I).ι hWu
      (homOfLE (Stacks.ProductFamilyRatio.nvCover_prodPowFamily_le_left hc t
        (fun _ : Fin 1 => v) α 0)).op) (ratio t α α')

end ProductRatio

/-! ### The products of a member of `V_{n₁}` with a family, as members of `V_n` -/

section ProdVanishing

variable (k : Type u) [CommRing k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (I : X.IdealSheafData) {L : X.Modules} [IsInvertibleModule X L]

/-- **The products of a member of `V_{n₁}` with a family of sections of `ℒ ^⊗ n'`, as members of
`V_n`.** The inclusion `V_{n₁} · Γ(X, ℒ ^⊗ n') ⊆ V_n` of the source's proof. -/
def prodVanishing {a b c : ℤ} (hc : a + b = c) {mm : ℕ}
    (t : Fin (mm + 1) → Γ(tensorPowModule X L a, ⊤)) (v : vanishingSections k f I L b)
    (β : Fin (mm + 1)) : vanishingSections k f I L c :=
  toVanishing (prodWith hc t (vanishingFamily k f I L b v) β)
    (pullbackGlobalSections_prodWith_eq_zero I hc t _
      (pullbackGlobalSections_vanishingFamily v) β)

/-- The section underlying `prodVanishing k f I hc t v β` is the product `t_β v`. -/
@[simp] theorem vanishingFamily_prodVanishing {a b c : ℤ} (hc : a + b = c) {mm : ℕ}
    (t : Fin (mm + 1) → Γ(tensorPowModule X L a, ⊤)) (v : vanishingSections k f I L b)
    (β : Fin (mm + 1)) :
    vanishingFamily k f I L c (prodVanishing k f I hc t v β) =
      prodWith hc t (vanishingFamily k f I L b v) β := rfl

end ProdVanishing

/-! ### The immersion -/

section Immersion

open Stacks.ProjectiveSpaceChartRatio Stacks.LinearChartProjection
open Stacks.AlgebraicGeometry.ProjBaseChange

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (I : X.IdealSheafData) {L : X.Modules} [IsInvertibleModule X L]

/-- **The immersion clause of [Stacks, Tag 0FD5] at one degree.** Suppose the sections of
`ℒ ^⊗ n'` in a finite family `t` generate it and the morphism `X ⟶ ℙᵐ_k` they pin is an immersion
— which for an ample `ℒ` on a scheme of finite type over `k` is steps 1–4 of [Stacks, Tag 01VS],
proved as `Stacks.ChartImmersionFinish.chartImmersion`. Suppose moreover that `V_{n₁}` generates
`ℒ ^⊗ n₁` off the closed subscheme and that `V_n` does, for `n = n' + n₁`. Then the canonical
morphism `X ∖ Z ⟶ P(V_n)` of [Stacks, Tag 0FCY] is an immersion.

This is the source's own argument. Fix a point `x` of `X ∖ Z`, a section `v ∈ V_{n₁}` not
vanishing at `x` and a member `t_{α'}` of the family not vanishing at `x`; the products
`u_β = t_β v` lie in `V_n` and `u_{α'}` does not vanish at `x`. Choose a basis of `V_n` whose
zeroth member is `u_{α'}`: being an immersion is unchanged by that choice, because the two
morphisms to `ℙᴺ_k` differ by the linear automorphism the change of basis induces
(`Stacks.ProjectiveSpaceChartRatio.toPolynomialModel_comp_map_basisChangeGradedHom`). In that
basis the preimage of the zeroth standard chart `D₊(T₀)` is `X_{u_{α'}} = X_v ⊓ X_{t_{α'}}`, and
on it the linear forms of the `u_β` are regular functions carrying the chart restriction of the
morphism to the restriction of the immersion of the `t`-family
(`Stacks.SectionsVanishingOnSubscheme.ratio_restrictSection_prodWith`: the ratios
`(t_β v)/(t_{α'} v)` are the ratios `t_β/t_{α'}`). So that restriction is an immersion by
[Stacks, Tag 07RK], and being an immersion is local on the target. -/
theorem isImmersion_toProjectiveSpaceOfVanishingSections
    {a n₁ n : ℤ} (hc : a + n₁ = n) {mm : ℕ}
    (t : Fin (mm + 1) → Γ(tensorPowModule X L a, ⊤)) (ht : GeneratesStalks t)
    (himm : IsImmersion (toProjectiveSpaceOver t ht f))
    (h₁ : GeneratesOffSupport k f I L n₁) (h : GeneratesOffSupport k f I L n)
    {N : ℕ} (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L n)) :
    IsImmersion (toProjectiveSpaceOfVanishingSections k f b h) := by
  classical
  rw [toProjectiveSpaceOfVanishingSections_eq,
    AlgebraicGeometry.isImmersion_toProjectiveSpaceOfModule_iff]
  -- the `t`-family restricted to `X ∖ Z`, and the immersion it pins there
  have htU : GeneratesStalks (fun i => restrictSection I (t i)) :=
    generatesStalks_restrictSection I t fun y =>
      exists_mem_nvCover_of_generatesStalks t ht ((openComplement I).ι.base y)
  have hjimm : IsImmersion (toProjectiveSpaceOver (fun i => restrictSection I (t i)) htU
      ((openComplement I).ι ≫ f)) := by
    rw [← comp_toProjectiveSpaceOver_self (openComplement I).ι t ht f htU]
    have : IsImmersion (toProjectiveSpaceOver t ht f) := himm
    infer_instance
  refine isImmersion_of_comp_forall _ fun x => ?_
  -- a section of `V_{n₁}` and a member of the family, neither vanishing at `x`
  obtain ⟨vv, hvv⟩ := Stacks.StalkwiseGeneration.exists_mem_nvOpen_of_span_eq_top
    (tensorPowModule X L n₁) (vanishingFamily k f I L n₁) ((openComplement I).ι.base x)
    (h₁ ((openComplement I).ι.base x)
      (show ((openComplement I).ι.base x : X) ∈ openComplement I from x.2))
  obtain ⟨α', hα'⟩ := exists_mem_nvCover_of_generatesStalks t ht ((openComplement I).ι.base x)
  -- the chosen product does not vanish at `x`, hence is a nonzero member of `V_n`
  have hxu : ((openComplement I).ι.base x) ∈ nvOpen (tensorPowModule X L n)
      (vanishingFamily k f I L n (prodVanishing k f I hc t vv α')) := by
    rw [vanishingFamily_prodVanishing, nvOpen_prodWith]
    exact ⟨hα', hvv⟩
  have hune : prodVanishing k f I hc t vv α' ≠ 0 := by
    intro h0
    refine ne_zero_of_mem_nvOpen _ hxu ?_
    rw [h0]
    rfl
  obtain ⟨b', hb'0⟩ := exists_basis_zero_eq b hune
  set Θ : projectiveSpaceOver N (Spec (.of k)) ⟶ projectiveSpaceOver N (Spec (.of k)) :=
    (polynomialComparison k N).iso.hom ≫
      AlgebraicGeometry.Proj.map (AlgebraicGeometry.basisChangeGradedHom b b')
        (AlgebraicGeometry.irrelevant_le_map_basisChangeGradedHom b b') ≫
      (polynomialComparison k N).iso.inv with hΘ
  -- the coordinate change between the two bases
  have hss' : ∀ i, restrictedBasisSection k f I b' i =
      ∑ l, baseRingHom ((openComplement I).ι ≫ f) (b.repr (b' i) l) •
        restrictedBasisSection k f I b l := fun i =>
    restrictSection_vanishingFamily_eq_sum_repr b (b' i)
  have hpoly := toPolynomialModel_comp_map_basisChangeGradedHom
    (restrictedBasisSection k f I b) (generatesStalks_restrictedBasisSection k f I b h)
    ((openComplement I).ι ≫ f) b b'
    (generatesStalks_restrictedBasisSection k f I b' h) hss'
  have hqΘ : toProjectiveSpaceOver (restrictedBasisSection k f I b)
        (generatesStalks_restrictedBasisSection k f I b h) ((openComplement I).ι ≫ f) ≫ Θ =
      toProjectiveSpaceOver (restrictedBasisSection k f I b')
        (generatesStalks_restrictedBasisSection k f I b' h) ((openComplement I).ι ≫ f) := by
    rw [hΘ, ← Category.assoc, ← Category.assoc,
      show toProjectiveSpaceOver (restrictedBasisSection k f I b)
            (generatesStalks_restrictedBasisSection k f I b h) ((openComplement I).ι ≫ f) ≫
          (polynomialComparison k N).iso.hom =
        toPolynomialModel (restrictedBasisSection k f I b)
          (generatesStalks_restrictedBasisSection k f I b h) ((openComplement I).ι ≫ f) from rfl,
      ← hpoly,
      show toPolynomialModel (restrictedBasisSection k f I b')
            (generatesStalks_restrictedBasisSection k f I b' h) ((openComplement I).ι ≫ f) =
          toProjectiveSpaceOver (restrictedBasisSection k f I b')
            (generatesStalks_restrictedBasisSection k f I b' h) ((openComplement I).ι ≫ f) ≫
            (polynomialComparison k N).iso.hom from rfl,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  -- the chart of the adapted basis, and its preimage
  have hq'pre : toProjectiveSpaceOver (restrictedBasisSection k f I b')
        (generatesStalks_restrictedBasisSection k f I b' h) ((openComplement I).ι ≫ f) ⁻¹ᵁ
      projectiveSpaceOver.standardChart N (Spec (.of k)) 0 =
      nvCover (restrictedBasisSection k f I b') 0 :=
    Stacks.AmpleImmersionReduction.preimage_standardChart _
      (generatesStalks_restrictedBasisSection k f I b' h) _
      (fun i => ι_toProjectiveSpaceOver _ (generatesStalks_restrictedBasisSection k f I b' h) _ i)
      0
  have hr'0 : restrictedBasisSection k f I b' 0 =
      restrictSection I (prodWith hc t (vanishingFamily k f I L n₁ vv) α') := by
    show restrictSection I (vanishingFamily k f I L n (b' 0)) = _
    rw [hb'0]
    rfl
  have hWeq : nvCover (restrictedBasisSection k f I b') 0 =
      nvCover (fun β => restrictSection I
        (prodWith hc t (vanishingFamily k f I L n₁ vv) β)) α' := by
    show nvOpen (restrictedPow I (L := L) (m := n)) (restrictedBasisSection k f I b' 0) = _
    rw [hr'0]
  have hnv0 : nvCover (restrictedBasisSection k f I b') 0 =
      (openComplement I).ι ⁻¹ᵁ (nvOpen (tensorPowModule X L a) (t α') ⊓
        nvOpen (tensorPowModule X L n₁) (vanishingFamily k f I L n₁ vv)) := by
    rw [show nvCover (restrictedBasisSection k f I b') 0 =
        nvOpen (restrictedPow I (L := L) (m := n)) (restrictedBasisSection k f I b' 0) from rfl,
      hr'0, nvOpen_restrictSection, nvOpen_prodWith]
  have hle : nvCover (restrictedBasisSection k f I b') 0 ≤
      nvCover (fun i => restrictSection I (t i)) α' := by
    rw [hnv0, show nvCover (fun i => restrictSection I (t i)) α' =
      (openComplement I).ι ⁻¹ᵁ nvOpen (tensorPowModule X L a) (t α') from
        nvOpen_restrictSection I (t α')]
    exact Scheme.Hom.preimage_mono _ inf_le_left
  have hqV : toProjectiveSpaceOver (restrictedBasisSection k f I b)
        (generatesStalks_restrictedBasisSection k f I b h) ((openComplement I).ι ≫ f) ⁻¹ᵁ
      (Θ ⁻¹ᵁ projectiveSpaceOver.standardChart N (Spec (.of k)) 0) =
      nvCover (restrictedBasisSection k f I b') 0 := by
    rw [← Scheme.Hom.comp_preimage, hqΘ, hq'pre]
  refine ⟨projectiveSpaceOver N (Spec (.of k)), Θ,
    Θ ⁻¹ᵁ projectiveSpaceOver.standardChart N (Spec (.of k)) 0,
    hqV.ge (hnv0.ge ⟨hα', hvv⟩), ?_⟩
  rw [hqV, hqΘ]
  refine isImmersion_ι_comp_of_chart (restrictedBasisSection k f I b')
    (fun i => restrictSection I (t i)) _ (toProjectiveSpaceOver_fst _ _ _) _
    (toProjectiveSpaceOver_fst _ _ _) 0 α'
    (ι_toProjectiveSpaceOver _ htU ((openComplement I).ι ≫ f) α') hle hq'pre.ge
    (fun β => chartLinearForm N k 0 (fun l => b'.repr (prodVanishing k f I hc t vv β) l)) ?_ ?_ ?_
  · -- the projection family spans the unit ideal: its `α'`-th member is `1`
    have hrepr : ∀ l, b'.repr (prodVanishing k f I hc t vv α') l =
        if (0 : Fin (N + 1)) = l then 1 else 0 := by
      intro l
      rw [← hb'0, Module.Basis.repr_self, Finsupp.single_apply]
    rw [Ideal.eq_top_iff_one]
    refine Ideal.subset_span ⟨α', ?_⟩
    show chartLinearForm N k 0 (fun l => b'.repr (prodVanishing k f I hc t vv α') l) = 1
    rw [chartLinearForm, Finset.sum_eq_single_of_mem (0 : Fin (N + 1)) (Finset.mem_univ _)
      (fun l _ hl => by rw [hrepr l, if_neg (fun he => hl he.symm), map_zero, zero_mul]),
      hrepr 0, if_pos rfl, map_one, one_mul,
      Stacks.ProductFamilyRatio.chartCoordScheme_self]
  · -- the chart ring map carries the projection family to the ratios of the `t`-family
    intro β
    rw [appTop_resLE_chartLinearForm (restrictedBasisSection k f I b')
      ((openComplement I).ι ≫ f) _ (toProjectiveSpaceOver_fst _ _ _) 0
      (ι_toProjectiveSpaceOver _ (generatesStalks_restrictedBasisSection k f I b' h) _ 0)
      hq'pre.ge (fun l => b'.repr (prodVanishing k f I hc t vv β) l), chartRatio,
      Stacks.ProjectiveFromSections.homOfLE_appTop_topIso_inv]
    refine congrArg (nvCover (restrictedBasisSection k f I b') 0).topIso.inv ?_
    rw [← restrictSection_vanishingFamily_eq_sum_repr b' (prodVanishing k f I hc t vv β),
      vanishingFamily_prodVanishing]
    refine (eq_div (restrictedBasisSection k f I b' 0) le_rfl ?_).symm
    have hstep := resO_ratio_smul
      (fun γ => restrictSection I (prodWith hc t (vanishingFamily k f I L n₁ vv) γ))
      hWeq.le β
    rw [ratio_restrictSection_prodWith I hc t _ α' β (hWeq.ge.trans hle),
      Stacks.ChartImmersionFinish.resO_resO, ← hr'0] at hstep
    exact hstep
  · -- the restriction of the immersion of the `t`-family is an immersion
    have : IsImmersion (toProjectiveSpaceOver (fun i => restrictSection I (t i)) htU
      ((openComplement I).ι ≫ f)) := hjimm
    infer_instance

/-! ### Stacks Tag 0FD5 -/

/-- **[Stacks, Tag 0FD5].** Let `k` be a field, let `X` be a proper scheme over `k`, let `ℒ` be an
ample invertible `𝒪_X`-module and let `Z ⊂ X` be the closed subscheme cut out by a quasi-coherent
sheaf of ideals `I`. Then there is an integer `n₀` such that for every `n ≥ n₀` the kernel `V_n`
of `Γ(X, ℒ ^⊗ n) ⟶ Γ(Z, ℒ ^⊗ n|_Z)` generates `ℒ ^⊗ n` on `X ∖ Z` and the canonical morphism

`X ∖ Z ⟶ 𝐏(V_n)`

of [Stacks, Tag 0FCY] is an immersion of schemes over `k`.

The generation is the hypothesis `h` the existential carries: `GeneratesOffSupport k f I L n` says
that the germs of the members of `V_n` span the stalk of `ℒ ^⊗ n` at every point of `X ∖ Z`, and
it is what makes the canonical morphism exist. That morphism is
`AlgebraicGeometry.toProjectiveSpaceOfModule`, the morphism of [Stacks, Tag 0FCY], applied to the
linear system `V_n` restricted to `X ∖ Z`: that is what
`Stacks.SectionsVanishingOnSubscheme.toProjectiveSpaceOfVanishingSections_eq` proves the morphism
named below to be. The source speaks of *the* canonical morphism, which is basis free, and the
conclusion is asserted for the morphism built in **every** basis of `V_n` — the presentation of
`𝐏(V_n)` as `ℙᴺ_k` that [Stacks, Tag 0FCY] is stated with needs one. -/
@[stacks 0FD5]
theorem exists_bound_generatesOffSupport_and_isImmersion [IsProper f]
    (hL : IsAmple X L) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → ∃ h : GeneratesOffSupport k f I L n,
      ∀ (N : ℕ) (b : Module.Basis (Fin (N + 1)) k (vanishingSections k f I L n)),
        IsImmersion (toProjectiveSpaceOfVanishingSections k f b h) ∧
        toProjectiveSpaceOfVanishingSections k f b h ≫
            projectiveSpaceOfModuleToSpec k (vanishingSections k f I L n) =
          (openComplement I).ι ≫ f := by
  have hft : LocallyOfFiniteType f := inferInstance
  obtain ⟨N₁, mm, t, hN₁, ht, hchimm⟩ := Stacks.ChartImmersionFinish.chartImmersion f L hL hft
  obtain ⟨m₀, hm₀⟩ := exists_bound_generatesOffSupport k f I L hL
  refine ⟨m₀ + N₁, fun n hn => ⟨hm₀ n (by omega), fun N b => ⟨?_, ?_⟩⟩⟩
  · exact isImmersion_toProjectiveSpaceOfVanishingSections k f I
      (show N₁ + (n - N₁) = n by ring) t ht
      (hchimm _ (toProjectiveSpaceOver_fst t ht f) (fun i => ι_toProjectiveSpaceOver t ht f i))
      (hm₀ (n - N₁) (by omega)) (hm₀ n (by omega)) b
  · exact toProjectiveSpaceOfVanishingSections_comp_toSpec k f b _

end Immersion

end Stacks.SectionsVanishingOnSubscheme

end
