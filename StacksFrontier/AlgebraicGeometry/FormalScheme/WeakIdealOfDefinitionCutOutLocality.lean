/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumComponentIso
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionKernelOfThickening
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionLocalityMcQuillan

/-!
# Locality of weak ideals of definition cut out by their sections

**Stacks 0AIV** says that the condition of being a weak ideal of definition, and that of being a
fundamental system of weak ideals of definition, may be checked on the members of an affine open
covering of a formal scheme `𝔛` in the sense of McQuillan. For an arbitrary ideal sheaf both claims
are false (`IdealSheaf.exists_not_isWeakIdealOfDefinitionOn_of_cover`,
`not_forall_isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_cover`,
`not_forall_isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_hasBasis_cover`). This file proves
them for the ideal sheaves cut out by their sections over the affine formal opens
(`IdealSheaf.IsCutOutOn`), the class to which the correspondence of Stacks 0AIV with thickenings
and its colimit criterion apply.

## The argument

Let `𝔚 ⊆ 𝔙` be affine formal opens, `𝔙 ≅ Spfw A`, with `ℐ(𝔙)` a weak ideal of definition, and let
`z : Spec (A/ℐ(𝔙)) → 𝔛` be the quotient point. Since `ℐ` is cut out over `𝔙`, a section over `𝔚`
lies in `ℐ(𝔚)` exactly when `z` kills it: every point landing in `𝔙` and killing `ℐ(𝔙)` factors
through `z`. The preimage `P = z⁻¹(𝔚)` is quasi-compact, `Spec (A/ℐ(𝔙))` being homeomorphic to
`Spfw A`, so the point `P → 𝔚 ≅ Spfw B` kills a weak ideal of definition `L` of `B` and factors
through `Spec (B/L)`, surjectively. Hence `ℐ(𝔚)` contains `L`, so is open, and its elements are
nilpotent modulo `L`, so are topologically nilpotent. For the neighbourhood-basis condition, given
a weak ideal of definition `N` of `B`, a member `ℐ` with `ℐ(𝔙)` inside the preimage of `N` has the
quotient point `Spec (B/N) → 𝔚` killing `ℐ(𝔙)`, hence `ℐ(𝔚)`, so `ℐ(𝔚) ⊆ N`.

## Main results

All in the namespace `AlgebraicGeometry.LocallyTopologicallyRingedSpace`:

* `IdealSheaf.isWeakIdealOfDefinition_of_le_of_isCutOutOn`
* `hasBasis_of_le_of_isCutOutOn`
* `IdealSheaf.isWeakIdealOfDefinitionOn_of_cover_of_isCutOutOn`:
  **Stacks 0AIV**, the weak ideal-of-definition condition on an affine open covering.
* `isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_cover_of_isCutOutOn`:
  **Stacks 0AIV**, the fundamental-system condition on an affine open covering.

## References

* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

open TopologicalRing

namespace LocallyTopologicallyRingedSpace.IdealSheaf

variable {X : LTRS.{u}} {I : IdealSheaf X}

/-- **A cut-out ideal sheaf which is a weak ideal of definition over an affine formal open is one
over every smaller affine formal open.** If `ℐ` is cut out by its sections over the weak affine
formal opens and `ℐ(𝔙)` is a weak ideal of definition, then so is `ℐ(𝔚)` for every weak affine
formal open `𝔚 ⊆ 𝔙`. -/
theorem isWeakIdealOfDefinition_of_le_of_isCutOutOn
    (hC : I.IsCutOutOn (IsWeakAffineFormalOpen X)) {V W : Opens X}
    (hV : IsWeakAffineFormalOpen X V) (hW : IsWeakAffineFormalOpen X W) (hWV : W ≤ V)
    (hJ : IsWeakIdealOfDefinition (I.ideal V)) :
    IsWeakIdealOfDefinition (I.ideal W) := by
  let A := hV.chart.ring.α
  let hA := hV.chart.admissible
  let χ := hV.chart.iso
  let J := weakChartIdeal A hA χ (I.ideal V) hJ
  let z := weakChartPoint A hA χ J
  have hzV : Set.range z.toHom.base ⊆ (V : Set X) := range_weakChartPoint_subset A hA χ J
  have hzI : ∀ t ∈ I.ideal V, (z.toHom.c.app (op V)).1 t = 0 := by
    intro t ht
    obtain ⟨a, rfl⟩ := (weakChartSectionsRingEquiv A hA χ).surjective t
    exact (weakChartPoint_c_app_weakChartSections_eq_zero_iff A hA χ J a).2 ht
  have key : ∀ s, s ∈ I.ideal W ↔ (z.toHom.c.app (op W)).1 s = 0 := by
    intro s
    refine ⟨fun hs => (hC V hV W hWV s).1 hs _ z hzV hzI, fun hs => (hC V hV W hWV s).2 ?_⟩
    intro T f hf hfI
    obtain ⟨b, hb, -⟩ := existsUnique_weakChartPoint_factor A hA χ J f hf fun a ha => hfI _ ha
    have := ker_le_ker_comp (schemeToLTRS.map b) z W (mem_ker_iff.2 hs)
    rw [hb] at this
    exact mem_ker_iff.1 this
  let P : (Spec (spfQuotientOn A J)).Opens := (Opens.map z.toHom.base).obj W
  have hQ : IsCompact ((weakChartEmbedding A hA χ).toHom.base ⁻¹' (W : Set X)) :=
    (PresheafedSpace.IsOpenImmersion.base_open
      (f := (weakChartEmbedding A hA χ).toHom)).isInducing.isCompact_preimage' hW.isCompact
      (by rwa [range_weakChartEmbedding])
  have : CompactSpace P.toScheme := isCompact_iff_compactSpace.1
    (isCompact_preimage_spfOfQuotientOn A J
      ((Opens.map (weakChartEmbedding A hA χ).toHom.base).obj W) hQ)
  let g := schemeToLTRS.map P.ι ≫ z
  have hgW : Set.range g.toHom.base ⊆ (W : Set X) := Set.range_subset_iff.2 fun y => y.2
  let B := hW.chart.ring.α
  let hB := hW.chart.admissible
  let ψ := hW.chart.iso
  obtain ⟨L, hL⟩ := exists_weakIdeal_kill_weakChartSections B hB ψ g hgW
  obtain ⟨b₀, hb₀, -⟩ := existsUnique_weakChartPoint_factor B hB ψ L g hgW hL
  let K : Ideal B := Ideal.comap (weakChartSectionsRingEquiv B hB ψ) (I.ideal W)
  have hK (b : B) : b ∈ K ↔ (z.toHom.c.app (op W)).1 ((weakChartSections B hB ψ).1 b) = 0 := key _
  have hLK : L.1 ≤ K := fun b hb => (hK b).2 (mem_ker_iff.1
    (mem_ker_of_mem_ker_schemeToLTRS_map_ι_comp z P le_rfl (mem_ker_iff.2 (hL b hb))))
  have hsurj : Function.Surjective b₀ := by
    intro y
    set x := (weakChartPoint B hB ψ L).toHom.base y
    have hxW : x ∈ (W : Set X) := range_weakChartPoint_subset B hB ψ L ⟨y, rfl⟩
    obtain ⟨q, hq⟩ := (range_weakChartEmbedding A hA χ).ge (hWV hxW)
    obtain ⟨p, rfl⟩ := surjective_spfOfQuotientOn A J q
    have hp : z.toHom.base p = x := hq
    let p' : P.toScheme := ⟨p, show z.toHom.base p ∈ (W : Set X) from hp ▸ hxW⟩
    refine ⟨p', injective_spfOfQuotientOn B L ((PresheafedSpace.IsOpenImmersion.base_open
      (f := (weakChartEmbedding B hB ψ).toHom)).injective ?_)⟩
    exact (congrArg (fun φ : schemeToLTRSObj P.toScheme ⟶ X => φ.toHom.base p') hb₀).trans hp
  have hKnil : ∀ b ∈ K, IsTopologicallyNilpotent b := by
    intro b hb
    have h2 := (c_app_weakChartSections_eq_zero_iff_of_comp B hB ψ
      (schemeToLTRS.map b₀ ≫ spfwQuotientPoint B hB L) g ((Category.assoc _ _ _).trans hb₀) b).1
      (mem_ker_iff.1 (ker_le_ker_comp (schemeToLTRS.map P.ι) z W (mem_ker_iff.2 ((hK b).1 hb))))
    rw [spfPointGammaHomOn_comp_spfwQuotientPoint] at h2
    have h3 : b₀.appTop ((Scheme.ΓSpecIso (spfQuotientOn B L)).inv
        (Ideal.Quotient.mk L.1 b)) = 0 := h2
    obtain ⟨n, hn⟩ := isNilpotent_of_surjective_of_appTop_eq_zero b₀ hsurj h3
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hn
    exact IsTopologicallyNilpotent.of_pow (L.2.2 _ hn)
  have hKopen : IsOpen (K : Set B) := Submodule.isOpen_mono hLK L.2.1
  have hsymm {s} (hs : s ∈ I.ideal W) : (weakChartSectionsRingEquiv B hB ψ).symm s ∈ K := by
    change (weakChartSectionsRingEquiv B hB ψ) _ ∈ I.ideal W
    rwa [RingEquiv.apply_symm_apply]
  have hset : ((I.ideal W : Ideal _) : Set (X.presheaf.obj (op W)).α) =
      weakChartSectionsHomeomorph B hB ψ '' (K : Set B) := by
    ext s
    exact ⟨fun hs => ⟨_, hsymm hs, (weakChartSectionsRingEquiv B hB ψ).apply_symm_apply s⟩,
      by rintro ⟨b, hb, rfl⟩; exact hb⟩
  refine ⟨?_, fun s hs => ?_⟩
  · rw [hset]
    exact (weakChartSectionsHomeomorph B hB ψ).isOpenMap _ hKopen
  · have h := IsTopologicallyNilpotent.map (φ := weakChartSectionsRingEquiv B hB ψ)
      (weakChartSectionsHomeomorph B hB ψ).continuous (hKnil _ (hsymm hs))
    rwa [RingEquiv.apply_symm_apply] at h

/-- A point landing in an open `W` inside `V` kills a section over `V` as soon as it kills its
restriction to `W`: the preimages of `W` and `V` agree. -/
theorem c_app_eq_zero_of_range_subset_of_le {Y : LTRS.{u}} (f : Y ⟶ X) {V W : Opens X}
    (hWV : W ≤ V) (hf : Set.range f.toHom.base ⊆ (W : Set X)) {t : (X.presheaf.obj (op V)).α}
    (h : (f.toHom.c.app (op W)).1 ((X.presheaf.map (homOfLE hWV).op).1 t) = 0) :
    (f.toHom.c.app (op V)).1 t = 0 := by
  have heq : (Opens.map f.toHom.base).obj W = (Opens.map f.toHom.base).obj V :=
    Opens.ext (Set.ext fun y => ⟨fun hy => hWV hy, fun _ => hf (Set.mem_range_self y)⟩)
  have hnat := congrArg (fun φ => φ.1 t) (f.toHom.c.naturality (homOfLE hWV).op)
  have hiso := isIso_presheaf_map_of_opens_eq Y.presheaf heq.symm
    ((Opens.map f.toHom.base).op.map (homOfLE hWV).op)
  have hinj : Function.Injective (Y.presheaf.map
      ((Opens.map f.toHom.base).op.map (homOfLE hWV).op)).1 :=
    (TopCat.homeoOfIso ((forget₂ TopCommRingCat TopCat).mapIso (asIso _))).injective
  exact hinj ((hnat.symm.trans h).trans (map_zero _).symm)

end LocallyTopologicallyRingedSpace.IdealSheaf

namespace LocallyTopologicallyRingedSpace

open IdealSheaf

variable {X : LTRS.{u}}

/-- **The neighbourhood-basis condition passes to smaller weak affine formal opens for ideal
sheaves cut out by their sections.** Let `𝒮` be a family of ideal sheaves cut out by their sections
over the weak affine formal opens, `W ⊆ V` weak affine formal opens, and suppose the members of `𝒮`
are weak ideals of definition over `W` and their ideals of sections over `V` form a neighbourhood
basis of zero. Then their ideals of sections over `W` form a neighbourhood basis of zero. No
directedness is needed: for a weak ideal of definition `N` of `𝒪(W) ≅ B`, a member `ℐ` with `ℐ(V)`
inside the preimage of `N` under restriction has the quotient point `Spec (B/N) → W` killing
`ℐ(V)`, hence, `ℐ` being cut out over `V`, killing `ℐ(W)`: so `ℐ(W) ⊆ N`. -/
theorem hasBasis_of_le_of_isCutOutOn (𝒮 : Set (IdealSheaf X))
    (hC : ∀ I ∈ 𝒮, I.IsCutOutOn (IsWeakAffineFormalOpen X)) {V W : Opens X}
    (hV : IsWeakAffineFormalOpen X V) (hW : IsWeakAffineFormalOpen X W) (hWV : W ≤ V)
    (hweak : ∀ I ∈ 𝒮, IsWeakIdealOfDefinition (I.ideal W))
    (hbasis : (nhds (0 : (X.presheaf.obj (op V)).α)).HasBasis (· ∈ 𝒮)
      fun I : IdealSheaf X => (I.ideal V : Set (X.presheaf.obj (op V)).α)) :
    (nhds (0 : (X.presheaf.obj (op W)).α)).HasBasis (· ∈ 𝒮)
      fun I : IdealSheaf X => (I.ideal W : Set (X.presheaf.obj (op W)).α) := by
  let B := hW.chart.ring.α
  let hB := hW.chart.admissible
  let ψ := hW.chart.iso
  let e := weakChartSectionsRingEquiv B hB ψ
  let h := weakChartSectionsHomeomorph B hB ψ
  refine ⟨fun t => ⟨fun ht => ?_, fun ⟨I, hI, hIt⟩ => Filter.mem_of_superset
    ((hweak I hI).1.mem_nhds (Submodule.zero_mem _)) hIt⟩⟩
  have ht' : h ⁻¹' t ∈ nhds (0 : B) := h.continuous.continuousAt.preimage_mem_nhds
    (by rwa [weakChartSectionsHomeomorph_apply, map_zero])
  obtain ⟨O, hO, hOt⟩ := (IsLinearTopology.hasBasis_ideal (R := B)).mem_iff.mp ht'
  let L₀ := weaklyPreAdmissibleSpfIndex B hB.1
  have hNopen : IsOpen ((O ⊓ L₀.1 : Ideal B) : Set B) := by
    rw [Submodule.coe_inf]
    exact (O.toAddSubgroup.isOpen_of_mem_nhds hO).inter L₀.2.1
  let N : WeakIdealsOfDefinition B := ⟨O ⊓ L₀.1, hNopen, fun x hx => L₀.2.2 x hx.2⟩
  let res := X.presheaf.map (homOfLE hWV).op
  have hS : (fun t' => e.symm (res.1 t')) ⁻¹' (N.1 : Set B) ∈
      nhds (0 : (X.presheaf.obj (op V)).α) := by
    refine (h.symm.continuous.comp res.2).continuousAt.preimage_mem_nhds (hNopen.mem_nhds ?_)
    change e.symm (res.1 0) ∈ N.1
    rw [map_zero, map_zero]
    exact Submodule.zero_mem _
  obtain ⟨I, hI, hIS⟩ := hbasis.mem_iff.mp hS
  refine ⟨I, hI, fun s hs => ?_⟩
  let f := weakChartPoint B hB ψ N
  have hfW : Set.range f.toHom.base ⊆ (W : Set X) := range_weakChartPoint_subset B hB ψ N
  have hsec : ∀ x : (X.presheaf.obj (op W)).α, (weakChartSections B hB ψ).1 (e.symm x) = x :=
    e.apply_symm_apply
  have hkill : ∀ t' ∈ I.ideal V, (f.toHom.c.app (op V)).1 t' = 0 := by
    intro t' ht'
    refine c_app_eq_zero_of_range_subset_of_le f hWV hfW ?_
    rw [← hsec (res.1 t')]
    exact (weakChartPoint_c_app_weakChartSections_eq_zero_iff B hB ψ N _).2 (hIS ht')
  have hs0 := (hC I hI V hV W hWV s).1 hs _ f (hfW.trans hWV) hkill
  rw [← hsec s] at hs0
  have hN := (weakChartPoint_c_app_weakChartSections_eq_zero_iff B hB ψ N _).1 hs0
  have := hOt hN.1
  rwa [Set.mem_preimage, weakChartSectionsHomeomorph_apply, hsec] at this

/-- **Stacks 0AIV, the weak ideal-of-definition condition may be checked on the members of an
affine open covering, for ideal sheaves cut out by their sections.** Let `𝔛` be a formal scheme
in the sense of McQuillan and `ℐ` an ideal sheaf cut out by its sections over the affine formal
opens (`IdealSheaf.IsCutOutOn`). If `ℐ(𝔙)` is a weak ideal of definition for the members `𝔙` of a
covering of `𝔛` by affine formal opens, then `ℐ` is a weak ideal of definition.

These are the ideal sheaves of the correspondence of Stacks 0AIV with thickenings
(`McQuillanFormalScheme.weakIdealOfDefinitionEquivThickening`) and of its colimit criterion
(`McQuillanFormalScheme.isFppfColimitOfThickenings_iff_exists_isFundamentalSystem`). For an
arbitrary ideal sheaf checking the covering members is not enough
(`IdealSheaf.exists_not_isWeakIdealOfDefinitionOn_of_cover`), and the condition must then be
checked on the affine formal opens inside the covering members
(`IdealSheaf.isWeakIdealOfDefinitionOn_of_cover_of_isMcQuillanFormalScheme`). Over an affine formal
open `𝔚` inside a covering member `𝔙 ≅ Spfw A`, the ideal `ℐ(𝔚)` is the kernel of the quotient
point `Spec (A/ℐ(𝔙)) → 𝔛` (`IdealSheaf.isWeakIdealOfDefinition_of_le_of_isCutOutOn`). -/
@[stacks 0AIV "it suffices to check the weak ideal-of-definition condition on the members of an \
affine open covering: for ideal sheaves cut out by their sections over the affine formal opens \
(IdealSheaf.IsCutOutOn), the class of the correspondence with thickenings and of the colimit \
criterion; for an arbitrary ideal sheaf it is false \
(IdealSheaf.exists_not_isWeakIdealOfDefinitionOn_of_cover)"]
theorem IdealSheaf.isWeakIdealOfDefinitionOn_of_cover_of_isCutOutOn
    (hX : IsMcQuillanFormalScheme X) (I : IdealSheaf X)
    (hC : I.IsCutOutOn (IsWeakAffineFormalOpen X)) (𝒰 : Set (Opens X))
    (h𝒰 : ∀ V ∈ 𝒰, IsWeakAffineFormalOpen X V) (hcover : sSup 𝒰 = ⊤)
    (hI : ∀ V ∈ 𝒰, IsWeakIdealOfDefinition (I.ideal V)) :
    I.IsWeakIdealOfDefinitionOn (IsWeakAffineFormalOpen X) :=
  I.isWeakIdealOfDefinitionOn_of_cover_of_isMcQuillanFormalScheme hX 𝒰 hcover
    fun V hV _ hUV hU => isWeakIdealOfDefinition_of_le_of_isCutOutOn hC (h𝒰 V hV) hU hUV (hI V hV)

/-- **Stacks 0AIV, the fundamental-system condition may be checked on the members of an affine
open covering, for ideal sheaves cut out by their sections.** Let `𝔛` be a formal scheme in the
sense of McQuillan and `{ℐ_λ}` a nonempty family of ideal sheaves, directed by inclusion, each cut
out by its sections over the affine formal opens. If over the members `𝔙` of a covering of `𝔛` by
affine formal opens the `ℐ_λ(𝔙)` are weak ideals of definition forming a neighbourhood basis of
zero, then `{ℐ_λ}` is a fundamental system of weak ideals of definition.

The family is indexed, as in the source, by a directed set (nonempty, by Stacks' definition of a
directed set), with `ℐ_μ ⊆ ℐ_λ` for `μ ≥ λ`; this is the directedness asked here. Over an affine
formal open inside a single covering member no directedness is used
(`hasBasis_of_le_of_isCutOutOn`); it serves to pass to affine formal opens meeting several members.
These are the families of the colimit criterion
`McQuillanFormalScheme.isFppfColimitOfThickenings_iff_exists_isFundamentalSystem`. For arbitrary
ideal sheaves checking the covering members is not enough
(`not_forall_isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_cover`,
`not_forall_isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_hasBasis_cover`). -/
@[stacks 0AIV "it suffices to check the fundamental-system condition on the members of an affine \
open covering: for a family indexed by a directed set, as in the source, of ideal sheaves cut out \
by their sections over the affine formal opens (IdealSheaf.IsCutOutOn), the class of the colimit \
criterion; for arbitrary ideal sheaves it is false \
(not_forall_isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_hasBasis_cover)"]
theorem isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_cover_of_isCutOutOn
    (hX : IsMcQuillanFormalScheme X) (𝒮 : Set (IdealSheaf X))
    (hC : ∀ I ∈ 𝒮, I.IsCutOutOn (IsWeakAffineFormalOpen X)) (hne : 𝒮.Nonempty)
    (hdir : ∀ I ∈ 𝒮, ∀ J ∈ 𝒮, ∃ K ∈ 𝒮, ∀ W : Opens X,
      K.ideal W ≤ I.ideal W ∧ K.ideal W ≤ J.ideal W)
    (𝒰 : Set (Opens X)) (h𝒰 : ∀ V ∈ 𝒰, IsWeakAffineFormalOpen X V) (hcover : sSup 𝒰 = ⊤)
    (h𝒮 : ∀ I ∈ 𝒮, ∀ V ∈ 𝒰, IsWeakIdealOfDefinition (I.ideal V))
    (hbasis : ∀ V ∈ 𝒰, (nhds (0 : (X.presheaf.obj (op V)).α)).HasBasis (· ∈ 𝒮)
      fun I : IdealSheaf X => (I.ideal V : Set (X.presheaf.obj (op V)).α)) :
    IsFundamentalSystemOfWeakIdealsOfDefinitionOn 𝒮 (IsWeakAffineFormalOpen X) :=
  isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_cover_of_isMcQuillanFormalScheme hX 𝒮 hne hdir
    𝒰 hcover
    (fun I hI V hV _ hUV hU =>
      isWeakIdealOfDefinition_of_le_of_isCutOutOn (hC I hI) (h𝒰 V hV) hU hUV (h𝒮 I hI V hV))
    fun V hV _ hUV hU => hasBasis_of_le_of_isCutOutOn 𝒮 hC (h𝒰 V hV) hU hUV
      (fun I hI => isWeakIdealOfDefinition_of_le_of_isCutOutOn (hC I hI) (h𝒰 V hV) hU hUV
        (h𝒮 I hI V hV)) (hbasis V hV)

end LocallyTopologicallyRingedSpace

end AlgebraicGeometry

end
