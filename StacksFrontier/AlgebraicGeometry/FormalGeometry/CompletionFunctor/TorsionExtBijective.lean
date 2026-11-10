module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Algebraize
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Exactness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.TorsionEssentialImage
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.TorsionExtBijectiveAux
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.TorsionHomBijective
public import StacksCore.Tactic.StacksAttribute

/-!
# Completion is bijective on extensions when one side is ideal-power torsion, and Tag 0EHP

Let `X` be a Noetherian scheme, `ℐ ⊂ 𝒪_X` a quasi-coherent sheaf of ideals and `ℱ`, `𝒢` coherent
`𝒪_X`-modules one of which is annihilated by a power of `ℐ`. The completion functor of
Stacks 0880 is exact, so it induces a map

`Ext_X(ℱ, 𝒢) ⟶ Ext_{Coh(X, ℐ)}(ℱ^∧, 𝒢^∧)`,

and this file proves that map bijective. Together with the essential-image assertion
`Stacks.Algebraization.mem_essImage_completionFunctor_of_isSystemPowerAnnihilated` and the `Hom`
assertion `Stacks.Algebraization.completionFunctor_map_bijective_of_isPowerAnnihilated`, that is
the whole of [Stacks, Tag 0EHP].

Injectivity is the `Hom` assertion: an extension whose completion splits is split, because a
splitting of the completed sequence descends to a splitting of the original one.

Surjectivity is the content, and it is where Stacks 0889 enters. An extension
`0 ⟶ 𝒢^∧ ⟶ (E_n) ⟶ ℱ^∧ ⟶ 0` of `Coh(X, ℐ)` has one of its two maps algebraizable: when `ℱ` is
annihilated by a power of `ℐ` the quotient `ℱ^∧` is a uniformly annihilated system, so the
levelwise kernels and cokernels of the inclusion `𝒢^∧ ⟶ (E_n)` are annihilated and part (2) of
Stacks 0889 presents that inclusion as the completion of a morphism `a : 𝒢 ⟶ E'` of coherent
modules; when `𝒢` is annihilated the same applies to the projection `(E_n) ⟶ ℱ^∧` and part (1).
In either case one end of the algebraized sequence is obtained as a kernel or a cokernel, and it
is identified with `ℱ`, respectively `𝒢`, because Stacks 0889 annihilates it by a power of `ℐ`
and completion is fully faithful between annihilated coherent modules.

## Main results

* `Stacks.Algebraization.extClass_eq_zero_iff_section` and
  `Stacks.Algebraization.extClass_eq_zero_iff_retraction` — in any abelian category an extension
  has zero class exactly when it is split.
* `Stacks.Algebraization.isSystemPowerAnnihilated_completionFunctor_obj` — the completion of a
  power-annihilated coherent module is a uniformly power-annihilated system.
* `Stacks.Algebraization.isZero_of_isZero_completionFunctor_obj`,
  `Stacks.Algebraization.exists_iso_of_completionFunctor_obj_iso`,
  `Stacks.Algebraization.mono_of_mono_completionFunctor_map` and
  `Stacks.Algebraization.epi_of_epi_completionFunctor_map` — what the `Hom` assertion reflects
  across the completion functor.
* `Stacks.Algebraization.completionFunctor_mapExt_injective_of_isPowerAnnihilated`,
  `Stacks.Algebraization.completionFunctor_mapExt_surjective_of_isPowerAnnihilated` and
  `Stacks.Algebraization.completionFunctor_mapExt_bijective_of_isPowerAnnihilated` — **the `Ext`
  half of the second assertion of Tag 0EHP.**
* `Stacks.Algebraization.essImage_and_bijective_of_isPowerAnnihilated` — **[Stacks, Tag 0EHP]**,
  the three assertions together.

## Implementation notes

`Ext` is Mathlib's `CategoryTheory.Abelian.Ext` at degree one, which
`Stacks.Algebraization.extClass_eq_zero_iff_section` and
`CategoryTheory.Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum` identify with the
group of extensions under Baer sum that the source means; the `HasExt` instance is the standard
one. The comparison map is `CategoryTheory.Functor.mapExtAddHom` of the completion functor, which
is a homomorphism of abelian groups, so bijectivity is the source's assertion that it is an
isomorphism.

The abelian structure on coherent modules is the one of
`AlgebraicGeometry.CoherentAbelian.coherentModulesAbelian`, for the root coherence predicate;
the inclusion into all sheaves of modules preserves finite limits and colimits, which is how the
kernel and the cokernel taken in coherent modules are compared with the ones taken in all
modules. Those comparisons are written with the object property spelled out rather than through
a local abbreviation: a `let`-bound functor is opaque to instance search, and the two coherence
predicates of the library have to be kept apart by hand inside a `Stacks.` namespace.

## References

* [Stacks Project, Tag 0EHP](https://stacks.math.columbia.edu/tag/0EHP)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0881](https://stacks.math.columbia.edu/tag/0881)
* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 06XV](https://stacks.math.columbia.edu/tag/06XV)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

attribute [local instance] CategoryTheory.HasExt.standard

universe u

namespace Stacks.Algebraization

/-! ### Splitting criteria for the class of an extension -/

section Splitting

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasExt 𝒜]

/-- An extension has zero class exactly when it admits a section. -/
public theorem extClass_eq_zero_iff_section {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    hS.extClass = 0 ↔ ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 _ := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Abelian.Ext.covariant_sequence_exact₃ S.X₃ hS
      (Abelian.Ext.mk₀ (𝟙 S.X₃)) (zero_add 1) (by simpa using h)
    obtain ⟨s, rfl⟩ := (Abelian.Ext.mk₀_bijective S.X₃ S.X₂).surjective x
    exact ⟨s, (Abelian.Ext.mk₀_bijective S.X₃ S.X₃).injective
      (by rwa [Abelian.Ext.mk₀_comp_mk₀] at hx)⟩
  · rintro ⟨s, hs⟩
    have h := congrArg (fun ξ => (Abelian.Ext.mk₀ s).comp ξ (zero_add 1)) hS.comp_extClass
    simpa only [Abelian.Ext.mk₀_comp_mk₀_assoc, hs, Abelian.Ext.mk₀_id_comp,
      Abelian.Ext.comp_zero] using h

/-- An extension has zero class exactly when it admits a retraction. -/
public theorem extClass_eq_zero_iff_retraction {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    hS.extClass = 0 ↔ ∃ r : S.X₂ ⟶ S.X₁, S.f ≫ r = 𝟙 _ := by
  let := HasDerivedCategory.standard 𝒜
  constructor
  · intro h
    obtain ⟨y, hy⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS S.X₁
      (Abelian.Ext.mk₀ (𝟙 S.X₁)) (add_zero 1) (by simp [h])
    obtain ⟨r, rfl⟩ := (Abelian.Ext.mk₀_bijective S.X₂ S.X₁).surjective y
    exact ⟨r, (Abelian.Ext.mk₀_bijective _ _).injective
      (by simpa only [Abelian.Ext.mk₀_comp_mk₀] using hy)⟩
  · rintro ⟨r, hr⟩
    calc
      hS.extClass = hS.extClass.comp (Abelian.Ext.mk₀ (𝟙 _)) (add_zero 1) := by simp
      _ = hS.extClass.comp (Abelian.Ext.mk₀ (S.f ≫ r)) (add_zero 1) := by rw [hr]
      _ = 0 := by rw [← Abelian.Ext.mk₀_comp_mk₀]; exact hS.extClass_comp_assoc _

end Splitting

/-! ### The completion functor is exact and additive -/

section Instances

variable (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)

/-- The completion functor preserves finite limits, being exact (Stacks 0881). -/
public instance completionFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (completionFunctor X I) :=
  ((exactFunctor_iff _).mp (completionFunctor_exact X I)).1

/-- The completion functor preserves finite colimits, being exact (Stacks 0881). -/
public instance completionFunctor_preservesFiniteColimits' :
    PreservesFiniteColimits (completionFunctor X I) :=
  ((exactFunctor_iff _).mp (completionFunctor_exact X I)).2

/-- The completion functor is additive, preserving finite products. -/
public instance completionFunctor_additive : (completionFunctor X I).Additive :=
  Functor.additive_of_preserves_binary_products _

end Instances

/-! ### Transporting annihilation across the completion functor -/

section Torsion

variable {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}

omit [AlgebraicGeometry.IsNoetherian X] in
/-- Uniform annihilation of a coherent adic system transports along an isomorphism. -/
public theorem isSystemPowerAnnihilated_of_iso
    {F G : Stacks.Coherent.CoherentAdicSystems I} (e : F ≅ G)
    (hF : IsSystemPowerAnnihilated I F.obj) : IsSystemPowerAnnihilated I G.obj := by
  obtain ⟨k, hk⟩ := hF
  exact ⟨k, fun n =>
    idealPowerMultiple_eq_bot_of_iso I ((Stacks.underlyingObjIso e).app (op n)).symm k (hk n)⟩

omit [AlgebraicGeometry.IsNoetherian X] in
/-- A coherent adic system with zero terms is uniformly annihilated. -/
public theorem isSystemPowerAnnihilated_of_isZero
    (F : Stacks.Coherent.CoherentAdicSystems I) (hF : IsZero F) :
    IsSystemPowerAnnihilated I F.obj := by
  refine ⟨0, fun n => idealPowerMultiple_eq_bot_of_affine_sections_annihilated fun V _ _ x => ?_⟩
  have h : IsZero (F.obj.obj (op n)) :=
    ((evaluation ℕᵒᵖ X.Modules).obj (op n)).map_isZero ((ObjectProperty.ι _).map_isZero hF)
  have hx : x = 0 := by
    simpa using congrArg (fun f : F.obj.obj (op n) ⟶ F.obj.obj (op n) =>
      Scheme.Modules.Hom.app f V.1 x) (h.eq_of_src (𝟙 _) 0)
  rw [hx, smul_zero]

/-- **The completion of a power-annihilated coherent module is a uniformly power-annihilated
system.** Below the annihilating exponent the terms are annihilated because they are quotients by
a power of `ℐ`; above it the canonical projection is an isomorphism. -/
public theorem isSystemPowerAnnihilated_completionFunctor_obj
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hF : IsPowerAnnihilated I F.obj) :
    IsSystemPowerAnnihilated I ((completionFunctor X I).obj F).obj := by
  obtain ⟨c, hc⟩ := hF
  refine ⟨max 1 c, fun n => ?_⟩
  by_cases hn : n + 1 ≤ max 1 c
  · exact idealPowerMultiple_eq_bot_of_le
      (((completionFunctor X I).obj F).property.idealPowerMultiple_eq_bot n) hn
  · have hbot : idealPowerMultiple I (n + 1) F.obj = ⊥ :=
      idealPowerMultiple_eq_bot_of_le hc (by omega)
    have := isIso_completionProjection_of_idealPowerMultiple_eq_bot F hbot
    exact idealPowerMultiple_eq_bot_of_iso I (asIso (completionProjection X I F n)).symm _
      (idealPowerMultiple_eq_bot_of_le hc (le_max_right 1 c))

variable {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}

omit [AlgebraicGeometry.IsNoetherian X] in
/-- The kernel of a morphism of coherent modules, taken in the category of coherent modules, is
power-annihilated as soon as the kernel taken in all sheaves of modules is. -/
public theorem isPowerAnnihilated_coherentKernel (a : F ⟶ G)
    (h : IsPowerAnnihilated I (kernel (C := X.Modules) a.hom)) :
    IsPowerAnnihilated I (kernel a).obj := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, idealPowerMultiple_eq_bot_of_iso I
    (PreservesKernel.iso (ObjectProperty.ι
      (fun M : _root_.SheafOfModules.{u} X.ringCatSheaf =>
        _root_.SheafOfModules.IsCoherent M)) a) n hn⟩

omit [AlgebraicGeometry.IsNoetherian X] in
/-- The cokernel of a morphism of coherent modules, taken in the category of coherent modules, is
power-annihilated as soon as the cokernel taken in all sheaves of modules is. -/
public theorem isPowerAnnihilated_coherentCokernel (a : F ⟶ G)
    (h : IsPowerAnnihilated I (cokernel (C := X.Modules) a.hom)) :
    IsPowerAnnihilated I (cokernel a).obj := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, idealPowerMultiple_eq_bot_of_iso I
    (PreservesCokernel.iso (ObjectProperty.ι
      (fun M : _root_.SheafOfModules.{u} X.ringCatSheaf =>
        _root_.SheafOfModules.IsCoherent M)) a) n hn⟩

/-- **Completion reflects vanishing of power-annihilated coherent modules.** -/
public theorem isZero_of_isZero_completionFunctor_obj
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hM : IsPowerAnnihilated I M.obj)
    (hzero : IsZero ((completionFunctor X I).obj M)) : IsZero M := by
  refine (IsZero.iff_id_eq_zero M).2 ?_
  refine (completionFunctor_map_bijective_of_isPowerAnnihilated M M (Or.inl hM)).1 ?_
  change (completionFunctor X I).map (𝟙 M) = (completionFunctor X I).map (0 : M ⟶ M)
  rw [(completionFunctor X I).map_id, (completionFunctor X I).map_zero]
  exact hzero.eq_of_src _ _

/-- **Completion reflects isomorphisms between power-annihilated coherent modules**, and does so
through a lift of the given isomorphism of completions. -/
public theorem exists_iso_of_completionFunctor_obj_iso
    (hF : IsPowerAnnihilated I F.obj) (hG : IsPowerAnnihilated I G.obj)
    (e : (completionFunctor X I).obj F ≅ (completionFunctor X I).obj G) :
    ∃ e' : F ≅ G, (completionFunctor X I).map e'.hom = e.hom := by
  have hFG := completionFunctor_map_bijective_of_isPowerAnnihilated F G (Or.inl hF)
  have hGF := completionFunctor_map_bijective_of_isPowerAnnihilated G F (Or.inl hG)
  have hFF := completionFunctor_map_bijective_of_isPowerAnnihilated F F (Or.inl hF)
  have hGG := completionFunctor_map_bijective_of_isPowerAnnihilated G G (Or.inl hG)
  obtain ⟨f, hf⟩ := hFG.2 e.hom
  obtain ⟨g, hg⟩ := hGF.2 e.inv
  have hfg : f ≫ g = 𝟙 F := by
    refine hFF.1 ?_
    change (completionFunctor X I).map (f ≫ g) = (completionFunctor X I).map (𝟙 F)
    simp [hf, hg]
  have hgf : g ≫ f = 𝟙 G := by
    refine hGG.1 ?_
    change (completionFunctor X I).map (g ≫ f) = (completionFunctor X I).map (𝟙 G)
    simp [hf, hg]
  let : IsIso f := ⟨g, hfg, hgf⟩
  exact ⟨asIso f, hf⟩

/-- **Completion reflects epimorphisms with power-annihilated cokernel.** -/
public theorem epi_of_epi_completionFunctor_map (a : F ⟶ G)
    (hC : IsPowerAnnihilated I (cokernel (C := X.Modules) a.hom))
    [Epi ((completionFunctor X I).map a)] : Epi a := by
  have hz : IsZero ((completionFunctor X I).obj (cokernel a)) :=
    (isZero_cokernel_of_epi ((completionFunctor X I).map a)).of_iso
      (PreservesCokernel.iso (completionFunctor X I) a)
  have hz' : IsZero (cokernel a) :=
    isZero_of_isZero_completionFunctor_obj _ (isPowerAnnihilated_coherentCokernel a hC) hz
  refine Preadditive.epi_of_cancel_zero a fun {R} g hg => ?_
  obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' (cokernelIsCokernel a) g hg
  change cokernel.π a ≫ d = g at hd
  rw [← hd, hz'.eq_of_src d 0, comp_zero]

/-- **Completion reflects monomorphisms with power-annihilated kernel.** -/
public theorem mono_of_mono_completionFunctor_map (a : F ⟶ G)
    (hK : IsPowerAnnihilated I (kernel (C := X.Modules) a.hom))
    [Mono ((completionFunctor X I).map a)] : Mono a := by
  have hz : IsZero ((completionFunctor X I).obj (kernel a)) :=
    (isZero_kernel_of_mono ((completionFunctor X I).map a)).of_iso
      (PreservesKernel.iso (completionFunctor X I) a)
  have hz' : IsZero (kernel a) :=
    isZero_of_isZero_completionFunctor_obj _ (isPowerAnnihilated_coherentKernel a hK) hz
  refine Preadditive.mono_of_cancel_zero a fun {R} g hg => ?_
  obtain ⟨d, hd⟩ := KernelFork.IsLimit.lift' (kernelIsKernel a) g hg
  change d ≫ kernel.ι a = g at hd
  rw [← hd, hz'.eq_of_tgt d 0, zero_comp]

end Torsion

/-! ### Completion is bijective on extension groups -/

section Ext

variable {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
  (F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- The comparison map sends the class of a short exact sequence to the class of its completion. -/
private theorem mapExtAddHom_extClass_eq (J : X.IdealSheafData)
    {S : ShortComplex (AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)}
    (hS : S.ShortExact) :
    (completionFunctor X J).mapExtAddHom S.X₃ S.X₁ 1 hS.extClass =
      (hS.map_of_exact (completionFunctor X J)).extClass := by
  rw [Functor.mapExtAddHom_apply]
  exact (Abelian.Ext.mapExactFunctor_extClass (completionFunctor X J) hS)

/-- **Completion is injective on extension groups** when a power of `ℐ` annihilates one of the
two coherent modules: an extension whose completion splits is split, because the splitting
descends by the bijectivity of completion on morphisms. -/
public theorem completionFunctor_mapExt_injective_of_isPowerAnnihilated
    (h : IsPowerAnnihilated I F.obj ∨ IsPowerAnnihilated I G.obj) :
    Function.Injective ((completionFunctor X I).mapExtAddHom F G 1) := by
  have hzero : ∀ x : Abelian.Ext F G 1,
      (completionFunctor X I).mapExtAddHom F G 1 x = 0 → x = 0 := by
    intro x hx
    obtain ⟨E, i, p, w, hS, hxS⟩ :=
      (Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
        (AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) F G).1 x
    have hT := hS.map_of_exact (completionFunctor X I)
    have hTzero : hT.extClass = 0 :=
      (mapExtAddHom_extClass_eq I hS).symm.trans ((congrArg _ hxS).trans hx)
    have hSzero : hS.extClass = 0 := by
      rcases h with hF | hG
      · obtain ⟨s, hs⟩ := (extClass_eq_zero_iff_section hT).1 hTzero
        obtain ⟨t, ht⟩ :=
          (completionFunctor_map_bijective_of_isPowerAnnihilated F E (Or.inl hF)).2 s
        refine (extClass_eq_zero_iff_section hS).2 ⟨t, ?_⟩
        refine (completionFunctor_map_bijective_of_isPowerAnnihilated F F (Or.inl hF)).1 ?_
        change (completionFunctor X I).map (t ≫ p) = (completionFunctor X I).map (𝟙 F)
        rw [(completionFunctor X I).map_comp, (completionFunctor X I).map_id,
          show (completionFunctor X I).map t = s from ht]
        exact hs
      · obtain ⟨r, hr⟩ := (extClass_eq_zero_iff_retraction hT).1 hTzero
        obtain ⟨t, ht⟩ :=
          (completionFunctor_map_bijective_of_isPowerAnnihilated E G (Or.inr hG)).2 r
        refine (extClass_eq_zero_iff_retraction hS).2 ⟨t, ?_⟩
        refine (completionFunctor_map_bijective_of_isPowerAnnihilated G G (Or.inl hG)).1 ?_
        change (completionFunctor X I).map (i ≫ t) = (completionFunctor X I).map (𝟙 G)
        rw [(completionFunctor X I).map_comp, (completionFunctor X I).map_id,
          show (completionFunctor X I).map t = r from ht]
        exact hr
    exact hxS.symm.trans hSzero
  intro x y hxy
  exact sub_eq_zero.mp (hzero (x - y) (by rw [map_sub, hxy, sub_self]))

/-- **Completion is surjective on extension groups** when a power of `ℐ` annihilates one of the
two coherent modules. Given an extension of `ℱ^∧` by `𝒢^∧` in `Coh(X, ℐ)`, Stacks 0889
algebraizes one of its two maps — part (2) for the inclusion when `ℱ` is annihilated, part (1)
for the projection when `𝒢` is — and the remaining end of the algebraized sequence is identified
with `ℱ`, respectively `𝒢`, because both it and that end are annihilated by a power of `ℐ`. -/
public theorem completionFunctor_mapExt_surjective_of_isPowerAnnihilated
    (h : IsPowerAnnihilated I F.obj ∨ IsPowerAnnihilated I G.obj) :
    Function.Surjective ((completionFunctor X I).mapExtAddHom F G 1) := by
  intro ξ
  obtain ⟨E, i, p, w, hS, hξ⟩ :=
    (Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
      (Stacks.Coherent.CoherentAdicSystems I)
      ((completionFunctor X I).obj F) ((completionFunctor X I).obj G)).1 ξ
  have : Mono i := hS.mono_f
  have : Epi p := hS.epi_g
  rcases h with hF | hG
  · -- `ℱ` is annihilated: algebraize the monomorphism `𝒢^∧ ⟶ E`
    obtain ⟨E', a, β, hKa, hCa, hfac⟩ :=
      exists_algebraization_of_map_from_completion I G E i.hom
        (isKernelCokernelAnnihilatedByPower_f_of_shortExact I (ShortComplex.mk i p w) hS
          (isSystemPowerAnnihilated_completionFunctor_obj F hF))
    have hia : (completionFunctor X I).map a ≫ β.hom = i :=
      (ObjectProperty.hom_ext _ hfac).symm
    have : Mono ((completionFunctor X I).map a ≫ β.hom) := by rw [hia]; infer_instance
    have : Mono ((completionFunctor X I).map a) := mono_of_mono _ β.hom
    have : Mono a := mono_of_mono_completionFunctor_map a hKa
    have hCobj : IsPowerAnnihilated I (cokernel a).obj :=
      isPowerAnnihilated_coherentCokernel a hCa
    have hiff : ∀ (W : Stacks.Coherent.CoherentAdicSystems I) (φ : E ⟶ W),
        i ≫ φ = 0 ↔ (completionFunctor X I).map a ≫ β.hom ≫ φ = 0 := by
      intro W φ
      rw [← hia, Category.assoc]
    let hc := CokernelCofork.isColimitOfIsColimitOfIff (cokernelIsCokernel i)
      ((completionFunctor X I).map a) β fun _ φ => hiff _ φ
    let eβ : cokernel i ≅ cokernel ((completionFunctor X I).map a) :=
      hc.coconePointUniqueUpToIso (colimit.isColimit _)
    have heβ : β.hom ≫ cokernel.π i ≫ eβ.hom =
        cokernel.π ((completionFunctor X I).map a) := by
      simpa [eβ, hc, Category.assoc] using
        IsColimit.comp_coconePointUniqueUpToIso_hom hc (colimit.isColimit _)
          WalkingParallelPair.one
    let eP : cokernel i ≅ (completionFunctor X I).obj F :=
      (cokernelIsCokernel i).coconePointUniqueUpToIso hS.gIsCokernel
    have heP : cokernel.π i ≫ eP.hom = p := by
      simpa using IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel i)
        hS.gIsCokernel WalkingParallelPair.one
    let eC := PreservesCokernel.iso (completionFunctor X I) a
    let eComp : (completionFunctor X I).obj (cokernel a) ≅ (completionFunctor X I).obj F :=
      eC ≪≫ eβ.symm ≪≫ eP
    obtain ⟨eCF, heCF⟩ := exists_iso_of_completionFunctor_obj_iso hCobj hF eComp
    let p' : E' ⟶ F := cokernel.π a ≫ eCF.hom
    have hmap_p : (completionFunctor X I).map p' = β.hom ≫ p := by
      calc
        (completionFunctor X I).map p'
            = (completionFunctor X I).map (cokernel.π a) ≫ eComp.hom := by
              rw [show eComp.hom = (completionFunctor X I).map eCF.hom from heCF.symm]
              exact (completionFunctor X I).map_comp _ _
        _ = cokernel.π ((completionFunctor X I).map a) ≫ eβ.inv ≫ eP.hom := by
              simp only [eComp, Iso.trans_hom, Iso.symm_hom]
              rw [← Category.assoc, ← Category.assoc, PreservesCokernel.π_iso_hom]
              simp only [Category.assoc]
        _ = β.hom ≫ p := by
              rw [← heβ]
              simp only [Category.assoc, Iso.hom_inv_id_assoc]
              rw [heP]
    have wa : a ≫ p' = 0 := by
      simp only [p', ← Category.assoc, cokernel.condition, zero_comp]
    have : Epi p' := epi_comp _ _
    have hcp : IsColimit (CokernelCofork.ofπ p' wa) := by
      refine CokernelCofork.IsColimit.ofπ' p' wa fun {W} q hq => ?_
      exact ⟨eCF.inv ≫ cokernel.desc a q hq, by simp [p', Category.assoc]⟩
    have hT : (ShortComplex.mk a p' wa).ShortExact :=
      ShortComplex.ShortExact.mk' ((ShortComplex.mk a p' wa).exact_of_g_is_cokernel hcp)
        inferInstance inferInstance
    refine ⟨hT.extClass, ?_⟩
    have hM := hT.map_of_exact (completionFunctor X I)
    refine (mapExtAddHom_extClass_eq I hT).trans (Eq.trans ?_ hξ)
    exact
      ((Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
        (Stacks.Coherent.CoherentAdicSystems I) ((completionFunctor X I).obj F)
        ((completionFunctor X I).obj G)).2.1 _ _ ((completionFunctor X I).map a)
        ((completionFunctor X I).map p') _ i p w hM hS).2 ⟨β, hia, hmap_p.symm⟩
  · -- `𝒢` is annihilated: algebraize the epimorphism `E ⟶ ℱ^∧`
    obtain ⟨E', a, β0, ⟨hfac, hKa, hCa⟩, -⟩ :=
      exists_unique_algebraization_of_isNoetherian I F E p.hom
        (isKernelCokernelAnnihilatedByPower_g_of_shortExact I (ShortComplex.mk i p w) hS
          (isSystemPowerAnnihilated_completionFunctor_obj G hG))
    let β : E ≅ (completionFunctor X I).obj E' := ObjectProperty.isoMk _ β0
    have hpa : p = β.hom ≫ (completionFunctor X I).map a := ObjectProperty.hom_ext _ hfac
    have : Epi (β.hom ≫ (completionFunctor X I).map a) := by rw [← hpa]; infer_instance
    have : Epi ((completionFunctor X I).map a) := epi_of_epi β.hom _
    have : Epi a := epi_of_epi_completionFunctor_map a hCa
    have hKobj : IsPowerAnnihilated I (kernel a).obj := isPowerAnnihilated_coherentKernel a hKa
    have hiff : ∀ (W : Stacks.Coherent.CoherentAdicSystems I) (φ : W ⟶ E),
        φ ≫ p = 0 ↔ φ ≫ β.hom ≫ (completionFunctor X I).map a = 0 := by
      intro W φ
      rw [hpa]
    let hc := KernelFork.isLimitOfIsLimitOfIff (kernelIsKernel p)
      ((completionFunctor X I).map a) β fun _ φ => hiff _ φ
    let eβ : kernel p ≅ kernel ((completionFunctor X I).map a) :=
      hc.conePointUniqueUpToIso (limit.isLimit _)
    have heβ : eβ.hom ≫ kernel.ι ((completionFunctor X I).map a) = kernel.ι p ≫ β.hom := by
      simpa [eβ, hc] using
        IsLimit.conePointUniqueUpToIso_hom_comp hc (limit.isLimit _) WalkingParallelPair.zero
    let eP : kernel p ≅ (completionFunctor X I).obj G :=
      (kernelIsKernel p).conePointUniqueUpToIso hS.fIsKernel
    have heP : eP.hom ≫ i = kernel.ι p := by
      simpa using IsLimit.conePointUniqueUpToIso_hom_comp (kernelIsKernel p) hS.fIsKernel
        WalkingParallelPair.zero
    let eK := PreservesKernel.iso (completionFunctor X I) a
    have heK : eK.hom ≫ kernel.ι ((completionFunctor X I).map a) =
        (completionFunctor X I).map (kernel.ι a) := by
      simp [eK, PreservesKernel.iso_hom, kernelComparison_comp_ι]
    let eComp : (completionFunctor X I).obj (kernel a) ≅ (completionFunctor X I).obj G :=
      eK ≪≫ eβ.symm ≪≫ eP
    obtain ⟨eKG, heKG⟩ := exists_iso_of_completionFunctor_obj_iso hKobj hG eComp
    let i' : G ⟶ E' := eKG.inv ≫ kernel.ι a
    have hmap_i : (completionFunctor X I).map i' = i ≫ β.hom := by
      refine (cancel_epi eComp.hom).1 ?_
      calc
        eComp.hom ≫ (completionFunctor X I).map i'
            = (completionFunctor X I).map (kernel.ι a) := by
              rw [show eComp.hom = (completionFunctor X I).map eKG.hom from heKG.symm,
                ← (completionFunctor X I).map_comp]
              simp [i']
        _ = eK.hom ≫ kernel.ι ((completionFunctor X I).map a) := heK.symm
        _ = eComp.hom ≫ i ≫ β.hom := by
              simp only [eComp, Iso.trans_hom, Iso.symm_hom, Category.assoc]
              rw [reassoc_of% heP, ← heβ, Iso.inv_hom_id_assoc]
    have wi : i' ≫ a = 0 := by
      simp only [i', Category.assoc, kernel.condition, comp_zero]
    have : Mono i' := mono_comp _ _
    have hki : IsLimit (KernelFork.ofι i' wi) := by
      refine KernelFork.IsLimit.ofι' i' wi fun {W} k hk => ?_
      exact ⟨kernel.lift a k hk ≫ eKG.hom, by simp [i', Category.assoc]⟩
    have hT : (ShortComplex.mk i' a wi).ShortExact :=
      ShortComplex.ShortExact.mk' ((ShortComplex.mk i' a wi).exact_of_f_is_kernel hki)
        inferInstance inferInstance
    refine ⟨hT.extClass, ?_⟩
    have hM := hT.map_of_exact (completionFunctor X I)
    have hmap_i_inv : (completionFunctor X I).map i' ≫ β.inv = i := by
      rw [hmap_i, Category.assoc, β.hom_inv_id, Category.comp_id]
    have hmap_p_inv : β.inv ≫ p = (completionFunctor X I).map a := by
      rw [hpa, ← Category.assoc, β.inv_hom_id, Category.id_comp]
    refine (mapExtAddHom_extClass_eq I hT).trans (Eq.trans ?_ hξ)
    exact
      ((Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
        (Stacks.Coherent.CoherentAdicSystems I) ((completionFunctor X I).obj F)
        ((completionFunctor X I).obj G)).2.1 _ _ ((completionFunctor X I).map i')
        ((completionFunctor X I).map a) _ i p w hM hS).2
        ⟨β.symm, hmap_i_inv, hmap_p_inv⟩

/-- **Completion is bijective on extension groups** when a power of `ℐ` annihilates one of the
two coherent modules. This is the `Ext` half of the second assertion of [Stacks, Tag 0EHP]. -/
public theorem completionFunctor_mapExt_bijective_of_isPowerAnnihilated
    (h : IsPowerAnnihilated I F.obj ∨ IsPowerAnnihilated I G.obj) :
    Function.Bijective ((completionFunctor X I).mapExtAddHom F G 1) :=
  ⟨completionFunctor_mapExt_injective_of_isPowerAnnihilated F G h,
    completionFunctor_mapExt_surjective_of_isPowerAnnihilated F G h⟩

end Ext

/-! ### Tag 0EHP -/

/-- **[Stacks, Tag 0EHP].** Let `X` be a Noetherian scheme and `ℐ ⊂ 𝒪_X` a quasi-coherent sheaf
of ideals.

* Any object of `Coh(X, ℐ)` annihilated by a power of `ℐ` is in the essential image of the
  completion functor of Stacks 0880.
* If `ℱ`, `𝒢` are coherent `𝒪_X`-modules and a power of `ℐ` annihilates `ℱ` or `𝒢`, then both

  `Hom_X(ℱ, 𝒢) ⟶ Hom_{Coh(X, ℐ)}(ℱ^∧, 𝒢^∧)` and
  `Ext_X(ℱ, 𝒢) ⟶ Ext_{Coh(X, ℐ)}(ℱ^∧, 𝒢^∧)`

  are isomorphisms.

Both comparison maps are the ones induced by the completion functor, and both are homomorphisms
of abelian groups for formal reasons — the functor is additive — so their bijectivity is the
whole of the source's assertion that they are isomorphisms. -/
@[stacks 0EHP]
public theorem essImage_and_bijective_of_isPowerAnnihilated (X : Scheme.{u}) [IsNoetherian X]
    (I : X.IdealSheafData) :
    (∀ S : Stacks.Coherent.CoherentAdicSystems I, IsSystemPowerAnnihilated I S.obj →
        (completionFunctor X I).essImage S) ∧
      ∀ F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
        IsPowerAnnihilated I F.obj ∨ IsPowerAnnihilated I G.obj →
          Function.Bijective (fun f : F ⟶ G => (completionFunctor X I).map f) ∧
            Function.Bijective ((completionFunctor X I).mapExtAddHom F G 1) :=
  ⟨fun S hS => mem_essImage_completionFunctor_of_isSystemPowerAnnihilated X I S hS,
    fun F G h => ⟨completionFunctor_map_bijective_of_isPowerAnnihilated F G h,
      completionFunctor_mapExt_bijective_of_isPowerAnnihilated F G h⟩⟩

end Stacks.Algebraization

end
