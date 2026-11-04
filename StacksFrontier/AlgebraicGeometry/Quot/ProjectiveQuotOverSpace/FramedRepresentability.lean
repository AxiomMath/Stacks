/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.FramedReading
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.TwistedFreeFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.SchemeRepresentation
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.SiteRepresentable
public import StacksFrontier.AlgebraicGeometry.Quot.QuotSubfunctorRepresentedProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenLiftOverHenselianPair
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction

/-!
# `Quot^P` over a framed affine base is represented by a proper scheme

Let `F/X/B` be a Quot situation with a projective frame `X = B × ℙⁿ_ℤ` and an identification
`B ≅ h_W` with the algebraic space of a scheme `W`, and suppose `F` is pulled back from a module
`F₀` on `h_{ℙⁿ_W}` whose reading `G₀` on `ℙⁿ_W` is `𝒪(-d)^{⊕ r}`, `r ≥ 1`.  For a scheme `T` of the
site, a section of `Quot^P_{F/X/B}` over `T` is a morphism `a : T ⟶ W` together with a quotient of
`F_T`; reading the latter on `ℙⁿ_T ≅ X_T` as a quotient of `a^* G₀ ≅ 𝒪(-d)^{⊕ r}` and untwisting
by `d` (Stacks 0DP7) makes it a quotient of `𝒪^{⊕ r}` on `ℙⁿ_T`, flat over `T` with Hilbert
polynomial `t ↦ P(t + d)` (`AlgebraicGeometry.ProjectiveQuotOverSpace.framedRead`).  This reading
is injective (Stacks 03DX) and natural in `T`.  With `X_{P(·+d)}` the proper scheme representing
these quotients of `𝒪^{⊕ r}` (the scheme-level Stacks 0DPA), `Quot^P_{F/X/B}` is therefore
represented by `X_{P(·+d)} ×_ℤ W`, which is proper over `W ≅ B`.

## Main results

* `AlgebraicGeometry.ProjectiveQuotOverSpace.framedRead_injective`,
  `AlgebraicGeometry.ProjectiveQuotOverSpace.framedRead_baseChange`: the objectwise reading.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.isRepresentedProper_hilbertSubfunctor_framed`.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
* [Stacks Project, Tag 0DP7](https://stacks.math.columbia.edu/tag/0DP7)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

namespace AlgebraicGeometry.ProjectiveQuotOverSpace

open ProjectiveQuot

universe u

variable {B : BigFppfSite.{u}} {n : ℕ}
  {D : Space.QuotSituation B integerBase B.contains_integerBase}
  (E : ProjectiveFrame B n D) {W : BigFppfOver B integerBase B.contains_integerBase}
  (φ : schemeSpace W ≅ D.Y)

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-! ### The morphism to `W` -/

/-- The morphism `T ⟶ W` underlying a morphism `h_T ⟶ B ≅ h_W`. -/
def framedBase {T : BigFppfOver B integerBase B.contains_integerBase}
    (b : schemeSpace T ⟶ D.Y) : T ⟶ W :=
  Yoneda.fullyFaithful.preimage (b ≫ φ.inv).hom

/-- A morphism of the site is determined by the morphism of algebraic spaces it induces. -/
private theorem schemeSpaceMap_inj {T T' : BigFppfOver B integerBase B.contains_integerBase}
    {g g' : T ⟶ T'} (h : schemeSpaceMap g = schemeSpaceMap g') : g = g' :=
  Yoneda.fullyFaithful.map_injective (congrArg (·.hom) h)

/-- The morphism `h_T ⟶ h_W` induced by `framedBase φ b` is `b ≫ φ.inv`. -/
theorem schemeSpaceMap_framedBase {T : BigFppfOver B integerBase B.contains_integerBase}
    (b : schemeSpace T ⟶ D.Y) :
    schemeSpaceMap (framedBase φ b) = b ≫ φ.inv :=
  ObjectProperty.hom_ext _ (Yoneda.fullyFaithful.map_preimage _)

/-- A morphism `b : h_T ⟶ B` factors as the morphism induced by `framedBase φ b` followed by
`φ.hom`. -/
theorem framedBase_spec {T : BigFppfOver B integerBase B.contains_integerBase}
    (b : schemeSpace T ⟶ D.Y) :
    b = schemeSpaceMap (framedBase φ b) ≫ φ.hom := by
  simp [schemeSpaceMap_framedBase]

/-- `framedBase φ` sends the morphism `h_T ⟶ B` induced by `a : T ⟶ W` back to `a`. -/
theorem framedBase_schemeSpaceMap {T : BigFppfOver B integerBase B.contains_integerBase}
    (a : T ⟶ W) : framedBase φ (schemeSpaceMap a ≫ φ.hom) = a := by
  apply schemeSpaceMap_inj
  rw [schemeSpaceMap_framedBase, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- `framedBase φ` is compatible with precomposition by a morphism `g : T' ⟶ T`. -/
theorem framedBase_comp {T T' : BigFppfOver B integerBase B.contains_integerBase} (g : T' ⟶ T)
    (b : schemeSpace T ⟶ D.Y) :
    framedBase φ (schemeSpaceMap g ≫ b) = g ≫ framedBase φ b := by
  apply schemeSpaceMap_inj
  rw [schemeSpaceMap_framedBase, schemeSpaceMap_comp, schemeSpaceMap_framedBase, Category.assoc]

/-! ### Quotients of `F_T` read as quotients of `𝒪^{⊕ r}` on `ℙⁿ_T` -/

variable (F₀ : Space.Modules.{u, u} B integerBase B.contains_integerBase
  (repSpace (projectiveSite B n W)).1 (repSpace (projectiveSite B n W)).2)
  (hF₀ : F₀.IsQuasicoherentOnSite) (κ : D.F ≅ framedModule E φ F₀)
  {d r : ℕ}

/-- The framed reading of `K` is the kernel of the reading of `F_T ⟶ F_T / K`, transported along
`AlgebraicGeometry.ProjectiveQuotOverSpace.framedReadingIso`. -/
theorem framedSubobject_eq_subobjectIsoEquiv (T : Space.SchemesOver D.Y)
    (m : projectiveSite B n T.left ⟶ projectiveSite B n W)
    (hm : (spaceIsoY E T).hom ≫ framedProjection E φ T =
      Space.representedSpaceMap B integerBase B.contains_integerBase m)
    (K : Subobject (D.baseChangeModule T)) :
    framedSubobject E φ F₀ hF₀ κ T m hm K =
      subobjectIsoEquiv (framedReadingIso E φ F₀ hF₀ κ T m hm).symm
        (kernelSubobject ((readingY E T).map (cokernel.π K.arrow))) :=
  (subobjectIsoEquiv_kernelSubobject (framedReadingIso E φ F₀ hF₀ κ T m hm).symm
    ((readingY E T).map (cokernel.π K.arrow))).symm

/-- **The quotient by the framed reading of `K` is the reading of `F_T / K`**, for a quasi-coherent
quotient. -/
def framedSubobjectCokernelIso (T : Space.SchemesOver D.Y)
    (m : projectiveSite B n T.left ⟶ projectiveSite B n W)
    (hm : (spaceIsoY E T).hom ≫ framedProjection E φ T =
      Space.representedSpaceMap B integerBase B.contains_integerBase m)
    (K : Subobject (D.baseChangeModule T)) (hK : (D.quotientModule T K).IsQuasicoherentOnSite) :
    cokernel (framedSubobject E φ F₀ hF₀ κ T m hm K).arrow ≅
      (readingY E T).obj (cokernel K.arrow) :=
  haveI := epi_readingY_map_cokernel_π E T K hK
  haveI : Epi ((framedReadingIso E φ F₀ hF₀ κ T m hm).hom ≫
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj (projectiveSite B n T.left)) (projectiveSite B n T.left).left.property).map
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
          (projectiveSite B n T.left)).inverse.map
        ((Space.modulePullback B integerBase B.contains_integerBase (spaceIsoY E T).hom).map
          (cokernel.π K.arrow)))) := epi_comp _ _
  Abelian.cokernelKernelSubobjectIso ((framedReadingIso E φ F₀ hF₀ κ T m hm).hom ≫
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((𝒯).obj (projectiveSite B n T.left)) (projectiveSite B n T.left).left.property).map
      ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
          (projectiveSite B n T.left)).inverse.map
        ((Space.modulePullback B integerBase B.contains_integerBase (spaceIsoY E T).hom).map
          (cokernel.π K.arrow))))

/-- **A submodule `K ⊆ F_T` read as a submodule of `𝒪^{⊕ r}` on `ℙⁿ_T`**, for `a : T ⟶ W` over
`B ≅ h_W`: the framed reading of `K` in `a^* G₀ ≅ a^* 𝒪(-d)^{⊕ r}`, untwisted by `d`. -/
def framedFreeSubobject (ε : framedBaseReading F₀ ≅ twist (-(d : ℤ)) (freeModule n r ((𝒯).obj W)))
    (T : Space.SchemesOver D.Y) (a : T.left ⟶ W)
    (ha : T.hom = schemeSpaceMap a ≫ φ.hom) (K : Subobject (D.baseChangeModule T)) :
    Subobject (freeModule n r ((𝒯).obj T.left)) :=
  twistedFreeSubobjectEquiv (n := n) (r := r) (d := d) (W := (𝒯).obj W)
    (G := framedBaseReading F₀) ε ((𝒯).map a)
    (framedSubobject E φ F₀ hF₀ κ T (projectiveSiteMap B n a)
      (spaceIsoY_hom_framedProjection E φ T a ha) K)

/-- A quasi-coherent quotient of `F_T` is in `Quot_{F/X/B}(T)` exactly when its reading on `ℙⁿ_T`
is a flat family (Stacks 09TR read on `ℙⁿ_T`). -/
theorem mem_properlySupportedQuotients_iff_reading (T : Space.SchemesOver D.Y)
    (K : Subobject (D.baseChangeModule T)) (hK : (cokernel K.arrow).IsQuasicoherentOnSite) :
    K ∈ D.properlySupportedQuotients T ↔
      IsFlatFamily (n := n) (T := (𝒯).obj T.left) ((reading E T).obj (D.quotientModule T K)) := by
  rw [mem_properlySupportedQuotients_iff E T K hK]
  exact ⟨isFlatFamily_of_iso (readingSubobjectCokernelIso E T K hK),
    isFlatFamily_of_iso (readingSubobjectCokernelIso E T K hK).symm⟩

/-- **Membership in `Quot^P` is read on the framed reading**: a quasi-coherent quotient of `F_T` is
in `Quot^P(T)` exactly when the quotient of `a^* G₀` by its framed reading is a flat family with
fibrewise Hilbert polynomial `P`. -/
theorem mem_hilbertQuotients_iff_framedSubobject (p : Polynomial ℚ) (T : Space.SchemesOver D.Y)
    (m : projectiveSite B n T.left ⟶ projectiveSite B n W)
    (hm : (spaceIsoY E T).hom ≫ framedProjection E φ T =
      Space.representedSpaceMap B integerBase B.contains_integerBase m)
    (K : Subobject (D.baseChangeModule T)) (hK : (cokernel K.arrow).IsQuasicoherentOnSite) :
    K ∈ hilbertQuotients E p T ↔
      IsFlatFamily (cokernel (framedSubobject E φ F₀ hF₀ κ T m hm K).arrow) ∧
        HasFibreHilbertPolynomial p (cokernel (framedSubobject E φ F₀ hF₀ κ T m hm K).arrow) := by
  let e : cokernel (framedSubobject E φ F₀ hF₀ κ T m hm K).arrow ≅
      (reading E T).obj (D.quotientModule T K) :=
    framedSubobjectCokernelIso E φ F₀ hF₀ κ T m hm K hK
  change K ∈ D.properlySupportedQuotients T ∧ _ ↔ _
  rw [mem_properlySupportedQuotients_iff_reading E T K hK]
  exact ⟨fun ⟨hf, hh⟩ =>
      ⟨isFlatFamily_of_iso e.symm hf, hasFibreHilbertPolynomial_of_iso hf.1 e.symm hh⟩,
    fun ⟨hf, hh⟩ => ⟨isFlatFamily_of_iso e hf, hasFibreHilbertPolynomial_of_iso hf.1 e hh⟩⟩

/-- **Membership in `Quot^P` is read on `𝒪^{⊕ r}`**: a quasi-coherent quotient of `F_T` is in
`Quot^P(T)` exactly when the corresponding quotient of `𝒪^{⊕ r}` on `ℙⁿ_T` is a flat family with
fibrewise Hilbert polynomial `t ↦ P(t + d)`. -/
theorem mem_hilbertQuotients_iff_framedFreeSubobject
    (ε : framedBaseReading F₀ ≅ twist (-(d : ℤ)) (freeModule n r ((𝒯).obj W))) (p : Polynomial ℚ)
    (T : Space.SchemesOver D.Y) (a : T.left ⟶ W) (ha : T.hom = schemeSpaceMap a ≫ φ.hom)
    (K : Subobject (D.baseChangeModule T)) (hK : (cokernel K.arrow).IsQuasicoherentOnSite) :
    K ∈ hilbertQuotients E p T ↔
      framedFreeSubobject E φ F₀ hF₀ κ ε T a ha K ∈
        hilbertFamilies n r (shiftPolynomial p d) ((𝒯).obj T.left) :=
  (mem_hilbertQuotients_iff_framedSubobject E φ F₀ hF₀ κ p T _
    (spaceIsoY_hom_framedProjection E φ T a ha) K hK).trans
    (mem_hilbertFamilies_twistedFreeSubobjectEquiv_iff (n := n) (r := r) (d := d)
      (W := (𝒯).obj W) (G := framedBaseReading F₀) ε ((𝒯).map a) p _)

/-- For equal functors `G = G'`, the kernel subobjects of `G.map f` and `G'.map f` are
heterogeneously equal. -/
theorem heq_kernelSubobject_map_of_eq {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] [Abelian 𝒟]
    {G G' : 𝒞 ⥤ 𝒟} (h : G = G') {X Y : 𝒞} (f : X ⟶ Y) :
    HEq (kernelSubobject (G.map f)) (kernelSubobject (G'.map f)) := by
  subst h
  rfl

/-- The reading of `K` is the kernel of the reading of the projection `F_T ⟶ F_T / K`. -/
theorem readingSubobject_eq_kernelSubobject (T : Space.SchemesOver D.Y)
    (K : Subobject (D.baseChangeModule T)) :
    readingSubobject E T K = kernelSubobject ((readingY E T).map (cokernel.π K.arrow)) :=
  eq_of_heq (heq_kernelSubobject_map_of_eq (readingY_eq E T).symm (cokernel.π K.arrow))

/-- **The framed reading is injective on quasi-coherent quotients** (Stacks 03DX). -/
theorem framedSubobject_injective (T : Space.SchemesOver D.Y)
    (m : projectiveSite B n T.left ⟶ projectiveSite B n W)
    (hm : (spaceIsoY E T).hom ≫ framedProjection E φ T =
      Space.representedSpaceMap B integerBase B.contains_integerBase m)
    {K K' : Subobject (D.baseChangeModule T)} (hK : (cokernel K.arrow).IsQuasicoherentOnSite)
    (hK' : (cokernel K'.arrow).IsQuasicoherentOnSite)
    (h : framedSubobject E φ F₀ hF₀ κ T m hm K = framedSubobject E φ F₀ hF₀ κ T m hm K') :
    K = K' := by
  rw [framedSubobject_eq_subobjectIsoEquiv, framedSubobject_eq_subobjectIsoEquiv] at h
  have h' := (subobjectIsoEquiv (framedReadingIso E φ F₀ hF₀ κ T m hm).symm).injective h
  rw [← readingSubobject_eq_kernelSubobject, ← readingSubobject_eq_kernelSubobject] at h'
  exact congrArg Subtype.val ((qcohQuotientEquiv E T).injective <|
    Subtype.ext ((qcohQuotientEquiv_apply_coe E T ⟨K, hK⟩).trans
      (h'.trans (qcohQuotientEquiv_apply_coe E T ⟨K', hK'⟩).symm)))

/-- **Every quasi-coherent quotient of the framed reading comes from one of `F_T`**
(Stacks 03DX). -/
theorem exists_framedSubobject_eq (T : Space.SchemesOver D.Y)
    (m : projectiveSite B n T.left ⟶ projectiveSite B n W)
    (hm : (spaceIsoY E T).hom ≫ framedProjection E φ T =
      Space.representedSpaceMap B integerBase B.contains_integerBase m)
    (K₁ : Subobject ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
        (associatedBigEtaleSite B) m.left)).obj (framedBaseReading F₀)))
    (hK₁ : SheafOfModules.IsQuasicoherent (cokernel K₁.arrow)) :
    ∃ (K : Subobject (D.baseChangeModule T)) (_ : (cokernel K.arrow).IsQuasicoherentOnSite),
      framedSubobject E φ F₀ hF₀ κ T m hm K = K₁ := by
  let e := (framedReadingIso E φ F₀ hF₀ κ T m hm).symm
  let K' : Subobject ((reading E T).obj (D.baseChangeModule T)) := (subobjectIsoEquiv e).symm K₁
  have hK'e : subobjectIsoEquiv e K' = K₁ := (subobjectIsoEquiv e).apply_symm_apply K₁
  obtain ⟨i⟩ := nonempty_cokernel_subobjectIsoEquiv_iso e K'
  rw [hK'e] at i
  have hqc : SheafOfModules.IsQuasicoherent (cokernel K'.arrow) :=
    (SheafOfModules.isQuasicoherent _).prop_of_iso i hK₁
  let K := (qcohQuotientEquiv E T).symm ⟨K', hqc⟩
  have hK : readingSubobject E T K.1 = K' :=
    (qcohQuotientEquiv_apply_coe E T K).symm.trans
      (congrArg Subtype.val ((qcohQuotientEquiv E T).apply_symm_apply ⟨K', hqc⟩))
  refine ⟨K.1, K.2, ?_⟩
  rwa [framedSubobject_eq_subobjectIsoEquiv, ← readingSubobject_eq_kernelSubobject, hK]

/-- The framed reading along equal morphisms `ℙⁿ_T ⟶ ℙⁿ_W`, compared through the identification
of the inverse images. -/
theorem framedSubobject_congr (T : Space.SchemesOver D.Y)
    {m₁ m₂ : projectiveSite B n T.left ⟶ projectiveSite B n W} (h : m₁ = m₂)
    (hm₁ : (spaceIsoY E T).hom ≫ framedProjection E φ T =
      Space.representedSpaceMap B integerBase B.contains_integerBase m₁)
    (hm₂ : (spaceIsoY E T).hom ≫ framedProjection E φ T =
      Space.representedSpaceMap B integerBase B.contains_integerBase m₂)
    (K : Subobject (D.baseChangeModule T)) :
    framedSubobject E φ F₀ hF₀ κ T m₁ hm₁ K =
      subobjectIsoEquiv ((Scheme.Modules.pullbackCongr
          (congrArg (fun m => _root_.AlgebraicGeometry.SmallEtale.schemeHom
            (associatedBigEtaleSite B) m.left) h.symm)).app (framedBaseReading F₀))
        (framedSubobject E φ F₀ hF₀ κ T m₂ hm₂ K) := by
  subst h
  rw [subobjectIsoEquiv_apply]
  exact (Subobject.map_id _).symm

/-- The two spellings of the composition law of inverse images along `ℙⁿ_T ⟶ ℙⁿ_{T''} ⟶ ℙⁿ_W`
agree. -/
theorem pullbackComp_inv_eq_pullbackCompIso
    {T T'' : BigFppfOver B integerBase B.contains_integerBase} (g : T ⟶ T'') (a'' : T'' ⟶ W)
    (h₁ : projectiveSpaceOverMap n ((𝒯).map g) ≫ projectiveSpaceOverMap n ((𝒯).map a'') =
      projectiveSpaceOverMap n ((𝒯).map (g ≫ a'')))
    (h𝒯 : (𝒯).map g ≫ (𝒯).map a'' = (𝒯).map (g ≫ a''))
    (G : (projectiveSpaceOver n ((𝒯).obj W)).Modules) :
    ((Scheme.Modules.pullbackCongr h₁).app G).inv ≫
        ((Scheme.Modules.pullbackComp (projectiveSpaceOverMap n ((𝒯).map g))
          (projectiveSpaceOverMap n ((𝒯).map a''))).app G).inv =
      (pullbackCompIso ((𝒯).map g) ((𝒯).map a'') h𝒯 G).hom := by
  unfold pullbackCompIso
  rw [Iso.symm_hom, asIso_inv, ← cancel_epi (pullbackCompCongrApp
    (projectiveSpaceOverMap n ((𝒯).map g)) (projectiveSpaceOverMap n ((𝒯).map a''))
    ((projectiveSpaceOverMap_comp n ((𝒯).map g) ((𝒯).map a'')).trans
      (congrArg (projectiveSpaceOverMap n) h𝒯)) G), IsIso.hom_inv_id]
  unfold pullbackCompCongrApp
  rw [Category.assoc, Iso.app_inv, Iso.app_inv, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  rfl

/-- **The reading on `𝒪^{⊕ r}` commutes with pullback of quotients**: for `g : T ⟶ T''` over
`a'' : T'' ⟶ W`, the submodule of `𝒪^{⊕ r}` on `ℙⁿ_T` corresponding to the pullback of `K` is the
base change of the one corresponding to `K`. -/
theorem framedFreeSubobject_quotientPullback
    (ε : framedBaseReading F₀ ≅ twist (-(d : ℤ)) (freeModule n r ((𝒯).obj W)))
    {T T'' : Space.SchemesOver D.Y} (g : T ⟶ T'') (a'' : T''.left ⟶ W)
    (ha'' : T''.hom = schemeSpaceMap a'' ≫ φ.hom)
    (ha : T.hom = schemeSpaceMap (g.left ≫ a'') ≫ φ.hom)
    (K : Subobject (D.baseChangeModule T'')) (hK : (D.quotientModule T'' K).IsQuasicoherentOnSite) :
    framedFreeSubobject E φ F₀ hF₀ κ ε T (g.left ≫ a'') ha (D.quotientPullback g K) =
      baseChange ((𝒯).map g.left) (framedFreeSubobject E φ F₀ hF₀ κ ε T'' a'' ha'' K) := by
  have hmm : projectiveSiteMap B n (g.left ≫ a'') =
      projectiveSiteMap B n g.left ≫ projectiveSiteMap B n a'' := projectiveSiteMap_comp _ _
  have hT := spaceIsoY_hom_framedProjection E φ T'' a'' ha''
  have hTc : (spaceIsoY E T).hom ≫ framedProjection E φ T =
      Space.representedSpaceMap B integerBase B.contains_integerBase
        (projectiveSiteMap B n g.left ≫ projectiveSiteMap B n a'') := by
    rw [← hmm]
    exact spaceIsoY_hom_framedProjection E φ T _ ha
  have h𝒯 : (𝒯).map g.left ≫ (𝒯).map a'' = (𝒯).map (g.left ≫ a'') := ((𝒯).map_comp _ _).symm
  refine Eq.trans ?_ (twistedFreeSubobjectEquiv_subobjectPullback (n := n) (r := r) (d := d)
    (W := (𝒯).obj W) (G := framedBaseReading F₀) ε ((𝒯).map g.left) ((𝒯).map a'') h𝒯
    (framedSubobject E φ F₀ hF₀ κ T'' (projectiveSiteMap B n a'') hT K))
  unfold framedFreeSubobject
  congr 1
  rw [framedSubobject_congr E φ F₀ hF₀ κ T hmm _ hTc,
    framedSubobject_quotientPullback E φ F₀ hF₀ κ g (projectiveSiteMap B n a'') hT hTc K hK,
    subobjectIsoEquiv_kernelSubobject]
  unfold subobjectPullback
  apply kernelSubobject_congr
  rw [← pullbackComp_inv_eq_pullbackCompIso g.left a''
    (((projectiveSpaceOverMap_comp n ((𝒯).map g.left) ((𝒯).map a''))).trans
      (congrArg (projectiveSpaceOverMap n) h𝒯)) h𝒯 (framedBaseReading F₀),
    Category.assoc]
  have hi : inv ((Scheme.Modules.pullbackComp
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (projectiveSiteMap B n g.left).left)
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (projectiveSiteMap B n a'').left)).hom.app (framedBaseReading F₀)) =
      ((Scheme.Modules.pullbackComp
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (projectiveSiteMap B n g.left).left)
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (projectiveSiteMap B n a'').left)).app (framedBaseReading F₀)).inv :=
    IsIso.Iso.inv_hom ((Scheme.Modules.pullbackComp
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (projectiveSiteMap B n g.left).left)
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
        (projectiveSiteMap B n a'').left)).app (framedBaseReading F₀))
  rw [hi]
  rfl

/-- The submodule of `𝒪^{⊕ r}` corresponding to `K` does not depend on the proof that `T`
lies over `a`, and agrees for equal morphisms `a₁ = a₂ : T ⟶ W`. -/
theorem framedFreeSubobject_congr
    (ε : framedBaseReading F₀ ≅ twist (-(d : ℤ)) (freeModule n r ((𝒯).obj W)))
    (T : Space.SchemesOver D.Y) {a₁ a₂ : T.left ⟶ W} (h : a₁ = a₂)
    (ha₁ : T.hom = schemeSpaceMap a₁ ≫ φ.hom) (ha₂ : T.hom = schemeSpaceMap a₂ ≫ φ.hom)
    (K : Subobject (D.baseChangeModule T)) :
    framedFreeSubobject E φ F₀ hF₀ κ ε T a₁ ha₁ K =
      framedFreeSubobject E φ F₀ hF₀ κ ε T a₂ ha₂ K := by
  subst h
  rfl

/-! ### The objectwise reading of `Quot^P` -/

/-- **A section of `Quot^P` over a scheme `T` of the site, read on `𝒪^{⊕ r}`**: its morphism
`T ⟶ W` and the corresponding quotient of `𝒪^{⊕ r}` on `ℙⁿ_T`. -/
def framedRead (ε : framedBaseReading F₀ ≅ twist (-(d : ℤ)) (freeModule n r ((𝒯).obj W)))
    {T : BigFppfOver B integerBase B.contains_integerBase} (x : Space.QuotFamilyOver D T) :
    (T ⟶ W) × Subobject (freeModule n r ((𝒯).obj T)) :=
  (framedBase φ x.toBase, framedFreeSubobject E φ F₀ hF₀ κ ε (CostructuredArrow.mk x.toBase)
    (framedBase φ x.toBase) (framedBase_spec φ x.toBase) x.subobject)

/-- **The objectwise reading is injective.** -/
theorem framedRead_injective
    (ε : framedBaseReading F₀ ≅ twist (-(d : ℤ)) (freeModule n r ((𝒯).obj W)))
    {T : BigFppfOver B integerBase B.contains_integerBase} {x y : Space.QuotFamilyOver D T}
    (h : framedRead E φ F₀ hF₀ κ ε x = framedRead E φ F₀ hF₀ κ ε y) : x = y := by
  obtain ⟨b, K, hK⟩ := x
  obtain ⟨b', K', hK'⟩ := y
  obtain rfl : b = b' := by
    rw [framedBase_spec φ b, framedBase_spec φ b']
    exact congrArg (fun a => schemeSpaceMap a ≫ φ.hom) (congrArg Prod.fst h)
  have h₂ := congrArg Prod.snd h
  dsimp only [framedRead, framedFreeSubobject] at h₂
  have h₃ := (twistedFreeSubobjectEquiv (n := n) (r := r) (d := d) (W := (𝒯).obj W)
    (G := framedBaseReading F₀) ε ((𝒯).map (framedBase φ b))).injective h₂
  obtain rfl := framedSubobject_injective E φ F₀ hF₀ κ _ _ _ hK.1.1.1 hK'.1.1.1 h₃
  rfl

/-- **The objectwise reading is natural**: pulling a section back along `g : T' ⟶ T` precomposes
its morphism to `W` with `g` and base changes its quotient of `𝒪^{⊕ r}` along `ℙⁿ_{T'} ⟶ ℙⁿ_T`. -/
theorem framedRead_baseChange
    (ε : framedBaseReading F₀ ≅ twist (-(d : ℤ)) (freeModule n r ((𝒯).obj W)))
    {T T' : BigFppfOver B integerBase B.contains_integerBase} (g : T' ⟶ T)
    (x : Space.QuotFamilyOver D T) :
    framedRead E φ F₀ hF₀ κ ε (x.baseChange g) =
      (g ≫ (framedRead E φ F₀ hF₀ κ ε x).1,
        baseChange ((𝒯).map g) (framedRead E φ F₀ hF₀ κ ε x).2) := by
  have hb : framedBase φ
      ((schemeSpaceFunctor B integerBase B.contains_integerBase).map g ≫ x.toBase) =
      g ≫ framedBase φ x.toBase := framedBase_comp φ g x.toBase
  have ha : (CostructuredArrow.mk ((schemeSpaceFunctor B integerBase B.contains_integerBase).map g ≫
      x.toBase) : Space.SchemesOver D.Y).hom =
      schemeSpaceMap ((Space.QuotFamilyOver.restrict g x.toBase).left ≫ framedBase φ x.toBase) ≫
        φ.hom := by
    have h := framedBase_spec φ ((schemeSpaceFunctor B integerBase B.contains_integerBase).map g ≫
      x.toBase)
    rwa [hb] at h
  exact Prod.ext hb <| (framedFreeSubobject_congr E φ F₀ hF₀ κ ε
    (CostructuredArrow.mk ((schemeSpaceFunctor B integerBase B.contains_integerBase).map g ≫
      x.toBase)) hb (framedBase_spec φ _) ha _).trans <|
    framedFreeSubobject_quotientPullback E φ F₀ hF₀ κ ε
    (Space.QuotFamilyOver.restrict g x.toBase) (framedBase φ x.toBase)
    (framedBase_spec φ x.toBase) ha x.subobject x.mem.1.1.1

/-! ### Representability -/

include φ F₀ hF₀ κ in
/-- **Stacks 0DPB over a framed affine base, in terms of representability.**  Let `F/X/B` be a
Quot situation with a projective frame `X = B × ℙⁿ_ℤ` and `B ≅ h_W`, and suppose `F` is pulled
back from a module `F₀` on `h_{ℙⁿ_W}` read on `ℙⁿ_W` as `𝒪(-d)^{⊕ r}`, `r ≥ 1`.  Then
`Quot^P_{F/X/B}` is represented by the scheme `X_{P(·+d)} ×_ℤ W`, proper over `B`, where
`X_{P(·+d)}` represents the quotients of `𝒪^{⊕ r}` on `ℙⁿ` with Hilbert polynomial `t ↦ P(t + d)`
(the scheme-level Stacks 0DPA). -/
theorem isRepresentedProper_hilbertSubfunctor_framed {d r : ℕ} (hr : 1 ≤ r)
    (c : framedBaseReading F₀ ≅ twist (-(d : ℤ)) (freeModule n r ((𝒯).obj W)))
    (p : Polynomial ℚ) : D.IsRepresentedProper (hilbertSubfunctor E p) := by
  obtain ⟨X, hXp, ⟨hX⟩⟩ := exists_isProper_iso_hilbertFunctor.{u} n r hr (shiftPolynomial p d)
  have : IsProper (terminal.from X) := hXp
  let Zs := pullback (terminal.from X) (terminal.from ((𝒯).obj W))
  have hZs : B.Contains Zs := Space.contains_of_locallyOfFiniteType_of_quasiCompact B integerBase
    B.contains_integerBase (Y₀ := W) (pullback.snd (terminal.from X) (terminal.from ((𝒯).obj W)))
  let Z : BigFppfOver B integerBase B.contains_integerBase := CurveFamily.ofScheme Zs hZs
  let aZ : Z ⟶ W :=
    CurveFamily.homOfScheme (pullback.snd (terminal.from X) (terminal.from ((𝒯).obj W)))
  let ξ : (hilbertFunctor n r (shiftPolynomial p d)).obj (Opposite.op Zs) :=
    hX.inv.app (Opposite.op Zs) ⟨pullback.fst (terminal.from X) (terminal.from ((𝒯).obj W))⟩
  let T₀ : Space.SchemesOver D.Y := CostructuredArrow.mk (schemeSpaceMap aZ ≫ φ.hom)
  have ha₀ : T₀.hom = schemeSpaceMap aZ ≫ φ.hom := rfl
  let tfse := twistedFreeSubobjectEquiv (n := n) (r := r) (d := d) (W := (𝒯).obj W)
    (G := framedBaseReading F₀) c ((𝒯).map aZ)
  let K₁ := tfse.symm ξ.1
  have hK₁ := (mem_hilbertFamilies_twistedFreeSubobjectEquiv_iff (n := n) (r := r) (d := d)
    (W := (𝒯).obj W) (G := framedBaseReading F₀) c ((𝒯).map aZ) p K₁).2
    (by
      change tfse (tfse.symm ξ.1) ∈ _
      exact (tfse.apply_symm_apply ξ.1).symm ▸ ξ.2)
  obtain ⟨K, hKqc, hK⟩ := exists_framedSubobject_eq E φ F₀ hF₀ κ T₀ (projectiveSiteMap B n aZ)
    (spaceIsoY_hom_framedProjection E φ T₀ aZ ha₀) K₁ (isQuasicoherent_of_isFlatFamily T₀ hK₁.1)
  have hKmem : K ∈ hilbertQuotients E p T₀ :=
    (mem_hilbertQuotients_iff_framedSubobject E φ F₀ hF₀ κ p T₀ _ _ K hKqc).2
      (by rwa [hK])
  let x₀ : Space.QuotFamilyOver D Z := ⟨schemeSpaceMap aZ ≫ φ.hom, K, hKmem.1⟩
  have hread₀ : framedRead E φ F₀ hF₀ κ c x₀ = (aZ, ξ.1) := by
    refine Prod.ext (framedBase_schemeSpaceMap φ aZ) ?_
    refine (framedFreeSubobject_congr E φ F₀ hF₀ κ c T₀ (framedBase_schemeSpaceMap φ aZ)
      (framedBase_spec φ _) ha₀ K).trans ?_
    change tfse (framedSubobject E φ F₀ hF₀ κ T₀ (projectiveSiteMap B n aZ) _ K) = ξ.1
    rw [hK]
    exact tfse.apply_symm_apply ξ.1
  let Q := hilbertSubfunctor E p
  let u : Q.toFunctor.obj (Opposite.op Z) := ⟨x₀, hKmem⟩
  have hreadψ : ∀ {T : BigFppfOver B integerBase B.contains_integerBase} (g : T ⟶ Z),
      framedRead E φ F₀ hF₀ κ c (Q.toFunctor.map g.op u).1 =
        (g ≫ aZ, baseChange ((𝒯).map g) ξ.1) := by
    intro T g
    change framedRead E φ F₀ hF₀ κ c (x₀.baseChange g) = _
    rw [framedRead_baseChange, hread₀]
  have hξ : ∀ {S : Scheme.{u}} (h : S ⟶ Zs),
      baseChange h ξ.1 = (hX.inv.app (Opposite.op S)
        ⟨h ≫ pullback.fst (terminal.from X) (terminal.from ((𝒯).obj W))⟩).1 := fun h =>
    (congrArg Subtype.val (types_congr_hom (hX.inv.naturality h.op)
      ⟨pullback.fst (terminal.from X) (terminal.from ((𝒯).obj W))⟩)).symm
  have hbij : ∀ T : (BigFppfOver B integerBase B.contains_integerBase)ᵒᵖ,
      Function.Bijective (fun g : (yoneda.obj Z ⋙ uliftFunctor.{u + 1, u}).obj T =>
        Q.toFunctor.map g.down.op u) := by
    refine fun T => ⟨?_, ?_⟩
    · rintro ⟨g⟩ ⟨g'⟩ hgg
      have h1 := congrArg (fun w => framedRead E φ F₀ hF₀ κ c w.1) hgg
      simp only at h1
      rw [hreadψ, hreadψ] at h1
      have h3' := (hξ ((𝒯).map g)).symm.trans ((congrArg Prod.snd h1).trans (hξ ((𝒯).map g')))
      have h5 := congrArg ULift.down
        ((asIso (hX.inv.app (Opposite.op ((𝒯).obj T.unop)))).toEquiv.injective (Subtype.ext h3'))
      have h6 : (𝒯).map g ≫ pullback.snd (terminal.from X) (terminal.from ((𝒯).obj W)) =
          (𝒯).map g' ≫ pullback.snd (terminal.from X) (terminal.from ((𝒯).obj W)) := by
        have := congrArg (𝒯).map (congrArg Prod.fst h1)
        simp only [Functor.map_comp] at this
        exact this
      exact congrArg ULift.up ((𝒯).map_injective (pullback.hom_ext h5 h6))
    · rintro ⟨x, hx⟩
      have hmem := (mem_hilbertQuotients_iff_framedFreeSubobject E φ F₀ hF₀ κ c p
        (CostructuredArrow.mk x.toBase) (framedBase φ x.toBase) (framedBase_spec φ _) x.subobject
        x.mem.1.1.1).1 hx
      let h : (𝒯).obj T.unop ⟶ X :=
        (hX.hom.app (Opposite.op ((𝒯).obj T.unop)) ⟨_, hmem⟩).down
      let g₀ : (𝒯).obj T.unop ⟶ Zs := pullback.lift h ((𝒯).map (framedBase φ x.toBase))
        (terminal.hom_ext _ _)
      let g : T.unop ⟶ Z := CurveFamily.homOfScheme g₀
      refine ⟨⟨g⟩, Subtype.ext (framedRead_injective E φ F₀ hF₀ κ c ?_)⟩
      change framedRead E φ F₀ hF₀ κ c (Q.toFunctor.map g.op u).1 = _
      rw [hreadψ]
      refine Prod.ext ?_ ?_
      · apply (𝒯).map_injective
        rw [Functor.map_comp]
        exact pullback.lift_snd _ _ _
      · refine (hξ g₀).trans ?_
        rw [pullback.lift_fst]
        exact congrArg Subtype.val (types_congr_hom
          (hX.hom_inv_id_app (Opposite.op ((𝒯).obj T.unop))) ⟨_, hmem⟩)
  let e : yoneda.obj Z ⋙ uliftFunctor.{u + 1, u} ≅ Q.toFunctor :=
    NatIso.ofComponents (fun T => Equiv.toIso (Equiv.ofBijective _ (hbij T))) (by
      intro T T' k
      ext ⟨g⟩
      change Q.toFunctor.map (k.unop ≫ g).op u = Q.toFunctor.map k (Q.toFunctor.map g.op u)
      rw [op_comp, Functor.map_comp]
      rfl)
  have hiso : IsIso φ.hom.hom := inferInstanceAs (IsIso ((ObjectProperty.ι _).mapIso φ).hom)
  refine ⟨Z, e, yoneda.map aZ ≫ φ.hom.hom, ?_,
    Space.isProper_comp' B integerBase B.contains_integerBase
    _ _ (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase W) D.Y.2
    ((Space.isProper_yoneda_map_iff B integerBase B.contains_integerBase aZ).2
      (inferInstanceAs (IsProper (pullback.snd (terminal.from X) (terminal.from ((𝒯).obj W))))))
    (@Space.isProper_of_isIso B integerBase B.contains_integerBase _ _ φ.hom.hom hiso)⟩
  ext T ⟨g⟩
  change ULift.up (yonedaEquiv ((schemeSpaceMap g ≫ schemeSpaceMap aZ ≫ φ.hom).hom)) =
    ULift.up ((yoneda.map aZ ≫ φ.hom.hom).app T g)
  congr 1

end AlgebraicGeometry.ProjectiveQuotOverSpace

end
