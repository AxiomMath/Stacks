module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AssociatedGraded
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AffineOpenSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DirectImageRestrictOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The degree-zero Artin–Rees bound for the direct image, over an affine open of the base

`CompletionProper/AffineOpenSectionsBaseChange.lean` reduces
`Stacks.Coherent.IsDirectImageAdicBounded` — clause (1) of Stacks 02OB in degree zero, at the
relative level — to a single hypothesis, that of
`Stacks.AffineOpenSectionsBaseChange.isDirectImageAdicBounded_of_affineOpens_self`: over each
affine open `V` of the base **separately**, with a constant that may depend on `V`,

`Γ(V, f_*𝓕) ⊇ s`, `s ↦ 0` in `Γ(V, f_*(𝓕 / ℐ ᵐ⁺¹ 𝓕))` ⟹ `s ∈ 𝒥(V) ⁿ⁺¹ Γ(V, f_*𝓕)` for
`n + c ≤ m`.

That is the affine-base statement of Stacks 02OB in degree zero, already proved on global
sections as `Stacks.Cohomology.FormalFunctions.ker_globalSections_idealPowerQuotient_le`. This
file transports it across the identifications of the restriction `f ∣_ V` with a proper morphism
onto an affine scheme, and thereby makes `Stacks.Coherent.IsDirectImageAdicBounded` — and with
it Stacks 02OC in degree zero in the relative sheaf form and the uniqueness clause of the proof
of Stacks 088B — unconditional. No uniformity is involved: the flat base change that makes one
constant serve every affine open inside `V` is
`Stacks.AffineOpenSectionsBaseChange.mem_idealPow_smul_of_le_of_affineOpens`, and the passage
from the resulting family to a cover of the base is
`Stacks.Coherent.isDirectImageAdicBounded_of_affineOpens`; both are already available.

## The chart

For an affine open `V` of `Y` the morphism `Stacks.AdicBoundAffineChart.chartMap` is
`f ∣_ V : f ⁻¹ V ⟶ V` followed by `AlgebraicGeometry.IsAffineOpen.isoSpec`, a proper morphism
`f ⁻¹ V ⟶ Spec Γ(Y, V)` (`AlgebraicGeometry.IsProper.instMorphismRestrict`, properness being
stable under composition and holding for an isomorphism). The three identifications the transport
needs are:

* on the base ring, `Stacks.AdicBoundAffineChart.baseRingHom_chartMap`: the ring map
  `Γ(Y, V) ⟶ Γ(f ⁻¹ V, 𝒪)` the chart induces on global sections is `f.app V` followed by
  `AlgebraicGeometry.Scheme.Opens.topIso`. The computation is
  `AlgebraicGeometry.Scheme.Hom.resLE_app_top` for the restricted morphism together with
  `AlgebraicGeometry.IsAffineOpen.isoSpec_hom_appTop`;
* on the ideal sheaf, `Stacks.AdicBoundAffineChart.baseIdealSheaf_chartMap`: the ideal sheaf
  `𝒥(V) · 𝒪` generated on the chart is `(𝒥 · 𝒪_X)|_{f ⁻¹ V}`. This is
  `Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap` and
  `Stacks.Coherent.comap_comap_morphismRestrict`, on an affine scheme where an ideal sheaf is
  determined by its ideal of global sections;
* on the sections, `Stacks.AdicBoundAffineChart.mem_pow_smul_of_chart`: the global sections of
  the restriction of `𝓕` are the sections of `𝓕` over `f ⁻¹ V`, compatibly with the two
  `Γ(Y, V)`-module structures. The underlying module isomorphism is
  `Stacks.Coherent.restrictionSectionsIso`, and what is added here is that it is `Γ(Y, V)`-linear
  for the action through the chart, which is the first identification read on an element.

## Main results

* `Stacks.AdicBoundAffineChart.exists_bound_sections` — **the hypothesis of
  `Stacks.AffineOpenSectionsBaseChange.isDirectImageAdicBounded_of_affineOpens_self`, over one
  affine open of the base.** The constant is the one Stacks 02OB produces for the chart, shifted
  by one: the source bounds the kernel at level `k` by `𝒥(V) ᵏ⁻ᶜ`, and the level here is `m + 1`,
  so `n + (c + 1) ≤ m` is what gives `n + 1 ≤ (m + 1) - c`.
* `Stacks.AdicBoundAffineChart.isDirectImageAdicBounded` —
  **`Stacks.Coherent.IsDirectImageAdicBounded` is a theorem**, for a proper morphism of Noetherian
  schemes, a quasi-coherent ideal sheaf on the base and a coherent module on the source, with no
  hypotheses beyond those.
* `Stacks.AdicBoundAffineChart.mono_limMap_directImageQuotientComparisonSystem` and
  `Stacks.AdicBoundAffineChart.eq_of_comp_directImageQuotientComparisonSystem_eq` — Stacks 02OC
  in degree zero in the relative sheaf form, and the uniqueness clause of the proof of
  Stacks 088B, **with no hypothesis left**: these are
  `Stacks.Coherent.mono_limMap_directImageQuotientComparisonSystem` and
  `Stacks.Coherent.eq_of_comp_directImageQuotientComparisonSystem_eq_of_adicBounded` with their
  Artin–Rees binder discharged.

## Implementation notes

No `@[stacks]` attribute is attached. The tag registrations stay where they are: Stacks 02OB on
`Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient_of_isProper`
(`CompletionProper/ArtinReesChain.lean`), and Stacks 02OC on
`Stacks.Cohomology.FormalFunctions.exists_formalFunctionsEquiv_of_isProper` there. Everything here
is transport of an existing statement across identifications of the data, and the unconditional
forms below are the same tags with a binder removed, not new mathematics.

Two coherence classes meet in this file.
`Stacks.Cohomology.FormalFunctions.ker_globalSections_idealPowerQuotient_le` is stated at
`Stacks.SheafOfModules.IsCoherent` while `AlgebraicGeometry.Modules.isCoherent_restrict` and the
`property` field of `AlgebraicGeometry.SheafOfModules.CoherentModules` produce the root-level
`SheafOfModules.IsCoherent`; these are two constants with the same two fields and instance search
crosses neither way, so `Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent'_of_isCoherent` is
applied explicitly.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules _`, so the morphisms
`Stacks.Algebraization.completionProjection` produces are not of a form on which the projection
`.app` resolves; `AlgebraicGeometry.Scheme.Modules.Hom.app` is therefore written out, and the
associativity used in `completionProjection_comp_eqToHom` is ascribed at `X.Modules`
positionally, as elsewhere in this subtree. The scalar-compatibility step of
`mem_pow_smul_of_chart` is phrased as an equality of two elements rather than as a rewrite of the
`•` instances, because `ModuleCat.restrictScalars.smul_def` is a `rfl` lemma whose two sides have
module instances that instance search will not unify through the `def`.

## References

* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.AdicBoundAffineChart

open Stacks.Algebraization Stacks.Coherent Stacks.Cohomology.FormalFunctions

/-- **The ideal of a quasi-coherent ideal sheaf over two equal affine opens.** Transport along
the restriction map of `𝒪_Z` between two opens that happen to be equal carries the ideal over one
to the ideal over the other. -/
private theorem ideal_map_eqToHom {Z : Scheme.{u}} (K : Z.IdealSheafData) {P Q : Z.Opens}
    (hP : IsAffineOpen P) (hQ : IsAffineOpen Q) (h : P = Q) :
    (K.ideal ⟨P, hP⟩).map (Z.presheaf.map (eqToHom h.symm).op).hom = K.ideal ⟨Q, hQ⟩ := by
  cases h
  simp

/-- **The ideal of `𝒦` over an affine open, read on the open subscheme.** The restriction map
`Γ(Z, P) ⟶ Γ(P, 𝒪)` of `AlgebraicGeometry.Scheme.Opens.topIso` carries `𝒦(P)` to the ideal of
`𝒦|_P` over the whole of `P`.

Both sides are the ideal of `𝒦` over `P.ι ''ᵁ ⊤ = P`: on the right by
`AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion`, whose comparison
isomorphism is the identity for the inclusion of an open
(`AlgebraicGeometry.Scheme.Opens.ι_appIso`), and on the left by `ideal_map_eqToHom`. -/
private theorem ideal_map_topIso_inv {Z : Scheme.{u}} (K : Z.IdealSheafData) {P : Z.Opens}
    (hP : IsAffineOpen P) (hT : IsAffineOpen (⊤ : P.toScheme.Opens)) :
    (K.ideal ⟨P, hP⟩).map P.topIso.inv.hom = (K.comap P.ι).ideal ⟨⊤, hT⟩ := by
  rw [K.ideal_comap_of_isOpenImmersion]
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  show (K.ideal ⟨P, hP⟩).map (Z.presheaf.map (eqToHom P.ι_image_top).op).hom =
    (K.ideal ⟨P.ι ''ᵁ ⊤, hT.image_of_isOpenImmersion P.ι⟩).comap (RingHom.id _)
  rw [Ideal.comap_id]
  exact ideal_map_eqToHom K hP _ P.ι_image_top.symm

/-- **An ideal-power multiple is carried along an `R`-equivariant additive map.** If `φ` is
additive and `φ (r • x) = r • φ x`, then `φ` sends `I ᵏ M` into `I ᵏ N`.

Stated for an `AddMonoidHom` with the equivariance as a hypothesis rather than for an
`R`-linear map: at the section types of a sheaf of modules the two module structures in play are
definitionally equal but are found by instance search only in one of their spellings, so the
equivariance has to be supplied by hand anyway. -/
private theorem mem_pow_smul_top_of_addHom {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (φ : M →+ N) (hφ : ∀ (r : R) (x : M), φ (r • x) = r • φ x) (I : Ideal R) (k : ℕ)
    {x : M} (hx : x ∈ I ^ k • (⊤ : Submodule R M)) :
    φ x ∈ I ^ k • (⊤ : Submodule R N) := by
  refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun u v hu hv => ?_)
  · rw [hφ]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [map_add]
    exact Submodule.add_mem _ hu hv

/-- **The restriction map of `M` along `W.ι ''ᵁ ⊤ = W`, in its two spellings.** The sections of
`M` over `W.ι ''ᵁ ⊤` are the global sections of `M|_W`, and the restriction map from `Γ(M, W)` is
the same whether the inclusion `W.ι ''ᵁ ⊤ ≤ W` is named by `homOfLE` or by `eqToHom`: morphisms
of opens are unique. -/
private theorem presheaf_map_ι_image_top {X : Scheme.{u}} (M : X.Modules) (W : X.Opens)
    (s : Γ(M, W)) :
    (M.presheaf.map (homOfLE W.ι_image_top.le).op) s =
      (M.val.map (eqToHom W.ι_image_top).op) s :=
  rfl

/-- **The projection onto the `m`-th term of the completion is the quotient projection.**
`Stacks.Algebraization.completionProjection` is `cokernel.π` of `ℐ ᵐ⁺¹ 𝓕 ⊆ 𝓕` followed by the
transport along `Stacks.Algebraization.completionFunctor_obj`; composing with that transport the
other way returns the quotient projection. -/
private theorem completionProjection_comp_eqToHom {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (m : ℕ) :
    completionProjection X I F m ≫ eqToHom (completionFunctor_obj X I F m) =
      cokernel.π (C := X.Modules) (idealPowerMultiple I (m + 1) F.obj).ι := by
  have h1 : completionProjection X I F m ≫ eqToHom (completionFunctor_obj X I F m) =
      cokernel.π (C := X.Modules) (idealPowerMultiple I (m + 1) F.obj).ι ≫
        (eqToHom (completionFunctor_obj X I F m).symm ≫
          eqToHom (completionFunctor_obj X I F m)) :=
    Category.assoc (obj := X.Modules) _ _ _
  rw [h1, eqToHom_trans, eqToHom_refl]
  exact Category.comp_id (obj := X.Modules) _

/-- **Clause (1) of [Stacks, Tag 02OB] in degree zero, on global sections, pointwise.** For `A`
Noetherian, `g : Z ⟶ Spec A` proper and `𝒢` coherent there is a `c` such that for every `k ≥ c` a
global section of `𝒢` killed by `𝒢 ⟶ 𝒢 / (I 𝒪_Z) ᵏ 𝒢` lies in `I ᵏ⁻ᶜ Γ(Z, 𝒢)`.

This is `Stacks.Cohomology.FormalFunctions.ker_globalSections_idealPowerQuotient_le` with its
kernel containment written out on elements, which is the form the geometric caller has: the
`A`-linear map it takes the kernel of acts on a global section as the quotient projection does
(`AlgebraicGeometry.Scheme.Modules.Hom.app` at `⊤`), by definition. Nothing is proved here. -/
theorem exists_bound_app_top (A : Type u) [CommRing A] [IsNoetherianRing A] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of A)) (I : Ideal A) (G : Z.Modules) (hg : AlgebraicGeometry.IsProper g)
    (hG : Stacks.SheafOfModules.IsCoherent G) :
    ∃ c : ℕ, ∀ k : ℕ, c ≤ k → ∀ s : Γ(G, ⊤),
      (cokernel.π (C := Z.Modules)
          (idealPowerMultiple (baseIdealSheaf A I g) k G).ι).app ⊤ s = 0 →
        s ∈ I ^ (k - c) • (⊤ : Submodule A (globalSectionsOverBase A g G)) := by
  obtain ⟨c, hc⟩ := ker_globalSections_idealPowerQuotient_le A g I G hg hG
  exact ⟨c, fun k hk s hs => hc k hk (LinearMap.mem_ker.mpr hs)⟩

/-- **A section killed by the quotient projection stays killed by the quotient projection of the
restriction.** If `s : Γ(M, W)` dies in `M / 𝒦 ᵏ M`, then its image in the global sections of
`M|_W` dies in `(M|_W) / (𝒦|_W) ᵏ (M|_W)`.

`Stacks.Algebraization.restrictFunctor_map_cokernel_π_comp_restrictIdealPowerQuotientIso_inv`
identifies the quotient projection of the restriction with the restriction of the quotient
projection, read through `Stacks.Algebraization.restrictIdealPowerQuotientIso`; the restriction of
a morphism of modules acts on the global sections of `M|_W` as the morphism itself acts on the
sections over `W.ι ''ᵁ ⊤`, and a morphism of modules commutes with restriction of sections
(`Stacks.AlgebraicGeometry.ModuleLimits.Hom_app_presheaf_map`). -/
theorem cokernel_π_restrict_app_top_eq_zero {X : Scheme.{u}} (K : X.IdealSheafData) (k : ℕ)
    (M : X.Modules) [M.IsQuasicoherent] (W : X.Opens) (s : Γ(M, W))
    (hs : (cokernel.π (C := X.Modules) (idealPowerMultiple K k M).ι).app W s = 0) :
    (cokernel.π (C := W.toScheme.Modules)
          (idealPowerMultiple (K.comap W.ι) k
            ((Scheme.Modules.restrictFunctor W.ι).obj M)).ι).app ⊤
        (M.presheaf.map (homOfLE W.ι_image_top.le).op s) = 0 := by
  rw [← restrictFunctor_map_cokernel_π_comp_restrictIdealPowerQuotientIso_inv W.ι K k M]
  have h2 : ((Scheme.Modules.restrictFunctor W.ι).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple K k M).ι)).app ⊤
      (M.presheaf.map (homOfLE W.ι_image_top.le).op s) = 0 := by
    refine Eq.trans (Stacks.AlgebraicGeometry.ModuleLimits.Hom_app_presheaf_map
      (cokernel.π (C := X.Modules) (idealPowerMultiple K k M).ι)
      W.ι_image_top.le s).symm ?_
    rw [hs]
    exact map_zero _
  exact (congrArg (fun z => (Scheme.Modules.Hom.app
    (restrictIdealPowerQuotientIso W.ι K k M).inv ⊤) z) h2).trans (map_zero _)

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {V : Y.Opens} (hV : IsAffineOpen V)

/-- **The affine chart of `f` over an affine open `V` of the base**: the restriction
`f ∣_ V : f ⁻¹ V ⟶ V` followed by the identification of `V` with `Spec Γ(Y, V)`. It is proper
whenever `f` is, being a proper morphism composed with an isomorphism. -/
def chartMap : (f ⁻¹ᵁ V).toScheme ⟶ Spec (.of ↥Γ(Y, V)) :=
  (f ∣_ V) ≫ hV.isoSpec.hom

/-- **The `Spec Γ` identification cancels against `isoSpec` on global sections.** -/
private theorem ΓSpecIso_inv_comp_isoSpec_hom_appTop {Y : Scheme.{u}} {V : Y.Opens}
    (hV : IsAffineOpen V) :
    (Scheme.ΓSpecIso (CommRingCat.of ↥Γ(Y, V))).inv ≫ hV.isoSpec.hom.appTop = V.topIso.inv := by
  rw [IsAffineOpen.isoSpec_hom_appTop]
  exact (Scheme.ΓSpecIso Γ(Y, V)).inv_hom_id_assoc _

/-- **The chart on global sections.** The ring map `Γ(Y, V) ⟶ Γ(f ⁻¹ V, 𝒪)` that the chart
induces, read through `AlgebraicGeometry.Scheme.ΓSpecIso`, is `f.app V` followed by
`AlgebraicGeometry.Scheme.Opens.topIso`.

`AlgebraicGeometry.IsAffineOpen.isoSpec_hom_appTop` cancels the `Spec Γ` identification against
the one `AlgebraicGeometry.Scheme.ΓSpecIso` supplies, leaving the global sections of `f ∣_ V`;
those are `f.appLE V (f ⁻¹ V)` conjugated by the two `topIso`, which is
`AlgebraicGeometry.Scheme.Hom.resLE_app_top` for `f.resLE V (f ⁻¹ V) le_rfl = f ∣_ V`. -/
theorem ΓSpecIso_inv_comp_chartMap_appTop :
    (Scheme.ΓSpecIso (CommRingCat.of ↥Γ(Y, V))).inv ≫ (chartMap f hV).appTop =
      f.app V ≫ (f ⁻¹ᵁ V).topIso.inv := by
  rw [show chartMap f hV = (f ∣_ V) ≫ hV.isoSpec.hom from rfl, Scheme.Hom.comp_appTop,
    ← Category.assoc, ΓSpecIso_inv_comp_isoSpec_hom_appTop]
  rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
    Iso.inv_hom_id_assoc, Scheme.Hom.appLE_eq_app]

/-- **The base ring map of the chart**, as a ring homomorphism: this is
`ΓSpecIso_inv_comp_chartMap_appTop` read on the underlying maps, and it is what makes the
`Γ(Y, V)`-module structure the chart puts on the global sections of `𝓕|_{f ⁻¹ V}` the one
`f_*𝓕` puts on its sections over `V`. -/
theorem baseRingHom_chartMap :
    baseRingHom ↥Γ(Y, V) (chartMap f hV) = (f.app V ≫ (f ⁻¹ᵁ V).topIso.inv).hom :=
  congrArg CommRingCat.Hom.hom (ΓSpecIso_inv_comp_chartMap_appTop f hV)

/-- **The ideal sheaf the chart generates is the restricted pullback of `𝒥`.** The extension of
`𝒥(V)` to `f ⁻¹ V` along the chart is `(𝒥 · 𝒪_X)|_{f ⁻¹ V}`.

Forming `I · 𝒪` commutes with pulling back
(`Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap`), so it is enough to see that `𝒥(V) · 𝒪`
on `V` itself is `𝒥|_V`, which on an affine scheme is a statement about the ideals of global
sections (`AlgebraicGeometry.Scheme.IdealSheafData.ext_of_isAffine` and
`ideal_map_topIso_inv`); the two ways of reaching `f ⁻¹ V` then agree by
`Stacks.Coherent.comap_comap_morphismRestrict`. -/
@[ega "I 10.3.1" "special case"]
theorem baseIdealSheaf_chartMap (J : Y.IdealSheafData) :
    baseIdealSheaf ↥Γ(Y, V) (J.ideal ⟨V, hV⟩) (chartMap f hV) =
      (J.comap f).comap (f ⁻¹ᵁ V).ι := by
  have hAff : IsAffine V.toScheme := hV
  have h2 : baseIdeal ↥Γ(Y, V) (J.ideal ⟨V, hV⟩) hV.isoSpec.hom =
      (J.ideal ⟨V, hV⟩).map V.topIso.inv.hom :=
    congrArg (fun z => Ideal.map (CommRingCat.Hom.hom z) (J.ideal ⟨V, hV⟩))
      (ΓSpecIso_inv_comp_isoSpec_hom_appTop hV)
  have hbase : baseIdealSheaf ↥Γ(Y, V) (J.ideal ⟨V, hV⟩) hV.isoSpec.hom = J.comap V.ι := by
    refine Scheme.IdealSheafData.ext_of_isAffine ?_
    rw [show baseIdealSheaf ↥Γ(Y, V) (J.ideal ⟨V, hV⟩) hV.isoSpec.hom =
        Scheme.IdealSheafData.ofIdealTop
          (baseIdeal ↥Γ(Y, V) (J.ideal ⟨V, hV⟩) hV.isoSpec.hom) from rfl,
      Scheme.IdealSheafData.ofIdealTop_ideal]
    have hid : (V.toScheme.presheaf.map
        (homOfLE (le_top (a := (⊤ : V.toScheme.Opens)))).op).hom = RingHom.id _ := by
      rw [show (homOfLE (le_top (a := (⊤ : V.toScheme.Opens)))).op =
          𝟙 (op (⊤ : V.toScheme.Opens)) from rfl, CategoryTheory.Functor.map_id,
        CommRingCat.hom_id]
    rw [hid, Ideal.map_id, h2]
    exact ideal_map_topIso_inv J hV _
  rw [show chartMap f hV = (f ∣_ V) ≫ hV.isoSpec.hom from rfl,
    ← Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap, hbase]
  exact Stacks.Coherent.comap_comap_morphismRestrict f V J

/-- **An ideal-power bound on the global sections of the chart is one on the sections over `V`.**
If the image of `s : Γ(V, f_*M)` in the global sections of `M|_{f ⁻¹ V}` lies in
`I ᵏ Γ(f ⁻¹ V, M)` for the `Γ(Y, V)`-module structure the chart supplies, then `s` lies in
`I ᵏ Γ(V, f_*M)`.

The underlying isomorphism of modules is `Stacks.Coherent.restrictionSectionsIso`, which is the
restriction map along `(f ⁻¹ V).ι ''ᵁ ⊤ = f ⁻¹ V` and is `Γ(X, f ⁻¹ V)`-linear. What is added
here is that it is `Γ(Y, V)`-linear for the two actions at hand: the chart acts through
`baseRingHom_chartMap`, which is `f.app V` followed by the `topIso` the restriction of scalars on
the left is taken along, and `f_*M` acts through `f.app V` by definition. Membership is then
carried by `mem_pow_smul_top_of_addHom`. -/
theorem mem_pow_smul_of_chart (M : X.Modules) (I : Ideal ↥Γ(Y, V)) (k : ℕ)
    (s : Γ((Scheme.Modules.pushforward f).obj M, V))
    (hx : (Scheme.Modules.presheaf M).map (homOfLE (f ⁻¹ᵁ V).ι_image_top.le).op s ∈
      I ^ k • (⊤ : Submodule ↥Γ(Y, V) ↥(globalSectionsOverBase ↥Γ(Y, V) (chartMap f hV)
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M)))) :
    s ∈ I ^ k • (⊤ : Submodule Γ(Y, V) Γ((Scheme.Modules.pushforward f).obj M, V)) := by
  let P : ModuleCat.{u} ↥Γ((f ⁻¹ᵁ V).toScheme, ⊤) :=
    (Stacks.Cohomology.AffineBase.moduleGlobalSections (f ⁻¹ᵁ V).toScheme).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M)
  let e := (Stacks.Coherent.restrictionSectionsIso (f ⁻¹ᵁ V)).app M
  let φ : ↥(globalSectionsOverBase ↥Γ(Y, V) (chartMap f hV)
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M)) →+
      ↥Γ((Scheme.Modules.pushforward f).obj M, V) :=
    { toFun := fun z => e.hom.hom z
      map_zero' := map_zero _
      map_add' := fun z w => e.hom.hom.map_add z w }
  have hba : ∀ a : ↥Γ(Y, V), baseRingHom ↥Γ(Y, V) (chartMap f hV) a =
      (f ⁻¹ᵁ V).topIso.inv.hom ((f.app V).hom a) := by
    intro a
    rw [baseRingHom_chartMap f hV, CommRingCat.hom_comp]
    rfl
  have hφ : ∀ (a : ↥Γ(Y, V)) (z : ↥(globalSectionsOverBase ↥Γ(Y, V) (chartMap f hV)
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M))), φ (a • z) = a • φ z := by
    intro a z
    have hsm : (a • z : ↥(globalSectionsOverBase ↥Γ(Y, V) (chartMap f hV)
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M))) =
        (((f ⁻¹ᵁ V).topIso.inv.hom ((f.app V).hom a) • (z : ↥P)) : ↥P) := by
      rw [← hba a]
      rfl
    rw [hsm]
    exact e.hom.hom.map_smul ((f.app V).hom a) z
  have hres : φ ((Scheme.Modules.presheaf M).map
      (homOfLE (f ⁻¹ᵁ V).ι_image_top.le).op s) = s := by
    show e.hom.hom (((Scheme.Modules.presheaf M).map
      (homOfLE (f ⁻¹ᵁ V).ι_image_top.le).op) s) = s
    rw [presheaf_map_ι_image_top M (f ⁻¹ᵁ V) s]
    exact ConcreteCategory.congr_hom e.inv_hom_id s
  exact hres ▸ mem_pow_smul_top_of_addHom φ hφ I k hx

section Main

variable [IsNoetherian X] [IsNoetherian Y] [IsProper f] (J : Y.IdealSheafData)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- **Clause (1) of [Stacks, Tag 02OB] in degree zero on the sections over an affine open of the
base.** There is a `c` such that for every pair `n + c ≤ m` a section of `f_*𝓕` over `V` killed by
`f_*𝓕 ⟶ f_*(𝓕 / ℐ ᵐ⁺¹ 𝓕)` lies in `𝒥(V) ⁿ⁺¹ Γ(V, f_*𝓕)`.

This is the hypothesis of
`Stacks.AffineOpenSectionsBaseChange.isDirectImageAdicBounded_of_affineOpens_self`, over one
affine open of the base, and it is the last thing that stood between the library and
`Stacks.Coherent.IsDirectImageAdicBounded`.

The bound comes from `exists_bound_app_top` applied to the chart `chartMap f hV`, a proper
morphism from `f ⁻¹ V` to an affine scheme, and to the restriction of `𝓕`, which is coherent
(`AlgebraicGeometry.Modules.isCoherent_restrict`). Its data are identified with the data at hand
by `baseIdealSheaf_chartMap` for the ideal sheaf and `mem_pow_smul_of_chart` for the sections, and
the vanishing hypothesis is moved to the chart by `cokernel_π_restrict_app_top_eq_zero` after
`completionProjection_comp_eqToHom` presents the completion projection as a quotient projection.
The constant is `c + 1` for the `c` of Stacks 02OB: the level on the chart is `m + 1`, so
`n + (c + 1) ≤ m` is exactly what gives `n + 1 ≤ (m + 1) - c`. -/
theorem exists_bound_sections :
    ∃ c : ℕ, ∀ n m : ℕ, n + c ≤ m →
      ∀ s : Γ((Scheme.Modules.pushforward f).obj F.obj, V),
        ((Scheme.Modules.pushforward f).map
            (completionProjection X (J.comap f) F m)).app V s = 0 →
          s ∈ J.ideal ⟨V, hV⟩ ^ (n + 1) •
            (⊤ : Submodule Γ(Y, V) Γ((Scheme.Modules.pushforward f).obj F.obj, V)) := by
  have hcohF : _root_.SheafOfModules.IsCoherent F.obj := F.property
  have hqcF : F.obj.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F.obj).1
  have hnoeth : IsNoetherianRing ↥Γ(Y, V) :=
    IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hproper : AlgebraicGeometry.IsProper (chartMap f hV) :=
    show AlgebraicGeometry.IsProper ((f ∣_ V) ≫ hV.isoSpec.hom) from inferInstance
  have hcohM' : Stacks.SheafOfModules.IsCoherent
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F.obj) :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent'_of_isCoherent
      (AlgebraicGeometry.Modules.isCoherent_restrict F.obj (f ⁻¹ᵁ V))
  obtain ⟨c, hc⟩ := exists_bound_app_top ↥Γ(Y, V) (chartMap f hV) (J.ideal ⟨V, hV⟩)
    ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F.obj) hproper hcohM'
  refine ⟨c + 1, fun n m hnm s hs => ?_⟩
  -- the hypothesis read as a quotient projection on the sections over `f ⁻¹ V`
  have hs1 : Scheme.Modules.Hom.app (completionProjection X (J.comap f) F m) (f ⁻¹ᵁ V) s = 0 := hs
  have hs0 : (cokernel.π (C := X.Modules)
      (idealPowerMultiple (J.comap f) (m + 1) F.obj).ι).app (f ⁻¹ᵁ V) s = 0 := by
    rw [← completionProjection_comp_eqToHom (J.comap f) F m]
    show (Scheme.Modules.Hom.app (eqToHom (completionFunctor_obj X (J.comap f) F m))
      (f ⁻¹ᵁ V)) (Scheme.Modules.Hom.app (completionProjection X (J.comap f) F m)
        (f ⁻¹ᵁ V) s) = 0
    rw [hs1]
    exact map_zero _
  -- the same, on the global sections of the chart
  have hzero := cokernel_π_restrict_app_top_eq_zero (J.comap f) (m + 1) F.obj (f ⁻¹ᵁ V) s hs0
  rw [← baseIdealSheaf_chartMap f hV J] at hzero
  have hmem := hc (m + 1) (by omega) _ hzero
  -- transport back along the identification of the global sections of the chart
  have hfinal := mem_pow_smul_of_chart f hV F.obj (J.ideal ⟨V, hV⟩) (m + 1 - c) s hmem
  refine Submodule.smul_induction_on hfinal (fun a ha y _ => ?_)
    (fun u v hu hv => Submodule.add_mem _ hu hv)
  exact Submodule.smul_mem_smul
    (Ideal.pow_le_pow_right (show n + 1 ≤ m + 1 - c by omega) ha) Submodule.mem_top

end Main

end

section Unconditional

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
  (J : Y.IdealSheafData)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- **`Stacks.Coherent.IsDirectImageAdicBounded` holds**, for a proper morphism of Noetherian
schemes, a quasi-coherent ideal sheaf on the base and a coherent module on the source: clause (1)
of Stacks 02OB in degree zero at the relative level, with nothing assumed.

This is `exists_bound_sections` over each affine open of the base fed to
`Stacks.AffineOpenSectionsBaseChange.isDirectImageAdicBounded_of_affineOpens_self`, which supplies
the uniformity inside each affine open by flat base change and across a cover by
quasi-compactness. -/
theorem isDirectImageAdicBounded : IsDirectImageAdicBounded f J F :=
  Stacks.AffineOpenSectionsBaseChange.isDirectImageAdicBounded_of_affineOpens_self f J F
    fun V => exists_bound_sections f V.2 J F

/-- **[Stacks, Tag 02OC] in degree zero, in the relative sheaf form, with no hypothesis.** The
comparison `δ : (f_*𝓕) ^∧ ⟶ f_*(𝓕 ^∧)` induces a monomorphism on inverse limits.

This is `Stacks.Coherent.mono_limMap_directImageQuotientComparisonSystem` with its Artin–Rees
binder discharged by `isDirectImageAdicBounded`; the tag registration stays on that theorem. -/
theorem mono_limMap_directImageQuotientComparisonSystem :
    Mono (limMap (C := Y.Modules) (directImageQuotientComparisonSystem f J F)) :=
  Stacks.Coherent.mono_limMap_directImageQuotientComparisonSystem f J F
    (isDirectImageAdicBounded f J F)

/-- **The uniqueness clause of the proof of [Stacks, Tag 088B], with no hypothesis.** Two
morphisms out of a completion `𝒜 ^∧` with the same composite with
`Stacks.Coherent.directImageQuotientComparisonSystem` are equal.

This is `Stacks.Coherent.eq_of_comp_directImageQuotientComparisonSystem_eq_of_adicBounded` with
its Artin–Rees binder discharged by `isDirectImageAdicBounded`. -/
theorem eq_of_comp_directImageQuotientComparisonSystem_eq
    (𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    {u v : ((completionFunctor Y J).obj 𝒜).obj ⟶
      ((completionFunctor Y J).obj (properPushforwardCoherent f F)).obj}
    (h : u ≫ directImageQuotientComparisonSystem f J F =
      v ≫ directImageQuotientComparisonSystem f J F) : u = v :=
  Stacks.Coherent.eq_of_comp_directImageQuotientComparisonSystem_eq_of_adicBounded f J F 𝒜
    (isDirectImageAdicBounded f J F) h

end Unconditional

end Stacks.AdicBoundAffineChart

end
