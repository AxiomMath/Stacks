module

public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.UnitRescale
public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.Sections

/-!
# Morphisms into `Proj` through a standard chart

Let `A = ⨁ 𝒜 n` be a graded ring and `t ∈ 𝒜 d` homogeneous of positive degree. A morphism
`g : W ⟶ Proj A` with `g⁻¹ D₊(t) = W` is determined by its *chart ring map*
`A_{(t)} ⟶ Γ(W, 𝒪_W)`, the composite of `A_{(t)} → Γ(D₊(t), 𝒪)` with `g^♯`, because `D₊(t)` is
affine. For the morphism `φ_χ` defined by a ring map `χ : A →+* Γ(T, 𝒪_T)`
(`AlgebraicGeometry.Proj.fromOfGlobalSections`) the chart ring map on `T_{χ(t)} = φ_χ⁻¹ D₊(t)` is
`x / tᵏ ↦ χ(x) / χ(t)ᵏ`.

## Main results

* `Stacks.LinearSystemScheme.awayToSection_comp_appLE_fromOfGlobalSections`: the chart ring map
  of `φ_χ` on `T_{χ(t)}` is `Stacks.ProjGlobalSectionsAppTop.projAwayHom`.
* `Stacks.LinearSystemScheme.eq_of_awayToSection_comp_appLE_eq`: two morphisms landing in `D₊(t)`
  with the same chart ring map are equal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization
open AlgebraicGeometry.Proj

universe u

namespace Stacks.LinearSystemScheme

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] {𝒜 : ℕ → σ}
  [GradedRing 𝒜] {T W : Scheme.{u}} {t : A} {d : ℕ}

/-- **The chart ring map of `φ_χ`.** On `T_{χ(t)} = φ_χ⁻¹ D₊(t)`, the section of `𝒪_{Proj A}`
attached to `x ∈ A_{(t)}` pulls back to `projAwayHom χ x`, which sends `x / tᵏ` to
`χ(x) / χ(t)ᵏ`. -/
theorem awayToSection_comp_appLE_fromOfGlobalSections (χ : A →+* Γ(T, ⊤))
    (hχ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map χ = ⊤) (hd : 0 < d) (ht : t ∈ 𝒜 d) :
    awayToSection 𝒜 t ≫ (fromOfGlobalSections 𝒜 χ hχ).appLE (basicOpen 𝒜 t) (T.basicOpen (χ t))
        (fromOfGlobalSections_preimage_basicOpen 𝒜 χ hχ hd ht).ge =
      CommRingCat.ofHom (Stacks.ProjGlobalSectionsAppTop.projAwayHom 𝒜 χ) := by
  have h := Stacks.ProjGlobalSectionsAppTop.toBasicOpenOfGlobalSections_appTop 𝒜 χ hd ht
  rw [← fromOfGlobalSections_resLE 𝒜 χ hχ hd ht, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
    basicOpenIsoAway_hom] at h
  simp only [Iso.inv_hom_id_assoc] at h
  rw [← cancel_mono (T.basicOpen (χ t)).topIso.inv, Category.assoc]
  exact h

/-- **Two morphisms into `Proj A` landing in `D₊(t)` with the same chart ring map are equal.** -/
theorem eq_of_awayToSection_comp_appLE_eq (hd : 0 < d) (ht : t ∈ 𝒜 d) {g g' : W ⟶ Proj 𝒜}
    (hg : g ⁻¹ᵁ basicOpen 𝒜 t = ⊤) (hg' : g' ⁻¹ᵁ basicOpen 𝒜 t = ⊤)
    (h : awayToSection 𝒜 t ≫ g.appLE (basicOpen 𝒜 t) ⊤ hg.ge =
      awayToSection 𝒜 t ≫ g'.appLE (basicOpen 𝒜 t) ⊤ hg'.ge) : g = g' := by
  have hiso : IsIso (awayToSection 𝒜 t) := by
    rw [← basicOpenIsoAway_hom 𝒜 t ht hd]; infer_instance
  have happ : g.appLE (basicOpen 𝒜 t) ⊤ hg.ge = g'.appLE (basicOpen 𝒜 t) ⊤ hg'.ge :=
    (cancel_epi (awayToSection 𝒜 t)).mp h
  have hres : g.resLE (basicOpen 𝒜 t) ⊤ hg.ge = g'.resLE (basicOpen 𝒜 t) ⊤ hg'.ge := by
    refine Stacks.ProjGlobalSectionsAppTop.ext_of_appTop_basicOpen 𝒜 hd ht ?_
    rw [Scheme.Hom.appTop, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Scheme.Hom.resLE_app_top,
      happ]
  have e1 := Scheme.Hom.resLE_comp_ι g hg.ge
  have e2 := Scheme.Hom.resLE_comp_ι g' hg'.ge
  rw [hres] at e1
  have : IsIso (⊤ : W.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
  exact (cancel_epi (⊤ : W.Opens).ι).mp (e1.symm.trans e2)

/-! ### Morphisms into a chart as morphisms into `Spec A_{(t)}` -/

/-- A morphism `g : W ⟶ Proj A` with `g⁻¹ D₊(t) = W` has image contained in the image of the
standard open immersion `Spec A_{(t)} ⟶ Proj A`. -/
theorem range_subset_range_awayι (hd : 0 < d) (ht : t ∈ 𝒜 d) {g : W ⟶ Proj 𝒜}
    (hg : g ⁻¹ᵁ basicOpen 𝒜 t = ⊤) : Set.range g ⊆ Set.range (awayι 𝒜 t ht hd) := by
  rintro _ ⟨w, rfl⟩
  have hw : w ∈ g ⁻¹ᵁ basicOpen 𝒜 t := by rw [hg]; trivial
  have : g w ∈ (awayι 𝒜 t ht hd).opensRange := by rw [opensRange_awayι]; exact hw
  exact this

/-- The lift through `Spec A_{(t)} ⟶ Proj A` of a morphism landing in `D₊(t)`. -/
def chartLift (hd : 0 < d) (ht : t ∈ 𝒜 d) (g : W ⟶ Proj 𝒜) (hg : g ⁻¹ᵁ basicOpen 𝒜 t = ⊤) :
    W ⟶ Spec (.of (Away 𝒜 t)) :=
  IsOpenImmersion.lift (awayι 𝒜 t ht hd) g (range_subset_range_awayι hd ht hg)

/-- The lift `chartLift hd ht g hg` composed with `Spec A_{(t)} ⟶ Proj A` is `g`. -/
@[reassoc (attr := simp)]
theorem chartLift_comp_awayι (hd : 0 < d) (ht : t ∈ 𝒜 d) (g : W ⟶ Proj 𝒜)
    (hg : g ⁻¹ᵁ basicOpen 𝒜 t = ⊤) : chartLift hd ht g hg ≫ awayι 𝒜 t ht hd = g :=
  IsOpenImmersion.lift_fac _ _ _

/-- The preimage of `D₊(t)` under the standard open immersion `Spec A_{(t)} ⟶ Proj A` is all of
`Spec A_{(t)}`. -/
theorem awayι_preimage_basicOpen_self (hd : 0 < d) (ht : t ∈ 𝒜 d) :
    awayι 𝒜 t ht hd ⁻¹ᵁ basicOpen 𝒜 t = ⊤ := by
  rw [← opensRange_awayι 𝒜 t ht hd]; simp

/-- The chart ring map of the standard open immersion `Spec A_{(t)} ⟶ Proj A` is the canonical
identification of `A_{(t)}` with the global sections of `Spec A_{(t)}`. -/
theorem awayToSection_comp_awayι_appLE (hd : 0 < d) (ht : t ∈ 𝒜 d)
    (e : (⊤ : (Spec (.of (Away 𝒜 t))).Opens) ≤ awayι 𝒜 t ht hd ⁻¹ᵁ basicOpen 𝒜 t) :
    awayToSection 𝒜 t ≫ (awayι 𝒜 t ht hd).appLE (basicOpen 𝒜 t) ⊤ e =
      (Scheme.ΓSpecIso (.of (Away 𝒜 t))).inv := by
  ext x
  exact Stacks.AlgebraicGeometry.ProjTwistChain.appLE_awayι_awayToSection hd ht e x

/-- **The chart ring map of `g` is the ring map of its lift `W ⟶ Spec A_{(t)}`.** -/
theorem awayToSection_comp_appLE_eq_chartLift (hd : 0 < d) (ht : t ∈ 𝒜 d) (g : W ⟶ Proj 𝒜)
    (hg : g ⁻¹ᵁ basicOpen 𝒜 t = ⊤) :
    awayToSection 𝒜 t ≫ g.appLE (basicOpen 𝒜 t) ⊤ hg.ge =
      (Scheme.ΓSpecIso (.of (Away 𝒜 t))).inv ≫ (chartLift hd ht g hg).appTop := by
  have e := (awayι_preimage_basicOpen_self hd ht).ge
  have h1 : g.appLE (basicOpen 𝒜 t) ⊤ hg.ge =
      (awayι 𝒜 t ht hd).appLE (basicOpen 𝒜 t) ⊤ e ≫ (chartLift hd ht g hg).appLE ⊤ ⊤ le_top := by
    refine (Stacks.AlgebraicGeometry.ProjTwistChain.appLE_congr_hom
      (chartLift_comp_awayι hd ht g hg).symm _ _ _ ?_).trans
        (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [chartLift_comp_awayι]; exact hg.ge
  rw [h1, ← Category.assoc, awayToSection_comp_awayι_appLE hd ht e]
  exact congrArg _ (Stacks.AlgebraicGeometry.ProjTwistChain.appLE_top_top _ _)

/-- **On constants the chart ring map is the structure morphism.** -/
theorem awayToSection_comp_appLE_fromZeroRingHom (hd : 0 < d) (ht : t ∈ 𝒜 d) (g : W ⟶ Proj 𝒜)
    (hg : g ⁻¹ᵁ basicOpen 𝒜 t = ⊤) :
    CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers t)) ≫ awayToSection 𝒜 t ≫
        g.appLE (basicOpen 𝒜 t) ⊤ hg.ge =
      (Scheme.ΓSpecIso (.of (𝒜 0))).inv ≫ (g ≫ toSpecZero 𝒜).appTop := by
  rw [awayToSection_comp_appLE_eq_chartLift hd ht g hg]
  have e1 : g ≫ toSpecZero 𝒜 = chartLift hd ht g hg ≫
      Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _)) := by
    conv_lhs => rw [← chartLift_comp_awayι hd ht g hg]
    rw [Category.assoc, awayι_toSpecZero]
  rw [e1, Scheme.Hom.comp_appTop, Scheme.ΓSpecIso_inv_naturality_assoc]

end Stacks.LinearSystemScheme

end
