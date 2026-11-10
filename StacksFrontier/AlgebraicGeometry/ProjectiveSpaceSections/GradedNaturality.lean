module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.FromGlobalSections

/-!
# Naturality in the graded ring of the morphism to `Proj` defined by global sections

`AlgebraicGeometry.Proj.fromOfGlobalSections` turns a ring homomorphism `f : B →+* Γ(X, ⊤)`
whose image of the irrelevant ideal generates the unit ideal into a morphism `X ⟶ Proj ℬ`, and
`AlgebraicGeometry.Proj.map` turns a graded ring homomorphism `φ : 𝒜 →+*ᵍ ℬ` into a morphism
`Proj ℬ ⟶ Proj 𝒜`. This file proves that the two are compatible: following
`fromOfGlobalSections ℬ f` by `map φ` is `fromOfGlobalSections 𝒜 (f ∘ φ)`.

Together with `AlgebraicGeometry.Proj.comp_fromOfGlobalSections`, this says that
`fromOfGlobalSections` is natural in both of its arguments.

## Main results

* `AlgebraicGeometry.Proj.awayMap_comp_localizationMap`: the ring-theoretic content — on the
  degree-zero ring `Away 𝒜 t` the two routes to `Γ(X, ⊤)[1/f (φ t)]` agree.
* `AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections_ι_comp_map`: the same at the level of a
  single chart `D₊(t)`.
* `AlgebraicGeometry.Proj.fromOfGlobalSections_comp_map`: **naturality of
  `AlgebraicGeometry.Proj.fromOfGlobalSections` in the graded ring.**

## Implementation notes

The chart-level statement is the one that carries the content, and it is obtained from Mathlib's
`AlgebraicGeometry.Proj.awayι_comp_map` — the square comparing the standard affine chart of
`Proj ℬ` at `φ t` with the standard affine chart of `Proj 𝒜` at `t` — by composing both of its
sides with the canonical morphism `X_{f (φ t)} ⟶ Spec Γ(X, ⊤)[1/f (φ t)]` that
`AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections` is built out of. That morphism is the *same*
on both sides, because `(f ∘ φ) t` is `f (φ t)`: no geometric input is needed beyond Mathlib's
square, and what is left is the identity of ring homomorphisms
`awayMap_comp_localizationMap`, checked on a fraction `a / tⁿ`.

The cover used for the global statement is the one of the *target* homomorphism `f ∘ φ`, namely
`AlgebraicGeometry.Proj.openCoverOfMapIrrelevantEqTop 𝒜 (f ∘ φ)`: its charts are the
nonvanishing loci `X_{f (φ t)}` for homogeneous `t` of positive degree in `A`, which is exactly
where the chart statement applies. Running the cover of `ℬ` instead would produce charts
`X_{f u}` for homogeneous `u ∈ B` not of the form `φ t`, where neither side has a chart
description.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

@[expose] public section

universe u

open CategoryTheory Graded Limits HomogeneousLocalization

namespace AlgebraicGeometry.Proj

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] {X : Scheme.{u}}

/-- `AlgebraicGeometry.Proj.fromOfGlobalSections` depends on the ring homomorphism only, not on
the proof that it generates. -/
theorem fromOfGlobalSections_congr {f f' : A →+* Γ(X, ⊤)} (h : f = f')
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hf' : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f' = ⊤) :
    fromOfGlobalSections 𝒜 f hf = fromOfGlobalSections 𝒜 f' hf' := by
  subst h; rfl

/-- **The ring-theoretic content of naturality in the graded ring.** The degree-zero ring
`Away 𝒜 t` maps to `Γ(X, ⊤)[1/f (φ t)]` in two ways: through `Away ℬ (φ t)` and the localization
of `f`, or through `Localization.Away t` and the localization of `f ∘ φ`. They agree: on a
fraction `a / tⁿ` both give `f (φ a) / f (φ t)ⁿ`. -/
theorem awayMap_comp_localizationMap (φ : 𝒜 →+*ᵍ ℬ) (f : B →+* Γ(X, ⊤)) {t : A} {d : ℕ}
    (hd : t ∈ 𝒜 d) :
    ((IsLocalization.map (M := .powers (φ t)) (T := .powers (f (φ t)))
            (Localization.Away (f (φ t))) f
            (Submonoid.powers_le.mpr (Submonoid.mem_powers _))).comp
          (algebraMap (Away ℬ (φ t)) (Localization.Away (φ t)))).comp
        (HomogeneousLocalization.Away.map φ t) =
      (IsLocalization.map (M := .powers t) (T := .powers (f (φ t)))
            (Localization.Away (f (φ t))) (f.comp φ.toRingHom)
            (Submonoid.powers_le.mpr (Submonoid.mem_powers _))).comp
        (algebraMap (Away 𝒜 t) (Localization.Away t)) := by
  ext z
  obtain ⟨m, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hd z
  simp only [HomogeneousLocalization.Away.map_mk, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk', map_pow,
    RingHom.comp_apply, GradedRingHom.coe_toRingHom]

/-- The inclusion of the standard chart `D₊(t)`, read through the affine identification of that
chart: it is `AlgebraicGeometry.Proj.awayι` preceded by the identification. -/
theorem basicOpenIsoSpec_hom_awayι {t : A} {d : ℕ} (hd : t ∈ 𝒜 d) (h0d : 0 < d) :
    (basicOpenIsoSpec 𝒜 t hd h0d).hom ≫ awayι 𝒜 t hd h0d = (basicOpen 𝒜 t).ι := by
  rw [← basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]

/-- **Naturality in the graded ring at a single chart, on the affine models.** Read through the
identifications of the two standard charts with the spectra of their degree-zero rings, the chart
morphism of `f` at `φ t` followed by `Spec` of `HomogeneousLocalization.Away.map φ` is the chart
morphism of `f ∘ φ` at `t`. -/
theorem toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom (φ : 𝒜 →+*ᵍ ℬ)
    (f : B →+* Γ(X, ⊤)) {t : A} {d : ℕ} (h0d : 0 < d) (hd : t ∈ 𝒜 d) :
    (toBasicOpenOfGlobalSections ℬ f rfl h0d (map_mem φ hd) ≫
          (basicOpenIsoSpec ℬ (φ t) (map_mem φ hd) h0d).hom) ≫
        Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map φ t)) =
      toBasicOpenOfGlobalSections 𝒜 (f.comp φ.toRingHom) rfl h0d hd ≫
        (basicOpenIsoSpec 𝒜 t hd h0d).hom := by
  simp only [toBasicOpenOfGlobalSections, Scheme.isoOfEq_inv, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, awayMap_comp_localizationMap φ f hd]
  rfl

/-- **Naturality in the graded ring at a single chart.** The chart morphism
`X_{f (φ t)} ⟶ D₊(φ t)` of `f`, followed by the inclusion of `D₊(φ t)` and by
`AlgebraicGeometry.Proj.map φ`, is the chart morphism `X_{(f ∘ φ) t} ⟶ D₊(t)` of `f ∘ φ`
followed by the inclusion of `D₊(t)`. -/
theorem toBasicOpenOfGlobalSections_ι_comp_map (φ : 𝒜 →+*ᵍ ℬ)
    (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)
    (f : B →+* Γ(X, ⊤)) {t : A} {d : ℕ} (h0d : 0 < d) (hd : t ∈ 𝒜 d) :
    toBasicOpenOfGlobalSections ℬ f rfl h0d (map_mem φ hd) ≫
        (basicOpen ℬ (φ t)).ι ≫ map φ hφ =
      toBasicOpenOfGlobalSections 𝒜 (f.comp φ.toRingHom) rfl h0d hd ≫ (basicOpen 𝒜 t).ι := by
  have e1 : (basicOpen ℬ (φ t)).ι ≫ map φ hφ =
      (basicOpenIsoSpec ℬ (φ t) (map_mem φ hd) h0d).hom ≫
        Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map φ t)) ≫
          awayι 𝒜 t hd h0d := by
    rw [← awayι_comp_map φ hφ h0d t hd, ← basicOpenIsoSpec_inv_ι, Category.assoc,
      Iso.hom_inv_id_assoc]
  rw [e1, ← basicOpenIsoSpec_hom_awayι hd h0d]
  simp only [← Category.assoc]
  rw [toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom φ f h0d hd]

/-- **Naturality of `AlgebraicGeometry.Proj.fromOfGlobalSections` in the graded ring.** For a
graded ring homomorphism `φ : 𝒜 →+*ᵍ ℬ` satisfying Mathlib's hypothesis for
`AlgebraicGeometry.Proj.map`, the morphism `X ⟶ Proj ℬ` of a ring homomorphism
`f : B →+* Γ(X, ⊤)` followed by `Proj.map φ : Proj ℬ ⟶ Proj 𝒜` is the morphism `X ⟶ Proj 𝒜` of
the composite `f ∘ φ`. -/
theorem fromOfGlobalSections_comp_map (φ : 𝒜 →+*ᵍ ℬ)
    (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)
    (f : B →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal.map f = ⊤)
    (hfφ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (f.comp φ.toRingHom) = ⊤) :
    fromOfGlobalSections ℬ f hf ≫ map φ hφ =
      fromOfGlobalSections 𝒜 (f.comp φ.toRingHom) hfφ := by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 (f.comp φ.toRingHom) hfφ).hom_ext _ _ fun i ↦ ?_
  obtain ⟨d, t, h0d, hd⟩ := i
  have h1 : (X.basicOpen ((f.comp φ.toRingHom) t)).ι ≫ fromOfGlobalSections ℬ f hf =
      toBasicOpenOfGlobalSections ℬ f rfl h0d (map_mem φ hd) ≫ (basicOpen ℬ (φ t)).ι :=
    basicOpen_ι_comp_fromOfGlobalSections ℬ f hf h0d (map_mem φ hd)
  change (X.basicOpen ((f.comp φ.toRingHom) t)).ι ≫ fromOfGlobalSections ℬ f hf ≫ map φ hφ =
    (X.basicOpen ((f.comp φ.toRingHom) t)).ι ≫
      fromOfGlobalSections 𝒜 (f.comp φ.toRingHom) hfφ
  rw [basicOpen_ι_comp_fromOfGlobalSections 𝒜 (f.comp φ.toRingHom) hfφ h0d hd,
    ← Category.assoc, h1, Category.assoc,
    toBasicOpenOfGlobalSections_ι_comp_map φ hφ f h0d hd]

end AlgebraicGeometry.Proj

end
