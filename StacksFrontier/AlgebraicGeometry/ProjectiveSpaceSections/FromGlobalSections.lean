module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Naturality in the source of the morphism to `Proj` defined by global sections

`AlgebraicGeometry.Proj.fromOfGlobalSections` turns a ring homomorphism `f : A →+* Γ(X, ⊤)`
whose image of the irrelevant ideal generates the unit ideal into a morphism `X ⟶ Proj 𝒜`. The
construction is natural in the source: precomposing with `g : Y ⟶ X` is the same as running the
construction for the pulled-back ring homomorphism `g.appTop.hom.comp f`.

## Main results

* `AlgebraicGeometry.Proj.resLE_comp_toBasicOpenOfGlobalSections`: source naturality of the
  chart morphism `AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections`.
* `AlgebraicGeometry.Proj.comp_fromOfGlobalSections`: source naturality of
  `AlgebraicGeometry.Proj.fromOfGlobalSections` itself.
* `AlgebraicGeometry.Proj.basicOpen_ι_comp_fromOfGlobalSections`: the chart description of the
  morphism on the source.

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

@[expose] public section

universe u

open CategoryTheory Limits HomogeneousLocalization

namespace AlgebraicGeometry.Proj

variable {σ : Type*} {A : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

section Away

variable {X Y : Scheme.{u}}

/-- The canonical morphism `X_x ⟶ Spec Γ(X, ⊤)[1/x]`, the one used in the construction of
`AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections`, becomes `Scheme.toSpecΓ` after composing
with the open immersion `Spec Γ(X, ⊤)[1/x] ⟶ Spec Γ(X, ⊤)`. -/
theorem homOfLE_toSpecΓ_restrict_ι (X : Scheme.{u}) (x : Γ(X, ⊤)) :
    X.homOfLE (X.toSpecΓ_preimage_basicOpen x).ge ≫
        (X.toSpecΓ ∣_ PrimeSpectrum.basicOpen x) ≫ Scheme.Opens.ι _ =
      (X.basicOpen x).ι ≫ X.toSpecΓ :=
  (Category.assoc _ _ _).symm.trans
    (Scheme.Hom.resLE_comp_ι X.toSpecΓ (X.toSpecΓ_preimage_basicOpen x).ge)

/-- `homOfLE_toSpecΓ_restrict_ι` with a trailing morphism. -/
theorem homOfLE_toSpecΓ_restrict_ι_assoc (X : Scheme.{u}) (x : Γ(X, ⊤)) {Z : Scheme.{u}}
    (h : Spec Γ(X, ⊤) ⟶ Z) :
    X.homOfLE (X.toSpecΓ_preimage_basicOpen x).ge ≫
        (X.toSpecΓ ∣_ PrimeSpectrum.basicOpen x) ≫ Scheme.Opens.ι _ ≫ h =
      (X.basicOpen x).ι ≫ X.toSpecΓ ≫ h :=
  (Category.assoc _ _ _).symm.trans
    (Scheme.Hom.resLE_comp_ι_assoc X.toSpecΓ (X.toSpecΓ_preimage_basicOpen x).ge h)

/-- The canonical morphism `X_x ⟶ Spec Γ(X, ⊤)[1/x]`, composed with the open immersion onto
`Spec Γ(X, ⊤)`, is the restriction of `Scheme.toSpecΓ`. -/
theorem homOfLE_toSpecΓ_restrict_basicOpenIsoSpecAway_hom_SpecMap (X : Scheme.{u})
    (x : Γ(X, ⊤)) :
    X.homOfLE (X.toSpecΓ_preimage_basicOpen x).ge ≫
        (X.toSpecΓ ∣_ PrimeSpectrum.basicOpen x) ≫ (basicOpenIsoSpecAway x).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away x))) =
      (X.basicOpen x).ι ≫ X.toSpecΓ := by
  rw [basicOpenIsoSpecAway_hom_SpecMap]
  exact homOfLE_toSpecΓ_restrict_ι X x

/-- **The canonical morphism `X_x ⟶ Spec Γ(X, ⊤)[1/x]` is natural in `X`.** -/
@[reassoc]
theorem resLE_comp_toSpecΓ_restrict_basicOpenIsoSpecAway_hom (g : Y ⟶ X) (x : Γ(X, ⊤)) :
    g.resLE (X.basicOpen x) (Y.basicOpen (g.appTop.hom x))
        (by rw [Scheme.preimage_basicOpen_top]) ≫
      X.homOfLE (X.toSpecΓ_preimage_basicOpen x).ge ≫
        (X.toSpecΓ ∣_ PrimeSpectrum.basicOpen x) ≫ (basicOpenIsoSpecAway x).hom =
      (Y.homOfLE (Y.toSpecΓ_preimage_basicOpen (g.appTop.hom x)).ge ≫
          (Y.toSpecΓ ∣_ PrimeSpectrum.basicOpen (g.appTop.hom x)) ≫
            (basicOpenIsoSpecAway (g.appTop.hom x)).hom) ≫
        Spec.map (CommRingCat.ofHom
          (IsLocalization.map (M := .powers x) (T := .powers (g.appTop.hom x))
            (Localization.Away (g.appTop.hom x)) g.appTop.hom
            (Submonoid.powers_le.mpr (Submonoid.mem_powers _)))) := by
  have hsuf : (basicOpenIsoSpecAway (g.appTop.hom x)).hom ≫
      Spec.map (CommRingCat.ofHom
        (IsLocalization.map (M := .powers x) (T := .powers (g.appTop.hom x))
          (Localization.Away (g.appTop.hom x)) g.appTop.hom
          (Submonoid.powers_le.mpr (Submonoid.mem_powers _)))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away x))) =
      Scheme.Opens.ι (X := Spec Γ(Y, ⊤)) (PrimeSpectrum.basicOpen (g.appTop.hom x)) ≫
        Spec.map g.appTop := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsLocalization.map_comp,
      CommRingCat.ofHom_comp, Spec.map_comp, basicOpenIsoSpecAway_hom_SpecMap_assoc,
      CommRingCat.ofHom_hom]
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away x))))]
  simp only [Category.assoc]
  rw [hsuf, homOfLE_toSpecΓ_restrict_basicOpenIsoSpecAway_hom_SpecMap,
    homOfLE_toSpecΓ_restrict_ι_assoc, Scheme.Hom.resLE_comp_ι_assoc,
    Scheme.toSpecΓ_naturality]

end Away

section Naturality

variable {X Y : Scheme.{u}}

/-- The hypothesis of `AlgebraicGeometry.Proj.fromOfGlobalSections` is stable under
precomposition with a scheme morphism. -/
theorem map_irrelevant_comp_appTop_eq_top (g : Y ⟶ X) (f : A →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (g.appTop.hom.comp f) = ⊤ := by
  rw [← Ideal.map_map, hf, Ideal.map_top]

/-- **Source naturality of `AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections`.** Restricting
`g : Y ⟶ X` to the nonvanishing locus of `f t` and following the chart morphism of `f` is the
chart morphism of the pulled-back ring homomorphism `g.appTop.hom.comp f`. -/
@[reassoc]
theorem resLE_comp_toBasicOpenOfGlobalSections (g : Y ⟶ X) (f : A →+* Γ(X, ⊤)) {t : A} {d : ℕ}
    (h0d : 0 < d) (hd : t ∈ 𝒜 d) :
    g.resLE (X.basicOpen (f t)) (Y.basicOpen (g.appTop.hom (f t)))
        (by rw [Scheme.preimage_basicOpen_top]) ≫
      toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd =
      toBasicOpenOfGlobalSections 𝒜 (g.appTop.hom.comp f) rfl h0d hd := by
  have hmap : ∀ {Z : Scheme.{u}} (h : Spec (CommRingCat.of (Localization.Away t)) ⟶ Z),
      Spec.map (CommRingCat.ofHom
          (IsLocalization.map (M := .powers (f t)) (T := .powers (g.appTop.hom (f t)))
            (Localization.Away (g.appTop.hom (f t))) g.appTop.hom
            (Submonoid.powers_le.mpr (Submonoid.mem_powers _)))) ≫
        Spec.map (CommRingCat.ofHom
          (IsLocalization.map (M := .powers t) (T := .powers (f t))
            (Localization.Away (f t)) f
            (Submonoid.powers_le.mpr (Submonoid.mem_powers _)))) ≫ h =
      Spec.map (CommRingCat.ofHom
          (IsLocalization.map (M := .powers t) (T := .powers (g.appTop.hom (f t)))
            (Localization.Away (g.appTop.hom (f t))) (g.appTop.hom.comp f)
            (Submonoid.powers_le.mpr (Submonoid.mem_powers _)))) ≫ h := by
    intro Z h
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      IsLocalization.map_comp_map]
  rw [← cancel_mono (basicOpenIsoSpec 𝒜 t hd h0d).hom]
  simp only [toBasicOpenOfGlobalSections, Scheme.isoOfEq_inv, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_comp, Spec.map_comp,
    resLE_comp_toSpecΓ_restrict_basicOpenIsoSpecAway_hom_assoc, hmap]
  rfl

/-- **The chart description of `AlgebraicGeometry.Proj.fromOfGlobalSections` on the source.**
Restricted to the nonvanishing locus of `f r` the morphism is
`AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections`, followed by the inclusion of `D₊(r)`. -/
@[reassoc]
theorem basicOpen_ι_comp_fromOfGlobalSections (f : A →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) {r : A} {n : ℕ} (hn : 0 < n)
    (hr : r ∈ 𝒜 n) :
    (X.basicOpen (f r)).ι ≫ fromOfGlobalSections 𝒜 f hf =
      toBasicOpenOfGlobalSections 𝒜 f rfl hn hr ≫ (basicOpen 𝒜 r).ι := by
  rw [← Scheme.Hom.resLE_comp_ι (fromOfGlobalSections 𝒜 f hf)
      (fromOfGlobalSections_preimage_basicOpen 𝒜 f hf hn hr).ge,
    fromOfGlobalSections_resLE]

/-- **Source naturality of `AlgebraicGeometry.Proj.fromOfGlobalSections`.** Precomposing the
morphism defined by `f` with `g : Y ⟶ X` gives the morphism defined by the pulled-back ring
homomorphism `g.appTop.hom.comp f`. -/
theorem comp_fromOfGlobalSections (g : Y ⟶ X) (f : A →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hf' : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (g.appTop.hom.comp f) = ⊤) :
    g ≫ fromOfGlobalSections 𝒜 f hf =
      fromOfGlobalSections 𝒜 (g.appTop.hom.comp f) hf' := by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 (g.appTop.hom.comp f) hf').hom_ext _ _ fun i ↦ ?_
  obtain ⟨d, t, h0d, hd⟩ := i
  show (Y.basicOpen ((g.appTop.hom.comp f) t)).ι ≫ g ≫ fromOfGlobalSections 𝒜 f hf =
    (Y.basicOpen ((g.appTop.hom.comp f) t)).ι ≫
      fromOfGlobalSections 𝒜 (g.appTop.hom.comp f) hf'
  rw [basicOpen_ι_comp_fromOfGlobalSections 𝒜 (g.appTop.hom.comp f) hf' h0d hd,
    ← Scheme.Hom.resLE_comp_ι_assoc g (U := X.basicOpen (f t))
      (V := Y.basicOpen ((g.appTop.hom.comp f) t))
      (e := by rw [Scheme.preimage_basicOpen_top]; exact le_rfl),
    basicOpen_ι_comp_fromOfGlobalSections 𝒜 f hf h0d hd]
  exact resLE_comp_toBasicOpenOfGlobalSections_assoc 𝒜 g f h0d hd (basicOpen 𝒜 t).ι

end Naturality

end AlgebraicGeometry.Proj

end
