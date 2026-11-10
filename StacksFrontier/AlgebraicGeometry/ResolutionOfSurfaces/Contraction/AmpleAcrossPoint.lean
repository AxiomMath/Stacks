module

public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.HartogsExtension.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DepthCoherence.ReflexiveExtension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.DenseOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.LocalOnBase

/-!
# Ampleness across a point of depth two

Let `L` be an invertible module on a scheme `X`, `Y ⊆ X` a quasi-compact quasi-separated open
and `v ∈ Y` a point at which the structure sheaf has depth at least two. If `L` is ample on a
basic open `Y_h ∋ v` and on `Y \ {v}`, then `L` is ample on `Y`, provided sections over
`Y \ {v}` extend to `Y` and no open `Ω ∋ v` has `Ω \ {v}` affine
(`AlgebraicGeometry.isAmple_pullbackModule_of_basicOpen_of_compl`). The two provisos hold when `Y`
is separated over an affine scheme and `v` has depth two
(`AlgebraicGeometry.isIso_unit_of_isInvertible_of_depth` and
`AlgebraicGeometry.false_of_isIso_c_of_isAffine`).

A point of `Y_h` lies in an affine nonvanishing locus of a section over `Y_h`, which becomes,
after multiplication by a power of `h`, a section over `Y` with the same nonvanishing locus
([Stacks, Tag 01P7]). A point `y ≠ v` lies in an affine nonvanishing locus of a section over
`Y \ {v}`; by Hartogs the section extends over `v`, and the extension vanishes at `v`: otherwise
its nonvanishing locus would be an open `Ω ∋ v` with `Ω \ {v}` affine, which is impossible
(`AlgebraicGeometry.false_of_isIso_c_of_isAffine`). Indeed functions on `Ω` and on `Ω \ {v}`
agree, so `Ω ⟶ Spec Γ(Ω) = Ω \ {v}` would retract `Ω` onto the scheme-theoretically dense open
`Ω \ {v}`, and a separated scheme admits no such retraction.

This is the ampleness statement needed in [Stacks, Tag 0C2N] (2) over affine opens of the base
which contain the point under the contracted curve without that point being closed in them.

## Main results

* `AlgebraicGeometry.surjective_restriction_of_isIso_unit`: Hartogs extension of sections, from
  invertibility of the unit of `j^* ⊣ j_*` for an open immersion `j`.
* `AlgebraicGeometry.isIso_unit_of_isInvertible_of_depth`: that unit is invertible at an
  invertible module when the structure sheaf has depth `≥ 2` off the open.
* `AlgebraicGeometry.false_of_isIso_c_of_isAffine`: no proper open subscheme of a separated
  scheme over an affine scheme is affine, scheme-theoretically dense and with the same functions.
* `AlgebraicGeometry.isAmple_pullbackModule_of_basicOpen_of_compl`: the gluing statement above.

## References

* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
* [Stacks Project, Tag 0C2N](https://stacks.math.columbia.edu/tag/0C2N)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-! ### Hartogs extension of sections -/

/-- **Hartogs extension of sections.** If the unit of the adjunction `j^* ⊣ j_*` of an open
immersion `j : U ⟶ X` is an isomorphism at an `𝒪_X`-module `F`, then every section of `F` over
`Y ∩ U` is the restriction of a section over `Y`, for every open `Y`. -/
theorem surjective_restriction_of_isIso_unit {X : Scheme.{u}} (U : X.Opens) (F : X.Modules)
    (h : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F)) (Y : X.Opens) :
    Function.Surjective (F.presheaf.map (homOfLE (inf_le_left : Y ⊓ U ≤ Y)).op) := by
  have key := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction U.ι)
    (Scheme.Modules.pullbackPushforwardAdjunction U.ι) F
  have hres : IsIso ((Scheme.Modules.restrictAdjunction U.ι).unit.app F) := by
    have : IsIso ((Scheme.Modules.restrictAdjunction U.ι).unit.app F ≫
        (Scheme.Modules.pushforward U.ι).map
          (((Scheme.Modules.restrictAdjunction U.ι).leftAdjointUniq
            (Scheme.Modules.pullbackPushforwardAdjunction U.ι)).hom.app F)) := key ▸ h
    exact IsIso.of_isIso_comp_right ((Scheme.Modules.restrictAdjunction U.ι).unit.app F)
      ((Scheme.Modules.pushforward U.ι).map
          (((Scheme.Modules.restrictAdjunction U.ι).leftAdjointUniq
            (Scheme.Modules.pullbackPushforwardAdjunction U.ι)).hom.app F))
  have happ : IsIso (((Scheme.Modules.restrictAdjunction U.ι).unit.app F).app Y) :=
    inferInstance
  rw [Scheme.Modules.restrictAdjunction_unit_app_app] at happ
  have hopen : U.ι ''ᵁ U.ι ⁻¹ᵁ Y = Y ⊓ U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
  intro σ
  obtain ⟨τ, hτ⟩ :=
    ((ConcreteCategory.isIso_iff_bijective _).mp happ).2 (F.presheaf.map (eqToHom hopen).op σ)
  refine ⟨τ, ?_⟩
  calc F.presheaf.map (homOfLE (inf_le_left : Y ⊓ U ≤ Y)).op τ
      = F.presheaf.map (eqToHom hopen.symm).op
          (F.presheaf.map (homOfLE (U.ι.image_preimage_le Y)).op τ) := by
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl
    _ = F.presheaf.map (eqToHom hopen.symm).op (F.presheaf.map (eqToHom hopen).op σ) :=
        congrArg (fun z => F.presheaf.map (eqToHom hopen.symm).op z) hτ
    _ = σ := by
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
          show (eqToHom hopen).op ≫ (eqToHom hopen.symm).op = 𝟙 (op (Y ⊓ U)) from
            Subsingleton.elim _ _, F.presheaf.map_id]
        rfl

/-- **Hartogs for invertible modules.** On a locally Noetherian scheme, the unit of `j^* ⊣ j_*`
for the inclusion `j` of an open `U` is an isomorphism at every invertible module, provided the
structure sheaf has depth at least two at every point off `U`: the stalks of an invertible module
are free of rank one. -/
theorem isIso_unit_of_isInvertible_of_depth (X : Scheme.{u}) [IsLocallyNoetherian X]
    (F : X.Modules) [Stacks.Ample.IsInvertibleModule X F] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F) := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F :=
    ‹Stacks.Ample.IsInvertibleModule X F›
  have : F.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X F
  have h1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := X.ringCatSheaf) F 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme X F
  have h2 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) F :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F 1
  exact Stacks.FundamentalGroup.DepthCoherence.isIso_unit_of_isReflexive U F
    (Stacks.FundamentalGroup.ExtendedEtale.isReflexive_of_isFiniteLocallyFree F
      ((Stacks.Modules.isFiniteLocallyFree_iff_localGenerators F).mpr h2)) hdepth

/-! ### An open subscheme with the same functions is not affine -/

/-- **A scheme separated over an affine scheme is not retracted onto a proper affine open with
the same functions.** Let `q : Z ⟶ T` be separated with `T` affine, and `U ⊆ Z` an affine open with
`𝒪_Z ≅ (U ⊆ Z)_* 𝒪_U`. Then `U = Z`.

Functions on `Z` and `U` agree, so `Z ⟶ Spec Γ(Z) = Spec Γ(U) ≅ U` is a morphism over `T`
retracting `Z` onto `U`; composed with the inclusion it agrees with the identity on `U`, which is
scheme-theoretically dense, so it is the identity, and every point of `Z` lies in `U`. -/
theorem false_of_isIso_c_of_isAffine {Z T : Scheme.{u}} [IsAffine T] (q : Z ⟶ T) [IsSeparated q]
    (U : Z.Opens) [IsAffine U.toScheme] (hc : IsIso U.ι.c) (v : Z) (hv : v ∉ U) : False := by
  have : IsIso U.ι.appTop := by
    change IsIso (U.ι.c.app (op ⊤))
    infer_instance
  -- `Z ⟶ Spec Γ(Z)` is separated, `q` being so
  have hqf : q = Z.toSpecΓ ≫ Spec.map q.appTop ≫ T.isoSpec.inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc]
    change q = q ≫ T.isoSpec.hom ≫ T.isoSpec.inv
    rw [Iso.hom_inv_id, Category.comp_id]
  have : IsSeparated (Z.toSpecΓ ≫ Spec.map q.appTop ≫ T.isoSpec.inv) := hqf ▸ ‹IsSeparated q›
  have : IsSeparated Z.toSpecΓ :=
    IsSeparated.of_comp Z.toSpecΓ (Spec.map q.appTop ≫ T.isoSpec.inv)
  let r : Z ⟶ U.toScheme := Z.toSpecΓ ≫ Spec.map (inv U.ι.appTop) ≫ U.toScheme.isoSpec.inv
  have hspec : Spec.map U.ι.appTop ≫ Spec.map (inv U.ι.appTop) = 𝟙 _ := by
    rw [← Spec.map_comp, IsIso.inv_hom_id, Spec.map_id]
  have hspec' : Spec.map (inv U.ι.appTop) ≫ Spec.map U.ι.appTop = 𝟙 _ := by
    rw [← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id]
  have hr : U.ι ≫ r = 𝟙 _ := by
    change U.ι ≫ Z.toSpecΓ ≫ Spec.map (inv U.ι.appTop) ≫ U.toScheme.isoSpec.inv = 𝟙 _
    rw [Scheme.toSpecΓ_naturality_assoc, reassoc_of% hspec]
    exact U.toScheme.isoSpec.hom_inv_id
  have hq : (r ≫ U.ι) ≫ Z.toSpecΓ = Z.toSpecΓ := by
    change (Z.toSpecΓ ≫ Spec.map (inv U.ι.appTop) ≫ U.toScheme.isoSpec.inv) ≫ U.ι ≫ Z.toSpecΓ =
      Z.toSpecΓ
    rw [Scheme.toSpecΓ_naturality, Category.assoc, Category.assoc, ← Category.assoc
      U.toScheme.isoSpec.inv]
    change Z.toSpecΓ ≫ Spec.map (inv U.ι.appTop) ≫
      (U.toScheme.isoSpec.inv ≫ U.toScheme.isoSpec.hom) ≫ Spec.map U.ι.appTop = Z.toSpecΓ
    rw [Iso.inv_hom_id, Category.id_comp, hspec', Category.comp_id]
  have hdense : Scheme.Opens.IsSchemeTheoreticallyDense U := by
    have h := (isSchemeTheoreticallyDense_opensRange_iff_mono U.ι).mpr inferInstance
    rwa [Scheme.Opens.opensRange_ι] at h
  have : IsSeparated (Over.mk Z.toSpecΓ).hom := ‹IsSeparated Z.toSpecΓ›
  have heq := eq_of_isSchemeTheoreticallyDense (X := Over.mk Z.toSpecΓ) (Y := Over.mk Z.toSpecΓ)
    (Over.homMk (r ≫ U.ι) hq) (𝟙 _) U hdense (by
      change U.ι ≫ r ≫ U.ι = U.ι ≫ 𝟙 Z
      rw [← Category.assoc, hr, Category.id_comp, Category.comp_id])
  have hv' : (r ≫ U.ι).base v = v := congrArg (fun φ => φ.left.base v) heq
  apply hv
  rw [← hv']
  exact (r.base v).2

/-! ### Ampleness across the point -/

open Stacks.NonvanishingLocusRestrict (nonvanishingLocusOn nonvanishingLocusOn_subset
  nonvanishingLocusOn_res)
open Stacks.SectionPowerOpen (nonvanishingOpenOn)
open Stacks.RelativeAmpleLocalOnBase (exists_section_nonvanishingLocusOn_eq
  isAmple_pullbackModule_iff)

/-- **Ampleness glues across a point.** Let `L` be invertible on `X`, `Y ⊆ X` a quasi-compact
quasi-separated open, `v ∈ Y`, and `Y₂ = Y \ {v}` open. Suppose that `L` is ample on a basic open
`Y_h ∋ v` of `Y` and on `Y₂`, that sections of the tensor powers of `L` over `Y₂` extend to `Y`,
and that no open `Ω ⊆ Y` containing `v` has `Ω ∩ Y₂` affine. Then `L` is ample on `Y`. -/
theorem isAmple_pullbackModule_of_basicOpen_of_compl {X : Scheme.{u}} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (Y Y₂ : X.Opens) (hYc : CompactSpace Y.toScheme)
    (hqs : IsQuasiSeparated (Y : Set X)) (v : X) (hvY : v ∈ Y) (hY₂ : Y₂ ≤ Y) (hvY₂ : v ∉ Y₂)
    (hY₂' : ∀ y ∈ Y, y ≠ v → y ∈ Y₂) (h : Γ(X, Y)) (hv : v ∈ X.basicOpen h)
    (ha : Stacks.Ample.IsAmple (X.basicOpen h).toScheme
      (Stacks.AmpleLocallyClosed.pullbackModule (X.basicOpen h).ι L))
    (hb : Stacks.Ample.IsAmple Y₂.toScheme (Stacks.AmpleLocallyClosed.pullbackModule Y₂.ι L))
    (hext : ∀ n : ℕ, ∀ σ : Γ(Stacks.Ample.tensorPowModule X L (n : ℤ), Y₂),
      ∃ τ : Γ(Stacks.Ample.tensorPowModule X L (n : ℤ), Y),
        (Stacks.Ample.tensorPowModule X L (n : ℤ)).presheaf.map (homOfLE hY₂).op τ = σ)
    (hR : ∀ Ω : X.Opens, Ω ≤ Y → v ∈ Ω → ¬ IsAffineOpen (Ω ⊓ Y₂)) :
    Stacks.Ample.IsAmple Y.toScheme (Stacks.AmpleLocallyClosed.pullbackModule Y.ι L) := by
  have hYcpt : IsCompact (Y : Set X) := isCompact_iff_compactSpace.mpr hYc
  -- affineness of an open only depends on its underlying set
  have transfer : ∀ {A B : X.Opens}, IsAffineOpen B → (A : Set X) = B → IsAffineOpen A :=
    fun h e => Opens.ext e ▸ h
  rw [isAmple_pullbackModule_iff]
  refine ⟨hYc, fun y hy => ?_⟩
  by_cases hyv : y = v
  · subst hyv
    obtain ⟨n, hn, s, haff, hmem⟩ := ((isAmple_pullbackModule_iff L (X.basicOpen h)).mp ha).2 y hv
    have : (Stacks.Ample.tensorPowModule X L (n : ℤ)).IsQuasicoherent :=
      Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule L (n : ℤ)
    obtain ⟨u, hu⟩ := exists_section_nonvanishingLocusOn_eq
      (Stacks.Ample.tensorPowModule X L (n : ℤ)) hYcpt hqs h s
    exact ⟨n, hn, u, transfer haff hu, (Set.ext_iff.mp hu y).mpr hmem⟩
  · have hy₂ := hY₂' y hy hyv
    obtain ⟨n, hn, σ, haff, hmem⟩ := ((isAmple_pullbackModule_iff L Y₂).mp hb).2 y hy₂
    obtain ⟨τ, hτ⟩ := hext n σ
    have hres := nonvanishingLocusOn_res (Stacks.Ample.tensorPowModule X L (n : ℤ)) hY₂ τ
    rw [hτ] at hres
    have hvτ : v ∉ nonvanishingLocusOn (Stacks.Ample.tensorPowModule X L (n : ℤ)) Y τ := fun hvτ =>
      hR (nonvanishingOpenOn _ Y τ) (nonvanishingLocusOn_subset _ Y τ) hvτ
        (transfer haff (hres.trans (Set.inter_comm _ _)).symm)
    have heq : nonvanishingLocusOn (Stacks.Ample.tensorPowModule X L (n : ℤ)) Y τ =
        nonvanishingLocusOn (Stacks.Ample.tensorPowModule X L (n : ℤ)) Y₂ σ := by
      rw [hres]
      refine (Set.inter_eq_self_of_subset_right fun z hz => ?_).symm
      exact hY₂' z (nonvanishingLocusOn_subset _ Y τ hz) fun hzv => hvτ (hzv ▸ hz)
    exact ⟨n, hn, τ, transfer haff heq, (Set.ext_iff.mp heq y).mpr hmem⟩

end AlgebraicGeometry

end
