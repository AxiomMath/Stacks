module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import StacksCore.Tactic.StacksAttribute

/-!
# The canonical morphism to the spectrum of global sections

Let `X` be a quasi-compact and quasi-separated scheme and let `f` be a global section of its
structure sheaf. If the basic open `X.basicOpen f` is affine, then the canonical morphism from
`X` to the spectrum of its global sections identifies this basic open with the standard open
defined by `f`.

Consequently an open immersion between quasi-affine schemes is recovered by base change from
the induced morphism between the spectra of their rings of global sections: the standard opens
whose preimages are affine cover a quasi-affine scheme, and on each of them the canonical
morphism is already an isomorphism.

## Main results

* `AlgebraicGeometry.isIso_toSpecΓ_restrict_basicOpen` says that the restriction of the
  canonical morphism to the standard open defined by `f` is an isomorphism.
* `AlgebraicGeometry.isPullback_id_toSpecΓ_of_isOpenImmersion` states that the square formed by
  an open immersion of quasi-affine schemes and the canonical morphisms to spectra of global
  sections is cartesian.

## Implementation notes

The inverse image of `PrimeSpectrum.basicOpen f` under `X.toSpecΓ` is `X.basicOpen f` by
`Scheme.toSpecΓ_preimage_basicOpen`. Thus Mathlib's `morphismRestrict` is precisely the
morphism between the two opens occurring in the source.

A morphism between affine schemes is an isomorphism as soon as it is one on global sections,
because it is then isomorphic as an arrow to the spectrum of that map; this is recorded as
`isIso_of_isAffine_of_isIso_appTop` and is what reduces the first result to the Qcqs lemma.
Mathlib's `isIso_morphismRestrict_iff_isIso_app` is the same criterion for a restriction, but
it assumes the ambient morphism is affine, which `X.toSpecΓ` is not known to be here; only the
one basic open is assumed affine. So the restriction criterion is proved directly from the
arrow isomorphism instead.

In the cartesian square the lower horizontal arrow of the source diagram is displayed as two
arrows; here it is written as their composite `f ≫ V.toSpecΓ`.

## References

* [Stacks Project, Tag 01P8](https://stacks.math.columbia.edu/tag/01P8)
* [Stacks Project, Tag 0ARY](https://stacks.math.columbia.edu/tag/0ARY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A morphism between affine schemes which is an isomorphism on global sections is an
isomorphism: as an arrow it is isomorphic to the spectrum of the map on global sections. -/
lemma isIso_of_isAffine_of_isIso_appTop {A B : Scheme.{u}} [IsAffine A] [IsAffine B]
    (g : A ⟶ B) (hg : IsIso g.appTop) : IsIso g :=
  (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme.{u})
    (arrowIsoSpecΓOfIsAffine g)).mpr (inferInstanceAs (IsIso (Spec.map g.appTop)))

/-- The restriction of a morphism to an affine open with affine preimage is an isomorphism as
soon as it is one on the sections over that open. -/
private lemma isIso_morphismRestrict_of_isAffine {X Y : Scheme.{u}} (g : X ⟶ Y)
    (V : Y.Opens) [IsAffine V] (h₁ : IsAffine (g ⁻¹ᵁ V)) (h₂ : IsIso (g.app V)) :
    IsIso (g ∣_ V) := by
  have hV : V.ι ''ᵁ ⊤ = V := by simp
  refine isIso_of_isAffine_of_isIso_appTop (g ∣_ V) ?_
  rw [morphismRestrict_appTop]
  exact @IsIso.comp_isIso' _ _ _ _ _ _ _
    (Eq.mpr congr(IsIso (Scheme.Hom.app g $hV)) h₂)
    (inferInstanceAs
      (IsIso (X.presheaf.map (eqToHom (image_morphismRestrict_preimage g V ⊤)).op)))

/-- **Stacks Project, Tag 01P8.** If `X` is quasi-compact and quasi-separated
and its basic open defined by `f` is affine, then the canonical morphism to
`Spec Γ(X, ᵊ_X)` restricts to an isomorphism from that basic open onto the
standard open defined by `f`. -/
@[stacks 01P8]
lemma isIso_toSpecΓ_restrict_basicOpen (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (f : Γ(X, ⊤)) (hf : IsAffineOpen (X.basicOpen f)) :
    IsIso (X.toSpecΓ ∣_ PrimeSpectrum.basicOpen f) := by
  have : IsAffine (Scheme.Opens.toScheme (X := Spec Γ(X, ⊤)) (PrimeSpectrum.basicOpen f)) :=
    IsAffineOpen.Spec_basicOpen f
  exact isIso_morphismRestrict_of_isAffine X.toSpecΓ _
    (by simpa only [Scheme.toSpecΓ_preimage_basicOpen, IsAffineOpen] using hf)
    (isIso_ΓSpec_adjunction_unit_app_basicOpen f)

/-- An open immersion which factors as an isomorphism onto `φ ⁻¹ᵁ D` followed by `φ`, where
`φ ∣_ D` is an isomorphism, has range `D`. -/
private lemma opensRange_eq_of_isIso_morphismRestrict {X Y Z : Scheme.{u}} (φ : Y ⟶ Z) (D : Z.Opens)
    [IsIso (φ ∣_ D)] {b : X ⟶ Z} [IsOpenImmersion b] (e : X ≅ (φ ⁻¹ᵁ D).toScheme)
    (he : e.hom ≫ (φ ⁻¹ᵁ D).ι ≫ φ = b) : b.opensRange = D := by
  rw [show b.opensRange = (e.hom ≫ (φ ∣_ D) ≫ D.ι).opensRange from
      TopologicalSpace.Opens.ext (congrArg (fun g : X ⟶ Z => Set.range g)
        (by rw [morphismRestrict_ι, he])),
    Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Opens.opensRange_ι]

/-- An open immersion maps the basic open of the pullback of a section onto the basic open of
that section, provided the latter lies in its range. -/
private lemma image_basicOpen_appTop_of_le_opensRange {U V : Scheme.{u}} (f : U ⟶ V)
    [IsOpenImmersion f] {g : Γ(V, ⊤)} (hg : V.basicOpen g ≤ f.opensRange) :
    f ''ᵁ U.basicOpen (f.appTop g) = V.basicOpen g := by
  rw [← Scheme.preimage_basicOpen_top, f.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hg]

/-- Under an open immersion of quasi-affine schemes, the canonical morphism from the basic open
of the pullback of `g` to `Spec Γ(V, ⊤)` has range the standard open defined by `g`, provided
`V.basicOpen g` is affine and lies in the range. -/
private lemma opensRange_basicOpen_ι_comp_toSpecΓ {U V : Scheme.{u}} (f : U ⟶ V) [IsOpenImmersion f]
    [U.IsQuasiAffine] [V.IsQuasiAffine] {g : Γ(V, ⊤)} (hg : IsAffineOpen (V.basicOpen g))
    (hgr : V.basicOpen g ≤ f.opensRange) :
    ((U.basicOpen (f.appTop g)).ι ≫ f ≫ V.toSpecΓ).opensRange = PrimeSpectrum.basicOpen g := by
  have := isIso_toSpecΓ_restrict_basicOpen V g hg
  refine opensRange_eq_of_isIso_morphismRestrict V.toSpecΓ _
    (f.isoImage _ ≪≫ V.isoOfEq ((image_basicOpen_appTop_of_le_opensRange f hgr).trans
      (V.toSpecΓ_preimage_basicOpen g).symm)) ?_
  simp only [Iso.trans_hom, Category.assoc]
  rw [reassoc_of% Scheme.isoOfEq_hom_ι, reassoc_of% Scheme.Hom.isoImage_hom_ι]

/-- **Stacks Project, Tag 0ARY.** For an open immersion `U ⟶ V` between
quasi-affine schemes, the canonical morphism from `U` to the spectrum of its
global sections is the base change of the induced morphism on spectra along
the canonical morphism from `V`. -/
@[stacks 0ARY]
lemma isPullback_id_toSpecΓ_of_isOpenImmersion (U V : Scheme.{u}) (f : U ⟶ V)
    [IsOpenImmersion f]
    [U.IsQuasiAffine] [V.IsQuasiAffine] :
    IsPullback (𝟙 U) U.toSpecΓ (f ≫ V.toSpecΓ) (Spec.map f.appTop) := by
  let I := { g : Γ(V, ⊤) // IsAffineOpen (V.basicOpen g) ∧
    V.basicOpen g ≤ f.opensRange }
  let 𝒰 : U.OpenCover := U.openCoverOfIsOpenCover
    (fun i : I ↦ U.basicOpen (f.appTop i.1)) <| top_le_iff.mp fun x _ ↦ by
      obtain ⟨_, ⟨_, ⟨g, hg, rfl⟩, rfl⟩, hxg, hgr⟩ :=
        (Scheme.IsQuasiAffine.isBasis_basicOpen V).exists_subset_of_mem_open
          (show f x ∈ f.opensRange by simp) f.opensRange.2
      refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hg, hgr⟩, ?_⟩
      rwa [← Scheme.preimage_basicOpen_top]
  apply Scheme.isPullback_of_openCover (𝟙 U) U.toSpecΓ (f ≫ V.toSpecΓ)
    (Spec.map f.appTop) 𝒰
  intro i
  have hWaff : IsAffine (U.basicOpen (f.appTop i.1)) :=
    (IsAffine.iff_of_isIso (f.isoImage _ ≪≫
      V.isoOfEq (image_basicOpen_appTop_of_le_opensRange f i.2.2)).hom).2 i.2.1
  have := isIso_toSpecΓ_restrict_basicOpen U (f.appTop i.1) hWaff
  have hRangeU : ((U.basicOpen (f.appTop i.1)).ι ≫ U.toSpecΓ).opensRange =
      PrimeSpectrum.basicOpen (f.appTop i.1) :=
    opensRange_eq_of_isIso_morphismRestrict U.toSpecΓ _
      (U.isoOfEq (U.toSpecΓ_preimage_basicOpen _).symm)
      (by rw [← Category.assoc, Scheme.isoOfEq_hom_ι])
  have hfactor : (𝒰.pullback₁ (𝟙 U)).f i =
      𝒰.pullbackHom (𝟙 U) i ≫ 𝒰.f i := by
    show pullback.fst (𝟙 U) (𝒰.f i) =
      pullback.snd (𝟙 U) (𝒰.f i) ≫ 𝒰.f i
    rw [← pullback.condition]
    simp
  have : IsIso (𝒰.pullbackHom (𝟙 U) i) := by
    dsimp [Scheme.Cover.pullbackHom]
    exact pullback_snd_iso_of_left_iso (f := 𝟙 U) (g := 𝒰.f i)
  have : IsOpenImmersion
      (((𝒰.pullback₁ (𝟙 U)).f i) ≫ U.toSpecΓ) := by
    rw [hfactor]
    infer_instance
  apply IsOpenImmersion.isPullback
  · simp only [Category.assoc, ← Scheme.toSpecΓ_naturality, hfactor]
  · show Spec.map f.appTop ⁻¹ᵁ
      ((U.basicOpen (f.appTop i.1)).ι ≫ f ≫ V.toSpecΓ).opensRange = _
    rw [opensRange_basicOpen_ι_comp_toSpecΓ f i.2.1 i.2.2, SpecMap_preimage_basicOpen]
    simp only [hfactor, Category.assoc, Scheme.Hom.opensRange_comp_of_isIso]
    exact hRangeU.symm

end AlgebraicGeometry
