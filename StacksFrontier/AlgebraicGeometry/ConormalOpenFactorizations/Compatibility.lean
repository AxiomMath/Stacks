module

public import StacksFrontier.AlgebraicGeometry.ConormalOpenFactorizations.Basic
public import StacksFrontier.AlgebraicGeometry.DiagonalConormal.Retraction

/-!
# Compatibility of the conormal quotient map across open factorizations

This file proves the part (1) assertion "compatibility of open factorizations" of
[Stacks, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3): for two factorizations of an
immersion `i : Z ⟶ X` as a closed immersion into an open subscheme, the quotient generators
attached to one and the same section of the ambient structure sheaf agree after restriction to
any common open of `Z`.

`StacksFrontier.AlgebraicGeometry.ConormalOpenFactorizations.Basic` reduces each factorization to
the coborder one. What is added here is the bookkeeping that makes the reduction applicable to
*both* factorizations at the same open of `i.coborderRange`, and the section of the coborder ideal
sheaf that the two then share.

## The common open, and why it is an image

The two factorizations are compared at `O = (j₁ ''ᵁ W₁) ⊓ (j₂ ''ᵁ W₂)`, where `jₖ` is the
inclusion `Uₖ ⟶ i.coborderRange` provided by `Stacks.Conormal.le_coborderRange_of_comp_eq`.
Images rather than, say, `i.coborderRange.ι ⁻¹ᵁ V` are used deliberately: with images,
`jₖ ⁻¹ᵁ O ≤ Wₖ`, so the section of the ideal sheaf of `iₖ` that is needed there is a *restriction*
of the given `xₖ` and no existence statement is required for it. The one section that must be
produced is `y` over `O` for the coborder factorization, and its existence is
`Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff` applied to the vanishing
`appLE_eq_zero`, which is itself read off from `x₁`.

Consequently **no part of the statement's presentation data is used**: the affine hypothesis `hV`, the
ideal `I`, the identification `e` of the fibre and the compatibility `he` play no role, and
`generator_eq_of_two_factorizations` is stated for an arbitrary section `r` of `Γ(X, V)` over an
arbitrary open `V`. Had the comparison been made at `i.coborderRange.ι ⁻¹ᵁ V` instead, three
sections would have had to be produced rather than one, and each would have needed the
presentation to see that `a ∈ I` dies on `i ⁻¹ᵁ V`.

## Main results

* `Stacks.Conormal.OpenFactorizations.app_appLE_comp`: naming a section through a composite —
  restricting along `g` and then along `f` is restricting along `f ≫ g`. Used twice, at
  `(jₖ, C.ι, Uₖ.ι)` and at `(i.liftCoborder, C.ι, i)`.
* `Stacks.Conormal.OpenFactorizations.appLE_eq_zero`: an ambient section naming a section of the
  ideal sheaf of `k` over `W` restricts to zero on every open of `Z` inside `k ⁻¹ᵁ W`.
* `Stacks.Conormal.OpenFactorizations.idealRestrictHomOfCompEq_app_eq`: the two sections
  correspond under the comparison of `Basic`, by injectivity of the inclusion of the ideal sheaf
  into the structure sheaf on sections.
* `Stacks.Conormal.OpenFactorizations.generator_eq_liftCoborder`: one factorization against the
  coborder one.
* `Stacks.Conormal.OpenFactorizations.generator_eq_of_two_factorizations`: the comparison of two
  factorizations, for an arbitrary ambient section.
* `Stacks.Conormal.OpenFactorizations.conormalQuotientMap_restrict_factorization`: **the tagged
  statement**, carrying the `stacks` attribute.

## Universe situation

A single universe `u`, as in the tagged statements.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe u

namespace Stacks.Conormal.OpenFactorizations

open Stacks.Conormal Stacks.Conormal.AffineCotangent

/-! ### Naming a section through a composite -/

/-- Restricting `r` along `g` and then along `f` is restricting along `i`, when `f ≫ g = i`. -/
private theorem appLE_appLE_eq_of_comp_eq {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (i : A ⟶ C)
    (hfg : f ≫ g = i) (V : C.Opens) (O : B.Opens) (S : A.Opens) (hO : O ≤ g ⁻¹ᵁ V)
    (hS : S ≤ f ⁻¹ᵁ O) (hi : S ≤ i ⁻¹ᵁ V) (r : Γ(C, V)) :
    (f.appLE O S hS).hom ((g.appLE V O hO).hom r) = (i.appLE V S hi).hom r := by
  have hg : (f ≫ g).appLE V S (hS.trans (f.preimage_mono hO)) = i.appLE V S hi :=
    Stacks.DiagonalConormal.appLE_congr hfg _ _ _ _
  exact congr($((Scheme.Hom.appLE_comp_appLE f g V O S hO hS).trans hg) r)

/-- **Naming a section through a composite.** Restricting `r : Γ(C, V)` to an open `O` of `B`
along `g`, then along `f` to `f ⁻¹ᵁ O`, is restricting it along `f ≫ g`.

`AlgebraicGeometry.Scheme.Hom.appLE` carries a containment proof mentioning the morphism, so the
passage from `f ≫ g` to the separately named `i` cannot be a `rw`; it is
`Stacks.DiagonalConormal.appLE_congr`, which substitutes and then uses proof irrelevance. -/
theorem app_appLE_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (i : A ⟶ C)
    (hfg : f ≫ g = i) (V : C.Opens) (O : B.Opens) (hO : O ≤ g ⁻¹ᵁ V)
    (h' : f ⁻¹ᵁ O ≤ i ⁻¹ᵁ V) (r : Γ(C, V)) :
    (f.app O).hom ((g.appLE V O hO).hom r) = (i.appLE V (f ⁻¹ᵁ O) h').hom r := by
  have ha : f.appLE O (f ⁻¹ᵁ O) le_rfl = f.app O := Scheme.Hom.appLE_eq_app _
  rw [← ha]
  exact appLE_appLE_eq_of_comp_eq f g i hfg V O _ hO le_rfl h' r

/-- **An ambient section naming a section of the ideal sheaf dies on the source.** If `r` names a
section `x` of the ideal sheaf of `k` over `W` — that is, if `r` restricted to `W` along `U.ι` is
the image of `x` in the structure sheaf — then `r` restricts to zero on every open `S` of `Z`
inside `k ⁻¹ᵁ W`.

This is what produces the section of the coborder ideal sheaf in
`generator_eq_of_two_factorizations` without any appeal to the presentation data of the statement: the
vanishing needed there is read off from one of the two given sections. -/
theorem appLE_eq_zero {Z X : Scheme.{u}} (i : Z ⟶ X) (V : X.Opens)
    (U : X.Opens) (k : Z ⟶ U.toScheme) (hfac : k ≫ U.ι = i)
    (W : U.toScheme.Opens) (hW : W ≤ U.ι ⁻¹ᵁ V) (r : Γ(X, V))
    (x : (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom).val.obj (.op W))
    (hx : (U.ι.appLE V W hW).hom r =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom k.toLRSHom.toShHom))).val.app (.op W) x)
    (S : Z.Opens) (hS : S ≤ i ⁻¹ᵁ V) (hSk : S ≤ k ⁻¹ᵁ W) :
    (i.appLE V S hS).hom r = 0 := by
  rw [← appLE_appLE_eq_of_comp_eq k U.ι i hfac V W S hW hSk hS r, hx]
  show (Z.presheaf.map (homOfLE hSk).op).hom ((k.app W).hom _) = 0
  rw [Sections.app_idealSheaf_section_eq_zero, map_zero]

/-! ### The two sections correspond -/

/-- A composite of morphisms of sheaves of modules, on sections over one open. -/
theorem comp_val_app {A : Scheme.{u}}
    {M N P : SheafOfModules.{u} (structureSheafRing A.toLocallyRingedSpace.toRingedSpace)}
    (f : M ⟶ N) (g : N ⟶ P) (O : A.Opens) (t : M.val.obj (.op O)) :
    (f ≫ g).val.app (.op O) t = g.val.app (.op O) (f.val.app (.op O) t) :=
  rfl

/-- **The two sections named by the same ambient element correspond under the comparison.** The
section of the coborder ideal sheaf over `O` named by `r` is carried by
`Stacks.Conormal.OpenFactorizations.idealRestrictHomOfCompEq` to the restriction to `j ⁻¹ᵁ O` of
the section of the ideal sheaf of `k` named by `r`.

Both are sections of the same sheaf over the same open, so by
`Stacks.Conormal.Locality.idealSheaf_section_injective` it suffices to compare their images in
the structure sheaf; `idealRestrictHomOfCompEq_comp_ι` computes the first and `app_appLE_comp`
the second. -/
theorem idealRestrictHomOfCompEq_app_eq {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (V : X.Opens) (r : Γ(X, V))
    (U : X.Opens) (k : Z ⟶ U.toScheme) [IsClosedImmersion k] (hfac : k ≫ U.ι = i)
    (W : U.toScheme.Opens) (hW : W ≤ U.ι ⁻¹ᵁ V)
    (x : (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom).val.obj (.op W))
    (hx : (U.ι.appLE V W hW).hom r =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom k.toLRSHom.toShHom))).val.app (.op W) x)
    (O : i.coborderRange.toScheme.Opens) (hO : O ≤ i.coborderRange.ι ⁻¹ᵁ V)
    (hOW : X.homOfLE (le_coborderRange_of_comp_eq i U k hfac) ⁻¹ᵁ O ≤ W)
    (y : (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom).val.obj (.op O))
    (hy : (i.coborderRange.ι.appLE V O hO).hom r =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i.liftCoborder.toLRSHom.toShHom))).val.app (.op O) y) :
    (idealRestrictHomOfCompEq k (X.homOfLE (le_coborderRange_of_comp_eq i U k hfac))
        i.liftCoborder (comp_homOfLE_eq_liftCoborder i U k hfac)).val.app (.op O) y =
      (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom).val.map (homOfLE hOW).op x := by
  have hW' : X.homOfLE (le_coborderRange_of_comp_eq i U k hfac) ⁻¹ᵁ O ≤ U.ι ⁻¹ᵁ V :=
    hOW.trans hW
  have hx' : (U.ι.appLE V (X.homOfLE (le_coborderRange_of_comp_eq i U k hfac) ⁻¹ᵁ O) hW').hom r =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom k.toLRSHom.toShHom))).val.app
          (.op (X.homOfLE (le_coborderRange_of_comp_eq i U k hfac) ⁻¹ᵁ O))
          ((Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom).val.map
            (homOfLE hOW).op x) := by
    rw [PresheafOfModules.naturality_apply, ← hx]
    exact congr($(U.ι.appLE_map hW (homOfLE hOW).op) r).symm
  have hmor := idealRestrictHomOfCompEq_comp_ι k
    (X.homOfLE (le_coborderRange_of_comp_eq i U k hfac)) i.liftCoborder
    (comp_homOfLE_eq_liftCoborder i U k hfac)
  have h0 := congrArg (fun m => SheafOfModules.Hom.val m |>.app (.op O) y) hmor
  refine Locality.idealSheaf_section_injective k _ ?_
  show (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom k.toLRSHom.toShHom))).val.app
          (.op (X.homOfLE (le_coborderRange_of_comp_eq i U k hfac) ⁻¹ᵁ O))
      ((idealRestrictHomOfCompEq k (X.homOfLE (le_coborderRange_of_comp_eq i U k hfac))
        i.liftCoborder (comp_homOfLE_eq_liftCoborder i U k hfac)).val.app (.op O) y) = _
  refine h0.trans ?_
  show ((X.homOfLE (le_coborderRange_of_comp_eq i U k hfac)).app O).hom
      ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i.liftCoborder.toLRSHom.toShHom))).val.app (.op O) y) = _
  rw [← hy, app_appLE_comp _ i.coborderRange.ι U.ι (X.homOfLE_ι _) V O hO hW' r, hx']
  rfl

/-! ### One factorization against the coborder one -/

/-- **One factorization against the coborder one, on named generators.** With `r` naming `x` over
`W` and `y` over `O`, the quotient generator computed at the coborder factorization and the one
computed at `(U, k)` agree after restriction to `T`.

`Stacks.Conormal.OpenFactorizations.conormalQuotientMap_eq_of_factorization` compares the two at
`j ⁻¹ᵁ O`, and `Stacks.Conormal.Locality.conormalQuotientMap_restrict` moves the second from
there up to `W`. -/
theorem generator_eq_liftCoborder {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (V : X.Opens) (r : Γ(X, V))
    (U : X.Opens) (k : Z ⟶ U.toScheme) [IsClosedImmersion k] (hfac : k ≫ U.ι = i)
    (W : U.toScheme.Opens) (hW : W ≤ U.ι ⁻¹ᵁ V)
    (x : (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom).val.obj (.op W))
    (hx : (U.ι.appLE V W hW).hom r =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom k.toLRSHom.toShHom))).val.app (.op W) x)
    (O : i.coborderRange.toScheme.Opens) (hO : O ≤ i.coborderRange.ι ⁻¹ᵁ V)
    (hOW : X.homOfLE (le_coborderRange_of_comp_eq i U k hfac) ⁻¹ᵁ O ≤ W)
    (y : (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom).val.obj (.op O))
    (hy : (i.coborderRange.ι.appLE V O hO).hom r =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i.liftCoborder.toLRSHom.toShHom))).val.app (.op O) y)
    (T : Z.Opens) (hT : T ≤ i.liftCoborder ⁻¹ᵁ O) (hTW : T ≤ k ⁻¹ᵁ W) :
    (conormalSheaf i).val.map (homOfLE hT).op
        ((conormalQuotientMap i i.coborderRange i.liftCoborder
          i.liftCoborder_ι).val.app (.op O) y) =
      (conormalSheaf i).val.map (homOfLE hTW).op
        ((conormalQuotientMap i U k hfac).val.app (.op W) x) := by
  have hT' : T ≤ k ⁻¹ᵁ (X.homOfLE (le_coborderRange_of_comp_eq i U k hfac) ⁻¹ᵁ O) := by
    rw [← comp_homOfLE_eq_liftCoborder i U k hfac] at hT
    exact hT
  refine (conormalQuotientMap_eq_of_factorization i U k hfac O T hT hT' y _
    (idealRestrictHomOfCompEq_app_eq i V r U k hfac W hW x hx O hO hOW y hy)).trans ?_
  rw [← Locality.conormalQuotientMap_restrict i U k hfac hOW x]
  exact ((conormalSheaf i).val.map_comp_apply
    (homOfLE (k.preimage_mono hOW)).op (homOfLE hT').op _).symm

/-! ### Two factorizations -/

/-- The preimage under `i.liftCoborder` of the image of `W` is the preimage of `W` under `k`. -/
private theorem liftCoborder_preimage_image {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (k : Z ⟶ U.toScheme) [IsClosedImmersion k] (hfac : k ≫ U.ι = i)
    (W : U.toScheme.Opens) :
    i.liftCoborder ⁻¹ᵁ (X.homOfLE (le_coborderRange_of_comp_eq i U k hfac) ''ᵁ W) = k ⁻¹ᵁ W := by
  rw [← comp_homOfLE_eq_liftCoborder i U k hfac, Scheme.Hom.comp_preimage,
    Scheme.Hom.preimage_image_eq]

/-- **Compatibility of two open factorizations, for an arbitrary ambient section.** This is the
assertion of part (1) of the tag with its presentation data removed: no affineness of `V`, no ideal, no
identification of the fibre. Only that `r : Γ(X, V)` names a section of each of the two ideal
sheaves. -/
theorem generator_eq_of_two_factorizations {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (V : X.Opens) (r : Γ(X, V))
    (U₁ U₂ : X.Opens)
    (i₁ : Z ⟶ U₁.toScheme) [IsClosedImmersion i₁]
    (i₂ : Z ⟶ U₂.toScheme) [IsClosedImmersion i₂]
    (hfac₁ : i₁ ≫ U₁.ι = i) (hfac₂ : i₂ ≫ U₂.ι = i)
    (W₁ : U₁.toScheme.Opens) (hW₁ : W₁ ≤ U₁.ι ⁻¹ᵁ V)
    (W₂ : U₂.toScheme.Opens) (hW₂ : W₂ ≤ U₂.ι ⁻¹ᵁ V)
    (x₁ : (Stacks.ClosedImmersion.idealSheaf i₁.toLRSHom.toShHom).val.obj (.op W₁))
    (x₂ : (Stacks.ClosedImmersion.idealSheaf i₂.toLRSHom.toShHom).val.obj (.op W₂))
    (hx₁ : (U₁.ι.appLE V W₁ hW₁).hom r =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i₁.toLRSHom.toShHom))).val.app (.op W₁) x₁)
    (hx₂ : (U₂.ι.appLE V W₂ hW₂).hom r =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i₂.toLRSHom.toShHom))).val.app (.op W₂) x₂)
    (T : Z.Opens) (hT₁ : T ≤ i₁ ⁻¹ᵁ W₁) (hT₂ : T ≤ i₂ ⁻¹ᵁ W₂) :
    (conormalSheaf i).val.map (homOfLE hT₁).op
        ((conormalQuotientMap i U₁ i₁ hfac₁).val.app (.op W₁) x₁) =
      (conormalSheaf i).val.map (homOfLE hT₂).op
        ((conormalQuotientMap i U₂ i₂ hfac₂).val.app (.op W₂) x₂) := by
  set j₁ := X.homOfLE (le_coborderRange_of_comp_eq i U₁ i₁ hfac₁) with hj₁
  set j₂ := X.homOfLE (le_coborderRange_of_comp_eq i U₂ i₂ hfac₂) with hj₂
  set O : i.coborderRange.toScheme.Opens := (j₁ ''ᵁ W₁) ⊓ (j₂ ''ᵁ W₂) with hOdef
  have hOW₁ : j₁ ⁻¹ᵁ O ≤ W₁ :=
    (j₁.preimage_mono inf_le_left).trans (j₁.preimage_image_eq W₁).le
  have hOW₂ : j₂ ⁻¹ᵁ O ≤ W₂ :=
    (j₂.preimage_mono inf_le_right).trans (j₂.preimage_image_eq W₂).le
  have himg₁ : j₁ ''ᵁ W₁ ≤ i.coborderRange.ι ⁻¹ᵁ V := by
    have hle : W₁ ≤ j₁ ⁻¹ᵁ (i.coborderRange.ι ⁻¹ᵁ V) := by
      rw [hj₁, ← Scheme.Hom.comp_preimage, X.homOfLE_ι]
      exact hW₁
    exact Set.image_subset_iff.mpr hle
  have hO : O ≤ i.coborderRange.ι ⁻¹ᵁ V := inf_le_left.trans himg₁
  have hL₁ := liftCoborder_preimage_image i U₁ i₁ hfac₁ W₁
  have hL₂ := liftCoborder_preimage_image i U₂ i₂ hfac₂ W₂
  have hTO : T ≤ i.liftCoborder ⁻¹ᵁ O := le_inf (hL₁ ▸ hT₁) (hL₂ ▸ hT₂)
  have hSV : i.liftCoborder ⁻¹ᵁ O ≤ i ⁻¹ᵁ V := by
    have h := i.liftCoborder.preimage_mono hO
    rw [← Scheme.Hom.comp_preimage, i.liftCoborder_ι] at h
    exact h
  have hS₁ : i.liftCoborder ⁻¹ᵁ O ≤ i₁ ⁻¹ᵁ W₁ :=
    (i.liftCoborder.preimage_mono inf_le_left).trans hL₁.le
  have hvan : (i.liftCoborder.app O).hom ((i.coborderRange.ι.appLE V O hO).hom r) = 0 := by
    rw [app_appLE_comp i.liftCoborder i.coborderRange.ι i i.liftCoborder_ι V O hO hSV r]
    exact appLE_eq_zero i V U₁ i₁ hfac₁ W₁ hW₁ r x₁ hx₁ _ hSV hS₁
  obtain ⟨y, hy⟩ := (Sections.exists_idealSheaf_section_iff i.liftCoborder O _).mpr hvan
  exact (generator_eq_liftCoborder i V r U₁ i₁ hfac₁ W₁ hW₁ x₁ hx₁ O hO hOW₁ y hy.symm
      T hTO hT₁).symm.trans
    (generator_eq_liftCoborder i V r U₂ i₂ hfac₂ W₂ hW₂ x₂ hx₂ O hO hOW₂ y hy.symm T hTO hT₂)

/-! ### The tagged statement -/

/-- **[Stacks, Tag 01R3], part (1): compatibility of open factorizations.** The quotient
identifications from two open factorizations agree on common conormal sections: images of the
same ambient ideal generator agree after restriction to any common source open.

This is `generator_eq_of_two_factorizations` at `r = (a : Γ(X, V))`. The presentation data
`hV`, `I`, `e`, `he` is carried because the tagged statement carries it; the proof does not use it, and the
statement proved is the stronger one with `a : I` replaced by an arbitrary `r : Γ(X, V)` and the
presentation dropped altogether. -/
@[stacks 01R3 "part (1): compatibility of open factorizations"]
theorem conormalQuotientMap_restrict_factorization {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (V : X.Opens) (hV : IsAffineOpen V)
    (I : Ideal Γ(X, V))
    (e : Limits.pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I)))
    (he : Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (U₁ U₂ : X.Opens)
    (i₁ : Z ⟶ U₁.toScheme) [IsClosedImmersion i₁]
    (i₂ : Z ⟶ U₂.toScheme) [IsClosedImmersion i₂]
    (hfac₁ : i₁ ≫ U₁.ι = i) (hfac₂ : i₂ ≫ U₂.ι = i)
    (W₁ : U₁.toScheme.Opens) (hW₁ : W₁ ≤ U₁.ι ⁻¹ᵁ V)
    (W₂ : U₂.toScheme.Opens) (hW₂ : W₂ ≤ U₂.ι ⁻¹ᵁ V)
    (a : I)
    (x₁ : (Stacks.ClosedImmersion.idealSheaf i₁.toLRSHom.toShHom).val.obj (.op W₁))
    (x₂ : (Stacks.ClosedImmersion.idealSheaf i₂.toLRSHom.toShHom).val.obj (.op W₂))
    (hx₁ : (U₁.ι.appLE V W₁ hW₁).hom (a : Γ(X, V)) =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i₁.toLRSHom.toShHom))).val.app (.op W₁) x₁)
    (hx₂ : (U₂.ι.appLE V W₂ hW₂).hom (a : Γ(X, V)) =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i₂.toLRSHom.toShHom))).val.app (.op W₂) x₂)
    (T : Z.Opens) (hT₁ : T ≤ i₁ ⁻¹ᵁ W₁) (hT₂ : T ≤ i₂ ⁻¹ᵁ W₂) :
    (conormalSheaf i).val.map (homOfLE hT₁).op
        ((conormalQuotientMap i U₁ i₁ hfac₁).val.app (.op W₁) x₁) =
      (conormalSheaf i).val.map (homOfLE hT₂).op
        ((conormalQuotientMap i U₂ i₂ hfac₂).val.app (.op W₂) x₂) := by
  -- `he` is a hypothesis of the tagged statement, so it is kept verbatim; the proof does not need it.
  -- Mentioning it keeps the statement's binder name while satisfying the unused-variable linter.
  have _ := he
  exact generator_eq_of_two_factorizations i V (a : Γ(X, V)) U₁ U₂ i₁ i₂ hfac₁ hfac₂
    W₁ hW₁ W₂ hW₂ x₁ x₂ hx₁ hx₂ T hT₁ hT₂

end Stacks.Conormal.OpenFactorizations

end
