module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ReducedThickening.NeighborhoodThickening
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionToClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SectionsExtendFromCompletion
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.Thickening

/-!
# Sections near a closed subscheme are unchanged by a thickening of the ambient scheme

Let `i : X' ⟶ X` be a thickening, let `Y ⊆ X` and `Y' ⊆ X'` be closed subschemes given by their
ideal sheaves, and let `jY : Y' ⟶ Y` be a thickening lying over `i`.  The open neighbourhoods of
`Y` in `X` and those of `Y'` in `X'` correspond to one another, by taking inverse images along
`i` in one direction and images under the homeomorphism `i` induces in the other.

A finite étale cover of a neighbourhood `V` of `Y` has the same sections over `V` as it has over
the matching neighbourhood of `Y'`, because base change along a thickening is an equivalence on
finite étale covers and sections of a cover are morphisms from the cover of the base by itself.
The extension property for sections near a closed subscheme — every section over the closed
subscheme is the restriction of a section over some neighbourhood, and two sections over a
neighbourhood that agree over the closed subscheme agree over a smaller one — therefore holds for
`Y ⊆ X` as soon as it holds for `Y' ⊆ X'`.  Since that property implies full faithfulness of the
restriction functor `colim_V FÉt_V ⟶ FÉt_Y`, the full faithfulness statement passes from the thin
pair to the thick one as well.

## Main results

* `Stacks.FundamentalGroup.bijective_restrictSection_of_isThickening` — sections of a finite
  étale cover restrict bijectively along a thickening.
* `Stacks.FundamentalGroup.sectionsExtendNearSubscheme_of_isThickening` — the extension property
  for sections of finite étale covers near a closed subscheme passes from `Y' ⊆ X'` to `Y ⊆ X`.
* `Stacks.FundamentalGroup.finiteEtaleColimitFullyFaithful_of_isThickening` — full faithfulness
  of `colim_V FÉt_V ⟶ FÉt_Y` passes from `Y' ⊆ X'` to `Y ⊆ X`.
* `Stacks.FundamentalGroup.finiteEtaleColimitFullyFaithful_of_completionComplete_of_isThickening`
  — the same conclusion from full faithfulness of the completion functor on `X'`.

## Implementation notes

The neighbourhood of `Y` matching a neighbourhood `V''` of `Y'` is the image of the latter under
the order isomorphism `Stacks.Thickenings.IsThickening.opensCongr` on opens.  Its inverse image
along `i` is `V''` again, but only up to an equality of opens rather than by definition, so the
section produced over `V''` is carried to the inverse image by the inclusion of opens
`AlgebraicGeometry.Scheme.homOfLE` attached to that equality.

## References

* [Stacks Project, Tag 0BQB](https://stacks.math.columbia.edu/tag/0BQB)
* [Stacks Project, Tag 0ELA](https://stacks.math.columbia.edu/tag/0ELA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Thickenings

universe u

namespace Stacks.FundamentalGroup

/-! ### Sections restrict bijectively along a thickening -/

/-- **Sections of a finite étale cover restrict bijectively along a thickening.**  Let `U` be a
finite étale cover of `Z`, let `g : T ⟶ Z`, and let `j : T' ⟶ T` be a thickening.  Then a section
of `U` over `g` is determined by its restriction along `j`, and every section over `j ≫ g` arises
this way: base change along a thickening is an equivalence of categories of finite étale covers,
and a section is a morphism out of the cover of the base by itself. -/
theorem bijective_restrictSection_of_isThickening {Z T T' : Scheme.{u}} (g : T ⟶ Z)
    {j : T' ⟶ T} (hj : IsThickening j) (U : FiniteEtaleOver Z) :
    Function.Bijective (fun s : {s : T ⟶ U.left // s ≫ U.hom = g} =>
      (⟨j ≫ s.1, by rw [Category.assoc, s.2]⟩ :
        {t : T' ⟶ U.left // t ≫ U.hom = j ≫ g})) :=
  have := finiteEtaleBaseChange_isEquivalence_of_isThickening j hj
  bijective_restrictSection_of_fullyFaithful g j (j ≫ g) rfl (.ofFullyFaithful _) U

/-! ### The neighbourhood of `Y` matching a neighbourhood of `Y'` -/

variable {X X' : Scheme.{u}} {i : X' ⟶ X} (hi : IsThickening i)
  (Y : X.IdealSheafData) (Y' : X'.IdealSheafData) (jY : Y'.subscheme ⟶ Y.subscheme)
  (hjY : jY ≫ Y.subschemeι = Y'.subschemeι ≫ i) (hjYt : IsThickening jY)

include hi hjY hjYt

/-- **A neighbourhood of `Y'` contained in the inverse image of a neighbourhood `V` of `Y`
matches a neighbourhood of `Y` contained in `V`.** -/
theorem Neighborhood.le_image {V : Neighborhood X Y} {V' : Neighborhood X' Y'}
    (hV' : Neighborhood.open X' Y' V' ≤ i ⁻¹ᵁ Neighborhood.open X Y V) :
    V ≤ Neighborhood.image hi Y Y' jY hjY hjYt V' :=
  show hi.opensCongr (Neighborhood.open X' Y' V') ≤ Neighborhood.open X Y V from
    (hi.opensCongr.monotone hV').trans (hi.opensCongr_preimage _).le

/-- **The inverse image of the open matching a neighbourhood of `Y'` is that neighbourhood.** -/
theorem Neighborhood.preimage_open_image (V' : Neighborhood X' Y') :
    i ⁻¹ᵁ Neighborhood.open X Y (Neighborhood.image hi Y Y' jY hjY hjYt V') =
      Neighborhood.open X' Y' V' :=
  hi.preimage_opensCongr _

/-- **The chosen factorisation of `Y'` through the inverse image of the open matching a
neighbourhood `V'`, followed by the inclusion into `V'`, is the chosen factorisation through
`V'`.**  Both are factorisations of the closed immersion of `Y'` through the same open. -/
theorem Neighborhood.toSchemeHom_comp_homOfLE_image (V' : Neighborhood X' Y') :
    Neighborhood.toSchemeHom X' Y' (Neighborhood.preimage hi Y Y' jY hjY hjYt
          (Neighborhood.image hi Y Y' jY hjY hjYt V')) ≫
        X'.homOfLE (Neighborhood.preimage_open_image hi Y Y' jY hjY hjYt V').le =
      Neighborhood.toSchemeHom X' Y' V' := by
  refine (cancel_mono (Neighborhood.open X' Y' V').ι).1 ?_
  calc (Neighborhood.toSchemeHom X' Y' (Neighborhood.preimage hi Y Y' jY hjY hjYt
            (Neighborhood.image hi Y Y' jY hjY hjYt V')) ≫
          X'.homOfLE (Neighborhood.preimage_open_image hi Y Y' jY hjY hjYt V').le) ≫
        (Neighborhood.open X' Y' V').ι
      = Neighborhood.toSchemeHom X' Y' (Neighborhood.preimage hi Y Y' jY hjY hjYt
            (Neighborhood.image hi Y Y' jY hjY hjYt V')) ≫
          (X'.homOfLE (Neighborhood.preimage_open_image hi Y Y' jY hjY hjYt V').le ≫
            (Neighborhood.open X' Y' V').ι) := Category.assoc _ _ _
    _ = Neighborhood.toSchemeHom X' Y' (Neighborhood.preimage hi Y Y' jY hjY hjYt
            (Neighborhood.image hi Y Y' jY hjY hjYt V')) ≫
          (i ⁻¹ᵁ Neighborhood.open X Y (Neighborhood.image hi Y Y' jY hjY hjYt V')).ι :=
        congrArg (fun k => Neighborhood.toSchemeHom X' Y' (Neighborhood.preimage hi Y Y' jY hjY
          hjYt (Neighborhood.image hi Y Y' jY hjY hjYt V')) ≫ k) (Scheme.homOfLE_ι X' _)
    _ = Y'.subschemeι := Neighborhood.toSchemeHom_fac X' Y' _
    _ = Neighborhood.toSchemeHom X' Y' V' ≫ (Neighborhood.open X' Y' V').ι :=
        (Neighborhood.toSchemeHom_fac X' Y' V').symm

/-- **The restriction of the thickening over the open matching a neighbourhood `V'` of `Y'` is
the inclusion of opens into `V'` followed by the restriction of the thickening over a
neighbourhood of `Y` containing that open.** -/
theorem morphismRestrict_image_comp_homOfLE {V : Neighborhood X Y} {V' : Neighborhood X' Y'}
    (hV' : Neighborhood.open X' Y' V' ≤ i ⁻¹ᵁ Neighborhood.open X Y V)
    (hWle : Neighborhood.open X Y (Neighborhood.image hi Y Y' jY hjY hjYt V') ≤
      Neighborhood.open X Y V) :
    (i ∣_ Neighborhood.open X Y (Neighborhood.image hi Y Y' jY hjY hjYt V')) ≫ X.homOfLE hWle
      = X'.homOfLE (Neighborhood.preimage_open_image hi Y Y' jY hjY hjYt V').le ≫
          X'.homOfLE hV' ≫ (i ∣_ Neighborhood.open X Y V) :=
  (morphismRestrict_comp_homOfLE hi Y Y' jY hjY hjYt hWle).trans
    ((congrArg (fun k => k ≫ (i ∣_ Neighborhood.open X Y V))
        (X'.homOfLE_homOfLE (Neighborhood.preimage_open_image hi Y Y' jY hjY hjYt V').le
          hV').symm).trans (Category.assoc _ _ _))

/-! ### Transport of the extension property -/

/-- **Sections over a closed subscheme extend near it as soon as they do after a thickening of the
ambient scheme.**  The existence half of `sectionsExtendNearSubscheme_of_isThickening`. -/
theorem sectionsExtendNearSubscheme_exists_of_isThickening
    (hext : ∀ (V : Neighborhood X' Y') (U : FiniteEtaleOver (Neighborhood.open X' Y' V).toScheme)
      (t : Y'.subscheme ⟶ U.left), t ≫ U.hom = Neighborhood.toSchemeHom X' Y' V →
      ∃ (V' : Neighborhood X' Y') (e : V ⟶ V')
        (s : (Neighborhood.open X' Y' V').toScheme ⟶ U.left),
        s ≫ U.hom = X'.homOfLE e.le ∧ Neighborhood.toSchemeHom X' Y' V' ≫ s = t) :
    ∀ (V : Neighborhood X Y) (U : FiniteEtaleOver (Neighborhood.open X Y V).toScheme)
      (t : Y.subscheme ⟶ U.left), t ≫ U.hom = Neighborhood.toSchemeHom X Y V →
      ∃ (V' : Neighborhood X Y) (e : V ⟶ V')
        (s : (Neighborhood.open X Y V').toScheme ⟶ U.left),
        s ≫ U.hom = X.homOfLE e.le ∧ Neighborhood.toSchemeHom X Y V' ≫ s = t := by
  intro V U t ht
  have hab : (jY ≫ t) ≫ U.hom =
      Neighborhood.toSchemeHom X' Y' (Neighborhood.preimage hi Y Y' jY hjY hjYt V) ≫
        (i ∣_ Neighborhood.open X Y V) := by
    rw [Neighborhood.subschemeHom_comp_morphismRestrict hi Y Y' jY hjY hjYt V,
      Category.assoc, ht]
  obtain ⟨V'', j, s'', hs''hom, hs''t⟩ := hext
    (Neighborhood.preimage hi Y Y' jY hjY hjYt V)
    ((finiteEtaleBaseChange (i ∣_ Neighborhood.open X Y V)).obj U)
    (baseChangeLift U (i ∣_ Neighborhood.open X Y V) hab)
    (baseChangeLift_hom U (i ∣_ Neighborhood.open X Y V) hab)
  have hjle : Neighborhood.open X' Y' V'' ≤ i ⁻¹ᵁ Neighborhood.open X Y V := j.le
  have hs''hom' : s'' ≫ ((finiteEtaleBaseChange (i ∣_ Neighborhood.open X Y V)).obj U).hom
      = X'.homOfLE hjle := hs''hom
  have hVle : V ≤ Neighborhood.image hi Y Y' jY hjY hjYt V'' :=
    Neighborhood.le_image hi Y Y' jY hjY hjYt hjle
  have hWle : Neighborhood.open X Y (Neighborhood.image hi Y Y' jY hjY hjYt V'') ≤
    Neighborhood.open X Y V := hVle
  have hsigma : (X'.homOfLE (Neighborhood.preimage_open_image hi Y Y' jY hjY hjYt V'').le ≫
        s'' ≫ finiteEtaleBaseChangeProj (i ∣_ Neighborhood.open X Y V) U) ≫ U.hom
      = (i ∣_ Neighborhood.open X Y (Neighborhood.image hi Y Y' jY hjY hjYt V'')) ≫
        X.homOfLE hWle := by
    rw [morphismRestrict_comp_homOfLE hi Y Y' jY hjY hjYt hWle, Category.assoc,
      Category.assoc, finiteEtaleBaseChangeProj_comp_hom, ← Category.assoc s'', hs''hom',
      ← Category.assoc, Scheme.homOfLE_homOfLE]
  obtain ⟨⟨s, hs⟩, hsval⟩ := (bijective_restrictSection_of_isThickening (X.homOfLE hWle)
    (hi.morphismRestrict (Neighborhood.open X Y (Neighborhood.image hi Y Y' jY hjY hjYt V'')))
    U).2 ⟨_, hsigma⟩
  have hsv : (i ∣_ Neighborhood.open X Y (Neighborhood.image hi Y Y' jY hjY hjYt V'')) ≫ s
      = X'.homOfLE (Neighborhood.preimage_open_image hi Y Y' jY hjY hjYt V'').le ≫
        s'' ≫ finiteEtaleBaseChangeProj (i ∣_ Neighborhood.open X Y V) U :=
    congrArg Subtype.val hsval
  refine ⟨Neighborhood.image hi Y Y' jY hjY hjYt V'', homOfLE hVle, s, hs, ?_⟩
  have hfac : (Neighborhood.toSchemeHom X Y (Neighborhood.image hi Y Y' jY hjY hjYt V'') ≫ s)
      ≫ U.hom = Neighborhood.toSchemeHom X Y V :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => Neighborhood.toSchemeHom X Y
            (Neighborhood.image hi Y Y' jY hjY hjYt V'') ≫ k) hs).trans
        (Neighborhood.toSchemeHom_comp X Y (homOfLE hVle)))
  exact congrArg Subtype.val ((bijective_restrictSection_of_isThickening
    (Neighborhood.toSchemeHom X Y V) hjYt U).1 (a₁ := ⟨_, hfac⟩) (a₂ := ⟨t, ht⟩) (Subtype.ext
      (((reassoc_of% (Neighborhood.subschemeHom_comp_morphismRestrict hi Y Y' jY hjY hjYt
          (Neighborhood.image hi Y Y' jY hjY hjYt V''))) s).symm.trans
        ((congrArg (fun k => Neighborhood.toSchemeHom X' Y' (Neighborhood.preimage hi Y Y'
              jY hjY hjYt (Neighborhood.image hi Y Y' jY hjY hjYt V'')) ≫ k) hsv).trans
          (((reassoc_of% (Neighborhood.toSchemeHom_comp_homOfLE_image hi Y Y' jY hjY hjYt V''))
              (s'' ≫ finiteEtaleBaseChangeProj (i ∣_ Neighborhood.open X Y V) U)).trans
            (((reassoc_of% hs''t)
                (finiteEtaleBaseChangeProj (i ∣_ Neighborhood.open X Y V) U)).trans
              (baseChangeLift_proj U (i ∣_ Neighborhood.open X Y V) hab)))))))

/-- **Two sections over a neighbourhood `V'` of `Y` agreeing over `Y` induce sections over the
inverse image of `V'` that agree over `Y'`.**  The sections over the inverse image are the lifts
into the base change of the cover along the restriction of the thickening. -/
theorem toSchemeHom_preimage_comp_baseChangeLift_eq {V V' : Neighborhood X Y} (e : V ⟶ V')
    {U : FiniteEtaleOver (Neighborhood.open X Y V).toScheme}
    {s₁ s₂ : (Neighborhood.open X Y V').toScheme ⟶ U.left}
    (h₁ : ((i ∣_ Neighborhood.open X Y V') ≫ s₁) ≫ U.hom
      = X'.homOfLE (opens_preimage_mono i e.le) ≫ (i ∣_ Neighborhood.open X Y V))
    (h₂ : ((i ∣_ Neighborhood.open X Y V') ≫ s₂) ≫ U.hom
      = X'.homOfLE (opens_preimage_mono i e.le) ≫ (i ∣_ Neighborhood.open X Y V))
    (hs : Neighborhood.toSchemeHom X Y V' ≫ s₁ = Neighborhood.toSchemeHom X Y V' ≫ s₂) :
    Neighborhood.toSchemeHom X' Y' (Neighborhood.preimage hi Y Y' jY hjY hjYt V') ≫
        baseChangeLift U (i ∣_ Neighborhood.open X Y V) h₁
      = Neighborhood.toSchemeHom X' Y' (Neighborhood.preimage hi Y Y' jY hjY hjYt V') ≫
        baseChangeLift U (i ∣_ Neighborhood.open X Y V) h₂ := by
  have hcommon : ∀ (s : (Neighborhood.open X Y V').toScheme ⟶ U.left)
      (h : ((i ∣_ Neighborhood.open X Y V') ≫ s) ≫ U.hom
        = X'.homOfLE (opens_preimage_mono i e.le) ≫ (i ∣_ Neighborhood.open X Y V)),
      (Neighborhood.toSchemeHom X' Y' (Neighborhood.preimage hi Y Y' jY hjY hjYt V') ≫
          baseChangeLift U (i ∣_ Neighborhood.open X Y V) h) ≫
          finiteEtaleBaseChangeProj (i ∣_ Neighborhood.open X Y V) U
        = jY ≫ Neighborhood.toSchemeHom X Y V' ≫ s := fun s h =>
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => Neighborhood.toSchemeHom X' Y'
            (Neighborhood.preimage hi Y Y' jY hjY hjYt V') ≫ k)
          (baseChangeLift_proj U (i ∣_ Neighborhood.open X Y V) h)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ s) (Neighborhood.subschemeHom_comp_morphismRestrict
              hi Y Y' jY hjY hjYt V')).trans (Category.assoc _ _ _))))
  refine finiteEtaleBaseChangeProj_hom_ext (i ∣_ Neighborhood.open X Y V) U ?_ ?_
  · exact (hcommon s₁ h₁).trans ((congrArg (fun k => jY ≫ k) hs).trans (hcommon s₂ h₂).symm)
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => Neighborhood.toSchemeHom X' Y'
            (Neighborhood.preimage hi Y Y' jY hjY hjYt V') ≫ k)
          (baseChangeLift_hom U (i ∣_ Neighborhood.open X Y V) h₁)).trans
        ((congrArg (fun k => Neighborhood.toSchemeHom X' Y'
              (Neighborhood.preimage hi Y Y' jY hjY hjYt V') ≫ k)
            (baseChangeLift_hom U (i ∣_ Neighborhood.open X Y V) h₂)).symm.trans
          (Category.assoc _ _ _).symm))

/-- **Sections near a closed subscheme agreeing over it agree near it as soon as this holds after
a thickening of the ambient scheme.**  The uniqueness half of
`sectionsExtendNearSubscheme_of_isThickening`. -/
theorem sectionsExtendNearSubscheme_eq_of_isThickening
    (huniq : ∀ (V V' : Neighborhood X' Y') (e : V ⟶ V')
      (U : FiniteEtaleOver (Neighborhood.open X' Y' V).toScheme)
      (s₁ s₂ : (Neighborhood.open X' Y' V').toScheme ⟶ U.left),
      s₁ ≫ U.hom = X'.homOfLE e.le → s₂ ≫ U.hom = X'.homOfLE e.le →
      Neighborhood.toSchemeHom X' Y' V' ≫ s₁ = Neighborhood.toSchemeHom X' Y' V' ≫ s₂ →
      ∃ (V'' : Neighborhood X' Y') (j : V' ⟶ V''),
        X'.homOfLE j.le ≫ s₁ = X'.homOfLE j.le ≫ s₂) :
    ∀ (V V' : Neighborhood X Y) (e : V ⟶ V')
      (U : FiniteEtaleOver (Neighborhood.open X Y V).toScheme)
      (s₁ s₂ : (Neighborhood.open X Y V').toScheme ⟶ U.left),
      s₁ ≫ U.hom = X.homOfLE e.le → s₂ ≫ U.hom = X.homOfLE e.le →
      Neighborhood.toSchemeHom X Y V' ≫ s₁ = Neighborhood.toSchemeHom X Y V' ≫ s₂ →
      ∃ (V'' : Neighborhood X Y) (j : V' ⟶ V''),
        X.homOfLE j.le ≫ s₁ = X.homOfLE j.le ≫ s₂ := by
  intro V V' iVV' U s₁ s₂ hs₁ hs₂ hs
  have hlift : ∀ s : (Neighborhood.open X Y V').toScheme ⟶ U.left,
      s ≫ U.hom = X.homOfLE iVV'.le →
      ((i ∣_ Neighborhood.open X Y V') ≫ s) ≫ U.hom
        = X'.homOfLE (opens_preimage_mono i iVV'.le) ≫ (i ∣_ Neighborhood.open X Y V) :=
    fun s hsU => (Category.assoc _ _ _).trans
      ((congrArg (fun k => (i ∣_ Neighborhood.open X Y V') ≫ k) hsU).trans
        (morphismRestrict_comp_homOfLE hi Y Y' jY hjY hjYt iVV'.le))
  obtain ⟨V'', j, hju⟩ := huniq (Neighborhood.preimage hi Y Y' jY hjY hjYt V)
    (Neighborhood.preimage hi Y Y' jY hjY hjYt V')
    (homOfLE (Neighborhood.preimage_le_preimage hi Y Y' jY hjY hjYt iVV'.le))
    ((finiteEtaleBaseChange (i ∣_ Neighborhood.open X Y V)).obj U)
    (baseChangeLift U (i ∣_ Neighborhood.open X Y V) (hlift s₁ hs₁))
    (baseChangeLift U (i ∣_ Neighborhood.open X Y V) (hlift s₂ hs₂))
    (baseChangeLift_hom U (i ∣_ Neighborhood.open X Y V) (hlift s₁ hs₁))
    (baseChangeLift_hom U (i ∣_ Neighborhood.open X Y V) (hlift s₂ hs₂))
    (toSchemeHom_preimage_comp_baseChangeLift_eq hi Y Y' jY hjY hjYt iVV' _ _ hs)
  have hjle : Neighborhood.open X' Y' V'' ≤ i ⁻¹ᵁ Neighborhood.open X Y V' := j.le
  have hju' : X'.homOfLE hjle ≫
        baseChangeLift U (i ∣_ Neighborhood.open X Y V) (hlift s₁ hs₁)
      = X'.homOfLE hjle ≫
        baseChangeLift U (i ∣_ Neighborhood.open X Y V) (hlift s₂ hs₂) := hju
  have hVle : V' ≤ Neighborhood.image hi Y Y' jY hjY hjYt V'' :=
    Neighborhood.le_image hi Y Y' jY hjY hjYt hjle
  have hWle : Neighborhood.open X Y (Neighborhood.image hi Y Y' jY hjY hjYt V'') ≤
    Neighborhood.open X Y V' := hVle
  have hstar : X'.homOfLE hjle ≫ (i ∣_ Neighborhood.open X Y V') ≫ s₁
      = X'.homOfLE hjle ≫ (i ∣_ Neighborhood.open X Y V') ≫ s₂ :=
    (congrArg (X'.homOfLE hjle ≫ ·) (baseChangeLift_proj U _ (hlift s₁ hs₁)).symm).trans
      (((reassoc_of% hju') (finiteEtaleBaseChangeProj (i ∣_ Neighborhood.open X Y V) U)).trans
        (congrArg (X'.homOfLE hjle ≫ ·) (baseChangeLift_proj U _ (hlift s₂ hs₂))))
  have hmid : ∀ s : (Neighborhood.open X Y V').toScheme ⟶ U.left,
      (i ∣_ Neighborhood.open X Y (Neighborhood.image hi Y Y' jY hjY hjYt V'')) ≫
          X.homOfLE hWle ≫ s
        = X'.homOfLE (Neighborhood.preimage_open_image hi Y Y' jY hjY hjYt V'').le ≫
          X'.homOfLE hjle ≫ (i ∣_ Neighborhood.open X Y V') ≫ s := fun s =>
    (reassoc_of% (morphismRestrict_image_comp_homOfLE hi Y Y' jY hjY hjYt hjle hWle)) s
  have hg : ∀ s : (Neighborhood.open X Y V').toScheme ⟶ U.left, s ≫ U.hom = X.homOfLE iVV'.le →
      (X.homOfLE hWle ≫ s) ≫ U.hom = X.homOfLE hWle ≫ X.homOfLE iVV'.le :=
    fun s hs => (Category.assoc _ _ _).trans (congrArg (fun k => X.homOfLE hWle ≫ k) hs)
  exact ⟨Neighborhood.image hi Y Y' jY hjY hjYt V'', homOfLE hVle,
    congrArg Subtype.val ((bijective_restrictSection_of_isThickening
      (X.homOfLE hWle ≫ X.homOfLE iVV'.le)
      (hi.morphismRestrict (Neighborhood.open X Y (Neighborhood.image hi Y Y' jY hjY hjYt V'')))
      U).1 (a₁ := ⟨_, hg s₁ hs₁⟩) (a₂ := ⟨_, hg s₂ hs₂⟩) (Subtype.ext ((hmid s₁).trans
        ((congrArg (fun k => X'.homOfLE (Neighborhood.preimage_open_image hi Y Y' jY hjY hjYt
          V'').le ≫ k) hstar).trans (hmid s₂).symm))))⟩

/-- **Sections of finite étale covers extend near a closed subscheme as soon as they do after a
thickening of the ambient scheme.**  Let `i : X' ⟶ X` be a thickening and let `jY : Y' ⟶ Y` be a
thickening of closed subschemes over it.  If every section of a finite étale cover of a
neighbourhood of `Y'` over `Y'` extends to a smaller neighbourhood and is determined there after
further shrinking, then the same holds for `Y` in `X`.

Each neighbourhood `V` of `Y` is carried to the neighbourhood `i ⁻¹ V` of `Y'`, over which a
cover `U` of `V` is replaced by its base change; the section over `Y'` is the one induced by the
given section over `Y`.  The neighbourhood of `Y'` the hypothesis produces matches a
neighbourhood of `Y` inside `V`, and the section produced over it extends to that neighbourhood
of `Y` because restriction of sections along the restriction of `i` is bijective.  That the
extension restricts to the given section over `Y`, and the uniqueness assertion, are both checked
after restriction along `jY`, where the same bijectivity applies. -/
theorem sectionsExtendNearSubscheme_of_isThickening
    (h : SectionsExtendNearSubscheme X' Y') : SectionsExtendNearSubscheme X Y :=
  ⟨sectionsExtendNearSubscheme_exists_of_isThickening hi Y Y' jY hjY hjYt h.1,
    sectionsExtendNearSubscheme_eq_of_isThickening hi Y Y' jY hjY hjYt h.2⟩

/-- **Full faithfulness of the restriction functor `colim_V FÉt_V ⟶ FÉt_Y` passes to a thickening
of the ambient scheme.**  The transport of the extension property for sections, composed with the
deduction of full faithfulness from it. -/
theorem finiteEtaleColimitFullyFaithful_of_isThickening
    (h : SectionsExtendNearSubscheme X' Y') : FiniteEtaleColimitFullyFaithful X Y :=
  finiteEtaleColimitFullyFaithful_of_sectionsExtendNearSubscheme X Y
    (sectionsExtendNearSubscheme_of_isThickening hi Y Y' jY hjY hjYt h)

/-- **Full faithfulness of `colim_V FÉt_V ⟶ FÉt_Y` from full faithfulness of completion after a
thickening of the ambient scheme.**  Assume `X'` is Noetherian and the completion functor
`colim_{V'} Coh(𝒪_{V'}) ⟶ Coh(X', I')` is fully faithful on the finite locally free objects, which
is `Stacks.Algebraization.NeighbourhoodCompletion.CompletionFullyFaithfulComplete` at the closed
immersion of `Y'`.  Then the restriction functor `colim_V FÉt_V ⟶ FÉt_Y` of the thickened pair is
fully faithful.

This is the shape in which the hypothesis of [Stacks, Tag 0ELA] is available after replacing a
scheme by a closed subscheme with the same underlying space: the completion hypothesis is checked
on `X'`, where it may hold for reasons that fail on `X`, and the conclusion is read on `X`. -/
theorem finiteEtaleColimitFullyFaithful_of_completionComplete_of_isThickening
    [IsNoetherian X']
    (h : Stacks.Algebraization.NeighbourhoodCompletion.CompletionFullyFaithfulComplete
      Y'.subschemeι) : FiniteEtaleColimitFullyFaithful X Y :=
  finiteEtaleColimitFullyFaithful_of_isThickening hi Y Y' jY hjY hjYt
    (sectionsExtendNearSubscheme_of_completionFullyFaithfulComplete X' Y' h)

end Stacks.FundamentalGroup

end
