module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import StacksFrontier.CategoryTheory.Sites.Topos.LocalizationOfTopoi
public import StacksFrontier.CategoryTheory.Sites.ToposLocalization
import StacksCore.Tactic.EgaSgaAttribute

/-! # The localization of `Sh(C)` at a sheaf `F` (Stacks 04GZ)

For a sheaf `F` on a small site `(C, J)` this file proves that `Sh(C)/F` is a topos and constructs
the localization morphism of topoi `j_F : Sh(C)/F ⟶ Sh(C)`, with its pushforward `j_{F,*}` built
rather than assumed. See `StacksFrontier.CategoryTheory.Sites.ToposLocalization` for the overview and
the general `MorphismOfTopoi.overLocalization`.

`Sh(C)/F ≌ Sh(C/F)` is Stacks 0791 (`Stacks.Topos.Localized.sheafEquivalence`), the site `C/F`
having the pairs `(U, s)`, `s ∈ F(U)`, as objects and the coverings of `C`. The projection
`j : C/F ⥤ C` is continuous and cocontinuous, so restriction along it has the right adjoint `j^s`
(`Functor.sheafAdjunctionCocontinuous`); restriction along `j`, read in `Sh(C)/F`, is `toOver F`,
since both are right adjoint to `Over.forget F`. Hence `j_{F,*}` is the equivalence followed by
`j^s`.

The site is small, as Stacks requires of sites (Remark 00VI); this is what makes the right Kan
extensions defining `j^s` exist in `Type u`.

## Main results

* `CategoryTheory.Sheaf.exists_over_equiv_sheaf`: `Sh(C)/F` is a topos.
* `MorphismOfTopoi.sheafOverLocalization`: the morphism of topoi `j_F`.
* `MorphismOfTopoi.sheafOverLocalization_inverseImage_obj`: `j_F⁻¹` is `H ↦ (H × F ⟶ F)`.
* `MorphismOfTopoi.sheafOverLocalizationShriek`: `j_{F!}` is the forgetful functor.
* `MorphismOfTopoi.sheafOverLocalization_isLocalization`: `j_{F!} ⊣ j_F⁻¹ ⊣ j_{F,*}`.

Tags covered: 04GZ.
-/

@[expose] public section

namespace MorphismOfTopoi

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Stacks.Topos.Localized
universe u

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- **Stacks 04GZ, the topos `Sh(C)/F`.** For a sheaf `F` on a site `(C, J)`, the slice
`Sh(C)/F` is equivalent to the category of sheaves on the site `C/F` of pairs `(U, s)` with
`s ∈ F(U)`, whose coverings are those of `C` (Stacks 0791). This is the inverse of
`Stacks.Topos.Localized.sheafEquivalence`, which sends `(U, s) ↦ {t ∈ G(U) | φ(t) = s}` for an
object `φ : G ⟶ F` of `Sh(C)/F`. -/
noncomputable def sheafOverEquivalence (F : Sheaf J (Type u)) :
    Over F ≌ Sheaf ((CostructuredArrow.proj yoneda F.obj).restrictedTopology J) (Type u) :=
  (sheafEquivalence F.obj J F.property).symm

/-- **Stacks 04GZ: `Sh(C)/F` is a topos.** For a sheaf `F` on a site `(C, J)`, the slice
`Sh(C)/F` is equivalent to the category of sheaves of sets on a site, namely the site `C/F` of
`sheafOverEquivalence`. -/
@[stacks 04GZ "the category Sh(C)/F is a topos: it is equivalent to Sh(C/F), sheaves on the site
  of pairs (U, s) with s ∈ F(U)"]
theorem _root_.CategoryTheory.Sheaf.exists_over_equiv_sheaf (F : Sheaf J (Type u)) :
    ∃ (D : Type u) (_ : SmallCategory D) (K : GrothendieckTopology D),
      Nonempty (Over F ≌ Sheaf K (Type u)) :=
  ⟨_, inferInstance, _, ⟨sheafOverEquivalence J F⟩⟩

/-- The inverse image `j_F⁻¹ = toOver F` is the restriction along `j : C/F ⥤ C`, read in `Sh(C)/F`
along `sheafOverEquivalence`: both are right adjoint to `Over.forget F`. -/
noncomputable def toOverIsoRestriction (F : Sheaf J (Type u)) :
    toOver F ≅ restrictionFunctor F.obj J ⋙ (sheafOverEquivalence J F).inverse :=
  (forgetAdjToOver F).rightAdjointUniq (forgetAdjunction F.obj J F.property)

/-- The pushforward `j_{F,*} : Sh(C)/F ⥤ Sh(C)` of the localization morphism at a sheaf `F`: the
equivalence `Sh(C)/F ≌ Sh(C/F)` followed by the pushforward `j^s` along the cocontinuous
functor `j : C/F ⥤ C`, i.e. the right Kan extension along `j`. -/
noncomputable def overLocalizationPushforward (F : Sheaf J (Type u)) :
    Over F ⥤ Sheaf J (Type u) :=
  (sheafOverEquivalence J F).functor ⋙
    (CostructuredArrow.proj yoneda F.obj).sheafPushforwardCocontinuous (Type u)
      ((CostructuredArrow.proj yoneda F.obj).restrictedTopology J) J

/-- `j_F⁻¹ = toOver F` is left adjoint to `j_{F,*}`. -/
noncomputable def toOverAdjOverLocalizationPushforward (F : Sheaf J (Type u)) :
    toOver F ⊣ overLocalizationPushforward J F :=
  (((CostructuredArrow.proj yoneda F.obj).sheafAdjunctionCocontinuous (Type u)
      ((CostructuredArrow.proj yoneda F.obj).restrictedTopology J) J).comp
    (sheafOverEquivalence J F).symm.toAdjunction).ofNatIsoLeft (toOverIsoRestriction J F).symm

/-- **Stacks 04GZ.** Let `(C, J)` be a site and `F` a sheaf on it. The localization morphism
`j_F : Sh(C)/F ⟶ Sh(C)` is the morphism of topoi with inverse image `j_F⁻¹ = toOver F`, i.e.
`H ↦ (H × F ⟶ F)`, and pushforward `j_{F,*} = overLocalizationPushforward J F`, its right
adjoint. -/
@[stacks 04GZ "the canonical morphism of topoi j_F : Sh(C)/F → Sh(C), with j_F^{-1} = toOver F
  and j_{F,*} its right adjoint, constructed through Sh(C)/F ≌ Sh(C/F)"]
noncomputable def sheafOverLocalization (F : Sheaf J (Type u)) :
    MorphismOfTopoi (Over F) (Sheaf J (Type u)) :=
  overLocalization F (toOverAdjOverLocalizationPushforward J F)

/-- **Stacks 04GZ (1).** The inverse image of `j_F : Sh(C)/F ⟶ Sh(C)` is
`H ↦ (H × F ⟶ F)`. -/
@[stacks 04GZ "(1): the functor j_F^{-1} is H ↦ H × F / F"]
lemma sheafOverLocalization_inverseImage_obj (F H : Sheaf J (Type u)) :
    (sheafOverLocalization J F).inverseImage.obj H = Over.mk (snd H F) :=
  rfl

/-- **Stacks 04GZ (2).** The functor `j_{F!}` of `j_F : Sh(C)/F ⟶ Sh(C)` is the forgetful functor
`(G ⟶ F) ↦ G`: it is left adjoint to `j_F⁻¹`. -/
@[stacks 04GZ "(2): the functor j_{F!} is the forgetful functor G/F ↦ G"]
noncomputable def sheafOverLocalizationShriek (F : Sheaf J (Type u)) :
    Over.forget F ⊣ (sheafOverLocalization J F).inverseImage :=
  forgetAdjToOver F

/-- **Stacks 04GZ: `j_F` is a localization.** The triple of adjoints
`j_{F!} ⊣ j_F⁻¹ ⊣ j_{F,*}` of `j_F : Sh(C)/F ⟶ Sh(C)`, with `j_{F!} = Over.forget F` and
`j_F⁻¹ = toOver F`, as in Section 7.25 (tag 00XZ). -/
@[stacks 04GZ "j_F is a localization: the triple of adjoints j_{F!} ⊣ j_F^{-1} ⊣ j_{F,*}, with
  j_{F!} the forgetful functor and j_F^{-1} = H ↦ H × F / F"]
theorem sheafOverLocalization_isLocalization (F : Sheaf J (Type u)) :
    Nonempty (Over.forget F ⊣ (sheafOverLocalization J F).inverseImage) ∧
      Nonempty ((sheafOverLocalization J F).inverseImage ⊣
        (sheafOverLocalization J F).pushforward) ∧
      (sheafOverLocalization J F).inverseImage = toOver F :=
  ⟨⟨sheafOverLocalizationShriek J F⟩, ⟨(sheafOverLocalization J F).adj⟩, rfl⟩

end MorphismOfTopoi
