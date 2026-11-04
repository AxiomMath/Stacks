module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteSections

/-!
# The inverse image of a representable algebraic space after enlarging the big fppf site

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B`, and write
`i` for the localized inclusion and `f` for the morphism of sites it determines. Stacks 03FP,
part (1) says that the inverse image `f⁻¹h_T` of the sheaf represented by a test object `T` of
the smaller localized site is the sheaf represented by `i T`. This file proves that for the
*canonical* comparison

`h_{i T} ⟶ f⁻¹h_T`,

namely the Yoneda transpose of the transport of `𝟙_T` under the bijection on sections of
Stacks 04W1. The comparison is therefore computable on sections: it sends a morphism
`V ⟶ i T` of the enlarged site to the restriction along it of the transport of `𝟙_T`, and in
particular it sends `i d` to the transport of `d` for every morphism `d` of the smaller site.

That last identity is what a consumer needs and what the comparison produced by Stacks 03FP,
part (1) cannot supply: that comparison is only obtained as *some* isomorphism, so nothing is
known about its values. Invertibility is transferred from it to the canonical comparison instead.

## Main definitions

* `AlgebraicGeometry.changeBigSiteYonedaHom`: the canonical comparison.
* `AlgebraicGeometry.changeBigSiteYonedaIso`: the comparison, as an isomorphism.

## Main results

* `AlgebraicGeometry.changeBigSiteYonedaHom_app` and
  `AlgebraicGeometry.changeBigSiteYonedaHom_app_map`: the values of the comparison.
* `AlgebraicGeometry.bijective_changeBigSiteYonedaHom_app_self`: the comparison is bijective on
  sections over the image of the test object.
* `AlgebraicGeometry.isIso_changeBigSiteYonedaHom`: **Stacks 03FP, part (1)** for the canonical
  comparison.

## References

* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe u

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

/-- **The canonical comparison from the sheaf represented by the image of a test object to the
inverse image of the sheaf it represents.** It is the Yoneda transpose of the transport of the
identity. -/
def changeBigSiteYonedaHom (T : BigFppfOver B S hS) :
    yoneda.obj ((inclusionOver h S hS).obj T) ⟶
      ((changeBigSite B B' h S hS).obj ((schemeSpaceFunctor B S hS).obj T)).obj :=
  yonedaEquiv.symm
    (changeBigSiteSectionEquiv B B' h S hS ((schemeSpaceFunctor B S hS).obj T) T (𝟙 T))

/-- The comparison sends a morphism to the image of the identity restricted along it. -/
theorem changeBigSiteYonedaHom_app (T : BigFppfOver B S hS)
    (V : BigFppfOver B' S (largerContains h hS))
    (ξ : V ⟶ (inclusionOver h S hS).obj T) :
    (changeBigSiteYonedaHom B B' h S hS T).app (op V) ξ =
      ((changeBigSite B B' h S hS).obj ((schemeSpaceFunctor B S hS).obj T)).obj.map ξ.op
        (changeBigSiteSectionEquiv B B' h S hS ((schemeSpaceFunctor B S hS).obj T) T (𝟙 T)) :=
  yonedaEquiv_symm_app_apply _ _ _

/-- The comparison sends a morphism to the image of the identity restricted along it. -/
theorem changeBigSiteYonedaHom_app_map (T W : BigFppfOver B S hS) (d : W ⟶ T) :
    (changeBigSiteYonedaHom B B' h S hS T).app
        (op ((inclusionOver h S hS).obj W)) ((inclusionOver h S hS).map d) =
      changeBigSiteSectionEquiv B B' h S hS ((schemeSpaceFunctor B S hS).obj T) W d := by
  have h1 := changeBigSiteYonedaHom_app B B' h S hS T
    ((inclusionOver h S hS).obj W) ((inclusionOver h S hS).map d)
  have h2 := changeBigSiteSectionEquiv_restrict B B' h S hS
    ((schemeSpaceFunctor B S hS).obj T) d (𝟙 T)
  have h3 : ((schemeSpaceFunctor B S hS).obj T).obj.map d.op (𝟙 T) = d := Category.comp_id d
  rw [h3] at h2
  rw [h1]
  exact h2.symm

/-- **The comparison is bijective on sections over the image of the test object itself.** The
localized inclusion is fully faithful, so every such section of the represented sheaf is the
image of a morphism of the smaller site, and the transport of sections is a bijection. -/
theorem bijective_changeBigSiteYonedaHom_app_self (T : BigFppfOver B S hS) :
    Function.Bijective
      (fun ξ : ((yoneda.obj ((inclusionOver h S hS).obj T)).obj
          (op ((inclusionOver h S hS).obj T))) =>
        (changeBigSiteYonedaHom B B' h S hS T).app
          (op ((inclusionOver h S hS).obj T)) ξ) := by
  have : (inclusionOver h S hS).Full := inclusionOver_full h S hS
  have key := changeBigSiteYonedaHom_app_map B B' h S hS T T
  constructor
  · intro ξ₁ ξ₂ hξ
    obtain ⟨d₁, rfl⟩ := (inclusionOver h S hS).map_surjective ξ₁
    obtain ⟨d₂, rfl⟩ := (inclusionOver h S hS).map_surjective ξ₂
    dsimp only at hξ
    rw [key d₁, key d₂] at hξ
    exact congrArg (inclusionOver h S hS).map
      ((changeBigSiteSectionEquiv B B' h S hS ((schemeSpaceFunctor B S hS).obj T) T).injective hξ)
  · intro σ
    refine ⟨(inclusionOver h S hS).map
      ((changeBigSiteSectionEquiv B B' h S hS ((schemeSpaceFunctor B S hS).obj T) T).symm σ), ?_⟩
    exact (key _).trans ((changeBigSiteSectionEquiv B B' h S hS
      ((schemeSpaceFunctor B S hS).obj T) T).apply_symm_apply σ)

/-- The comparison of Stacks 03FP, part (1), as it is produced there: *some* isomorphism between
the inverse image of a representable sheaf and the sheaf represented by the image of the test
object, carrying no information about its action on sections. -/
private def chosenYonedaIso (T : BigFppfOver B S hS) :
    (changeBigSite B B' h S hS).obj ((schemeSpaceFunctor B S hS).obj T) ≅
      ((schemeSpaceFunctor B' S (largerContains h hS)).obj ((inclusionOver h S hS).obj T)) := by
  letI J := overTopology .fppf B S hS
  letI K := overTopology .fppf B' S (largerContains h hS)
  letI i := inclusionOver h S hS
  letI : i.IsContinuous J K :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  letI : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
    inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
  letI : HasSheafify J (Type u) := hasSheafify_overTopology B S hS
  letI : HasSheafify K (Type u) := hasSheafify_overTopology B' S (largerContains h hS)
  letI : J.Subcanonical := subcanonical_overTopology B S hS
  letI : K.Subcanonical := subcanonical_overTopology B' S (largerContains h hS)
  exact ObjectProperty.isoMk _
    ((sheafToPresheaf K (Type u)).mapIso ((pullbackYonedaIso i J K).app T))

/-- **Stacks 03FP, part (1), for the canonical comparison.** The inverse image of the sheaf
represented by a test object of the smaller localized big fppf site is the sheaf represented by
its image, by the comparison determined by the transport of the identity.

The isomorphism of Stacks 03FP, part (1) is only produced as *some* isomorphism, so it cannot be
evaluated on sections. The argument transfers invertibility to the canonical comparison: the two
differ by precomposition with a morphism of the enlarged site, because a map out of a
representable sheaf is its own Yoneda transpose; that morphism is invertible because the canonical
comparison is bijective on sections over the image of the test object, where the chosen
isomorphism is bijective as well; and precomposition with an invertible morphism preserves
invertibility. -/
@[stacks 03FP "part (1), canonically"]
theorem isIso_changeBigSiteYonedaHom (T : BigFppfOver B S hS) :
    IsIso (changeBigSiteYonedaHom B B' h S hS T) := by
  have hb := bijective_changeBigSiteYonedaHom_app_self B B' h S hS T
  let θp : ((changeBigSite B B' h S hS).obj ((schemeSpaceFunctor B S hS).obj T)).obj ≅
      yoneda.obj ((inclusionOver h S hS).obj T) :=
    (ObjectProperty.ι _).mapIso (chosenYonedaIso B B' h S hS T)
  let c : (inclusionOver h S hS).obj T ⟶ (inclusionOver h S hS).obj T :=
    yonedaEquiv (changeBigSiteYonedaHom B B' h S hS T ≫ θp.hom)
  have hc : changeBigSiteYonedaHom B B' h S hS T ≫ θp.hom = yoneda.map c :=
    yonedaEquiv.injective (yonedaEquiv_yoneda_map c).symm
  have h1 : Function.Bijective
      (fun ξ : (inclusionOver h S hS).obj T ⟶ (inclusionOver h S hS).obj T =>
        (changeBigSiteYonedaHom B B' h S hS T ≫ θp.hom).app
          (op ((inclusionOver h S hS).obj T)) ξ) :=
    (ConcreteCategory.bijective_of_isIso
      ((θp.hom).app (op ((inclusionOver h S hS).obj T)))).comp hb
  rw [hc] at h1
  obtain ⟨e, he0⟩ := h1.surjective (𝟙 _)
  have he : e ≫ c = 𝟙 _ := he0
  have hce : c ≫ e = 𝟙 _ := h1.injective (show (c ≫ e) ≫ c = 𝟙 _ ≫ c by
    rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have hiso : IsIso (changeBigSiteYonedaHom B B' h S hS T ≫ θp.hom) := by
    rw [hc]
    refine ⟨yoneda.map e, ?_, ?_⟩
    · exact (yoneda.map_comp c e).symm.trans
        ((congrArg yoneda.map hce).trans (yoneda.map_id _))
    · exact (yoneda.map_comp e c).symm.trans
        ((congrArg yoneda.map he).trans (yoneda.map_id _))
  exact @IsIso.of_isIso_comp_right _ _ _ _ _
    (changeBigSiteYonedaHom B B' h S hS T) θp.hom ⟨θp.inv, θp.hom_inv_id, θp.inv_hom_id⟩ hiso

/-- **The inverse image of a representable algebraic space is represented by the image of the
test object**, by the canonical comparison of
`AlgebraicGeometry.changeBigSiteYonedaHom`. -/
@[stacks 03FP "part (1), canonically"]
def changeBigSiteYonedaIso (T : BigFppfOver B S hS) :
    yoneda.obj ((inclusionOver h S hS).obj T) ≅
      ((changeBigSite B B' h S hS).obj ((schemeSpaceFunctor B S hS).obj T)).obj :=
  haveI := isIso_changeBigSiteYonedaHom B B' h S hS T
  asIso (changeBigSiteYonedaHom B B' h S hS T)

/-- The isomorphism is the canonical comparison. -/
@[simp]
theorem changeBigSiteYonedaIso_hom (T : BigFppfOver B S hS) :
    (changeBigSiteYonedaIso B B' h S hS T).hom = changeBigSiteYonedaHom B B' h S hS T := rfl

end AlgebraicGeometry

end
