module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteUnconditional

/-!
# Sections of an algebraic space after enlarging the big fppf site

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B`, and write
`i` for the localized inclusion and `f` for the morphism of sites it determines. The inverse
image `f⁻¹` on sheaves of sets is fully faithful, so the unit of the adjunction is an
isomorphism: an algebraic space `X` over `S` for `B` is recovered from `f⁻¹X` by restricting
along `i`.

Evaluated at a test object `T` of the smaller localized site this says that the `T`-points of
`X` are exactly the `i T`-points of `f⁻¹X`. That bijection is the dictionary through which a
groupoid in algebraic spaces and its inverse image have the same groupoids of points.

## Main definitions

* `AlgebraicGeometry.changeBigSiteSheafUnitIso`: the unit of the inverse-image adjunction on
  sheaves of sets, as an isomorphism.
* `AlgebraicGeometry.changeBigSitePresheafIso`: the resulting isomorphism `X ≅ i^op ⋙ f⁻¹X` of
  presheaves on the smaller localized site.
* `AlgebraicGeometry.changeBigSiteSectionEquiv`: the induced bijection `X(T) ≃ (f⁻¹X)(i T)`.

## Main results

* `AlgebraicGeometry.changeBigSiteSectionEquiv_restrict`: the bijection commutes with
  restriction along a morphism of test objects of the smaller site.
* `AlgebraicGeometry.changeBigSiteSectionEquiv_map`: the bijection commutes with the map on
  sections induced by a morphism of algebraic spaces over `S`.

## References

* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU)
* [Stacks Project, Tag 022K](https://stacks.math.columbia.edu/tag/022K)
* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry

universe u

/-- Two equal morphisms of sheaves of sets have the same component at every test object. -/
private theorem sheafHom_congr_app {𝒞 : Type (u + 1)} [Category.{u} 𝒞]
    {J : GrothendieckTopology 𝒞} {F G : Sheaf J (Type u)} {a b : F ⟶ G} (hab : a = b)
    (T : 𝒞ᵒᵖ) : a.hom.app T = b.hom.app T := by rw [hab]

/-- Two equal maps of sets agree at every element. -/
private theorem congr_hom_apply {A C : Type u} {a b : A ⟶ C} (hab : a = b) (x : A) :
    ConcreteCategory.hom a x = ConcreteCategory.hom b x := by rw [hab]

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

/-- **The unit of the inverse-image adjunction is an isomorphism.** Restricting the inverse
image of a sheaf of sets on the smaller localized big fppf site back along the inclusion
recovers the sheaf, because the inverse image is fully faithful. -/
def changeBigSiteSheafUnitIso :
    letI J := overTopology .fppf B S hS
    letI K := overTopology .fppf B' S (largerContains h hS)
    letI i := inclusionOver h S hS
    letI : i.IsContinuous J K :=
      (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
    letI : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
      inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
    (𝟭 (Sheaf J (Type u))) ≅
      (i.sheafPullback (Type u) J K) ⋙ (i.sheafPushforwardContinuous (Type u) J K) := by
  letI J := overTopology .fppf B S hS
  letI K := overTopology .fppf B' S (largerContains h hS)
  letI i := inclusionOver h S hS
  letI : i.IsContinuous J K :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  letI : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
    inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
  obtain ⟨hfull, hfaith⟩ := inclusionOver_full_and_faithful_sheafPullback B B' h S hS
  letI : (i.sheafPullback (Type u) J K).Full := hfull
  letI : (i.sheafPullback (Type u) J K).Faithful := hfaith
  exact asIso (i.sheafAdjunctionContinuous (Type u) J K).unit

/-- An algebraic space over `S` for the smaller big fppf site is the restriction along the
localized inclusion of its inverse image. -/
def changeBigSitePresheafIso (X : AlgebraicSpaces B S hS) :
    X.obj ≅ (inclusionOver h S hS).op ⋙ ((changeBigSite B B' h S hS).obj X).obj :=
  (sheafToPresheaf (overTopology .fppf B S hS) (Type u)).mapIso
    ((changeBigSiteSheafUnitIso B B' h S hS).app ⟨X.obj, X.property.isSheaf⟩)

/-- **The `T`-points of an algebraic space are the `i T`-points of its inverse image.** -/
def changeBigSiteSectionEquiv (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS) :
    X.obj.obj (op T) ≃
      ((changeBigSite B B' h S hS).obj X).obj.obj (op ((inclusionOver h S hS).obj T)) :=
  ((changeBigSitePresheafIso B B' h S hS X).app (op T)).toEquiv

/-- The bijection on sections is evaluation of the comparison isomorphism of presheaves. -/
@[simp]
theorem changeBigSiteSectionEquiv_apply (X : AlgebraicSpaces B S hS)
    (T : BigFppfOver B S hS) (x : X.obj.obj (op T)) :
    changeBigSiteSectionEquiv B B' h S hS X T x =
      (changeBigSitePresheafIso B B' h S hS X).hom.app (op T) x := rfl

/-- The comparison isomorphism is natural in the algebraic space. -/
theorem changeBigSitePresheafIso_naturality {X Y : AlgebraicSpaces B S hS} (φ : X ⟶ Y)
    (T : BigFppfOver B S hS) :
    φ.hom.app (op T) ≫ (changeBigSitePresheafIso B B' h S hS Y).hom.app (op T) =
      (changeBigSitePresheafIso B B' h S hS X).hom.app (op T) ≫
        ((changeBigSite B B' h S hS).map φ).hom.app
          (op ((inclusionOver h S hS).obj T)) :=
  sheafHom_congr_app ((changeBigSiteSheafUnitIso B B' h S hS).hom.naturality
    (X := (⟨X.obj, X.property.isSheaf⟩ : Sheaf (overTopology .fppf B S hS) (Type u)))
    (Y := (⟨Y.obj, Y.property.isSheaf⟩ : Sheaf (overTopology .fppf B S hS) (Type u)))
    ⟨φ.hom⟩) (op T)

/-- **Transport of sections commutes with a morphism of algebraic spaces.** -/
theorem changeBigSiteSectionEquiv_map {X Y : AlgebraicSpaces B S hS} (φ : X ⟶ Y)
    (T : BigFppfOver B S hS) (x : X.obj.obj (op T)) :
    changeBigSiteSectionEquiv B B' h S hS Y T (φ.hom.app (op T) x) =
      ((changeBigSite B B' h S hS).map φ).hom.app (op ((inclusionOver h S hS).obj T))
        (changeBigSiteSectionEquiv B B' h S hS X T x) :=
  congr_hom_apply (changeBigSitePresheafIso_naturality B B' h S hS φ T) x

/-- **Transport of sections commutes with restriction along a morphism of test objects.** -/
theorem changeBigSiteSectionEquiv_restrict (X : AlgebraicSpaces B S hS)
    {T₁ T₂ : BigFppfOver B S hS} (g : T₁ ⟶ T₂) (x : X.obj.obj (op T₂)) :
    changeBigSiteSectionEquiv B B' h S hS X T₁ (X.obj.map g.op x) =
      ((changeBigSite B B' h S hS).obj X).obj.map ((inclusionOver h S hS).map g).op
        (changeBigSiteSectionEquiv B B' h S hS X T₂ x) :=
  NatTrans.naturality_apply (changeBigSitePresheafIso B B' h S hS X).hom g.op x

end AlgebraicGeometry

end
