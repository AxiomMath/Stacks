module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalkAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleBaseChangeMate
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperBaseChangeRepresentable

/-!
# The stalk of a spaces-étale sheaf at a geometric point as global sections

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let `x` be
a geometric point of `X`, the spectrum `Spec Ω` of an algebraically closed field lying in `B`
together with a section of `X` over it. The field spectrum represents an algebraic space, and the
section is a morphism `x̄ : Spec Ω ⟶ X` of algebraic spaces. This file proves that the stalk at `x`
of a sheaf `G` on the spaces-étale site of `X` is the set (or group, or object of any coefficient
category with the relevant colimits) of global sections of `x̄⁻¹ G`:

`G_x ≅ Γ(Spec Ω, x̄⁻¹ G)`,

naturally in `G`. Here the stalk at a geometric point is the fibre functor of
`AlgebraicGeometry.Space.spacesEtaleSitePoint`, which computes the colimit over all étale
neighbourhoods of Stacks 04JV (`AlgebraicGeometry.Space.spacesEtaleSitePointStalkIso`).

Then, for a morphism `f : Y ⟶ X`, it defines the canonical comparison
`(f_* F)_x ⟶ Γ(Y_x, F|_{Y_x})` of Stacks 0DG1 (the spaces version of Stacks 0A3T) and proves that
it is an isomorphism as soon as the base-change map of Stacks 0DG0 of the cartesian square of the
geometric fibre `Y_x = Y ×_X Spec Ω` is one, hence, for `f` proper, granted Stacks 0A3U (which
gives Stacks 0DG0 there).

## Main definitions

* `AlgebraicGeometry.Space.geometricPointSpace`, `AlgebraicGeometry.Space.geometricPointHom`: the
  algebraic space represented by the field spectrum of a geometric point, and the geometric point
  as a morphism of algebraic spaces.
* `AlgebraicGeometry.Space.geometricPointSpaceBase`: the canonical geometric point of that space;
  its image under `geometricPointHom` is the original point
  (`AlgebraicGeometry.Space.geometricPointMap_geometricPointSpaceBase`).
* `AlgebraicGeometry.Space.spacesEtaleSheafFiberInverseImageIso`: **Stacks 04K2, part (4), on the
  spaces-étale sites**, for an arbitrary morphism and arbitrary coefficients: the stalk at `x` of
  the inverse image along `f` is the stalk at `f ∘ x`.
* `AlgebraicGeometry.Space.spacesEtaleBaseSheafFiberIsoGamma`: the stalk at the canonical point of
  the field spectrum is global sections.
* `AlgebraicGeometry.Space.spacesEtaleSheafFiberIsoInverseImageGamma`: `G_x ≅ Γ(Spec Ω, x̄⁻¹ G)`.
* `AlgebraicGeometry.Space.spacesPushforwardGammaIso`: global sections of a direct image along base
  change are global sections upstairs.
* `AlgebraicGeometry.Space.spacesProperGeometricFibreComparison`: the comparison of Stacks 0DG1.

## Main results

* `AlgebraicGeometry.Space.isIso_spacesProperGeometricFibreComparison_of_isIso`: the comparison of
  Stacks 0DG1 is invertible when the base-change map of the geometric fibre square is.
* `AlgebraicGeometry.Space.bijective_spacesProperGeometricFibreComparison_app_of_isIso`: Stacks
  0DG1, granted Stacks 0A3U.

## References

* [Stacks Project, Tag 0DG1](https://stacks.math.columbia.edu/tag/0DG1)
* [Stacks Project, Tag 0DG0](https://stacks.math.columbia.edu/tag/0DG0)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

-- The slice-category smallness instances `CategoryTheory.small_over` and
-- `CategoryTheory.locallySmall_over` send the searches for the sheaf pullback's left Kan
-- extensions here into a typeclass timeout, so they are switched off in this file.
attribute [-instance] CategoryTheory.small_over CategoryTheory.locallySmall_over

universe u v w

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The field spectrum of a geometric point as an algebraic space -/

section PointSpace

variable {X : AlgebraicSpaces B S hS} (x : GeometricPoint B S hS X.1)

/-- The algebraic space represented by the field spectrum of a geometric point. -/
def geometricPointSpace : AlgebraicSpaces B S hS :=
  schemeSpace x.val.siteObject

/-- A geometric point of `X`, as the morphism of algebraic spaces from its field spectrum. -/
def geometricPointHom : geometricPointSpace x ⟶ X :=
  ObjectProperty.homMk (yonedaEquiv.symm x.val.value)

/-- The canonical geometric point of the field spectrum of a geometric point: the same field, with
the identity as its section. -/
def geometricPointSpaceBase : GeometricPoint B S hS (geometricPointSpace x).1 :=
  ⟨{ carrier := x.val.carrier
     contained := x.val.contained
     toBase := x.val.toBase
     value := 𝟙 x.val.siteObject }, x.property⟩

/-- The image of the canonical geometric point of the field spectrum is the geometric point. -/
theorem geometricPointMap_geometricPointSpaceBase :
    geometricPointMap (geometricPointHom x).hom (geometricPointSpaceBase x) = x := by
  obtain ⟨⟨k, hk, t, v⟩, h⟩ := x
  exact Subtype.ext <|
    congrArg (FieldValuedPoint.mk (F := X.1) k hk t) (yonedaEquiv.apply_symm_apply v)

/-- The identity lift of the canonical geometric point to the final object of the spaces-étale
site of the field spectrum. -/
def spacesGeometricFiberBaseElement :
    (spacesGeometricFiber (geometricPointSpaceBase x)).obj
      (SpacesEtale.idObj B S hS (geometricPointSpace x)) :=
  ⟨𝟙 x.val.siteObject, rfl⟩

/-- The morphism from the final object of the spaces-étale site of the field spectrum to an
étale neighbourhood of the canonical point, given by its chosen lift. -/
def spacesGeometricFiberBaseHom
    (V : (spacesGeometricFiber (geometricPointSpaceBase x)).Elements) :
    SpacesEtale.idObj B S hS (geometricPointSpace x) ⟶ V.1 :=
  ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk (yonedaEquiv.symm V.2.1)) (by
    apply ObjectProperty.hom_ext
    apply yonedaEquiv.injective
    change yonedaEquiv (yonedaEquiv.symm V.2.1 ≫
        ((SpacesEtale.inclusion B S hS _).obj V.1).hom.hom) = yonedaEquiv (𝟙 _)
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact V.2.2))

/-- **The identity lift is an initial étale neighbourhood of the canonical point of a field
spectrum.** -/
def isInitialSpacesGeometricFiberBaseElement :
    IsInitial ((spacesGeometricFiber (geometricPointSpaceBase x)).elementsMk
      (SpacesEtale.idObj B S hS (geometricPointSpace x)) (spacesGeometricFiberBaseElement x)) :=
  IsInitial.ofUniqueHom
    (fun V => ⟨spacesGeometricFiberBaseHom x V, Subtype.ext (yonedaEquiv.apply_symm_apply _)⟩)
    (fun V m => by
      refine CategoryOfElements.ext _ _ _ ?_
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      apply yonedaEquiv.injective
      change m.1.hom.left.hom.app _ (𝟙 _) = yonedaEquiv (yonedaEquiv.symm V.2.1)
      rw [Equiv.apply_symm_apply]
      exact congrArg Subtype.val m.2)

variable (A : Type v) [Category.{w} A] [HasColimitsOfSize.{u, u} A]

/-- **The fibre at the canonical point of a field spectrum is evaluation at the final object**,
for presheaves on the spaces-étale site of the field spectrum with values in any category with
the colimits computing it. -/
def spacesEtaleBasePresheafFiberIsoSections :
    (evaluation (SpacesEtale B S hS (geometricPointSpace x))ᵒᵖ A).obj
        (op (SpacesEtale.idObj B S hS (geometricPointSpace x))) ≅
      (spacesEtaleSitePoint (geometricPointSpaceBase x)).presheafFiber := by
  let Φ := spacesEtaleSitePoint (geometricPointSpaceBase x)
  let τ := Φ.toPresheafFiberNatTrans (A := A) (SpacesEtale.idObj B S hS (geometricPointSpace x))
    (spacesGeometricFiberBaseElement x)
  letI : ∀ P, IsIso (τ.app P) := fun P ↦
    (Φ.isColimitPresheafFiberCocone P).isIso_ι_app_of_isTerminal
      (op ((spacesGeometricFiber (geometricPointSpaceBase x)).elementsMk
        (SpacesEtale.idObj B S hS (geometricPointSpace x)) (spacesGeometricFiberBaseElement x)))
      (isInitialSpacesGeometricFiberBaseElement x).op
  letI := NatIso.isIso_of_isIso_app τ
  exact asIso τ

variable [HasWeakSheafify (SpacesEtale.topology B S hS (geometricPointSpace x)) A]

/-- **The stalk at the canonical point of a field spectrum is global sections.** -/
def spacesEtaleBaseSheafFiberIsoGamma :
    (spacesEtaleSitePoint (geometricPointSpaceBase x)).sheafFiber (A := A) ≅
      Sheaf.Γ (SpacesEtale.topology B S hS (geometricPointSpace x)) A :=
  (Functor.isoWhiskerLeft
      (sheafToPresheaf (SpacesEtale.topology B S hS (geometricPointSpace x)) A)
      (spacesEtaleBasePresheafFiberIsoSections x A)).symm ≪≫
    (Sheaf.ΓNatIsoSheafSections (SpacesEtale.topology B S hS (geometricPointSpace x)) A
      (SpacesEtale.isTerminal_idObj B S hS (geometricPointSpace x))).symm

end PointSpace

/-! ### Stalks of inverse images on the spaces-étale sites -/

section InverseImage

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (x : GeometricPoint B S hS X.1)
  (A : Type v) [Category.{w} A] [HasProducts.{u} A] [HasColimitsOfSize.{u, u} A]
  [((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous A
    (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).IsRightAdjoint]

/-- **Stacks 04K2, part (4), on the spaces-étale sites.** For a morphism `f : X ⟶ Y` of algebraic
spaces and a geometric point `x` of `X`, the stalk at `x` of the inverse image along `f` of a
sheaf on the spaces-étale site of `Y` is the stalk of that sheaf at the image geometric point,
naturally in the sheaf and for any coefficients. -/
def spacesEtaleSheafFiberInverseImageIso :
    (spacesBaseChange B S hS f).functor.sheafPullback A
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
        (spacesEtaleSitePoint x).sheafFiber ≅
      (spacesEtaleSitePoint (geometricPointMap f.hom x)).sheafFiber :=
  let g := (spacesBaseChange B S hS f).functor
  let Px := spacesEtaleSitePoint x
  let hcover : CoverPreserving (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) g :=
    CoverPreserving.of_isContinuous g _ _
  let efib : g ⋙ Px.fiber ≅ (spacesEtaleSitePoint (geometricPointMap f.hom x)).fiber :=
    spacesBaseChangeFiberIso B S hS f x
  haveI : InitiallySmall.{u} (g ⋙ Px.fiber).Elements :=
    initiallySmall_of_initial_of_initiallySmall
      (CategoryOfElements.equivalenceOfNatIso efib).inverse
  haveI : HasColimitsOfShape (g ⋙ Px.fiber).Elementsᵒᵖ A :=
    inferInstanceAs (HasColimitsOfShape (Px.comap g hcover).fiber.Elementsᵒᵖ A)
  (Px.sheafFiberComapIso g hcover A).symm ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf (SpacesEtale.topology B S hS Y) A)
      (CategoryOfElements.presheafColimIsoOfNatIsoOfCoefficients efib)

end InverseImage

section GeometricPoint

variable {X : AlgebraicSpaces B S hS} (x : GeometricPoint B S hS X.1)
  (A : Type v) [Category.{w} A] [HasProducts.{u} A] [HasColimitsOfSize.{u, u} A]
  [((spacesBaseChange B S hS (geometricPointHom x)).functor.sheafPushforwardContinuous A
    (SpacesEtale.topology B S hS X)
    (SpacesEtale.topology B S hS (geometricPointSpace x))).IsRightAdjoint]
  [HasWeakSheafify (SpacesEtale.topology B S hS (geometricPointSpace x)) A]

/-- **The stalk of a spaces-étale sheaf at a geometric point `x̄` is the object of global sections
of its inverse image along `x̄`**, naturally in the sheaf. -/
def spacesEtaleSheafFiberIsoInverseImageGamma :
    (spacesEtaleSitePoint x).sheafFiber (A := A) ≅
      (spacesBaseChange B S hS (geometricPointHom x)).functor.sheafPullback A
          (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS (geometricPointSpace x)) ⋙
        Sheaf.Γ (SpacesEtale.topology B S hS (geometricPointSpace x)) A :=
  eqToIso (congrArg (fun z : GeometricPoint B S hS X.1 ↦ (spacesEtaleSitePoint z).sheafFiber
      (A := A)) (geometricPointMap_geometricPointSpaceBase x).symm) ≪≫
    (spacesEtaleSheafFiberInverseImageIso (geometricPointHom x) (geometricPointSpaceBase x)
      A).symm ≪≫
    Functor.isoWhiskerLeft _ (spacesEtaleBaseSheafFiberIsoGamma x A)

end GeometricPoint

/-! ### Global sections of a direct image -/

section Pushforward

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (A : Type v) [Category.{w} A]
  [HasWeakSheafify (SpacesEtale.topology B S hS X) A]
  [HasWeakSheafify (SpacesEtale.topology B S hS Y) A]

/-- **Global sections of a direct image are global sections upstairs**: for `f : X ⟶ Y`, the
global sections of the direct image along `f` of a sheaf on the spaces-étale site of `X` are the
global sections of that sheaf, naturally in the sheaf. -/
def spacesPushforwardGammaIso :
    (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous A
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
      Sheaf.Γ (SpacesEtale.topology B S hS Y) A ≅
    Sheaf.Γ (SpacesEtale.topology B S hS X) A :=
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections (SpacesEtale.topology B S hS Y) A
      (SpacesEtale.isTerminal_idObj B S hS Y)) ≪≫
    NatIso.ofComponents (fun _ => Iso.refl _)
      (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm) ≪≫
    (Sheaf.ΓNatIsoSheafSections (SpacesEtale.topology B S hS X) A
      (isTerminal_spacesBaseChange_idObj B S hS f)).symm

end Pushforward

/-! ### The comparison of Stacks 0DG1 -/

section Comparison

variable {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (x : GeometricPoint B S hS X.1)

/-- **The comparison map of Stacks 0DG1.** For a morphism `f : Y ⟶ X` of algebraic spaces and a
geometric point `x̄ : Spec Ω ⟶ X`, the canonical map from the stalk `(f_* F)_x̄` to the global
sections of `F_x̄ = i⁻¹ F` on the geometric fibre `Y_x̄ = Y ×_X Spec Ω`, `i : Y_x̄ ⟶ Y` the
projection, naturally in the sheaf of sets `F` on the spaces-étale site of `Y`: the base-change
map of the cartesian square of the fibre, read on global sections over `Spec Ω` through the
identification of the stalk at `x̄` with the global sections of the inverse image and of the
global sections of a direct image with the global sections upstairs. -/
def spacesProperGeometricFibreComparison :
    (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y) ⋙
        (spacesEtaleSitePoint x).sheafFiber ⟶
      ((spacesBaseChange_isMorphismOfSites B S hS
          (pullback.fst f (geometricPointHom x))).morphismOfTopoi).inverseImage ⋙
        Sheaf.Γ (SpacesEtale.topology B S hS (pullback f (geometricPointHom x)))
          (Type (u + 1)) :=
  (Functor.isoWhiskerLeft _
      (spacesEtaleSheafFiberIsoInverseImageGamma x (Type (u + 1)))).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (spacesToposBaseChangeSquare B S hS (pullback.fst f (geometricPointHom x))
        (pullback.snd f (geometricPointHom x)) f (geometricPointHom x)
        (IsPullback.of_hasPullback f (geometricPointHom x)))
      (Sheaf.Γ (SpacesEtale.topology B S hS (geometricPointSpace x)) (Type (u + 1))) ≫
    (Functor.associator _ _ _).hom ≫
    (Functor.isoWhiskerLeft _
      (spacesPushforwardGammaIso (pullback.snd f (geometricPointHom x)) (Type (u + 1)))).hom

/-- **The comparison of Stacks 0DG1 is invertible as soon as the base-change map of Stacks 0DG0
of the geometric fibre square is.** -/
theorem isIso_spacesProperGeometricFibreComparison_of_isIso
    (hbc : IsIso (spacesToposBaseChangeSquare B S hS (pullback.fst f (geometricPointHom x))
      (pullback.snd f (geometricPointHom x)) f (geometricPointHom x)
      (IsPullback.of_hasPullback f (geometricPointHom x)))) :
    IsIso (spacesProperGeometricFibreComparison f x) := by
  dsimp only [spacesProperGeometricFibreComparison]
  have : IsIso (Functor.whiskerRight
      (spacesToposBaseChangeSquare B S hS (pullback.fst f (geometricPointHom x))
        (pullback.snd f (geometricPointHom x)) f (geometricPointHom x)
        (IsPullback.of_hasPullback f (geometricPointHom x)))
      (Sheaf.Γ (SpacesEtale.topology B S hS (geometricPointSpace x)) (Type (u + 1)))) :=
    Functor.isIso_whiskerRight _ _
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance ?_
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance ?_
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ this ?_
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance inferInstance

/-- **Stacks 0DG1, granted Stacks 0A3U.** Let `f : Y ⟶ X` be a proper morphism of algebraic
spaces over `S` and `x̄` a geometric point of `X`. For every sheaf `F` on `Y_étale` the canonical
map `(f_* F)_x̄ ⟶ Γ(Y_x̄, F_x̄)` is bijective. Stacks 0A3U is the hypothesis `h0A3U`. -/
theorem bijective_spacesProperGeometricFibreComparison_app_of_isIso
    (hf : IsProper B S hS f.hom)
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w))
    (F : Sheaf (SpacesEtale.topology B S hS Y) (Type (u + 1))) :
    Function.Bijective ((spacesProperGeometricFibreComparison f x).app F) := by
  have := isIso_spacesProperGeometricFibreComparison_of_isIso f x
    (isIso_spacesToposBaseChangeSquare_of_isProper_of_properBaseChange B S hS h0A3U f hf _ _ _
      (IsPullback.of_hasPullback f (geometricPointHom x)))
  exact (isIso_iff_bijective _).mp inferInstance

end Comparison

end AlgebraicGeometry.Space

end
