module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedChow.Restriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.BaseChangeLimits
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.RestrictedFibreProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeSpacesEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFinitePart

/-!
# Restriction of algebraic spaces to a smaller base and projective spaces

Let `g : T ⟶ S` be a morphism of a big fppf site. Restriction `R` of presheaves along `g`
(`CategoryTheory.OverShriek.relocalizeRestrict`) carries algebraic spaces over `S` to algebraic
spaces over `T`, the base change along `T ⟶ S`. This file records what the derived Chow lemma
(Stacks 0CTR) needs of it: `R` preserves closed immersions, open immersions and étale morphisms,
`R(ℙⁿ_S) ≅ ℙⁿ_T`, and `R(X₀ ×_S ℙⁿ_S) ≅ X ×_T ℙⁿ_T` for `X ≅ R X₀`.

## Main definitions

* `AlgebraicGeometry.Space.relocalizeRestrictSpace`, `AlgebraicGeometry.Space.restrictHom`: `R` on
  algebraic spaces and their morphisms.
* `AlgebraicGeometry.Space.restrictYonedaProjectiveSpaceIso`: `R(ℙⁿ_S) ≅ ℙⁿ_T`.
* `AlgebraicGeometry.Space.restrictProductIso`: `X ×_T ℙⁿ_T ≅ R(X₀ ×_S ℙⁿ_S)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open DerivedChow

variable {B : BigFppfSite.{u}} {T S : Scheme.{u}} {hT : B.Contains T} {hS : B.Contains S}
  (g : B.obj hT ⟶ B.obj hS)

/-- The restriction `R Y` of an algebraic space `Y` over `S` to `T`. -/
abbrev relocalizeRestrictSpace (Y : AlgebraicSpaces B S hS) : AlgebraicSpaces B T hT :=
  ⟨(OverShriek.relocalizeRestrict g).obj Y.1,
    isAlgebraicSpace_relocalizeRestrict B T S hT hS g Y.1 Y.2⟩

/-- The restriction `R f` of a morphism of algebraic spaces over `S` to `T`. -/
abbrev restrictHom {Y Z : AlgebraicSpaces B S hS} (f : Y ⟶ Z) :
    relocalizeRestrictSpace g Y ⟶ relocalizeRestrictSpace g Z :=
  ObjectProperty.homMk ((OverShriek.relocalizeRestrict g).map f.hom)

/-- Restriction to a smaller base preserves relative properties coming from a base change stable
property `Q` of schemes. -/
private theorem presheaf_relocalizeRestrict_map_of_isStableUnderBaseChange
    (Q : MorphismProperty Scheme.{u}) [Q.IsStableUnderBaseChange]
    {A G : (Over (B.obj hS))ᵒᵖ ⥤ Type u} {h : A ⟶ G}
    (hh : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf h) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B T hT)).presheaf
      ((OverShriek.relocalizeRestrict g).map h) := by
  have : Q.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B T hT)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  exact OverShriek.relative_relocalizeRestrict_map g
    (inverseImage_restrictReindexSnd B T S hT hS g _) hh

/-- **Restriction to a smaller base preserves closed immersions.** -/
theorem isClosedImmersion_restrictHom {Y Z : AlgebraicSpaces B S hS} (f : Y ⟶ Z)
    (hf : IsClosedImmersion B S hS f.hom) : IsClosedImmersion B T hT (restrictHom g f).hom :=
  presheaf_relocalizeRestrict_map_of_isStableUnderBaseChange g
    (@AlgebraicGeometry.IsClosedImmersion.{u}) hf

/-- **Restriction to a smaller base preserves open immersions.** -/
theorem isOpenImmersion_restrictHom {Y Z : AlgebraicSpaces B S hS} (f : Y ⟶ Z)
    (hf : IsOpenImmersion B S hS f.hom) : IsOpenImmersion B T hT (restrictHom g f).hom :=
  presheaf_relocalizeRestrict_map_of_isStableUnderBaseChange g
    (@AlgebraicGeometry.IsOpenImmersion.{u}) hf

/-- **Restriction to a smaller base preserves étale morphisms**: viewed again over `S`, the
restriction of `f` is a base change of `f`. -/
theorem isEtale_restrictHom {Y Z : AlgebraicSpaces B S hS} (f : Y ⟶ Z)
    (hf : IsEtale B S hS f.hom) : IsEtale B T hT (restrictHom g f).hom :=
  (isEtale_relocalizeHom_iff B hT hS g (restrictHom g f)).1
    (isEtale_of_isPullback_of_isAlgebraicSpace B S hS
      (isPullback_relocalize_relocalizeRestrict_map B S hS f.hom hT g).flip
      (relocalizeSpace B hT hS g (relocalizeRestrictSpace g Y)).2
      (relocalizeSpace B hT hS g (relocalizeRestrictSpace g Z)).2 Y.2 Z.2 hf)

/-- Projective `n`-space over `T` lies in the site when projective `n`-space over `S` does. -/
theorem contains_projectiveSpaceOver_of_hom (g' : B.obj hT ⟶ B.obj hS) (n : ℕ)
    (hP : B.Contains (projectiveSpaceOver n S)) :
    B.Contains (projectiveSpaceOver n T) := by
  have h := Scheme.size_pullback_lt (κ := B.cutoff) (projectiveSpaceOver n S ↘ S)
    (B.inclusion.map g') hP hT
  exact lt_of_eq_of_lt
    (Scheme.size_congr (projectiveSpaceOverBaseChangeIso n (B.inclusion.map g'))).symm h

/-- The base change of `ℙⁿ_S` along `T ⟶ S`, as an object of the site over `T`, is `ℙⁿ_T`. -/
def pullbackProjectiveSpaceSiteObjIso (n : ℕ) (hP : B.Contains (projectiveSpaceOver n S))
    (hPT : B.Contains (projectiveSpaceOver n T)) :
    (Over.pullback g).obj (projectiveSpaceSiteObj B S hS n hP) ≅
      projectiveSpaceSiteObj B T hT n hPT :=
  let E₁ :
      (Over.post B.inclusion).obj ((Over.pullback g).obj (projectiveSpaceSiteObj B S hS n hP)) ≅
      (Over.post B.inclusion).obj (projectiveSpaceSiteObj B T hT n hPT) :=
    (Over.postPullbackIso B.inclusion g).app _ ≪≫
      Over.isoMk (projectiveSpaceOverBaseChangeIso n (B.inclusion.map g))
        (projectiveSpaceOverBaseChangeIso_hom_over n _)
  (Functor.FullyFaithful.ofFullyFaithful (Over.post B.inclusion)).preimageIso E₁

/-- **`R(ℙⁿ_S) ≅ ℙⁿ_T`**, as presheaves on the site over `T`. -/
def restrictYonedaProjectiveSpaceIso (n : ℕ) (hP : B.Contains (projectiveSpaceOver n S))
    (hPT : B.Contains (projectiveSpaceOver n T)) :
    (OverShriek.relocalizeRestrict g).obj (yoneda.obj (projectiveSpaceSiteObj B S hS n hP)) ≅
      yoneda.obj (projectiveSpaceSiteObj B T hT n hPT) :=
  (OverShriek.restrictYonedaIso g _).symm ≪≫
    yoneda.mapIso (pullbackProjectiveSpaceSiteObjIso g n hP hPT)

/-- The restriction of the terminal object `h_S` is terminal. -/
def isTerminalRestrictYonedaBase :
    IsTerminal ((OverShriek.relocalizeRestrict g).obj (yoneda.obj (Over.mk (𝟙 (B.obj hS))))) :=
  (isTerminal_yoneda_obj_base B S hS).isTerminalObj _ _

/-- **`X ×_T ℙⁿ_T ≅ R(X₀ ×_S ℙⁿ_S)`** for an isomorphism `X ≅ R X₀`, compatibly with the two
projections. -/
def restrictProductIso {X₀ : AlgebraicSpaces B S hS} {X : AlgebraicSpaces B T hT}
    (eX : X.1 ≅ (OverShriek.relocalizeRestrict g).obj X₀.1) (n : ℕ)
    (hP : B.Contains (projectiveSpaceOver n S)) (hPT : B.Contains (projectiveSpaceOver n T)) :
    (product B T hT X n hPT).1 ≅ (relocalizeRestrictSpace g (product B S hS X₀ n hP)).1 :=
  IsPullback.isoIsPullback _ _ (IsPullback.of_hasPullback _ _)
    (IsPullback.of_iso ((IsPullback.of_hasPullback (toBase B S hS X₀).hom
        (yoneda.map (projectiveSpaceSiteObjToBase B S hS n hP))).map
          (OverShriek.relocalizeRestrict g))
      (fst' := (OverShriek.relocalizeRestrict g).map (productFst X₀ n hP).hom ≫ eX.inv)
      (snd' := (OverShriek.relocalizeRestrict g).map (productSnd X₀ n hP).hom ≫
        (restrictYonedaProjectiveSpaceIso g n hP hPT).hom)
      (Iso.refl _) eX.symm (restrictYonedaProjectiveSpaceIso g n hP hPT)
      ((isTerminalRestrictYonedaBase g).uniqueUpToIso (isTerminal_yoneda_obj_base B T hT))
      (by exact (Category.id_comp _).symm) (by exact (Category.id_comp _).symm)
      ((isTerminal_yoneda_obj_base B T hT).hom_ext _ _)
      ((isTerminal_yoneda_obj_base B T hT).hom_ext _ _))

/-- `restrictProductIso` is compatible with the projections to `X` and `R X₀`. -/
@[reassoc (attr := simp)]
theorem restrictProductIso_hom_fst {X₀ : AlgebraicSpaces B S hS} {X : AlgebraicSpaces B T hT}
    (eX : X.1 ≅ (OverShriek.relocalizeRestrict g).obj X₀.1) (n : ℕ)
    (hP : B.Contains (projectiveSpaceOver n S)) (hPT : B.Contains (projectiveSpaceOver n T)) :
    (restrictProductIso g eX n hP hPT).hom ≫
        (OverShriek.relocalizeRestrict g).map (productFst X₀ n hP).hom =
      (productFst X n hPT).hom ≫ eX.hom :=
  (Iso.comp_inv_eq _).1 (by rw [Category.assoc]; exact IsPullback.isoIsPullback_hom_fst _ _ _ _)

/-- `restrictProductIso` is compatible with the projections to `ℙⁿ_T` and `R(ℙⁿ_S)`. -/
@[reassoc (attr := simp)]
theorem restrictProductIso_hom_snd {X₀ : AlgebraicSpaces B S hS} {X : AlgebraicSpaces B T hT}
    (eX : X.1 ≅ (OverShriek.relocalizeRestrict g).obj X₀.1) (n : ℕ)
    (hP : B.Contains (projectiveSpaceOver n S)) (hPT : B.Contains (projectiveSpaceOver n T)) :
    (restrictProductIso g eX n hP hPT).hom ≫
        (OverShriek.relocalizeRestrict g).map (productSnd X₀ n hP).hom =
      (productSnd X n hPT).hom ≫ (restrictYonedaProjectiveSpaceIso g n hP hPT).inv :=
  (Iso.eq_comp_inv _).2 (by rw [Category.assoc]; exact IsPullback.isoIsPullback_hom_snd _ _ _ _)

/-- The inverse of `restrictProductIso` is compatible with the projections to `R X₀` and `X`. -/
@[reassoc (attr := simp)]
theorem restrictProductIso_inv_fst {X₀ : AlgebraicSpaces B S hS} {X : AlgebraicSpaces B T hT}
    (eX : X.1 ≅ (OverShriek.relocalizeRestrict g).obj X₀.1) (n : ℕ)
    (hP : B.Contains (projectiveSpaceOver n S)) (hPT : B.Contains (projectiveSpaceOver n T)) :
    (restrictProductIso g eX n hP hPT).inv ≫ (productFst X n hPT).hom =
      (OverShriek.relocalizeRestrict g).map (productFst X₀ n hP).hom ≫ eX.inv :=
  IsPullback.isoIsPullback_inv_fst _ _ _ _

/-- The inverse of `restrictProductIso` is compatible with the projections to `R(ℙⁿ_S)` and
`ℙⁿ_T`. -/
@[reassoc (attr := simp)]
theorem restrictProductIso_inv_snd {X₀ : AlgebraicSpaces B S hS} {X : AlgebraicSpaces B T hT}
    (eX : X.1 ≅ (OverShriek.relocalizeRestrict g).obj X₀.1) (n : ℕ)
    (hP : B.Contains (projectiveSpaceOver n S)) (hPT : B.Contains (projectiveSpaceOver n T)) :
    (restrictProductIso g eX n hP hPT).inv ≫ (productSnd X n hPT).hom =
      (OverShriek.relocalizeRestrict g).map (productSnd X₀ n hP).hom ≫
        (restrictYonedaProjectiveSpaceIso g n hP hPT).hom :=
  IsPullback.isoIsPullback_inv_snd _ _ _ _

/-- An isomorphism of the underlying presheaves is an isomorphism of algebraic spaces. -/
instance isIso_homMk_hom {A C : AlgebraicSpaces B T hT} (e : A.1 ≅ C.1) :
    IsIso (ObjectProperty.homMk e.hom : A ⟶ C) :=
  ⟨⟨ObjectProperty.homMk e.inv, ObjectProperty.hom_ext _ e.hom_inv_id,
    ObjectProperty.hom_ext _ e.inv_hom_id⟩⟩

/-- An isomorphism of the underlying presheaves is an isomorphism of algebraic spaces. -/
instance isIso_homMk_inv {A C : AlgebraicSpaces B T hT} (e : A.1 ≅ C.1) :
    IsIso (ObjectProperty.homMk e.inv : C ⟶ A) :=
  isIso_homMk_hom e.symm

/-- The underlying morphism of presheaves of `ObjectProperty.homMk e.hom` is an isomorphism. -/
instance isIso_homMk_hom_hom {A C : AlgebraicSpaces B T hT} (e : A.1 ≅ C.1) :
    IsIso (ObjectProperty.homMk e.hom : A ⟶ C).hom :=
  inferInstanceAs (IsIso e.hom)

/-- The underlying morphism of presheaves of `ObjectProperty.homMk e.inv` is an isomorphism. -/
instance isIso_homMk_inv_hom {A C : AlgebraicSpaces B T hT} (e : A.1 ≅ C.1) :
    IsIso (ObjectProperty.homMk e.inv : C ⟶ A).hom :=
  inferInstanceAs (IsIso e.inv)

end AlgebraicGeometry.Space

end
