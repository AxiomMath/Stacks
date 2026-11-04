module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.CoefficientsGerm
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardStalkComparisonGeneral

/-!
# The stalk comparison of a direct image, on germs

For a morphism `f : Y ⟶ X` of algebraic spaces over `S` and a geometric point `ȳ` of `Y` with
image `x̄ = f(ȳ)`, `AlgebraicGeometry.Space.smallEtaleAbelianDirectImageStalkMap` is the
canonical comparison `(f_*F)_{x̄} ⟶ F_ȳ`, built out of the identification of Stacks 04K2
part (4) and the stalk at `ȳ` of the counit of `f^{-1} ⊣ f_*`.  This file computes it on germs.

A section of `f_*F` over an étale chart `U` of `X` is, by definition of the direct image as a
conjugate by the comparison equivalences of Stacks 03G1, a section of the spaces-étale
extension of `F` over the base change `U ×_X Y`.  Given a lift `u` of `x̄` into `U`, the
cartesian square of Stacks 03G2 part (1) gives a lift of `ȳ` into `U ×_X Y`; for any chart `W`
of `Y`, a lift `w` of `ȳ` into it and a map `h : W ⟶ U ×_X Y` carrying `w` to that lift, the
comparison sends the germ of the section at `u` to the germ at `w` of its restriction along `h`,
read on `W` through the counit of the comparison equivalence.

The proof chases the germ through the five pieces of the identification of Stacks 04K2 part (4)
(each sends a germ to a germ in front of a map of sections), and then cancels the resulting
chain of units and counits on sections by the triangle identities of the comparison
equivalences and of the spaces-étale inverse-image adjunction.

## Main results

* `AlgebraicGeometry.Space.smallEtaleAbelianDirectImageStalkMap_germ`: the germ formula.
* `AlgebraicGeometry.Space.spacesComparisonSheafFiberIso_hom_germ` and
  `AlgebraicGeometry.Space.spacesComparisonSheafFiberIso_inv_germ`: the fibre comparison of
  Stacks 04JZ on germs.
* `AlgebraicGeometry.Space.smallEtaleAbelianGeneralInverseImageStalkIso_eq`: the identification
  of Stacks 04K2 part (4) for an arbitrary morphism, as its fibre part
  `AlgebraicGeometry.Space.smallEtaleAbelianGeneralInverseImageFiberIso` framed by the two
  comparisons of point-stalks with geometric stalks.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 04JZ](https://stacks.math.columbia.edu/tag/04JZ)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The fibre comparison of Stacks 04JZ on germs: the germ at a lift into an étale chart of a
section of a spaces-étale sheaf is the germ at the same lift of the same section of its
restriction to the small étale site. -/
@[reassoc]
theorem spacesComparisonSheafFiberIso_hom_germ {X : AlgebraicSpaces B S hS}
    (x : GeometricPoint B S hS X.1) (hX : IsAlgebraicSpace B S hS X.1)
    {A : Type*} [Category A] [HasColimitsOfSize.{u, u} A]
    (K : Sheaf (SpacesEtale.topology B S hS X) A) (V : SmallEtale B S hS X.1)
    (v : (etaleSitePoint B S hS X.1 x hX).fiber.obj V) :
    (spacesEtaleSitePoint x).toPresheafFiber ((comparisonFunctor B S hS X).obj V) v K.obj ≫
        (spacesComparisonSheafFiberIso B S hS x hX).hom.app K =
      (etaleSitePoint B S hS X.1 x hX).toPresheafFiber V v
        (((comparisonFunctor B S hS X).sheafPushforwardContinuous A
          (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).obj K).obj := by
  have : HasColimitsOfShape (spacesGeometricFiber x).Elementsᵒᵖ A :=
    inferInstanceAs (HasColimitsOfShape (spacesEtaleSitePoint x).fiber.Elementsᵒᵖ A)
  have : HasColimitsOfShape (geometricFiber B S hS X.1 x).Elementsᵒᵖ A :=
    inferInstanceAs (HasColimitsOfShape (etaleSitePoint B S hS X.1 x hX).fiber.Elementsᵒᵖ A)
  have h := Functor.Final.ι_colimitIso_inv (smallToSpacesFiberElements B S hS x).op
    ((CategoryOfElements.π (spacesGeometricFiber x)).op ⋙ K.obj) (op ⟨V, v⟩)
  have e : (spacesComparisonSheafFiberIso B S hS x hX).hom.app K =
      (Functor.Final.colimitIso (smallToSpacesFiberElements B S hS x).op
        ((CategoryOfElements.π (spacesGeometricFiber x)).op ⋙ K.obj)).inv ≫ 𝟙 _ ≫
        (etaleSitePoint B S hS X.1 x hX).presheafFiber.map
          (𝟙 ((comparisonFunctor B S hS X).op ⋙ K.obj)) ≫ 𝟙 _ := rfl
  have hid : ∀ {a b : A} (g : a ⟶ b), g ≫ 𝟙 b ≫ 𝟙 b ≫ 𝟙 b = g := fun g => by simp
  rw [e, CategoryTheory.Functor.map_id]
  refine Eq.trans ?_ h
  exact whisker_eq _ (hid _)

/-- The fibre comparison of Stacks 04JZ, inverted, on germs. -/
theorem spacesComparisonSheafFiberIso_inv_germ {X : AlgebraicSpaces B S hS}
    (x : GeometricPoint B S hS X.1) (hX : IsAlgebraicSpace B S hS X.1)
    {A : Type*} [Category A] [HasColimitsOfSize.{u, u} A]
    (K : Sheaf (SpacesEtale.topology B S hS X) A) (V : SmallEtale B S hS X.1)
    (v : (etaleSitePoint B S hS X.1 x hX).fiber.obj V) :
    (etaleSitePoint B S hS X.1 x hX).toPresheafFiber V v
        (((comparisonFunctor B S hS X).sheafPushforwardContinuous A
          (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).obj K).obj ≫
        (spacesComparisonSheafFiberIso B S hS x hX).inv.app K =
      (spacesEtaleSitePoint x).toPresheafFiber ((comparisonFunctor B S hS X).obj V) v K.obj :=
  (((spacesComparisonSheafFiberIso B S hS x hX).app K).comp_inv_eq).2
    (spacesComparisonSheafFiberIso_hom_germ B S hS x hX K V v).symm

/-- The fibre at a geometric point of an abelian sheaf on the small étale site, read on the
spaces-étale site through the comparison equivalence of Stacks 03G1: the fibre of a sheaf is the
fibre of its extension to the spaces-étale site. -/
def smallEtaleAbelianSheafFiberSpacesIso (Y : AlgebraicSpaces B S hS)
    (y : GeometricPoint B S hS Y.1) :
    (etaleSitePoint B S hS Y.1 y Y.2).sheafFiber (A := AddCommGrpCat.{u + 1}) ≅
      (smallEtaleAbelianSheafComparisonEquiv B S hS Y).inverse ⋙
        (spacesEtaleSitePoint y).sheafFiber :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (smallEtaleAbelianSheafComparisonEquiv B S hS Y).counitIso.symm _ ≪≫
    Functor.associator .. ≪≫
    Functor.isoWhiskerLeft (smallEtaleAbelianSheafComparisonEquiv B S hS Y).inverse
      (spacesComparisonSheafFiberIso B S hS y Y.2).symm

/-- The fibre at the image geometric point, read through base change on the spaces-étale sites:
Mathlib's fibre of an inverse image at a comap point, followed by the invariance of the
elements-colimit under the cartesian square of Stacks 03G2, part (1). -/
def spacesBaseChangeSheafFiberIso {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (y : GeometricPoint B S hS Y.1) :
    (spacesBaseChange B S hS f).functor.sheafPullback AddCommGrpCat.{u + 1}
        (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y) ⋙
      (spacesEtaleSitePoint y).sheafFiber ≅
      (spacesEtaleSitePoint (geometricPointMap f.hom y)).sheafFiber := by
  let A := AddCommGrpCat.{u + 1}
  let Ksrc := SpacesEtale.topology B S hS Y
  let Ktgt := SpacesEtale.topology B S hS X
  let g := (spacesBaseChange B S hS f).functor
  let x := geometricPointMap f.hom y
  let Psrc := spacesEtaleSitePoint y
  let Ptgt := spacesEtaleSitePoint x
  letI : RepresentablyFlat g := representablyFlat_spacesBaseChange B S hS f
  let hcover : CoverPreserving Ktgt Ksrc g := CoverPreserving.of_isContinuous g Ktgt Ksrc
  let efib : g ⋙ Psrc.fiber ≅ Ptgt.fiber := spacesBaseChangeFiberIso B S hS f y
  haveI : InitiallySmall.{u} (g ⋙ Psrc.fiber).Elements :=
    initiallySmall_of_initial_of_initiallySmall
      (CategoryOfElements.equivalenceOfNatIso efib).inverse
  let Pg := Psrc.comap g hcover
  haveI : HasColimitsOfShape (g ⋙ Psrc.fiber).Elementsᵒᵖ A :=
    inferInstanceAs (HasColimitsOfShape Pg.fiber.Elementsᵒᵖ A)
  haveI : HasColimitsOfShape Ptgt.fiber.Elementsᵒᵖ A := inferInstance
  let eComap : Pg.sheafFiber (A := A) ≅ g.sheafPullback A Ktgt Ksrc ⋙ Psrc.sheafFiber :=
    Psrc.sheafFiberComapIso g hcover A
  let eBase : Pg.sheafFiber (A := A) ≅ Ptgt.sheafFiber :=
    Functor.isoWhiskerLeft (sheafToPresheaf Ktgt A)
      (CategoryOfElements.presheafColimIsoOfNatIsoOfCoefficients efib)
  exact eComap.symm ≪≫ eBase

/-- `AlgebraicGeometry.Space.smallEtaleAbelianSheafFiberSpacesIso` on germs: a germ at a lift
into an étale chart goes to the germ at the same lift of the section read in the extension to the
spaces-étale site through the inverse counit. -/
theorem smallEtaleAbelianSheafFiberSpacesIso_hom_germ (Y : AlgebraicSpaces B S hS)
    (y : GeometricPoint B S hS Y.1)
    (L : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1})
    (W : SmallEtale B S hS Y.1) (w : (etaleSitePoint B S hS Y.1 y Y.2).fiber.obj W) :
    (etaleSitePoint B S hS Y.1 y Y.2).toPresheafFiber W w L.obj ≫
        (smallEtaleAbelianSheafFiberSpacesIso B S hS Y y).hom.app L =
      ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).counitInv.app L).hom.app (op W) ≫
        (spacesEtaleSitePoint y).toPresheafFiber ((comparisonFunctor B S hS Y).obj W) w
          ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).inverse.obj L).obj := by
  have e : (smallEtaleAbelianSheafFiberSpacesIso B S hS Y y).hom.app L =
      (etaleSitePoint B S hS Y.1 y Y.2).sheafFiber.map
          ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).counitInv.app L) ≫
        (spacesComparisonSheafFiberIso B S hS y Y.2).inv.app
          ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).inverse.obj L) := by
    simp [smallEtaleAbelianSheafFiberSpacesIso]
    rfl
  rw [e]
  exact (GrothendieckTopology.Point.toSheafFiber_naturality_assoc (etaleSitePoint B S hS Y.1 y Y.2)
      ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).counitInv.app L) W w _).trans
    (whisker_eq _ (spacesComparisonSheafFiberIso_inv_germ B S hS y Y.2
        ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).inverse.obj L) W w))

/-- `AlgebraicGeometry.Space.smallEtaleAbelianSheafFiberSpacesIso`, inverted, on germs. -/
theorem smallEtaleAbelianSheafFiberSpacesIso_inv_germ (Y : AlgebraicSpaces B S hS)
    (y : GeometricPoint B S hS Y.1)
    (L : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1})
    (W : SmallEtale B S hS Y.1) (w : (etaleSitePoint B S hS Y.1 y Y.2).fiber.obj W) :
    (spacesEtaleSitePoint y).toPresheafFiber ((comparisonFunctor B S hS Y).obj W) w
          ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).inverse.obj L).obj ≫
        (smallEtaleAbelianSheafFiberSpacesIso B S hS Y y).inv.app L =
      ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).counit.app L).hom.app (op W) ≫
        (etaleSitePoint B S hS Y.1 y Y.2).toPresheafFiber W w L.obj := by
  have e : (smallEtaleAbelianSheafFiberSpacesIso B S hS Y y).inv.app L =
      (spacesComparisonSheafFiberIso B S hS y Y.2).hom.app
          ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).inverse.obj L) ≫
        (etaleSitePoint B S hS Y.1 y Y.2).sheafFiber.map
          ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).counit.app L) := by
    simp [smallEtaleAbelianSheafFiberSpacesIso]
    rfl
  rw [e]
  exact (spacesComparisonSheafFiberIso_hom_germ_assoc B S hS y Y.2
      ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).inverse.obj L) W w _).trans
    (GrothendieckTopology.Point.toSheafFiber_naturality (etaleSitePoint B S hS Y.1 y Y.2)
      ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).counit.app L) W w)

/-- `AlgebraicGeometry.Space.spacesBaseChangeSheafFiberIso`, inverted, on germs: the germ at a
lift `efib(e)` of the image point of a section `s` over `V` goes to the germ at `e` of the
pull-back of `s` along the unit of the inverse-image adjunction. -/
theorem spacesBaseChangeSheafFiberIso_inv_germ {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (y : GeometricPoint B S hS Y.1)
    (M : Sheaf (SpacesEtale.topology B S hS X) AddCommGrpCat.{u + 1})
    (V : SpacesEtale B S hS X)
    (e : (spacesEtaleSitePoint y).fiber.obj ((spacesBaseChange B S hS f).functor.obj V)) :
    (spacesEtaleSitePoint (geometricPointMap f.hom y)).toPresheafFiber V
          ((spacesBaseChangeFiberIso B S hS f y).hom.app V e) M.obj ≫
        (spacesBaseChangeSheafFiberIso B S hS f y).inv.app M =
      (((spacesBaseChange B S hS f).functor.sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
          (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)).unit.app M).hom.app
          (op V) ≫
        (spacesEtaleSitePoint y).toPresheafFiber ((spacesBaseChange B S hS f).functor.obj V) e
          (((spacesBaseChange B S hS f).functor.sheafPullback AddCommGrpCat.{u + 1}
            (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)).obj M).obj := by
  let A := AddCommGrpCat.{u + 1}
  let Ksrc := SpacesEtale.topology B S hS Y
  let Ktgt := SpacesEtale.topology B S hS X
  let g := (spacesBaseChange B S hS f).functor
  let x := geometricPointMap f.hom y
  let Psrc := spacesEtaleSitePoint y
  let Ptgt := spacesEtaleSitePoint x
  let : RepresentablyFlat g := representablyFlat_spacesBaseChange B S hS f
  let hcover : CoverPreserving Ktgt Ksrc g := CoverPreserving.of_isContinuous g Ktgt Ksrc
  let efib : g ⋙ Psrc.fiber ≅ Ptgt.fiber := spacesBaseChangeFiberIso B S hS f y
  have : InitiallySmall.{u} (g ⋙ Psrc.fiber).Elements :=
    initiallySmall_of_initial_of_initiallySmall
      (CategoryOfElements.equivalenceOfNatIso efib).inverse
  let Pg := Psrc.comap g hcover
  have : HasColimitsOfShape (g ⋙ Psrc.fiber).Elementsᵒᵖ A :=
    inferInstanceAs (HasColimitsOfShape Pg.fiber.Elementsᵒᵖ A)
  have : HasColimitsOfShape Ptgt.fiber.Elementsᵒᵖ A := inferInstance
  let eComap : Pg.sheafFiber (A := A) ≅ g.sheafPullback A Ktgt Ksrc ⋙ Psrc.sheafFiber :=
    Psrc.sheafFiberComapIso g hcover A
  have h1 : Ptgt.toPresheafFiber V (efib.hom.app V e) M.obj =
      Pg.toPresheafFiber V e M.obj ≫
        (CategoryOfElements.presheafColimIsoOfNatIsoOfCoefficients (A := A) efib).hom.app M.obj :=
    (CategoryOfElements.ι_presheafColimIsoOfNatIsoOfCoefficients_hom efib M.obj (op ⟨V, e⟩)).symm
  have h2 := GrothendieckTopology.Point.toSheafFiber_sheafFiberComapIso_hom Psrc g hcover M V e
  show Ptgt.toPresheafFiber V (efib.hom.app V e) M.obj ≫
      ((CategoryOfElements.presheafColimIsoOfNatIsoOfCoefficients (A := A) efib).inv.app M.obj ≫
        eComap.hom.app M) = _
  rw [h1]
  exact (Category.assoc _ _ _).trans ((whisker_eq _
    (Iso.hom_inv_id_app_assoc
      (CategoryOfElements.presheafColimIsoOfNatIsoOfCoefficients (A := A) efib) M.obj
      (eComap.hom.app M))).trans h2)

/-- The inverse of a composite of isomorphisms of the shape of the fibre part of Stacks 04K2
part (4), computed on an object, in arbitrary categories. -/
private theorem chainIso_inv_app {C₁ C₂ C₃ C₄ E : Type*} [Category C₁] [Category C₂] [Category C₃]
    [Category C₄] [Category E] (F₀ : C₁ ⥤ C₄) (I : C₁ ⥤ C₂) (P : C₂ ⥤ C₃) (Iy : C₄ ⥤ C₃)
    (q : C₄ ⥤ E) (Ψ : C₃ ⥤ E) (Φ : C₂ ⥤ E) (p : C₁ ⥤ E) (eQY : q ≅ Iy ⋙ Ψ)
    (ePull : F₀ ⋙ Iy ≅ I ⋙ P) (eBC : P ⋙ Ψ ≅ Φ) (eQX : p ≅ I ⋙ Φ) (G : C₁) :
    (Functor.isoWhiskerLeft F₀ eQY ≪≫ (Functor.associator ..).symm ≪≫
        Functor.isoWhiskerRight ePull Ψ ≪≫ Functor.associator .. ≪≫
        Functor.isoWhiskerLeft I eBC ≪≫ eQX.symm).inv.app G =
      eQX.hom.app G ≫ eBC.inv.app (I.obj G) ≫ Ψ.map (ePull.inv.app G) ≫
        eQY.inv.app (F₀.obj G) := by
  simp

/-- Cancelling a unit isomorphism against a right unitor, computed on an object. -/
private theorem isoWhiskerLeft_symm_trans_rightUnitor_inv_app {C D : Type*} [Category C]
    [Category D] (F : C ⥤ D) {T : D ⥤ D} (η : 𝟭 D ≅ T) (G : C) :
    (Functor.isoWhiskerLeft F η.symm ≪≫ Functor.rightUnitor F).inv.app G =
      η.hom.app (F.obj G) := by
  simp

/-- A cancellation of six composable morphisms in an arbitrary category. -/
private theorem comp_six_eq_of_triangles {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ B₁ A₆ B₃ : C}
    (σ₁ : A₀ ⟶ A₁) (σ₂ : A₁ ⟶ A₂) (σ₃ : A₂ ⟶ A₃) (ρ : A₃ ⟶ A₄) (σ₅ : A₄ ⟶ B₁) (σ₆ : B₁ ⟶ A₆)
    (ν : A₂ ⟶ B₁) (μ : B₁ ⟶ A₄) (ξ : B₁ ⟶ B₃) (κ : B₃ ⟶ A₆) (ζ : A₂ ⟶ A₀) (τ : A₀ ⟶ B₃)
    (h₁ : σ₃ ≫ ρ = ν ≫ μ) (h₂ : μ ≫ σ₅ = 𝟙 B₁) (h₃ : σ₆ = ξ ≫ κ) (h₄ : ν ≫ ξ = ζ ≫ τ)
    (h₅ : σ₁ ≫ σ₂ ≫ ζ = 𝟙 A₀) :
    σ₁ ≫ σ₂ ≫ σ₃ ≫ ρ ≫ σ₅ ≫ σ₆ = τ ≫ κ := by
  calc σ₁ ≫ σ₂ ≫ σ₃ ≫ ρ ≫ σ₅ ≫ σ₆ = σ₁ ≫ σ₂ ≫ ν ≫ (μ ≫ σ₅) ≫ σ₆ := by
        rw [reassoc_of% h₁]; simp only [Category.assoc]
    _ = (σ₁ ≫ σ₂ ≫ ζ) ≫ τ ≫ κ := by
        rw [h₂, Category.id_comp, h₃, reassoc_of% h₄]; simp only [Category.assoc]
    _ = τ ≫ κ := by rw [h₅, Category.id_comp]

/-- For an adjunction `L ⊣ R`, the unit followed by `R` of the adjoint transpose of `a` is
`a`, with the transpose written as `L.map a ≫ ε`. -/
private theorem unit_app_comp_map_map_comp_counit {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {M : C} {H : D} (a : M ⟶ R.obj H) :
    adj.unit.app M ≫ R.map (L.map a ≫ adj.counit.app H) = a := by
  simp

/-- Chasing a germ through five maps of stalks, each of which sends a germ to a germ in front of
a map of sections, in an arbitrary category. -/
private theorem germ_chase_five {C : Type*} [Category C]
    {b₀ b₁ b₂ b₃ b₃' b₄ b₅ s₀ s₁ s₂ s₃ s₄ s₅ : C}
    {g₀ : b₀ ⟶ s₀} {g₁ : b₁ ⟶ s₁} {g₂ : b₂ ⟶ s₂} {g₃ : b₃' ⟶ s₃} {g₄ : b₄ ⟶ s₄}
    {g₅ : b₅ ⟶ s₅} {x₁ : s₀ ⟶ s₁} {x₂ : s₁ ⟶ s₂} {x₃ : s₂ ⟶ s₃} {x₄ : s₃ ⟶ s₄}
    {x₅ : s₄ ⟶ s₅} {σ₁ : b₀ ⟶ b₁} {σ₂ : b₁ ⟶ b₂} {σ₃ : b₂ ⟶ b₃} {σ₃' : b₃ ⟶ b₃'}
    {σ₄ : b₃' ⟶ b₄} {σ₅ : b₄ ⟶ b₅} {τ : b₀ ⟶ b₅}
    (h₁ : g₀ ≫ x₁ = σ₁ ≫ g₁) (h₂ : g₁ ≫ x₂ = σ₂ ≫ g₂) (h₃ : g₂ ≫ x₃ = (σ₃ ≫ σ₃') ≫ g₃)
    (h₄ : g₃ ≫ x₄ = σ₄ ≫ g₄) (h₅ : g₄ ≫ x₅ = σ₅ ≫ g₅)
    (hσ : σ₁ ≫ σ₂ ≫ σ₃ ≫ σ₃' ≫ σ₄ ≫ σ₅ = τ) :
    g₀ ≫ x₁ ≫ x₂ ≫ x₃ ≫ x₄ ≫ x₅ = τ ≫ g₅ := by
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄, h₅, ← hσ]
  simp only [Category.assoc]

/-- The inverse of an isomorphism framed by two whiskered isomorphisms, computed on an object,
in arbitrary categories. -/
private theorem isoWhiskerLeft_frame_inv_app {C₁ C₂ D₁ D₂ E : Type*} [Category C₁] [Category C₂]
    [Category D₁] [Category D₂] [Category E] (F₀ : C₁ ⥤ C₂) (T : C₂ ⥤ D₂) (T' : C₁ ⥤ D₁)
    {Φ Φ' : D₂ ⥤ E} {Ψ Ψ' : D₁ ⥤ E} (a : Φ ≅ Φ') (e : F₀ ⋙ T ⋙ Φ ≅ T' ⋙ Ψ) (b : Ψ ≅ Ψ')
    (G : C₁) :
    (Functor.isoWhiskerLeft F₀ (Functor.isoWhiskerLeft T a.symm) ≪≫ e ≪≫
        Functor.isoWhiskerLeft T' b).inv.app G =
      b.inv.app (T'.obj G) ≫ e.inv.app G ≫ a.hom.app (T.obj (F₀.obj G)) := by
  simp

/-- Cancelling an isomorphism against its inverse in front of a naturality square, in an
arbitrary category. -/
private theorem comp_iso_frame_eq {C : Type*} [Category C] {a P P' Q R R' Q' z₀ z₁ : C} (g₀ : a ⟶ P)
    (α : P ≅ P') (E : P ⟶ Q) (s₁ : Q ⟶ R) (m : R ⟶ R') (qm : Q ⟶ Q') (s₂ : Q' ⟶ R')
    (z₁' : a ⟶ z₀) (z₂ : z₀ ⟶ z₁) (z₃ : z₁ ⟶ Q') (I : P' ⟶ R) (hI : I = α.inv ≫ E ≫ s₁)
    (hnat : qm ≫ s₂ = s₁ ≫ m) (hcore : g₀ ≫ E ≫ qm = (z₁' ≫ z₂) ≫ z₃) :
    g₀ ≫ α.hom ≫ I ≫ m = z₁' ≫ z₂ ≫ z₃ ≫ s₂ := by
  subst hI
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← hnat, reassoc_of% hcore]

variable {X Y : AlgebraicSpaces B S hS}

/-- The fibre part of the identification of Stacks 04K2 part (4) for an arbitrary morphism. -/
def smallEtaleAbelianGeneralInverseImageFiberIso (f : Y ⟶ X)
    (y : GeometricPoint B S hS Y.1) :
    smallEtaleAbelianGeneralInverseImage B S hS f ⋙
        (etaleSitePoint B S hS Y.1 y Y.2).sheafFiber (A := AddCommGrpCat.{u + 1}) ≅
      (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).sheafFiber :=
  Functor.isoWhiskerLeft _ (smallEtaleAbelianSheafFiberSpacesIso B S hS Y y) ≪≫
    (Functor.associator ..).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft ((smallEtaleAbelianSheafComparisonEquiv B S hS X).inverse ⋙
          (spacesBaseChange B S hS f).functor.sheafPullback AddCommGrpCat.{u + 1}
            (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y))
          (smallEtaleAbelianSheafComparisonEquiv B S hS Y).unitIso.symm ≪≫
        Functor.rightUnitor _) _ ≪≫
    Functor.associator .. ≪≫
    Functor.isoWhiskerLeft (smallEtaleAbelianSheafComparisonEquiv B S hS X).inverse
      (spacesBaseChangeSheafFiberIso B S hS f y) ≪≫
    (smallEtaleAbelianSheafFiberSpacesIso B S hS X (geometricPointMap f.hom y)).symm

/-- The identification of Stacks 04K2 part (4) for an arbitrary morphism, unfolded into its
fibre part and the two comparisons of point-stalks with geometric stalks. -/
theorem smallEtaleAbelianGeneralInverseImageStalkIso_eq (f : Y ⟶ X)
    (y : GeometricPoint B S hS Y.1) :
    smallEtaleAbelianGeneralInverseImageStalkIso B S hS f y =
      Functor.isoWhiskerLeft (smallEtaleAbelianGeneralInverseImage B S hS f)
          (Functor.isoWhiskerLeft (sheafToPresheaf (SmallEtale.topology B S hS Y.1) _)
            (etaleSitePointStalkFunctorIso B S hS Y.1 y Y.2).symm) ≪≫
        smallEtaleAbelianGeneralInverseImageFiberIso B S hS f y ≪≫
        Functor.isoWhiskerLeft (sheafToPresheaf (SmallEtale.topology B S hS X.1) _)
          (etaleSitePointStalkFunctorIso B S hS X.1 (geometricPointMap f.hom y) X.2) :=
  rfl

/-- The inverse of the fibre part of Stacks 04K2 part (4), as the composite of its four
pieces. -/
theorem smallEtaleAbelianGeneralInverseImageFiberIso_inv_app (f : Y ⟶ X)
    (y : GeometricPoint B S hS Y.1)
    (G : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) :
    (smallEtaleAbelianGeneralInverseImageFiberIso B S hS f y).inv.app G =
      (smallEtaleAbelianSheafFiberSpacesIso B S hS X (geometricPointMap f.hom y)).hom.app G ≫
        (spacesBaseChangeSheafFiberIso B S hS f y).inv.app
          ((smallEtaleAbelianSheafComparisonEquiv B S hS X).inverse.obj G) ≫
        (spacesEtaleSitePoint y).sheafFiber.map
          ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).unit.app
            (((spacesBaseChange B S hS f).functor.sheafPullback AddCommGrpCat.{u + 1}
              (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)).obj
              ((smallEtaleAbelianSheafComparisonEquiv B S hS X).inverse.obj G))) ≫
        (smallEtaleAbelianSheafFiberSpacesIso B S hS Y y).inv.app
          ((smallEtaleAbelianGeneralInverseImage B S hS f).obj G) := by
  have hpull := chainIso_inv_app (smallEtaleAbelianGeneralInverseImage B S hS f)
    (smallEtaleAbelianSheafComparisonEquiv B S hS X).inverse
    ((spacesBaseChange B S hS f).functor.sheafPullback AddCommGrpCat.{u + 1}
      (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y))
    (smallEtaleAbelianSheafComparisonEquiv B S hS Y).inverse _ _ _ _
    (smallEtaleAbelianSheafFiberSpacesIso B S hS Y y)
    (Functor.isoWhiskerLeft ((smallEtaleAbelianSheafComparisonEquiv B S hS X).inverse ⋙
          (spacesBaseChange B S hS f).functor.sheafPullback AddCommGrpCat.{u + 1}
            (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y))
          (smallEtaleAbelianSheafComparisonEquiv B S hS Y).unitIso.symm ≪≫
        Functor.rightUnitor _)
    (spacesBaseChangeSheafFiberIso B S hS f y)
    (smallEtaleAbelianSheafFiberSpacesIso B S hS X (geometricPointMap f.hom y)) G
  refine hpull.trans ?_
  have hu := isoWhiskerLeft_symm_trans_rightUnitor_inv_app
    ((smallEtaleAbelianSheafComparisonEquiv B S hS X).inverse ⋙
      (spacesBaseChange B S hS f).functor.sheafPullback AddCommGrpCat.{u + 1}
        (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y))
    (smallEtaleAbelianSheafComparisonEquiv B S hS Y).unitIso G
  exact congrArg (fun k => _ ≫ _ ≫ (spacesEtaleSitePoint y).sheafFiber.map k ≫ _) hu

/-- The counit of the conjugated adjunction `f^{-1} ⊣ f_*`, written out: the spaces-étale
counit, framed by the unit of the target comparison equivalence and the counit of the source
one. -/
theorem smallEtaleAbelianGeneralAdjunction_counit_app (f : Y ⟶ X)
    (F : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1}) :
    (smallEtaleAbelianGeneralAdjunction B S hS f).counit.app F =
      (smallEtaleAbelianSheafComparisonEquiv B S hS Y).functor.map
          (((spacesBaseChange B S hS f).functor.sheafPullback AddCommGrpCat.{u + 1}
              (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)).map
              ((smallEtaleAbelianSheafComparisonEquiv B S hS X).unitInv.app
                (((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous
                  AddCommGrpCat.{u + 1} (SpacesEtale.topology B S hS X)
                  (SpacesEtale.topology B S hS Y)).obj
                  ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).inverse.obj F))) ≫
            ((spacesBaseChange B S hS f).functor.sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
              (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)).counit.app
              ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).inverse.obj F)) ≫
        (smallEtaleAbelianSheafComparisonEquiv B S hS Y).counit.app F := by
  simp [smallEtaleAbelianGeneralAdjunction, Adjunction.comp_counit_app]
  rfl

/-- **The counit of `f^{-1} ⊣ f_*` on sections.** On sections over an étale chart `W` of `Y`
mapping by `h` to the base change of a chart `U` of `X`, the composite of the inverse counit of
the target comparison, the unit of the spaces-étale inverse-image adjunction, the unit of the
source comparison, restriction along `h`, the counit of the source comparison and the counit of
`f^{-1} ⊣ f_*` is restriction along `h` followed by the counit of the source comparison. -/
theorem smallEtaleAbelianGeneralAdjunction_counit_section (f : Y ⟶ X)
    (F : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1})
    (U : SmallEtale B S hS X.1) (W : SmallEtale B S hS Y.1)
    (h : (comparisonFunctor B S hS Y).obj W ⟶
      (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS X).obj U)) :
    ((smallEtaleAbelianSheafComparisonEquiv B S hS X).counitInv.app
          ((smallEtaleAbelianDirectImage B S hS f).obj F)).hom.app (op U) ≫
      (((spacesBaseChange B S hS f).functor.sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
          (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)).unit.app
          ((smallEtaleAbelianSheafComparisonEquiv B S hS X).inverse.obj
            ((smallEtaleAbelianDirectImage B S hS f).obj F))).hom.app
          (op ((comparisonFunctor B S hS X).obj U)) ≫
      ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).unit.app
          (((spacesBaseChange B S hS f).functor.sheafPullback AddCommGrpCat.{u + 1}
            (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)).obj
            ((smallEtaleAbelianSheafComparisonEquiv B S hS X).inverse.obj
              ((smallEtaleAbelianDirectImage B S hS f).obj F)))).hom.app
          (op ((spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS X).obj U))) ≫
      ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).inverse.obj
          ((smallEtaleAbelianGeneralInverseImage B S hS f).obj
            ((smallEtaleAbelianDirectImage B S hS f).obj F))).obj.map h.op ≫
      ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).counit.app
          ((smallEtaleAbelianGeneralInverseImage B S hS f).obj
            ((smallEtaleAbelianDirectImage B S hS f).obj F))).hom.app (op W) ≫
      ((smallEtaleAbelianGeneralAdjunction B S hS f).counit.app F).hom.app (op W) =
    ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).inverse.obj F).obj.map h.op ≫
      ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).counitIso.hom.app F).hom.app (op W) := by
  let esrc := smallEtaleAbelianSheafComparisonEquiv B S hS Y
  let etgt := smallEtaleAbelianSheafComparisonEquiv B S hS X
  let g := (spacesBaseChange B S hS f).functor
  let adj := g.sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)
  let gPull := g.sheafPullback AddCommGrpCat.{u + 1}
    (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)
  let gPush := g.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)
  let H := esrc.inverse.obj F
  let K := gPush.obj H
  let N := gPull.obj (etgt.inverse.obj (etgt.functor.obj K))
  let Ξ : N ⟶ H := gPull.map (etgt.unitInv.app K) ≫ adj.counit.app H
  let cW := (comparisonFunctor B S hS Y).obj W
  let cU := (comparisonFunctor B S hS X).obj U
  have h₁ := ((esrc.unit.app N).hom.naturality h.op).symm
  have h₂ : (esrc.unit.app N).hom.app (op cW) ≫
      (esrc.counit.app (esrc.functor.obj N)).hom.app (op W) = 𝟙 _ :=
    congrArg (fun φ => φ.hom.app (op W)) (esrc.functor_unit_comp N)
  have h₃ : ((smallEtaleAbelianGeneralAdjunction B S hS f).counit.app F).hom.app (op W) =
      Ξ.hom.app (op cW) ≫ (esrc.counit.app F).hom.app (op W) := by
    rw [smallEtaleAbelianGeneralAdjunction_counit_app]
    rfl
  have h₄ := Ξ.hom.naturality h.op
  have h₅a : (adj.unit.app (etgt.inverse.obj (etgt.functor.obj K))).hom.app (op cU) ≫
      Ξ.hom.app (op (g.obj cU)) = (etgt.unitInv.app K).hom.app (op cU) :=
    congrArg (fun φ => φ.hom.app (op cU))
      (unit_app_comp_map_map_comp_counit adj (etgt.unitInv.app K))
  have h₅b : (etgt.counitInv.app (etgt.functor.obj K)).hom.app (op U) ≫
      (etgt.unitInv.app K).hom.app (op cU) = 𝟙 _ :=
    congrArg (fun φ => φ.hom.app (op U)) (etgt.counitInv_functor_comp K)
  have h₅ : (etgt.counitInv.app (etgt.functor.obj K)).hom.app (op U) ≫
      (adj.unit.app (etgt.inverse.obj (etgt.functor.obj K))).hom.app (op cU) ≫
      Ξ.hom.app (op (g.obj cU)) = 𝟙 _ :=
    (whisker_eq _ h₅a).trans h₅b
  exact comp_six_eq_of_triangles _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅

/-- **The germ formula for the fibre part of the stalk comparison of a direct image.** -/
theorem smallEtaleAbelianGeneralInverseImageFiberIso_inv_counit_germ (f : Y ⟶ X)
    (y : GeometricPoint B S hS Y.1)
    (F : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1})
    (U : SmallEtale B S hS X.1)
    (u : (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).fiber.obj U)
    (W : SmallEtale B S hS Y.1) (w : (etaleSitePoint B S hS Y.1 y Y.2).fiber.obj W)
    (h : (comparisonFunctor B S hS Y).obj W ⟶
      (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS X).obj U))
    (hw : (spacesEtaleSitePoint y).fiber.map h w =
      (spacesBaseChangeFiberIso B S hS f y).inv.app ((comparisonFunctor B S hS X).obj U) u) :
    (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).toPresheafFiber U u
        ((smallEtaleAbelianDirectImage B S hS f).obj F).obj ≫
      (smallEtaleAbelianGeneralInverseImageFiberIso B S hS f y).inv.app
        ((smallEtaleAbelianDirectImage B S hS f).obj F) ≫
      (etaleSitePoint B S hS Y.1 y Y.2).sheafFiber.map
        ((smallEtaleAbelianGeneralAdjunction B S hS f).counit.app F) =
    (((smallEtaleAbelianSheafComparisonEquiv B S hS Y).inverse.obj F).obj.map h.op ≫
      ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).counitIso.hom.app F).hom.app (op W)) ≫
      (etaleSitePoint B S hS Y.1 y Y.2).toPresheafFiber W w F.obj := by
  let esrc := smallEtaleAbelianSheafComparisonEquiv B S hS Y
  let etgt := smallEtaleAbelianSheafComparisonEquiv B S hS X
  let g := (spacesBaseChange B S hS f).functor
  let gPull := g.sheafPullback AddCommGrpCat.{u + 1}
    (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)
  let Psrc := spacesEtaleSitePoint y
  let efib := spacesBaseChangeFiberIso B S hS f y
  let G := (smallEtaleAbelianDirectImage B S hS f).obj F
  let M := etgt.inverse.obj G
  let N := gPull.obj M
  let cU := (comparisonFunctor B S hS X).obj U
  let cW := (comparisonFunctor B S hS Y).obj W
  have hu : u = efib.hom.app cU (Psrc.fiber.map h w) := by
    rw [hw]
    exact (Iso.inv_hom_id_app_apply efib cU u).symm
  subst hu
  rw [smallEtaleAbelianGeneralInverseImageFiberIso_inv_app]
  have hA := smallEtaleAbelianSheafFiberSpacesIso_hom_germ B S hS X (geometricPointMap f.hom y)
    G U (efib.hom.app cU (Psrc.fiber.map h w))
  have hB := spacesBaseChangeSheafFiberIso_inv_germ B S hS f y M cU (Psrc.fiber.map h w)
  have hCD : Psrc.toPresheafFiber (g.obj cU) (Psrc.fiber.map h w) N.obj ≫
      Psrc.sheafFiber.map (esrc.unit.app N) =
      ((esrc.unit.app N).hom.app (op (g.obj cU)) ≫
        (esrc.inverse.obj (esrc.functor.obj N)).obj.map h.op) ≫
        Psrc.toPresheafFiber cW w (esrc.inverse.obj (esrc.functor.obj N)).obj :=
    (Psrc.toPresheafFiber_naturality (esrc.unit.app N).hom (g.obj cU) (Psrc.fiber.map h w)).trans
      ((whisker_eq _
        (Psrc.toPresheafFiber_w h w (esrc.inverse.obj (esrc.functor.obj N)).obj).symm).trans
        (Category.assoc _ _ _).symm)
  have hE := smallEtaleAbelianSheafFiberSpacesIso_inv_germ B S hS Y y
    ((smallEtaleAbelianGeneralInverseImage B S hS f).obj G) W w
  have hF := GrothendieckTopology.Point.toSheafFiber_naturality (etaleSitePoint B S hS Y.1 y Y.2)
    ((smallEtaleAbelianGeneralAdjunction B S hS f).counit.app F) W w
  exact germ_chase_five hA hB hCD hE hF
    (smallEtaleAbelianGeneralAdjunction_counit_section B S hS f F U W h)

/-- **The germ formula for the stalk comparison of a direct image along an arbitrary morphism of
algebraic spaces.** Let `u` be a lift of `x̄ = f(ȳ)` into an étale chart `U` of `X`, `w` a lift of
`ȳ` into an étale chart `W` of `Y`, and `h` a map from (the space of) `W` to the base change
`U ×_X Y` carrying `w` to the lift of `ȳ` that the cartesian square of Stacks 03G2 part (1)
assigns to `u`. A section of `f_*F` over `U` is a section of the spaces-étale extension of `F`
over `U ×_X Y`; the comparison `(f_*F)_{x̄} ⟶ F_ȳ` sends its germ at `u` to the germ at `w` of
its restriction along `h`, read on `W` through the counit of the comparison equivalence of
Stacks 03G1. -/
theorem smallEtaleAbelianDirectImageStalkMap_germ (f : Y ⟶ X)
    (y : GeometricPoint B S hS Y.1)
    (F : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1})
    (U : SmallEtale B S hS X.1)
    (u : (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).fiber.obj U)
    (W : SmallEtale B S hS Y.1) (w : (etaleSitePoint B S hS Y.1 y Y.2).fiber.obj W)
    (h : (comparisonFunctor B S hS Y).obj W ⟶
      (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS X).obj U))
    (hw : (spacesEtaleSitePoint y).fiber.map h w =
      (spacesBaseChangeFiberIso B S hS f y).inv.app ((comparisonFunctor B S hS X).obj U) u) :
    (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).toPresheafFiber U u
        ((smallEtaleAbelianDirectImage B S hS f).obj F).obj ≫
      (etaleSitePointStalkFunctorIso B S hS X.1 (geometricPointMap f.hom y) X.2).hom.app
        ((smallEtaleAbelianDirectImage B S hS f).obj F).obj ≫
      (smallEtaleAbelianDirectImageStalkMap B S hS f y).app F =
    ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).inverse.obj F).obj.map h.op ≫
      ((smallEtaleAbelianSheafComparisonEquiv B S hS Y).counitIso.hom.app F).hom.app (op W) ≫
      (etaleSitePoint B S hS Y.1 y Y.2).toPresheafFiber W w F.obj ≫
      (etaleSitePointStalkFunctorIso B S hS Y.1 y Y.2).hom.app F.obj := by
  rw [smallEtaleAbelianDirectImageStalkMap_app, smallEtaleAbelianGeneralInverseImageStalkIso_eq]
  exact comp_iso_frame_eq _
    ((etaleSitePointStalkFunctorIso B S hS X.1 (geometricPointMap f.hom y) X.2).app
      ((smallEtaleAbelianDirectImage B S hS f).obj F).obj) _ _ _ _ _ _ _ _ _
    (isoWhiskerLeft_frame_inv_app (smallEtaleAbelianGeneralInverseImage B S hS f)
      (sheafToPresheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1})
      (sheafToPresheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1})
      (etaleSitePointStalkFunctorIso B S hS Y.1 y Y.2)
      (smallEtaleAbelianGeneralInverseImageFiberIso B S hS f y)
      (etaleSitePointStalkFunctorIso B S hS X.1 (geometricPointMap f.hom y) X.2)
      ((smallEtaleAbelianDirectImage B S hS f).obj F))
    ((etaleSitePointStalkFunctorIso B S hS Y.1 y Y.2).hom.naturality
      ((smallEtaleAbelianGeneralAdjunction B S hS f).counit.app F).hom)
    (smallEtaleAbelianGeneralInverseImageFiberIso_inv_counit_germ B S hS f y F U u W w h hw)

end AlgebraicGeometry.Space

end
