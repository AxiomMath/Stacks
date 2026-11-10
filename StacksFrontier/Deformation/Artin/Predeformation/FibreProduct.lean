module

public import StacksCore.CategoryTheory.FiberedInGroupoids
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase
public import StacksFrontier.Deformation.Artin.Predeformation

/-!
# Predeformation categories of a 2-fibre product

Let `𝒲` be a 2-fibre product of `𝒳 ⟶ 𝒴` and `𝒵 ⟶ 𝒴` in categories fibred in groupoids over
schemes over a base `S`, and let `w₀` be an object of `𝒲` lying over `Spec k`. Write `x₀` and
`z₀` for the images of `w₀` in `𝒳` and `𝒵`, and `y₀` for its image in `𝒴`. Then the square

    𝓕_{𝒲,k,w₀} ⟶ 𝓕_{𝒵,k,z₀}
        ↓              ↓
    𝓕_{𝒳,k,x₀} ⟶ 𝓕_{𝒴,k,y₀}

of predeformation categories is again a 2-fibre product, this time in the `(2,1)`-category of
categories over `𝒞_Λ`.

## Main definitions

* `Deformation.Artin.PredeformationFibreProductData` is the right-hand arrow of the square
  together with its characterisation, the 2-cell filling the square, and the assertion that the
  square is a 2-fibre product.

## Main results

* `Deformation.Artin.fibreProductOfPredeformationCategories`: the square of predeformation
  categories of a 2-fibre product is a 2-fibre product.

## Implementation notes

The two routes from `𝒲` to `𝒴` agree only up to the comparison isomorphism
`ψ(w₀) : F(x₀) ≅ G(z₀)`, so `y₀` is taken to be `F(x₀)` and the right-hand arrow of the square is
the functor induced by `G` transported along `ψ(w₀)`: on a deformation object `z₀ ⟶ z` it is
`y₀ ⟶ G(z₀) ⟶ G(z)`, the first arrow being `ψ(w₀)`.

The square commutes up to the canonical 2-cell: its component at a deformation object has
underlying arrow of `𝒴` the comparison isomorphism `ψ` at the underlying object of `𝒲`.

Being a 2-fibre product is phrased, for the hypothesis and the conclusion alike, as "the mediating
functor into `CategoryTheory.TwoFibreProductOver` is an equivalence".

## References

* [Stacks Project, Tag 07WL](https://stacks.math.columbia.edu/tag/07WL)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

attribute [local implicit_reducible] TwoFibreProductOver.lift
  TwoFibreProductOver.structureFunctor TwoFibreProductOver.fst TwoFibreProductOver.snd

namespace Deformation.Artin

attribute [local implicit_reducible] predeformationCategory mapPredeformationCategory

universe u v v₁ v₂ v₃ v₄ w w₁ w₂ w₃ w₄

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {S : Scheme.{u}}
variable {W : Type v₁} [Category.{w₁} W] {X : Type v₂} [Category.{w₂} X]
variable {Z : Type v₃} [Category.{w₃} Z] {Y : Type v₄} [Category.{w₄} Y]

/-- The category structure carried by a predeformation-category construction. -/
local instance instCategoryPredeformationConstructionCarrier {X' : Type v} [Category.{w} X']
    (iΛ : Spec (.of Λ) ⟶ S) (q : X' ⥤ Over S) (x₀ : X')
    (hx₀ : q.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (P : PredeformationConstruction iΛ q x₀ hx₀) : Category.{max u w} P.carrier :=
  P.category

variable (iΛ : Spec (.of Λ) ⟶ S)
variable (qW : W ⥤ Over S) (qX : X ⥤ Over S) (qZ : Z ⥤ Over S) (qY : Y ⥤ Over S)
variable (A : W ⥤ X) (B : W ⥤ Z) (F : X ⥤ Y) (G : Z ⥤ Y)
variable (hA : A ⋙ qX = qW) (hB : B ⋙ qZ = qW) (hF : F ⋙ qY = qX)
variable (ψ : A ⋙ F ≅ B ⋙ G) (w₀ : W)
variable (hw₀ : qW.obj w₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

/-- A vertical isomorphism of distinguished points is the canonical identification of the two
base points: it lies over the identity, so the functor sends it to an `eqToHom`. -/
private theorem map_hom_eq_eqToHom {X' : Type v} [Category.{w} X'] (q : X' ⥤ Over S)
    {x₀ x₁ : X'} (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₁ : q.obj x₁ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (i : x₀ ≅ x₁) (hi : q.IsHomLift (𝟙 (q.obj x₀)) i.hom) :
    q.map i.hom = eqToHom (hx₀.trans hx₁.symm) := by
  have h := IsHomLift.fac' q (𝟙 (q.obj x₀)) i.hom
  have hd : IsHomLift.domain_eq q (𝟙 (q.obj x₀)) i.hom = rfl := Subsingleton.elim _ _
  have hc : IsHomLift.codomain_eq q (𝟙 (q.obj x₀)) i.hom = hx₁.trans hx₀.symm :=
    Subsingleton.elim _ _
  rw [hd, hc] at h
  simpa using h

/-- Rebase a deformation along an isomorphism of its distinguished point that is vertical over
the scheme base. The algebra and the deformed object are unchanged; only the arrow from the
distinguished point is precomposed with the isomorphism. -/
private def rebaseDeformationObject
    {X' : Type v} [Category.{w} X'] (q : X' ⥤ Over S)
    {x₀ x₁ : X'} (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₁ : q.obj x₁ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (i : x₀ ≅ x₁) (hi : q.IsHomLift (𝟙 (q.obj x₀)) i.hom)
    (d : DeformationObject iΛ q x₁ hx₁) :
    DeformationObject iΛ q x₀ hx₀ where
  algebra := d.algebra
  point := d.point
  arrow := i.hom ≫ d.arrow
  base := d.base
  arrow_base := by
    rw [Functor.map_comp, map_hom_eq_eqToHom iΛ q hx₀ hx₁ i hi, Over.comp_left]
    simpa [Category.assoc, Over.eqToHom_left, eqToHom_trans] using d.arrow_base

@[simp]
private theorem rebaseDeformationObject_algebra {X' : Type v} [Category.{w} X']
    (q : X' ⥤ Over S) {x₀ x₁ : X'} (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₁ : q.obj x₁ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (i : x₀ ≅ x₁) (hi : q.IsHomLift (𝟙 (q.obj x₀)) i.hom)
    (d : DeformationObject iΛ q x₁ hx₁) :
    (rebaseDeformationObject iΛ q hx₀ hx₁ i hi d).algebra = d.algebra := rfl

@[simp]
private theorem rebaseDeformationObject_point {X' : Type v} [Category.{w} X']
    (q : X' ⥤ Over S) {x₀ x₁ : X'} (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₁ : q.obj x₁ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (i : x₀ ≅ x₁) (hi : q.IsHomLift (𝟙 (q.obj x₀)) i.hom)
    (d : DeformationObject iΛ q x₁ hx₁) :
    (rebaseDeformationObject iΛ q hx₀ hx₁ i hi d).point = d.point := rfl

@[simp]
private theorem rebaseDeformationObject_arrow {X' : Type v} [Category.{w} X']
    (q : X' ⥤ Over S) {x₀ x₁ : X'} (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₁ : q.obj x₁ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (i : x₀ ≅ x₁) (hi : q.IsHomLift (𝟙 (q.obj x₀)) i.hom)
    (d : DeformationObject iΛ q x₁ hx₁) :
    (rebaseDeformationObject iΛ q hx₀ hx₁ i hi d).arrow = i.hom ≫ d.arrow := rfl

/-- A reversed deformation arrow is unchanged when both distinguished points are rebased along
the same vertical isomorphism. -/
private def rebaseDeformationMorphism
    {X' : Type v} [Category.{w} X'] (q : X' ⥤ Over S)
    {x₀ x₁ : X'} (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₁ : q.obj x₁ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (i : x₀ ≅ x₁) (hi : q.IsHomLift (𝟙 (q.obj x₀)) i.hom)
    {a b : DeformationObject iΛ q x₁ hx₁}
    (m : DeformationMorphism iΛ q x₁ hx₁ a b) :
    DeformationMorphism iΛ q x₀ hx₀
      (rebaseDeformationObject iΛ q hx₀ hx₁ i hi a)
      (rebaseDeformationObject iΛ q hx₀ hx₁ i hi b) where
  ringHom := m.ringHom
  arrow := m.arrow
  triangle := by
    change (i.hom ≫ b.arrow) ≫ m.arrow = i.hom ≫ a.arrow
    rw [Category.assoc, m.triangle]
  arrow_base := m.arrow_base

@[simp]
private theorem rebaseDeformationMorphism_ringHom {X' : Type v} [Category.{w} X']
    (q : X' ⥤ Over S) {x₀ x₁ : X'} (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₁ : q.obj x₁ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (i : x₀ ≅ x₁) (hi : q.IsHomLift (𝟙 (q.obj x₀)) i.hom)
    {a b : DeformationObject iΛ q x₁ hx₁}
    (m : DeformationMorphism iΛ q x₁ hx₁ a b) :
    (rebaseDeformationMorphism iΛ q hx₀ hx₁ i hi m).ringHom = m.ringHom := rfl

@[simp]
private theorem rebaseDeformationMorphism_arrow {X' : Type v} [Category.{w} X']
    (q : X' ⥤ Over S) {x₀ x₁ : X'} (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hx₁ : q.obj x₁ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (i : x₀ ≅ x₁) (hi : q.IsHomLift (𝟙 (q.obj x₀)) i.hom)
    {a b : DeformationObject iΛ q x₁ hx₁}
    (m : DeformationMorphism iΛ q x₁ hx₁ a b) :
    (rebaseDeformationMorphism iΛ q hx₀ hx₁ i hi m).arrow = m.arrow := rfl

/-- The arrow of a deformation object determines that of any object equal to it. -/
private theorem deformationObject_arrow_eq
    {X' : Type v} [Category.{w} X'] {q : X' ⥤ Over S} {x₀ : X'}
    {h : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a b : DeformationObject iΛ q x₀ h} (hab : a = b) :
    a.arrow = b.arrow ≫ eqToHom (congrArg DeformationObject.point hab).symm := by
  cases hab
  simp

/-- The projection of a predeformation category reads off the arrow of `𝒞_Λ` underlying a
morphism of deformations, up to the identifications of the projected objects. -/
private theorem deformationHom_projection
    {X' : Type v} [Category.{w} X'] {q : X' ⥤ Over S} {x₀ : X'}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (P : PredeformationConstruction iΛ q x₀ hx₀)
    {a b : P.carrier} (f : a ⟶ b) :
    P.projection.map f = eqToHom (P.object_projection a) ≫
      (P.morphisms a b f).ringHom ≫ eqToHom (P.object_projection b).symm := by
  rw [← P.morphism_projection]
  simp

section Rebase

variable {X' : Type v} [Category.{w} X'] (q : X' ⥤ Over S)
variable {x₀ x₁ : X'}
variable (hx₀ : q.obj x₀ = Over.mk
  (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
variable (hx₁ : q.obj x₁ = Over.mk
  (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
variable (i : x₀ ≅ x₁) (hi : q.IsHomLift (𝟙 (q.obj x₀)) i.hom)
variable (P₀ : PredeformationConstruction iΛ q x₀ hx₀)
variable (P₁ : PredeformationConstruction iΛ q x₁ hx₁)

/-- The object of the rebased predeformation category corresponding to a deformation of the
other distinguished point. -/
private def rebaseObj (a : P₁.carrier) : P₀.carrier :=
  P₀.objects.symm (rebaseDeformationObject iΛ q hx₀ hx₁ i hi (P₁.objects a))

private theorem rebaseObj_spec (a : P₁.carrier) :
    P₀.objects (rebaseObj iΛ q hx₀ hx₁ i hi P₀ P₁ a) =
      rebaseDeformationObject iΛ q hx₀ hx₁ i hi (P₁.objects a) :=
  P₀.objects.apply_symm_apply _

private theorem rebaseObj_algebra (a : P₁.carrier) :
    (P₀.objects (rebaseObj iΛ q hx₀ hx₁ i hi P₀ P₁ a)).algebra = (P₁.objects a).algebra :=
  congrArg DeformationObject.algebra (rebaseObj_spec iΛ q hx₀ hx₁ i hi P₀ P₁ a)

private theorem rebaseObj_point (a : P₁.carrier) :
    (P₀.objects (rebaseObj iΛ q hx₀ hx₁ i hi P₀ P₁ a)).point = (P₁.objects a).point :=
  congrArg DeformationObject.point (rebaseObj_spec iΛ q hx₀ hx₁ i hi P₀ P₁ a)

private theorem rebaseObj_arrow (a : P₁.carrier) :
    (P₀.objects (rebaseObj iΛ q hx₀ hx₁ i hi P₀ P₁ a)).arrow =
      i.hom ≫ (P₁.objects a).arrow ≫
        eqToHom (rebaseObj_point iΛ q hx₀ hx₁ i hi P₀ P₁ a).symm := by
  refine (deformationObject_arrow_eq iΛ (rebaseObj_spec iΛ q hx₀ hx₁ i hi P₀ P₁ a)).trans ?_
  exact Category.assoc _ _ _

/-- The morphism of deformations of `x₀` attached to a morphism of deformations of `x₁`. -/
private def rebaseMorphismData {a b : P₁.carrier} (f : a ⟶ b) :
    DeformationMorphism iΛ q x₀ hx₀
      (P₀.objects (rebaseObj iΛ q hx₀ hx₁ i hi P₀ P₁ a))
      (P₀.objects (rebaseObj iΛ q hx₀ hx₁ i hi P₀ P₁ b)) :=
  transportDeformationMorphism (rebaseObj_spec iΛ q hx₀ hx₁ i hi P₀ P₁ a)
    (rebaseObj_spec iΛ q hx₀ hx₁ i hi P₀ P₁ b)
    (rebaseDeformationMorphism iΛ q hx₀ hx₁ i hi (P₁.morphisms a b f))

private theorem rebaseMorphismData_ringHom {a b : P₁.carrier} (f : a ⟶ b) :
    (rebaseMorphismData iΛ q hx₀ hx₁ i hi P₀ P₁ f).ringHom =
      eqToHom (rebaseObj_algebra iΛ q hx₀ hx₁ i hi P₀ P₁ a) ≫
        (P₁.morphisms a b f).ringHom ≫
          eqToHom (rebaseObj_algebra iΛ q hx₀ hx₁ i hi P₀ P₁ b).symm := rfl

private theorem rebaseMorphismData_arrow {a b : P₁.carrier} (f : a ⟶ b) :
    (rebaseMorphismData iΛ q hx₀ hx₁ i hi P₀ P₁ f).arrow =
      eqToHom (rebaseObj_point iΛ q hx₀ hx₁ i hi P₀ P₁ b) ≫
        (P₁.morphisms a b f).arrow ≫
          eqToHom (rebaseObj_point iΛ q hx₀ hx₁ i hi P₀ P₁ a).symm := rfl

/-- The arrow of `𝒞_Λ` underlying an identity of a predeformation category is an identity. -/
private theorem morphisms_id_ringHom (a : P₁.carrier) :
    (P₁.morphisms a a (𝟙 a)).ringHom = 𝟙 (P₁.objects a).algebra := by
  simpa using (P₁.morphism_projection (f := 𝟙 a)).symm

/-- The arrow of `𝒞_Λ` underlying a composite is the composite of the two arrows. -/
private theorem morphisms_comp_ringHom {a b c : P₁.carrier} (f : a ⟶ b) (g : b ⟶ c) :
    (P₁.morphisms a c (f ≫ g)).ringHom =
      (P₁.morphisms a b f).ringHom ≫ (P₁.morphisms b c g).ringHom := by
  have h := P₁.morphism_projection (f := f ≫ g)
  have hf := P₁.morphism_projection (f := f)
  have hg := P₁.morphism_projection (f := g)
  simp only [Functor.map_comp] at h
  rw [← h, ← hf, ← hg]
  simp [Category.assoc]

/-- Changing the distinguished point along a vertical isomorphism induces a functor of
predeformation categories. -/
private def rebasePredeformationCategory : P₁.carrier ⥤ P₀.carrier where
  obj := rebaseObj iΛ q hx₀ hx₁ i hi P₀ P₁
  map f := (P₀.morphisms _ _).symm (rebaseMorphismData iΛ q hx₀ hx₁ i hi P₀ P₁ f)
  map_id a := by
    apply (P₀.morphisms _ _).injective
    refine DeformationMorphism.ext_of_components _ _ _ _ ?_ ?_
    · rw [Equiv.apply_symm_apply, rebaseMorphismData_ringHom,
        morphisms_id_ringHom, morphisms_id_ringHom]
      simp
    · rw [Equiv.apply_symm_apply, rebaseMorphismData_arrow,
        P₁.reversed_identity, P₀.reversed_identity]
      simp
  map_comp {a b c} f g := by
    apply (P₀.morphisms _ _).injective
    refine DeformationMorphism.ext_of_components _ _ _ _ ?_ ?_
    · rw [Equiv.apply_symm_apply, rebaseMorphismData_ringHom,
        morphisms_comp_ringHom, morphisms_comp_ringHom, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply, rebaseMorphismData_ringHom, rebaseMorphismData_ringHom]
      simp [Category.assoc]
    · rw [Equiv.apply_symm_apply, rebaseMorphismData_arrow,
        P₁.reversed_composition, P₀.reversed_composition, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply, rebaseMorphismData_arrow, rebaseMorphismData_arrow]
      simp [Category.assoc]

@[simp]
private theorem rebasePredeformationCategory_obj (a : P₁.carrier) :
    (rebasePredeformationCategory iΛ q hx₀ hx₁ i hi P₀ P₁).obj a =
      rebaseObj iΛ q hx₀ hx₁ i hi P₀ P₁ a := rfl

private theorem rebasePredeformationCategory_morphisms_map {a b : P₁.carrier} (f : a ⟶ b) :
    P₀.morphisms _ _ ((rebasePredeformationCategory iΛ q hx₀ hx₁ i hi P₀ P₁).map f) =
      rebaseMorphismData iΛ q hx₀ hx₁ i hi P₀ P₁ f :=
  (P₀.morphisms _ _).apply_symm_apply _

/-- The rebasing functor is a morphism of categories over `𝒞_Λ`. -/
private theorem rebasePredeformation_projection_comm :
    rebasePredeformationCategory iΛ q hx₀ hx₁ i hi P₀ P₁ ⋙ P₀.projection =
      P₁.projection := by
  have hobj (a : P₁.carrier) :
      (rebasePredeformationCategory iΛ q hx₀ hx₁ i hi P₀ P₁ ⋙ P₀.projection).obj a =
        P₁.projection.obj a :=
    (P₀.object_projection _).trans
      ((rebaseObj_algebra iΛ q hx₀ hx₁ i hi P₀ P₁ a).trans
        (P₁.object_projection a).symm)
  refine CategoryTheory.Functor.hext hobj ?_
  intro a b f
  change P₀.projection.map ((rebasePredeformationCategory iΛ q hx₀ hx₁ i hi P₀ P₁).map f) ≍ _
  rw [deformationHom_projection iΛ P₀, deformationHom_projection iΛ P₁,
    rebasePredeformationCategory_morphisms_map, rebaseMorphismData_ringHom]
  refine HEq.trans (eqToHom_comp_heq _ _) ?_
  refine HEq.trans (comp_eqToHom_heq _ _) ?_
  refine HEq.trans (eqToHom_comp_heq _ _) ?_
  refine HEq.trans (comp_eqToHom_heq _ _) ?_
  refine HEq.symm ?_
  refine HEq.trans (eqToHom_comp_heq _ _) ?_
  exact comp_eqToHom_heq _ _

/-- The rebasing functor does not change the deformed object. -/
private theorem rebasePredeformation_object_point (a : P₁.carrier) :
    (P₀.objects ((rebasePredeformationCategory iΛ q hx₀ hx₁ i hi P₀ P₁).obj a)).point =
      (P₁.objects a).point :=
  rebaseObj_point iΛ q hx₀ hx₁ i hi P₀ P₁ a

/-- The rebasing functor precomposes the arrow from the distinguished point with the chosen
vertical isomorphism. -/
private theorem rebasePredeformation_object_arrow (a : P₁.carrier) :
    (P₀.objects ((rebasePredeformationCategory iΛ q hx₀ hx₁ i hi P₀ P₁).obj a)).arrow =
      i.hom ≫ (P₁.objects a).arrow ≫
        eqToHom (rebasePredeformation_object_point iΛ q hx₀ hx₁ i hi P₀ P₁ a).symm :=
  rebaseObj_arrow iΛ q hx₀ hx₁ i hi P₀ P₁ a

/-- The rebasing functor does not change the reversed arrow of a morphism of deformations. -/
private theorem rebasePredeformation_morphism_arrow {a b : P₁.carrier} (f : a ⟶ b) :
    (P₀.morphisms
      ((rebasePredeformationCategory iΛ q hx₀ hx₁ i hi P₀ P₁).obj a)
      ((rebasePredeformationCategory iΛ q hx₀ hx₁ i hi P₀ P₁).obj b)
      ((rebasePredeformationCategory iΛ q hx₀ hx₁ i hi P₀ P₁).map f)).arrow =
      eqToHom (rebasePredeformation_object_point iΛ q hx₀ hx₁ i hi P₀ P₁ b) ≫
        (P₁.morphisms a b f).arrow ≫
          eqToHom (rebasePredeformation_object_point iΛ q hx₀ hx₁ i hi P₀ P₁ a).symm := by
  rw [rebasePredeformationCategory_morphisms_map, rebaseMorphismData_arrow]
  rfl

end Rebase

/-- The functor sending an object of `𝒞_Λ` to the `S`-scheme `Spec` of it, contravariantly.
A deformation of `x₀` over `A` lies over `artinianSpec.obj (op A)`. -/
private def artinianSpec :
    (ArtinianLocalAlgCat.{u, u, u} Λ k)ᵒᵖ ⥤ Over S where
  obj R := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ R.unop)) ≫ iΛ)
  map f := Over.homMk (Spec.map (CommRingCat.ofHom f.unop.hom.toRingHom)) (by
    dsimp
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    exact CommRingCat.hom_ext (RingHom.ext (fun x => f.unop.hom.commutes x)))
  map_id R := by
    apply Over.OverMorphism.ext
    simp [← Spec.map_id]
  map_comp f g := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom g.unop.hom.toRingHom ≫
      CommRingCat.ofHom f.unop.hom.toRingHom) = _
    exact Spec.map_comp _ _

attribute [local implicit_reducible] artinianSpec

private theorem artinianSpec_map_left
    {R T : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : R ⟶ T) :
    ((artinianSpec (k := k) iΛ).map f.op).left =
      Spec.map (CommRingCat.ofHom f.hom.toRingHom) := rfl

private theorem deformationBase
    {X' : Type v} [Category.{w} X'] {q : X' ⥤ Over S} {x₀ : X'}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (P : PredeformationConstruction iΛ q x₀ hx₀) (c : P.carrier) :
    q.obj (P.objects c).point = (artinianSpec iΛ).obj (Opposite.op (P.projection.obj c)) :=
  (P.objects c).base.trans (congrArg (fun R =>
    (artinianSpec iΛ).obj (Opposite.op R)) (P.object_projection c).symm)

private theorem deformationMap_base
    {X' : Type v} [Category.{w} X'] {q : X' ⥤ Over S} {x₀ : X'}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (P : PredeformationConstruction iΛ q x₀ hx₀)
    {c d : P.carrier} (f : c ⟶ d) :
    q.map (P.morphisms c d f).arrow =
      eqToHom (deformationBase iΛ P d) ≫ (artinianSpec iΛ).map (P.projection.map f).op ≫
        eqToHom (deformationBase iΛ P c).symm := by
  have hm := (P.morphisms c d f).arrow_base
  have h : q.map (P.morphisms c d f).arrow =
      eqToHom (P.objects d).base ≫
        (artinianSpec iΛ).map (P.morphisms c d f).ringHom.op ≫
          eqToHom (P.objects c).base.symm := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.eqToHom_left, artinianSpec_map_left]
    rw [← hm]
    simp
  rw [h, ← P.morphism_projection]
  simp [Category.assoc, CategoryTheory.Functor.map_comp,
    eqToHom_map, eqToHom_op]

private def residueArrow (R : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ⟶
      (artinianSpec iΛ).obj (Opposite.op R) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (residueMap R))) (by
    dsimp [artinianSpec]
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    exact RingHom.ext (fun x => R.residueEquiv.commutes x))

private theorem deformationArrow_base
    {X' : Type v} [Category.{w} X'] {q : X' ⥤ Over S} {x₀ : X'}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (P : PredeformationConstruction iΛ q x₀ hx₀) (c : P.carrier)
    {R : ArtinianLocalAlgCat.{u, u, u} Λ k} (hr : P.projection.obj c = R) :
    q.map (P.objects c).arrow = eqToHom hx₀ ≫ residueArrow iΛ R ≫
      eqToHom ((deformationBase iΛ P c).trans
        (congrArg (fun R => (artinianSpec iΛ).obj (Opposite.op R)) hr)).symm := by
  have he : (P.objects c).algebra = R := (P.object_projection c).symm.trans hr
  cases he
  apply Over.OverMorphism.ext
  have hm := (P.objects c).arrow_base
  simp only [Over.comp_left, Over.eqToHom_left]
  change _ = eqToHom _ ≫ Spec.map _ ≫ eqToHom _
  rw [← hm]
  simp

private def deformationPointIso
    {X' : Type v} [Category.{w} X'] {q : X' ⥤ Over S} {x₀ : X'}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (P : PredeformationConstruction iΛ q x₀ hx₀)
    {c d : P.carrier} (e : c ≅ d) : (P.objects d).point ≅ (P.objects c).point where
  hom := (P.morphisms c d e.hom).arrow
  inv := (P.morphisms d c e.inv).arrow
  hom_inv_id := by rw [← P.reversed_composition, e.inv_hom_id, P.reversed_identity]
  inv_hom_id := by rw [← P.reversed_composition, e.hom_inv_id, P.reversed_identity]

private theorem deformationHom_ext
    {X' : Type v} [Category.{w} X'] {q : X' ⥤ Over S} {x₀ : X'}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (P : PredeformationConstruction iΛ q x₀ hx₀)
    {a b : P.carrier} {f g : a ⟶ b}
    (hr : P.projection.map f = P.projection.map g)
    (ha : (P.morphisms a b f).arrow = (P.morphisms a b g).arrow) : f = g := by
  apply (P.morphisms a b).injective
  refine DeformationMorphism.ext_of_components _ _ _ _ ?_ ha
  rw [← P.morphism_projection, ← P.morphism_projection, hr]

private theorem deformationHom_isHomLift
    {X' : Type v} [Category.{w} X'] {q : X' ⥤ Over S} {x₀ : X'}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (P : PredeformationConstruction iΛ q x₀ hx₀)
    {c d : P.carrier} (f : c ⟶ d)
    {R T : ArtinianLocalAlgCat.{u, u, u} Λ k} (r : R ⟶ T)
    (hf : P.projection.IsHomLift r f) :
    q.IsHomLift ((artinianSpec iΛ).map r.op) (P.morphisms c d f).arrow := by
  apply IsHomLift.of_fac' q _ _
    ((deformationBase iΛ P d).trans (congrArg (fun T =>
      (artinianSpec iΛ).obj (Opposite.op T)) (IsHomLift.codomain_eq P.projection r f)))
    ((deformationBase iΛ P c).trans (congrArg (fun R =>
      (artinianSpec iΛ).obj (Opposite.op R)) (IsHomLift.domain_eq P.projection r f)))
  rw [deformationMap_base, IsHomLift.fac' P.projection r f]
  simp [Category.assoc, eqToHom_op, eqToHom_map]

private def deformationHomOfBase
    {X' : Type v} [Category.{w} X'] {q : X' ⥤ Over S} {x₀ : X'}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (P : PredeformationConstruction iΛ q x₀ hx₀)
    {c d : P.carrier} (r : P.projection.obj c ⟶ P.projection.obj d)
    (a : (P.objects d).point ⟶ (P.objects c).point)
    (ht : (P.objects d).arrow ≫ a = (P.objects c).arrow)
    (hb : q.map a = eqToHom (deformationBase iΛ P d) ≫
      (artinianSpec iΛ).map r.op ≫ eqToHom (deformationBase iΛ P c).symm) : c ⟶ d := by
  refine (P.morphisms c d).symm ?_
  refine ⟨eqToHom (P.object_projection c).symm ≫ r ≫ eqToHom (P.object_projection d),
    a, ht, ?_⟩
  have hh := congrArg Over.Hom.left hb
  have hr := artinianSpec_map_left iΛ
    (eqToHom (P.object_projection c).symm ≫ r ≫ eqToHom (P.object_projection d))
  rw [← hr]
  simp only [op_comp, CategoryTheory.Functor.map_comp, eqToHom_op, eqToHom_map]
  simp [hh, Over.comp_left, Over.eqToHom_left, Category.assoc]

private theorem deformationHomOfBase_arrow
    {X' : Type v} [Category.{w} X'] {q : X' ⥤ Over S} {x₀ : X'}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (P : PredeformationConstruction iΛ q x₀ hx₀)
    {c d : P.carrier} (r : P.projection.obj c ⟶ P.projection.obj d)
    (a : (P.objects d).point ⟶ (P.objects c).point)
    (ht : (P.objects d).arrow ≫ a = (P.objects c).arrow)
    (hb) : (P.morphisms c d (deformationHomOfBase iΛ P r a ht hb)).arrow = a := by
  simp [deformationHomOfBase]

private theorem deformationHomOfBase_projection
    {X' : Type v} [Category.{w} X'] {q : X' ⥤ Over S} {x₀ : X'}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (P : PredeformationConstruction iΛ q x₀ hx₀)
    {c d : P.carrier} (r : P.projection.obj c ⟶ P.projection.obj d)
    (a : (P.objects d).point ⟶ (P.objects c).point)
    (ht : (P.objects d).arrow ≫ a = (P.objects c).arrow)
    (hb) : P.projection.map (deformationHomOfBase iΛ P r a ht hb) = r := by
  simp [deformationHom_projection, deformationHomOfBase]

/-- Given two deformations whose algebras agree, a reversed arrow between their points lifting an
identity of the base and compatible with their arrows is a morphism of deformations. -/
public def verticalDeformationMorphism_of_isHomLift
    {X' : Type v} [Category.{w} X'] {q : X' ⥤ Over S} {x₀ : X'} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a b : DeformationObject iΛ q x₀ hx₀}
    (hr : a.algebra = b.algebra) (f : b.point ⟶ a.point)
    (ht : b.arrow ≫ f = a.arrow) {U : Over S}
    (hv : q.IsHomLift (𝟙 U) f) : DeformationMorphism iΛ q x₀ hx₀ a b := by
  refine ⟨eqToHom hr, f, ht, ?_⟩
  cases a with | mk aa ax af ab ah =>
    cases b with | mk ba bx bf bb bh =>
      dsimp at hr
      subst ba
      have hf := congrArg Over.Hom.left (IsHomLift.fac' q (𝟙 U) f)
      dsimp at hf ⊢
      rw [hf]
      simp [Over.eqToHom_left, eqToHom_trans]

private def deformationIso
    {X' : Type v} [Category.{w} X'] {q : X' ⥤ Over S} {x₀ : X'} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (P : PredeformationConstruction iΛ q x₀ hx₀)
    {a b : P.carrier} (hr : (P.objects a).algebra = (P.objects b).algebra)
    (e : (P.objects b).point ≅ (P.objects a).point)
    (ht : (P.objects b).arrow ≫ e.hom = (P.objects a).arrow)
    {U : Over S} (hv : q.IsHomLift (𝟙 U) e.hom) : a ≅ b := by
  let d := verticalDeformationMorphism_of_isHomLift iΛ hr e.hom ht hv
  have hti : (P.objects a).arrow ≫ e.inv = (P.objects b).arrow := by
    rw [← ht, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hvi : q.IsHomLift (𝟙 U) e.inv := by
    have := hv
    infer_instance
  let di := verticalDeformationMorphism_of_isHomLift iΛ hr.symm e.inv hti hvi
  refine ⟨(P.morphisms a b).symm d, (P.morphisms b a).symm di, ?_, ?_⟩ <;>
  · apply deformationHom_ext iΛ P
    · rw [Functor.map_comp, CategoryTheory.Functor.map_id]
      simp [deformationHom_projection iΛ P,
        d, di, verticalDeformationMorphism_of_isHomLift]
    · simp [P.reversed_composition, P.reversed_identity, d, di,
        verticalDeformationMorphism_of_isHomLift]

private theorem deformationIso_arrow
    {X' : Type v} [Category.{w} X'] {q : X' ⥤ Over S} {x₀ : X'} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (P : PredeformationConstruction iΛ q x₀ hx₀)
    {a b : P.carrier} (hr : (P.objects a).algebra = (P.objects b).algebra)
    (e : (P.objects b).point ≅ (P.objects a).point)
    (ht : (P.objects b).arrow ≫ e.hom = (P.objects a).arrow)
    {U : Over S} (hv : q.IsHomLift (𝟙 U) e.hom) :
    (P.morphisms a b (deformationIso iΛ P hr e ht hv).hom).arrow = e.hom := by
  simp [deformationIso, verticalDeformationMorphism_of_isHomLift]

private theorem deformationIso_projection
    {X' : Type v} [Category.{w} X'] {q : X' ⥤ Over S} {x₀ : X'} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (P : PredeformationConstruction iΛ q x₀ hx₀)
    {a b : P.carrier} (hr : (P.objects a).algebra = (P.objects b).algebra)
    (e : (P.objects b).point ≅ (P.objects a).point)
    (ht : (P.objects b).arrow ≫ e.hom = (P.objects a).arrow)
    {U : Over S} (hv : q.IsHomLift (𝟙 U) e.hom) :
    P.projection.map (deformationIso iΛ P hr e ht hv).hom =
      eqToHom ((P.object_projection a).trans (hr.trans (P.object_projection b).symm)) := by
  simp [deformationHom_projection iΛ P, deformationIso, verticalDeformationMorphism_of_isHomLift]

private theorem exists_deformationNatIso
    {X' : Type v} [Category.{w} X'] {q : X' ⥤ Over S} {x₀ : X'}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (P : PredeformationConstruction iΛ q x₀ hx₀)
    {D : Type v₁} [Category.{w₁} D]
    (p : D ⥤ ArtinianLocalAlgCat.{u, u, u} Λ k)
    (H K : D ⥤ P.carrier) (hH : H ⋙ P.projection = p)
    (hK : K ⋙ P.projection = p)
    (e : ∀ c, (P.objects (K.obj c)).point ≅ (P.objects (H.obj c)).point)
    (ht : ∀ c, (P.objects (K.obj c)).arrow ≫ (e c).hom =
      (P.objects (H.obj c)).arrow)
    (U : D → Over S) (hv : ∀ c, q.IsHomLift (𝟙 (U c)) (e c).hom)
    (hn : ∀ {c d} (f : c ⟶ d),
      (e d).hom ≫ (P.morphisms _ _ (H.map f)).arrow =
        (P.morphisms _ _ (K.map f)).arrow ≫ (e c).hom) :
    ∃ t : H ≅ K,
      (∀ c, (P.morphisms _ _ (t.hom.app c)).arrow = (e c).hom) ∧
      (∀ c, P.projection.IsHomLift (𝟙 (p.obj c)) (t.hom.app c)) := by
  let hr c := (P.object_projection (H.obj c)).symm.trans
    ((Functor.congr_obj hH c).trans
      ((Functor.congr_obj hK c).symm.trans (P.object_projection (K.obj c))))
  let ei c := deformationIso iΛ P (hr c) (e c) (ht c) (hv c)
  have ep c : P.projection.map (ei c).hom =
      eqToHom ((Functor.congr_obj hH c).trans (Functor.congr_obj hK c).symm) :=
    deformationIso_projection iΛ P (hr c) (e c) (ht c) (hv c)
  let t : H ≅ K := NatIso.ofComponents ei (by
    intro c d f
    apply deformationHom_ext iΛ P
    · simp only [Functor.map_comp, ep]
      simpa using (eqToHom (hH.trans hK.symm)).naturality f
    · simpa only [P.reversed_composition, ei, deformationIso_arrow] using hn f)
  refine ⟨t, ?_, ?_⟩
  · intro c
    exact deformationIso_arrow iΛ P (hr c) (e c) (ht c) (hv c)
  · intro c
    apply IsHomLift.of_fac' P.projection (𝟙 (p.obj c)) (t.hom.app c)
      (Functor.congr_obj hH c) (Functor.congr_obj hK c)
    simpa [t] using ep c

private theorem isHomLift_map
    {C : Type u} [Category.{v} C] {D : Type v₁} [Category.{w₁} D]
    {E : Type v₂} [Category.{w₂} E] (p : D ⥤ C) (q : E ⥤ C)
    (H : D ⥤ E) (h : H ⋙ q = p) {a b : D} (f : a ⟶ b)
    {U V : C} {r : U ⟶ V} (hf : p.IsHomLift r f) : q.IsHomLift r (H.map f) := by
  apply IsHomLift.of_fac' q r (H.map f)
    ((Functor.congr_obj h a).trans (IsHomLift.domain_eq p r f))
    ((Functor.congr_obj h b).trans (IsHomLift.codomain_eq p r f))
  change (H ⋙ q).map f = _
  rw [Functor.congr_hom h f, IsHomLift.fac' p r f]
  simp

private theorem isHomLift_conjugate
    {C : Type u} [Category.{v} C] {D : Type v₁} [Category.{w₁} D]
    (q : D ⥤ C) {a b a' b' : D} (ha : a' = a) (hb : b' = b)
    (f : a ⟶ b) {U V : C} {r : U ⟶ V} (hf : q.IsHomLift r f) :
    q.IsHomLift r (eqToHom ha ≫ f ≫ eqToHom hb.symm) := by
  subst a'
  subst b'
  simpa using hf

/-- Essential surjectivity of an equivalence over a base can be made strict on the base when
the source is fibred in groupoids. -/
private theorem exists_iso_over_base
    {𝒞 : Type u} [Category.{v} 𝒞] {𝒰 : Type v₁} [Category.{w₁} 𝒰]
    {𝒱 : Type v₂} [Category.{w₂} 𝒱] (p : 𝒰 ⥤ 𝒞) (q : 𝒱 ⥤ 𝒞)
    (L : 𝒰 ⥤ 𝒱) (hL : L ⋙ q = p) (hp : p.IsFiberedInGroupoids)
    (hLₑ : L.IsEquivalence) {U : 𝒞} (z : 𝒱) (hz : q.obj z = U) :
    ∃ x : 𝒰, p.obj x = U ∧ ∃ e : L.obj x ≅ z,
      q.IsHomLift (𝟙 U) e.hom := by
  classical
  cases hL
  obtain ⟨x₀, ⟨α⟩⟩ := hLₑ.essSurj.mem_essImage z
  let c : q.obj (L.obj x₀) ≅ U := q.mapIso α ≪≫ eqToIso hz
  obtain ⟨x, hx, β, hβ⟩ := hp.exists_iso_lift c
  let e : L.obj x ≅ z := (L.mapIso β).symm ≪≫ α
  have he : q.IsHomLift (𝟙 U) e.hom := by
    apply IsHomLift.of_fac' q (𝟙 U) e.hom hx hz
    have hβfac : c.hom = q.map (L.map β.hom) ≫ eqToHom hx := by
      have h := IsHomLift.fac (L ⋙ q) c.hom β.hom
      have hd : IsHomLift.domain_eq (L ⋙ q) c.hom β.hom = rfl := Subsingleton.elim _ _
      have hc : IsHomLift.codomain_eq (L ⋙ q) c.hom β.hom = hx := Subsingleton.elim _ _
      rw [hd, hc] at h
      simpa only [Functor.comp_map, eqToHom_refl, Category.id_comp] using h
    have hτ : c = q.mapIso (L.mapIso β) ≪≫ eqToIso hx := Iso.ext hβfac
    have hβinv : q.map (L.map β.inv) = eqToHom hx ≫ c.inv := by
      have hinv := congrArg Iso.inv hτ
      have hinv' : c.inv = eqToHom hx.symm ≫ q.map (L.map β.inv) := by
        simpa using hinv
      rw [hinv']
      simp
    dsimp [e]
    rw [Functor.map_comp, hβinv]
    have hα : q.map α.hom = c.hom ≫ eqToHom hz.symm := by
      simp [c, Category.assoc]
    rw [hα]
    simp [Category.assoc]
  exact ⟨x, hx, e, he⟩

/-- Essential surjectivity of the ambient lift can be used with the point fixed over a chosen
scheme. The comparison isomorphism is vertical over the deformation's base. -/
private theorem lift_fibre_iso_over_base
    (hψ : ∀ w : W, qY.IsHomLift (𝟙 (qW.obj w)) (ψ.hom.app w))
    (hqW : qW.IsFiberedInGroupoids)
    (hfp : (TwoFibreProductOver.lift qX qZ qY F G qW A B hA hB ψ hψ).IsEquivalence)
    (U : Over S) (t : TwoFibreProductOver qX qZ qY F G)
    (ht : (TwoFibreProductOver.structureFunctor qX qZ qY F G).obj t = U) :
    ∃ w : W, qW.obj w = U ∧ ∃ e :
      (TwoFibreProductOver.lift qX qZ qY F G qW A B hA hB ψ hψ).obj w ≅ t,
      (TwoFibreProductOver.structureFunctor qX qZ qY F G).IsHomLift (𝟙 U) e.hom := by
  let p := TwoFibreProductOver.structureFunctor qX qZ qY F G
  let L := TwoFibreProductOver.lift qX qZ qY F G qW A B hA hB ψ hψ
  exact exists_iso_over_base qW p L
    (TwoFibreProductOver.lift_comp_structureFunctor qX qZ qY F G qW A B hA hB ψ hψ)
    hqW hfp t ht

/-- The arrow of `𝒬` underlying a reversed arrow of deformations of `x₀' = C(w₀)` in the image of
an induced functor, read between the images of the deformed objects of `𝒲`. -/
private def inducedArrow {Q : Type v₂} [Category.{w₂} Q] {qQ : Q ⥤ Over S} {C : W ⥤ Q}
    {hC : C ⋙ qQ = qW} (M : InducedPredeformationFunctor iΛ qW qQ C hC w₀ hw₀)
    (c d : (predeformationCategory iΛ qW w₀ hw₀).carrier)
    (fx : M.toFunctor.obj c ⟶ M.toFunctor.obj d) :
    C.obj ((predeformationCategory iΛ qW w₀ hw₀).objects d).point ⟶
      C.obj ((predeformationCategory iΛ qW w₀ hw₀).objects c).point :=
  eqToHom (M.object_point d).symm ≫
    ((predeformationCategory iΛ qQ (C.obj w₀)
      (imageBasePoint (qY := qQ) iΛ qW C hC w₀ hw₀)).morphisms _ _ fx).arrow ≫
    eqToHom (M.object_point c)

/-- An induced functor sends the arrow of a morphism of deformations to its image. -/
private theorem inducedArrow_map {Q : Type v₂} [Category.{w₂} Q] {qQ : Q ⥤ Over S} {C : W ⥤ Q}
    {hC : C ⋙ qQ = qW} (M : InducedPredeformationFunctor iΛ qW qQ C hC w₀ hw₀)
    {c d : (predeformationCategory iΛ qW w₀ hw₀).carrier} (f : c ⟶ d) :
    inducedArrow iΛ qW w₀ hw₀ M c d (M.toFunctor.map f) =
      C.map ((predeformationCategory iΛ qW w₀ hw₀).morphisms c d f).arrow := by
  rw [inducedArrow, M.morphism_arrow]
  simp

/-- Equal images under an induced functor have equal underlying arrows of deformed objects. -/
private theorem map_arrow_eq_of_induced_map_eq {Q : Type v₂} [Category.{w₂} Q]
    {qQ : Q ⥤ Over S} {C : W ⥤ Q} {hC : C ⋙ qQ = qW}
    (M : InducedPredeformationFunctor iΛ qW qQ C hC w₀ hw₀)
    {c d : (predeformationCategory iΛ qW w₀ hw₀).carrier} {f g : c ⟶ d}
    (h : M.toFunctor.map f = M.toFunctor.map g) :
    C.map ((predeformationCategory iΛ qW w₀ hw₀).morphisms c d f).arrow =
      C.map ((predeformationCategory iΛ qW w₀ hw₀).morphisms c d g).arrow := by
  rw [← inducedArrow_map iΛ qW w₀ hw₀ M, ← inducedArrow_map iΛ qW w₀ hw₀ M, h]

/-- The triangle of a reversed arrow of deformations, transported along an induced functor. -/
private theorem map_arrow_comp_inducedArrow {Q : Type v₂} [Category.{w₂} Q]
    {qQ : Q ⥤ Over S} {C : W ⥤ Q} {hC : C ⋙ qQ = qW}
    (M : InducedPredeformationFunctor iΛ qW qQ C hC w₀ hw₀)
    (c d : (predeformationCategory iΛ qW w₀ hw₀).carrier)
    (fx : M.toFunctor.obj c ⟶ M.toFunctor.obj d) :
    C.map ((predeformationCategory iΛ qW w₀ hw₀).objects d).arrow ≫
      inducedArrow iΛ qW w₀ hw₀ M c d fx =
      C.map ((predeformationCategory iΛ qW w₀ hw₀).objects c).arrow := by
  have hh := ((predeformationCategory iΛ qQ (C.obj w₀)
    (imageBasePoint (qY := qQ) iΛ qW C hC w₀ hw₀)).morphisms _ _ fx).triangle
  change ((predeformationCategory iΛ qQ (C.obj w₀)
      (imageBasePoint (qY := qQ) iΛ qW C hC w₀ hw₀)).objects (M.toFunctor.obj d)).arrow ≫ _ =
    ((predeformationCategory iΛ qQ (C.obj w₀)
      (imageBasePoint (qY := qQ) iΛ qW C hC w₀ hw₀)).objects (M.toFunctor.obj c)).arrow at hh
  rw [M.object_arrow, M.object_arrow] at hh
  simpa [inducedArrow, Category.assoc] using congrArg (fun m => m ≫ eqToHom (M.object_point c)) hh

/-- A reversed arrow of deformations lifting `r` gives, along an induced functor, an arrow of `𝒬`
lifting the corresponding arrow of the schemes. -/
private theorem isHomLift_inducedArrow {Q : Type v₂} [Category.{w₂} Q]
    {qQ : Q ⥤ Over S} {C : W ⥤ Q} {hC : C ⋙ qQ = qW}
    (M : InducedPredeformationFunctor iΛ qW qQ C hC w₀ hw₀)
    (c d : (predeformationCategory iΛ qW w₀ hw₀).carrier)
    (fx : M.toFunctor.obj c ⟶ M.toFunctor.obj d)
    (r : (predeformationCategory iΛ qW w₀ hw₀).projection.obj c ⟶
      (predeformationCategory iΛ qW w₀ hw₀).projection.obj d)
    (hf : (predeformationCategory iΛ qQ (C.obj w₀)
      (imageBasePoint (qY := qQ) iΛ qW C hC w₀ hw₀)).projection.IsHomLift r fx) :
    qQ.IsHomLift (eqToHom (deformationBase iΛ (predeformationCategory iΛ qW w₀ hw₀) d) ≫
      (artinianSpec iΛ).map r.op ≫
        eqToHom (deformationBase iΛ (predeformationCategory iΛ qW w₀ hw₀) c).symm)
      (inducedArrow iΛ qW w₀ hw₀ M c d fx) := by
  have hh : qQ.IsHomLift ((artinianSpec iΛ).map r.op) (inducedArrow iΛ qW w₀ hw₀ M c d fx) :=
    isHomLift_conjugate qQ (M.object_point d).symm
      (M.object_point c).symm _ (deformationHom_isHomLift iΛ _ fx r hf)
  apply IsHomLift.of_fac' qQ _ _ (Functor.congr_obj hC _) (Functor.congr_obj hC _)
  rw [IsHomLift.fac' qQ ((artinianSpec iΛ).map r.op) (inducedArrow iΛ qW w₀ hw₀ M c d fx)]
  simp [Category.assoc]

/-- Inverting `inducedArrow`: a morphism of deformations of `𝒲` whose image under `C` is the
given arrow and which lies over `r` is sent by an induced functor to the given morphism. -/
private theorem induced_map_deformationHomOfBase {Q : Type v₂} [Category.{w₂} Q]
    {qQ : Q ⥤ Over S} {C : W ⥤ Q} {hC : C ⋙ qQ = qW}
    (M : InducedPredeformationFunctor iΛ qW qQ C hC w₀ hw₀)
    {c d : (predeformationCategory iΛ qW w₀ hw₀).carrier}
    (fx : M.toFunctor.obj c ⟶ M.toFunctor.obj d)
    (r : (predeformationCategory iΛ qW w₀ hw₀).projection.obj c ⟶
      (predeformationCategory iΛ qW w₀ hw₀).projection.obj d)
    (hf : (predeformationCategory iΛ qQ (C.obj w₀)
      (imageBasePoint (qY := qQ) iΛ qW C hC w₀ hw₀)).projection.IsHomLift r fx)
    (a : ((predeformationCategory iΛ qW w₀ hw₀).objects d).point ⟶
      ((predeformationCategory iΛ qW w₀ hw₀).objects c).point)
    (ht : ((predeformationCategory iΛ qW w₀ hw₀).objects d).arrow ≫ a =
      ((predeformationCategory iΛ qW w₀ hw₀).objects c).arrow) (hr)
    (haa : C.map a = inducedArrow iΛ qW w₀ hw₀ M c d fx) :
    M.toFunctor.map (deformationHomOfBase iΛ (predeformationCategory iΛ qW w₀ hw₀) r a ht hr) =
      fx := by
  apply deformationHom_ext iΛ (predeformationCategory iΛ qQ (C.obj w₀)
    (imageBasePoint (qY := qQ) iΛ qW C hC w₀ hw₀))
  · rw [← Functor.comp_map, Functor.congr_hom M.projection_comm, deformationHomOfBase_projection]
    simpa using (IsHomLift.fac' (predeformationCategory iΛ qQ _ _).projection r fx).symm
  · rw [M.morphism_arrow, deformationHomOfBase_arrow, haa]
    simp [inducedArrow]

local notation "hX" => imageBasePoint (qY := qX) iΛ qW A hA w₀ hw₀
local notation "hZ" => imageBasePoint (qY := qZ) iΛ qW B hB w₀ hw₀
local notation "hY" => imageBasePoint (qY := qY) iΛ qX F hF (A.obj w₀) hX
local notation "pW" => predeformationCategory iΛ qW w₀ hw₀
local notation "pX" => predeformationCategory iΛ qX (A.obj w₀) hX
local notation "pZ" => predeformationCategory iΛ qZ (B.obj w₀) hZ
local notation "pY" => predeformationCategory iΛ qY (F.obj (A.obj w₀)) hY
local notation "mA" => InducedPredeformationFunctor.toFunctor
  (mapPredeformationCategory iΛ qW qX A hA w₀ hw₀)
local notation "mB" => InducedPredeformationFunctor.toFunctor
  (mapPredeformationCategory iΛ qW qZ B hB w₀ hw₀)
local notation "mF" => InducedPredeformationFunctor.toFunctor
  (mapPredeformationCategory iΛ qX qY F hF (A.obj w₀) hX)

/-- The data exhibiting the square of predeformation categories of a 2-fibre product as a
2-fibre product: the right-hand arrow `𝓕_{𝒵,k,z₀} ⥤ 𝓕_{𝒴,k,y₀}`, which is the functor
induced by `G` transported along the comparison isomorphism `ψ(w₀) : y₀ ≅ G(z₀)`, the
2-cell filling the square, and the assertion that the mediating functor into the 2-fibre
product of categories over `𝒞_Λ` is an equivalence. -/
public structure PredeformationFibreProductData where
  /-- The right-hand arrow `𝓕_{𝒵,k,z₀} ⥤ 𝓕_{𝒴,k,y₀}` of the square. -/
  rightFunctor : (pZ).carrier ⥤ (pY).carrier
  /-- It is a morphism of categories over `𝒞_Λ`. -/
  rightFunctor_projection :
    rightFunctor ⋙ (pY).projection = (pZ).projection
  /-- On a deformation object it is `G` on the underlying object of `𝒴`. -/
  rightFunctor_point : ∀ c,
    ((pY).objects (rightFunctor.obj c)).point =
      G.obj ((pZ).objects c).point
  /-- Its arrow from the basepoint is the image under `G` of the given one, precomposed
  with the comparison isomorphism `ψ(w₀) : y₀ ≅ G(z₀)`. -/
  rightFunctor_arrow : ∀ c,
    ((pY).objects (rightFunctor.obj c)).arrow =
      ψ.hom.app w₀ ≫ G.map ((pZ).objects c).arrow ≫
        eqToHom (rightFunctor_point c).symm
  /-- On a reversed arrow of deformations it is `G`. -/
  rightFunctor_map_arrow : ∀ {c d} (f : c ⟶ d),
    ((pY).morphisms (rightFunctor.obj c)
        (rightFunctor.obj d) (rightFunctor.map f)).arrow =
      eqToHom (rightFunctor_point d) ≫
        G.map ((pZ).morphisms c d f).arrow ≫
          eqToHom (rightFunctor_point c).symm
  /-- The square of predeformation categories 2-commutes. -/
  filler : mA ⋙ mF ≅ mB ⋙ rightFunctor
  /-- The filling 2-cell is the canonical one: the underlying arrow of `𝒴` of its component
  at a deformation object is the comparison isomorphism `ψ` of the 2-fibre product, taken at
  the underlying object of `𝒲`. -/
  filler_arrow : ∀ c,
    ((pY).morphisms _ _ (filler.hom.app c)).arrow =
      eqToHom ((rightFunctor_point ((mB).obj c)).trans
        (congrArg G.obj
          ((mapPredeformationCategory iΛ qW qZ B hB w₀ hw₀).object_point c))) ≫
      ψ.inv.app ((pW).objects c).point ≫
      eqToHom
        (((mapPredeformationCategory iΛ qX qY F hF (A.obj w₀) hX).object_point
          ((mA).obj c)).trans
          (congrArg F.obj
            ((mapPredeformationCategory iΛ qW qX A hA w₀ hw₀).object_point
              c))).symm
  /-- The filling 2-cell is a 2-morphism over `𝒞_Λ`: all its components are vertical. -/
  filler_vertical : ∀ c,
    (pY).projection.IsHomLift
      (𝟙 ((pW).projection.obj c)) (filler.hom.app c)
  /-- The square is a 2-fibre product: the mediating functor into the 2-fibre product of
  categories over `𝒞_Λ` is an equivalence. -/
  isEquivalence : (TwoFibreProductOver.lift
    (pX).projection
    (pZ).projection
    (pY).projection
    mF rightFunctor
    (pW).projection
    mA mB
    (mapPredeformationCategory iΛ qW qX A hA w₀ hw₀).projection_comm
    (mapPredeformationCategory iΛ qW qZ B hB w₀ hw₀).projection_comm
    filler filler_vertical).IsEquivalence

private theorem nonempty_fibreProductOfPredeformationCategories (hG : G ⋙ qY = qZ)
    (hψ : ∀ w : W, qY.IsHomLift (𝟙 (qW.obj w)) (ψ.hom.app w))
    (hess : ∀ (U : Over S) (t : TwoFibreProductOver qX qZ qY F G),
      (TwoFibreProductOver.structureFunctor qX qZ qY F G).obj t = U →
      ∃ w : W, qW.obj w = U ∧ ∃ e :
        (TwoFibreProductOver.lift qX qZ qY F G qW A B hA hB ψ hψ).obj w ≅ t,
        (TwoFibreProductOver.structureFunctor qX qZ qY F G).IsHomLift (𝟙 U) e.hom)
    (hfp : (TwoFibreProductOver.lift qX qZ qY F G qW A B hA hB ψ hψ).IsEquivalence) :
    Nonempty (PredeformationFibreProductData iΛ qW qX qZ qY A B F G hA hB hF ψ w₀ hw₀) := by
  let hYG := imageBasePoint (qY := qY) iΛ qZ G hG (B.obj w₀) hZ
  let pYG := predeformationCategory iΛ qY (G.obj (B.obj w₀)) hYG
  let mG := mapPredeformationCategory iΛ qZ qY G hG (B.obj w₀) hZ
  have hbase0 : qY.obj (F.obj (A.obj w₀)) = qW.obj w₀ :=
    (Functor.congr_obj hF (A.obj w₀)).trans (Functor.congr_obj hA w₀)
  have hψ0 : qY.IsHomLift (𝟙 (qY.obj (F.obj (A.obj w₀))))
      (ψ.hom.app w₀) := by
    have h := hψ w₀
    rwa [← hbase0] at h
  let rebase := rebasePredeformationCategory (iΛ := iΛ) qY hY hYG
    (ψ.app w₀) hψ0 (pY) pYG
  let right := mG.toFunctor ⋙ rebase
  have rp : right ⋙ (pY).projection = (pZ).projection := by
    dsimp [right]
    rw [Functor.assoc, rebasePredeformation_projection_comm, mG.projection_comm]
  have rpt (c) : ((pY).objects (right.obj c)).point =
      G.obj ((pZ).objects c).point :=
    (rebasePredeformation_object_point (iΛ := iΛ) qY hY hYG
      (ψ.app w₀) hψ0 (pY) pYG (mG.toFunctor.obj c)).trans (mG.object_point c)
  have ra (c) : ((pY).objects (right.obj c)).arrow =
      ψ.hom.app w₀ ≫ G.map ((pZ).objects c).arrow ≫ eqToHom (rpt c).symm := by
    dsimp [right]
    rw [rebasePredeformation_object_arrow, mG.object_arrow]
    simp only [Category.assoc, eqToHom_trans]
    rfl
  have rm {c d} (f : c ⟶ d) :
      ((pY).morphisms (right.obj c) (right.obj d) (right.map f)).arrow =
        eqToHom (rpt d) ≫ G.map ((pZ).morphisms c d f).arrow ≫
          eqToHom (rpt c).symm := by
    refine (conj_eqToHom_iff_heq _ _ (rpt d) (rpt c)).mpr ?_
    dsimp [right]
    rw [rebasePredeformation_morphism_arrow, mG.morphism_arrow]
    refine HEq.trans (eqToHom_comp_heq _ _) ?_
    refine HEq.trans (comp_eqToHom_heq _ _) ?_
    refine HEq.trans (eqToHom_comp_heq _ _) ?_
    exact comp_eqToHom_heq _ _
  let aM := mapPredeformationCategory iΛ qW qX A hA w₀ hw₀
  let bM := mapPredeformationCategory iΛ qW qZ B hB w₀ hw₀
  let fM := mapPredeformationCategory iΛ qX qY F hF (A.obj w₀) hX
  let H := aM.toFunctor ⋙ fM.toFunctor
  let K := bM.toFunctor ⋙ right
  have hp : H ⋙ (pY).projection = (pW).projection := by
    dsimp [H]
    rw [Functor.assoc, fM.projection_comm, aM.projection_comm]
  have kp : K ⋙ (pY).projection = (pW).projection := by
    dsimp [K]
    rw [Functor.assoc, rp, bM.projection_comm]
  let lp c := (fM.object_point (aM.toFunctor.obj c)).trans
    (congrArg F.obj (aM.object_point c))
  let up c := (rpt (bM.toFunctor.obj c)).trans (congrArg G.obj (bM.object_point c))
  have la c : ((pY).objects (H.obj c)).arrow =
      F.map (A.map ((pW).objects c).arrow) ≫ eqToHom (lp c).symm := by
    dsimp [H]
    rw [fM.object_arrow, aM.object_arrow]
    simp [Category.assoc, eqToHom_map]
  have ua c : ((pY).objects (K.obj c)).arrow =
      ψ.hom.app w₀ ≫ G.map (B.map ((pW).objects c).arrow) ≫ eqToHom (up c).symm := by
    dsimp [K]
    rw [ra, bM.object_arrow]
    simp [Category.assoc, eqToHom_map]
  have lm {c d} (f : c ⟶ d) :
      ((pY).morphisms _ _ (H.map f)).arrow =
      eqToHom (lp d) ≫ F.map (A.map ((pW).morphisms _ _ f).arrow) ≫
        eqToHom (lp c).symm := by
    dsimp [H]
    rw [fM.morphism_arrow, aM.morphism_arrow]
    simp [Category.assoc, eqToHom_map]
  have um {c d} (f : c ⟶ d) :
      ((pY).morphisms _ _ (K.map f)).arrow =
      eqToHom (up d) ≫ G.map (B.map ((pW).morphisms _ _ f).arrow) ≫
        eqToHom (up c).symm := by
    dsimp [K]
    rw [rm, bM.morphism_arrow]
    simp [Category.assoc, eqToHom_map]
  let e c : ((pY).objects (K.obj c)).point ≅ ((pY).objects (H.obj c)).point :=
    eqToIso (up c) ≪≫ (ψ.app ((pW).objects c).point).symm ≪≫ (eqToIso (lp c)).symm
  have et c : ((pY).objects (K.obj c)).arrow ≫ (e c).hom =
      ((pY).objects (H.obj c)).arrow := by
    rw [ua, la]
    dsimp [e]
    simp only [Category.assoc]
    have hn := ψ.hom.naturality ((pW).objects c).arrow
    dsimp at hn
    rw [← Category.assoc (ψ.hom.app w₀), ← hn]
    simp
  have ev c : qY.IsHomLift (𝟙 (qW.obj ((pW).objects c).point)) (e c).hom := by
    have hv : qY.IsHomLift (𝟙 (qW.obj ((pW).objects c).point))
        (ψ.app ((pW).objects c).point).hom := hψ ((pW).objects c).point
    have hi : qY.IsHomLift (𝟙 (qW.obj ((pW).objects c).point))
        (ψ.inv.app ((pW).objects c).point) :=
      (inferInstance : qY.IsHomLift (𝟙 (qW.obj ((pW).objects c).point))
        (ψ.app ((pW).objects c).point).inv)
    exact isHomLift_conjugate qY (up c) (lp c) _ hi
  obtain ⟨filler, fa, fv⟩ := exists_deformationNatIso iΛ (pY) (pW).projection
    H K hp kp e et (fun c => qW.obj ((pW).objects c).point) ev (by
      intro c d f
      rw [lm, um]
      have hn := ψ.inv.naturality ((pW).morphisms _ _ f).arrow
      dsimp at hn
      simpa [e, Category.assoc] using congrArg
        (fun m => eqToHom (up d) ≫ m ≫ eqToHom (lp c).symm) hn.symm)
  refine ⟨⟨right, rp, rpt, ra, @rm, filler, fa, fv, ?_⟩⟩
  let L := TwoFibreProductOver.lift qX qZ qY F G qW A B hA hB ψ hψ
  let M := TwoFibreProductOver.lift (pX).projection (pZ).projection (pY).projection
    mF right (pW).projection mA mB aM.projection_comm bM.projection_comm filler fv
  have : L.IsEquivalence := hfp
  have : M.Faithful := ⟨by
    intro c d f g h
    apply deformationHom_ext iΛ (pW)
    · exact congrArg TwoFibreProductOver.Hom.hbase h
    · apply L.map_injective
      apply TwoFibreProductOver.Hom.ext'
      · exact map_arrow_eq_of_induced_map_eq iΛ qW w₀ hw₀ aM
          (congrArg TwoFibreProductOver.Hom.a h)
      · exact map_arrow_eq_of_induced_map_eq iΛ qW w₀ hw₀ bM
          (congrArg TwoFibreProductOver.Hom.b h)⟩
  have : M.Full := ⟨by
    intro c d f
    let fx : aM.toFunctor.obj c ⟶ aM.toFunctor.obj d := f.a
    let fz : bM.toFunctor.obj c ⟶ bM.toFunctor.obj d := f.b
    let ac := inducedArrow iΛ qW w₀ hw₀ aM c d fx
    let bc := inducedArrow iΛ qW w₀ hw₀ bM c d fz
    let r := eqToHom (deformationBase iΛ (pW) d) ≫
      (artinianSpec iΛ).map f.hbase.op ≫ eqToHom (deformationBase iΛ (pW) c).symm
    have hac : qX.IsHomLift r ac := isHomLift_inducedArrow iΛ qW w₀ hw₀ aM c d fx f.hbase f.ha
    have hbc : qZ.IsHomLift r bc := isHomLift_inducedArrow iΛ qW w₀ hw₀ bM c d fz f.hbase f.hb
    have hi : ψ.inv.app ((pW).objects d).point ≫ F.map ac =
        G.map bc ≫ ψ.inv.app ((pW).objects c).point := by
      have hh := congrArg (fun m => ((pY).morphisms _ _ m).arrow) f.w
      change ((pY).morphisms _ _
        (fM.toFunctor.map fx ≫ filler.hom.app d)).arrow =
        ((pY).morphisms _ _ (filler.hom.app c ≫ right.map fz)).arrow at hh
      rw [(pY).reversed_composition, (pY).reversed_composition] at hh
      change ((pY).morphisms (H.obj d) (K.obj d) (filler.hom.app d)).arrow ≫
        ((pY).morphisms (H.obj c) (H.obj d) (fM.toFunctor.map fx)).arrow =
        ((pY).morphisms (K.obj c) (K.obj d) (right.map fz)).arrow ≫
        ((pY).morphisms (H.obj c) (K.obj c) (filler.hom.app c)).arrow at hh
      rw [fa, fa] at hh
      dsimp only [H, K, Functor.comp_obj] at hh
      rw [fM.morphism_arrow, rm] at hh
      simpa [ac, bc, inducedArrow, e, lp, up, Category.assoc, eqToHom_map] using
        congrArg (fun m => eqToHom (up d).symm ≫ m ≫ eqToHom (lp c)) hh
    have hw : F.map ac ≫ ψ.hom.app ((pW).objects c).point =
        ψ.hom.app ((pW).objects d).point ≫ G.map bc := by
      simpa [Category.assoc] using congrArg
        (fun m => ψ.hom.app ((pW).objects d).point ≫ m ≫
          ψ.hom.app ((pW).objects c).point) hi
    let t : L.obj ((pW).objects d).point ⟶ L.obj ((pW).objects c).point :=
      ⟨r, ac, bc, hac, hbc, hw⟩
    obtain ⟨a, ha⟩ := L.map_surjective t
    have haa : A.map a = ac := congrArg TwoFibreProductOver.Hom.a ha
    have hab : B.map a = bc := congrArg TwoFibreProductOver.Hom.b ha
    have har : qW.map a = r := congrArg TwoFibreProductOver.Hom.hbase ha
    have hat : ((pW).objects d).arrow ≫ a = ((pW).objects c).arrow := by
      apply L.map_injective
      apply TwoFibreProductOver.Hom.ext'
      · change A.map (_ ≫ a) = A.map _
        rw [CategoryTheory.Functor.map_comp, haa]
        exact map_arrow_comp_inducedArrow iΛ qW w₀ hw₀ aM c d fx
      · change B.map (_ ≫ a) = B.map _
        rw [CategoryTheory.Functor.map_comp, hab]
        exact map_arrow_comp_inducedArrow iΛ qW w₀ hw₀ bM c d fz
    let a' := deformationHomOfBase iΛ (pW) f.hbase a hat har
    refine ⟨a', ?_⟩
    apply TwoFibreProductOver.Hom.ext'
    · exact induced_map_deformationHomOfBase iΛ qW w₀ hw₀ aM fx f.hbase f.ha a hat har haa
    · exact induced_map_deformationHomOfBase iΛ qW w₀ hw₀ bM fz f.hbase f.hb a hat har hab⟩
  have : M.EssSurj := by
    constructor
    intro z
    let R := z.base
    let J := artinianSpec (k := k) iΛ
    let tx := (deformationBase iΛ (pX) z.x).trans
      (congrArg (fun R => J.obj (Opposite.op R)) z.hx)
    let tz := (deformationBase iΛ (pZ) z.y).trans
      (congrArg (fun R => J.obj (Opposite.op R)) z.hy)
    let ti : F.obj ((pX).objects z.x).point ≅ G.obj ((pZ).objects z.y).point :=
      (eqToIso (fM.object_point z.x)).symm ≪≫
        (deformationPointIso iΛ (pY) z.iso).symm ≪≫ eqToIso (rpt z.y)
    have tiv : qY.IsHomLift (𝟙 (J.obj (Opposite.op R))) ti.hom := by
      have := z.vertical
      have vi : (pY).projection.IsHomLift (𝟙 R) z.iso.inv := inferInstance
      have hh := deformationHom_isHomLift iΛ (pY) z.iso.inv (𝟙 R) vi
      have hh' : qY.IsHomLift (𝟙 (J.obj (Opposite.op R)))
          ((pY).morphisms _ _ z.iso.inv).arrow := by simpa [J] using hh
      exact isHomLift_conjugate qY (fM.object_point z.x).symm (rpt z.y).symm _ hh'
    let t : TwoFibreProductOver qX qZ qY F G :=
      ⟨J.obj (Opposite.op R), ((pX).objects z.x).point,
        ((pZ).objects z.y).point, tx, tz, ti, tiv⟩
    let r₀ := eqToHom hw₀ ≫ residueArrow iΛ R
    have tax : qX.IsHomLift r₀ ((pX).objects z.x).arrow := by
      apply IsHomLift.of_fac' qX _ _ (Functor.congr_obj hA w₀) tx
      rw [deformationArrow_base iΛ (pX) z.x z.hx]
      simp [r₀, J, R, Category.assoc]
    have taz : qZ.IsHomLift r₀ ((pZ).objects z.y).arrow := by
      apply IsHomLift.of_fac' qZ _ _ (Functor.congr_obj hB w₀) tz
      rw [deformationArrow_base iΛ (pZ) z.y z.hy]
      simp [r₀, J, R, Category.assoc]
    have taw : F.map ((pX).objects z.x).arrow ≫ ti.hom =
        ψ.hom.app w₀ ≫ G.map ((pZ).objects z.y).arrow := by
      have hh := ((pY).morphisms _ _ z.iso.inv).triangle
      change ((pY).objects (fM.toFunctor.obj z.x)).arrow ≫ _ =
        ((pY).objects (right.obj z.y)).arrow at hh
      rw [fM.object_arrow, ra] at hh
      simpa [ti, deformationPointIso, Category.assoc] using congrArg
        (fun m => m ≫ eqToHom (rpt z.y)) hh
    let a₀ : L.obj w₀ ⟶ t :=
      ⟨r₀, ((pX).objects z.x).arrow, ((pZ).objects z.y).arrow, tax, taz, taw⟩
    obtain ⟨w, hw, ei, hei⟩ := hess (J.obj (Opposite.op R)) t rfl
    have ei_base : ei.inv.hbase = eqToHom hw.symm := by
      have := hei
      have hi : (TwoFibreProductOver.structureFunctor qX qZ qY F G).IsHomLift
          (𝟙 (J.obj (Opposite.op R))) ei.inv := inferInstance
      have hh := IsHomLift.fac' (TwoFibreProductOver.structureFunctor qX qZ qY F G)
        (𝟙 (J.obj (Opposite.op R))) ei.inv
      simpa [TwoFibreProductOver.structureFunctor, t, L, eqToHom_trans,
        eqToHom_trans_assoc] using hh
    obtain ⟨a, ha⟩ := L.map_surjective (a₀ ≫ ei.inv)
    have ab : qW.map a = r₀ ≫ eqToHom hw.symm := by
      simpa [a₀, ei_base, L] using congrArg TwoFibreProductOver.Hom.hbase ha
    let d₀ : DeformationObject iΛ qW w₀ hw₀ :=
      ⟨R, w, a, hw, by
        rw [ab]
        simp [r₀, residueArrow, Over.comp_left, Over.eqToHom_left, Category.assoc]⟩
    let c := (pW).objects.symm d₀
    have ce : (pW).objects c = d₀ := (pW).objects.apply_symm_apply _
    have cr : (pW).projection.obj c = R := (pW).object_projection c |>.trans
      (congrArg DeformationObject.algebra ce)
    let cp : ((pW).objects c).point = w := congrArg DeformationObject.point ce
    have ca : ((pW).objects c).arrow = a ≫ eqToHom cp.symm :=
      deformationObject_arrow_eq iΛ ce
    let ec : L.obj ((pW).objects c).point ≅ t := L.mapIso (eqToIso cp) ≪≫ ei
    have ecb : ec.inv.hbase = eqToHom
        ((deformationBase iΛ (pW) c).trans
          (congrArg (fun R => J.obj (Opposite.op R)) cr)).symm := by
      change ei.inv.hbase ≫ (L.map (eqToHom cp.symm)).hbase = _
      change ei.inv.hbase ≫ qW.map (eqToHom cp.symm) = _
      rw [ei_base, eqToHom_map, eqToHom_trans]
    have ecax : qX.IsHomLift (𝟙 (J.obj (Opposite.op R))) ec.inv.a := by
      have hh := ec.inv.ha
      rw [ecb] at hh
      exact (IsHomLift.lift_comp_eqToHom_iff qX (𝟙 _) _ _).mp (by simpa using hh)
    have ecbz : qZ.IsHomLift (𝟙 (J.obj (Opposite.op R))) ec.inv.b := by
      have hh := ec.inv.hb
      rw [ecb] at hh
      exact (IsHomLift.lift_comp_eqToHom_iff qZ (𝟙 _) _ _).mp (by simpa using hh)
    have eca : L.map ((pW).objects c).arrow = a₀ ≫ ec.inv := by
      rw [ca, CategoryTheory.Functor.map_comp, ha]
      simp [ec, Category.assoc, eqToHom_map]
    let ex : ((pX).objects z.x).point ≅ ((pX).objects (aM.toFunctor.obj c)).point :=
      ((TwoFibreProductOver.fst qX qZ qY F G).mapIso ec).symm ≪≫
        (eqToIso (aM.object_point c)).symm
    let ez : ((pZ).objects z.y).point ≅ ((pZ).objects (bM.toFunctor.obj c)).point :=
      ((TwoFibreProductOver.snd qX qZ qY F G).mapIso ec).symm ≪≫
        (eqToIso (bM.object_point c)).symm
    have ext : ((pX).objects z.x).arrow ≫ ex.hom =
        ((pX).objects (aM.toFunctor.obj c)).arrow := by
      rw [aM.object_arrow]
      have hh := congrArg TwoFibreProductOver.Hom.a eca
      change A.map ((pW).objects c).arrow = ((pX).objects z.x).arrow ≫ ec.inv.a at hh
      simpa [ex, Category.assoc, eqToHom_trans, eqToHom_trans_assoc] using congrArg
        (fun m => m ≫ eqToHom (aM.object_point c).symm) hh.symm
    have ezt : ((pZ).objects z.y).arrow ≫ ez.hom =
        ((pZ).objects (bM.toFunctor.obj c)).arrow := by
      rw [bM.object_arrow]
      have hh := congrArg TwoFibreProductOver.Hom.b eca
      change B.map ((pW).objects c).arrow = ((pZ).objects z.y).arrow ≫ ec.inv.b at hh
      simpa [ez, Category.assoc, eqToHom_trans, eqToHom_trans_assoc] using congrArg
        (fun m => m ≫ eqToHom (bM.object_point c).symm) hh.symm
    have exv : qX.IsHomLift (𝟙 (J.obj (Opposite.op R))) ex.hom := by
      simpa [ex, eqToHom_trans, eqToHom_trans_assoc] using
        isHomLift_conjugate qX rfl (aM.object_point c) ec.inv.a ecax
    have ezv : qZ.IsHomLift (𝟙 (J.obj (Opposite.op R))) ez.hom := by
      simpa [ez, eqToHom_trans, eqToHom_trans_assoc] using
        isHomLift_conjugate qZ rfl (bM.object_point c) ec.inv.b ecbz
    let xr := ((pX).object_projection (aM.toFunctor.obj c)).symm.trans
      ((Functor.congr_obj aM.projection_comm c).trans
        (cr.trans (z.hx.symm.trans ((pX).object_projection z.x))))
    let zr := ((pZ).object_projection (bM.toFunctor.obj c)).symm.trans
      ((Functor.congr_obj bM.projection_comm c).trans
        (cr.trans (z.hy.symm.trans ((pZ).object_projection z.y))))
    let ix := deformationIso iΛ (pX) xr ex ext exv
    let iz := deformationIso iΛ (pZ) zr ez ezt ezv
    have ixp := deformationIso_projection iΛ (pX) xr ex ext exv
    have izp := deformationIso_projection iΛ (pZ) zr ez ezt ezv
    have ixa : ((pX).morphisms _ _ ix.hom).arrow = ex.hom :=
      deformationIso_arrow iΛ (pX) xr ex ext exv
    have iza : ((pZ).morphisms _ _ iz.hom).arrow = ez.hom :=
      deformationIso_arrow iΛ (pZ) zr ez ezt ezv
    have hxv : (pX).projection.IsHomLift (eqToHom cr) ix.hom := by
      apply IsHomLift.of_fac' (pX).projection _ _
        (Functor.congr_obj aM.projection_comm c) z.hx
      simpa using ixp
    have hzv : (pZ).projection.IsHomLift (eqToHom cr) iz.hom := by
      apply IsHomLift.of_fac' (pZ).projection _ _
        (Functor.congr_obj bM.projection_comm c) z.hy
      simpa using izp
    have iw : fM.toFunctor.map ix.hom ≫ z.iso.hom =
        filler.hom.app c ≫ right.map iz.hom := by
      apply deformationHom_ext iΛ (pY)
      · have h1 := isHomLift_map (pX).projection (pY).projection fM.toFunctor
          fM.projection_comm ix.hom hxv
        have h2 := z.vertical
        have h3 := fv c
        have h4 := isHomLift_map (pZ).projection (pY).projection right rp iz.hom hzv
        have hl : (pY).projection.IsHomLift (eqToHom cr)
            (fM.toFunctor.map ix.hom ≫ z.iso.hom) := by
          simpa using (inferInstance : (pY).projection.IsHomLift
            (eqToHom cr ≫ 𝟙 R) (fM.toFunctor.map ix.hom ≫ z.iso.hom))
        have hr : (pY).projection.IsHomLift (eqToHom cr)
            (filler.hom.app c ≫ right.map iz.hom) := by
          simpa using (inferInstance : (pY).projection.IsHomLift
            (𝟙 ((pW).projection.obj c) ≫ eqToHom cr)
            (filler.hom.app c ≫ right.map iz.hom))
        rw [IsHomLift.fac' (pY).projection (eqToHom cr) _,
          IsHomLift.fac' (pY).projection (eqToHom cr) _]
      · rw [(pY).reversed_composition, (pY).reversed_composition]
        have fc := fa c
        dsimp only [H, K, Functor.comp_obj] at fc ⊢
        rw [fc, fM.morphism_arrow, rm, ixa, iza]
        have ih : ti.inv ≫ F.map ec.inv.a =
            G.map ec.inv.b ≫ ψ.inv.app ((pW).objects c).point := by
          apply ti.inv_comp_eq.mpr
          rw [← Category.assoc]
          exact (ψ.app ((pW).objects c).point).eq_comp_inv.mpr ec.inv.w
        simpa [ti, deformationPointIso, ex, ez, lp, up, e, fM, Category.assoc, eqToHom_map,
          eqToHom_trans, eqToHom_trans_assoc]
          using congrArg (fun m => eqToHom (rpt z.y) ≫ m ≫ eqToHom (lp c).symm) ih
    let f : M.obj c ⟶ z := ⟨eqToHom cr, ix.hom, iz.hom, hxv, hzv, iw⟩
    have : IsIso f := TwoFibreProductOver.isIso_of_isIso_components
      (pX).projection (pZ).projection (pY).projection mF right f
      (by dsimp [f]; infer_instance) (by dsimp [f]; infer_instance)
    exact ⟨c, ⟨asIso f⟩⟩
  change M.IsEquivalence
  exact {}

/-- Let `𝒲` be a 2-fibre product of `𝒳 ⟶ 𝒴` and `𝒵 ⟶ 𝒴` in categories fibred in groupoids over
schemes over `S`, and let `w₀` be an object of `𝒲` over `Spec k` with images `x₀`, `z₀`,
`y₀ = F(x₀)`. Then the square of predeformation categories `𝓕_{𝒲,k,w₀} ⟶ 𝓕_{𝒵,k,z₀}`,
`𝓕_{𝒳,k,x₀} ⟶ 𝓕_{𝒴,k,y₀}` is a 2-fibre product of predeformation categories. -/
@[stacks 07WL]
public def fibreProductOfPredeformationCategories (hG : G ⋙ qY = qZ)
    (hψ : ∀ w : W, qY.IsHomLift (𝟙 (qW.obj w)) (ψ.hom.app w))
    (hqW : qW.IsFiberedInGroupoids) (_hqX : qX.IsFiberedInGroupoids)
    (_hqZ : qZ.IsFiberedInGroupoids) (_hqY : qY.IsFiberedInGroupoids)
    (hfp : (TwoFibreProductOver.lift qX qZ qY F G qW A B hA hB ψ hψ).IsEquivalence) :
    PredeformationFibreProductData iΛ qW qX qZ qY A B F G hA hB hF ψ w₀ hw₀ := by
  exact Classical.choice (by
    exact nonempty_fibreProductOfPredeformationCategories
      iΛ qW qX qZ qY A B F G hA hB hF ψ w₀ hw₀ hG hψ
      (lift_fibre_iso_over_base qW qX qZ qY A B F G hA hB ψ hψ hqW hfp) hfp)

/-- The square of predeformation categories of a 2-fibre product is a 2-fibre product, given the
essential surjectivity of the ambient comparison functor strictly over the base in place of the
fibredness of `qW`. -/
@[stacks 07WL "the essential surjectivity of the ambient comparison functor supplied directly"]
public def fibreProductOfPredeformationCategoriesOfEssSurj (hG : G ⋙ qY = qZ)
    (hψ : ∀ w : W, qY.IsHomLift (𝟙 (qW.obj w)) (ψ.hom.app w))
    (hess : ∀ (U : Over S) (t : TwoFibreProductOver qX qZ qY F G),
      (TwoFibreProductOver.structureFunctor qX qZ qY F G).obj t = U →
      ∃ w : W, qW.obj w = U ∧ ∃ e :
        (TwoFibreProductOver.lift qX qZ qY F G qW A B hA hB ψ hψ).obj w ≅ t,
        (TwoFibreProductOver.structureFunctor qX qZ qY F G).IsHomLift (𝟙 U) e.hom)
    (hfp : (TwoFibreProductOver.lift qX qZ qY F G qW A B hA hB ψ hψ).IsEquivalence) :
    PredeformationFibreProductData iΛ qW qX qZ qY A B F G hA hB hF ψ w₀ hw₀ := by
  exact Classical.choice (by
    exact nonempty_fibreProductOfPredeformationCategories
      iΛ qW qX qZ qY A B F G hA hB hF ψ w₀ hw₀ hG hψ hess hfp)

end Deformation.Artin

end
