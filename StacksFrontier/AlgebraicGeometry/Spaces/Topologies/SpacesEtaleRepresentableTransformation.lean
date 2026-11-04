module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
public import StacksFrontier.CategoryTheory.Bicategory.Functor.Cat.ULift
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafGivesSpaceRepresentable
public import StacksFrontier.CategoryTheory.Bicategory.OverPullbackPseudofunctor
public import StacksFrontier.CategoryTheory.Sites.Descent.StrongTransDescentData

/-!
# The spaces-étale sites as a pseudofunctor, and Stacks 04D3 for representable sheaves

The spaces-étale sites `X ↦ X_{spaces,étale}` of the algebraic spaces over `S`, with base change
`V ↦ X ×_Y V` along `f : X ⟶ Y`, form a pseudofunctor: the sub-pseudofunctor of the pullback
pseudofunctor of slice categories on the objects étale over the base. Its fibres are the
spaces-étale sites on the nose and its transition functors are the base-change functors of
Stacks 03G2 on the nose.

Sending an algebraic space `V` étale over `X` to the sheaf `h_V` it represents is compatible with
inverse images: `f⁻¹ h_V ≅ h_{Y ×_X V}` (Stacks 04D3), naturally in `V`, and this identification
carries the identity comparison of the spaces-étale inverse images to the identity comparison of
base change. Together with its compatibility with the composition comparisons,
`AlgebraicGeometry.Space.spacesEtaleInverseImage_comp_inv_app_comp_baseChangeYonedaIso_hom`,
these are the data and the two coherences of a strong transformation from the pseudofunctor of
spaces-étale sites to `AlgebraicGeometry.Space.spacesEtalePseudofunctor`, the input through
which a descent datum of algebraic spaces étale over the source becomes a descent datum of
spaces-étale sheaves.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleObjectProperty`: being étale over the base, as a property
  of objects for the pullback pseudofunctor of slices of algebraic spaces.
* `AlgebraicGeometry.Space.spacesEtaleSitePseudofunctor`: the pseudofunctor of spaces-étale
  sites and base change.
* `AlgebraicGeometry.Space.spacesEtaleYonedaNaturality`: Stacks 04D3, `f⁻¹ h_V ≅ h_{Y ×_X V}`,
  as a natural isomorphism in `V`.
* `AlgebraicGeometry.Space.spacesEtaleYonedaStrongTrans`: the strong transformation `V ↦ h_V`
  from the pseudofunctor of spaces-étale sites, with objects lifted by
  `CategoryTheory.Pseudofunctor.uliftObj`, to `AlgebraicGeometry.Space.spacesEtalePseudofunctor`,
  and `AlgebraicGeometry.Space.spacesEtaleYonedaStrongTransAppFullyFaithful`, the full
  faithfulness of its components.

## Main results

* `AlgebraicGeometry.Space.spacesEtaleInverseImage_id_hom_app_yoneda`: along an identity, the
  identification of Stacks 04D3 is the identity comparison of base change.

## Implementation notes

The fibres of `AlgebraicGeometry.Space.spacesEtaleSitePseudofunctor` are categories whose
objects and morphisms both live in `Type (u + 1)`, while the categories of sheaves of
`AlgebraicGeometry.Space.spacesEtalePseudofunctor` have objects in `Type (u + 2)`, so the two
pseudofunctors land in different universe levels of `CategoryTheory.Cat`; the strong
transformation between them is therefore defined on
`CategoryTheory.Pseudofunctor.uliftObj.{u + 2}` of the former, which has the same morphisms.
Its two coherences are checked on components, through the private lemmas
`spacesEtaleYonedaStrongTrans_naturality_id_app` and
`spacesEtaleYonedaStrongTrans_naturality_comp_app`, which are stated for the spaces-étale sites
themselves.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 04D3](https://stacks.math.columbia.edu/tag/04D3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Being étale over the base, as a property of objects for the pullback pseudofunctor of the
slice categories of algebraic spaces over `S`. -/
def spacesEtaleObjectProperty :
    (Over.pullbackPseudofunctor (AlgebraicSpaces B S hS)).ObjectProperty where
  prop X := IsEtaleOver B S hS X.as.unop

/-- Being étale over the base is stable under base change along morphisms of algebraic spaces
over `S`. -/
instance : (spacesEtaleObjectProperty B S hS).IsClosedUnderMapObj where
  map_obj hM f := isEtaleOver_overPullback B S hS f.as.unop _ hM

/-- The pseudofunctor of spaces-étale sites: an algebraic space `X` over `S` goes to its
spaces-étale site `X_{spaces,étale}` and a morphism `f : X ⟶ Y` to base change
`V ↦ X ×_Y V`. -/
noncomputable abbrev spacesEtaleSitePseudofunctor :
    Pseudofunctor (LocallyDiscrete (AlgebraicSpaces B S hS)ᵒᵖ) Cat :=
  (spacesEtaleObjectProperty B S hS).fullsubcategory

/-- **Stacks 04D3 along an identity is the identity comparison.** Under the identification of
the inverse image along `𝟙 X` of the sheaf `h_V` with `h_{X ×_X V}`, the identity comparison of
the spaces-étale inverse images is the identity comparison of base change. -/
theorem spacesEtaleInverseImage_id_hom_app_yoneda (X : AlgebraicSpaces B S hS)
    (V : SpacesEtale B S hS X) :
    (spacesEtaleInverseImage_id B S hS X).hom.app
        ((SpacesEtale.topology B S hS X).yoneda.obj V) =
      (baseChangeYonedaIso B S hS (𝟙 X) V).hom ≫
        (SpacesEtale.topology B S hS X).yoneda.map ((spacesBaseChange_id B S hS X).hom.app V) := by
  apply ((spacesEtaleAdjunction B S hS (𝟙 X)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_naturality_right,
    show (spacesEtaleInverseImage_id B S hS X).hom =
      (conjugateEquiv Adjunction.id (spacesEtaleAdjunction B S hS (𝟙 X))).symm
        (spacesEtaleSheafPushforwardId B S hS X).inv from rfl,
    ← unit_conjugateEquiv_symm Adjunction.id (spacesEtaleAdjunction B S hS (𝟙 X))
      (spacesEtaleSheafPushforwardId B S hS X).inv ((SpacesEtale.topology B S hS X).yoneda.obj V)]
  apply (Adjunction.pushforwardYonedaEquiv (u := (spacesBaseChange B S hS (𝟙 X)).functor)
    V _).injective
  rw [Adjunction.pushforwardYonedaEquiv_comp,
    Adjunction.pushforwardYonedaEquiv_homEquiv_yonedaIso_hom]
  exact (Category.comp_id ((spacesBaseChange_id B S hS X).hom.app V)).trans
    (Category.id_comp ((spacesBaseChange_id B S hS X).hom.app V)).symm

/-- **Stacks 04D3 as a natural isomorphism.** For `f : Y ⟶ X` the sheaf represented by the
base change `Y ×_X V` is the inverse image of the sheaf represented by `V`, naturally in the
algebraic space `V` étale over `X`. -/
noncomputable def spacesEtaleYonedaNaturality {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) :
    (spacesBaseChange B S hS f).functor ⋙ (SpacesEtale.topology B S hS Y).yoneda ≅
      (SpacesEtale.topology B S hS X).yoneda ⋙ spacesEtaleInverseImage B S hS f :=
  NatIso.ofComponents (fun V => (baseChangeYonedaIso B S hS f V).symm) (fun {V V'} k => by
    simp only [Functor.comp_map, Iso.symm_hom]
    rw [Iso.comp_inv_eq, Category.assoc,
      Adjunction.map_yoneda_map_comp_yonedaIso_hom, Iso.inv_hom_id_assoc])

/-- A functor applied to an identity, followed by a morphism, is that morphism followed by an
identity. -/
private lemma map_id_comp_eq_comp_id {C D : Type*} [Category C] [Category D] (G : C ⥤ D) {X : C}
    {Y : D} (n : G.obj X ⟶ Y) : G.map (𝟙 X) ≫ n = n ≫ 𝟙 Y := by
  simp

/-- Composing with two identities does nothing. -/
private lemma comp_id_comp_id {C : Type*} [Category C] {X Y : C} (a : X ⟶ Y) :
    a ≫ 𝟙 Y ≫ 𝟙 Y = a := by
  simp

/-- Interleaving identities does nothing. -/
private lemma comp_id_comp_id_comp_id {C : Type*} [Category C] {X Y Z W : C} (a : X ⟶ Y)
    (b : Y ⟶ Z) (c : Z ⟶ W) :
    a ≫ 𝟙 Y ≫ b ≫ 𝟙 Z ≫ c ≫ 𝟙 W = a ≫ b ≫ c := by
  simp

/-- The unit coherence of the strong transformation `V ↦ h_V`, on components: the identity
comparison of the inverse images, read through Stacks 04D3, is that of base change. -/
private lemma spacesEtaleYonedaStrongTrans_naturality_id_app (X : AlgebraicSpaces B S hS)
    (V : SpacesEtale B S hS X) :
    (baseChangeYonedaIso B S hS (𝟙 X) V).inv ≫
        (spacesEtaleInverseImage_id B S hS X).hom.app
          ((SpacesEtale.topology B S hS X).yoneda.obj V) =
      (SpacesEtale.topology B S hS X).yoneda.map ((spacesBaseChange_id B S hS X).hom.app V) := by
  rw [spacesEtaleInverseImage_id_hom_app_yoneda, Iso.inv_hom_id_assoc]

/-- The composition coherence of the strong transformation `V ↦ h_V`, on components, in the
orientation the strong transformation asks for. -/
private lemma spacesEtaleYonedaStrongTrans_naturality_comp_app {T' T Z : AlgebraicSpaces B S hS}
    (k : T' ⟶ T) (y : T ⟶ Z) (V : SpacesEtale B S hS Z) :
    (baseChangeYonedaIso B S hS (k ≫ y) V).inv ≫
        (spacesEtaleInverseImage_comp B S hS k y).hom.app
          ((SpacesEtale.topology B S hS Z).yoneda.obj V) =
      (SpacesEtale.topology B S hS T').yoneda.map
          ((spacesBaseChange_comp B S hS k y).inv.app V) ≫
        (baseChangeYonedaIso B S hS k ((spacesBaseChange B S hS y).functor.obj V)).inv ≫
          (spacesEtaleInverseImage B S hS k).map (baseChangeYonedaIso B S hS y V).inv := by
  have hB : (baseChangeYonedaIso B S hS (k ≫ y) V).hom =
      (spacesEtaleInverseImage_comp B S hS k y).hom.app
          ((SpacesEtale.topology B S hS Z).yoneda.obj V) ≫
        (spacesEtaleInverseImage B S hS k).map (baseChangeYonedaIso B S hS y V).hom ≫
        (baseChangeYonedaIso B S hS k ((spacesBaseChange B S hS y).functor.obj V)).hom ≫
          (SpacesEtale.topology B S hS T').yoneda.map
            ((spacesBaseChange_comp B S hS k y).hom.app V) := by
    rw [← spacesEtaleInverseImage_comp_inv_app_comp_baseChangeYonedaIso_hom B S hS k y V,
      Iso.hom_inv_id_app_assoc]
  rw [Iso.inv_comp_eq, hB]
  simp [← Functor.map_comp_assoc, ← Functor.map_comp]

attribute [local instance] uliftCategory in
/-- **The strong transformation `V ↦ h_V`.** Sending an algebraic space `V` étale over `X` to
the sheaf `h_V` it represents on `X_{spaces,étale}` is a strong transformation from the
pseudofunctor of spaces-étale sites, with objects lifted to the universe of the categories of
sheaves, to the pseudofunctor of spaces-étale sheaves and inverse images: its naturality
constraint is Stacks 04D3, `f⁻¹ h_V ≅ h_{Y ×_X V}`. -/
noncomputable def spacesEtaleYonedaStrongTrans :
    ((spacesEtaleSitePseudofunctor B S hS).uliftObj.{u + 2}).StrongTrans
      (spacesEtalePseudofunctor B S hS) where
  app X := (ULift.downFunctor ⋙ (SpacesEtale.topology B S hS X.as.unop).yoneda).toCatHom
  naturality f := Cat.Hom.isoMk
    (Functor.isoWhiskerLeft ULift.downFunctor (spacesEtaleYonedaNaturality B S hS f.as.unop))
  naturality_naturality {a b} {f g} η := by
    obtain rfl : f = g := LocallyDiscrete.eq_of_hom η
    obtain rfl : η = 𝟙 f := Subsingleton.elim _ _
    rw [PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]
    ext V
    exact map_id_comp_eq_comp_id (SpacesEtale.topology B S hS b.as.unop).yoneda _
  naturality_id a := by
    ext V
    exact (spacesEtaleYonedaStrongTrans_naturality_id_app B S hS a.as.unop V.down).trans
      (comp_id_comp_id _).symm
  naturality_comp f g := by
    ext V
    exact (spacesEtaleYonedaStrongTrans_naturality_comp_app B S hS g.as.unop f.as.unop
      V.down).trans (comp_id_comp_id_comp_id _ _ _).symm

attribute [local instance] uliftCategory in
/-- The components of the strong transformation `V ↦ h_V` are fully faithful: this is the Yoneda
lemma for the subcanonical spaces-étale topology. -/
noncomputable def spacesEtaleYonedaStrongTransAppFullyFaithful
    (a : LocallyDiscrete (AlgebraicSpaces B S hS)ᵒᵖ) :
    ((spacesEtaleYonedaStrongTrans B S hS).app a).toFunctor.FullyFaithful :=
  (ULift.equivalence.symm.fullyFaithfulFunctor).comp
    (SpacesEtale.topology B S hS a.as.unop).yonedaFullyFaithful

/-- The components of the strong transformation `V ↦ h_V` are full. -/
instance (a : LocallyDiscrete (AlgebraicSpaces B S hS)ᵒᵖ) :
    ((spacesEtaleYonedaStrongTrans B S hS).app a).toFunctor.Full :=
  (spacesEtaleYonedaStrongTransAppFullyFaithful B S hS a).full

/-- The components of the strong transformation `V ↦ h_V` are faithful. -/
instance (a : LocallyDiscrete (AlgebraicSpaces B S hS)ᵒᵖ) :
    ((spacesEtaleYonedaStrongTrans B S hS).app a).toFunctor.Faithful :=
  (spacesEtaleYonedaStrongTransAppFullyFaithful B S hS a).faithful

end AlgebraicGeometry.Space

end
