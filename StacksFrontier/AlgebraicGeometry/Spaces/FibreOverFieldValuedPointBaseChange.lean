module

public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricallyReduced

/-!
# Fibres over field-valued points and base change

For a cartesian square of algebraic spaces with `f' : X' ⟶ Y'` the base change of
`f : X ⟶ Y` along `g : Y' ⟶ Y`, the fibre of `f'` over a field-valued point `Spec k ⟶ Y'` is the
fibre of `f` over the composite `Spec k ⟶ Y' ⟶ Y`. This is the remark
`(X ×_Y Y') ×_{Y'} Spec k = X ×_Y Spec k` used in the source whenever a fibrewise hypothesis is
passed to a base change, for the base changes formed in the category of algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Space.restrictedFibreIsoOfIso`: the fibre over a section does not change
  when the source of the morphism is replaced by an isomorphic one.
* `AlgebraicGeometry.Space.fibreOverFieldValuedPointPullbackSndIso`: the fibre of the base change
  `pullback.snd f g` over a field-valued point is the fibre of `f` over its image.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The fibre over a section of `Y` is unchanged when the source of the morphism is replaced by
an isomorphic presheaf: the fibre of `e.hom ≫ f` is the fibre of `f`. -/
noncomputable def restrictedFibreIsoOfIso {X X' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : X' ≅ X) (f : X ⟶ Y) {T : Scheme.{u}} (hT : B.Contains T) (g : B.obj hT ⟶ B.obj hS)
    (v : Y.obj (op (Over.mk g))) :
    restrictedFibre B S hS (e.hom ≫ f) hT g v ≅ restrictedFibre B S hS f hT g v :=
  have h₁ : (OverShriek.relocalizeRestrict g).map (e.hom ≫ f) ≫ 𝟙 _ =
      (OverShriek.relocalizeRestrict g).map e.hom ≫ (OverShriek.relocalizeRestrict g).map f := by
    rw [Category.comp_id, Functor.map_comp]
  have h₂ : restrictedSection B S hS Y hT g v ≫ 𝟙 _ =
      𝟙 _ ≫ restrictedSection B S hS Y hT g v := by
    simp
  @asIso _ _ _ _ _ (pullback.map_isIso ((OverShriek.relocalizeRestrict g).map (e.hom ≫ f))
      (restrictedSection B S hS Y hT g v) ((OverShriek.relocalizeRestrict g).map f)
      (restrictedSection B S hS Y hT g v)
      ((OverShriek.relocalizeRestrict g).map e.hom) (𝟙 _) (𝟙 _) h₁ h₂)

/-- **The fibre of a base change.** For morphisms `f : X ⟶ Y` and `g : Y' ⟶ Y` of algebraic
spaces, the fibre of the base change `pullback.snd f g : X ×_Y Y' ⟶ Y'` over a field-valued
point `p` of `Y'` is the fibre of `f` over the image of `p` in `Y`. -/
noncomputable def fibreOverFieldValuedPointPullbackSndIso {X Y Y' : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (p : FieldValuedPoint B S hS Y'.1) :
    fibreOverFieldValuedPoint B S hS (pullback.snd f g).hom p ≅
      fibreOverFieldValuedPoint B S hS f.hom (p.map B S hS Y'.1 g.hom) :=
  have h := AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback f g)
  eqToIso (congrArg (fun φ => restrictedFibre B S hS φ p.contained ⟨p.toBase⟩ p.value)
      (h.isoPullback_hom_snd).symm) ≪≫
    restrictedFibreIsoOfIso B S hS h.isoPullback (pullback.snd f.hom g.hom) p.contained _
      p.value ≪≫
    restrictedFibreBaseChangeIso B S hS f.hom g.hom p.contained _ p.value

end AlgebraicGeometry.Space
