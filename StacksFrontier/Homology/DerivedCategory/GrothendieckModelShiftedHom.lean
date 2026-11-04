module

public import StacksFrontier.Homology.DerivedCategory.GrothendieckModel
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport
public import StacksFrontier.Homology.Injectives.Ext.SpectralSequenceOfFilteredComplex

/-!
# Shifted homomorphisms and `Ext` groups at the two models of the derived category

A Grothendieck abelian category `C` locally small in `w` carries two models of its derived
category side by side in this development: `HasDerivedCategory.standard C`, pinned file-locally
by many modules, and the model of Tag 079Q,
`Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian`, which is the model
`SheafOfModules.hasDerivedCategory` on sheaves of modules, activated file-locally. A term
`ShiftedHom X Y n` — in
particular an `Ext` group `DerivedCategory.Ext X Y n` — written at one model is a different type
from the same expression written at the other, although the objects `X` and `Y` are literally the
same (`Stacks.Injectives.grothendieckModelEquiv_functor_obj`).

This file identifies the two, in every degree and naturally in both arguments. The comparison
`Stacks.Injectives.grothendieckModelEquiv` is the identity on objects and carries the standard
localization functor to the one of Tag 079Q on the nose; this file equips it with its commutation
with the shift, proves it additive, and reads off the induced isomorphism of shifted
homomorphism groups through `Stacks.Injectives.shiftedHomMapAddEquiv`.

## Main definitions

* `Stacks.Injectives.grothendieckModelEquivCommShift`: the comparison commutes with the shift.
* `Stacks.Injectives.grothendieckModelShiftedHomAddEquiv`: **the isomorphism
  `ShiftedHom X Y n ≃+ ShiftedHom X Y n` between the two models**, for every `n : ℤ`.

## Main results

* `Stacks.Injectives.grothendieckModelEquiv_functor_additive`: the comparison is additive.
* `Stacks.Injectives.grothendieckModelEquiv_map_commShiftIso_hom_app_Q_obj`: at the image of a
  complex the commutation isomorphism carries the commutation isomorphism of the standard
  localization functor to that of Tag 079Q's.
* `Stacks.Injectives.grothendieckModelShiftedHomAddEquiv_map_Q`: compatibility with the classes
  of maps of complexes.
* `Stacks.Injectives.grothendieckModelShiftedHomAddEquiv_comp`: compatibility with the
  composition of shifted homomorphisms.
* `Stacks.Injectives.grothendieckModelShiftedHomAddEquiv_Q_map_comp` and
  `Stacks.Injectives.grothendieckModelShiftedHomAddEquiv_comp_singleFunctor_map`: compatibility
  with precomposition by the image of a map of complexes and with postcomposition by the image of
  a map of `C` placed in a single degree.

## Implementation notes

The commutation with the shift is `Functor.commShiftOfLocalization` along the localization
`DerivedCategory.Q` of cochain complexes, the lifting isomorphism being the identity: the
comparison composed with the standard `Q` *is* the `Q` of Tag 079Q
(`grothendieckModelEquiv_comp_Q`). It is not `StacksDraft.Perfect.derivedEquivalenceCommShift`,
which is the commutation of the other comparison `StacksDraft.DerivedModel.modelEquiv`, an
equivalence that is not the identity on objects.

Additivity is checked after precomposition with `DerivedCategory.Qh`, a localization at a
morphism property with a calculus of fractions, through
`StacksDraft.DerivedModel.shrinkComparisonQhIso`.

No `@[stacks]` attribute is attached: as explained in
`StacksFrontier/Homology/DerivedCategory/ModelComparisonTransport.lean`, the two models are an
artefact of formalizing the derived category as a chosen localization.

## References

* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 06XQ](https://stacks.math.columbia.edu/tag/06XQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe w v u

namespace Stacks.Injectives

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- The comparison of the two models carries the standard localization functor of cochain
complexes to the one of Tag 079Q, with the identity as lifting isomorphism. -/
instance grothendieckModelEquiv_lifting :
    Localization.Lifting (@DerivedCategory.Q C _ _ (HasDerivedCategory.standard C))
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (@DerivedCategory.Q C _ _ (hasDerivedCategory_of_isGrothendieckAbelian.{w} C))
      (grothendieckModelEquiv.{w} C).functor :=
  ⟨Iso.refl _⟩

/-- **The comparison of the two models commutes with the shift**: it is induced, along the
localization functor of the standard model, by the localization functor of Tag 079Q, which
commutes with the shift. -/
@[instance_reducible]
def grothendieckModelEquivCommShift : (grothendieckModelEquiv.{w} C).functor.CommShift ℤ :=
  Functor.commShiftOfLocalization (@DerivedCategory.Q C _ _ (HasDerivedCategory.standard C))
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ
    (@DerivedCategory.Q C _ _ (hasDerivedCategory_of_isGrothendieckAbelian.{w} C))
    (grothendieckModelEquiv.{w} C).functor

attribute [local instance] grothendieckModelEquivCommShift

/-- At the image of a complex `K`, the commutation of the comparison with the shift carries the
standard commutation of `Q` with the shift to the one of Tag 079Q's `Q`. -/
theorem grothendieckModelEquiv_map_commShiftIso_hom_app_Q_obj (n : ℤ) (K : CochainComplex C ℤ) :
    (grothendieckModelEquiv.{w} C).functor.map
        (((@DerivedCategory.Q C _ _ (HasDerivedCategory.standard C)).commShiftIso n).hom.app K) ≫
      ((grothendieckModelEquiv.{w} C).functor.commShiftIso n).hom.app
        ((@DerivedCategory.Q C _ _ (HasDerivedCategory.standard C)).obj K) =
      ((@DerivedCategory.Q C _ _
        (hasDerivedCategory_of_isGrothendieckAbelian.{w} C)).commShiftIso n).hom.app K := by
  rw [Functor.commShiftOfLocalization_iso_hom_app, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  dsimp only [grothendieckModelEquiv_lifting, Localization.Lifting.iso, Iso.refl_hom,
    Iso.refl_inv, NatTrans.id_app]
  refine (Category.id_comp _).trans ?_
  let Q₂ := @DerivedCategory.Q C _ _ (hasDerivedCategory_of_isGrothendieckAbelian.{w} C)
  exact (congrArg (fun t => (Q₂.commShiftIso n).hom.app K ≫ t)
    ((shiftFunctor (@DerivedCategory C _ _ (hasDerivedCategory_of_isGrothendieckAbelian.{w} C))
      n).map_id (Q₂.obj K))).trans (Category.comp_id _)

/-- **The comparison of the two models is additive.** Its composite with the standard `Qh` is
isomorphic to the `Qh` of Tag 079Q, which is additive, and `Qh` is a localization at a morphism
property with a calculus of fractions. -/
theorem grothendieckModelEquiv_functor_additive :
    (grothendieckModelEquiv.{w} C).functor.Additive := by
  let := HasDerivedCategory.standard C
  rw [Localization.functor_additive_iff (@DerivedCategory.Qh C _ _ (HasDerivedCategory.standard C))
    (HomotopyCategory.subcategoryAcyclic C).trW]
  let := hasDerivedCategory_of_isGrothendieckAbelian.{w} C
  exact Functor.additive_of_iso (StacksDraft.DerivedModel.shrinkComparisonQhIso C)

attribute [local instance] grothendieckModelEquiv_functor_additive

/-- **Shifted homomorphisms at the two models of the derived category.** For objects `X`, `Y` of
the standard model and `n : ℤ`, the group `ShiftedHom X Y n` computed at the standard model is
isomorphic to the one computed at the model of Tag 079Q — the objects being the same — by
applying the comparison equivalence. In particular this identifies the groups
`DerivedCategory.Ext X Y n` of the two models. -/
def grothendieckModelShiftedHomAddEquiv
    (X Y : @DerivedCategory C _ _ (HasDerivedCategory.standard C)) (n : ℤ) :
    ShiftedHom X Y n ≃+
      ShiftedHom ((grothendieckModelEquiv.{w} C).functor.obj X)
        ((grothendieckModelEquiv.{w} C).functor.obj Y) n :=
  shiftedHomMapAddEquiv (grothendieckModelEquiv.{w} C).functor X Y n

variable {C}

/-- The isomorphism of shifted homomorphism groups is the action of the comparison on shifted
homomorphisms. -/
theorem grothendieckModelShiftedHomAddEquiv_apply
    {X Y : @DerivedCategory C _ _ (HasDerivedCategory.standard C)} {n : ℤ}
    (x : ShiftedHom X Y n) :
    grothendieckModelShiftedHomAddEquiv.{w} C X Y n x =
      x.map (grothendieckModelEquiv.{w} C).functor := rfl

/-- The isomorphism is compatible with the composition of shifted homomorphisms. -/
theorem grothendieckModelShiftedHomAddEquiv_comp
    {X Y Z : @DerivedCategory C _ _ (HasDerivedCategory.standard C)} {a b c : ℤ}
    (x : ShiftedHom X Y a) (y : ShiftedHom Y Z b) (h : b + a = c) :
    grothendieckModelShiftedHomAddEquiv.{w} C X Z c (x.comp y h) =
      (grothendieckModelShiftedHomAddEquiv.{w} C X Y a x).comp
        (grothendieckModelShiftedHomAddEquiv.{w} C Y Z b y) h :=
  ShiftedHom.map_comp x y h (grothendieckModelEquiv.{w} C).functor

/-- The isomorphism is compatible with precomposition by a morphism of the derived category. -/
theorem grothendieckModelShiftedHomAddEquiv_precomp
    {X' X Y : @DerivedCategory C _ _ (HasDerivedCategory.standard C)} {n : ℤ}
    (a : X' ⟶ X) (x : ShiftedHom X Y n) :
    grothendieckModelShiftedHomAddEquiv.{w} C X' Y n (a ≫ x) =
      (grothendieckModelEquiv.{w} C).functor.map a ≫
        grothendieckModelShiftedHomAddEquiv.{w} C X Y n x := by
  simp [grothendieckModelShiftedHomAddEquiv_apply, ShiftedHom.map]

/-- The isomorphism is compatible with postcomposition by the shift of a morphism of the derived
category. -/
theorem grothendieckModelShiftedHomAddEquiv_postcomp
    {X Y Y' : @DerivedCategory C _ _ (HasDerivedCategory.standard C)} {n : ℤ}
    (x : ShiftedHom X Y n) (b : Y ⟶ Y') :
    grothendieckModelShiftedHomAddEquiv.{w} C X Y' n (x ≫ b⟦n⟧') =
      grothendieckModelShiftedHomAddEquiv.{w} C X Y n x ≫
        ((grothendieckModelEquiv.{w} C).functor.map b)⟦n⟧' := by
  simp [grothendieckModelShiftedHomAddEquiv_apply, ShiftedHom.map,
    Functor.commShiftIso_hom_naturality]

/-- **Compatibility with precomposition by a map of complexes**: precomposing with `Q.map φ` at
the standard model corresponds to precomposing with `Q.map φ` at the model of Tag 079Q. -/
theorem grothendieckModelShiftedHomAddEquiv_Q_map_comp {K L : CochainComplex C ℤ}
    {Y : @DerivedCategory C _ _ (HasDerivedCategory.standard C)} {n : ℤ} (φ : K ⟶ L)
    (x : ShiftedHom ((@DerivedCategory.Q C _ _ (HasDerivedCategory.standard C)).obj L) Y n) :
    grothendieckModelShiftedHomAddEquiv.{w} C _ Y n
        ((@DerivedCategory.Q C _ _ (HasDerivedCategory.standard C)).map φ ≫ x) =
      (@DerivedCategory.Q C _ _ (hasDerivedCategory_of_isGrothendieckAbelian.{w} C)).map φ ≫
        grothendieckModelShiftedHomAddEquiv.{w} C _ Y n x :=
  grothendieckModelShiftedHomAddEquiv_precomp _ x

/-- **Compatibility with postcomposition by a map placed in a single degree**: postcomposing with
the shift of `(singleFunctor C d).map g` at the standard model corresponds to postcomposing with
the shift of `(singleFunctor C d).map g` at the model of Tag 079Q. -/
theorem grothendieckModelShiftedHomAddEquiv_comp_singleFunctor_map
    {X : @DerivedCategory C _ _ (HasDerivedCategory.standard C)} {A B : C} {d n : ℤ}
    (x : ShiftedHom X ((@DerivedCategory.singleFunctor C _ _ (HasDerivedCategory.standard C)
      d).obj A) n) (g : A ⟶ B) :
    grothendieckModelShiftedHomAddEquiv.{w} C X _ n
        (x ≫ ((@DerivedCategory.singleFunctor C _ _ (HasDerivedCategory.standard C) d).map g)⟦n⟧') =
      grothendieckModelShiftedHomAddEquiv.{w} C X _ n x ≫
        ((@DerivedCategory.singleFunctor C _ _
          (hasDerivedCategory_of_isGrothendieckAbelian.{w} C) d).map g)⟦n⟧' :=
  grothendieckModelShiftedHomAddEquiv_postcomp x _

/-- **Compatibility with classes of cochain maps**: a shifted homomorphism between images of
complexes coming from a map of complexes `K ⟶ L⟦n⟧` at the standard model goes to the shifted
homomorphism coming from the same map at the model of Tag 079Q. -/
theorem grothendieckModelShiftedHomAddEquiv_map_Q {K L : CochainComplex C ℤ} {n : ℤ}
    (φ : K ⟶ L⟦n⟧) :
    grothendieckModelShiftedHomAddEquiv.{w} C _ _ n
        (ShiftedHom.map φ (@DerivedCategory.Q C _ _ (HasDerivedCategory.standard C))) =
      ShiftedHom.map φ
        (@DerivedCategory.Q C _ _ (hasDerivedCategory_of_isGrothendieckAbelian.{w} C)) := by
  rw [grothendieckModelShiftedHomAddEquiv_apply, ShiftedHom.map, ShiftedHom.map,
    ShiftedHom.map, CategoryTheory.Functor.map_comp, Category.assoc]
  exact congrArg (fun t => (grothendieckModelEquiv.{w} C).functor.map
      ((@DerivedCategory.Q C _ _ (HasDerivedCategory.standard C)).map φ) ≫ t)
    (grothendieckModelEquiv_map_commShiftIso_hom_app_Q_obj C n L)

/-- The isomorphism in degree `0` on a morphism: it is the comparison applied to that
morphism. -/
theorem grothendieckModelShiftedHomAddEquiv_mk₀
    {X Y : @DerivedCategory C _ _ (HasDerivedCategory.standard C)} (a : X ⟶ Y) :
    grothendieckModelShiftedHomAddEquiv.{w} C X Y 0 (ShiftedHom.mk₀ 0 rfl a) =
      ShiftedHom.mk₀ 0 rfl ((grothendieckModelEquiv.{w} C).functor.map a) :=
  ShiftedHom.map_mk₀ (0 : ℤ) rfl a (grothendieckModelEquiv.{w} C).functor

end Stacks.Injectives

end
