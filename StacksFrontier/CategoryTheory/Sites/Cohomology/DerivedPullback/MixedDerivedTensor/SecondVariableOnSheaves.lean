module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.BaseChangeSecondVariable
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.SheafificationAndRestrictionOfScalars

/-!
# Naturality of the underived identity of Stacks 08I6 in the second variable

Let `α : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a site `(C, J)`. The
cancellation of a base change

`H|_{O₁} ⊗_{O₁} G ≅ (H ⊗_{O₂} (O₂ ⊗_{O₁} G))|_{O₁}`

of sheaves of `O₁`-modules is natural in the `O₁`-module `G`, as well as in the `O₂`-module `H`.

For a morphism of ringed topoi `f : (Sh(C), O) ⟶ (Sh(C'), O')`, the isomorphism

`F|_{f⁻¹O'} ⊗_{f⁻¹O'} f⁻¹G ≅ (F ⊗_O f^*G)|_{f⁻¹O'}`

is natural in the sheaf `G` of `O'`-modules, as well as in the sheaf `F` of `O`-modules.

## Main results

* `Stacks.Cohomology.MixedDerivedTensor.baseChange_inv_naturality_snd`: the inverse of the
  sectionwise cancellation of a base change is natural in the second tensor factor.
* `Stacks.Cohomology.MixedDerivedTensor.tensorBaseChangeLinearIso_naturality_snd` and
  `tensorBaseChangeLinearIso_hom_naturality_snd`: the cancellation of a base change is natural
  in the second tensor factor as an isomorphism of sheaves of `O₁`-modules, componentwise and as
  an equality of natural transformations.
* `Stacks.Cohomology.MixedDerivedTensor.pullbackIsoExtendInverseImage_naturality`: the
  identification of `f^*G` with the extension of scalars of `f⁻¹G` is natural in `G`.
* `Stacks.Cohomology.MixedDerivedTensor.underivedTensorInverseImageLinearIso_naturality_snd`
  and `underivedTensorInverseImageLinearIso_hom_naturality_snd`: the underived identity of
  Stacks 08I6 is natural in the sheaf of `O'`-modules, componentwise and as an equality of natural
  transformations.

## References

* [The Stacks Project, Tag 08I6](https://stacks.math.columbia.edu/tag/08I6)
* [The Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.Cohomology.MixedDerivedTensor

open Stacks Stacks.FlatChangeOfRings

/-! ### Pasting commuting squares -/

section Pasting

variable {D : Type*} [Category D]

/-- Three commuting squares pasted along their common edges give a commuting rectangle. -/
lemma eq_of_three_squares {X₀ X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ : D}
    {a : X₀ ⟶ X₁} {b : X₁ ⟶ X₂} {c : X₂ ⟶ X₃} {d : X₃ ⟶ X₄}
    {a' : X₀ ⟶ Y₁} {b' : Y₁ ⟶ X₂} {c' : Y₁ ⟶ Y₂} {d' : Y₂ ⟶ X₃}
    {e : Y₂ ⟶ Y₃} {g : Y₃ ⟶ X₄}
    (h₁ : a ≫ b = a' ≫ b') (h₂ : b' ≫ c = c' ≫ d') (h₃ : d' ≫ d = e ≫ g) :
    a ≫ b ≫ c ≫ d = a' ≫ c' ≫ e ≫ g := by
  rw [← Category.assoc, h₁, Category.assoc, ← Category.assoc b' c d, h₂, Category.assoc, h₃]

/-- Two commuting squares pasted along their common edge. -/
lemma eq_of_two_squares {X₀ X₁ X₂ X₃ Y₁ Y₂ : D}
    {a : X₀ ⟶ X₁} {b : X₁ ⟶ X₂} {c : X₂ ⟶ X₃}
    {a' : X₀ ⟶ Y₁} {b' : Y₁ ⟶ X₂} {c' : Y₁ ⟶ Y₂} {d : Y₂ ⟶ X₃}
    (h₁ : a ≫ b = a' ≫ b') (h₂ : b' ≫ c = c' ≫ d) :
    a ≫ b ≫ c = (a' ≫ c') ≫ d := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

end Pasting

/-! ### The cancellation of a base change in the second variable -/

section BaseChange

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {O₁ O₂ : Sheaf J CommRingCat.{w}}

omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The inverse of the sectionwise cancellation of a base change is natural in the second tensor
factor. -/
lemma baseChange_inv_naturality_snd (α : O₁ ⟶ O₂)
    {G G' : PresheafOfModules.{w} (ringPresheaf O₁.obj)} (γ : G ⟶ G')
    (H : PresheafOfModules.{w} (ringPresheaf O₂.obj)) :
    tensorMapRight ((PresheafOfModules.restrictScalars (ringPresheafMap α)).obj H) γ ≫
        (baseChange α G' H).inv
      = (baseChange α G H).inv ≫
        (PresheafOfModules.restrictScalars (ringPresheafMap α)).map
          (tensorMapRight H
            ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings α.hom).map γ)) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (baseChange_naturality_snd α γ H).symm

/-- The three squares whose pasting is the naturality of the `O₁`-linear cancellation of a base
change in the second tensor factor, at a fixed sheaf `H` of `O₂`-modules. -/
private lemma tensorBaseChangeLinear_square (α : O₁ ⟶ O₂)
    {G G' : SheafOfModules.{w} (commRingSheafToRingSheaf O₁)} (γ : G ⟶ G')
    (H : SheafOfModules.{w} (commRingSheafToRingSheaf O₂)) :
    (moduleSheafification O₁).map (tensorMapRight
          ((PresheafOfModules.restrictScalars (ringSheafMap α).hom).obj H.val) γ.val) ≫
        (moduleSheafification O₁).map ((baseChange α G'.val H.val).inv) ≫
        sheafifyRestrictHom α (tensorObj H.val ((presheafExtendScalars α).obj G'.val)) ≫
        (SheafOfModules.restrictScalars.{w} (ringSheafMap α)).map
          ((moduleSheafification O₂).map (tensorMapRight H.val
            (toSheafifyVal ((presheafExtendScalars α).obj G'.val))))
      = (moduleSheafification O₁).map ((baseChange α G.val H.val).inv) ≫
        sheafifyRestrictHom α (tensorObj H.val ((presheafExtendScalars α).obj G.val)) ≫
        (SheafOfModules.restrictScalars.{w} (ringSheafMap α)).map
          ((moduleSheafification O₂).map (tensorMapRight H.val
            (toSheafifyVal ((presheafExtendScalars α).obj G.val)))) ≫
        (SheafOfModules.restrictScalars.{w} (ringSheafMap α)).map
          ((moduleSheafification O₂).map (tensorMapRight H.val
            ((SheafOfModules.forget (commRingSheafToRingSheaf O₂)).map
              ((moduleSheafification O₂).map ((presheafExtendScalars α).map γ.val))))) := by
  have h₁ : (moduleSheafification O₁).map (tensorMapRight
        ((PresheafOfModules.restrictScalars (ringSheafMap α).hom).obj H.val) γ.val) ≫
      (moduleSheafification O₁).map ((baseChange α G'.val H.val).inv)
      = (moduleSheafification O₁).map ((baseChange α G.val H.val).inv) ≫
        (moduleSheafification O₁).map ((PresheafOfModules.restrictScalars
          (ringSheafMap α).hom).map (tensorMapRight H.val
            ((presheafExtendScalars α).map γ.val))) :=
    map_comp_eq_map_comp _ (baseChange_inv_naturality_snd α γ.val H.val)
  have h₂ := sheafifyRestrictHom_naturality α
    (tensorMapRight H.val ((presheafExtendScalars α).map γ.val))
  have h₃ : (SheafOfModules.restrictScalars.{w} (ringSheafMap α)).map
        ((moduleSheafification O₂).map (tensorMapRight H.val
          ((presheafExtendScalars α).map γ.val))) ≫
      (SheafOfModules.restrictScalars.{w} (ringSheafMap α)).map
        ((moduleSheafification O₂).map (tensorMapRight H.val
          (toSheafifyVal ((presheafExtendScalars α).obj G'.val))))
      = (SheafOfModules.restrictScalars.{w} (ringSheafMap α)).map
          ((moduleSheafification O₂).map (tensorMapRight H.val
            (toSheafifyVal ((presheafExtendScalars α).obj G.val)))) ≫
        (SheafOfModules.restrictScalars.{w} (ringSheafMap α)).map
          ((moduleSheafification O₂).map (tensorMapRight H.val
            ((SheafOfModules.forget (commRingSheafToRingSheaf O₂)).map
              ((moduleSheafification O₂).map ((presheafExtendScalars α).map γ.val))))) := by
    refine map_comp_eq_map_comp _ (map_comp_eq_map_comp _ ?_)
    exact (tensorMapRight_comp H.val _ _).trans
      ((congrArg (fun z ↦ tensorMapRight H.val z)
        (toSheafifyVal_naturality ((presheafExtendScalars α).map γ.val))).trans
          (tensorMapRight_comp H.val _ _).symm)
  exact eq_of_three_squares h₁ h₂ h₃

/-- The `O₁`-linear cancellation of a base change is natural in the second tensor factor, at a
fixed sheaf `H` of `O₂`-modules. -/
theorem tensorBaseChangeLinearIso_naturality_snd (α : O₁ ⟶ O₂)
    {G G' : SheafOfModules.{w} (commRingSheafToRingSheaf O₁)} (γ : G ⟶ G')
    (H : SheafOfModules.{w} (commRingSheafToRingSheaf O₂)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O₁).obj
      ((SheafOfModules.restrictScalars.{w} (ringSheafMap α)).obj H)).map γ ≫
        (tensorBaseChangeLinearIso α G').hom.app H
      = (tensorBaseChangeLinearIso α G).hom.app H ≫
        (SheafOfModules.restrictScalars.{w} (ringSheafMap α)).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O₂).obj H).map
            ((extendScalars α).map γ)) :=
  tensorBaseChangeLinear_square α γ H

/-- The `O₁`-linear cancellation of a base change is natural in the second tensor factor, as an
equality of natural transformations. -/
theorem tensorBaseChangeLinearIso_hom_naturality_snd (α : O₁ ⟶ O₂)
    {G G' : SheafOfModules.{w} (commRingSheafToRingSheaf O₁)} (γ : G ⟶ G') :
    Functor.whiskerLeft (SheafOfModules.restrictScalars.{w} (ringSheafMap α))
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O₁).flip.map γ) ≫
        (tensorBaseChangeLinearIso α G').hom
      = (tensorBaseChangeLinearIso α G).hom ≫
        Functor.whiskerRight
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O₂).flip.map
            ((extendScalars α).map γ))
          (SheafOfModules.restrictScalars.{w} (ringSheafMap α)) :=
  NatTrans.ext (funext fun H ↦ tensorBaseChangeLinearIso_naturality_snd α γ H)

end BaseChange

/-! ### The underived identity of Stacks 08I6 in the second variable -/

section Tag08I6

open StacksPullbackFactorization

attribute [local instance]
  AlgebraicGeometry.SheafOfModules.isRightAdjoint_sheafPushforwardContinuous_commRingCat

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The identification of `f^*G` with the extension of scalars of `f⁻¹G` is natural in `G`. -/
lemma pullbackIsoExtendInverseImage_naturality
    (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    {G G' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)}
    (γ : G ⟶ G') :
    (Stacks.FlatChangeOfRings.extendScalars ((auxHomH f).fSharp)).map
          ((auxHomG f).pullbackTopos.map γ) ≫
        (pullbackIsoExtendInverseImage f G').hom
      = (pullbackIsoExtendInverseImage f G).hom ≫ f.pullbackTopos.map γ :=
  eq_of_two_squares
    ((extendScalarsIsoPullbackAuxHomH f).hom.naturality ((auxHomG f).pullbackTopos.map γ))
    ((pullbackFactorIso f).hom.naturality γ)

omit [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The underived identity of Stacks 08I6 is natural in the sheaf of `O'`-modules, at a fixed
sheaf `H` of `O`-modules. -/
theorem underivedTensorInverseImageLinearIso_naturality_snd
    (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    {G G' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)} (γ : G ⟶ G')
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).obj
      ((restrictToInvRing f).obj H)).map ((auxHomG f).pullbackTopos.map γ) ≫
        (underivedTensorInverseImageLinearIso f G').hom.app H
      = (underivedTensorInverseImageLinearIso f G).hom.app H ≫
        (restrictToInvRing f).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj H).map
            (f.pullbackTopos.map γ)) := by
  refine eq_of_two_squares (tensorBaseChangeLinearIso_naturality_snd ((auxHomH f).fSharp)
    ((auxHomG f).pullbackTopos.map γ) H) ?_
  exact map_comp_eq_map_comp (restrictToInvRing f)
    (map_comp_eq_map_comp
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj H)
      (pullbackIsoExtendInverseImage_naturality f γ))

omit [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The underived identity of Stacks 08I6 is natural in the sheaf of `O'`-modules, as an
equality of natural transformations. -/
theorem underivedTensorInverseImageLinearIso_hom_naturality_snd
    (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    {G G' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)}
    (γ : G ⟶ G') :
    Functor.whiskerLeft (restrictToInvRing f)
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).flip.map
            ((auxHomG f).pullbackTopos.map γ)) ≫
        (underivedTensorInverseImageLinearIso f G').hom
      = (underivedTensorInverseImageLinearIso f G).hom ≫
        Functor.whiskerRight
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).flip.map
            (f.pullbackTopos.map γ))
          (restrictToInvRing f) :=
  NatTrans.ext (funext fun H ↦ underivedTensorInverseImageLinearIso_naturality_snd f γ H)

end Tag08I6

end Stacks.Cohomology.MixedDerivedTensor

end
