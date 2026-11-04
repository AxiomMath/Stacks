module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison
public import StacksCore.Tactic.StacksAttribute

/-! # Change of rings preserves local isomorphisms, and base change of a tensor product sheaf

Let `θ : A₁ ⟶ A₂` be a morphism of presheaves of commutative rings on a site `(C, J)` whose
underlying presheaves of rings are both sheaves. The change-of-rings functor
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ`, i.e. `G ↦ A₂ ⊗_{p,A₁} G`, carries a
*local isomorphism* of presheaves of `A₁`-modules — a morphism which sheafification inverts,
equivalently one which is locally injective and locally surjective — to a local isomorphism of
presheaves of `A₂`-modules. This is the fact that makes extension of scalars for *sheaves* of
modules compatible with sheafification, and with it the sheaf-level base change of a tensor
product follows from the presheaf-level one of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsTensor`:

`A₂ ⊗_{A₁} (F ⊗_{A₁} G) ≅ (A₂ ⊗_{A₁} F) ⊗_{A₂} (A₂ ⊗_{A₁} G)` for sheaves of `A₁`-modules.

This is step 4 of the chain of bijections recorded in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImageTensor`, at the level of sheaves:
the pullback of Stacks 03D6 part (2) is the inverse image followed by extension of scalars, so
this says the second half of that pullback is monoidal.

## Main definitions

* `Stacks.PresheafOfModules.ChangeOfRings.sheafifyChangeOfRingsAdjunction`: change of rings
  followed by sheafification is left adjoint to restriction of scalars of the underlying
  presheaf of modules of a sheaf.
* `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsUnit`: the change-of-rings image of a
  sheafification unit.
* `Stacks.Sheaves.RingedToposModules.extendScalarsSheafifyIso`: extension of scalars for
  sheaves of modules computes the sheafification of a change of rings, i.e.
  `(A₂ ⊗_{p,A₁} P)^# ≅ A₂ ⊗_{A₁} P^#`.
* `Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso`: **base change of a tensor
  product of sheaves of modules**, `A₂ ⊗_{A₁} (F ⊗_{A₁} G) ≅ (A₂ ⊗_{A₁} F) ⊗_{A₂}
  (A₂ ⊗_{A₁} G)`.

## Main results

* `Stacks.PresheafOfModules.ChangeOfRings.localIso_changeOfRings_map`: change of rings preserves
  local isomorphisms.
* `Stacks.PresheafOfModules.ChangeOfRings.localIso_iff_isIso_sheafification`: a morphism of
  presheaves of modules is a local isomorphism if and only if sheafification inverts it. This is
  Mathlib's `PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms`, read at
  one morphism.
* `Stacks.PresheafOfModules.ChangeOfRings.localIso_sheafificationUnit`: the unit of the
  sheafification of presheaves of modules is a local isomorphism.

## Implementation notes

The proof that change of rings preserves local isomorphisms is by the universal property, not
by a computation on sections, and in particular it does not redo the work of Tag 05NA. A
morphism `g` is inverted by sheafification exactly when precomposition with `g` is bijective on
morphisms into every sheaf of modules, and the composite functor `sheafification ∘ changeOfRings`
is a left adjoint whose right adjoint takes values in presheaves of modules which are sheaves —
restriction of scalars does not change the underlying presheaf of abelian groups. So
`Adjunction.homEquiv_naturality_left` turns precomposition with the change-of-rings image of `u`
into precomposition with `u` itself, which is bijective into a sheaf by Mathlib's
`PresheafOfModules.homEquivOfIsLocallyBijective`; `CategoryTheory.isIso_of_coyoneda_map_bijective`
then concludes.

Two spellings of one object have to be crossed, and both times the move is a *term*-level
coercion, which checks at default transparency, rather than a `rw` or a binder ascription,
which do not:

* the unit of the sheafification adjunction has target
  `(SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).obj P^#` rather than
  `(P^#).val`; `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsUnit` is declared at the
  second type and elaborated from the first, which works because
  `PresheafOfModules.restrictScalars (𝟙 R)` is definitionally the identity functor (as Mathlib's
  own `inferInstanceAs (𝟭 _).Full` instance for it records);
* `Stacks.SheafOfModules.TensorSheafification.structureSheaf A h` and
  `Stacks.Sheaves.RingedToposModules.commRingSheaf J A h` are two names for the sheaf of rings
  `⟨A ⋙ forget₂ CommRingCat RingCat, h⟩`, so `Stacks.SheafOfModules.Tensor.sheafTensor` and
  `Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso` are available for sheaves of
  modules over the second spelling without any comparison map.

The tensor product of sheaves of modules used here is `Stacks.SheafOfModules.Tensor.sheafTensor`,
the sheafification of the objectwise tensor product.

## References

* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Stacks.Sheaves.RingedToposModules

universe w v u

/-! ## Local isomorphisms and change of rings -/

namespace Stacks.PresheafOfModules.ChangeOfRings

section LocalIso

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- A morphism of presheaves of modules over a presheaf of commutative rings whose underlying
presheaf of rings is a sheaf is a local isomorphism — i.e. locally bijective on the underlying
presheaves of abelian groups — if and only if sheafification inverts it. -/
theorem localIso_iff_isIso_sheafification {A : Cᵒᵖ ⥤ CommRingCat.{w}}
    (h : Presheaf.IsSheaf J (ringPresheaf A))
    {P Q : PresheafOfModules.{w} (ringPresheaf A)} (g : P ⟶ Q) :
    J.W ((PresheafOfModules.toPresheaf (ringPresheaf A)).map g) ↔
      IsIso ((PresheafOfModules.sheafification (R := commRingSheaf J A h) (𝟙 _)).map g) := by
  have e := PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (J := J) (𝟙 (commRingSheaf J A h).obj)
  have key : (J.W.inverseImage (PresheafOfModules.toPresheaf (commRingSheaf J A h).obj)) g ↔
      ((MorphismProperty.isomorphisms (SheafOfModules.{w} (commRingSheaf J A h))).inverseImage
        (PresheafOfModules.sheafification (R := commRingSheaf J A h) (𝟙 _))) g := by rw [e]
  exact key

/-- The unit of the sheafification of presheaves of modules is a local isomorphism: on
underlying presheaves of abelian groups it is the sheafification unit. -/
theorem localIso_sheafificationUnit {A : Cᵒᵖ ⥤ CommRingCat.{w}}
    (h : Presheaf.IsSheaf J (ringPresheaf A)) (P : PresheafOfModules.{w} (ringPresheaf A)) :
    J.W ((PresheafOfModules.toPresheaf (ringPresheaf A)).map
      ((PresheafOfModules.sheafificationAdjunction
        (R := commRingSheaf J A h) (𝟙 _)).unit.app P)) := by
  rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact J.W_toSheafify _

/-- Change of rings along `θ : A₁ ⟶ A₂` followed by sheafification of presheaves of
`A₂`-modules is left adjoint to restriction of scalars of the underlying presheaf of modules of
a sheaf: the composite of the adjunction of Tag 03CU with the sheafification adjunction. -/
def sheafifyChangeOfRingsAdjunction {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)
    (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂)) :
    changeOfRings θ ⋙
        PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _) ⊣
      (SheafOfModules.forget (commRingSheaf J A₂ h₂) ⋙
          PresheafOfModules.restrictScalars (𝟙 (commRingSheaf J A₂ h₂).obj)) ⋙
        restrictScalars θ :=
  (changeOfRingsAdjunction θ).comp
    (PresheafOfModules.sheafificationAdjunction (R := commRingSheaf J A₂ h₂) (𝟙 _))

/-- **Change of rings preserves local isomorphisms.** If `u` is a morphism of presheaves of
`A₁`-modules which sheafification inverts, then `A₂ ⊗_{p,A₁} u` is a morphism of presheaves of
`A₂`-modules which sheafification inverts. Equivalently, `sheafification ∘ changeOfRings θ`
factors through sheafification of presheaves of `A₁`-modules, which is what makes extension of
scalars for sheaves of modules compatible with sheafification. -/
theorem localIso_changeOfRings_map {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)
    (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂))
    {P Q : PresheafOfModules.{w} (ringPresheaf A₁)} (u : P ⟶ Q)
    (hu : J.W ((PresheafOfModules.toPresheaf (ringPresheaf A₁)).map u)) :
    J.W ((PresheafOfModules.toPresheaf (ringPresheaf A₂)).map ((changeOfRings θ).map u)) := by
  have := hu.isLocallyInjective
  have := hu.isLocallySurjective
  have key : IsIso ((changeOfRings θ ⋙
      PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map u) := by
    let adj := sheafifyChangeOfRingsAdjunction θ h₂
    refine isIso_of_coyoneda_map_bijective _ fun T ↦ ?_
    have hsheaf : Presheaf.IsSheaf J
        (((SheafOfModules.forget (commRingSheaf J A₂ h₂) ⋙
          PresheafOfModules.restrictScalars (𝟙 (commRingSheaf J A₂ h₂).obj)) ⋙
            restrictScalars θ).obj T).presheaf := T.isSheaf
    let ψ := PresheafOfModules.homEquivOfIsLocallyBijective (f := u) hsheaf
    have hcomp : (fun (x : _ ⟶ T) ↦ (changeOfRings θ ⋙
        PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map u ≫ x) =
          (adj.homEquiv P T).symm ∘ ψ ∘ (adj.homEquiv Q T) := by
      funext x
      refine ((Equiv.symm_apply_eq _).2 ?_).symm
      rw [adj.homEquiv_naturality_left u x]
      rfl
    rw [hcomp]
    exact (adj.homEquiv P T).symm.bijective.comp
      (ψ.bijective.comp (adj.homEquiv Q T).bijective)
  rw [localIso_iff_isIso_sheafification h₂]
  exact key

variable {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (ringPresheaf A₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂))

/-- The change-of-rings image of the sheafification unit of a presheaf of `A₁`-modules, read as
a morphism into the change of rings of the underlying presheaf of modules of the associated
sheaf. The two possible targets differ only by a restriction of scalars along an identity. -/
def changeOfRingsUnit (P : PresheafOfModules.{w} (ringPresheaf A₁)) :
    (changeOfRings θ).obj P ⟶ (changeOfRings θ).obj
      ((PresheafOfModules.sheafification (R := commRingSheaf J A₁ h₁) (𝟙 _)).obj P).val :=
  (changeOfRings θ).map
    ((PresheafOfModules.sheafificationAdjunction (R := commRingSheaf J A₁ h₁) (𝟙 _)).unit.app P)

/-- Sheafification of presheaves of `A₂`-modules inverts the change-of-rings image of a
sheafification unit. -/
theorem isIso_sheafification_map_changeOfRingsUnit
    (P : PresheafOfModules.{w} (ringPresheaf A₁)) :
    IsIso ((PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).map
      (changeOfRingsUnit θ h₁ P)) := by
  rw [← localIso_iff_isIso_sheafification h₂]
  exact localIso_changeOfRings_map θ h₂ _ (localIso_sheafificationUnit h₁ P)

end LocalIso

end Stacks.PresheafOfModules.ChangeOfRings

/-! ## Base change of a tensor product of sheaves of modules -/

namespace Stacks.Sheaves.RingedToposModules

open Stacks.PresheafOfModules.ChangeOfRings

section ExtendScalars

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (ringPresheaf A₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf A₂))

/-- **Extension of scalars commutes with sheafification.** The sheafification of the
change-of-rings presheaf `A₂ ⊗_{p,A₁} P` is the extension of scalars of the sheafification of
`P`: `(A₂ ⊗_{p,A₁} P)^# ≅ A₂ ⊗_{A₁} P^#`. -/
def extendScalarsSheafifyIso (P : PresheafOfModules.{w} (ringPresheaf A₁)) :
    (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).obj
        ((changeOfRings θ).obj P) ≅
      (extendScalars J θ h₁ h₂).obj
        ((PresheafOfModules.sheafification (R := commRingSheaf J A₁ h₁) (𝟙 _)).obj P) :=
  @asIso _ _ _ _ _ (isIso_sheafification_map_changeOfRingsUnit θ h₁ h₂ P)

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- **Base change of a tensor product of sheaves of modules.** Extension of scalars along a
morphism `θ : A₁ ⟶ A₂` of presheaves of commutative rings whose underlying presheaves of rings
are sheaves carries the tensor product sheaf over `A₁` to the tensor product sheaf over `A₂`:
`A₂ ⊗_{A₁} (F ⊗_{A₁} G) ≅ (A₂ ⊗_{A₁} F) ⊗_{A₂} (A₂ ⊗_{A₁} G)`.

This is step 4 of the chain of Tag 03EL at the level of sheaves of modules. -/
def extendScalarsTensorIso (F G : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) :
    (extendScalars J θ h₁ h₂).obj ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨A₁,
        Presheaf.isSheaf_of_isSheaf_comp _ A₁
        (forget₂ CommRingCat RingCat) h₁⟩).obj F).obj G))
      ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨A₂, Presheaf.isSheaf_of_isSheaf_comp _ A₂
        (forget₂ CommRingCat RingCat) h₂⟩).obj ((extendScalars J θ h₁ h₂).obj F)).obj
            ((extendScalars J θ h₁ h₂).obj G)) :=
  (extendScalarsSheafifyIso θ h₁ h₂ (F.val ⊗ G.val)).symm ≪≫
    (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).mapIso
      (changeOfRingsTensorObjIso θ F.val G.val) ≪≫
    Stacks.SheafOfModules.TensorSheafification.tensorSheafifyIso A₂ h₂ ((changeOfRings θ).obj F.val)
      ((changeOfRings θ).obj G.val)

end ExtendScalars

end Stacks.Sheaves.RingedToposModules

end
