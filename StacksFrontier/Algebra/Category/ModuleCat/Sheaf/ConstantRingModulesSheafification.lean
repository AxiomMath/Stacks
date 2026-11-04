module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantRingModulesCompatibility

/-!
# Sheaves of `Λ`-modules as sheaves of modules over `Λ̲`, through sheafification

Let `(C, J)` be a site, `Λ` a ring and `α : Λ̲₀ ⟶ R` a locally bijective morphism from the
constant presheaf of rings with value `Λ` to a sheaf of rings `R`, for instance the
sheafification map. The library identifies sheaves of `R`-modules with sheaves of `Λ`-modules by
the equivalence `Stacks.ConstantRingModules.moduleSheafEquivalence` of
`StacksFrontier.CategoryTheory.Sites.Modules.ModuleSheavesAsConstantRingModules`, whose functor
`Stacks.ConstantRingModules.toModuleSheaf` restricts the scalars along `α`. This file describes
its inverse: it is the sheafification of the presheaf of modules over the constant presheaf of
rings underlying a sheaf of `Λ`-modules, and it commutes with restriction to a slice site.

## Main definitions

* `Stacks.ConstantRingModules.sheafificationFunctor`: a sheaf of `Λ`-modules, read as a presheaf
  of modules over the constant presheaf of rings and sheafified along `α`.
* `Stacks.ConstantRingModules.moduleSheafEquivalenceInverseIso`: the inverse of
  `moduleSheafEquivalence` is `sheafificationFunctor`.
* `Stacks.ConstantRingModules.moduleSheafEquivalenceInverseOverIso`: the inverse of
  `moduleSheafEquivalence` commutes with restriction to a slice site `C/U`.
* `Stacks.ConstantRingModules.sheafificationFunctorOverIso`: the same for
  `sheafificationFunctor`.

## Main results

* `Stacks.ConstantRingModules.isIso_sheafificationAdjunction_unit_app_ofFunctor`: the unit of
  the sheafification adjunction of presheaves of modules is invertible at a sheaf of
  `Λ`-modules, its underlying abelian presheaf being already a sheaf.

## Implementation notes

The slice square for the functors, `Stacks.ConstantRingModules.toModuleSheafOverIso`, has
identity components; the one for the inverses is its conjugate by the units and counits of the
two equivalences. `Stacks.ConstantRingModules.toModuleSheafInvOverIso` of
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantRingDerivedTensorRestriction` is the
same square, obtained as a mate, but only for a site, ring and modules in one universe and under
the derived-category hypotheses of that file; the square here keeps the universes of
`moduleSheafEquivalence` independent and assumes nothing beyond its hypotheses.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits

universe a r v u

namespace Stacks.ConstantRingModules

open Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] (Λ : Type r) [Ring Λ]
  (J : GrothendieckTopology C) {R : Sheaf J RingCat.{r}}
  (α : constRing (C := C) Λ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]

/-- A sheaf of `Λ`-modules read as a sheaf of modules over a sheaf of rings `R` receiving a
locally bijective map `α` from the constant presheaf of rings with value `Λ`: the sheafification
along `α` of its presheaf of modules over the constant presheaf of rings. -/
def sheafificationFunctor : Sheaf J (ModuleCat.{a} Λ) ⥤ _root_.SheafOfModules.{a} R :=
  sheafToPresheaf J (ModuleCat.{a} Λ) ⋙ ofFunctor Λ ⋙
    _root_.PresheafOfModules.sheafification α

variable [J.HasSheafCompose (forget₂ (ModuleCat.{a} Λ) AddCommGrpCat.{a})]

/-- The unit of the sheafification adjunction of presheaves of modules along `α` is invertible
at the presheaf of modules over the constant presheaf of rings underlying a sheaf of
`Λ`-modules: on underlying abelian presheaves it is `toSheafify`, at a presheaf which is
already a sheaf. -/
instance isIso_sheafificationAdjunction_unit_app_ofFunctor (P : Sheaf J (ModuleCat.{a} Λ)) :
    IsIso ((_root_.PresheafOfModules.sheafificationAdjunction α).unit.app
      ((ofFunctor Λ).obj P.obj)) := by
  have hP : Presheaf.IsSheaf J ((ofFunctor Λ).obj P.obj).presheaf :=
    ((sheafCompose J (forget₂ (ModuleCat.{a} Λ) AddCommGrpCat.{a})).obj P).property
  have : IsIso ((_root_.PresheafOfModules.toPresheaf _).map
      ((_root_.PresheafOfModules.sheafificationAdjunction α).unit.app
        ((ofFunctor Λ).obj P.obj))) := by
    rw [_root_.PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact isIso_toSheafify J hP
  exact isIso_of_reflects_iso _ (_root_.PresheafOfModules.toPresheaf _)

/-- Restricting the scalars of the sheafification of a sheaf of `Λ`-modules back along `α` gives
the sheaf of `Λ`-modules, naturally: the inverse of the unit of the sheafification adjunction. -/
def sheafificationFunctorCompToModuleSheafIso :
    sheafificationFunctor.{a} Λ J α ⋙ toModuleSheaf.{a} Λ J α ≅ 𝟭 (Sheaf J (ModuleCat.{a} Λ)) :=
  let Φ := sheafToPresheaf J (ModuleCat.{a} Λ) ⋙ ofFunctor.{a} Λ
  let η := Functor.whiskerLeft Φ (_root_.PresheafOfModules.sheafificationAdjunction.{a} α).unit
  haveI : ∀ P, IsIso (η.app P) := fun P ↦
    isIso_sheafificationAdjunction_unit_app_ofFunctor.{a} Λ J α P
  haveI : IsIso η := NatIso.isIso_of_isIso_app _
  ((fullyFaithfulSheafToPresheaf J (ModuleCat.{a} Λ)).whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (sheafificationFunctor.{a} Λ J α)
        (toModuleSheafCompSheafToPresheafIso.{a} Λ J α) ≪≫
      Functor.isoWhiskerRight (asIso η).symm (toFunctor.{a} Λ) ≪≫
      Functor.isoWhiskerLeft (sheafToPresheaf J (ModuleCat.{a} Λ))
        (ofFunctorCompToFunctorIso.{a} Λ) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

/-- **The inverse of `Stacks.ConstantRingModules.moduleSheafEquivalence` is sheafification**: it
is isomorphic to `Stacks.ConstantRingModules.sheafificationFunctor`, which reads a sheaf of
`Λ`-modules as a presheaf of modules over the constant presheaf of rings and sheafifies it
along `α`. -/
def moduleSheafEquivalenceInverseIso :
    (moduleSheafEquivalence.{a} Λ J α).inverse ≅ sheafificationFunctor.{a} Λ J α :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (sheafificationFunctorCompToModuleSheafIso.{a} Λ J α).symm _ ≪≫
    Functor.isoWhiskerLeft (sheafificationFunctor.{a} Λ J α)
      (moduleSheafEquivalence.{a} Λ J α).unitIso.symm ≪≫
    Functor.rightUnitor _

section Slice

variable (U : C) [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{a}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{a}]
  [(J.over U).HasSheafCompose (forget₂ (ModuleCat.{a} Λ) AddCommGrpCat.{a})]

/-- **The inverse of `Stacks.ConstantRingModules.moduleSheafEquivalence` commutes with
restriction to a slice site.** A sheaf of `Λ`-modules, read as a sheaf of `R`-modules and
restricted to `C/U`, is its restriction read as a sheaf of `R|_U`-modules, for the restricted
comparison `Stacks.ConstantRingModules.overRingMap`. This is the conjugate of the square
`Stacks.ConstantRingModules.toModuleSheafOverIso` for the functors. -/
def moduleSheafEquivalenceInverseOverIso :
    (moduleSheafEquivalence.{a} Λ J α).inverse ⋙ _root_.SheafOfModules.overFunctor.{a} R U ≅
      J.overPullback (ModuleCat.{a} Λ) U ⋙
        (moduleSheafEquivalence.{a} Λ (J.over U) (overRingMap Λ J α U)).inverse :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _
      (moduleSheafEquivalence.{a} Λ (J.over U) (overRingMap Λ J α U)).unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (moduleSheafEquivalence.{a} Λ J α).inverse
      (toModuleSheafOverIso.{a} Λ J α U).symm) _ ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _).symm _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight
      (moduleSheafEquivalence.{a} Λ J α).counitIso _) _ ≪≫
    Functor.isoWhiskerRight (Functor.leftUnitor _) _

/-- **Sheafification of sheaves of `Λ`-modules commutes with restriction to a slice site**, read
off `Stacks.ConstantRingModules.moduleSheafEquivalenceInverseOverIso` through
`Stacks.ConstantRingModules.moduleSheafEquivalenceInverseIso`. -/
def sheafificationFunctorOverIso :
    sheafificationFunctor.{a} Λ J α ⋙ _root_.SheafOfModules.overFunctor.{a} R U ≅
      J.overPullback (ModuleCat.{a} Λ) U ⋙
        sheafificationFunctor.{a} Λ (J.over U) (overRingMap Λ J α U) :=
  Functor.isoWhiskerRight (moduleSheafEquivalenceInverseIso.{a} Λ J α).symm _ ≪≫
    moduleSheafEquivalenceInverseOverIso.{a} Λ J α U ≪≫
    Functor.isoWhiskerLeft _ (moduleSheafEquivalenceInverseIso.{a} Λ (J.over U)
      (overRingMap Λ J α U))

end Slice

end Stacks.ConstantRingModules

end
