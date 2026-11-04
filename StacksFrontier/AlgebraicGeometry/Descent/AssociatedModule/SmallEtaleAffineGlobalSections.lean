module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianTerminal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffinePushforward
public import
  StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSheafificationAffineSections
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.AffineSiteFinalObject

/-!
# Maps out of a quasi-coherent module on the small étale site of an affine scheme

Let `S` be a scheme.  A sheaf of modules `G` on the small étale site of `S` which is
cartesian between affine objects — for instance a quasi-coherent one, by Descent,
Proposition 03DX (2) — is determined by its sections over an affine terminal object `t` (the final
object, when `S` is affine): for every sheaf of modules `X`, a morphism `G ⟶ X` is the same as
a linear map from the sections of `G` over `t` to those of `X`.

The proof restricts to the affine objects, which form a dense subsite on which restriction of
sheaves of modules is fully faithful (`Stacks.DenseSubsiteModules.moduleRestriction`); there the
final object `S / S` is terminal and the restricted module is cartesian over every map to it, so
`Stacks.PresheafOfModules.bijective_app_of_isTerminal` applies.

## Main results

* `AlgebraicGeometry.SmallEtale.bijective_val_app_of_isTerminal_of_isCartesianOnAffines`
* `AlgebraicGeometry.SmallEtale.bijective_val_app_final_of_isCartesianOnAffines`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

open Stacks.PresheafOfModules

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A sheaf of modules on the small étale site of a scheme which is cartesian between affine
objects is determined by its sections over an affine terminal object**: evaluation at such an
object `t` is a bijection from morphisms out of it to linear maps out of its sections there. -/
theorem bijective_val_app_of_isTerminal_of_isCartesianOnAffines
    (G X : SheafOfModules.{u} (structureSheaf B S hS)) (hG : IsCartesianOnAffines B S hS G)
    {t : SmallEtale B S hS} (ht : IsTerminal t)
    (hta : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj t)) :
    Function.Bijective (fun u : G ⟶ X => u.val.app (op t)) := by
  have : (SmallAffineEtale.inclusion B S hS).IsDenseSubsite
      (SmallAffineEtale.topology B S hS) (topology B S hS) :=
    (SmallAffineEtale.inclusion_isSpecialCocontinuous B S hS).2
  let ρ := Stacks.DenseSubsiteModules.moduleRestriction (SmallAffineEtale.topology B S hS)
    (topology B S hS) (SmallAffineEtale.inclusion B S hS) (structureSheaf B S hS)
  have hρ : Function.Bijective (fun u : G ⟶ X => ρ.map u) :=
    (Functor.FullyFaithful.ofFullyFaithful ρ).map_bijective G X
  have hval : Function.Bijective (fun w : ρ.obj G ⟶ ρ.obj X => w.val) :=
    ⟨fun _ _ h => SheafOfModules.hom_ext h, fun w => ⟨⟨w⟩, rfl⟩⟩
  let M : PresheafOfModules.{u} (affineChartRings B S hS ⋙ forget₂ CommRingCat RingCat) :=
    (ρ.obj G).val
  let N : PresheafOfModules.{u} (affineChartRings B S hS ⋙ forget₂ CommRingCat RingCat) :=
    (ρ.obj X).val
  let ta : SmallAffineEtale B S hS := ⟨t, hta⟩
  have hta' : IsTerminal ta :=
    IsTerminal.ofUniqueHom
      (fun Y => (SmallAffineEtale.inclusion B S hS).preimage
        (ht.from ((SmallAffineEtale.inclusion B S hS).obj Y)))
      (fun _ _ => (SmallAffineEtale.inclusion B S hS).map_injective (ht.hom_ext _ _))
  have hM : ∀ V : SmallAffineEtale B S hS, IsIso (restrictionBaseChange M (hta'.from V).op) :=
    fun V => (ConcreteCategory.isIso_iff_bijective _).2
      (hG ((SmallAffineEtale.inclusion B S hS).map (hta'.from V)) V.property hta)
  exact (bijective_app_of_isTerminal M hta' hM (N := N)).comp (hval.comp hρ)

/-- `AlgebraicGeometry.SmallEtale.bijective_val_app_of_isTerminal_of_isCartesianOnAffines` with
the target a presheaf of modules which is a sheaf, and the source read as a presheaf of
modules. -/
theorem bijective_app_of_isTerminal_of_isCartesianOnAffines
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (X : PresheafOfModules.{u}
      (structureSheaf B S hS).obj) (hX : Presheaf.IsSheaf (topology B S hS) X.presheaf)
    (hG : IsCartesianOnAffines B S hS G)
    {t : SmallEtale B S hS} (ht : IsTerminal t)
    (hta : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj t)) :
    Function.Bijective (fun u : G.val ⟶ X => u.app (op t)) := by
  have hY := bijective_val_app_of_isTerminal_of_isCartesianOnAffines B S hS G ⟨X, hX⟩ hG ht hta
  have hwrap : Function.Bijective
      (fun u : G.val ⟶ X => (⟨u⟩ : G ⟶ (⟨X, hX⟩ : SheafOfModules.{u} _))) :=
    ⟨fun _ _ h => congrArg SheafOfModules.Hom.val h,
      fun (v : G ⟶ (⟨X, hX⟩ : SheafOfModules.{u} _)) => ⟨v.val, rfl⟩⟩
  exact hY.comp hwrap

/-- **A sheaf of modules on the small étale site of an affine scheme which is cartesian between
affine objects is determined by its global sections**: evaluation at the final object is a
bijection from morphisms out of it to linear maps out of its global sections. -/
theorem bijective_val_app_final_of_isCartesianOnAffines [AlgebraicGeometry.IsAffine S]
    (G X : SheafOfModules.{u} (structureSheaf B S hS)) (hG : IsCartesianOnAffines B S hS G) :
    Function.Bijective (fun u : G ⟶ X => u.val.app (op (final B S hS))) :=
  bijective_val_app_of_isTerminal_of_isCartesianOnAffines B S hS G X hG
    (finalIsTerminal B S hS) (SmallAffineEtale.final B S hS).property

/-- `AlgebraicGeometry.SmallEtale.exists_sheafOfModules_sections_iso` for a module over the ring of
sections of the structure sheaf, rather than of the commutative structure presheaf: every such
module is the sections over an affine terminal object of a sheaf of modules. -/
theorem exists_sheafOfModules_sections_iso_structureSheaf {t : SmallEtale B S hS}
    (ht : IsTerminal t) (hta : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj t))
    (T : ModuleCat.{u} ((structureSheaf B S hS).obj.obj (op t))) :
    ∃ L : SheafOfModules.{u} (structureSheaf B S hS), Nonempty (L.val.obj (op t) ≅ T) :=
  exists_sheafOfModules_sections_iso B S hS ht hta T

end AlgebraicGeometry.SmallEtale

end
