module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftDenseSubsite

/-!
# Pullback of sheaves of modules commutes with raising the universe of the rings

Let `F : C ⥤ D` be a continuous functor between sites, let `O₀` and `O` be sheaves of commutative
rings on `C` and `D` with sections in `Type r`, and let `φ : O₀ ⟶ F_*O` be a morphism of sheaves
of rings.  Sheaves of modules with sections in `Type (max r z)` over `O₀` are the same thing as
sheaves of modules over the universe lift `U ↦ ULift (O₀(U))`, by restriction of scalars along
`ULift.ringEquiv` (`Stacks.UniverseLift.RingTransport.sheafEquivalence` for
`Stacks.UniverseLift.uliftRingTransport`), and similarly over `O`.

This file shows that these identifications carry the pushforward along `φ` to the pushforward
along the lifted morphism `φ↑ : O₀↑ ⟶ F_*O↑`, and hence, by uniqueness of left adjoints, the
pullback `φ^*` of Stacks 03D6 (2) to the pullback `φ↑^*`.  The point is that the second pullback
has its sheaves of rings and of modules in the *same* universe, which is the setting in which
the exactness results of the library (Stacks 04JC) are stated, while the first is the one that
arises when the modules have to live in a universe containing a large site — the naive cotangent
complex of a morphism of algebraic spaces, say, whose sections lie in `Type (u + 1)` while the
structure rings lie in `Type u`.

## Main definitions

* `Stacks.UniverseLift.sheafRingULift`: the universe lift of a sheaf of commutative rings.
* `Stacks.UniverseLift.ringTransportEquivalence`: sheaves of modules over `O` are sheaves of
  modules over its universe lift.
* `Stacks.UniverseLift.liftedRingHom`: the lifted morphism `φ↑ : O₀↑ ⟶ F_*O↑`.
* `Stacks.UniverseLift.pushforwardRingULiftIso`: the identifications carry `φ_*` to `φ↑_*`.
* `Stacks.UniverseLift.pullbackRingULiftIso`: the identifications carry `φ^*` to `φ↑^*`.

## Main results

* `Stacks.UniverseLift.isRightAdjoint_pushforward_liftedRingHom`: `φ↑_*` has a left adjoint as
  soon as `φ_*` has.
* `Stacks.UniverseLift.preservesFiniteLimits_pullback_of_liftedRingHom`: `φ^*` is left exact as
  soon as `φ↑^*` is.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe m z r v₁ u₁ v₂ u₂

namespace Stacks.UniverseLift

section Lift

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

/-- **The universe lift of a sheaf of commutative rings**: `U ↦ ULift (O(U))`. -/
abbrev sheafRingULift (O : Sheaf J CommRingCat.{r}) : Sheaf J CommRingCat.{max r z} :=
  ⟨O.obj ⋙ AlgebraicGeometry.SheafOfModules.commRingCatULift.{r, z},
    isSheaf_comp_commRingCatULift _ O.property⟩

/-- **Sheaves of modules over a sheaf of commutative rings are sheaves of modules over its
universe lift**, by restriction of scalars along `ULift.ringEquiv`; the sections and the
restriction maps do not change. -/
abbrev ringTransportEquivalence (O : Sheaf J CommRingCat.{r}) :
    _root_.SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf O) ≌
      _root_.SheafOfModules.{m}
        (Stacks.SheafOfModules.Tensor.ringSheaf (sheafRingULift.{z} O)) :=
  (uliftRingTransport.{z} O.obj).sheafEquivalence
    (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
    (R' := Stacks.SheafOfModules.Tensor.ringSheaf (sheafRingULift.{z} O))

end Lift

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D} [F.IsContinuous J K]
  {O₀ : Sheaf J CommRingCat.{r}} {O : Sheaf K CommRingCat.{r}}
  (φ : Stacks.SheafOfModules.Tensor.ringSheaf O₀ ⟶
    (F.sheafPushforwardContinuous RingCat.{r} J K).obj (Stacks.SheafOfModules.Tensor.ringSheaf O))

/-- **The lifted morphism `φ↑ : O₀↑ ⟶ F_*O↑`**: `φ` on the lifted sections. -/
def liftedRingHom :
    Stacks.SheafOfModules.Tensor.ringSheaf (sheafRingULift.{z} O₀) ⟶
      (F.sheafPushforwardContinuous RingCat.{max r z} J K).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (sheafRingULift.{z} O)) :=
  ⟨{ app U := RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((φ.hom.app U).hom.comp ULift.ringEquiv.toRingHom))
     naturality {U V} f := by
       ext x
       exact congrArg ULift.up (ConcreteCategory.congr_hom (φ.hom.naturality f) x.down) }⟩

/-- The component of `liftedRingHom φ` at `U` sends `ULift.up a` to `ULift.up (φ_U a)`. -/
theorem liftedRingHom_app_apply (U : Cᵒᵖ) (x : ULift.{z} (O₀.obj.obj U)) :
    ((liftedRingHom.{z} φ).hom.app U).hom x = ULift.up ((φ.hom.app U).hom x.down) :=
  rfl

/-- The component at `M` of `pushforwardRingULiftIso`: both sides have the sections of `M` over
`F(U)` as sections over `U`, with the same action of `ULift (O₀(U))`. -/
def pushforwardRingULiftObjIso
    (M : _root_.SheafOfModules.{max r z m} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (ringTransportEquivalence.{max r z m, z} O₀).functor.obj
        ((_root_.SheafOfModules.pushforward.{max r z m} φ).obj M) ≅
      (_root_.SheafOfModules.pushforward.{max r z m} (liftedRingHom.{z} φ)).obj
        ((ringTransportEquivalence.{max r z m, z} O).functor.obj M) :=
  (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (fun _ _ _ => rfl))

/-- **The identifications of modules over `O₀`, `O` with modules over their universe lifts carry
the pushforward along `φ` to the pushforward along the lifted morphism.** -/
def pushforwardRingULiftIso :
    _root_.SheafOfModules.pushforward.{max r z m} φ ⋙
        (ringTransportEquivalence.{max r z m, z} O₀).functor ≅
      (ringTransportEquivalence.{max r z m, z} O).functor ⋙
        _root_.SheafOfModules.pushforward.{max r z m} (liftedRingHom.{z} φ) :=
  NatIso.ofComponents (pushforwardRingULiftObjIso.{m, z} φ)
    (fun _ => _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ => rfl))

/-- The pushforward along the lifted morphism, written as a conjugate of the pushforward
along `φ`. -/
def pushforwardLiftedRingHomIso :
    _root_.SheafOfModules.pushforward.{max r z m} (liftedRingHom.{z} φ) ≅
      (ringTransportEquivalence.{max r z m, z} O).inverse ⋙
        _root_.SheafOfModules.pushforward.{max r z m} φ ⋙
          (ringTransportEquivalence.{max r z m, z} O₀).functor :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (ringTransportEquivalence.{max r z m, z} O).counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (pushforwardRingULiftIso.{m, z} φ).symm

/-- **The pushforward along the lifted morphism has a left adjoint as soon as the pushforward
along `φ` has**: it is conjugate to it by equivalences. -/
theorem isRightAdjoint_pushforward_liftedRingHom
    [(_root_.SheafOfModules.pushforward.{max r z m} φ).IsRightAdjoint] :
    (_root_.SheafOfModules.pushforward.{max r z m} (liftedRingHom.{z} φ)).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (pushforwardLiftedRingHomIso.{m, z} φ).symm

variable [(_root_.SheafOfModules.pushforward.{max r z m} φ).IsRightAdjoint]

/-- **The identifications of modules over `O₀`, `O` with modules over their universe lifts carry
the pullback along `φ` to the pullback along the lifted morphism**, by uniqueness of left
adjoints: the conjugate `T₀⁻¹ ⋙ φ^* ⋙ T` is left adjoint to `T⁻¹ ⋙ φ_* ⋙ T₀`, which is `φ↑_*`. -/
def pullbackRingULiftIso :
    have := isRightAdjoint_pushforward_liftedRingHom.{m, z} φ
    _root_.SheafOfModules.pullback.{max r z m} φ ≅
      (ringTransportEquivalence.{max r z m, z} O₀).functor ⋙
        _root_.SheafOfModules.pullback.{max r z m} (liftedRingHom.{z} φ) ⋙
          (ringTransportEquivalence.{max r z m, z} O).inverse :=
  have := isRightAdjoint_pushforward_liftedRingHom.{m, z} φ
  let T₀ := ringTransportEquivalence.{max r z m, z} O₀
  let T := ringTransportEquivalence.{max r z m, z} O
  let adj₁ : T₀.inverse ⋙ _root_.SheafOfModules.pullback.{max r z m} φ ⋙ T.functor ⊣
      T.inverse ⋙ _root_.SheafOfModules.pushforward.{max r z m} φ ⋙ T₀.functor :=
    T₀.symm.toAdjunction.comp
      ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{max r z m} φ).comp T.toAdjunction)
  let adj₂ := (_root_.SheafOfModules.pullbackPushforwardAdjunction.{max r z m}
    (liftedRingHom.{z} φ)).ofNatIsoRight (pushforwardLiftedRingHomIso.{m, z} φ)
  let e := adj₁.leftAdjointUniq adj₂
  (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ T.unitIso ≪≫
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight T₀.unitIso _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft T₀.functor
      ((Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          ((Functor.associator _ _ _) ≪≫ e) T.inverse)

/-- **Left exactness of `φ^*` follows from left exactness of `φ↑^*`**, the pullback along the
lifted morphism, whose rings and modules share a universe. -/
theorem preservesFiniteLimits_pullback_of_liftedRingHom
    (h : have := isRightAdjoint_pushforward_liftedRingHom.{m, z} φ
      PreservesFiniteLimits
        (_root_.SheafOfModules.pullback.{max r z m} (liftedRingHom.{z} φ))) :
    PreservesFiniteLimits (_root_.SheafOfModules.pullback.{max r z m} φ) :=
  have := isRightAdjoint_pushforward_liftedRingHom.{m, z} φ
  have := h
  preservesFiniteLimits_of_natIso (pullbackRingULiftIso.{m, z} φ).symm

end Stacks.UniverseLift

end
