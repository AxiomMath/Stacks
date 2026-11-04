module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackEssentiallySmallUnivLE
public import Mathlib.CategoryTheory.Adjunction.Mates
public import
  StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticRestrictionQuasiCoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UliftFunctorSheafification

/-!
# Pullback of presheaves of modules commutes with the universe lift

Let `φ : S ⟶ F.op ⋙ R` be a morphism of presheaves of rings along a functor `F : C ⥤ D`. The
pullback `PresheafOfModules.pullback φ` exists in every module universe `v` in which the source
site is essentially small, and the universe lift `PresheafOfModules.uliftFunctor` commutes with
the pushforward on the nose. This file shows that it commutes with the pullback as well: the mate
`pullback φ (M↑) ⟶ (pullback φ M)↑` of the identity square of pushforwards is an isomorphism.

## Main definitions

* `PresheafOfModules.pushforwardULiftIso`: the universe lift commutes with pushforward.
* `PresheafOfModules.pullbackULiftHom`: the comparison `pullback φ (M↑) ⟶ (pullback φ M)↑`.
* `PresheafOfModules.uliftFreeObjShrinkIso`: the universe lift of a free presheaf of modules is
  the free presheaf of modules in the larger universe.

## Main results

* `PresheafOfModules.bijective_uliftFunctor_eval`: a corepresentation of evaluation survives the
  universe lift.
* `PresheafOfModules.isIso_pullbackULiftHom_app_freeObjShrink`: the comparison is an isomorphism
  on free presheaves of modules on representables.
* `PresheafOfModules.isIso_pullbackULiftHom_app`: the comparison is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v t v₁ v₂ u₁ u₂ r

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{r}} {S : Cᵒᵖ ⥤ RingCat.{r}} (φ : S ⟶ F.op ⋙ R)

/-- The universe lift commutes with the pushforward of presheaves of modules, on the nose. -/
def pushforwardULiftIso :
    pushforward.{v} φ ⋙ uliftFunctor.{_, _, _, _, t} ≅
      uliftFunctor.{_, _, _, _, t} ⋙ pushforward.{max v t} φ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

section Mate

variable [(pushforward.{v} φ).IsRightAdjoint] [(pushforward.{max v t} φ).IsRightAdjoint]

/-- The comparison `pullback φ (M↑) ⟶ (pullback φ M)↑` between pulling back the universe lift
and lifting the pullback: the mate of `PresheafOfModules.pushforwardULiftIso`. -/
def pullbackULiftHom :
    uliftFunctor.{_, _, _, _, t} ⋙ pullback.{max v t} φ ⟶
      pullback.{v} φ ⋙ uliftFunctor.{_, _, _, _, t} :=
  (mateEquiv (pullbackPushforwardAdjunction.{v} φ)
    (pullbackPushforwardAdjunction.{max v t} φ)).symm (pushforwardULiftIso.{v, t} φ).hom

/-- The adjoint transpose of `pullbackULiftHom` at `M` is the lift of the unit at `M`. -/
theorem homEquiv_pullbackULiftHom_app (M : PresheafOfModules.{v} S) :
    (pullbackPushforwardAdjunction.{max v t} φ).homEquiv _ _
        ((pullbackULiftHom.{v, t} φ).app M) =
      uliftFunctor.{_, _, _, _, t}.map ((pullbackPushforwardAdjunction.{v} φ).unit.app M) := by
  rw [Adjunction.homEquiv_unit]
  have h := unit_mateEquiv_symm (pullbackPushforwardAdjunction.{v} φ)
    (pullbackPushforwardAdjunction.{max v t} φ) (pushforwardULiftIso.{v, t} φ).hom M
  simp only [pushforwardULiftIso] at h
  exact h.symm

end Mate

section FreeULift

variable {E : Type u₂} [Category.{v₂} E] (T : Eᵒᵖ ⥤ RingCat.{r}) [∀ X, Small.{v} (T.obj X)]
  (P : Eᵒᵖ ⥤ Type v₁) [∀ X, Small.{v} (P.obj X)]

/-- The free presheaf of modules on `P` in the module universe `max v t`, its smallness read off
from smallness in `v`. -/
abbrev freeObjShrinkMax : PresheafOfModules.{max v t} T :=
  @freeObjShrink _ _ T (fun X => (small_lift (T.obj X) : Small.{max v t} (T.obj X))) P
    (fun X => (small_lift (P.obj X) : Small.{max v t} (P.obj X)))

/-- The generator of `freeObjShrinkMax` at `i`. -/
abbrev freeGenShrinkMax {X : Eᵒᵖ} (i : P.obj X) : (freeObjShrinkMax.{v, t} T P).obj X :=
  @freeGenShrink _ _ T (fun X => (small_lift (T.obj X) : Small.{max v t} (T.obj X))) P
    (fun X => (small_lift (P.obj X) : Small.{max v t} (P.obj X))) X i

/-- The sections of the universe lift of a free presheaf of modules are those of the free
presheaf of modules in the larger universe. -/
def uliftFreeObjShrinkLinearEquiv (X : Eᵒᵖ) :
    (uliftFunctor.{_, _, _, _, t}.obj (freeObjShrink T P : PresheafOfModules.{v} T)).obj X
      ≃ₗ[T.obj X] (freeObjShrinkMax.{v, t} T P).obj X :=
  haveI : Small.{max v t} (P.obj X →₀ T.obj X) := small_lift _
  (ULift.moduleEquiv.trans (Shrink.linearEquiv.{v} (T.obj X) (P.obj X →₀ T.obj X))).trans
    (Shrink.linearEquiv.{max v t} (T.obj X) (P.obj X →₀ T.obj X)).symm

/-- `uliftFreeObjShrinkLinearEquiv` sends `z` to the element of the larger universe with the
same underlying finitely supported function as `z.down`. -/
theorem uliftFreeObjShrinkLinearEquiv_apply (X : Eᵒᵖ)
    (z : (uliftFunctor.{_, _, _, _, t}.obj (freeObjShrink T P : PresheafOfModules.{v} T)).obj X) :
    haveI : Small.{max v t} (P.obj X →₀ T.obj X) := small_lift _
    uliftFreeObjShrinkLinearEquiv.{v, t} T P X z =
      (Shrink.addEquiv : Shrink.{max v t} (P.obj X →₀ T.obj X) ≃+ _).symm
        (Shrink.addEquiv z.down) := rfl

/-- The universe lift of a free presheaf of modules is the free presheaf of modules on the same
presheaf of types in the larger universe. -/
def uliftFreeObjShrinkIso :
    uliftFunctor.{_, _, _, _, t}.obj (freeObjShrink T P : PresheafOfModules.{v} T) ≅
      freeObjShrinkMax.{v, t} T P :=
  isoMk (fun X => (uliftFreeObjShrinkLinearEquiv.{v, t} T P X).toModuleIso) (by
    intro X Y f
    have : ∀ Z : Eᵒᵖ, Small.{max v t} (P.obj Z →₀ T.obj Z) := fun _ => small_lift _
    ext a
    change uliftFreeObjShrinkLinearEquiv.{v, t} T P Y
        ((uliftFunctor.{_, _, _, _, t}.obj (freeObjShrink T P : PresheafOfModules.{v} T)).map f a) =
      (freeObjShrinkMax.{v, t} T P).map f (uliftFreeObjShrinkLinearEquiv.{v, t} T P X a)
    have h1 : uliftFreeObjShrinkLinearEquiv.{v, t} T P Y
        ((uliftFunctor.{_, _, _, _, t}.obj (freeObjShrink T P : PresheafOfModules.{v} T)).map f a) =
      (Shrink.addEquiv : Shrink.{max v t} (P.obj Y →₀ T.obj Y) ≃+ _).symm
        (Finsupp.mapDomainMapRange (T.map f).hom (P.map f) (Shrink.addEquiv a.down)) := by
      change (Shrink.addEquiv : Shrink.{max v t} (P.obj Y →₀ T.obj Y) ≃+ _).symm
        (Shrink.addEquiv ((Shrink.addEquiv : Shrink.{v} (P.obj Y →₀ T.obj Y) ≃+ _).symm
          (Finsupp.mapDomainMapRange (T.map f).hom (P.map f) (Shrink.addEquiv a.down)))) = _
      rw [AddEquiv.apply_symm_apply]
    have h2 : (freeObjShrinkMax.{v, t} T P).map f (uliftFreeObjShrinkLinearEquiv.{v, t} T P X a) =
      (Shrink.addEquiv : Shrink.{max v t} (P.obj Y →₀ T.obj Y) ≃+ _).symm
        (Finsupp.mapDomainMapRange (T.map f).hom (P.map f) (Shrink.addEquiv a.down)) := by
      change (Shrink.addEquiv : Shrink.{max v t} (P.obj Y →₀ T.obj Y) ≃+ _).symm
        (Finsupp.mapDomainMapRange (T.map f).hom (P.map f)
          ((Shrink.addEquiv : Shrink.{max v t} (P.obj X →₀ T.obj X) ≃+ _)
            ((Shrink.addEquiv : Shrink.{max v t} (P.obj X →₀ T.obj X) ≃+ _).symm
              (Shrink.addEquiv a.down)))) = _
      rw [AddEquiv.apply_symm_apply]
    exact h1.trans h2.symm)

omit [∀ X, Small.{v} (T.obj X)] [∀ X, Small.{v} (P.obj X)] in
/-- The inverse of `uliftFreeObjShrinkIso` carries a generator to the lift of the generator. -/
theorem uliftFreeObjShrinkIso_inv_gen [∀ X, Small.{v} (T.obj X)] [∀ X, Small.{v} (P.obj X)]
    {X : Eᵒᵖ} (i : P.obj X) :
    (uliftFreeObjShrinkIso.{v, t} T P).inv.app X (freeGenShrinkMax.{v, t} T P i) =
      ULift.up (freeGenShrink T P i) := by
  have : ∀ Z : Eᵒᵖ, Small.{max v t} (P.obj Z →₀ T.obj Z) := fun _ => small_lift _
  change ULift.up ((Shrink.addEquiv : Shrink.{v} (P.obj X →₀ T.obj X) ≃+ _).symm
      ((Shrink.addEquiv : Shrink.{max v t} (P.obj X →₀ T.obj X) ≃+ _)
        ((Shrink.addEquiv : Shrink.{max v t} (P.obj X →₀ T.obj X) ≃+ _).symm
          (Finsupp.single i 1)))) = _
  rw [AddEquiv.apply_symm_apply]
  rfl

end FreeULift

section Corepresentable

/-- Transport bijectivity along an equivalence: if `e ∘ u = v` pointwise, `u` is bijective
exactly when `v` is. -/
private theorem bijective_iff_of_equiv_apply_eq {α β γ : Type*} (e : β ≃ γ) {u : α → β}
    {v : α → γ} (h : ∀ x, e (u x) = v x) : Function.Bijective u ↔ Function.Bijective v := by
  rw [← funext h]
  exact (Function.Bijective.of_comp_iff' e.bijective u).symm

variable {E : Type u₂} [Category.{v₂} E] {T : Eᵒᵖ ⥤ RingCat.{r}} [∀ X, Small.{v} (T.obj X)]
  [LocallySmall.{v} E]

/-- If `(B, e)` corepresents evaluation at `Y` on presheaves of modules in universe `v`, then its
universe lift corepresents evaluation at `Y` in universe `max v t`. -/
theorem bijective_uliftFunctor_eval {B : PresheafOfModules.{v} T} {Y : E} (e : B.obj (op Y))
    (hB : ∀ N : PresheafOfModules.{v} T,
      Function.Bijective (fun β : B ⟶ N => β.app (op Y) e))
    (N : PresheafOfModules.{max v t} T) :
    Function.Bijective
      (fun β : uliftFunctor.{_, _, _, _, t}.obj B ⟶ N => β.app (op Y) (ULift.up e)) := by
  let a := fromFreeYonedaShrink T e
  have ha : IsIso a := by
    rw [isIso_iff_coyoneda_map_bijective]
    intro N₀
    exact (bijective_iff_of_equiv_apply_eq (freeYonedaShrinkEquiv T)
      (u := fun β : B ⟶ N₀ => a ≫ β) (v := fun β : B ⟶ N₀ => β.app (op Y) e) fun β => by
        rw [freeYonedaShrinkEquiv_comp, freeYonedaShrinkEquiv_fromFreeYonedaShrink]).mpr (hB N₀)
  have : ∀ X, Small.{max v t} (T.obj X) := fun X => small_lift _
  have : LocallySmall.{max v t} E := CategoryTheory.locallySmall_trans_univLE ‹_›
  let c : freeObjShrinkMax.{v, t} T (yoneda.obj Y) ⟶ uliftFunctor.{_, _, _, _, t}.obj B :=
    (uliftFreeObjShrinkIso.{v, t} T (yoneda.obj Y)).inv ≫ uliftFunctor.{_, _, _, _, t}.map a
  have hcgen : c.app (op Y) (freeGenShrinkMax.{v, t} T (yoneda.obj Y) (𝟙 Y)) = ULift.up e := by
    change (uliftFunctor.{_, _, _, _, t}.map a).app (op Y)
      ((uliftFreeObjShrinkIso.{v, t} T (yoneda.obj Y)).inv.app (op Y)
        (freeGenShrinkMax.{v, t} T (yoneda.obj Y) (𝟙 Y))) = _
    rw [uliftFreeObjShrinkIso_inv_gen]
    exact congrArg ULift.up (freeYonedaShrinkEquiv_fromFreeYonedaShrink T e)
  refine (bijective_iff_of_equiv_apply_eq (freeYonedaShrinkEquiv T)
    (u := fun β : uliftFunctor.{_, _, _, _, t}.obj B ⟶ N => c ≫ β) (v := fun β =>
      β.app (op Y) (ULift.up e)) fun β => ?_).mp
    ((isIso_iff_coyoneda_map_bijective c).mp inferInstance N)
  rw [freeYonedaShrinkEquiv_comp]
  change β.app (op Y) (c.app (op Y) (freeGenShrinkMax.{v, t} T (yoneda.obj Y) (𝟙 Y))) = _
  rw [hcgen]

end Corepresentable

end PresheafOfModules

namespace PresheafOfModules

section Generator

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{r}} {S : Cᵒᵖ ⥤ RingCat.{r}} (φ : S ⟶ F.op ⋙ R)
  [(pushforward.{v} φ).IsRightAdjoint] [(pushforward.{max v t} φ).IsRightAdjoint]
  [∀ X, Small.{v} (S.obj X)] [LocallySmall.{v} C] [∀ X, Small.{v} (R.obj X)] [LocallySmall.{v} D]

/-- The comparison `pullbackULiftHom` is an isomorphism at the free presheaf of modules on a
representable. -/
theorem isIso_pullbackULiftHom_app_freeObjShrink (X : C) :
    IsIso ((pullbackULiftHom.{v, t} φ).app
      (freeObjShrink S (yoneda.obj X) : PresheafOfModules.{v} S)) := by
  let A : PresheafOfModules.{v} S := freeObjShrink S (yoneda.obj X)
  let adj := pullbackPushforwardAdjunction.{v} φ
  let adj' := pullbackPushforwardAdjunction.{max v t} φ
  have hθ : (pullbackULiftHom.{v, t} φ).app A =
      (adj'.homEquiv _ _).symm (uliftFunctor.{_, _, _, _, t}.map (adj.unit.app A)) := by
    rw [← homEquiv_pullbackULiftHom_app, Equiv.symm_apply_apply]
  rw [hθ]
  refine (Adjunction.isIso_homEquiv_symm_iff_bijective adj' _).mpr fun N => ?_
  let g : (yoneda.obj X).obj (op X) := 𝟙 X
  let e : ((pullback.{v} φ).obj A).obj (op (F.obj X)) :=
    (adj.unit.app A).app (op X) (freeGenShrink S (yoneda.obj X) g)
  have hB : ∀ N₀ : PresheafOfModules.{v} R,
      Function.Bijective (fun β : (pullback.{v} φ).obj A ⟶ N₀ => β.app (op (F.obj X)) e) := by
    intro N₀
    refine (bijective_iff_of_equiv_apply_eq (freeYonedaShrinkEquiv S)
      (u := adj.homEquiv A N₀) (v := fun β : (pullback.{v} φ).obj A ⟶ N₀ =>
        β.app (op (F.obj X)) e) fun β => ?_).mp (adj.homEquiv A N₀).bijective
    rw [Adjunction.homEquiv_unit, freeYonedaShrinkEquiv_comp]
    rfl
  have hA : ∀ N₀ : PresheafOfModules.{v} S,
      Function.Bijective (fun β : A ⟶ N₀ => β.app (op X) (freeGenShrink S (yoneda.obj X) g)) :=
    fun N₀ => (freeYonedaShrinkEquiv S).bijective
  have h₁ := bijective_uliftFunctor_eval.{v, t} e hB N
  have h₂ := bijective_uliftFunctor_eval.{v, t} (freeGenShrink S (yoneda.obj X) g) hA
    ((pushforward.{max v t} φ).obj N)
  have h : (fun β : uliftFunctor.{_, _, _, _, t}.obj ((pullback.{v} φ).obj A) ⟶ N =>
        β.app (op (F.obj X)) (ULift.up e)) =
      (fun ψ : uliftFunctor.{_, _, _, _, t}.obj A ⟶ (pushforward.{max v t} φ).obj N =>
          ψ.app (op X) (ULift.up (freeGenShrink S (yoneda.obj X) g))) ∘
        (fun β : uliftFunctor.{_, _, _, _, t}.obj ((pullback.{v} φ).obj A) ⟶ N =>
          uliftFunctor.{_, _, _, _, t}.map (adj.unit.app A) ≫
            (pushforwardULiftIso.{v, t} φ).hom.app _ ≫ (pushforward.{max v t} φ).map β) := by
    rfl
  rw [h] at h₁
  exact (Function.Bijective.of_comp_iff' h₂ _).mp h₁

end Generator

end PresheafOfModules

namespace PresheafOfModules

section ULiftColimits

variable {C : Type u₁} [Category.{v₁} C] {S : Cᵒᵖ ⥤ RingCat.{r}}

/- The universe lift of modules preserves colimits of a shape for which abelian groups have them
in both module universes. -/
attribute [instance] ModuleCat.uliftFunctor_preservesColimitsOfShape

/-- The universe lift of presheaves of modules preserves colimits of a shape for which abelian
groups have them and the universe lift of modules preserves them. -/
instance uliftFunctor_preservesColimitsOfShape (K : Type*) [Category* K]
    [HasColimitsOfShape K AddCommGrpCat.{v}]
    [∀ X, PreservesColimitsOfShape K (ModuleCat.uliftFunctor.{t, v} (S.obj X))] :
    PreservesColimitsOfShape K (uliftFunctor.{_, _, _, _, t} : PresheafOfModules.{v} S ⥤ _) :=
  ⟨fun {_} => ⟨fun {_} hc => ⟨evaluationJointlyReflectsColimits _ _ (fun X =>
    isColimitOfPreserves (ModuleCat.uliftFunctor.{t, v} (S.obj X))
      (isColimitOfPreserves (evaluation S X) hc))⟩⟩⟩

end ULiftColimits

end PresheafOfModules

namespace PresheafOfModules

section Main

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{r}} {S : Cᵒᵖ ⥤ RingCat.{r}} (φ : S ⟶ F.op ⋙ R)
  [(pushforward.{v} φ).IsRightAdjoint] [(pushforward.{max v t} φ).IsRightAdjoint]
  [∀ X, Small.{v} (S.obj X)] [EssentiallySmall.{v} C] [∀ X, Small.{v} (R.obj X)]
  [LocallySmall.{v} D]

/-- The comparison `pullback φ (M↑) ⟶ (pullback φ M)↑` is an isomorphism for every presheaf of
modules `M` over an essentially small site. -/
theorem isIso_pullbackULiftHom_app (M : PresheafOfModules.{v} S) :
    IsIso ((pullbackULiftHom.{v, t} φ).app M) := by
  have : PreservesColimitsOfSize.{v, v} (pullback.{v} φ) :=
    (pullbackPushforwardAdjunction.{v} φ).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{v, v} (pullback.{max v t} φ) :=
    (pullbackPushforwardAdjunction.{max v t} φ).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{0, 0} (pullback.{v} φ) :=
    (pullbackPushforwardAdjunction.{v} φ).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{0, 0} (pullback.{max v t} φ) :=
    (pullbackPushforwardAdjunction.{max v t} φ).leftAdjoint_preservesColimits
  let ι : SmallModel.{v} C → C := fun U ↦ (equivSmallModel.{v} C).inverse.obj U
  have hι : ∀ X : C, ∃ i, Nonempty (ι i ≅ X) := fun X ↦
    ⟨(equivSmallModel.{v} C).functor.obj X, ⟨((equivSmallModel.{v} C).unitIso.app X).symm⟩⟩
  have hsum : ∀ N : PresheafOfModules.{v} S,
      IsIso ((pullbackULiftHom.{v, t} φ).app (∐ freePresentationDiagram S ι N)) := by
    intro N
    have : PreservesColimitsOfShape (Discrete (freePresentationIndex S ι N))
        (uliftFunctor.{_, _, _, _, t} : PresheafOfModules.{v} S ⥤ _) :=
      uliftFunctor_preservesColimitsOfShape _
    have : IsIso (Functor.whiskerLeft (Discrete.functor (freePresentationDiagram S ι N))
        (pullbackULiftHom.{v, t} φ)) := by
      rw [NatTrans.isIso_iff_isIso_app]
      rintro ⟨j⟩
      exact isIso_pullbackULiftHom_app_freeObjShrink.{v, t} φ (ι j.1)
    exact isIso_app_coconePt_of_preservesColimit _ (pullbackULiftHom.{v, t} φ) _
      (coproductIsCoproduct (freePresentationDiagram S ι N))
  have : PreservesColimitsOfShape WalkingParallelPair
      (uliftFunctor.{_, _, _, _, t} : PresheafOfModules.{v} S ⥤ _) :=
    have : ∀ X, PreservesColimitsOfShape WalkingParallelPair
        (ModuleCat.uliftFunctor.{t, v} (S.obj X)) := fun X => inferInstance
    uliftFunctor_preservesColimitsOfShape _
  have h0 : IsIso ((pullbackULiftHom.{v, t} φ).app
      ((parallelPair (toFreePresentation S ι M) 0).obj WalkingParallelPair.zero)) := hsum _
  have h1 : IsIso ((pullbackULiftHom.{v, t} φ).app
      ((parallelPair (toFreePresentation S ι M) 0).obj WalkingParallelPair.one)) := hsum _
  have : IsIso (Functor.whiskerLeft (parallelPair (toFreePresentation S ι M) 0)
      (pullbackULiftHom.{v, t} φ)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    rintro (_ | _)
    exacts [h0, h1]
  have hc := isColimitFreePresentationCokernelCofork S ι hι M
  have key := isIso_app_coconePt_of_preservesColimit _ (pullbackULiftHom.{v, t} φ) _ hc
  exact key

end Main

end PresheafOfModules
