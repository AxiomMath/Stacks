module

public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatSource.CechKFlat
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatSource.UnderivedComparison
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.AffinePushforwardComparison
public import StacksFrontier.AlgebraicGeometry.RelativeCechAcyclic.Basic
public import StacksFrontier.AlgebraicGeometry.RightAcyclicProduct.Basic
public import StacksFrontier.CategoryTheory.Triangulated.ComponentwiseInvertibility

/-!
# The terms of the absolute Čech resolution under base change

The underived base change map is invertible at every term of the Čech complex of a
quasi-coherent module for an affine cover, and the terms are acyclic for the pushforward after
pullback.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeCech Stacks.AlgebraicGeometry.RelativeCechComplex
open Stacks.CategoryTheory.CechComplex
open scoped Stacks.AlgebraicGeometry.RelativeCechBaseChange

universe u

namespace Stacks.AlgebraicGeometry.FlatSourceBaseChange

noncomputable section

/-- **A natural transformation between additive functors is invertible at a finite product as
soon as it is invertible at every factor.** -/
theorem isIso_app_pi_of_preserves {C D : Type*} [Category* C] [Category* D] {P Q : C ⥤ D}
    (τ : P ⟶ Q) {ι : Type*} (A : ι → C) [HasProductsOfShape ι C] [HasProductsOfShape ι D]
    [PreservesLimit (Discrete.functor A) P]
    [PreservesLimit (Discrete.functor A) Q]
    (h : ∀ k, IsIso (τ.app (A k))) : IsIso (τ.app (∏ᶜ A)) := by
  have : ∀ k, IsIso (τ.app (A k)) := h
  have key : τ.app (∏ᶜ A) ≫ piComparison Q A =
      piComparison P A ≫ Limits.Pi.map fun k => τ.app (A k) := by
    refine Pi.hom_ext _ _ fun k => ?_
    simp only [Category.assoc, piComparison_comp_π, Pi.map_π, piComparison_comp_π_assoc]
    exact (τ.naturality _).symm
  have h₁ : IsIso (piComparison P A) := by
    rw [← PreservesProduct.iso_hom]
    infer_instance
  have h₂ : IsIso (Limits.Pi.map fun k => τ.app (A k)) :=
    Iso.isIso_hom (Pi.mapIso fun k => asIso (τ.app (A k)))
  have hcomp : IsIso (τ.app (∏ᶜ A) ≫ piComparison Q A) := by
    rw [key]
    infer_instance
  exact IsIso.of_isIso_comp_right (τ.app (∏ᶜ A)) (piComparison Q A)

variable {X X' S S' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
  (hsq : IsPullback g' f' f g) (T : X.AffineOpenCover.{u, u}) [Finite T.I₀]
  [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from S))]
  (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)

/-- The structure map of an intersection of the cover is affine, also over `S`, and the pullback
of a quasi-coherent module along it is quasi-coherent. -/
private theorem inter_hom_facts {p : ℕ} (T : X.AffineOpenCover.{u, u})
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (x : Fin (p + 1) → T.I₀) :
    IsAffineHom (inter (fun i ↦ (Over.mk (T.f i) : Over X)) x).hom ∧
      IsAffineHom ((inter (fun i ↦ (Over.mk (T.f i) : Over X)) x).hom ≫ f) ∧
      ((Scheme.Modules.pullback (inter (fun i ↦ (Over.mk (T.f i) : Over X)) x).hom).obj
        F.obj).IsQuasicoherent :=
  ⟨RelativeCechBaseChange.isAffineHom_pi_hom T x,
    RelativeCechBaseChange.isAffineHom_pi_hom_comp (f := f) T x,
    AffineBaseChange.isQuasicoherent_pullback _ F.obj⟩

include hsq in
/-- **The base change morphism of [Stacks, Tag 02KG] is invertible at every term of the `ℕ`-indexed
absolute Čech resolution.** Each factor is the direct image along an affine morphism, composed
with `f` still affine, of a quasi-coherent module. -/
theorem isIso_baseChangeNatTrans_app_cechComplex_X (p : ℕ) :
    IsIso ((ModuleBaseChange.baseChangeNatTrans hsq.w).app
      (((cechComplexFunctor fun i ↦ (Over.mk (T.f i) : Over X)).obj
        ((CechPushforwardComplex.absoluteCechPresheaf X).obj F)).X p)) := by
  refine isIso_app_pi_of_preserves (ModuleBaseChange.baseChangeNatTrans hsq.w)
    (ι := Fin (p + 1) → T.I₀) (fun x => ((CechPushforwardComplex.absoluteCechPresheaf X).obj F).obj
      (op (inter (fun i ↦ (Over.mk (T.f i) : Over X)) x))) fun x => ?_
  set A := inter (fun i ↦ (Over.mk (T.f i) : Over X)) x
  change IsIso ((ModuleBaseChange.baseChangeNatTrans hsq.w).app
    ((Scheme.Modules.pushforward A.hom).obj ((Scheme.Modules.pullback A.hom).obj F.obj)))
  obtain ⟨_, _, _⟩ := inter_hom_facts (f := f) T F x
  exact ModuleBaseChange.isIso_baseChangeNatTrans_app_pushforward hsq
    (IsPullback.of_hasPullback _ g') _

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

include hsq in
omit [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from S))] in
/-- **The inverse image of a factor of the absolute Čech resolution is right acyclic for the direct
image along the base change.** For `A` over `X` with `A ⟶ X` and `A ⟶ S` affine, the module
`(g')^* a_* a^* ℱ` is, by affine base change ([Stacks, Tag 02KG]), the direct image along the
base change `a'` of `a`, which is again affine and affine over `S'`; such a module is right acyclic
for `f'_*`. -/
theorem rightAcyclic_pullback_pushforward (A : Over X) [IsAffineHom A.hom]
    [IsAffineHom (A.hom ≫ f)] (M : A.left.Modules) [M.IsQuasicoherent] :
    (Scheme.Modules.pushforward f').rightAcyclic ((Scheme.Modules.pullback g').obj
      ((Scheme.Modules.pushforward A.hom).obj M)) := by
  have Hi := IsPullback.of_hasPullback A.hom g'
  have : IsAffineHom (pullback.snd A.hom g') :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback Hi inferInstance
  have : IsAffineHom (pullback.snd A.hom g' ≫ f') :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (Hi.paste_vert hsq) inferInstance
  have : ((Scheme.Modules.pullback (pullback.fst A.hom g')).obj M).IsQuasicoherent :=
    AffineBaseChange.isQuasicoherent_pullback _ _
  have := AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom Hi M
  have hac := RelativeCechAcyclic.rightAcyclic_pushforward_comp (pullback.snd A.hom g') f'
    ((Scheme.Modules.pullback (pullback.fst A.hom g')).obj M)
  exact RightAcyclicProduct.rightAcyclic_of_iso (Scheme.Modules.pushforward f')
    (asIso ((AffinePushforward.baseChangeNatTrans Hi.w).app M)).symm hac

include hsq in
/-- **The inverse image of every term of the `ℕ`-indexed absolute Čech resolution is right acyclic
for the direct image along the base change**: the inverse image preserves the finite product, and
every factor is handled by `rightAcyclic_pullback_pushforward`. -/
theorem rightAcyclic_pullback_cechComplex_X (p : ℕ) :
    (Scheme.Modules.pushforward f').rightAcyclic ((Scheme.Modules.pullback g').obj
      (((cechComplexFunctor fun i ↦ (Over.mk (T.f i) : Over X)).obj
        ((CechPushforwardComplex.absoluteCechPresheaf X).obj F)).X p)) := by
  refine RightAcyclicProduct.rightAcyclic_of_isLimit_fan _
    (isLimitFanMkObjOfIsLimit (Scheme.Modules.pullback g') _ _
      (isLimitFan (fun i ↦ (Over.mk (T.f i) : Over X))
        ((CechPushforwardComplex.absoluteCechPresheaf X).obj F) p)) fun x => ?_
  change (Scheme.Modules.pushforward f').rightAcyclic ((Scheme.Modules.pullback g').obj
    ((Scheme.Modules.pushforward (inter (fun i ↦ (Over.mk (T.f i) : Over X)) x).hom).obj
      ((Scheme.Modules.pullback (inter (fun i ↦ (Over.mk (T.f i) : Over X)) x).hom).obj F.obj)))
  obtain ⟨_, _, _⟩ := inter_hom_facts (f := f) T F x
  exact rightAcyclic_pullback_pushforward hsq _ _

end

end Stacks.AlgebraicGeometry.FlatSourceBaseChange
