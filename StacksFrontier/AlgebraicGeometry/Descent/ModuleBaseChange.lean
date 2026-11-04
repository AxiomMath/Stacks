module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.BaseChange
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.RingTheory.MilnorPatching.Relative

/-!
# Base change for direct images of quasi-coherent modules on affine schemes

For a commutative square of schemes
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
the canonical base-change morphism `g^* f_* ⟶ f'_* (g')^*` on sheaves of modules is
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans`, the mate of the identification
of the two composite direct images around the square. This file proves that it is an
isomorphism at every quasi-coherent module when the square is the spectrum of a pushout square
of commutative rings: the affine case of the base-change assertion of [Stacks, Tag 02KG], where
it comes down to the equality `(R' ⊗_R A) ⊗_A M = R' ⊗_R M` of `R'`-modules.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.baseChangeNatTrans_unit_top`: for an arbitrary
  commutative square of schemes, the base-change morphism carries the pullback of a global
  section to the pullback of that global section.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_baseChangeNatTrans_specMap`: for a pushout
  square of commutative rings and a quasi-coherent module `M` on the spectrum of the lower left
  corner, the base-change morphism of the square of spectra is an isomorphism at `M`.

## Implementation notes

The `A`-module structure on `Γ(f_*M, ⊤)` is a restriction of scalars along the structure
morphism, not along `φ₂`, so the two spellings are defeq but not syntactically equal and `rw`
fails on patterns that print identically to the target. The proof of
`isIso_baseChangeNatTrans_specMap` therefore combines named equations by `Eq.trans` and
`congrArg`, each stated at the spelling its consumer uses.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-- Composed with the unit of `(g')^* ⊣ (g')_*` pushed forward along `f`, the comparison of the
two composite direct images around the square is the unit of `g^* ⊣ g_*` followed by `g_*` of the
base-change morphism. -/
lemma unit_baseChangeNatTrans (w : g' ≫ f = f' ≫ g) (M : X.Modules) :
    (Scheme.Modules.pushforward f).map
        ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app M) ≫
      (AffinePushforward.pushforwardSquareIso w).hom.app
        ((Scheme.Modules.pullback g').obj M) =
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        ((Scheme.Modules.pushforward f).obj M) ≫
      (Scheme.Modules.pushforward g).map
        ((AffinePushforward.baseChangeNatTrans w).app M) :=
  unit_mateEquiv_symm (Scheme.Modules.pullbackPushforwardAdjunction g')
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    (AffinePushforward.pushforwardSquareIso w).hom M

/-- `unit_baseChangeNatTrans` read on sections over the whole space. -/
lemma baseChangeNatTrans_val_app_top (w : g' ≫ f = f' ≫ g) (M : X.Modules)
    (a : M.val.obj (op (⊤ : X.Opens))) :
    ((AffinePushforward.baseChangeNatTrans w).app M).val.app (op (⊤ : S'.Opens))
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
            ((Scheme.Modules.pushforward f).obj M)).val.app (op (⊤ : S.Opens)) a) =
      ((AffinePushforward.pushforwardSquareIso w).hom.app
          ((Scheme.Modules.pullback g').obj M)).val.app (op (⊤ : S.Opens))
        (((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app M).val.app
          (op (⊤ : X.Opens)) a) :=
  (congrArg (fun t : (Scheme.Modules.pushforward f).obj M ⟶
      (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward f').obj
        ((Scheme.Modules.pullback g').obj M)) =>
      t.val.app (op (⊤ : S.Opens)) a) (unit_baseChangeNatTrans w M)).symm

/-- On sections over the whole space the comparison of the two composite direct images around a
commutative square is the identity. -/
lemma pushforwardSquareIso_val_app_top (w : g' ≫ f = f' ≫ g) (N : X'.Modules)
    (b : N.val.obj (op (⊤ : X'.Opens))) :
    ((AffinePushforward.pushforwardSquareIso w).hom.app N).val.app (op (⊤ : S.Opens)) b = b := by
  have E : (f' ≫ g) ⁻¹ᵁ (⊤ : S.Opens) = (g' ≫ f) ⁻¹ᵁ (⊤ : S.Opens) := by rw [w]
  have h : ((AffinePushforward.pushforwardSquareIso w).hom.app N).val.app (op (⊤ : S.Opens)) b =
      ConcreteCategory.hom (N.presheaf.map (eqToHom E).op) b := rfl
  have h2 : ((eqToHom E).op : op ((g' ≫ f) ⁻¹ᵁ (⊤ : S.Opens)) ⟶ op ((f' ≫ g) ⁻¹ᵁ (⊤ : S.Opens)))
      = 𝟙 _ := Subsingleton.elim _ _
  have h3 : N.presheaf.map ((eqToHom E).op) = N.presheaf.map (𝟙 _) := congrArg _ h2
  rw [h, h3, N.presheaf.map_id]
  rfl

/-- For a commutative square of schemes, the base-change morphism
`AffinePushforward.baseChangeNatTrans` carries the pullback of a global section to the pullback of
that global section. -/
lemma baseChangeNatTrans_unit_top (w : g' ≫ f = f' ≫ g) (M : X.Modules)
    (a : M.val.obj (op (⊤ : X.Opens))) :
    ((AffinePushforward.baseChangeNatTrans w).app M).val.app (op (⊤ : S'.Opens))
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
            ((Scheme.Modules.pushforward f).obj M)).val.app (op (⊤ : S.Opens)) a) =
      ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app M).val.app
        (op (⊤ : X.Opens)) a :=
  (baseChangeNatTrans_val_app_top w M a).trans
    (pushforwardSquareIso_val_app_top w _ _)

section Affine

open scoped ChangeOfRings

variable {A B₁ B₂ C : CommRingCat.{u}} {φ₁ : A ⟶ B₁} {φ₂ : A ⟶ B₂} {ψ₁ : B₁ ⟶ C} {ψ₂ : B₂ ⟶ C}

/-- A commutative square of commutative rings gives a commutative square of spectra. -/
lemma specSquare (comm : φ₂ ≫ ψ₂ = φ₁ ≫ ψ₁) :
    Spec.map ψ₂ ≫ Spec.map φ₂ = Spec.map ψ₁ ≫ Spec.map φ₁ := by
  rw [← Spec.map_comp, ← Spec.map_comp, comm]

/-- Let
```
A --φ₁--> B₁
|φ₂       |ψ₁
B₂ --ψ₂-> C
```
be a pushout square of commutative rings and let `M` be a quasi-coherent module on `Spec B₂`.
Then the canonical base-change morphism
`(Spec φ₁)^* (Spec φ₂)_* M ⟶ (Spec ψ₁)_* (Spec ψ₂)^* M` is an isomorphism. -/
theorem isIso_baseChangeNatTrans_specMap (comm : φ₂ ≫ ψ₂ = φ₁ ≫ ψ₁)
    (hp : MilnorPatching.IsPushoutSquare φ₂.hom φ₁.hom ψ₂.hom ψ₁.hom
      (by rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, comm]))
    (M : (Spec B₂).Modules) [M.IsQuasicoherent] :
    IsIso ((AffinePushforward.baseChangeNatTrans (specSquare comm)).app M) := by
  have hq1 : ((Scheme.Modules.pushforward (Spec.map φ₂)).obj M).IsQuasicoherent :=
    Stacks.Descent.isQuasicoherent_pushforward_specMap φ₂ M
  have hq2 : ((Scheme.Modules.pullback (Spec.map ψ₂)).obj M).IsQuasicoherent :=
    Stacks.Descent.isQuasicoherent_pullback_specMap ψ₂ M
  have hL : ((Scheme.Modules.pushforward (Spec.map φ₂) ⋙
      Scheme.Modules.pullback (Spec.map φ₁)).obj M).IsQuasicoherent :=
    Stacks.Descent.isQuasicoherent_pullback_specMap φ₁ _
  have hR : ((Scheme.Modules.pullback (Spec.map ψ₂) ⋙
      Scheme.Modules.pushforward (Spec.map ψ₁)).obj M).IsQuasicoherent :=
    Stacks.Descent.isQuasicoherent_pushforward_specMap ψ₁ _
  let u₁ := quasicoherentPullbackSectionsIso A B₁ φ₁
    ((Scheme.Modules.pushforward (Spec.map φ₂)).obj M)
  let u₂ := quasicoherentPullbackSectionsIso B₂ C ψ₂ M
  let u₃ := (Stacks.Descent.pushforwardSpecΓIso ψ₁).app
    ((Scheme.Modules.pullback (Spec.map ψ₂)).obj M)
  let u₄ := (Stacks.Descent.pushforwardSpecΓIso φ₂).app M
  let alg := MilnorPatching.pushoutBaseChange φ₂.hom φ₁.hom ψ₂.hom ψ₁.hom
    (by rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, comm]) hp
  refine AffineBaseChange.isIso_of_isIso_moduleSpecΓ _ ?_
  have key : u₁.hom ≫ moduleSpecΓFunctor.map
        ((AffinePushforward.baseChangeNatTrans (specSquare comm)).app M) =
      (ModuleCat.extendScalars φ₁.hom).map u₄.hom ≫
        alg.inv.app (moduleSpecΓFunctor.obj M) ≫
        (ModuleCat.restrictScalars ψ₁.hom).map u₂.hom ≫ u₃.inv := by
    refine ModuleCat.ExtendScalars.hom_ext fun a => ?_
    have h1 : u₁.hom ((1 : B₁) ⊗ₜ[A, φ₁.hom] a)
        = ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ₁)).unit.app
            ((Scheme.Modules.pushforward (Spec.map φ₂)).obj M)).val.app (op ⊤) a :=
      quasicoherentPullbackSectionsIso_hom_one_tmul A B₁ φ₁ _ a
    have h2 := quasicoherentPullbackSectionsIso_hom_one_tmul B₂ C ψ₂ M (u₄.hom a)
    have h3 := MilnorPatching.pushoutBaseChangeIso_inv_tmul φ₂.hom φ₁.hom ψ₂.hom ψ₁.hom
      (by rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, comm]) hp
      (moduleSpecΓFunctor.obj M) 1 (u₄.hom a)
    rw [map_one] at h3
    have L : (u₁.hom ≫ moduleSpecΓFunctor.map
          ((AffinePushforward.baseChangeNatTrans (specSquare comm)).app M))
            ((1 : B₁) ⊗ₜ[A, φ₁.hom] a)
        = ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ψ₂)).unit.app M).val.app
            (op ⊤) a :=
      (congrArg (fun z => ((AffinePushforward.baseChangeNatTrans (specSquare comm)).app M).val.app
          (op (⊤ : (Spec B₁).Opens)) z) h1).trans
        (baseChangeNatTrans_unit_top (specSquare comm) M a)
    have c0 : ((ModuleCat.extendScalars φ₁.hom).map u₄.hom ≫
          alg.inv.app (moduleSpecΓFunctor.obj M) ≫
          (ModuleCat.restrictScalars ψ₁.hom).map u₂.hom ≫ u₃.inv)
            ((1 : B₁) ⊗ₜ[A, φ₁.hom] a)
        = u₃.inv ((ModuleCat.restrictScalars ψ₁.hom).map u₂.hom
            (alg.inv.app (moduleSpecΓFunctor.obj M)
              ((ModuleCat.extendScalars φ₁.hom).map u₄.hom
                ((1 : B₁) ⊗ₜ[A, φ₁.hom] a)))) := rfl
    exact L.trans (c0.trans (Eq.trans
      (congrArg (ConcreteCategory.hom
        ((ModuleCat.restrictScalars ψ₁.hom).map u₂.hom ≫ u₃.inv)) h3) h2)).symm
  exact IsIso.of_isIso_fac_left key

end Affine

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
