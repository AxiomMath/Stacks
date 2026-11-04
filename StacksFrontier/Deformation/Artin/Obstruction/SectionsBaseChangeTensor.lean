module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsSheafSequence
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsThickening

/-!
# The terms of the sequence of Stacks 07YH, read on `W_A`

Let `q : W → S` be a morphism of schemes, let `𝓕` be an `𝒪_W`-module, let `t : Spec A' → S` be
a scheme over `S` and let `φ : A' → A` be a ring map. Write `i : W_A → W_{A'}` for the
base-change immersion. For an `A`-module `M`, the term

```
𝓕_{A'} ⊗_{A'} M
```

of the sheaf-level sequence of Stacks 07YH — formed over the base `A'`, with `M` regarded as an
`A'`-module along `φ` — is the direct image along `i` of

```
𝓕_A ⊗_A M,
```

the term formed over the base `A`.

## Main definitions

* `Deformation.Artin.SectionsSheaf.quotOver` and `..quotHom` — the morphism `Spec A → Spec A'`
  of schemes over `S` that a ring map `φ : A' → A` induces.
* `Deformation.Artin.SectionsSheaf.baseChangeSheafIso` — `i^* 𝓕_{A'} ≅ 𝓕_A`.
* `Deformation.Artin.SectionsSheaf.tildePushforwardIso` — `(Spec φ)_* M̃_A ≅ (M|_{A'})~`.
* `Deformation.Artin.SectionsSheaf.affineBaseChangeIso` — `π_{A'}^* (Spec φ)_* N ≅ i_* π_A^* N`.
* `Deformation.Artin.SectionsSheaf.immersionProjectionFormulaIso` — the projection formula
  `i_*G ⊗ 𝓕_{A'} ≅ i_*(G ⊗ i^*𝓕_{A'})`.

## Main results

* `closedImmersionProjectionFormulaIso`, in the namespace
  `Deformation.Artin.SectionsSheaf.Stacks.AffineProjectionFormula` — the identification
  `𝓕_{A'} ⊗_{A'} M ≅ i_*(𝓕_A ⊗_A M)`, for every `A`-module `M`.

## References

* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Deformation.Artin.SectionsSheaf

/-- `𝓕 ⊗_R M` computed by `tensorSheafFunctor` is the tensor product of `𝓕` with the pullback of
`M̃` given by the bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor`. -/
theorem tensorSheafFunctor_obj_eq {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R)
    (F : SheafOfModules.{u} X.ringCatSheaf) (M : ModuleCat.{u} R) :
    (tensorSheafFunctor π F).obj M =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩))).obj
        ((Scheme.Modules.pullback π).obj ((tilde.functor R).obj M), F) :=
  rfl

section BaseChangeTensor

variable {S : Scheme.{u}} {A' A : CommRingCat.{u}} (φ : A' ⟶ A) (t : Spec A' ⟶ S)
  {W : Scheme.{u}} (q : W ⟶ S) (𝓕 : W.Modules)

/-- `Spec A` as a scheme over `S`, through `Spec A'`. -/
abbrev quotOver : Over S := Over.mk (Spec.map φ ≫ t)

/-- The morphism `Spec A → Spec A'` of schemes over `S` induced by `φ : A' → A`. -/
abbrev quotHom : quotOver φ t ⟶ Over.mk t := Over.homMk (Spec.map φ) rfl

/-- The isomorphism `i^* 𝓕_{A'} ≅ 𝓕_A`. -/
def baseChangeSheafIso :
    (Scheme.Modules.pullback (baseChangeMap q (quotHom φ t))).obj
        ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕) ≅
      (Scheme.Modules.pullback (pullback.snd (quotOver φ t).hom q)).obj 𝓕 :=
  ((Scheme.Modules.pullbackComp (baseChangeMap q (quotHom φ t))
      (pullback.snd (Over.mk t).hom q)) ≪≫
    Scheme.Modules.pullbackCongr (baseChangeMap_comp_snd q (quotHom φ t))).app 𝓕

/-- The isomorphism `(Spec φ)_* M̃_A ≅ (M|_{A'})~`: the quasi-coherent sheaf on `Spec A'` of an
`A`-module is the direct image of its sheaf on `Spec A`. -/
def tildePushforwardIso (M : ModuleCat.{u} A) :
    (Scheme.Modules.pushforward (Spec.map φ)).obj ((tilde.functor A).obj M) ≅
      (tilde.functor A').obj ((ModuleCat.restrictScalars φ.hom).obj M) :=
  (pushforwardTildeIso A' A φ).app M

/-- Affine base change at the base-change square, `π_{A'}^* (Spec φ)_* N ≅ i_* π_A^* N`, for a
quasi-coherent `N`. -/
def affineBaseChangeIso (N : (Spec A).Modules) [N.IsQuasicoherent] :
    (Scheme.Modules.pullback (pullback.fst (Over.mk t).hom q)).obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj N) ≅
      (Scheme.Modules.pushforward (baseChangeMap q (quotHom φ t))).obj
        ((Scheme.Modules.pullback (pullback.fst (quotOver φ t).hom q)).obj N) := by
  haveI : IsAffineHom (quotHom φ t).left := inferInstanceAs (IsAffineHom (Spec.map φ))
  exact @asIso _ _ _ _ _
    (Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
      (isPullback_baseChangeMap q (quotHom φ t)).flip N)

/-- The projection formula at the base-change closed immersion,
`i_*G ⊗ 𝓕_{A'} ≅ i_*(G ⊗ i^*𝓕_{A'})`. -/
def immersionProjectionFormulaIso
    (hi : IsClosedImmersion (baseChangeMap q (quotHom φ t)))
    (G : (pullback (quotOver φ t).hom q).Modules) :
    letI := hi
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(((pullback (Over.mk t).hom q).toRingedSpace)).presheaf,
        (((pullback (Over.mk t).hom q).toRingedSpace)).IsSheaf⟩))).obj
        ((Scheme.Modules.pushforward (baseChangeMap q (quotHom φ t))).obj G,
          (Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕) ≅
      (Scheme.Modules.pushforward (baseChangeMap q (quotHom φ t))).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(((pullback (quotOver φ t).hom q).toRingedSpace)).presheaf,
            (((pullback (quotOver φ t).hom q).toRingedSpace)).IsSheaf⟩))).obj
          (G, (Scheme.Modules.pullback (baseChangeMap q (quotHom φ t))).obj
            ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕))) :=
  letI := hi
  Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso
    (baseChangeMap q (quotHom φ t)) G
    ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)

/-- For an `A`-module `M`,
```
𝓕_{A'} ⊗_{A'} M ≅ i_*(𝓕_A ⊗_A M),
```
where the left-hand side is formed over the base `A'` with `M` regarded as an `A'`-module and
the right-hand side over the base `A`. -/
def Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso
    (hi : IsClosedImmersion (baseChangeMap q (quotHom φ t))) (M : ModuleCat.{u} A) :
    letI := hi
    (tensorSheafFunctor (pullback.fst (Over.mk t).hom q)
        ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)).obj
          ((ModuleCat.restrictScalars φ.hom).obj M) ≅
      (Scheme.Modules.pushforward (baseChangeMap q (quotHom φ t))).obj
        ((tensorSheafFunctor (pullback.fst (quotOver φ t).hom q)
          ((Scheme.Modules.pullback (pullback.snd (quotOver φ t).hom q)).obj 𝓕)).obj M) :=
  letI := hi
  eqToIso (tensorSheafFunctor_obj_eq (pullback.fst (Over.mk t).hom q) _ _) ≪≫
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(((pullback (Over.mk t).hom q).toRingedSpace)).presheaf,
        (((pullback (Over.mk t).hom q).toRingedSpace)).IsSheaf⟩))).mapIso
      (Iso.prod ((Scheme.Modules.pullback (pullback.fst (Over.mk t).hom q)).mapIso
          (tildePushforwardIso φ M).symm ≪≫
        affineBaseChangeIso φ t q ((tilde.functor A).obj M)) (Iso.refl _)) ≪≫
    immersionProjectionFormulaIso φ t q 𝓕 hi ((Scheme.Modules.pullback
      (pullback.fst (quotOver φ t).hom q)).obj ((tilde.functor A).obj M)) ≪≫
    (Scheme.Modules.pushforward (baseChangeMap q (quotHom φ t))).mapIso
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((pullback (quotOver φ t).hom q).toRingedSpace)).presheaf,
          (((pullback (quotOver φ t).hom q).toRingedSpace)).IsSheaf⟩))).mapIso
        (Iso.prod (Iso.refl _) (baseChangeSheafIso φ t q 𝓕))) ≪≫
    (Scheme.Modules.pushforward (baseChangeMap q (quotHom φ t))).mapIso
      (eqToIso (tensorSheafFunctor_obj_eq (pullback.fst (quotOver φ t).hom q) _ M)).symm

end BaseChangeTensor

end Deformation.Artin.SectionsSheaf

end
