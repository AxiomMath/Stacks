module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.AlgebraicGeometry.Modules.AffineInternalHom
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.Adjunction
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.AffineTensor

/-!
# Duals, tensor products and reflexive hulls of associated sheaves on an affine scheme

Let `R` be a commutative ring.  The associated-sheaf functor `M ↦ M~` from `R`-modules to
`𝒪_{Spec R}`-modules is monoidal and, on modules of finite presentation, commutes with the
internal Hom; so it carries the module-theoretic dual and reflexive hull to the sheaf-theoretic
ones.  This file assembles those comparisons.

## Main definitions

* `sheafHomPackage X F G`: the internal Hom `ℋom_{𝒪_X}(F, G)` presented as a `SheafHom`
  package, i.e. together with the identification of its sections over `U` with the morphisms
  `F|_U ⟶ G|_U`.  Specialised to `G = 𝒪_X` its underlying module is the dual `F^∨` on the nose
  (`sheafHomPackage_obj`).
* `dualIso e`: the dual of an isomorphism, contravariantly.
* `tensorSheafComparison X F G`: the two constructions of `F ⊗_{𝒪_X} G` in the library — as the
  sheafification of the sectionwise tensor product and as the sheafification of the monoidal
  product of presheaves of modules — agree.
* `tensorSheafIso e e'`: functoriality of `F ⊗_{𝒪_X} G` in both arguments.
* `tensorSheafTildeIso R M N`: **the affine tensor comparison**
  `M~ ⊗_{𝒪_{Spec R}} N~ ≅ (M ⊗_R N)~`.

## Implementation notes

The library carries two spellings of the tensor product of sheaves of modules:
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`, used by the category of coherent
reflexive modules, and `Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, for which the
affine comparison `AlgebraicGeometry.tildeTensorIso` is available.  Both sheafify a presheaf
whose sections over `U` are `F(U) ⊗_{𝒪_X(U)} G(U)` by the same sheafification functor; only the
description of the restriction maps differs, and they agree on pure tensors.
`tensorSheafComparison` is that identification, and it is what lets the affine comparison be
used in the reflexive setting.

The `SheafHom` package of `sheafHomPackage` is the shape in which the affine internal-Hom
comparison `AlgebraicGeometry.internalHomTildeIso` takes its input.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open Stacks.PresheafOfModules.InternalHom
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf dualMap dualFunctor)

universe u

namespace AlgebraicGeometry

/-- The internal Hom of two `𝒪_X`-modules, packaged as a `SheafHom`: its sections over `U`
are the morphisms `F|_U ⟶ G|_U`, compatibly with restriction and with the `𝒪_X`-action. -/
noncomputable def sheafHomPackage (X : Scheme.{u}) (F G : X.Modules) :
    _root_.SheafHom X.sheaf F G where
  obj := ⟨_root_.internalHom X.sheaf.obj F.val G.val,
    _root_.internalHom_isSheaf X.sheaf.obj F.val G.val G.isSheaf⟩
  sectionsEquiv U := by
    let e : (F.over U ⟶ G.over U) ≃
        ((_root_.restrFun X.sheaf.obj U).obj F.val ⟶
          (_root_.restrFun X.sheaf.obj U).obj G.val) :=
      (SheafOfModules.fullyFaithfulForget ((_root_.structureSheaf X.sheaf).over U)).homEquiv
    exact
      { toFun := e.symm
        invFun := e
        left_inv := e.apply_symm_apply
        right_inv := e.symm_apply_apply
        map_add' := by
          intro f g
          apply e.injective
          rfl }
  restrict_natural := by
    intro U V hVU s W hWV x
    rfl
  smul_natural := by
    intro U r s W hWU x
    rfl

/-- The internal-Hom package into the structure sheaf carries the dual module `F^∨` itself,
not merely an isomorphic copy of it. -/
theorem sheafHomPackage_obj (X : Scheme.{u}) (F : X.Modules) :
    (sheafHomPackage X F (SheafOfModules.unit _)).obj = dualSheaf F :=
  rfl

/-- An isomorphism of `𝒪_X`-modules induces an isomorphism of their duals, contravariantly. -/
noncomputable def dualIso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) :
    dualSheaf G ≅ dualSheaf F :=
  (dualFunctor X).mapIso e.op

/-- The two constructions of the tensor product of `𝒪_X`-modules — as the sheafification of
the sectionwise tensor product and as the sheafification of the monoidal product of presheaves
of modules — agree.  Both sheafify a presheaf whose sections are `F(U) ⊗_{𝒪_X(U)} G(U)`; only
the description of the restriction maps differs, and that difference is invisible on pure
tensors. -/
noncomputable def tensorSheafComparison (X : Scheme.{u}) (F G : X.Modules) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (G)) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩).obj (F)).obj (G)) := by
  apply (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyFunctor X.toRingedSpace).mapIso
  refine PresheafOfModules.isoMk (fun _ => Iso.refl _) ?_
  intro V W f
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  rfl

/-- The monoidal tensor product of presheaves of modules, sheafified, is functorial in both
arguments. -/
noncomputable def tensorSheafificationIso (X : Scheme.{u}) {F F' G G' : X.Modules}
    (e : F ≅ F') (e' : G ≅ G') :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩).obj (F)).obj (G)) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.2)⟩).obj (F')).obj (G')) :=
  (Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf X.ringCatSheaf.2).mapIso
    (MonoidalCategory.tensorIso
      (C := PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat))
      ((SheafOfModules.forget X.ringCatSheaf).mapIso e)
      ((SheafOfModules.forget X.ringCatSheaf).mapIso e'))

/-- The tensor product of `𝒪_X`-modules is functorial in both arguments. -/
noncomputable def tensorSheafIso (X : Scheme.{u}) {F F' G G' : X.Modules}
    (e : F ≅ F') (e' : G ≅ G') :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (G)) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F')).obj (G')) :=
  tensorSheafComparison X F G ≪≫ tensorSheafificationIso X e e' ≪≫
    (tensorSheafComparison X F' G').symm

/-- **The affine tensor comparison, Stacks Tag 01I8.**  On `Spec R` the tensor product of the
sheaves associated to `M` and `N` is the sheaf associated to `M ⊗_R N`. -/
noncomputable def tensorSheafTildeIso (R : CommRingCat.{u}) (M N : ModuleCat.{u} R) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(((Spec R).toRingedSpace)).presheaf, (((Spec R).toRingedSpace)).IsSheaf⟩).obj ((tilde M))).obj ((tilde N))) ≅ tilde (M ⊗ N) :=
  tensorSheafComparison (Spec R) (tilde M) (tilde N) ≪≫ (tildeTensorIso R M N).symm

/-- **The affine dual comparison, Stacks Tag 01I8.**  On `Spec R` the dual of the sheaf
associated to a module `M` of finite presentation is the sheaf associated to the `R`-dual
of `M`. -/
noncomputable def dualSheafTildeIso (R : CommRingCat.{u}) (M : ModuleCat.{u} R)
    [Module.FinitePresentation R M] :
    dualSheaf (tilde M) ≅ tilde (ModuleCat.of R (Module.Dual R M)) :=
  (internalHomTildeIso R M (ModuleCat.of R R)
      (sheafHomPackage (Spec R) (tilde M) (tilde (ModuleCat.of R R)))).iso ≪≫
    (tilde.functor R).mapIso
      (ModuleCat.homLinearEquiv (M := M) (N := ModuleCat.of R R) (S := R)).toModuleIso

/-- **The affine comparison for reflexive hulls.**  On `Spec R`, with `R` Noetherian, the
reflexive hull of the sheaf associated to a finite module `M` is the sheaf associated to the
double `R`-dual of `M`. -/
noncomputable def reflexiveHullTildeIso (R : CommRingCat.{u}) [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    dualSheaf (dualSheaf (tilde M)) ≅
      tilde (ModuleCat.of R (Module.Dual R (Module.Dual R M))) :=
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  haveI : _root_.IsNoetherian R (Module.Dual R M) := isNoetherian_linearMap R R M
  haveI : Module.Finite R (Module.Dual R M) := Module.IsNoetherian.finite R _
  haveI : Module.FinitePresentation R (Module.Dual R M) :=
    Module.finitePresentation_of_finite R _
  (dualIso (dualSheafTildeIso R M)).symm ≪≫
    dualSheafTildeIso R (ModuleCat.of R (Module.Dual R M))

/-- The reflexive hull of a tensor product of two sheaves isomorphic to associated sheaves, on
an affine Noetherian base: it is the associated sheaf of the double dual of the tensor product
of the two modules. -/
noncomputable def doubleDualTensorTildeIso (R : CommRingCat.{u}) [IsNoetherianRing R]
    {F G : (Spec R).Modules} {M N : ModuleCat.{u} R}
    [Module.Finite R M] [Module.Finite R N] (e : F ≅ tilde M) (e' : G ≅ tilde N) :
    dualSheaf (dualSheaf ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(((Spec R).toRingedSpace)).presheaf, (((Spec R).toRingedSpace)).IsSheaf⟩).obj (F)).obj (G)))) ≅
      tilde (ModuleCat.of R (Module.Dual R (Module.Dual R (M ⊗ N : ModuleCat.{u} R)))) :=
  haveI : Module.Finite R (M ⊗ N : ModuleCat.{u} R) := Module.Finite.tensorProduct R M N
  dualIso (dualIso (tensorSheafIso (Spec R) e e' ≪≫ tensorSheafTildeIso R M N)) ≪≫
    reflexiveHullTildeIso R (M ⊗ N)

end AlgebraicGeometry

end
