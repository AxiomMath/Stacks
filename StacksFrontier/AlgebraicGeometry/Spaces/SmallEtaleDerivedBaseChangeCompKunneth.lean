module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.InterfaceUnitNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTorIndependentBaseChange
public import StacksFrontier.CategoryTheory.Adjunction.KunnethBaseChangeComp

/-!
# The base change map attached to a map out of a derived pullback, over an affine base change

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square of algebraic spaces with `f` and `g` quasi-compact and quasi-separated and
`Y'` affine, let `E ∈ D_QCoh(𝒪_X)`, `K' ∈ D_QCoh(𝒪_{X'})` and `φ : L(g')^*E ⟶ K'`.  Through the
Künneth argument of Stacks 08IR, the composite `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E ⟶ Rf'_*K'` of
Stacks 0DKH is invertible as soon as the map on `X`

`E ⊗ᴸ Lf^*Rg_*𝒪_{Y'} ⟶ E ⊗ᴸ Rg'_*L(f')^*𝒪_{Y'} ⟶ Rg'_*(L(g')^*E ⊗ᴸ L(f')^*𝒪_{Y'})
  ⟶ Rg'_*(K' ⊗ᴸ L(f')^*𝒪_{Y'})`

is invertible.  The latter is a statement on `X`, local on `X`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleTensorBaseChangeCompMap`

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeComp_of_isIso_tensor`
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeComp_of_isIso_tensorBaseChangeCompMap`
* `AlgebraicGeometry.Space.isIso_smallEtaleTensorBaseChangeCompMap_of_isIso`: the converse over
  an affine `X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- The map `E ⊗ᴸ Lf^*Rg_*𝒪_{Y'} ⟶ Rg'_*(K' ⊗ᴸ L(f')^*𝒪_{Y'})` on `X` attached to
`φ : L(g')^*E ⟶ K'`: the transposed base change map at `𝒪_{Y'}` in the second factor, the
projection formula of `g'`, and `Rg'_*` of `φ` tensored with `L(f')^*𝒪_{Y'}`. -/
def smallEtaleTensorBaseChangeCompMap (w : g' ≫ f = f' ≫ g)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj E ⟶ K') :=
  Stacks.CategoryTheory.KunnethBaseChange.tensorBaseChangeCompMap
    (smallEtaleDerivedModuleAdjunction B S hS g) (smallEtaleDerivedModuleAdjunction B S hS g')
    (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' w)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X'))
    (smallEtaleDerivedPullbackTensorIso g').hom E (structureDerived Y') φ

/-- In a cartesian square, `f'` and `g'` are quasi-compact and quasi-separated as soon as `f`
and `g` are. -/
private theorem isQuasiCompact_and_isQuasiSeparated_of_isPullback (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hgqc : IsQuasiCompact B S hS g.hom) (hgqs : IsQuasiSeparated B S hS g.hom) :
    IsQuasiCompact B S hS f'.hom ∧ IsQuasiSeparated B S hS f'.hom ∧
      IsQuasiCompact B S hS g'.hom ∧ IsQuasiSeparated B S hS g'.hom := by
  have sqh := AlgebraicSpaces.isPullback_hom B S hS sq
  exact ⟨isQuasiCompact_of_isPullback B S hS sqh hfqc,
    isQuasiSeparated_of_isPullback B S hS sqh hfqs,
    isQuasiCompact_of_isPullback B S hS sqh.flip hgqc,
    isQuasiSeparated_of_isPullback B S hS sqh.flip hgqs⟩

/-- **Stacks 0DKH over an affine `Y'`, reduced to a statement on `X`.**  For a cartesian square
with `f` and `g` quasi-compact and quasi-separated and `Y'` affine, `E ∈ D_QCoh(𝒪_X)`,
`K' ∈ D_QCoh(𝒪_{X'})` and `φ : L(g')^*E ⟶ K'`, the composite
`Lg^*Rf_*E ⟶ Rf'_*L(g')^*E ⟶ Rf'_*K'` is invertible as soon as
`smallEtaleTensorBaseChangeCompMap` is. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_of_isIso_tensor (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hgqc : IsQuasiCompact B S hS g.hom) (hgqs : IsQuasiSeparated B S hS g.hom)
    (hY' : IsAffineSpace B S hS Y'.1)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : QcohDerived B S hS X E)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj E ⟶ K')
    (hψ : IsIso (smallEtaleTensorBaseChangeCompMap B S hS f g f' g' sq.w E K' φ)) :
    IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w E ≫
      (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
        (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f')).map φ) := by
  obtain ⟨hf'qc, hf'qs, hg'qc, hg'qs⟩ :=
    isQuasiCompact_and_isQuasiSeparated_of_isPullback B S hS f g f' g' sq hfqc hfqs hgqc hgqs
  let O' := structureDerived Y'
  have hO' : QcohDerived B S hS Y' O' :=
    qcohDerived_singleFunctor_structureModule (X := Y'.1) (hX := Y'.2)
  let Rf := derivedModulePushforward B S hS f
  let Rg := derivedModulePushforward B S hS g
  let Lg := smallEtaleDerivedModulePullback B S hS g
  have hRf : QcohDerived B S hS Y (Rf.obj E) :=
    qcohDerived_derivedModulePushforward_obj B S hS f hfqc hfqs E hE
  have hRg : QcohDerived B S hS Y (Rg.obj O') :=
    qcohDerived_derivedModulePushforward_obj B S hS g hgqc hgqs O' hO'
  have key := Stacks.CategoryTheory.KunnethBaseChange.isIso_map_tensor_baseChange_comp_of_isIso
    (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedModuleAdjunction B S hS g)
    (smallEtaleDerivedModuleAdjunction B S hS f') (smallEtaleDerivedModuleAdjunction B S hS g')
    (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y'))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X'))
    (smallEtaleDerivedPullbackTensorIso f).hom (smallEtaleDerivedPullbackTensorIso f').hom
    (smallEtaleDerivedPullbackTensorIso g).hom (smallEtaleDerivedPullbackTensorIso g').hom E O' φ
    (tensorComparisonCompatible_smallEtaleDerivedPullbackTensorIso f g f' g' sq.w _ _)
    (isIso_smallEtaleProjectionFormulaMap B S hS f hfqc hfqs E hE _ hRg)
    (@Functor.map_isIso _ _ _ _ _ _ _ _ hψ)
    (isIso_smallEtaleProjectionFormulaMapSnd B S hS g hgqc hgqs _ hRf O' hO')
    (isIso_smallEtaleProjectionFormulaMap B S hS f' hf'qc hf'qs K' hK' O' hO')
  have hsrc : QcohDerived B S hS Y'
      (((smallEtaleDerivedTensor B S hS Y').obj (Lg.obj (Rf.obj E))).obj O') :=
    qcohDerived_smallEtaleDerivedTensor Y' _ _
      (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ g _ hRf) hO'
  have htgt : QcohDerived B S hS Y'
      (((smallEtaleDerivedTensor B S hS Y').obj
        ((derivedModulePushforward B S hS f').obj K')).obj O') :=
    qcohDerived_smallEtaleDerivedTensor Y' _ _
      (qcohDerived_derivedModulePushforward_obj B S hS f' hf'qc hf'qs _ hK') hO'
  have h₁ := isIso_of_isIso_derivedModulePushforward_map g hY' hsrc htgt _ key
  exact Stacks.CategoryTheory.KunnethBaseChange.isIso_of_isIso_uncurry_map_prod_id
    (smallEtaleDerivedTensor B S hS Y') O'
    (smallEtaleDerivedTensorProduct B S hS Y').unitComplexNatIso _ h₁

/-- `isIso_smallEtaleDerivedBaseChangeComp_of_isIso_tensor` for the composite
`AlgebraicGeometry.Space.smallEtaleDerivedBaseChangeComp` of Stacks 0DKH. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_of_isIso_tensorBaseChangeCompMap
    (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hgqc : IsQuasiCompact B S hS g.hom) (hgqs : IsQuasiSeparated B S hS g.hom)
    (hY' : IsAffineSpace B S hS Y'.1)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : QcohDerived B S hS X E)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj E ⟶ K')
    (hψ : IsIso (smallEtaleTensorBaseChangeCompMap B S hS f g f' g' sq.w E K' φ)) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' sq.w E K' φ) :=
  isIso_smallEtaleDerivedBaseChangeComp_of_isIso_tensor B S hS f g f' g' sq hfqc hfqs hgqc hgqs
    hY' E hE K' hK' φ hψ

/-- **The converse over an affine `X`.**  For a cartesian square with `f` and `g`
quasi-compact and quasi-separated and `X`, `Y'` affine, `smallEtaleTensorBaseChangeCompMap` is
invertible as soon as the composite `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E ⟶ Rf'_*K'` of Stacks 0DKH is. -/
theorem isIso_smallEtaleTensorBaseChangeCompMap_of_isIso (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hgqc : IsQuasiCompact B S hS g.hom) (hgqs : IsQuasiSeparated B S hS g.hom)
    (hX : IsAffineSpace B S hS X.1)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : QcohDerived B S hS X E)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj E ⟶ K')
    (h : IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' sq.w E K' φ)) :
    IsIso (smallEtaleTensorBaseChangeCompMap B S hS f g f' g' sq.w E K' φ) := by
  obtain ⟨hf'qc, hf'qs, hg'qc, hg'qs⟩ :=
    isQuasiCompact_and_isQuasiSeparated_of_isPullback B S hS f g f' g' sq hfqc hfqs hgqc hgqs
  let O' := structureDerived Y'
  have hO' : QcohDerived B S hS Y' O' :=
    qcohDerived_singleFunctor_structureModule (X := Y'.1) (hX := Y'.2)
  let Rf := derivedModulePushforward B S hS f
  let Rg := derivedModulePushforward B S hS g
  have hRf : QcohDerived B S hS Y (Rf.obj E) :=
    qcohDerived_derivedModulePushforward_obj B S hS f hfqc hfqs E hE
  have hRg : QcohDerived B S hS Y (Rg.obj O') :=
    qcohDerived_derivedModulePushforward_obj B S hS g hgqc hgqs O' hO'
  have key := Stacks.CategoryTheory.KunnethBaseChange.isIso_map_tensorBaseChangeCompMap_iff
    (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedModuleAdjunction B S hS g)
    (smallEtaleDerivedModuleAdjunction B S hS f') (smallEtaleDerivedModuleAdjunction B S hS g')
    (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y'))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X'))
    (smallEtaleDerivedPullbackTensorIso f).hom (smallEtaleDerivedPullbackTensorIso f').hom
    (smallEtaleDerivedPullbackTensorIso g).hom (smallEtaleDerivedPullbackTensorIso g').hom E O' φ
    (tensorComparisonCompatible_smallEtaleDerivedPullbackTensorIso f g f' g' sq.w _ _)
    (isIso_smallEtaleProjectionFormulaMap B S hS f hfqc hfqs E hE _ hRg)
    (isIso_smallEtaleProjectionFormulaMapSnd B S hS g hgqc hgqs _ hRf O' hO')
    (isIso_smallEtaleProjectionFormulaMap B S hS f' hf'qc hf'qs K' hK' O' hO')
  have hT : IsIso ((Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y')).map
      ((smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w E ≫
        (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f')).map φ) ×ₘ
        𝟙 O')) := by
    have h' : IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w E ≫
        (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f')).map φ) := h
    have hc : (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y')).map
        ((smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w E ≫
          (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
            (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f')).map φ) ×ₘ
          𝟙 O') =
        ((smallEtaleDerivedTensor B S hS Y').map
          (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w E ≫
          (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
            (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f')).map φ)).app
          O' := by simp
    rw [hc]
    infer_instance
  have hRf' := key.mpr (@Functor.map_isIso _ _ _ _ _ _ _ _ hT)
  have hsrc : QcohDerived B S hS X
      (((smallEtaleDerivedTensor B S hS X).obj E).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj (Rg.obj O'))) :=
    qcohDerived_smallEtaleDerivedTensor X _ _ hE
      (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ f _ hRg)
  have htgt : QcohDerived B S hS X
      ((derivedModulePushforward B S hS g').obj
        (((smallEtaleDerivedTensor B S hS X').obj K').obj
          ((smallEtaleDerivedModulePullback B S hS f').obj O'))) :=
    qcohDerived_derivedModulePushforward_obj B S hS g' hg'qc hg'qs _
      (qcohDerived_smallEtaleDerivedTensor X' _ _ hK'
        (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ f' _ hO'))
  exact isIso_of_isIso_derivedModulePushforward_map f hX hsrc htgt _ hRf'

end AlgebraicGeometry.Space

end
