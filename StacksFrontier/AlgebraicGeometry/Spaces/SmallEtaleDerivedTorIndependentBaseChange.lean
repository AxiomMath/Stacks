module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.InterfaceUnitNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardPullbackTensorIso
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardReflectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeAffineSpaceChart
public import StacksFrontier.AlgebraicGeometry.Spaces.QcqsOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeCompLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackComparisonTorIndependent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTransposeBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaSnd
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceEtaleLocal
public import StacksFrontier.CategoryTheory.Adjunction.KunnethBaseChange

/-!
# Tor independent base change for algebraic spaces

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square of algebraic spaces with `f` quasi-compact and quasi-separated.  Stacks
08IR asserts that the base change map `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` is an isomorphism for
`E ∈ D_QCoh(𝒪_X)` when `X` and `Y'` are Tor independent over `Y`.

This file carries the step of the source's proof that runs over an affine `Y'`: through the two
factorizations of the Künneth map
`Rf_*E ⊗^L Rg_*𝒪_{Y'} ⟶ R(f ∘ g')_*(L(g')^*E ⊗^L L(f')^*𝒪_{Y'})`, the four projection formulas
of Stacks 08IN reduce the invertibility of `Rg_*` of the base change map at `E` to that of the
base change map of the transposed square at `𝒪_{Y'}`, and `Rg_*` reflects isomorphisms of
`D_QCoh(𝒪_{Y'})`.

It also carries the two reductions of the source's proof: to affine `Y` and `Y'`, through the
étale locality of the composite of Stacks 0DKH on both bases, and, over affine bases, to the
comparison `Lf^* ⟶ f^*` at `g_*𝒪_{Y'}`, through the five-isomorphism argument and affine base
change of modules for the transposed square at `𝒪_{Y'}`.

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent`: **Stacks
  08IR**.
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeMap_of_isIso_transpose`
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeMap_of_isAffineSpace_of_isIso`
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeComp_of_isIso_chartBaseChangeMap`

## References

* [Stacks Project, Tag 08IR](https://stacks.math.columbia.edu/tag/08IR)
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

/-- The base change `f'` of a quasi-compact quasi-separated morphism `f` is again so. -/
private theorem isQuasiCompact_and_isQuasiSeparated_of_isPullback (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) :
    IsQuasiCompact B S hS f'.hom ∧ IsQuasiSeparated B S hS f'.hom :=
  have sqh := AlgebraicSpaces.isPullback_hom B S hS sq
  ⟨isQuasiCompact_of_isPullback B S hS sqh hfqc, isQuasiSeparated_of_isPullback B S hS sqh hfqs⟩

/-- **Base change over an affine `Y'` from base change of the structure sheaf of `Y'`.**  For a
cartesian square with `f` and `g` quasi-compact and quasi-separated and `Y'` affine, the base
change map `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` is invertible at every `E ∈ D_QCoh(𝒪_X)` as soon as the
base change map `Lf^*Rg_*𝒪_{Y'} ⟶ Rg'_*L(f')^*𝒪_{Y'}` of the transposed square is. -/
theorem isIso_smallEtaleDerivedBaseChangeMap_of_isIso_transpose (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hgqc : IsQuasiCompact B S hS g.hom) (hgqs : IsQuasiSeparated B S hS g.hom)
    (hY' : IsAffineSpace B S hS Y'.1)
    (hT : IsIso (Stacks.CategoryTheory.BaseChange.map (smallEtaleDerivedModuleAdjunction B S hS g)
      (smallEtaleDerivedModuleAdjunction B S hS g')
      (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w)
      (smallEtaleDerivedModulePullbackCompIso B S hS f' g) (structureDerived Y')))
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : QcohDerived B S hS X E) :
    IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w E) := by
  obtain ⟨hf'qc, hf'qs⟩ := isQuasiCompact_and_isQuasiSeparated_of_isPullback B S hS f g f' g' sq
    hfqc hfqs
  obtain ⟨hg'qc, hg'qs⟩ := isQuasiCompact_and_isQuasiSeparated_of_isPullback B S hS g f g' f'
    sq.flip hgqc hgqs
  let O' := structureDerived Y'
  have hO' : QcohDerived B S hS Y' O' :=
    qcohDerived_singleFunctor_structureModule (X := Y'.1) (hX := Y'.2)
  let Rf := derivedModulePushforward B S hS f
  let Rg := derivedModulePushforward B S hS g
  let Lg := smallEtaleDerivedModulePullback B S hS g
  let Lg' := smallEtaleDerivedModulePullback B S hS g'
  let Lf' := smallEtaleDerivedModulePullback B S hS f'
  have hRf : QcohDerived B S hS Y (Rf.obj E) :=
    qcohDerived_derivedModulePushforward_obj B S hS f hfqc hfqs E hE
  have hRg : QcohDerived B S hS Y (Rg.obj O') :=
    qcohDerived_derivedModulePushforward_obj B S hS g hgqc hgqs O' hO'
  have hLg' : QcohDerived B S hS X' (Lg'.obj E) :=
    derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ g' E hE
  have hLf' : QcohDerived B S hS X' (Lf'.obj O') :=
    derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ f' O' hO'
  have key := Stacks.CategoryTheory.KunnethBaseChange.isIso_map_tensor_baseChange_of_isIso
    (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedModuleAdjunction B S hS g)
    (smallEtaleDerivedModuleAdjunction B S hS f') (smallEtaleDerivedModuleAdjunction B S hS g')
    (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y'))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X'))
    (smallEtaleDerivedPullbackTensorIso f).hom (smallEtaleDerivedPullbackTensorIso f').hom
    (smallEtaleDerivedPullbackTensorIso g).hom (smallEtaleDerivedPullbackTensorIso g').hom E O'
    (tensorComparisonCompatible_smallEtaleDerivedPullbackTensorIso f g f' g' sq.w _ _)
    (isIso_smallEtaleProjectionFormulaMap B S hS f hfqc hfqs E hE _ hRg) hT
    (isIso_smallEtaleProjectionFormulaMapSnd B S hS g' hg'qc hg'qs E hE _ hLf')
    (isIso_smallEtaleProjectionFormulaMapSnd B S hS g hgqc hgqs _ hRf O' hO')
    (isIso_smallEtaleProjectionFormulaMap B S hS f' hf'qc hf'qs _ hLg' O' hO')
  have hsrc : QcohDerived B S hS Y'
      (((smallEtaleDerivedTensor B S hS Y').obj (Lg.obj (Rf.obj E))).obj O') :=
    qcohDerived_smallEtaleDerivedTensor Y' _ _
      (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ g _ hRf) hO'
  have htgt : QcohDerived B S hS Y'
      (((smallEtaleDerivedTensor B S hS Y').obj
        ((derivedModulePushforward B S hS f').obj (Lg'.obj E))).obj O') :=
    qcohDerived_smallEtaleDerivedTensor Y' _ _
      (qcohDerived_derivedModulePushforward_obj B S hS f' hf'qc hf'qs _ hLg') hO'
  have h₁ := isIso_of_isIso_derivedModulePushforward_map g hY' hsrc htgt _ key
  have h₂ : IsIso (((smallEtaleDerivedTensor B S hS Y').flip.obj O').map
      (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w E)) := by
    have e : (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y')).map
        (Stacks.CategoryTheory.BaseChange.map (smallEtaleDerivedModuleAdjunction B S hS f)
          (smallEtaleDerivedModuleAdjunction B S hS f')
          (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
          (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w) E ×ₘ 𝟙 O') =
        ((smallEtaleDerivedTensor B S hS Y').flip.obj O').map
          (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w E) := by
      simp [smallEtaleDerivedModuleBaseChangeMap]
    rw [← e]
    exact h₁
  exact (NatIso.isIso_map_iff (smallEtaleDerivedTensorProduct B S hS Y').unitComplexNatIso _).1 h₂

section Main

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X}

/-- The composite of Stacks 0DKH attached to an isomorphism `φ` is invertible as soon as the base
change map is. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_of_isIso (w : g' ≫ f = f' ≫ g) (K : _) (K' : _)
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K') [IsIso φ]
    (hBC : IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' w K)) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' w K K' φ) :=
  IsIso.comp_isIso

/-- **Base change over affine bases, from a statement on `X`.**  For a cartesian square with
`f` quasi-compact and quasi-separated and `Y`, `Y'` affine, the base change map is invertible at
every `E ∈ D_QCoh(𝒪_X)` as soon as the comparison `Lf^*(g_*𝒪_{Y'}) ⟶ f^*(g_*𝒪_{Y'})` is: the
base change map `f^*g_*𝒪_{Y'} ⟶ g'_*(f')^*𝒪_{Y'}` of modules of the transposed square is
invertible by affine base change. -/
theorem isIso_smallEtaleDerivedBaseChangeMap_of_isAffineSpace_of_isIso
    (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsAffineSpace B S hS Y.1) (hY' : IsAffineSpace B S hS Y'.1)
    (h₃ : IsIso ((smallEtaleDerivedModulePullbackComparison B S hS f).app
      ((smallEtalePushforwardMapHomotopy B S hS g).obj (structureHomotopy B S hS Y'))))
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : QcohDerived B S hS X E) :
    IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w E) := by
  have hg : IsAffineHom B S hS g.hom := isAffineHom_of_isAffineSpace B S hS g.hom hY' hY
  have hg' : IsAffineHom B S hS g'.hom :=
    isAffineHom_of_isPullback (AlgebraicSpaces.isPullback_hom B S hS sq).flip hg
  have h₅ : IsIso ((moduleBaseChangeMap g f g' f' sq.w.symm).app
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y'))) :=
    isIso_moduleBaseChangeMap_app_of_isAffineSpace f g f' g' sq hY hY' _
      (SheafOfModules.isQuasicoherentOnSite_unit _)
  exact isIso_smallEtaleDerivedBaseChangeMap_of_isIso_transpose B S hS f g f' g' sq hfqc hfqs
    (isQuasiCompact_of_isAffineHom_hom g hg) (isQuasiSeparated_of_isAffineHom_hom g hg)
    hY' (isIso_transposeBaseChangeMap_structure_of_isIso B S hS f g f' g' sq.w hg hg' h₃
      (isIso_smallEtaleUnderivedBaseChangeMap_structureHomotopy B S hS g f g' f' sq.w.symm h₅))
    E hE

/-- **Stacks 08IR over affine bases.**  For a cartesian square with `f` quasi-compact and
quasi-separated, `Y` and `Y'` affine and `X`, `Y'` Tor independent over `Y`, the base change map
`Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` is invertible at every `E ∈ D_QCoh(𝒪_X)`. -/
theorem isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent_of_isAffineSpace
    (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsAffineSpace B S hS Y.1) (hY' : IsAffineSpace B S hS Y'.1)
    (hTor : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : QcohDerived B S hS X E) :
    IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w E) :=
  isIso_smallEtaleDerivedBaseChangeMap_of_isAffineSpace_of_isIso B S hS sq hfqc hfqs hY hY'
    (isIso_smallEtaleDerivedModulePullbackComparison_app_pushforwardStructure B S hS f g hY hY'
      hTor) E hE

/-- **Reduction of the base change map to squares of affine charts.**  For a cartesian square
and an isomorphism `φ : L(g')^*K ⟶ K'`, the composite of Stacks 0DKH is invertible as soon as the
base change map of every square of affine étale charts is invertible at the restriction of `K`. -/
theorem isIso_smallEtaleDerivedBaseChangeComp_of_isIso_chartBaseChangeMap
    (sq : IsPullback g' f' f g) (K : _) (K' : _)
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K') [IsIso φ]
    (h : ∀ (W : SmallEtale B S hS Y'.1) (V : SmallEtale B S hS Y.1) (q : W.1.left ⟶ V.1.left)
      (hq : yoneda.map q ≫ V.1.hom = W.1.hom ≫ g.hom),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) →
      IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS (chartBaseChangeProjection B S hS f V)
        (chartSpaceMapOver B S hS q) (chartBaseChangeProjection B S hS f' W)
        (chartBaseChangeSquareMap B S hS f g f' g' sq.w W V q hq)
        (isPullback_chartBaseChangeSquareMap B S hS f g f' g' sq W V q hq).w
        ((smallEtaleDerivedModulePullback B S hS (chartBaseChangeInclusion B S hS f V)).obj K))) :
    IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' sq.w K K' φ) :=
  isIso_smallEtaleDerivedBaseChangeComp_of_affineCharts B S hS f g f' g' sq K K' φ
    fun W V q hq hW hV => by
      have h1 : IsIso ((smallEtaleDerivedModulePullbackCompIso B S hS
            (chartBaseChangeSquareMap B S hS f g f' g' sq.w W V q hq)
            (chartBaseChangeInclusion B S hS f V)).hom.app K) := inferInstance
      have h2 : IsIso ((smallEtaleDerivedModulePullbackCongr B S hS
            (chartBaseChangeSquareMap_inclusion B S hS f g f' g' sq.w W V q hq)).hom.app K) :=
        inferInstance
      have h3 : IsIso ((smallEtaleDerivedModulePullbackCompIso B S hS
            (chartBaseChangeInclusion B S hS f' W) g').inv.app K) := inferInstance
      have h4 : IsIso ((smallEtaleDerivedModulePullback B S hS
        (chartBaseChangeInclusion B S hS f' W)).map φ) := inferInstance
      have := IsIso.comp_isIso' h1 (IsIso.comp_isIso' h2 (IsIso.comp_isIso' h3 h4))
      exact isIso_smallEtaleDerivedBaseChangeComp_of_isIso B S hS _ _ _ _ (h W V q hq hW hV)

end Main

/-- **Stacks 08IR.**  Let `g : Y' ⟶ Y` be a morphism of algebraic spaces and `f : X ⟶ Y` a
quasi-compact and quasi-separated one, with base change `f' : X' ⟶ Y'`, `g' : X' ⟶ X`.  If `X`
and `Y'` are Tor independent over `Y`, then the base change map
`Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` is an isomorphism for every `E ∈ D_QCoh(𝒪_X)`. -/
@[stacks 08IR]
theorem isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hTor : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : QcohDerived B S hS X E) :
    IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w E) := by
  rw [← smallEtaleDerivedBaseChangeComp_id B S hS f g f' g' sq.w E]
  refine isIso_smallEtaleDerivedBaseChangeComp_of_isIso_chartBaseChangeMap B S hS sq E _ (𝟙 _)
    fun W V q hq hW hV => ?_
  have sqV := isPullback_chartBaseChangeInclusion B S hS f V
  have sqc := isPullback_chartBaseChangeSquareMap B S hS f g f' g' sq W V q hq
  obtain ⟨hqc, hqs⟩ := isQuasiCompact_and_isQuasiSeparated_of_isPullback B S hS f _ _ _ sqV hfqc
    hfqs
  have hT₀ := torIndependent_comp_of_isEtale_source B S hS f.hom g.hom
    (isEtale_chartBaseChangeInclusion B S hS f V) (isEtale_chartToSpace B S hS Y' W) hTor
  have hT : TorIndependent (chartBaseChangeSpace B S hS f V).2 (chartSpace B S hS Y' W).2
      (chartSpace B S hS Y V).2 (chartBaseChangeProjection B S hS f V).hom
      (chartSpaceMapOver B S hS q).hom := by
    refine torIndependent_of_comp_isEtale_base B S hS (isEtale_chartToSpace B S hS Y V) _ _ ?_
    have e₁ := (AlgebraicSpaces.isPullback_hom B S hS sqV).w
    have e₂ : (chartSpaceMapOver B S hS q).hom ≫ (chartToSpace B S hS Y V).hom =
        (chartToSpace B S hS Y' W).hom ≫ g.hom :=
      congrArg (fun k => k.hom) (chartSpaceMapOver_comp_chartToSpace B S hS g q hq)
    exact e₂.symm ▸ e₁ ▸ hT₀
  exact isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent_of_isAffineSpace B S hS sqc
    hqc hqs (isAffineSpace_chartSpace B S hS Y V hV) (isAffineSpace_chartSpace B S hS Y' W hW)
    hT _ (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _
      (chartBaseChangeInclusion B S hS f V) E hE)

end AlgebraicGeometry.Space

end
