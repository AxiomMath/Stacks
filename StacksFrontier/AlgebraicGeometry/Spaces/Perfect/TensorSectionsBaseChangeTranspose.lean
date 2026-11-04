module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseDerivedSectionsTranspose
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaSnd
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensorClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeTensorTranspose
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSingleCounitCompatible

/-!
# The base change map of `RΓ(X, E ⊗^𝐋 K)` along a map `K ⟶ Rg'_* Kₙ`

Let `g' : X' ⟶ X` be a morphism of algebraic spaces, `E` an object of `D(𝒪_X)` and
`u : K ⟶ Rg'_* K'` a morphism of `D(𝒪_X)`. The composite

`E ⊗^𝐋 K ⟶ E ⊗^𝐋 Rg'_* K' ⟶ Rg'_*(L(g')^*E ⊗^𝐋 K')`

of `E ⊗^𝐋 u` and the projection formula map has as transpose under `L(g')^* ⊣ Rg'_*` the
comparison `L(g')^*(E ⊗^𝐋 K) ≅ L(g')^*E ⊗^𝐋 L(g')^*K` followed by `L(g')^*E ⊗^𝐋 -` of the
transpose of `u`.

Over a cartesian square of algebraic spaces

```
X' --g'--> X
|f'        |f
U' --g---> U
```

with `U`, `U'` affine, `f` of finite presentation, `E` perfect and `K = 𝒢^•` a bounded complex
of `𝒪_X`-modules of finite presentation, flat over `U`, with support proper over `U`, the base
change map `RΓ(X, E ⊗^𝐋 K) ⊗^𝐋_R R' ⟶ RΓ(X', L(g')^*E ⊗^𝐋 K')` built from such a transpose is an
isomorphism as soon as the transpose of `u` is `L(g')^*𝒢^• ⟶ (g')^*𝒢^•` followed by an
isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleProjectionFormulaComp`: `E ⊗^𝐋 u` followed by the
  projection formula map.

## Main results

* `AlgebraicGeometry.Space.homEquiv_symm_smallEtaleProjectionFormulaComp`: its transpose.
* `AlgebraicGeometry.Space.isIso_affineBaseDerivedSectionsBaseChangeMap_comp_tensor`: the base
  change map followed by the comparison `L(g')^*(E ⊗^𝐋 K) ≅ L(g')^*E ⊗^𝐋 L(g')^*K` and
  `L(g')^*E ⊗^𝐋 τ` is invertible when `τ` is the comparison `L(g')^*𝒢^• ⟶ (g')^*𝒢^•` read through
  isomorphisms.
* `AlgebraicGeometry.Space.isIso_affineBaseDerivedSectionsBaseChangeMap_comp_single`,
  `AlgebraicGeometry.Space.isIso_affineBaseDerivedSectionsBaseChangeMap_comp_projectionFormula`:
  the case `K = M[0]`, `u : M[0] ⟶ (g'_*M')[0] ≅ Rg'_*(M'[0])` with
  `AlgebraicGeometry.Space.SingleCounitCompatible`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Prod

universe u

namespace Stacks.ProjectionFormula

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
  (α : Functor.uncurry.obj T ⋙ L ⟶ L.prod L ⋙ Functor.uncurry.obj T')

/-- **The transpose of `E ⊗ u` followed by the projection formula map**, for curried bifunctors:
for `u : K ⟶ R K'`, the transpose of `T(E, u)` followed by the projection formula map at
`(E, K')` is `α` at `(E, K)` followed by `T'(L E, -)` of the transpose of `u`. -/
theorem homEquiv_symm_map_comp_adjunctionTensorMapSnd (E K : C) (K' : D) (u : K ⟶ R.obj K') :
    (adj.homEquiv _ _).symm ((T.obj E).map u ≫
        adjunctionTensorMapSnd adj (Functor.uncurry.obj T) (Functor.uncurry.obj T') α E K') =
      α.app (E, K) ≫ (T'.obj (L.obj E)).map ((adj.homEquiv _ _).symm u) := by
  have h := adjunctionTensorMapSnd_comp_homEquiv adj (Functor.uncurry.obj T)
    (Functor.uncurry.obj T') α E K K' ((adj.homEquiv _ _).symm u)
  have h₀ : (Functor.uncurry.obj T).map (𝟙 E ×ₘ u) = (T.obj E).map u := by simp
  rw [Equiv.apply_symm_apply, h₀] at h
  rw [h]
  exact (Equiv.symm_apply_apply _ _).trans (by simp)

/-- **`α` is natural in the second factor**, for curried bifunctors: for `k : K₀ ⟶ K`,
`L(T(E, k))` followed by `α` at `(E, K)` is `α` at `(E, K₀)` followed by `T'(L E, L k)`. -/
theorem map_obj_map_comp_app (E : C) {K₀ K : C} (k : K₀ ⟶ K) :
    L.map ((T.obj E).map k) ≫ α.app (E, K) = α.app (E, K₀) ≫ (T'.obj (L.obj E)).map (L.map k) := by
  have h := α.naturality (𝟙 E ×ₘ k)
  simp only [Functor.comp_map, Functor.uncurry_obj_map, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp, Functor.prod_map] at h
  simpa using h

/-- **Transporting `α ≫ T'(L E, c)` along isomorphisms in the second factor**: for
`e : K₀ ≅ K`, `w : P ≅ P'`, `c : L K₀ ⟶ P` and `τ : L K ⟶ P'` with `c ≫ w = L e ≫ τ`,
`L(T(E, e))` followed by `α` at `(E, K)` and `T'(L E, τ)` is `α` at `(E, K₀)` followed by
`T'(L E, c)` and `T'(L E, w)`. -/
theorem map_obj_map_comp_app_comp_map_eq (E : C) {K₀ K : C} (e : K₀ ≅ K) {P P' : D} (w : P ≅ P')
    (c : L.obj K₀ ⟶ P) (τ : L.obj K ⟶ P') (h : c ≫ w.hom = L.map e.hom ≫ τ) :
    L.map ((T.obj E).map e.hom) ≫ α.app (E, K) ≫ (T'.obj (L.obj E)).map τ =
      (α.app (E, K₀) ≫ (T'.obj (L.obj E)).map c) ≫ (T'.obj (L.obj E)).map w.hom := by
  rw [reassoc_of% (map_obj_map_comp_app T T' α E e.hom), Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, h]

end Stacks.ProjectionFormula

namespace AlgebraicGeometry.Space

/-! The derived categories are the standard model on the sheaves of modules over the ring sheaf
of the small étale ringed topos. -/
section StandardModel

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard SheafOfModules.instAbelian

section ProjectionFormula

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X X' : AlgebraicSpaces B S hS}

/-- **`E ⊗^𝐋 u` followed by the projection formula map**, for `u : K ⟶ Rg'_* K'`:
`E ⊗^𝐋 K ⟶ E ⊗^𝐋 Rg'_* K' ⟶ Rg'_*(L(g')^*E ⊗^𝐋 K')`. -/
def smallEtaleProjectionFormulaComp (g' : X' ⟶ X)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    {K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))}
    (u : K ⟶ (derivedModulePushforward B S hS g').obj K') :
    ((smallEtaleDerivedTensor B S hS X).obj E).obj K ⟶
      (derivedModulePushforward B S hS g').obj
        (((smallEtaleDerivedTensor B S hS X').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj E)).obj K') :=
  ((smallEtaleDerivedTensor B S hS X).obj E).map u ≫
    (smallEtaleProjectionFormulaSndNatTrans g' K').app E

/-- **The transpose of `E ⊗^𝐋 u` followed by the projection formula map** under
`L(g')^* ⊣ Rg'_*` is the comparison `L(g')^*(E ⊗^𝐋 K) ≅ L(g')^*E ⊗^𝐋 L(g')^*K` followed by
`L(g')^*E ⊗^𝐋 -` of the transpose of `u`. -/
theorem homEquiv_symm_smallEtaleProjectionFormulaComp (g' : X' ⟶ X)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    {K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))}
    (u : K ⟶ (derivedModulePushforward B S hS g').obj K') :
    ((smallEtaleDerivedModuleAdjunction B S hS g').homEquiv _ _).symm
        (smallEtaleProjectionFormulaComp g' E u) =
      (smallEtaleDerivedPullbackTensorIso g').hom.app (E, K) ≫
        ((smallEtaleDerivedTensor B S hS X').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj E)).map
          (((smallEtaleDerivedModuleAdjunction B S hS g').homEquiv _ _).symm u) :=
  Stacks.ProjectionFormula.homEquiv_symm_map_comp_adjunctionTensorMapSnd
    (smallEtaleDerivedModuleAdjunction B S hS g') (smallEtaleDerivedTensor B S hS X)
    (smallEtaleDerivedTensor B S hS X') (smallEtaleDerivedPullbackTensorIso g').hom E K K' u

end ProjectionFormula

section BaseChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The comparison `L(g')^*(E ⊗ K) ≅ L(g')^*E ⊗ L(g')^*K` is natural in `K`**: for
`k : K₀ ⟶ K` the pullback of `E ⊗ k` followed by the comparison at `(E, K)` is the comparison at
`(E, K₀)` followed by `L(g')^*E ⊗ L(g')^*k`. -/
theorem smallEtaleDerivedPullbackTensorIso_hom_app_naturality_snd {X X' : AlgebraicSpaces B S hS}
    (g' : X' ⟶ X)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    {K₀ K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (k : K₀ ⟶ K) :
    (smallEtaleDerivedModulePullback B S hS g').map
      (((smallEtaleDerivedTensor B S hS X).obj E).map k) ≫
        (smallEtaleDerivedPullbackTensorIso g').hom.app (E, K) =
      (smallEtaleDerivedPullbackTensorIso g').hom.app (E, K₀) ≫
        ((smallEtaleDerivedTensor B S hS X').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj E)).map
          ((smallEtaleDerivedModulePullback B S hS g').map k) :=
  Stacks.ProjectionFormula.map_obj_map_comp_app (smallEtaleDerivedTensor B S hS X)
    (smallEtaleDerivedTensor B S hS X') (smallEtaleDerivedPullbackTensorIso g').hom E k

variable {U' U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  {X X' : AlgebraicSpaces B S hS} (g : U' ⟶ U)
  (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
  (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) (g' : X' ⟶ X)

/-- **The base change map of `RΓ(X, E ⊗^𝐋 K)` is invertible** when `K = 𝒢^•` is a bounded
complex of `𝒪_X`-modules of finite presentation, flat over `U`, with support proper over `U`, `f`
is of finite presentation and `E` is perfect: for a cartesian square, `K ≅ 𝒢^•`,
`K' ≅ (g')^*𝒢^•` and `τ : L(g')^*K ⟶ K'` the comparison `L(g')^*𝒢^• ⟶ (g')^*𝒢^•` read through these
isomorphisms, the map `RΓ(X, E ⊗^𝐋 K) ⊗^𝐋_R R' ⟶ RΓ(X', L(g')^*E ⊗^𝐋 K')` (the base change map
followed by the comparison `L(g')^*(E ⊗^𝐋 K) ≅ L(g')^*E ⊗^𝐋 L(g')^*K` and `L(g')^*E ⊗^𝐋 τ`) is an
isomorphism. -/
theorem isIso_affineBaseDerivedSectionsBaseChangeMap_comp_tensor
    (sq : IsPullback g' f' f (representedSpaceMap B S hS g))
    (hf : IsFinitePresentation B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : {i : ℤ | ¬ IsZero (G.X i)}.Finite) (hGfp : ∀ n, (G.X n).IsFinitePresentation)
    (hGflat : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n))
    (hGsupp : ∀ n, HasProperSupport B S hS X.2 (isAlgebraicSpace_yoneda B S hS U) f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1)
      ((SheafOfModules.toSheaf _).obj (G.X n)))
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (eK : DerivedCategory.Q.obj G ≅ K)
    {K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))}
    (v : (Arrow.mk (smallEtaleDerivedPullbackQComparison g' G)).right ≅ K')
    (hK : QcohDerived B S hS X K) (τ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K')
    (hτ : τ = (smallEtaleDerivedModulePullback B S hS g').map eK.inv ≫
      smallEtaleDerivedPullbackQComparison g' G ≫ v.hom) :
    IsIso (affineBaseDerivedSectionsBaseChangeMap B S hS g f f' g' sq.w
        (((smallEtaleDerivedTensor B S hS X).obj E).obj K) ≫
      (derivedModulePushforward B S hS f' ⋙ representedAffineDerivedSections B S hS U').map
        ((smallEtaleDerivedPullbackTensorIso g').hom.app (E, K) ≫
          ((smallEtaleDerivedTensor B S hS X').obj
            ((smallEtaleDerivedModulePullback B S hS g').obj E)).map τ)) := by
  have hEK : QcohDerived B S hS X (((smallEtaleDerivedTensor B S hS X).obj E).obj K) :=
    qcohDerived_smallEtaleDerivedTensor X E K (qcohDerived_of_isPerfect B S hS X E hE) hK
  have h₁ := isIso_representedAffineDerivedSectionsBaseChangeMap B S hS g
    ((derivedModulePushforward B S hS f).obj (((smallEtaleDerivedTensor B S hS X).obj E).obj K))
    (qcohDerived_derivedModulePushforward_obj B S hS f hf.2.1 hf.2.2 _ hEK)
  obtain ⟨m, hm, hQ⟩ : ∃ m, IsIso m ∧ smallEtaleDerivedModulePullbackQComparison g' G =
      smallEtaleDerivedPullbackQComparison g' G ≫ m := by
    refine ⟨_, ?_, rfl⟩
    refine @Functor.map_isIso _ ?_ _ _ _ ?_ _ _ ?_
    exact NatIso.isIso_app_of_isIso _ G
  let w := (asIso m).symm ≪≫ v
  have h₂ := (isIso_smallEtaleDerivedBaseChangeComp_iff_of_iso B S hS f
    (representedSpaceMap B S hS g) f' g' sq.w _ _ _ _ _
    ((smallEtaleDerivedPullbackTensorIso g').hom.app (E, K) ≫
      ((smallEtaleDerivedTensor B S hS X').obj
        ((smallEtaleDerivedModulePullback B S hS g').obj E)).map τ)
    (((smallEtaleDerivedTensor B S hS X).obj E).mapIso eK)
    (((smallEtaleDerivedTensor B S hS X').obj
      ((smallEtaleDerivedModulePullback B S hS g').obj E)).mapIso w) ?_).1
    ((isPerfect_derivedModulePushforward_derivedTensor_and_isIso_baseChange f hf E hE G hGb
      hGfp hGflat hGsupp).2 (representedSpaceMap B S hS g) f' g' sq)
  · let bc := smallEtaleDerivedModuleBaseChangeMap B S hS f (representedSpaceMap B S hS g)
        f' g' sq.w (((smallEtaleDerivedTensor B S hS X).obj E).obj K)
    let φ₁ := (derivedModulePushforward B S hS f').map
      ((smallEtaleDerivedPullbackTensorIso g').hom.app (E, K) ≫
        ((smallEtaleDerivedTensor B S hS X').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj E)).map τ)
    have h₃ : IsIso (bc ≫ φ₁) := h₂
    have h₄ : IsIso ((representedAffineDerivedSections B S hS U').map (bc ≫ φ₁)) :=
      ((representedAffineDerivedSections B S hS U').mapIso (@asIso _ _ _ _ (bc ≫ φ₁) h₃)).isIso_hom
    have h₅ : IsIso ((representedAffineDerivedSections B S hS U').map bc ≫
        (representedAffineDerivedSections B S hS U').map φ₁) :=
      (congrArg IsIso ((representedAffineDerivedSections B S hS U').map_comp bc φ₁)).mp h₄
    rw [affineBaseDerivedSectionsBaseChangeMap_eq, Category.assoc]
    exact IsIso.comp_isIso' h₁ h₅
  · have hc : smallEtaleDerivedModulePullbackQComparison g' G ≫ w.hom =
        (smallEtaleDerivedModulePullback B S hS g').map eK.hom ≫ τ := by
      rw [hτ, ← Functor.map_comp_assoc, eK.hom_inv_id, CategoryTheory.Functor.map_id,
        Category.id_comp, hQ]
      change (smallEtaleDerivedPullbackQComparison g' G ≫ m) ≫ (inv m ≫ v.hom) = _
      rw [Category.assoc, IsIso.hom_inv_id_assoc]
    exact Stacks.ProjectionFormula.map_obj_map_comp_app_comp_map_eq
      (smallEtaleDerivedTensor B S hS X) (smallEtaleDerivedTensor B S hS X')
      (smallEtaleDerivedPullbackTensorIso g').hom E eK w
      (smallEtaleDerivedModulePullbackQComparison g' G) τ hc

/-- **The base change map of `RΓ(X, E ⊗^𝐋 M[0])` along the transpose of an affine direct image is
invertible**: for a cartesian square with `f` of finite presentation and `g'` affine, `E` perfect,
`M` of finite presentation, flat over `U` with support proper over `U`, `M'` quasi-coherent on
`X'` and `a : M ⟶ g'_*M'` satisfying `AlgebraicGeometry.Space.SingleCounitCompatible`, the map
`RΓ(X, E ⊗^𝐋 M[0]) ⊗^𝐋_R R' ⟶ RΓ(X', L(g')^*E ⊗^𝐋 M'[0])` (the base change map, then the
pullback–tensor comparison and `L(g')^*E ⊗^𝐋 -` of the transpose of
`M[0] ⟶ (g'_*M')[0] ≅ Rg'_*(M'[0])`) is an isomorphism. -/
theorem isIso_affineBaseDerivedSectionsBaseChangeMap_comp_single
    (sq : IsPullback g' f' f (representedSpaceMap B S hS g))
    (hf : IsFinitePresentation B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (M : Modules.{u, u} B S hS X.1 X.2) (hMfp : M.IsFinitePresentation)
    (hMflat : IsFlatOver B S hS X.2 f.hom M)
    (hMsupp : HasProperSupport B S hS X.2 (isAlgebraicSpace_yoneda B S hS U) f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1)
      ((SheafOfModules.toSheaf _).obj M))
    (hg' : IsAffineHom B S hS g'.hom) (M' : Modules.{u, u} B S hS X'.1 X'.2)
    (hM' : M'.IsQuasicoherentOnSite) (a : M ⟶ (modulePushforward B S hS g').obj M')
    (hM : QcohDerived B S hS X ((spaceDerivedSingle B S hS X 0).obj M))
    (h : SingleCounitCompatible g' hg' M' hM' a) :
    IsIso (affineBaseDerivedSectionsBaseChangeMap B S hS g f f' g' sq.w
        (((smallEtaleDerivedTensor B S hS X).obj E).obj ((spaceDerivedSingle B S hS X 0).obj M)) ≫
      (derivedModulePushforward B S hS f' ⋙ representedAffineDerivedSections B S hS U').map
        ((smallEtaleDerivedPullbackTensorIso g').hom.app
          (E, (spaceDerivedSingle B S hS X 0).obj M) ≫
          ((smallEtaleDerivedTensor B S hS X').obj
            ((smallEtaleDerivedModulePullback B S hS g').obj E)).map
            (((smallEtaleDerivedModuleAdjunction B S hS g').homEquiv _ _).symm
              ((spaceDerivedSingle B S hS X 0).map a ≫
                (derivedModulePushforwardSingleIsoOfIsAffineHom B S hS g' hg' M' hM').inv :
                _ ⟶ (derivedModulePushforward B S hS g').obj
                  ((spaceDerivedSingle B S hS X' 0).obj M'))))) := by
  obtain ⟨v, hv⟩ := h
  let G := (HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (ComplexShape.up ℤ) 0).obj ((spaceToToposModules X).obj M)
  have hGz : ∀ i : ℤ, i ≠ 0 → IsZero (G.X i) := fun i hi =>
    HomologicalComplex.isZero_single_obj_X _ _ _ _ hi
  have hX : G.X 0 = M := by
    simp only [G, HomologicalComplex.single]
    rfl
  have hGb : {i : ℤ | ¬ IsZero (G.X i)}.Finite :=
    (Set.finite_singleton (0 : ℤ)).subset fun i hi => by
      by_contra h
      exact hi (hGz i h)
  let eK :=
    ((DerivedCategory.singleFunctorIsoCompQ
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) 0).app
        ((spaceToToposModules X).obj M)).symm ≪≫ ((singleSpaceToToposIso X).app M).symm
  refine isIso_affineBaseDerivedSectionsBaseChangeMap_comp_tensor g f f' g' sq hf E hE G hGb
    (fun n => by
      obtain rfl | hn := eq_or_ne n 0
      · exact hX ▸ hMfp
      · exact isFinitePresentation_of_isZero B S hS (hGz n hn))
    (fun n => by
      obtain rfl | hn := eq_or_ne n 0
      · exact IsFlatOver.of_iso B S hS X.2 (HomologicalComplex.singleObjXSelf _ _ _).symm hMflat
      · exact isFlatOver_of_isZero B S hS f (hGz n hn))
    (fun n => by
      obtain rfl | hn := eq_or_ne n 0
      · exact hX ▸ hMsupp
      · exact hasProperSupport_of_isZero B S hS X.2 _ f.hom _ (hGz n hn))
    (K := (spaceDerivedSingle B S hS X 0).obj M) eK (K' := (spaceDerivedSingle B S hS X' 0).obj M')
    v hM _ ?_
  refine (Adjunction.homEquiv_counit _ _ _ _).trans ?_
  have hu : (singleSpaceToToposIso X).inv.app M ≫
      (spaceToToposDerived X).map ((spaceDerivedSingle B S hS X 0).map a ≫
        (derivedModulePushforwardSingleIsoOfIsAffineHom B S hS g' hg' M' hM').inv :
        _ ⟶ (derivedModulePushforward B S hS g').obj ((spaceDerivedSingle B S hS X' 0).obj M')) ≫
      (derivedPushforwardSpaceToToposIso g').hom.app ((spaceDerivedSingle B S hS X' 0).obj M') =
      (spaceDerivedSingle B S hS X 0).map a ≫
        (derivedModulePushforwardSingleIsoOfIsAffineHom B S hS g' hg' M' hM').inv :=
    (Category.id_comp _).trans (Category.comp_id _)
  have heK : eK.inv = (DerivedCategory.singleFunctorIsoCompQ
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) 0).hom.app
        ((spaceToToposModules X).obj M) :=
    Category.id_comp _
  rw [heK]
  refine Eq.trans ?_ hv
  exact congrArg (fun x => (smallEtaleDerivedModulePullback B S hS g').map x ≫ _) hu.symm

/-- The base change map followed by `RΓ(X', -)` of the transpose of `E ⊗^𝐋 u` followed by the
projection formula map, `u : M[0] ⟶ (g'_*M')[0] ≅ Rg'_*(M'[0])`, is an isomorphism. -/
theorem isIso_affineBaseDerivedSectionsBaseChangeMap_comp_projectionFormula
    (sq : IsPullback g' f' f (representedSpaceMap B S hS g))
    (hf : IsFinitePresentation B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (M : Modules.{u, u} B S hS X.1 X.2) (hMfp : M.IsFinitePresentation)
    (hMflat : IsFlatOver B S hS X.2 f.hom M)
    (hMsupp : HasProperSupport B S hS X.2 (isAlgebraicSpace_yoneda B S hS U) f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1)
      ((SheafOfModules.toSheaf _).obj M))
    (hg' : IsAffineHom B S hS g'.hom) (M' : Modules.{u, u} B S hS X'.1 X'.2)
    (hM' : M'.IsQuasicoherentOnSite) (a : M ⟶ (modulePushforward B S hS g').obj M')
    (hM : QcohDerived B S hS X ((spaceDerivedSingle B S hS X 0).obj M))
    (h : SingleCounitCompatible g' hg' M' hM' a) :
    IsIso (affineBaseDerivedSectionsBaseChangeMap B S hS g f f' g' sq.w
        (((smallEtaleDerivedTensor B S hS X).obj E).obj ((spaceDerivedSingle B S hS X 0).obj M)) ≫
      (derivedModulePushforward B S hS f' ⋙ representedAffineDerivedSections B S hS U').map
        (((smallEtaleDerivedModuleAdjunction B S hS g').homEquiv _ _).symm
          (smallEtaleProjectionFormulaComp g' E
            ((spaceDerivedSingle B S hS X 0).map a ≫
              (derivedModulePushforwardSingleIsoOfIsAffineHom B S hS g' hg' M' hM').inv :
              _ ⟶ (derivedModulePushforward B S hS g').obj
                ((spaceDerivedSingle B S hS X' 0).obj M'))))) :=
  (congrArg (fun x => IsIso (affineBaseDerivedSectionsBaseChangeMap B S hS g f f' g' sq.w
        (((smallEtaleDerivedTensor B S hS X).obj E).obj ((spaceDerivedSingle B S hS X 0).obj M)) ≫
      (derivedModulePushforward B S hS f' ⋙ representedAffineDerivedSections B S hS U').map x))
    (homEquiv_symm_smallEtaleProjectionFormulaComp g' E
      ((spaceDerivedSingle B S hS X 0).map a ≫
        (derivedModulePushforwardSingleIsoOfIsAffineHom B S hS g' hg' M' hM').inv :
        _ ⟶ (derivedModulePushforward B S hS g').obj
          ((spaceDerivedSingle B S hS X' 0).obj M')))).mpr
    (isIso_affineBaseDerivedSectionsBaseChangeMap_comp_single g f f' g' sq hf E hE M hMfp hMflat
      hMsupp hg' M' hM' a hM h)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
/-- `RΓ(X', - ⊗^𝐋 K)` of an isomorphism is an isomorphism. -/
theorem isIso_map_map_flip_smallEtaleDerivedTensor (K : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS X')))
    {E₁ E₂ : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))}
    (c : E₁ ≅ E₂) :
    IsIso ((derivedModulePushforward B S hS f' ⋙ representedAffineDerivedSections B S hS U').map
      (((smallEtaleDerivedTensor B S hS X').flip.obj K).map c.hom)) :=
  ((derivedModulePushforward B S hS f' ⋙ representedAffineDerivedSections B S hS U').mapIso
    (((smallEtaleDerivedTensor B S hS X').flip.obj K).mapIso c)).isIso_hom

end BaseChange

end StandardModel

end AlgebraicGeometry.Space
