module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTorIndependentBaseChange
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareMates

/-!
# The base change map of global derived Homs over an affine base

Let `g : U' ⟶ U` be a morphism of the big fppf site over `S` whose source and target have affine
underlying schemes, `R = Γ(U, 𝒪)`, `R' = Γ(U', 𝒪)`, and consider a commutative square of
algebraic spaces

```
X' --g'--> X
|f'        |f
U' --g---> U
```

For `H ∈ D(𝒪_X)`, `RΓ(X, H)` read in `D(R)` is `RΓ(U, Rf_*H)`: its left adjoint is
`Lf^* ∘ Φ_R`, with `Φ_R` the derived associated-module functor. The square of left adjoints
`D(R) → D(𝒪_X) → D(𝒪_{X'})` and `D(R) → D(R') → D(𝒪_{X'})` commutes up to the affine base change
isomorphism `Lg^* Φ_R ≅ Φ_{R'}(- ⊗^L_R R')` and the comparison of iterated derived pullbacks, and
its mate is the base change map

`RΓ(X, H) ⊗^L_R R' ⟶ RΓ(X', L(g')^*H)`

in `D(R')`, the adjoint of the functoriality map `RΓ(X, H) ⟶ RΓ(X', L(g')^*H)` of `D(R)`. Followed
by `RΓ(X', -)` of the map `L(g')^*R𝓗om(M, K) ⟶ R𝓗om(L(g')^*M, L(g')^*K)` of Stacks 08JF it is
the canonical map of Stacks 0E4S,

`RHom_X(M, K) ⊗^L_R R' ⟶ RHom_{X'}(L(g')^*M, L(g')^*K)`.

## Main definitions

* `AlgebraicGeometry.Space.affineBaseDerivedSectionsAdjunction`: `Lf^* ∘ Φ_R ⊣ RΓ(U, Rf_* -)`.
* `AlgebraicGeometry.Space.affineBaseDerivedSectionsBaseChangeMap`: the base change map
  `RΓ(X, H) ⊗^L_R R' ⟶ RΓ(X', L(g')^*H)`.
* `AlgebraicGeometry.Space.globalDerivedHomBaseChangeMap`: the map of Stacks 0E4S.

## References

* [Stacks Project, Tag 0E4S](https://stacks.math.columbia.edu/tag/0E4S)
* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U' U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]

/-- **`RΓ(X, -)` over an affine base, with its left adjoint**: for `f : X ⟶ U` with `U` affine
representable, `Lf^* ∘ Φ_R ⊣ RΓ(U, Rf_* -)`, the composite of the adjunction `Φ_R ⊣ RΓ(U, -)` and
Stacks 07A6. -/
def affineBaseDerivedSectionsAdjunction {X : AlgebraicSpaces B S hS}
    (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) :
    representedAffineDerivedAssociated B S hS U ⋙ smallEtaleDerivedModulePullback B S hS f ⊣
      derivedModulePushforward B S hS f ⋙ representedAffineDerivedSections B S hS U :=
  (representedAffineDerivedAdjunction B S hS U).comp (smallEtaleDerivedModuleAdjunction B S hS f)

variable {X X' : AlgebraicSpaces B S hS} (g : U' ⟶ U)
  (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
  (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ representedSpaceMap B S hS g)

/-- The two composites of left adjoints `D(R) ⥤ D(𝒪_{X'})` around the square agree:
`L(f')^* Φ_{R'}(- ⊗^L_R R') ≅ L(f')^* Lg^* Φ_R ≅ L(g')^* Lf^* Φ_R`, by the affine base change
isomorphism of `Φ` and the comparison of the two iterated derived pullbacks. -/
def affineBaseDerivedSectionsSquareIso :
    (representedAffineDerivedExtension B S hS g).functor ⋙
        (representedAffineDerivedAssociated B S hS U' ⋙
          smallEtaleDerivedModulePullback B S hS f') ≅
      (representedAffineDerivedAssociated B S hS U ⋙ smallEtaleDerivedModulePullback B S hS f) ⋙
        smallEtaleDerivedModulePullback B S hS g' :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (representedAffineDerivedBaseChangeIso B S hS g).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (smallEtaleDerivedModulePullbackCompIso B S hS f'
        (representedSpaceMap B S hS g) ≪≫
      (smallEtaleDerivedModulePullbackSquareIso B S hS f (representedSpaceMap B S hS g) f' g'
        w).symm) ≪≫
    (Functor.associator _ _ _).symm

/-- **The base change map of `RΓ` over an affine base**,
`RΓ(X, H) ⊗^L_R R' ⟶ RΓ(X', L(g')^*H)` in `D(R')`, with `RΓ(X, H) = RΓ(U, Rf_*H)`: the mate of
`affineBaseDerivedSectionsSquareIso` under `affineBaseDerivedSectionsAdjunction` for `f` and `f'`,
that is the adjoint of the functoriality map `RΓ(X, H) ⟶ RΓ(X', L(g')^*H)` of `D(R)`. -/
def affineBaseDerivedSectionsBaseChangeMap
    (H : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (representedAffineDerivedExtension B S hS g).functor.obj
        ((representedAffineDerivedSections B S hS U).obj
          ((derivedModulePushforward B S hS f).obj H)) ⟶
      (representedAffineDerivedSections B S hS U').obj
        ((derivedModulePushforward B S hS f').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj H)) :=
  Stacks.CategoryTheory.BaseChange.map (affineBaseDerivedSectionsAdjunction B S hS f)
    (affineBaseDerivedSectionsAdjunction B S hS f')
    (affineBaseDerivedSectionsSquareIso B S hS g f f' g' w) (Iso.refl _) H

/-- **The base change map of `RΓ` between affine representables**,
`RΓ(U, F) ⊗^L_R R' ⟶ RΓ(U', Lg^*F)` in `D(R')`: the mate of the affine base change isomorphism
`Lg^* Φ_R ≅ Φ_{R'}(- ⊗^L_R R')` under `Φ_R ⊣ RΓ(U, -)` and `Φ_{R'} ⊣ RΓ(U', -)`. -/
def representedAffineDerivedSectionsBaseChangeMap
    (F : DerivedCategory
      (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))) :
    (representedAffineDerivedExtension B S hS g).functor.obj
        ((representedAffineDerivedSections B S hS U).obj F) ⟶
      (representedAffineDerivedSections B S hS U').obj
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj F) :=
  Stacks.CategoryTheory.BaseChange.map (representedAffineDerivedAdjunction B S hS U)
    (representedAffineDerivedAdjunction B S hS U')
    (representedAffineDerivedBaseChangeIso B S hS g).symm (Iso.refl _) F

/-- **The affine base change map of `RΓ` is invertible on `D_QCoh`**: for `F ∈ D_QCoh(𝒪_U)`,
`RΓ(U, F) ⊗^L_R R' ⟶ RΓ(U', Lg^*F)` is an isomorphism. -/
theorem isIso_representedAffineDerivedSectionsBaseChangeMap
    (F : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)))
    (hF : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ F) :
    IsIso (representedAffineDerivedSectionsBaseChangeMap B S hS g F) := by
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS U F hF
  exact Stacks.CategoryTheory.BaseChange.isIso_map_of_isIso_counit_app _ _ _ _ F

/-- **The base change map of `RΓ` over an affine base factors through Stacks 07A7**: it is the
affine base change map of `RΓ` at `Rf_*H` followed by `RΓ(U', -)` of the base change map
`Lg^*Rf_*H ⟶ Rf'_*L(g')^*H`. -/
theorem affineBaseDerivedSectionsBaseChangeMap_eq
    (H : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    affineBaseDerivedSectionsBaseChangeMap B S hS g f f' g' w H =
      representedAffineDerivedSectionsBaseChangeMap B S hS g
          ((derivedModulePushforward B S hS f).obj H) ≫
        (representedAffineDerivedSections B S hS U').map
          (smallEtaleDerivedModuleBaseChangeMap B S hS f (representedSpaceMap B S hS g) f' g' w
            H) :=
  Stacks.CategoryTheory.BaseChange.map_comp_adjunction (representedAffineDerivedAdjunction B S hS U)
    (smallEtaleDerivedModuleAdjunction B S hS f) (representedAffineDerivedAdjunction B S hS U')
    (smallEtaleDerivedModuleAdjunction B S hS f')
    (representedAffineDerivedBaseChangeIso B S hS g).symm
    (smallEtaleDerivedModulePullbackCompIso B S hS f' (representedSpaceMap B S hS g))
    (smallEtaleDerivedModulePullbackSquareIso B S hS f (representedSpaceMap B S hS g) f' g' w) H

/-- **The base change map of `RΓ` over an affine base is invertible on `D_QCoh`** (Stacks 08IR
and the affine case): for a cartesian square with `f` quasi-compact and quasi-separated and `X`,
`U'` Tor independent over `U`, the map `RΓ(X, H) ⊗^L_R R' ⟶ RΓ(X', L(g')^*H)` is an isomorphism for
every `H ∈ D_QCoh(𝒪_X)`. -/
theorem isIso_affineBaseDerivedSectionsBaseChangeMap
    (sq : IsPullback g' f' f (representedSpaceMap B S hS g))
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hTor : TorIndependent X.2 (isAlgebraicSpace_yoneda B S hS U')
      (isAlgebraicSpace_yoneda B S hS U) f.hom (representedSpaceMap B S hS g).hom)
    (H : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hH : QcohDerived B S hS X H) :
    IsIso (affineBaseDerivedSectionsBaseChangeMap B S hS g f f' g' sq.w H) := by
  rw [affineBaseDerivedSectionsBaseChangeMap_eq]
  have h₁ := isIso_representedAffineDerivedSectionsBaseChangeMap B S hS g _
    (qcohDerived_derivedModulePushforward_obj B S hS f hfqc hfqs H hH)
  have h₂ := isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent B S hS f
    (representedSpaceMap B S hS g) f' g' sq hfqc hfqs hTor H hH
  exact IsIso.comp_isIso' h₁ (@Functor.map_isIso _ _ _ _ _ _ _ _ h₂)

/-- **The canonical map of Stacks 0E4S**,
`RHom_X(M, K) ⊗^L_R R' ⟶ RHom_{X'}(L(g')^*M, L(g')^*K)` in `D(R')`, where
`RHom_X(M, K) = RΓ(X, R𝓗om(M, K))` is read in `D(R)`: the base change map of `RΓ` at
`R𝓗om(M, K)` followed by `RΓ(X', -)` of the map of Stacks 08JF. -/
def globalDerivedHomBaseChangeMap
    (M K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (representedAffineDerivedExtension B S hS g).functor.obj
        ((representedAffineDerivedSections B S hS U).obj
          ((derivedModulePushforward B S hS f).obj
            (((smallEtaleDerivedSheafHom B S hS X).obj (op M)).obj K))) ⟶
      (representedAffineDerivedSections B S hS U').obj
        ((derivedModulePushforward B S hS f').obj
          (((smallEtaleDerivedSheafHom B S hS X').obj
            (op ((smallEtaleDerivedModulePullback B S hS g').obj M))).obj
            ((smallEtaleDerivedModulePullback B S hS g').obj K))) :=
  affineBaseDerivedSectionsBaseChangeMap B S hS g f f' g' w _ ≫
    (representedAffineDerivedSections B S hS U').map ((derivedModulePushforward B S hS f').map
      (smallEtaleDerivedPullbackSheafHomMap g' M K))

/-- **Stacks 0E4S reduced to `RΓ(X', -)` of the map of Stacks 08JF.** For a cartesian square with
`f` quasi-compact and quasi-separated and `X`, `U'` Tor independent over `U`, and `M`, `K` with
`R𝓗om(M, K) ∈ D_QCoh(𝒪_X)`, the canonical map of Stacks 0E4S is an isomorphism as soon as
`RΓ(X', -)` of `L(g')^*R𝓗om(M, K) ⟶ R𝓗om(L(g')^*M, L(g')^*K)` is. -/
theorem isIso_globalDerivedHomBaseChangeMap_of_isIso
    (sq : IsPullback g' f' f (representedSpaceMap B S hS g))
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hTor : TorIndependent X.2 (isAlgebraicSpace_yoneda B S hS U')
      (isAlgebraicSpace_yoneda B S hS U) f.hom (representedSpaceMap B S hS g).hom)
    (M K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hH : QcohDerived B S hS X (((smallEtaleDerivedSheafHom B S hS X).obj (op M)).obj K))
    (hφ : IsIso ((representedAffineDerivedSections B S hS U').map
      ((derivedModulePushforward B S hS f').map (smallEtaleDerivedPullbackSheafHomMap g' M K)))) :
    IsIso (globalDerivedHomBaseChangeMap B S hS g f f' g' sq.w M K) := by
  have := isIso_affineBaseDerivedSectionsBaseChangeMap B S hS g f f' g' sq hfqc hfqs hTor _ hH
  exact IsIso.comp_isIso' inferInstance hφ

/-! ### The compatibility of Stacks 0E4T -/

/-- **`RΓ(X, Rg'_* -) = RΓ(X', -)` over `R`**: the isomorphism
`RΓ(U, Rf_* Rg'_* N) ≅ RΓ(U', Rf'_* N)` of `D(R)`, the conjugate of
`affineBaseDerivedSectionsSquareIso` along the composite adjunctions. -/
def affineBaseDerivedSectionsPushforwardIso :
    derivedPushforward (X := smallEtaleRingedTopos B S hS X')
          (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS g') ⋙
        (derivedModulePushforward B S hS f ⋙ representedAffineDerivedSections B S hS U) ≅
      (derivedModulePushforward B S hS f' ⋙ representedAffineDerivedSections B S hS U') ⋙
        (ModuleCat.restrictScalars
          (representedAffineCommRingCatHom B S hS g).hom).mapDerivedCategory :=
  conjugateIsoEquiv ((affineBaseDerivedSectionsAdjunction B S hS f).comp
      (smallEtaleDerivedModuleAdjunction B S hS g'))
    ((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom B S hS g).hom).comp
        (affineBaseDerivedSectionsAdjunction B S hS f'))
    (affineBaseDerivedSectionsSquareIso B S hS g f f' g' w)

/-- For `M ∈ D(𝒪_X)` and `L ∈ D(𝒪_{X'})`, the canonical map of Stacks 0E4S at `(M, Rg'_*L)`
followed by `RΓ(X', -)` of `R𝓗om(L(g')^*M, -)` of the counit `L(g')^*Rg'_*L ⟶ L` is the
multiplication map `K' ⊗^L_R R' ⟶ K'`, the counit of `- ⊗^L_R R' ⊣` restriction of scalars, at
`K' = RHom_{X'}(L(g')^*M, L)`, after the identification
`RHom_X(M, Rg'_*L) = RHom_{X'}(L(g')^*M, L)`. -/
@[stacks 0E4T]
theorem globalDerivedHomBaseChangeMap_comp_map_counit
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))) :
    globalDerivedHomBaseChangeMap B S hS g f f' g' w M
          ((derivedPushforward (X := smallEtaleRingedTopos B S hS X')
            (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS g')).obj L) ≫
        (representedAffineDerivedSections B S hS U').map ((derivedModulePushforward B S hS f').map
          (((smallEtaleDerivedSheafHom B S hS X').obj
            (op ((smallEtaleDerivedModulePullback B S hS g').obj M))).map
            ((smallEtaleDerivedModuleAdjunction B S hS g').counit.app L))) =
      (representedAffineDerivedExtension B S hS g).functor.map
          ((derivedModulePushforward B S hS f ⋙ representedAffineDerivedSections B S hS U).map
              ((derivedModulePushforwardSheafHomIso g' M).inv.app L) ≫
            (affineBaseDerivedSectionsPushforwardIso B S hS g f f' g' w).hom.app _) ≫
        (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom B S hS g).hom).counit.app _ := by
  exact Stacks.CategoryTheory.BaseChange.map_comp_map_homComparison_counit_of_eq
    (adjf := affineBaseDerivedSectionsAdjunction B S hS f)
    (ag := RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom B S hS g).hom)
    (ag' := smallEtaleDerivedModuleAdjunction B S hS g')
    (a := smallEtaleDerivedTensorSheafHomAdjunction B S hS X M)
    (a' := smallEtaleDerivedTensorSheafHomAdjunction B S hS X'
      ((smallEtaleDerivedModulePullback B S hS g').obj M))
    (μ := smallEtaleDerivedPullbackTensorRightIso g' M)
    (adj₂ := affineBaseDerivedSectionsAdjunction B S hS f')
    (e := affineBaseDerivedSectionsSquareIso B S hS g f f' g' w) (L := L)
    (φ := smallEtaleDerivedPullbackSheafHomMap g' M
      ((derivedPushforward (X := smallEtaleRingedTopos B S hS X')
          (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS g')).obj L))
    (by simp only [smallEtaleDerivedPullbackSheafHomMap_eq_homEquiv_counit,
      smallEtaleDerivedPullbackTensorRightIso,
      NatIso.ofComponents_inv_app, Iso.app_inv, Functor.id_obj])
    (derivedModulePushforwardSheafHomIso g' M) rfl
    (affineBaseDerivedSectionsPushforwardIso B S hS g f f' g' w) rfl

/-- **Stacks 0E4S reduced to `R(g')_*` of the map of Stacks 08JF.** Under the hypotheses of
`isIso_globalDerivedHomBaseChangeMap_of_isIso`, the canonical map of Stacks 0E4S is an
isomorphism as soon as `R(g')_*` of `L(g')^*R𝓗om(M, K) ⟶ R𝓗om(L(g')^*M, L(g')^*K)` is. -/
theorem isIso_globalDerivedHomBaseChangeMap_of_isIso_derivedPushforward
    (sq : IsPullback g' f' f (representedSpaceMap B S hS g))
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hTor : TorIndependent X.2 (isAlgebraicSpace_yoneda B S hS U')
      (isAlgebraicSpace_yoneda B S hS U) f.hom (representedSpaceMap B S hS g).hom)
    (M K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hH : QcohDerived B S hS X (((smallEtaleDerivedSheafHom B S hS X).obj (op M)).obj K))
    (hφ : IsIso ((derivedPushforward (X := smallEtaleRingedTopos B S hS X')
          (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS g')).map
      (smallEtaleDerivedPullbackSheafHomMap g' M K))) :
    IsIso (globalDerivedHomBaseChangeMap B S hS g f f' g' sq.w M K) := by
  refine isIso_globalDerivedHomBaseChangeMap_of_isIso B S hS g f f' g' sq hfqc hfqs hTor M K hH ?_
  have hn := (affineBaseDerivedSectionsPushforwardIso B S hS g f f' g' sq.w).hom.naturality
    (smallEtaleDerivedPullbackSheafHomMap g' M K)
  have := hφ
  have h₀ : IsIso (((derivedPushforward (X := smallEtaleRingedTopos B S hS X')
        (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS g')) ⋙
        (derivedModulePushforward B S hS f ⋙ representedAffineDerivedSections B S hS U)).map
          (smallEtaleDerivedPullbackSheafHomMap g' M K) ≫
      (affineBaseDerivedSectionsPushforwardIso B S hS g f f' g' sq.w).hom.app _) := by
    have : IsIso (((derivedPushforward (X := smallEtaleRingedTopos B S hS X')
        (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS g')) ⋙
        (derivedModulePushforward B S hS f ⋙ representedAffineDerivedSections B S hS U)).map
          (smallEtaleDerivedPullbackSheafHomMap g' M K)) := by
      rw [Functor.comp_map]
      infer_instance
    infer_instance
  rw [hn] at h₀
  have h₁ : IsIso ((ModuleCat.restrictScalars
      (representedAffineCommRingCatHom B S hS g).hom).mapDerivedCategory.map
      ((representedAffineDerivedSections B S hS U').map ((derivedModulePushforward B S hS f').map
        (smallEtaleDerivedPullbackSheafHomMap g' M K)))) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _
      ((affineBaseDerivedSectionsPushforwardIso B S hS g f f' g' sq.w).hom.app _)
      (((derivedModulePushforward B S hS f' ⋙ representedAffineDerivedSections B S hS U') ⋙
        (ModuleCat.restrictScalars
          (representedAffineCommRingCatHom B S hS g).hom).mapDerivedCategory).map
          (smallEtaleDerivedPullbackSheafHomMap g' M K)) _ h₀
  rw [DerivedCategory.isIso_iff]
  intro n
  have := ((ModuleCat.restrictScalars
    (representedAffineCommRingCatHom B S hS g).hom).isIso_mapDerivedCategory_map_iff _).1 h₁ n
  exact isIso_of_reflects_iso _
    (ModuleCat.restrictScalars (representedAffineCommRingCatHom B S hS g).hom)

end AlgebraicGeometry.Space

end
