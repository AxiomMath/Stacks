module

public import StacksFrontier.AlgebraicGeometry.AffineOpenSectionsBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.Cohomology
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.AffineBaseSectionsNatIndexed
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineGlobalSectionsIso
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.SectionTensorFormula.AffineOpen

/-!
# Base change of the higher direct images of a quasi-coherent module by a flat module

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes with `S` and `S'` affine and `f` quasi-compact and
quasi-separated, let `F` be a quasi-coherent `𝒪_X`-module and let `G` be a quasi-coherent
`𝒪_{S'}`-module which is flat over `S`. This file proves that in every degree

`G ⊗_{𝒪_{S'}} g^*(R ⁱ f_* F)  ≅  R ⁱ f'_*((f')^* G ⊗_{𝒪_{X'}} (g')^* F)`

as `𝒪_{S'}`-modules. This is [Stacks, Tag 0GN5] over affine bases, at the level of sheaves.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleBaseChange.baseSectionsRightDerivedPushforwardIso`:
  [Stacks, Tag 01XK] at one module, with the scalars of the cohomology restricted along
  `Scheme.Hom.appLE ⊤ ⊤` — over an affine base the cohomology of a quasi-coherent module is the
  module of global sections of its higher direct image.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.tensorPullbackSectionsEquiv`: the global sections of
  `G ⊗ g^* M` over an affine base, namely `Γ(G, ⊤) ⊗_{Γ(S, ⊤)} Γ(M, ⊤)`.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.higherDirectImageBaseChangeIsoOfCover`: **the
  isomorphism, for a given hypercovering.**

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.isBaseChange_pullbackTopLinear`: over affine bases
  the global sections of `g^* M` are `Γ(S', ⊤) ⊗_{Γ(S, ⊤)} Γ(M, ⊤)`, exhibited by pulling
  sections back.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isQuasicoherent_monoidalTensorObj`: the tensor
  product of two quasi-coherent modules on a scheme is quasi-coherent, [Stacks, Tag 01CE].
* `Stacks.AlgebraicGeometry.ModuleBaseChange.nonempty_higherDirectImageBaseChangeIso`: **the
  isomorphism**, with no hypercovering supplied.

## Implementation notes

Both sides are quasi-coherent modules on the affine scheme `S'`, and a quasi-coherent module on
an affine scheme is determined up to isomorphism by its module of global sections
(`Stacks.AlgebraicGeometry.ModuleLimits.isoOfGlobalSectionsIso`). So the whole content is an
isomorphism of `Γ(S', ⊤)`-modules between the two modules of global sections, and that is
assembled from four pieces, writing `A = Γ(S, ⊤)`, `B = Γ(S', ⊤)`, `N = Γ(G, ⊤)` and
`M = R ⁱ f_* F`:

* `Γ(G ⊗ g^* M, ⊤) ≅ N ⊗_A Γ(M, ⊤)`, which is `tensorPullbackSectionsEquiv`: the section formula
  over an affine open ([Stacks, Tag 01I8]) turns the left-hand side into `N ⊗_B Γ(g^* M, ⊤)`,
  affine base change for the sections of a pullback turns `Γ(g^* M, ⊤)` into `B ⊗_A Γ(M, ⊤)`, and
  `TensorProduct.AlgebraTensorModule.cancelBaseChange` cancels that base change. This step needs
  `M` quasi-coherent, which is [Stacks, Tag 01XJ].
* `N ⊗_A Γ(M, ⊤) ≅ N ⊗_A H ⁱ(X, F)`, which is `baseSectionsRightDerivedPushforwardIso` tensored
  with `N`: this is [Stacks, Tag 01XK] over the affine base `S`.
* `N ⊗_A H ⁱ(X, F) ≅ H ⁱ(X', (f')^* G ⊗ (g')^* F)`, the module-level core
  `Stacks.AlgebraicGeometry.ModuleBaseChange.cohomologyBaseChangeIsoOfCover`, which is where
  flatness of `G` over `S` is used.
* `H ⁱ(X', (f')^* G ⊗ (g')^* F) ≅ Γ(R ⁱ f'_*((f')^* G ⊗ (g')^* F), ⊤)`, which is
  [Stacks, Tag 01XK] again, over the affine base `S'` and for the morphism `f'`; `f'` is
  quasi-compact and quasi-separated because both properties are stable under base change.

The scalar structures of the middle two isomorphisms are those of the module-level core, and are
documented there. Restriction of scalars along the action of `f` on global functions is written
`Scheme.Hom.appLE ⊤ ⊤` there and `Scheme.Hom.appTop` in [Stacks, Tag 01XK]; the two ring maps are
equal by `AlgebraicGeometry.Scheme.Hom.appLE_eq_app`, and `baseRestrictScalarsIsoAppTop` crosses
between the two spellings once.

The hypercovering is a choice, so the isomorphism is stated twice: once as a `def` taking the
hypercovering and its properties as parameters, and once as a `Nonempty` with no choice made.

No `@[stacks]` attribute is attached. What is proved is [Stacks, Tag 0GN5] for affine bases
only, a special case of the derived-category statement that the tag names.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.FormalCoproduct
open MonoidalCategory Opposite Simplicial TopologicalSpace
open Stacks.AlgebraicGeometry.HigherDirectImageQcoh
open Stacks.AlgebraicGeometry.SectionsBaseChange
open Stacks.CategoryTheory.Hypercovering
open scoped TensorProduct

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

variable {S S' X X' : Scheme.{u}}

/-! ### Restriction of scalars along the global functions of the base -/

/-- Restriction of scalars along the action of `f : X ⟶ S` on global functions, at the two
spellings `Scheme.Hom.appLE ⊤ ⊤` and `Scheme.Hom.appTop` of that ring map. -/
def baseRestrictScalarsIsoAppTop (f : X ⟶ S) :
    baseRestrictScalars f ≅ ModuleCat.restrictScalars f.appTop.hom :=
  eqToIso (congrArg (fun φ : Γ(S, ⊤) ⟶ Γ(X, ⊤) => ModuleCat.restrictScalars φ.hom)
    (Scheme.Hom.appLE_eq_app f))

/-! ### Global sections of the higher direct image -/

/-- **[Stacks, Tag 01XK] at one module, with the scalars restricted along
`Scheme.Hom.appLE ⊤ ⊤`.** For a quasi-compact and quasi-separated morphism `f : X ⟶ S` with `S`
affine and a quasi-coherent `𝒪_X`-module `F`, the cohomology `H ⁱ(X, F)` read as a
`Γ(S, ⊤)`-module is the module of global sections of `R ⁱ f_* F`. -/
def baseSectionsRightDerivedPushforwardIso (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [IsAffine S] (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    (baseRestrictScalars f).obj (((moduleGlobalSections X).rightDerived i).obj F) ≅
      (moduleGlobalSections S).obj (((Scheme.Modules.pushforward f).rightDerived i).obj F) :=
  (baseRestrictScalarsIsoAppTop f).app _ ≪≫ sectionsRightDerivedPushforwardIso f F i

/-! ### Global sections of the pullback of a quasi-coherent module -/

/-- Pulling a global section back, as a `Γ(S, ⊤)`-linear map into the global sections of the
pullback. -/
def pullbackTopLinear (g : S' ⟶ S) (M : S.Modules) :
    letI := baseModule g ((Scheme.Modules.pullback g).obj M) ⊤
    Γ(M, ⊤) →ₗ[Γ(S, ⊤)] Γ((Scheme.Modules.pullback g).obj M, ⊤) :=
  letI := baseModule g ((Scheme.Modules.pullback g).obj M) ⊤
  { toFun := pullbackSectionsHom g M ⊤ ⊤ (le_preimage_top g ⊤)
    map_add' := (pullbackSectionsHom g M ⊤ ⊤ (le_preimage_top g ⊤)).map_add
    map_smul' := fun r a => by
      change pullbackSectionsHom g M ⊤ ⊤ (le_preimage_top g ⊤) (r • a) =
        (g.appLE ⊤ ⊤ (le_preimage_top g ⊤)).hom r •
          pullbackSectionsHom g M ⊤ ⊤ (le_preimage_top g ⊤) a
      rw [pullbackSectionsHom_top, pullbackSectionsHom_top,
        show g.appLE ⊤ ⊤ (le_preimage_top g ⊤) = g.appTop from Scheme.Hom.appLE_eq_app g]
      exact pullbackUnitSections_smul g M ⊤ r a }

/-- **The base scalar structures on the global sections of a pullback form a tower.** A scalar of
`Γ(S, ⊤)` acts through its image in `Γ(S', ⊤)`. -/
theorem pullbackTopTower (g : S' ⟶ S) (M : S.Modules) :
    letI := baseAlgebra g
    letI := baseModule g ((Scheme.Modules.pullback g).obj M) ⊤
    IsScalarTower Γ(S, ⊤) Γ(S', ⊤) Γ((Scheme.Modules.pullback g).obj M, ⊤) :=
  let := baseAlgebra g
  let := baseModule g ((Scheme.Modules.pullback g).obj M) ⊤
  Stacks.FlatSectionsDescent.isScalarTower_of_smul_eq (RingHom.id _) (fun _ _ => rfl)
    (g.appLE ⊤ ⊤ (le_preimage_top g ⊤)).hom (fun _ _ => rfl) (fun _ => rfl)

/-- **Over affine bases the global sections of `g^* M` are a base change.** For `g : S' ⟶ S` with
`S` and `S'` affine and `M` a quasi-coherent `𝒪_S`-module, pulling global sections back exhibits
`Γ(g^* M, ⊤)` as `Γ(S', ⊤) ⊗_{Γ(S, ⊤)} Γ(M, ⊤)`. This is affine base change,
[Stacks, Tag 02KG], over the pair of affine opens `⊤ ⊆ S` and `⊤ ⊆ S'`. -/
theorem isBaseChange_pullbackTopLinear [IsAffine S] [IsAffine S'] (g : S' ⟶ S) (M : S.Modules)
    [M.IsQuasicoherent] :
    letI := baseAlgebra g
    letI := baseModule g ((Scheme.Modules.pullback g).obj M) ⊤
    letI := pullbackTopTower g M
    IsBaseChange Γ(S', ⊤) (pullbackTopLinear g M) := by
  let := baseAlgebra g
  let := baseModule g ((Scheme.Modules.pullback g).obj M) ⊤
  let := pullbackTopTower g M
  refine AlgebraicGeometry.ModuleCat.isBaseChange_of_extendScalarsIso
    (g.appLE ⊤ ⊤ (le_preimage_top g ⊤)).hom rfl
    (affinePullbackSectionsBaseChangeIso g M (isAffineOpen_top S) (isAffineOpen_top S')
      (le_preimage_top g ⊤)) (pullbackTopLinear g M) (fun m => ?_)
  rw [affinePullbackSectionsBaseChangeIso_one_tmul]
  rfl

/-! ### Global sections of the left-hand side -/

/-- **The global sections of `G ⊗ g^* M` over an affine base.** For `g : S' ⟶ S` with `S` and `S'`
affine, `M` a quasi-coherent `𝒪_S`-module and `G` a quasi-coherent `𝒪_{S'}`-module,

`Γ(G, ⊤) ⊗_{Γ(S, ⊤)} Γ(M, ⊤) ≅ Γ(G ⊗ g^* M, ⊤)`

as `Γ(S', ⊤)`-modules. -/
def tensorPullbackSectionsEquiv [IsAffine S] [IsAffine S'] (g : S' ⟶ S) (M : S.Modules)
    [M.IsQuasicoherent] (G : S'.Modules) [G.IsQuasicoherent] :
    letI := baseAlgebra g
    letI := baseModule g G ⊤
    letI := coeffTower g G
    Γ(G, ⊤) ⊗[Γ(S, ⊤)] Γ(M, ⊤) ≃ₗ[Γ(S', ⊤)]
      Γ(G ⊗ (Scheme.Modules.pullback g).obj M, ⊤) :=
  letI := baseAlgebra g
  letI := baseModule g G ⊤
  letI := coeffTower g G
  letI := baseModule g ((Scheme.Modules.pullback g).obj M) ⊤
  letI := pullbackTopTower g M
  (TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(S, ⊤) Γ(S', ⊤) Γ(S', ⊤)
        Γ(G, ⊤) Γ(M, ⊤)).symm ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl Γ(S', ⊤) Γ(G, ⊤))
      (isBaseChange_pullbackTopLinear g M).equiv ≪≫ₗ
    Stacks.SectionTensorFormula.tensorSectionEquiv G ((Scheme.Modules.pullback g).obj M)
      (isAffineOpen_top S')

/-! ### The isomorphism -/

variable {g : S' ⟶ S} {f : X ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}

/-- The tensor product of two quasi-coherent modules on a scheme is quasi-coherent,
[Stacks, Tag 01CE], for the monoidal structure of
`Stacks.SheafInternalHom.schemeMonoidalCategory`. -/
theorem isQuasicoherent_monoidalTensorObj (M N : S.Modules) [M.IsQuasicoherent]
    [N.IsQuasicoherent] : (M ⊗ N).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    (Stacks.SectionTensorFormula.tensorSheafIsoTensorObj S.presheaf
      (Stacks.SectionTensorFormula.schemeSheafCondition S) _ _)
    (Scheme.Modules.isQuasicoherent_tensorObj _ _ inferInstance inferInstance)

/-- **Base change of the higher direct images of a quasi-coherent module by a flat module, from a
hypercovering.** For a cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

with `S` and `S'` affine and `f` quasi-compact and quasi-separated, a quasi-coherent
`𝒪_X`-module `F`, a quasi-coherent `𝒪_{S'}`-module `G` whose global sections are flat over
`Γ(S, ⊤)`, and a hypercovering `K` of `X` which is degreewise finite and all of whose members are
affine opens,

`G ⊗ g^*(R ⁱ f_* F) ≅ R ⁱ f'_*((f')^* G ⊗ (g')^* F)`

as `𝒪_{S'}`-modules, in every degree `i`. -/
def higherDirectImageBaseChangeIsoOfCover [IsAffine S] [IsAffine S'] (H : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] (G : S'.Modules) [G.IsQuasicoherent]
    (hflat : letI := baseModule g G ⊤; Module.Flat Γ(S, ⊤) Γ(G, ⊤))
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : X.Opens))))
    (hK : IsHypercovering (Opens.pretopology ↥X) K)
    (hfin : ∀ n : ℕ, Finite (K.obj (op ⦋n⦌)).I)
    (haff : ∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I), IsAffineOpen ((K.obj (op ⦋n⦌)).obj i).left)
    (i : ℕ) :
    G ⊗ (Scheme.Modules.pullback g).obj
          (((Scheme.Modules.pushforward f).rightDerived i).obj F) ≅
      ((Scheme.Modules.pushforward f').rightDerived i).obj (tensorPullback g' f' F G) :=
  letI := baseAlgebra g
  letI := baseModule g G ⊤
  letI := coeffTower g G
  haveI : QuasiCompact f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback H ‹QuasiCompact f›
  haveI : QuasiSeparated f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback H ‹QuasiSeparated f›
  haveI := isQuasicoherent_monoidalTensorObj G
    ((Scheme.Modules.pullback g).obj (((Scheme.Modules.pushforward f).rightDerived i).obj F))
  Stacks.AlgebraicGeometry.ModuleLimits.isoOfGlobalSectionsIso
    ((tensorPullbackSectionsEquiv g
            (((Scheme.Modules.pushforward f).rightDerived i).obj F) G).symm.toModuleIso ≪≫
      (Stacks.TensorBimodule.functor Γ(S, ⊤) Γ(S', ⊤) Γ(G, ⊤)).mapIso
        (baseSectionsRightDerivedPushforwardIso f F i).symm ≪≫
      cohomologyBaseChangeIsoOfCover H F G hflat K hK hfin haff i ≪≫
      baseSectionsRightDerivedPushforwardIso f' (tensorPullback g' f' F G) i)

/-- **Base change of the higher direct images of a quasi-coherent module by a flat module.** For
a cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

with `S` and `S'` affine and `f` quasi-compact and quasi-separated, a quasi-coherent
`𝒪_X`-module `F` and a quasi-coherent `𝒪_{S'}`-module `G` flat over `S`,

`G ⊗ g^*(R ⁱ f_* F) ≅ R ⁱ f'_*((f')^* G ⊗ (g')^* F)`

as `𝒪_{S'}`-modules, in every degree `i`. This is [Stacks, Tag 0GN5] over affine bases.

The hypercovering is a choice and no isomorphism is canonical, so the statement is a `Nonempty`;
`Stacks.AlgebraicGeometry.ModuleBaseChange.higherDirectImageBaseChangeIsoOfCover` is the
isomorphism attached to a hypercovering. -/
theorem nonempty_higherDirectImageBaseChangeIso [IsAffine S] [IsAffine S']
    (H : IsPullback g' f' f g) [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] (G : S'.Modules) [G.IsQuasicoherent]
    (hG : IsFlatOver g.toLRSHom.toShHom G) (i : ℕ) :
    Nonempty
      (G ⊗ (Scheme.Modules.pullback g).obj
            (((Scheme.Modules.pushforward f).rightDerived i).obj F) ≅
        ((Scheme.Modules.pushforward f').rightDerived i).obj (tensorPullback g' f' F G)) := by
  have : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace ↥X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨K, hK, hKprop⟩ :=
    Stacks.AlgebraicGeometry.UniversalPushforward.exists_finite_affine_hypercovering X
  exact ⟨higherDirectImageBaseChangeIsoOfCover H F G (flat_sections_of_isFlatOver g G hG) K hK
    (fun n ↦ (hKprop n).1) (fun n j ↦ (hKprop n).2 j) i⟩

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
