module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffinePositiveDegree
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.Complex
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.UniversalPushforward

/-!
# Base change of the cohomology of a quasi-coherent module by a flat module

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
`𝒪_{S'}`-module which is flat over `S`. Write `A = Γ(S, ⊤)`, `B = Γ(S', ⊤)` and `N = Γ(G, ⊤)`.
This file proves that in every degree

`N ⊗_A H ⁱ(X, F)  ≅  H ⁱ(X', (f')^* G ⊗_{𝒪_{X'}} (g')^* F)`

as `B`-modules. This is the algebraic heart of [Stacks, Tag 0GN5] over affine bases, at the level
of modules; it is steps 5–8 of the proof there.

## Scalar structures

`H ⁱ(X, F)` is the value of the `i`-th right derived functor of module-valued global sections, a
module over `Γ(X, ⊤)`; it is read as an `A`-module by restriction of scalars along
`f.appLE ⊤ ⊤`, which is `Stacks.AlgebraicGeometry.SectionsBaseChange.baseRestrictScalars f`, and
then tensored with `N` over `A`. The `B`-module structure of the result is the one on `N`, which
is its native `Γ(S', ⊤)`-module structure; `N` is an `A`-module by restriction along
`g.appLE ⊤ ⊤`, the two actions forming a tower
(`Stacks.AlgebraicGeometry.ModuleBaseChange.coeffTower`). On the other side,
`H ⁱ(X', (f')^* G ⊗ (g')^* F)` is a `Γ(X', ⊤)`-module, read as a `B`-module by restriction along
`f'.appLE ⊤ ⊤`. So the statement is an isomorphism in `ModuleCat B` between

`(baseRestrictScalars f ⋙ Stacks.TensorBimodule.functor A B N).obj (H ⁱ(X, F))` and
`(baseRestrictScalars f').obj (H ⁱ(X', (f')^* G ⊗ (g')^* F))`.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleBaseChange.baseTensorHomologyIso`: tensoring with `N` over `A`
  commutes with the homology of a complex, `N` being flat over `A`.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.cohomologyBaseChangeIsoOfCover`: **the isomorphism,
  for a given hypercovering.**

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.flat_sections_of_isFlatOver`: the global sections of
  a quasi-coherent module flat over an affine base are a flat module over the global functions of
  the base.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.nonempty_cohomologyBaseChangeIso`: **the
  isomorphism**, with no hypercovering supplied.

## Implementation notes

The hypercovering is a choice, so the isomorphism is stated twice: once as a `def` taking the
hypercovering and its properties as parameters, and once as a `Nonempty` with no choice made.
This is the shape of
`AlgebraicGeometry.cohomologyBaseChangeIsoOfCover` and
`AlgebraicGeometry.nonempty_cohomologyBaseChangeIso`, which do the same for the Čech route under
the stronger hypothesis of an affine diagonal.

The isomorphism is a composite of five: the cohomology of `F` is the cohomology of the complex of
sections of the hypercovering
(`Stacks.Cohomology.HypercoveringModules.sectionsModuleComplexHomologyIso`, which is where
quasi-coherence of the coefficients and affineness of the members are used); tensoring with `N`
commutes with homology, because `N` is flat over `A` — the only place flatness enters; the
complexes are compared by
`Stacks.AlgebraicGeometry.ModuleBaseChange.sectionsComplexBaseChangeIso`; restriction of scalars
commutes with homology, being exact; and the cohomology of the complex of sections upstairs is
the cohomology of `(f')^* G ⊗ (g')^* F`.

The hypotheses of the `Nonempty` form are exactly what
`Stacks.AlgebraicGeometry.UniversalPushforward.exists_finite_affine_hypercovering` needs: `f`
quasi-compact and quasi-separated over an affine base makes the space of `X` compact and
quasi-separated.

Nothing here identifies the isomorphism with the canonical base-change map of the derived
category; what is pinned down is the degreewise comparison, on pure tensors, by
`Stacks.AlgebraicGeometry.ModuleBaseChange.comparisonMap_tmul`.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
* [Stacks Project, Tag 01U4](https://stacks.math.columbia.edu/tag/01U4)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.FormalCoproduct
open ComplexShape MonoidalCategory Opposite Simplicial TopologicalSpace
open Stacks.AlgebraicGeometry.SectionsBaseChange
open Stacks.CategoryTheory.Hypercovering
open Stacks.Cohomology.HypercoveringModules
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ModuleCat.hasLimitsOfSize
attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

variable {S S' X X' : Scheme.{u}}

/-! ### Flatness of the coefficient module -/

/-- **The global sections of a quasi-coherent module flat over an affine base are flat over the
global functions of the base.**  This is the affine-opens characterisation of flatness,
[Stacks, Tag 01U4], at the pair of affine opens `⊤ ⊆ S'` and `⊤ ⊆ S`. -/
theorem flat_sections_of_isFlatOver [IsAffine S] [IsAffine S'] (g : S' ⟶ S) (G : S'.Modules)
    [G.IsQuasicoherent] (hG : IsFlatOver g.toLRSHom.toShHom G) :
    letI := baseModule g G ⊤
    Module.Flat Γ(S, ⊤) Γ(G, ⊤) := by
  have h := ((AlgebraicGeometry.isFlatOver_tfae g G).out 1 2).mp hG
  exact h ⊤ (isAffineOpen_top S') ⊤ (isAffineOpen_top S) (le_preimage_top g ⊤)

/-! ### Tensoring commutes with homology -/

variable {g : S' ⟶ S} {f : X ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}

/-- **Tensoring with `N = Γ(G, ⊤)` over `A = Γ(S, ⊤)` commutes with homology** when `N` is flat
over `A`: restriction of scalars is exact unconditionally and `N ⊗_A -` is exact under
flatness. -/
def baseTensorHomologyIso (f : X ⟶ S) (g : S' ⟶ S) (G : S'.Modules)
    (hflat : letI := baseModule g G ⊤; Module.Flat Γ(S, ⊤) Γ(G, ⊤))
    (C : CochainComplex (ModuleCat.{u} Γ(X, ⊤)) ℕ) (n : ℕ) :
    letI := baseAlgebra g
    letI := baseModule g G ⊤
    letI := coeffTower g G
    ((((baseRestrictScalars f ⋙
          Stacks.TensorBimodule.functor Γ(S, ⊤) Γ(S', ⊤) Γ(G, ⊤)).mapHomologicalComplex
            (up ℕ)).obj C).homology n) ≅
      (baseRestrictScalars f ⋙
        Stacks.TensorBimodule.functor Γ(S, ⊤) Γ(S', ⊤) Γ(G, ⊤)).obj (C.homology n) :=
  letI := baseAlgebra g
  letI := baseModule g G ⊤
  letI := coeffTower g G
  letI := hflat
  haveI : PreservesFiniteLimits
      (Stacks.TensorBimodule.functor Γ(S, ⊤) Γ(S', ⊤) Γ(G, ⊤)) :=
    Stacks.TensorBimodule.preservesFiniteLimits_of_flat Γ(S, ⊤) Γ(S', ⊤) Γ(G, ⊤)
  haveI : PreservesFiniteColimits
      (Stacks.TensorBimodule.functor Γ(S, ⊤) Γ(S', ⊤) Γ(G, ⊤)) :=
    Stacks.TensorBimodule.preservesFiniteColimits_of_flat Γ(S, ⊤) Γ(S', ⊤) Γ(G, ⊤)
  haveI : (baseRestrictScalars f ⋙
      Stacks.TensorBimodule.functor Γ(S, ⊤) Γ(S', ⊤) Γ(G, ⊤)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  (C.sc n).mapHomologyIso
    (baseRestrictScalars f ⋙ Stacks.TensorBimodule.functor Γ(S, ⊤) Γ(S', ⊤) Γ(G, ⊤))

/-! ### The isomorphism -/

/-- **Base change of the cohomology of a quasi-coherent module by a flat module, from a given
hypercovering.**  For a cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

with `S` and `S'` affine, a quasi-coherent `F` on `X`, a quasi-coherent `G` on `S'` whose global
sections are flat over `Γ(S, ⊤)`, and a hypercovering `K` of `X` which is finite in every degree
and all of whose members are affine opens,

`Γ(G, ⊤) ⊗_{Γ(S, ⊤)} H ⁱ(X, F) ≅ H ⁱ(X', (f')^* G ⊗ (g')^* F)`

as `Γ(S', ⊤)`-modules, in every degree `i`.  The scalar structures are described in the module
documentation. -/
def cohomologyBaseChangeIsoOfCover [IsAffine S] [IsAffine S'] (H : IsPullback g' f' f g)
    (F : X.Modules) [F.IsQuasicoherent] (G : S'.Modules) [G.IsQuasicoherent]
    (hflat : letI := baseModule g G ⊤; Module.Flat Γ(S, ⊤) Γ(G, ⊤))
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : X.Opens))))
    (hK : IsHypercovering (Opens.pretopology ↥X) K)
    (hfin : ∀ n : ℕ, Finite (K.obj (op ⦋n⦌)).I)
    (haff : ∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I), IsAffineOpen ((K.obj (op ⦋n⦌)).obj i).left)
    (i : ℕ) :
    letI := baseAlgebra g
    letI := baseModule g G ⊤
    letI := coeffTower g G
    (baseRestrictScalars f ⋙ Stacks.TensorBimodule.functor Γ(S, ⊤) Γ(S', ⊤) Γ(G, ⊤)).obj
        (((_root_.SheafOfModules.evaluation.{u} X.ringCatSheaf
          (op (⊤ : X.Opens))).rightDerived i).obj F) ≅
      (baseRestrictScalars f').obj
        (((_root_.SheafOfModules.evaluation.{u} X'.ringCatSheaf
          (op (⊤ : X'.Opens))).rightDerived i).obj (tensorPullback g' f' F G)) :=
  letI := baseAlgebra g
  letI := baseModule g G ⊤
  letI := coeffTower g G
  haveI : IsAffineHom g' := MorphismProperty.of_isPullback H.flip inferInstance
  haveI hK' : IsHypercovering (Opens.pretopology ↥X')
      (K ⋙ baseChangeFormalCoproduct.{u} g' ⊤) :=
    AlgebraicGeometry.isHypercovering_baseChange g' K hK
  haveI haff' : ∀ (n : ℕ) (j : ((K ⋙ baseChangeFormalCoproduct.{u} g' ⊤).obj (op ⦋n⦌)).I),
      IsAffineOpen (((K ⋙ baseChangeFormalCoproduct.{u} g' ⊤).obj (op ⦋n⦌)).obj j).left :=
    fun n j ↦ AlgebraicGeometry.isAffineOpen_baseChange_obj_left g' K (op ⦋n⦌) j (haff n j)
  (baseRestrictScalars f ⋙
        Stacks.TensorBimodule.functor Γ(S, ⊤) Γ(S', ⊤) Γ(G, ⊤)).mapIso
      (sectionsModuleComplexHomologyIso X K hK haff i F).symm ≪≫
    (baseTensorHomologyIso f g G hflat
      (SectionsOver.sectionsModuleComplex.{u} X.ringCatSheaf ⊤ K F) i).symm ≪≫
    (HomologicalComplex.homologyFunctor _ (up ℕ) i).mapIso
      (sectionsComplexBaseChangeIso H F G hflat K hfin haff) ≪≫
    AlgebraicGeometry.baseRestrictScalarsHomologyIso f'
      (SectionsOver.sectionsModuleComplex.{u} X'.ringCatSheaf ⊤
        (K ⋙ baseChangeFormalCoproduct.{u} g' ⊤) (tensorPullback g' f' F G)) i ≪≫
    (baseRestrictScalars f').mapIso
      (sectionsModuleComplexHomologyIso X' (K ⋙ baseChangeFormalCoproduct.{u} g' ⊤) hK' haff' i
        (tensorPullback g' f' F G))

/-- **Base change of the cohomology of a quasi-coherent module by a flat module.**  For a
cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

with `S` and `S'` affine and `f` quasi-compact and quasi-separated, a quasi-coherent
`𝒪_X`-module `F` and a quasi-coherent `𝒪_{S'}`-module `G` flat over `S`,

`Γ(G, ⊤) ⊗_{Γ(S, ⊤)} H ⁱ(X, F) ≅ H ⁱ(X', (f')^* G ⊗ (g')^* F)`

as `Γ(S', ⊤)`-modules, in every degree `i`.  This is the algebraic heart of
[Stacks, Tag 0GN5] over affine bases.

The hypercovering is a choice and no isomorphism is canonical, so the statement is a `Nonempty`;
`Stacks.AlgebraicGeometry.ModuleBaseChange.cohomologyBaseChangeIsoOfCover` is the isomorphism
attached to a hypercovering. -/
theorem nonempty_cohomologyBaseChangeIso [IsAffine S] [IsAffine S']
    (H : IsPullback g' f' f g) [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] (G : S'.Modules) [G.IsQuasicoherent]
    (hG : IsFlatOver g.toLRSHom.toShHom G) (i : ℕ) :
    letI := baseAlgebra g
    letI := baseModule g G ⊤
    letI := coeffTower g G
    Nonempty
      ((baseRestrictScalars f ⋙ Stacks.TensorBimodule.functor Γ(S, ⊤) Γ(S', ⊤) Γ(G, ⊤)).obj
          (((_root_.SheafOfModules.evaluation.{u} X.ringCatSheaf
            (op (⊤ : X.Opens))).rightDerived i).obj F) ≅
        (baseRestrictScalars f').obj
          (((_root_.SheafOfModules.evaluation.{u} X'.ringCatSheaf
            (op (⊤ : X'.Opens))).rightDerived i).obj (tensorPullback g' f' F G))) := by
  let := baseAlgebra g
  let := baseModule g G ⊤
  let := coeffTower g G
  have : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace ↥X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨K, hK, hKprop⟩ :=
    Stacks.AlgebraicGeometry.UniversalPushforward.exists_finite_affine_hypercovering X
  exact ⟨cohomologyBaseChangeIsoOfCover H F G (flat_sections_of_isFlatOver g G hG) K hK
    (fun n ↦ (hKprop n).1) (fun n j ↦ (hKprop n).2 j) i⟩

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
