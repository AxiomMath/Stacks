module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Spaces.Coherator
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsTerminalChart
import StacksCore.Tactic.StacksAttribute

/-!
# The coherator of an affine algebraic space is the associated module of the global sections

Let `X` be an affine algebraic space over a scheme `S` contained in a big fppf site `B`, and set
`A = Γ(X, 𝒪_X)`.  Stacks 08H0 (1) says that the coherator

`Q_X : Mod(𝒪_X) ⥤ QCoh(𝒪_X)`

of Stacks 077V (2) is the functor sending an `𝒪_X`-module `𝓕` to the quasi-coherent
`𝒪_X`-module associated to the `A`-module `Γ(X, 𝓕)`.  That is proved here, in both of the shapes
in which it is a statement: `Γ(X, -) ⋙ (-)^~` *is* a right adjoint of the inclusion
`QCoh(𝒪_X) ⥤ Mod(𝒪_X)`, and consequently the coherator is naturally isomorphic to it.

Nothing is assumed.  The coherator and its adjunction are the canonical ones of
`StacksFrontier/AlgebraicGeometry/Spaces/Coherator.lean`, built from Stacks 077V (2); the
associated-module equivalence `Mod(A) ≌ QCoh(𝒪_X)` and its adjunction to global sections — the
affine case of Stacks 03DX (2) and of Stacks 01BH (4) — are the ones constructed in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineSpaceAssociatedModule.lean`.

## Main definitions

* `AlgebraicGeometry.Space.affineSpaceAffineChart`, together with
  `AlgebraicGeometry.Space.isAffine_affineSpaceAffineChart` and
  `AlgebraicGeometry.Space.affineSpaceAffineChartIso`: the affine object of the site that an
  affine algebraic space is isomorphic to, with its affineness and the isomorphism.
* `AlgebraicGeometry.Space.affineSpaceAssociatedModuleEquivalence`: `Mod(A) ≌ QCoh(𝒪_X)`.
* `AlgebraicGeometry.Space.affineSpaceGlobalSections`: `Γ(X, -) : Mod(𝒪_X) ⥤ Mod(A)`.

## Main results

* `AlgebraicGeometry.Space.inclusionAdjunctionGlobalSectionsAssociated_of_isAffineSpace`:
  **Stacks 08H0 (1)** — `Γ(X, -) ⋙ (-)^~` is right adjoint to `QCoh(𝒪_X) ⥤ Mod(𝒪_X)`, so it is
  a coherator of `X`.
* `AlgebraicGeometry.Space.coheratorIsoGlobalSectionsAssociated_of_isAffineSpace`:
  **Stacks 08H0 (1)** — the coherator of `X` is naturally isomorphic to `Γ(X, -) ⋙ (-)^~`.
* `AlgebraicGeometry.Space.globalFunctionRingEquiv_of_isAffineSpace`: the ring over which the
  modules are taken is `A = Γ(X, 𝒪_X)`.

## How `A` and `Γ(X, -)` are read

The ring `A = Γ(X, 𝒪_X)` of compatible sections of the structure sheaf on the whole small étale
site of `X` is a subring of a product indexed by the objects of that site, so it lies one
universe above the sections themselves, while the coherator — and with it `QCoh(𝒪_X)` — lives at
the module universe `u` of the schemes.  An equivalence `Mod(A) ≌ QCoh(𝒪_X)` with the modules on
the left at that larger universe does not exist:
`AlgebraicGeometry.Space.not_nonempty_equivalence_moduleCat_quasicoherentSheaves_yoneda` refutes
it for a representable affine algebraic space with nontrivial ring of global functions.  So `A`
is read at the universe of the schemes, as the coordinate ring `Γ(T, 𝒪_T)` of the affine chart,
and `Γ(X, -)` as the sections over that chart.  Two statements say that this *is* `A` and is
`Γ(X, -)`:

* `AlgebraicGeometry.Space.globalFunctionRingEquiv_of_isAffineSpace`, which is
  `AlgebraicGeometry.Space.globalSectionsChartRingEquiv` at the terminal chart supplied by the
  isomorphism with the representable presheaf: evaluation there is a ring isomorphism
  `Γ(X, 𝒪_X) ≃+* Γ(T, 𝒪_T)`;
* `AlgebraicGeometry.Space.affineChartGlobalSections_obj_carrier` together with
  `AlgebraicGeometry.Space.globalSectionsEquivSectionsAtTerminalChart`, which say that
  `AlgebraicGeometry.Space.affineSpaceGlobalSections` at `𝓕` is the module of sections of `𝓕`
  over a terminal chart and that those are the compatible global sections of `𝓕`.

## Implementation notes

The affine chart is chosen out of `AlgebraicGeometry.Space.IsAffineSpace` by `Exists.choose`, as
in `AlgebraicGeometry.Space.isEquivalence_quasicoherentDerivedComparison_of_isAffineSpace`.  Any
other choice gives a canonically isomorphic equivalence and a canonically isomorphic global
sections functor, both right adjoints of the same inclusion.

## References

* [Stacks Project, Tag 08H0](https://stacks.math.columbia.edu/tag/08H0)
* [Stacks Project, Tag 077V](https://stacks.math.columbia.edu/tag/077V)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hAffine : IsAffineSpace B S hS F)

/-! ### The affine chart of an affine algebraic space -/

/-- The object of the big fppf site with affine underlying scheme that an affine algebraic space
is isomorphic to, chosen out of `AlgebraicGeometry.Space.IsAffineSpace`. -/
def affineSpaceAffineChart : BigFppfOver B S hS := hAffine.choose

/-- The underlying scheme of `AlgebraicGeometry.Space.affineSpaceAffineChart` is affine. -/
theorem isAffine_affineSpaceAffineChart :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (affineSpaceAffineChart B S hS F hAffine)) :=
  hAffine.choose_spec.1

/-- An affine algebraic space is isomorphic to the presheaf represented by
`AlgebraicGeometry.Space.affineSpaceAffineChart`. -/
def affineSpaceAffineChartIso :
    F ≅ yoneda.obj (affineSpaceAffineChart B S hS F hAffine) :=
  hAffine.choose_spec.2.some

/-- `A = Γ(X, 𝒪_X)` read at the universe of the schemes: the coordinate ring of the affine chart
of `AlgebraicGeometry.Space.affineSpaceAffineChart`.  It is the ring of global regular functions
of `X`, by `AlgebraicGeometry.Space.globalFunctionRingEquiv_of_isAffineSpace`. -/
abbrev affineSpaceCoordinateRing : CommRingCat.{u} :=
  Γ((BigFppfOver.toScheme B S hS).obj (affineSpaceAffineChart B S hS F hAffine), ⊤)

/-- **The coordinate ring of the affine chart is `A = Γ(X, 𝒪_X)`.**  The isomorphism with the
representable presheaf makes the chart terminal in the small étale site of `X`
(`AlgebraicGeometry.Space.isTerminalEtaleChartOfIso`), and evaluation of a compatible family of
global functions at a terminal chart is a ring isomorphism
(`AlgebraicGeometry.Space.globalSectionsChartRingEquiv`). -/
def globalFunctionRingEquiv_of_isAffineSpace :
    Stacks.Cohomology.SiteModules.GlobalSectionRing
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) ≃+*
      affineSpaceCoordinateRing B S hS F hAffine :=
  globalSectionsChartRingEquiv B S hS ⟨F, hF⟩
    (isTerminalEtaleChartOfIso B S hS (affineSpaceAffineChartIso B S hS F hAffine))

/-! ### The associated-module equivalence and the global sections of an affine algebraic space -/

/-- **The associated-module equivalence `Mod(A) ≌ QCoh(𝒪_X)` of an affine algebraic space**, the
affine case of Descent, Proposition 03DX (2) on the small étale site: `M ↦ M^~`.

This is `AlgebraicGeometry.Space.affineChartAssociatedModuleEquivalence` at the chart chosen out
of affineness. -/
def affineSpaceAssociatedModuleEquivalence :
    ModuleCat.{u} (affineSpaceCoordinateRing B S hS F hAffine) ≌
      QuasicoherentSheaves.{u, u} B S hS F hF :=
  affineChartAssociatedModuleEquivalence B S hS F hF _
    (isAffine_affineSpaceAffineChart B S hS F hAffine)
    (affineSpaceAffineChartIso B S hS F hAffine)

/-- **`Γ(X, -) : Mod(𝒪_X) ⥤ Mod(A)`**, the global sections of an `𝒪_X`-module read as a module
over `A = Γ(X, 𝒪_X)`, at the universe of the schemes.

This is `AlgebraicGeometry.Space.affineChartGlobalSections` at the chart chosen out of
affineness; `AlgebraicGeometry.Space.affineChartGlobalSections_obj_carrier` and
`AlgebraicGeometry.Space.globalSectionsEquivSectionsAtTerminalChart` identify its value at `𝓕`
with the compatible global sections of `𝓕`. -/
def affineSpaceGlobalSections :
    Modules.{u, u} B S hS F hF ⥤ ModuleCat.{u} (affineSpaceCoordinateRing B S hS F hAffine) :=
  affineChartGlobalSections B S hS F hF _
    (isAffine_affineSpaceAffineChart B S hS F hAffine)
    (affineSpaceAffineChartIso B S hS F hAffine)

/-- **The affine case of Stacks 01BH (4) for an affine algebraic space**: `M ↦ M^~`, followed by
the inclusion of the quasi-coherent modules, is left adjoint to `Γ(X, -)`. -/
def affineSpaceAssociatedModuleAdjunction :
    (affineSpaceAssociatedModuleEquivalence B S hS F hF hAffine).functor ⋙
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O))).ι ⊣
      affineSpaceGlobalSections B S hS F hF hAffine :=
  affineChartAssociatedModuleAdjunction B S hS F hF _
    (isAffine_affineSpaceAffineChart B S hS F hAffine)
    (affineSpaceAffineChartIso B S hS F hAffine)

/-- `Γ(X, -)` is additive. -/
instance additive_affineSpaceGlobalSections :
    (affineSpaceGlobalSections B S hS F hF hAffine).Additive :=
  inferInstanceAs ((affineChartGlobalSections B S hS F hF _
    (isAffine_affineSpaceAffineChart B S hS F hAffine)
    (affineSpaceAffineChartIso B S hS F hAffine)).Additive)

/-- The associated-module functor `M ↦ M^~` is additive. -/
instance additive_affineSpaceAssociatedModuleEquivalence_functor :
    (affineSpaceAssociatedModuleEquivalence B S hS F hF hAffine).functor.Additive :=
  inferInstanceAs ((affineChartAssociatedModuleEquivalence B S hS F hF _
    (isAffine_affineSpaceAffineChart B S hS F hAffine)
    (affineSpaceAffineChartIso B S hS F hAffine)).functor.Additive)

/-! ### Stacks 08H0 (1) -/

/-- **Stacks 08H0 (1).**  Let `X` be an affine algebraic space over a scheme `S` and set
`A = Γ(X, 𝒪_X)`.  The functor sending an `𝒪_X`-module `𝓕` to the quasi-coherent `𝒪_X`-module
associated to the `A`-module `Γ(X, 𝓕)` is a right adjoint of the inclusion
`QCoh(𝒪_X) ⥤ Mod(𝒪_X)`; that is, it is a coherator of `X` in the sense of Stacks 077V (2).

The proof is the source's: composing the adjunction `(-)^~ ⋙ ι ⊣ Γ(X, -)` of the affine case of
Stacks 01BH (4) with the adjunction `((-)^~)^{-1} ⊣ (-)^~` of the associated-module equivalence
gives `((-)^~)^{-1} ⋙ (-)^~ ⋙ ι ⊣ Γ(X, -) ⋙ (-)^~`, and the left-hand side is `ι` by the counit
of the equivalence. -/
@[stacks 08H0 "part (1)"]
def inclusionAdjunctionGlobalSectionsAssociated_of_isAffineSpace :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι ⊣
      affineSpaceGlobalSections B S hS F hF hAffine ⋙
        (affineSpaceAssociatedModuleEquivalence B S hS F hF hAffine).functor :=
  have hleft : (affineSpaceAssociatedModuleEquivalence B S hS F hF hAffine).inverse ⋙
      ((affineSpaceAssociatedModuleEquivalence B S hS F hF hAffine).functor ⋙
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O))).ι) ≅
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (affineSpaceAssociatedModuleEquivalence B S hS F hF hAffine).counitIso _ ≪≫
      Functor.leftUnitor _
  ((affineSpaceAssociatedModuleEquivalence B S hS F hF hAffine).symm.toAdjunction.comp
    (affineSpaceAssociatedModuleAdjunction B S hS F hF hAffine)).ofNatIsoLeft hleft

/-- **Stacks 08H0 (1).**  Let `X` be an affine algebraic space over a scheme `S` and set
`A = Γ(X, 𝒪_X)`.  The coherator `Q_X : Mod(𝒪_X) ⥤ QCoh(𝒪_X)` of Stacks 077V (2) is naturally
isomorphic to the functor sending `𝓕` to the quasi-coherent `𝒪_X`-module associated to the
`A`-module `Γ(X, 𝓕)`.

Both are right adjoints of the inclusion `QCoh(𝒪_X) ⥤ Mod(𝒪_X)` — the coherator by
`AlgebraicGeometry.Space.coheratorAdjunction` and the other by
`AlgebraicGeometry.Space.inclusionAdjunctionGlobalSectionsAssociated_of_isAffineSpace` — and a
right adjoint is unique up to a unique natural isomorphism. -/
@[stacks 08H0 "part (1)"]
def coheratorIsoGlobalSectionsAssociated_of_isAffineSpace :
    coherator B S hS F hF ≅
      affineSpaceGlobalSections B S hS F hF hAffine ⋙
        (affineSpaceAssociatedModuleEquivalence B S hS F hF hAffine).functor :=
  Adjunction.rightAdjointUniq (coheratorAdjunction B S hS F hF)
    (inclusionAdjunctionGlobalSectionsAssociated_of_isAffineSpace B S hS F hF hAffine)

end AlgebraicGeometry.Space

end
