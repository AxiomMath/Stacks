module

public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.AffineGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardPullbackTensor
public import StacksFrontier.CategoryTheory.Adjunction.PullbackInternalHomPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorAssociativityModels
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AssociativityGeneral

/-!
# `Rg_*` of the map of Stacks 08JF on algebraic spaces

Let `g : X' ⟶ X` be a quasi-compact and quasi-separated morphism of algebraic spaces. For
`M, K ∈ D(𝒪_X)` the map of Stacks 08JF is `φ : Lg^*R𝓗om(M, K) ⟶ R𝓗om(Lg^*M, Lg^*K)`. This file
shows that, for `R𝓗om(M, K)` and `K` in `D_QCoh(𝒪_X)`, `Rg_*φ` is invertible as soon as the
tensor–Hom diagonal `Rg_*𝒪_{X'} ⊗^L R𝓗om(M, K) ⟶ R𝓗om(M, Rg_*𝒪_{X'} ⊗^L K)` is, and that the
isomorphism of Stacks 07A4 is compatible with the associators of `⊗^L`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedTensorAssociator`,
  `AlgebraicGeometry.Space.smallEtaleDerivedTensorLeftUnitor`: the associator and left unitor of
  `⊗^L` on `D(𝒪_X)`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackTensorIso_associativity`: Stacks 07A4 is
  compatible with the associators.
* `AlgebraicGeometry.Space.isIso_derivedPushforward_map_smallEtaleDerivedPullbackSheafHomMap`:
  `Rg_*φ` is invertible when the tensor–Hom diagonal at `Rg_*𝒪_{X'}` is.

## References

* [Stacks Project, Tag 0E4S](https://stacks.math.columbia.edu/tag/0E4S)
* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 08IN](https://stacks.math.columbia.edu/tag/08IN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X X' : AlgebraicSpaces B S hS}

/-- The associator `(K ⊗^L L) ⊗^L M ≅ K ⊗^L (L ⊗^L M)` of the derived tensor product on an
algebraic space: the associativity constraint of the monoidal structure of Stacks 0FPT on `D(𝒪_X)`,
transported to `⊗^L`. -/
abbrev smallEtaleDerivedTensorAssociator (X : AlgebraicSpaces B S hS)
    (A A' A'' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    ((smallEtaleDerivedTensor B S hS X).obj
        (((smallEtaleDerivedTensor B S hS X).obj A).obj A')).obj A'' ≅
      ((smallEtaleDerivedTensor B S hS X).obj A).obj
        (((smallEtaleDerivedTensor B S hS X).obj A').obj A'') :=
  (smallEtaleDerivedTensorProduct B S hS X).associatorGeneral A A' A''

/-- The left unit law `𝒪_X ⊗^L K ≅ K` of the derived tensor product on an algebraic space. -/
abbrev smallEtaleDerivedTensorLeftUnitor (X : AlgebraicSpaces B S hS) :
    (smallEtaleDerivedTensor B S hS X).obj (structureDerived X) ≅ 𝟭 _ :=
  (smallEtaleDerivedTensorProduct B S hS X).leftUnitor

/-- The isomorphism of Stacks 07A4 on algebraic spaces is compatible with the associators of `⊗^L`:
for `g : X' ⟶ X` and `A, A', A'' ∈ D(𝒪_X)` the two isomorphisms
`Lg^*((A ⊗^L A') ⊗^L A'') ≅ Lg^*A ⊗^L (Lg^*A' ⊗^L Lg^*A'')` agree. -/
theorem smallEtaleDerivedPullbackTensorIso_associativity (g : X' ⟶ X)
    (A A' A'' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedModulePullback B S hS g).map
          (smallEtaleDerivedTensorAssociator X A A' A'').hom ≫
        (smallEtaleDerivedPullbackTensorIso g).hom.app
          (A, ((smallEtaleDerivedTensor B S hS X).obj A').obj A'') ≫
        ((smallEtaleDerivedTensor B S hS X').obj
          ((smallEtaleDerivedModulePullback B S hS g).obj A)).map
            ((smallEtaleDerivedPullbackTensorIso g).hom.app (A', A'')) =
      (smallEtaleDerivedPullbackTensorIso g).hom.app
          (((smallEtaleDerivedTensor B S hS X).obj A).obj A', A'') ≫
        ((smallEtaleDerivedTensor B S hS X').map
          ((smallEtaleDerivedPullbackTensorIso g).hom.app (A, A'))).app
            ((smallEtaleDerivedModulePullback B S hS g).obj A'') ≫
        (smallEtaleDerivedTensorAssociator X' ((smallEtaleDerivedModulePullback B S hS g).obj A)
          ((smallEtaleDerivedModulePullback B S hS g).obj A')
          ((smallEtaleDerivedModulePullback B S hS g).obj A'')).hom :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso_associativity
    (smallEtaleRingedToposHom B S hS g) (smallEtaleDerivedTensorProduct B S hS X')
    (smallEtaleDerivedTensorProduct B S hS X) A A' A''

/-- `Rg_*` of the map of Stacks 08JF is invertible when the tensor–Hom diagonal at `Rg_*𝒪_{X'}` is,
for `g` quasi-compact and quasi-separated, `R𝓗om(M, K)` and `K` in `D_QCoh(𝒪_X)`. -/
theorem isIso_derivedPushforward_map_smallEtaleDerivedPullbackSheafHomMap (g : X' ⟶ X)
    (hgqc : IsQuasiCompact B S hS g.hom) (hgqs : IsQuasiSeparated B S hS g.hom)
    (M K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hH : QcohDerived B S hS X (((smallEtaleDerivedSheafHom B S hS X).obj (op M)).obj K))
    (hK : QcohDerived B S hS X K)
    (hδ : IsIso (CategoryTheory.PullbackInternalHom.leftTensorHomDiagonal
      (smallEtaleDerivedTensor B S hS X) (smallEtaleDerivedSheafHom B S hS X)
      (smallEtaleDerivedTensorSheafHomAdjunction B S hS X) (smallEtaleDerivedTensorAssociator X)
      ((derivedPushforward (X := smallEtaleRingedTopos B S hS X')
        (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS g)).obj
          (structureDerived X')) M K)) :
    IsIso ((derivedPushforward (X := smallEtaleRingedTopos B S hS X')
        (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS g)).map
      (smallEtaleDerivedPullbackSheafHomMap g M K)) := by
  have hO : QcohDerived B S hS X' (structureDerived X') :=
    qcohDerived_singleFunctor_structureModule (X := X'.1) (hX := X'.2)
  have h1 := isIso_smallEtaleProjectionFormulaMap B S hS g hgqc hgqs _ hO _ hH
  have h2 := isIso_smallEtaleProjectionFormulaMap B S hS g hgqc hgqs _ hO _ hK
  have h3 := CategoryTheory.PullbackInternalHom.isIso_map_pullbackHomMap
    (smallEtaleDerivedModuleAdjunction B S hS g) (smallEtaleDerivedTensor B S hS X)
    (smallEtaleDerivedTensor B S hS X') (smallEtaleDerivedPullbackTensorIso g)
    (smallEtaleDerivedSheafHom B S hS X) (smallEtaleDerivedSheafHom B S hS X')
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X)
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X') (structureDerived X')
    (smallEtaleDerivedTensorLeftUnitor X') (smallEtaleDerivedTensorAssociator X)
    (smallEtaleDerivedTensorAssociator X') (smallEtaleDerivedPullbackTensorIso_associativity g)
    (fun a A' A'' ↦
      (smallEtaleDerivedTensorProduct B S hS X').associatorGeneral_naturality_left a A' A'')
    (fun A A' ↦ (smallEtaleDerivedTensorProduct B S hS X').leftUnitor_tensor A A') M K
  have e : smallEtaleDerivedPullbackSheafHomMap g M K =
      CategoryTheory.PullbackInternalHom.pullbackHomMap (smallEtaleDerivedTensor B S hS X)
        (smallEtaleDerivedTensor B S hS X') (smallEtaleDerivedPullbackTensorIso g)
        (smallEtaleDerivedSheafHom B S hS X) (smallEtaleDerivedSheafHom B S hS X')
        (smallEtaleDerivedTensorSheafHomAdjunction B S hS X)
        (smallEtaleDerivedTensorSheafHomAdjunction B S hS X') M K := by
    rw [smallEtaleDerivedPullbackSheafHomMap_eq_homEquiv_counit]
    unfold CategoryTheory.PullbackInternalHom.pullbackHomMap
    congr 1
  rw [e]
  exact h3 h1 h2 hδ

end AlgebraicGeometry.Space

end
