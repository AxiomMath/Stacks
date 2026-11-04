module

public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethFormula
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatKunneth.GlobalCupProductAffine
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeKunnethFormula
public import StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalKunnethMapCanonical
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedSectionsLeftAdjoint
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BoundedComparison
public import StacksFrontier.Homology.DerivedIndexing.Extend
import StacksCore.Tactic.StacksAttribute

/-!
# The de Rham Künneth formula over an affine base, from the relative one

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes with `S` affine, `A = Γ(S, 𝒪_S)`, and
`f : X ×_S Y ⟶ S` the structure morphism of the fibre product. [Stacks, Tag 0FMB] asserts that
the de Rham Künneth map

`RΓ(X, Ω^•_{X/S}) ⊗^𝐋_A RΓ(Y, Ω^•_{Y/S}) ⟶ RΓ(X ×_S Y, Ω^•_{X ×_S Y/S})`

is an isomorphism in `D(A)`. This file proves what is needed to pass from the relative statement,
the invertibility of

`Ra_*Ω^•_{X/S} ⊗^𝐋_{𝒪_S} Rb_*Ω^•_{Y/S} ⟶ Rf_*Ω^•_{X ×_S Y/S}`

of [Stacks, Tag 0FMC], to the global one. Applying `RΓ(S, -)` to the relative map gives the
global map, read through the Leray isomorphisms of [Stacks, Tag 0D5W] and the `A`-linear global
cup product of [Stacks, Section 0FKU] at the pair `(Ra_*Ω^•_{X/S}, Rb_*Ω^•_{Y/S})`. So two facts
are needed besides the relative statement, and both are proved here at the source's hypotheses:

* the global cup product on an affine base is invertible at every pair of complexes with
  quasi-coherent cohomology sheaves, which comes from the Spec–Γ equivalence of
  [Stacks, Tag 06Z0];
* `Ra_*Ω^•_{X/S}` has quasi-coherent cohomology sheaves when `a` is quasi-compact and
  quasi-separated. This is [Stacks, Tag 0FLX], read in the unbounded derived category and at the
  complex of inverse-image modules underlying the de Rham complex of differential operators.

## Main results

* `Stacks.Cohomology.BoxKunneth.isQuasicoherent_homology_derivedPushforward_leftComplex`:
  [Stacks, Tag 0FLX] at the complex that the Künneth maps push forward.
* `Stacks.Cohomology.BoxKunneth.globalBoxKunnethMap_eq_baseSections`: the global Künneth map of
  the box product is `RΓ(S, -)` of the relative one, conjugated by the Leray isomorphisms and
  preceded by the global cup product.
* `Stacks.Cohomology.BoxKunneth.isIso_globalBoxKunnethMap_of_isIso_relative` and
  `Stacks.Cohomology.BoxKunneth.isIso_deRhamGlobalKunnethMap_of_isIso_relative`: the global map
  is invertible when the cup product at the pair is and the relative map is. For the de Rham
  complexes over an affine base the first condition holds for qcqs morphisms, so the relative
  isomorphism of [Stacks, Tag 0FMC] is the only remaining input.
* `AlgebraicGeometry.isAffineHom_diagonal_of_isAffine` and
  `AlgebraicGeometry.quasiSeparated_of_isAffineHom_diagonal_terminal`: over an affine base an
  affine absolute diagonal gives an affine relative diagonal and a quasi-separated structure
  morphism. These translate the hypotheses of [Stacks, Tag 0FMB] into those of
  [Stacks, Tag 0FMC].

## Implementation notes

*The cup product is the canonical one.* The global map is
`Stacks.Cohomology.BoxKunneth.deRhamGlobalKunnethMap` at
`Stacks.Cohomology.GlobalKunneth.globalCupProductCanonical`, the cup product that the map of
[Stacks, Tag 0FLR] uses (`Stacks.Cohomology.BoxKunneth.globalBoxKunnethMapCanonical`). It is the
cup product built from the one-point comparison `onePointComparisonOfBaseTensorComparison` at
`baseTensorComparison`. Its tensor comparison is invertible because both of its factors
are, and its adjunction `derivedBaseAdjunction` has the fully faithful left adjoint
`derivedBaseExtension` on an affine scheme. So the unit is invertible, and the counit is
invertible on the essential image, which
`AlgebraicGeometry.AffineDerivedSections.essImage_derivedSectionsLeftAdjoint` identifies as
containing the quasi-coherent part.

*Two readings of the de Rham complex.* The Künneth maps push forward the complex of
`a^{-1}𝒪_S`-modules underlying the `ℤ`-indexed de Rham complex of differential operators,
`leftComplex a (deRhamDiffOpCochainComplex a)`. [Stacks, Tag 0FLX] is proved in
`StacksFrontier/AlgebraicGeometry/DeRham/DerivedDirectImage.lean` for
`Stacks.DeRhamDirectImage.deRhamCochainComplex`, the extension by zero of the de Rham complex of
`a^{-1}𝒪_S`-modules, and on `D⁺`. The two complexes have the same terms, and their differentials
agree on local sections by `AlgebraicGeometry.Scheme.Hom.deRhamDiffOpComplex_d_apply`. Extension
by zero commutes with applying an additive functor termwise
(`Stacks.DerivedIndexing.mapExtendIso`). The two derived direct images agree on bounded below
complexes (`boundedDerivedPushforwardIso`).

## References

* [Stacks Project, Tag 0FMB](https://stacks.math.columbia.edu/tag/0FMB)
* [Stacks Project, Tag 0FMC](https://stacks.math.columbia.edu/tag/0FMC)
* [Stacks Project, Tag 0FLX](https://stacks.math.columbia.edu/tag/0FLX)
* [Stacks Project, Tag 0FLR](https://stacks.math.columbia.edu/tag/0FLR)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory
open AlgebraicGeometry.Scheme.Hom
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedSectionsLeftAdjoint
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.GlobalKunneth
open Stacks.DeRhamDirectImage
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

universe u

attribute [local instance 2000] HasDerivedCategory.standard

namespace Stacks.Cohomology.BoxKunneth

variable {X S : Scheme.{u}} (a : X ⟶ S)

/-- The de Rham complex of differential operators, read termwise as `a^{-1}𝒪_S`-modules, is the
de Rham complex of `a^{-1}𝒪_S`-modules: the terms are the same, and the differentials agree on
local sections. -/
def deRhamComplexInverseImageIso :
    ((toInverseImageModules a).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (deRhamDiffOpComplex a) ≅
      (show CochainComplex (Modules (inverseImageBase a)) ℕ from Scheme.Hom.deRhamComplex a) :=
  HomologicalComplex.Hom.isoOfComponents (fun p => Iso.refl _) (by
    rintro p _ rfl
    simp only [Iso.refl_hom]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun s => ?_
    exact (deRhamDiffOpComplex_d_apply a p U s).symm)

/-- The `ℤ`-indexed complex of `a^{-1}𝒪_S`-modules that the Künneth maps push forward is the
extension by zero of the de Rham complex of `a^{-1}𝒪_S`-modules. -/
def leftComplexDeRhamIso : leftComplex a (deRhamDiffOpCochainComplex a) ≅ deRhamCochainComplex a :=
  (Stacks.DerivedIndexing.mapExtendIso (toInverseImageModules a) ComplexShape.embeddingUpNat
    (deRhamDiffOpComplex a)).symm ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor _).mapIso (deRhamComplexInverseImageIso a)

/-- The derived direct image `Rp_*Ω^•_{X/S}` of [Stacks, Tag 0FLX], formed on `D⁺`, is the
unbounded derived direct image of the complex that the Künneth maps push forward. -/
def derivedDeRhamDirectImageIso :
    DerivedCategory.Plus.ι.obj (derivedDeRhamDirectImage a) ≅
      (derivedPushforward (inverseImageBaseProjection a)).obj
        (DerivedCategory.Q.obj (leftComplex a (deRhamDiffOpCochainComplex a))) :=
  (boundedDerivedPushforwardIso (inverseImageBaseProjection a)).app
      (DerivedCategory.Plus.Q.obj
        ⟨deRhamCochainComplex a, 0, isStrictlyGE_deRhamCochainComplex a⟩) ≪≫
    (derivedPushforward (inverseImageBaseProjection a)).mapIso
      (DerivedCategory.Q.mapIso (leftComplexDeRhamIso a).symm)

/-- **[Stacks, Tag 0FLX] at the complex that the Künneth maps push forward**: for `a`
quasi-compact and quasi-separated, every cohomology sheaf of `Ra_*Ω^•_{X/S}` is a quasi-coherent
`𝒪_S`-module. Here the derived direct image is the unbounded one, and the complex is the one
underlying the de Rham complex of differential operators. -/
theorem isQuasicoherent_homology_derivedPushforward_leftComplex [QuasiCompact a]
    [QuasiSeparated a] (j : ℤ) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) j).obj
      ((derivedPushforward (inverseImageBaseProjection a)).obj
        (DerivedCategory.Q.obj (leftComplex a (deRhamDiffOpCochainComplex a))))).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor _ j).mapIso (derivedDeRhamDirectImageIso a))
    (isQuasicoherent_homology_derivedDeRhamDirectImage a j)

end Stacks.Cohomology.BoxKunneth

namespace Stacks.Cohomology.BoxKunneth

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
  (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
  (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
  (n₁ n₂ : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂]

/-- **The global Künneth map of the box product is `RΓ(S, -)` of the relative one**, preceded
by the Leray isomorphisms of [Stacks, Tag 0D5W] in the two factors and the global cup product at
`(Ra_*𝓕^•, Rb_*𝓖^•)`, and followed by the Leray isomorphism on the target. Steps (4) and (5) are
moved across the Leray isomorphism by its naturality. -/
theorem globalBoxKunnethMap_eq_baseSections (κ : GlobalCupProduct S.toRingedSpace) :
    globalBoxKunnethMap a b K L n₁ n₂ κ =
      (Functor.uncurry.obj (tensorBase S.toRingedSpace)).map
          ((lerayIso (inverseImageBaseProjection a)).inv.app
              (DerivedCategory.Q.obj (leftComplex a K)) ×ₘ
            (lerayIso (inverseImageBaseProjection b)).inv.app
              (DerivedCategory.Q.obj (rightComplex b L))) ≫
        κ.app ((derivedPushforward (inverseImageBaseProjection a)).obj
              (DerivedCategory.Q.obj (leftComplex a K)),
            (derivedPushforward (inverseImageBaseProjection b)).obj
              (DerivedCategory.Q.obj (rightComplex b L))) ≫
        (baseSections S.toRingedSpace).map (relativeBoxKunnethMap a b K L n₁ n₂) ≫
        (lerayIso (inverseImageBaseProjection (pullback.fst a b ≫ a))).hom.app
          (DerivedCategory.Q.obj (boxTotalModules a b K L n₁ n₂)) := by
  refine (globalBoxKunnethMap_eq a b K L n₁ n₂ κ).trans ?_
  refine (congrArg (· ≫ _) (kunnethGlobalMap_eq _ _ _ _ _ _ _ κ _ _)).trans ?_
  simp only [Category.assoc, relativeBoxKunnethMap]
  refine congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ?_)
  exact ((congrArg (_ ≫ ·)
      ((lerayIso (inverseImageBaseProjection (pullback.fst a b ≫ a))).hom.naturality
      (boxTotalDerivedComparison a b K L n₁ n₂ (boxTotalComparison a b K L n₁ n₂))).symm).trans
    (Category.assoc _ _ _).symm).trans
    (congrArg (· ≫ _) ((baseSections S.toRingedSpace).map_comp _ _).symm)


/-- **The global Künneth map of the box product is invertible as soon as the relative one is and
the global cup product is invertible at `(Ra_*𝓕^•, Rb_*𝓖^•)`**: by
`globalBoxKunnethMap_eq_baseSections` it is a composite of those two maps with Leray
isomorphisms. -/
theorem isIso_globalBoxKunnethMap_of_isIso_relative (κ : GlobalCupProduct S.toRingedSpace)
    (hκ : IsIso (κ.app ((derivedPushforward (inverseImageBaseProjection a)).obj
        (DerivedCategory.Q.obj (leftComplex a K)),
      (derivedPushforward (inverseImageBaseProjection b)).obj
        (DerivedCategory.Q.obj (rightComplex b L)))))
    (hrel : IsIso (relativeBoxKunnethMap a b K L n₁ n₂)) :
    IsIso (globalBoxKunnethMap a b K L n₁ n₂ κ) := by
  rw [globalBoxKunnethMap_eq_baseSections]
  have := hrel
  have h₁ : IsIso ((Functor.uncurry.obj (tensorBase S.toRingedSpace)).map
      ((lerayIso (inverseImageBaseProjection a)).inv.app
          (DerivedCategory.Q.obj (leftComplex a K)) ×ₘ
        (lerayIso (inverseImageBaseProjection b)).inv.app
          (DerivedCategory.Q.obj (rightComplex b L)))) :=
    ((Functor.uncurry.obj (tensorBase S.toRingedSpace)).mapIso
      (Iso.prod ((lerayIso (inverseImageBaseProjection a)).symm.app
          (DerivedCategory.Q.obj (leftComplex a K)))
        ((lerayIso (inverseImageBaseProjection b)).symm.app
          (DerivedCategory.Q.obj (rightComplex b L))))).isIso_hom
  have h₃ : IsIso ((baseSections S.toRingedSpace).map (relativeBoxKunnethMap a b K L n₁ n₂)) :=
    Functor.map_isIso _ (relativeBoxKunnethMap a b K L n₁ n₂)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ (@IsIso.comp_isIso _ _ _ _ _ _ _ hκ
    (@IsIso.comp_isIso _ _ _ _ _ _ _ h₃ inferInstance))


section DeRham

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **The de Rham Künneth map over an affine base is invertible as soon as the relative one of
[Stacks, Tag 0FMC] is.** For `S` affine and `a`, `b` quasi-compact and quasi-separated, the map
`RΓ(X, Ω^•_{X/S}) ⊗^𝐋_A RΓ(Y, Ω^•_{Y/S}) ⟶ RΓ(X ×_S Y, Ω^•_{X ×_S Y/S})`, built from the
canonical global cup product, is an isomorphism provided the relative cup product
`Ra_*Ω^•_{X/S} ⊗^𝐋_{𝒪_S} Rb_*Ω^•_{Y/S} ⟶ Rf_*Ω^•_{X ×_S Y/S}` is. The global cup product at
`(Ra_*Ω^•_{X/S}, Rb_*Ω^•_{Y/S})` is invertible by
`AlgebraicGeometry.FlatKunneth.isIso_globalCupProductCanonical_app` and [Stacks, Tag 0FLX]. -/
theorem isIso_deRhamGlobalKunnethMap_of_isIso_relative [IsAffine S] [QuasiCompact a]
    [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (h : IsIso (deRhamRelativeKunnethMap a b)) :
    IsIso (deRhamGlobalKunnethMap a b (globalCupProductCanonical S.toRingedSpace)) := by
  let e := DerivedCategory.Q.mapIso
    (((toInverseImageModules (pullback.fst a b ≫ a)).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso (deRhamBoxTotalKunnethIso a b))
  have hrel : IsIso (relativeBoxKunnethMap a b (deRhamDiffOpCochainComplex a)
      (deRhamDiffOpCochainComplex b) 0 0) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _
      ((derivedPushforward (inverseImageBaseProjection (pullback.fst a b ≫ a))).map e.hom)
      ((_ : _ ⥤ _).mapIso e).isIso_hom h
  have hκ := AlgebraicGeometry.FlatKunneth.isIso_globalCupProductCanonical_app S _ _
    (isQuasicoherent_homology_derivedPushforward_leftComplex a)
    (isQuasicoherent_homology_derivedPushforward_leftComplex b)
  have hmap := isIso_globalBoxKunnethMap_of_isIso_relative a b (deRhamDiffOpCochainComplex a)
    (deRhamDiffOpCochainComplex b) 0 0 _ hκ hrel
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hmap
    ((sectionsOverBase (inverseImageBaseProjection (pullback.fst a b ≫ a))).mapIso e).isIso_hom

end DeRham

end Stacks.Cohomology.BoxKunneth

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (a : X ⟶ S)

/-- **Over an affine base an affine absolute diagonal is an affine relative diagonal.** The
absolute diagonal of `X` factors as the diagonal of `a : X ⟶ S` followed by a base change of the
diagonal of `S`. That base change is a monomorphism, hence separated, so affineness of the
composite descends to the first factor. -/
theorem isAffineHom_diagonal_of_isAffine [IsAffine S]
    [IsAffineHom (pullback.diagonal (terminal.from X))] : IsAffineHom (pullback.diagonal a) := by
  have : IsAffineHom (pullback.diagonal (a ≫ terminal.from S)) := by
    rw [show a ≫ terminal.from S = terminal.from X from terminal.hom_ext _ _]
    infer_instance
  rw [pullback.diagonal_comp] at this
  exact IsAffineHom.of_comp _
    ((pullbackDiagonalMapIdIso a a (terminal.from S)).inv ≫ pullback.snd _ _)

/-- A scheme with affine diagonal is quasi-separated, so every morphism out of it is
quasi-separated. -/
theorem quasiSeparated_of_isAffineHom_diagonal_terminal
    [IsAffineHom (pullback.diagonal (terminal.from X))] : QuasiSeparated a := by
  have : QuasiSeparated (terminal.from X) := (quasiSeparated_iff _).2 inferInstance
  have := (quasiSeparatedSpace_iff_quasiSeparated X).2 this
  infer_instance

end AlgebraicGeometry

namespace Stacks.Cohomology.BoxKunneth

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **The de Rham Künneth formula over an affine base, at the hypotheses of [Stacks, Tag 0FMB],
from the relative one.** For `S` affine, `a` and `b` quasi-compact with affine diagonal, the
de Rham Künneth map `RΓ(X, Ω^•_{X/S}) ⊗^𝐋_A RΓ(Y, Ω^•_{Y/S}) ⟶ RΓ(X ×_S Y, Ω^•_{X ×_S Y/S})`
built from the canonical global cup product is an isomorphism as soon as the relative cup product
of [Stacks, Tag 0FMC] is. An affine diagonal makes `a` and `b` quasi-separated, which is what
`isIso_deRhamGlobalKunnethMap_of_isIso_relative` asks. -/
theorem isIso_deRhamGlobalKunnethMap_canonical_of_isIso_relative [IsAffine S]
    [QuasiCompact a] [QuasiCompact b]
    [IsAffineHom (pullback.diagonal a)] [IsAffineHom (pullback.diagonal b)]
    (h : IsIso (deRhamRelativeKunnethMap a b)) :
    IsIso (deRhamGlobalKunnethMap a b (globalCupProductCanonical S.toRingedSpace)) := by
  have : QuasiSeparated a := (quasiSeparated_iff a).2 inferInstance
  have : QuasiSeparated b := (quasiSeparated_iff b).2 inferInstance
  exact isIso_deRhamGlobalKunnethMap_of_isIso_relative a b h

end Stacks.Cohomology.BoxKunneth
