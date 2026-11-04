module

public import StacksFrontier.AlgebraicGeometry.DerivedTilde.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QuasiCoherentPullback
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTildeComplexes
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TildeStalkKFlat
import all StacksFrontier.Homology.Tor.DerivedExtensionScalars

/-!
# The affine comparison square for derived pullback and derived sheafification

Let `f : R ⟶ S` be a homomorphism of commutative rings. Derived pullback along `Spec f` and
derived extension of scalars are compared by

  `Lf^*(M̃^•) ≅ (S ⊗ᴸ_R M^•)~`,

naturally in `M^• ∈ D(R)`. This is the affine comparison square of [Stacks, Tag 08DW] part (2),
and it is the one step of that tag which does not reduce to the quasi-coherence of the
cohomology of `Lf^*` — on the contrary, it is what the source uses to prove the affine case of
that quasi-coherence.

Both sides are total left derived functors of degreewise constructions on complexes of
`R`-modules: `L~ ∘ L(S ⊗_R -)` of `M^• ↦ (S ⊗_R M^•)~`, and `Lf^* ∘ L~` of `M^• ↦ f^*(M̃^•)`.
Degreewise the two agree by [Stacks, Tag 01I9], which is already available as
`AlgebraicGeometry.pullbackTildeIso`, so the uniqueness of total left derived functors supplies
the comparison together with the equation pinning it.

## Why no Stacks attribute is attached

Tag 08DW has three declarations across two parts: part (1) is preservation of quasi-coherence of
cohomology by derived pullback, and part (2) is the affine comparison square together with its
canonical normalisation. This file proves **part (2) only, and unconditionally** — its input
`AlgebraicGeometry.KFlatTilde R` is proved in
`StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TildeStalkKFlat` as
`Stacks.TildeStalk.kFlatTilde`, so `isLeftDerivedFunctor_tildeDerivedPullback`,
`affinePullbackComparison` and `affinePullbackComparison_fac` take no such hypothesis.

Part (1) remains open, so the tag is not covered, and no attribute is attached here: a tag
attribute records the whole tag, including part (1).

How `KFlatTilde` is obtained, because the shape generalises: it is **not** a
localization computation. `tilde` is a left adjoint and so is the stalk functor, so the
identification of the stalk of `M̃` with `𝒪_{Spec R,x} ⊗_R M` is uniqueness of left adjoints
applied to a composite of two adjunctions that already existed, and nothing is ever computed
about `tilde` itself.

## Main definitions

* `Stacks.DerivedPullback.derivedPullbackComplexComparison` — the comparison
  `Lf^*(Q(K^•)) ⟶ Q(f^*K^•)`, read as a natural transformation out of `DerivedCategory.Q`
  rather than out of `DerivedCategory.Qh`.
* `AlgebraicGeometry.tildePullbackComplex` and
  `AlgebraicGeometry.extendScalarsTildeComplex` — the two degreewise functors
  `CochainComplex (ModuleCat R) ℤ ⥤ D(𝒪_{Spec S})`.
* `AlgebraicGeometry.tildeDerivedPullbackComparison` and
  `AlgebraicGeometry.extendScalarsTildeComparison` — the two comparisons exhibiting
  `Lf^* ∘ L~` and `L~ ∘ L(S ⊗_R -)` as total left derived functors of those.
* `AlgebraicGeometry.affinePullbackComparison` — **the affine comparison square.**

## Main results

* `AlgebraicGeometry.isLeftDerivedFunctor_extendScalarsTilde` and
  `AlgebraicGeometry.isLeftDerivedFunctor_tildeDerivedPullback` — both sides are total left
  derived functors.
* `AlgebraicGeometry.affinePullbackComparison_fac` — the equation pinning the comparison: on
  every complex it agrees with the ordinary affine-pullback isomorphism of Tag 01I9 composed
  with the two derived-functor comparisons. The comparison is not determined by its type alone,
  so this is part of the statement and not a convenience.

## Implementation notes

*The model of the derived categories.* The affine results are at the locally small model, as
`StacksFrontier/AlgebraicGeometry/DerivedTilde/Basic.lean` and
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/QuasiCoherentPullback.lean` are:
`ModuleCat.hasDerivedCategory` on the source and
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` on the target. No declaration here
mentions `CategoryTheory.HasDerivedCategory.standard`. That pin is forced rather than chosen —
`Stacks.Duality.derivedPullback` is itself pinned there, for the reason given in its file, and
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` takes a free model binder
which then resolves to `ModuleCat.hasDerivedCategory`.

*Where the K-flat computation of `Lf^*` comes from.*
`Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat` carries the
two model binders itself, so it applies at the locally small model used here and is used
directly. Every ingredient of its five-line proof
(`Stacks.Cohomology.KFlatDerivedPullback.hasResolutions_isKFlat`,
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackInvertsQuasiIso_isKFlat`,
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` and its comparison) is stated
at a free model, which is what lets it be.

*Which presentation of the localisation.* `Functor.leftDerivedNatIso` needs both functors to be
left derived along one localisation, and the two sides arrive at different ones:
`totalDerivedExtensionScalars` is left derived along
`(DerivedCategory.Q, HomologicalComplex.quasiIso)`, while `Lf^*` is left derived along
`(DerivedCategory.Qh, HomotopyCategory.quasiIso)`. Everything here is therefore brought to the
first presentation, and the passage between them is
`CochainComplex.DerivedExtensionScalars.isLeftDerivedFunctor_of_isIso_on_kFlat`, reached by
`import all`: a comparison to a functor on complexes which factors through the homotopy category
and is invertible on K-flat complexes exhibits its functor as a left derived functor along
`DerivedCategory.Q`. `Stacks.DerivedPullback.mapHomologicalComplexCompFactors` produces the
required factorisations.

*What is shared with the standard-model development.* The same comparison square is proved at
`CategoryTheory.HasDerivedCategory.standard` in
`StacksFrontier/AlgebraicGeometry/Perfect/RelativeDescentStandardModel.lean`, which cannot import
this file: the imports here carry `StacksFrontier.Homology.DerivedCategory.LocallySmall`, whose
`HasDerivedCategory` declarations are global instances and would beat that file's
`attribute [local instance]`. Of the ingredients, exactly those mentioning no derived category are
single declarations serving both — `Stacks.DerivedPullback.mapHomologicalComplexCompFactors`,
`AlgebraicGeometry.tildePullbackComplexIso` and `AlgebraicGeometry.extendScalarsSpec_additive`,
all three in `StacksFrontier/AlgebraicGeometry/Scheme/QuasiCoherent/AffineTildeComplexes.lean`, which
both files import. The rest is genuinely two declarations: `DerivedCategory (Spec S).Modules` is a
different type at the two models, with morphisms in `Type u` here and in `Type (u + 1)` there.

*Three spellings of one category.* The degreewise pullback is written
`AlgebraicGeometry.Scheme.Modules.pullback (Spec.map f)` and not
`RingedSpaceModuleAdjunction.modulePullback (Spec.map f).toLRSHom.toShHom`. The two are equal by
`rfl`, including their additivity instances, but only at the first spelling does synthesis find
`Additive` for the composite `tilde.functor R ⋙ f^*`: at the second the middle category is
presented as `SheafOfModules (structureSheafRing (Spec R).toSheafedSpace)` rather than
`(Spec R).Modules` and `CategoryTheory.Functor.instAdditiveComp` is not found. The crossing to the
ringed-space spelling happens once, inside `tildeDerivedPullbackComparison`.

## References

* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
* [Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open CochainComplex.DerivedExtensionScalars

universe w₁ w₂ u

namespace Stacks.DerivedPullback

/-! ### The K-flat computation of `Lf^*`, at an arbitrary model -/

/-- The comparison from the derived pullback to degreewise pullback, read as a natural
transformation out of `DerivedCategory.Q` instead of out of `DerivedCategory.Qh`: the
presentation of the localisation that derived extension of scalars uses. -/
def derivedPullbackComplexComparison {X Y : RingedSpace.{u, u}} (g : X ⟶ Y)
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))] :
    DerivedCategory.Q ⋙ Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g ⟶
      (modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing Y))).inv
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison g) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight ((modulePullback g).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).hom DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).hom

/-- The degreewise comparison is invertible on a K-flat complex: the four morphisms it is
composed with besides `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison`
are components of isomorphisms. -/
theorem isIso_derivedPullbackComplexComparison_app_of_kFlat
    {X Y : RingedSpace.{u, u}} (g : X ⟶ Y)
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))]
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y K) :
    IsIso ((derivedPullbackComplexComparison g).app K) := by
  have := Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat g
    K hK
  dsimp only [derivedPullbackComplexComparison]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

end Stacks.DerivedPullback

namespace AlgebraicGeometry

open Stacks.DerivedPullback

/-! ### The two degreewise functors on complexes of modules over the source ring -/

variable (R S : CommRingCat.{u}) (f : R ⟶ S)

-- The priority matters: this is a `local instance` of
-- `StacksFrontier/AlgebraicGeometry/Scheme/QuasiCoherent/AffineTildeComplexes.lean`, so without it
-- the many other `(ModuleCat.extendScalars _).Additive` instances in this file's import closure,
-- all declared later, outrank it and are chosen instead.
attribute [local instance 10000] extendScalarsSpec_additive

/-- `M^• ↦ f^*(M̃^•)`, degreewise, followed by localisation. -/
abbrev tildePullbackComplex :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ DerivedCategory (Spec S).Modules :=
  (tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    (Scheme.Modules.pullback (Spec.map f)).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

/-- `M^• ↦ (S ⊗_R M^•)~`, degreewise, followed by localisation. -/
abbrev extendScalarsTildeComplex :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ DerivedCategory (Spec S).Modules :=
  (ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    (tilde.functor S).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

/-- `tildePullbackComplexIso` after localisation: the two degreewise functors into
`D(𝒪_{Spec S})` agree. -/
def tildePullbackComplexCompQIso :
    tildePullbackComplex R S f ≅ extendScalarsTildeComplex R S f :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (tildePullbackComplexIso R S f) DerivedCategory.Q ≪≫
    Functor.associator _ _ _

/-! ### The two comparisons out of the localisation -/

/-- Derived sheafification followed by derived pullback, read as degreewise sheafification
followed by `Q ⋙ Lf^*`. -/
def tildeDerivedPullbackFactor :
    DerivedCategory.Q ⋙ ((tilde.functor R).mapDerivedCategory ⋙
        Stacks.Duality.derivedPullback (Spec.map f)) ≅
      (tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Q ⋙ Stacks.Duality.derivedPullback (Spec.map f)) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (tilde.functor R).mapDerivedCategoryFactors
      (Stacks.Duality.derivedPullback (Spec.map f)) ≪≫
    Functor.associator _ _ _

/-- The comparison from `Lf^* ∘ L~` to the degreewise `M^• ↦ f^*(M̃^•)`. -/
def tildeDerivedPullbackComparison :
    DerivedCategory.Q ⋙ ((tilde.functor R).mapDerivedCategory ⋙
        Stacks.Duality.derivedPullback (Spec.map f)) ⟶ tildePullbackComplex R S f :=
  (tildeDerivedPullbackFactor R S f).hom ≫
    Functor.whiskerLeft ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ))
      (derivedPullbackComplexComparison (Spec.map f).toLRSHom.toShHom)

/-- Degreewise extension of scalars followed by derived sheafification is the degreewise
`M^• ↦ (S ⊗_R M^•)~`. -/
def extendScalarsTildeFactor :
    extensionOfScalarsComplexGeneral.{u, u, u} f.hom ⋙
        (tilde.functor S).mapDerivedCategory ≅ extendScalarsTildeComplex R S f :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex
      (ComplexShape.up ℤ)) (tilde.functor S).mapDerivedCategoryFactors

/-- The comparison from `L~ ∘ L(S ⊗_R -)` to the degreewise `M^• ↦ (S ⊗_R M^•)~`. -/
def extendScalarsTildeComparison :
    DerivedCategory.Q ⋙ ((totalDerivedExtensionScalars.{u, u, u} f.hom).functor ⋙
        (tilde.functor S).mapDerivedCategory) ⟶ extendScalarsTildeComplex R S f :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (totalDerivedExtensionScalars.{u, u, u} f.hom).comparison
      (tilde.functor S).mapDerivedCategory ≫
    (extendScalarsTildeFactor R S f).hom

/-! ### Both sides are total left derived functors -/

/-- **Degreewise sheafification carries K-flat complexes to K-flat complexes.** This is the one
input of the affine comparison below beyond the derived-functor formalism; it is proved as
`Stacks.TildeStalk.kFlatTilde`, see the discussion at the head of this file. -/
abbrev KFlatTilde (R : CommRingCat.{u}) : Prop :=
  ∀ K : CochainComplex (ModuleCat.{u} R) ℤ, CochainComplex.KFlat.{u, u} K →
    Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex (Spec R).toRingedSpace
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)

/-- **`L~ ∘ L(S ⊗_R -)` is the total left derived functor of `M^• ↦ (S ⊗_R M^•)~`.** A K-flat
complex computes derived extension of scalars, and derived sheafification preserves
isomorphisms. -/
theorem isLeftDerivedFunctor_extendScalarsTilde :
    ((totalDerivedExtensionScalars.{u, u, u} f.hom).functor ⋙
        (tilde.functor S).mapDerivedCategory).IsLeftDerivedFunctor
      (extendScalarsTildeComparison R S f)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  refine isLeftDerivedFunctor_of_isIso_on_kFlat _
    ((ModuleCat.extendScalars.{u, u, u} f.hom).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      (tilde.functor S).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (mapHomologicalComplexCompFactors _ _ _
      (mapHomologicalComplexCompFactors _ _ _
        (DerivedCategory.quotientCompQhIso (Spec S).Modules))) _ _ (fun K hK => ?_)
  have := (totalDerivedExtensionScalars.{u, u, u} f.hom).comparison_isIso_of_kFlat K hK
  dsimp only [extendScalarsTildeComparison]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  infer_instance

/-- **`Lf^* ∘ L~` is the total left derived functor of `M^• ↦ f^*(M̃^•)`.** Degreewise
sheafification preserves K-flatness (`Stacks.TildeStalk.kFlatTilde`), so on `M̃^•` with `M^•`
K-flat the derived-pullback comparison is invertible, by
`Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat`. -/
theorem isLeftDerivedFunctor_tildeDerivedPullback :
    ((tilde.functor R).mapDerivedCategory ⋙
        Stacks.Duality.derivedPullback (Spec.map f)).IsLeftDerivedFunctor
      (tildeDerivedPullbackComparison R S f)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  refine isLeftDerivedFunctor_of_isIso_on_kFlat _
    ((tilde.functor R).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      (Scheme.Modules.pullback (Spec.map f)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh)
    (mapHomologicalComplexCompFactors _ _ _
      (mapHomologicalComplexCompFactors _ _ _
        (DerivedCategory.quotientCompQhIso (Spec S).Modules))) _ _ (fun K hK => ?_)
  have h1 : IsIso ((tildeDerivedPullbackFactor R S f).hom.app K) :=
    ((tildeDerivedPullbackFactor R S f).app K).isIso_hom
  dsimp only [tildeDerivedPullbackComparison]
  rw [NatTrans.comp_app]
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ h1 ?_
  exact isIso_derivedPullbackComplexComparison_app_of_kFlat
    (Spec.map f).toLRSHom.toShHom _ (Stacks.TildeStalk.kFlatTilde R K hK)

/-! ### The affine comparison square -/

/-- **Stacks 08DW, part (2): the affine comparison square.** For a homomorphism `f : R ⟶ S` of
commutative rings, derived pullback along `Spec f` of a complex of associated sheaves is
naturally isomorphic to derived extension of scalars followed by derived sheafification,

  `Lf^*(M̃^•) ≅ (S ⊗ᴸ_R M^•)~`.

Both sides are total left derived functors of degreewise constructions which agree by
Stacks 01I9, so this is the uniqueness of the total left derived functor. -/
def affinePullbackComparison :
    (tilde.functor R).mapDerivedCategory ⋙ Stacks.Duality.derivedPullback (Spec.map f) ≅
      (totalDerivedExtensionScalars.{u, u, u} f.hom).functor ⋙
        (tilde.functor S).mapDerivedCategory :=
  have := isLeftDerivedFunctor_extendScalarsTilde R S f
  have := isLeftDerivedFunctor_tildeDerivedPullback R S f
  Functor.leftDerivedNatIso _ _ (tildeDerivedPullbackComparison R S f)
    (extendScalarsTildeComparison R S f)
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (tildePullbackComplexCompQIso R S f)

/-- **Stacks 08DW, part (2): the canonical normalisation.** On every complex of `R`-modules the
affine comparison is pinned by the two derived-functor comparisons and the ordinary
affine-pullback isomorphism of Stacks 01I9. The type of `affinePullbackComparison` alone would
not distinguish it from its negative, so this equation is part of the statement. -/
theorem affinePullbackComparison_fac
    (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (affinePullbackComparison R S f).hom.app (DerivedCategory.Q.obj M) ≫
        (extendScalarsTildeComparison R S f).app M =
      (tildeDerivedPullbackComparison R S f).app M ≫
        (tildePullbackComplexCompQIso R S f).hom.app M := by
  have := isLeftDerivedFunctor_extendScalarsTilde R S f
  have := isLeftDerivedFunctor_tildeDerivedPullback R S f
  exact Functor.leftDerivedNatTrans_app _ _ (tildeDerivedPullbackComparison R S f)
    (extendScalarsTildeComparison R S f)
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (tildePullbackComplexCompQIso R S f).hom M

end AlgebraicGeometry

end
