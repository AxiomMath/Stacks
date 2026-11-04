module

public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTildeComplexes
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TildeStalkKFlat
import all StacksFrontier.Homology.Tor.DerivedExtensionScalars

/-!
# The affine comparison square at the standard model of the derived category

Let `f : R ⟶ S` be a homomorphism of commutative rings. Derived pullback along `Spec f` and
derived extension of scalars are compared by

  `Lf^*(M̃^•) ≅ (S ⊗ᴸ_R M^•)~`,

naturally in `M^• ∈ D(R)`. This is the affine comparison square of [Stacks, Tag 08DW] part (2),
the form in which [Stacks, Tag 06Z0] computes the derived category of an affine scheme, and it
is the geometric input of the affine case of [Stacks, Tag 0DI7].

`CategoryTheory.HasDerivedCategory` is `CategoryTheory.MorphismProperty.HasLocalization`, a
class carrying the localized category and the localization functor as *data*, so
`DerivedCategory C` at two instances is two different types and a functor built at one model is
not a functor at any other. The relative descent development of Tag 0DI7 in
`StacksFrontier/AlgebraicGeometry/Perfect/RelativeDescentDerivedHom.lean` lives at
`CategoryTheory.HasDerivedCategory.standard`, because that is the model at which the composition
isomorphism of [Stacks, Tag 0D5S] and its associativity and unit coherences are available, and
those coherences take no model binder. The affine comparison, on the other hand, is proved in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/AffinePullbackComparison.lean` at the
locally small model of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`. This file proves
it at the standard model, so that the two sides of Tag 0DI7's reduction meet.

## Main definitions

* `AlgebraicGeometry.StandardModel.specDerivedPullback` — derived pullback
  `Lf^* : D(𝒪_{Spec R}) ⥤ D(𝒪_{Spec S})` along `Spec f`, the derived pullback of
  [Stacks, Tag 079W] of the underlying morphism of ringed spaces with the two derived categories
  spelled in the scheme form.
* `AlgebraicGeometry.StandardModel.tildePullbackComplex` and
  `AlgebraicGeometry.StandardModel.extendScalarsTildeComplex` — the two degreewise functors
  `M^• ↦ f^*(M̃^•)` and `M^• ↦ (S ⊗_R M^•)~` from complexes of `R`-modules to
  `D(𝒪_{Spec S})`.
* `AlgebraicGeometry.StandardModel.tildeDerivedPullbackComparison` and
  `AlgebraicGeometry.StandardModel.extendScalarsTildeComparison` — the two comparisons
  exhibiting `Lf^* ∘ L~` and `L~ ∘ L(S ⊗_R -)` as total left derived functors of those.
* `AlgebraicGeometry.StandardModel.affinePullbackComparison` — **the affine comparison square,
  at the standard model.**

## Main results

* `AlgebraicGeometry.StandardModel.isLeftDerivedFunctor_tildeDerivedPullback` and
  `AlgebraicGeometry.StandardModel.isLeftDerivedFunctor_extendScalarsTilde` — both sides of the
  square are total left derived functors of degreewise constructions.
* `AlgebraicGeometry.StandardModel.affinePullbackComparison_fac` — the equation pinning the
  comparison: on every complex it agrees with the ordinary affine-pullback isomorphism of
  [Stacks, Tag 01I9] composed with the two derived-functor comparisons. The comparison is not
  determined by its type alone, so this is part of the statement and not a convenience.

## Implementation notes

*Why the construction is repeated rather than transported.* The alternative is to build an
equivalence `D_loc(𝒪_X) ≌ D_std(𝒪_X)` from `CategoryTheory.Localization.uniq` and carry
`AlgebraicGeometry.affinePullbackComparison` across it. That route is longer and leaves a worse
statement: identifying the equivalence with derived pullback on both sides is itself a
left-derived-functor uniqueness argument, of exactly the difficulty of the construction below,
and three equivalences would then sit permanently in the type of the comparison and in its
pinning equation. Nothing in the construction below is tied to a model.
`CategoryTheory.Functor.mapDerivedCategory`,
`CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars` and
`CochainComplex.DerivedExtensionScalars.isLeftDerivedFunctor_of_isIso_on_kFlat` all take free
model binders, `AlgebraicGeometry.pullbackTildeIso` and `Stacks.TildeStalk.kFlatTilde` mention no
derived category at all, and the K-flat computation of `Lf^*` is available at the standard model
as `Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat`. What
pins `AlgebraicGeometry.affinePullbackComparison` to the locally small model is not its proof but
its imports: `StacksFrontier.AlgebraicGeometry.DerivedTilde.Basic` and
`StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QuasiCoherentPullback` both carry
`StacksFrontier.Homology.DerivedCategory.LocallySmall`, whose `HasDerivedCategory` declarations are
*global* instances, and a global instance beats `attribute [local instance]`. The imports above
are therefore chosen so that `StacksFrontier.Homology.DerivedCategory.LocallySmall` is absent from
the closure, which is the regime `RelativeDescentDerivedHom.lean` itself works in; the local
attribute then fixes the standard model with nothing competing.
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom` is imported for that reason and
not for a declaration: it is the development this file exists to serve, so having it in the
closure is what guarantees that the derived categories here and there are the same ones, and it
puts `Stacks.DerivedPullback.schemeFactorIso` — the composition isomorphism of Tag 0D5S in the
form the relative descent system uses — beside `specDerivedPullback`.

*The two spellings of the derived category of an affine scheme.* Tag 079W is a statement about
ringed spaces, so its derived pullback is typed at
`SheafOfModules (structureSheafRing X.toRingedSpace)`, whereas
`CategoryTheory.Functor.mapDerivedCategory` of `AlgebraicGeometry.tilde.functor` is typed at
`(Spec R).Modules`. The two are equal, including their `Category` instances, but
`AlgebraicGeometry.Scheme.Modules` is not reducible, so the equality is invisible to instance
synthesis and to `rw`. `specDerivedPullback` ascribes the scheme spelling once, exactly as
`Stacks.Duality.derivedPullback` does at the locally small model; without it the composite
`(tilde.functor R).mapDerivedCategory ⋙ Lf^*` still elaborates but is type-correct only at
default transparency, and `NatTrans.comp_app` can no longer be rewritten inside it.

*Which presentation of the localisation.* `CategoryTheory.Functor.leftDerivedNatIso` needs both
functors to be left derived along one localisation, and the two sides arrive at different ones:
derived extension of scalars is left derived along `(DerivedCategory.Q, quasiIso)` while `Lf^*`
is left derived along `(DerivedCategory.Qh, quasiIso)`. Everything is therefore brought to the
first presentation; `derivedPullbackComplexComparison` performs that passage for `Lf^*` and
`Stacks.DerivedPullback.mapHomologicalComplexCompFactors` supplies the factorisations through the
homotopy category which `isLeftDerivedFunctor_of_isIso_on_kFlat` asks for.

*What is shared with the locally small development and what is not.* Of the ingredients above,
exactly those mentioning no derived category are single declarations serving both files:
`Stacks.DerivedPullback.mapHomologicalComplexCompFactors`,
`AlgebraicGeometry.tildePullbackComplexIso` and `AlgebraicGeometry.extendScalarsSpec_additive`,
all three in `StacksFrontier/AlgebraicGeometry/Scheme/QuasiCoherent/AffineTildeComplexes.lean`,
whose imports are confined so that `StacksFrontier.Homology.DerivedCategory.LocallySmall` stays out
of its closure and it can be imported here. Everything else is genuinely two declarations and not
a duplicated one: `HasDerivedCategory` carries the localized category as data, so `DerivedCategory
(Spec S).Modules` is a different type at the two models — the morphisms are in `Type u` at the
locally small model and in `Type (u + 1)` here — and a declaration whose statement mentions it
says nothing about the other model.

*Three spellings of one category.* The degreewise pullback is written
`AlgebraicGeometry.Scheme.Modules.pullback (Spec.map f)` and not
`RingedSpaceModuleAdjunction.modulePullback (Spec.map f).toLRSHom.toShHom`. The two are equal by
`rfl`, including their additivity instances, but only at the first spelling does synthesis find
`CategoryTheory.Functor.Additive` for the composite `tilde.functor R ⋙ f^*`. The crossing to the
ringed-space spelling happens once, inside `tildeDerivedPullbackComparison`.

*What is not proved here.* The comparison is natural in the complex and canonically normalised,
but nothing below asserts its compatibility with composition of ring maps: for `f : R ⟶ S` and
`g : S ⟶ T`, that `affinePullbackComparison` for `f ≫ g` is the composite of those for `f` and
for `g`, modulo the composition isomorphism of Tag 0D5S and a composition isomorphism for derived
extension of scalars. By uniqueness of a morphism into a total left derived functor
(`CategoryTheory.Functor.leftDerived_ext`) that cocycle identity reduces to two inputs, and both
of them are available. The composition compatibility of Tag 01I9, relating
`AlgebraicGeometry.pullbackTildeIso` for `f ≫ g` to those for `f` and `g` through
`AlgebraicGeometry.Scheme.Modules.pullbackComp` and `ModuleCat.extendScalarsComp`, is
`AlgebraicGeometry.pullbackTildeIso_comp` of
`StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTildeComposition`, with pointwise forms
in `StacksFrontier.AlgebraicGeometry.PullbackTildeComp`. The isomorphism
`(S ⊗ᴸ_R -) ⋙ (T ⊗ᴸ_S -) ≅ (T ⊗ᴸ_R -)` is
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp` of
`StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp`, with its own cocycle
`totalDerivedExtensionScalarsComp_assoc`. Neither involves a derived category at the first input
or a choice of model at the second; both are independent of the question this file settles.

*Why no Stacks attribute is attached.* Part (1) of Tag 08DW, the preservation of quasi-coherence
of cohomology by derived pullback, is not proved anywhere in the library, and the audit scanner
matches the bare four characters of a tag, so an attribute here would report the whole tag
formalized. Part (2) is already carried at the locally small model by
`AlgebraicGeometry.affinePullbackComparison`; this file is the same mathematics at a second
model, not a further part of the tag's statement.

## References

* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open CochainComplex.DerivedExtensionScalars
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPullbackComparison)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.StandardModel

open Stacks.DerivedPullback (mapHomologicalComplexCompFactors)

/-! ### The repackaged derived-pullback comparison -/

/-- The comparison from the derived pullback of a morphism of ringed spaces to degreewise
pullback, read as a natural transformation out of `DerivedCategory.Q` instead of out of
`DerivedCategory.Qh`: the presentation of the localisation that derived extension of scalars
uses. -/
def derivedPullbackComplexComparison {X Y : RingedSpace.{u, u}} (g : X ⟶ Y) :
    DerivedCategory.Q ⋙ derivedPullback g ⟶
      (modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing Y))).inv
      (derivedPullback g) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (derivedPullbackComparison g) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight ((modulePullback g).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).hom DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).hom

/-- The repackaged comparison is invertible on a K-flat complex: the four morphisms it is
composed with besides the derived-pullback comparison of [Stacks, Tag 06YJ] are components of
isomorphisms. -/
theorem isIso_derivedPullbackComplexComparison_app_of_kFlat
    {X Y : RingedSpace.{u, u}} (g : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y K) :
    IsIso ((derivedPullbackComplexComparison g).app K) := by
  have := Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
    g K hK
  dsimp only [derivedPullbackComplexComparison]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-! ### The two degreewise functors on complexes of modules over the source ring -/

/-- The unbounded derived pullback `Lf^* : D(𝒪_{Spec R}) ⥤ D(𝒪_{Spec S})` along the morphism of
affine schemes induced by `f : R ⟶ S`: the derived pullback of [Stacks, Tag 079W] of the
underlying morphism of ringed spaces, with the two derived categories spelled in the scheme
form. -/
abbrev specDerivedPullback {R S : CommRingCat.{u}} (f : R ⟶ S) :
    DerivedCategory (Spec R).Modules ⥤ DerivedCategory (Spec S).Modules :=
  derivedPullback (Spec.map f).toLRSHom.toShHom

variable (R S : CommRingCat.{u}) (f : R ⟶ S)

-- The priority matters, for the reason given at the same line of
-- `StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/AffinePullbackComparison.lean`.
attribute [local instance 10000] AlgebraicGeometry.extendScalarsSpec_additive

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

/-- `AlgebraicGeometry.tildePullbackComplexIso` after localisation: the two degreewise functors
into
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
    DerivedCategory.Q ⋙ ((tilde.functor R).mapDerivedCategory ⋙ specDerivedPullback f) ≅
      (tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Q ⋙ specDerivedPullback f) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (tilde.functor R).mapDerivedCategoryFactors
      (specDerivedPullback f) ≪≫
    Functor.associator _ _ _

/-- The comparison from `Lf^* ∘ L~` to the degreewise `M^• ↦ f^*(M̃^•)`. -/
def tildeDerivedPullbackComparison :
    DerivedCategory.Q ⋙ ((tilde.functor R).mapDerivedCategory ⋙ specDerivedPullback f) ⟶
      tildePullbackComplex R S f :=
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

/-- A comparison out of `Q ⋙ F` into a composite of two degreewise functors followed by
localisation, invertible on K-flat complexes, makes `F` the total left derived functor. -/
private theorem isLeftDerivedFunctor_comp_of_isIso_on_kFlat {B : Type*} [Category B]
    [Preadditive B] (G : ModuleCat.{u} R ⥤ B) [G.Additive]
    (G' : B ⥤ (Spec S).Modules) [G'.Additive]
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (Spec S).Modules)
    (β : DerivedCategory.Q ⋙ F ⟶ G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      G'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (hβ : ∀ K : CochainComplex (ModuleCat.{u} R) ℤ, CochainComplex.KFlat.{u, u} K →
      IsIso (β.app K)) :
    F.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  isLeftDerivedFunctor_of_isIso_on_kFlat _
    (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      G'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (mapHomologicalComplexCompFactors _ _ _
      (mapHomologicalComplexCompFactors _ _ _
        (DerivedCategory.quotientCompQhIso (Spec S).Modules))) _ _ hβ

/-- **`L~ ∘ L(S ⊗_R -)` is the total left derived functor of `M^• ↦ (S ⊗_R M^•)~`.** A K-flat
complex computes derived extension of scalars, and derived sheafification preserves
isomorphisms. -/
theorem isLeftDerivedFunctor_extendScalarsTilde :
    ((totalDerivedExtensionScalars.{u, u, u} f.hom).functor ⋙
        (tilde.functor S).mapDerivedCategory).IsLeftDerivedFunctor
      (extendScalarsTildeComparison R S f)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  refine isLeftDerivedFunctor_comp_of_isIso_on_kFlat R S _ _ _ _ (fun K hK => ?_)
  have := (totalDerivedExtensionScalars.{u, u, u} f.hom).comparison_isIso_of_kFlat K hK
  dsimp only [extendScalarsTildeComparison]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  infer_instance

/-- **`Lf^* ∘ L~` is the total left derived functor of `M^• ↦ f^*(M̃^•)`.** Degreewise
sheafification carries a K-flat complex of `R`-modules to a K-flat complex of
`𝒪_{Spec R}`-modules by `Stacks.TildeStalk.kFlatTilde`, and on such a complex the
derived-pullback comparison of [Stacks, Tag 06YJ] is invertible. -/
theorem isLeftDerivedFunctor_tildeDerivedPullback :
    ((tilde.functor R).mapDerivedCategory ⋙ specDerivedPullback f).IsLeftDerivedFunctor
      (tildeDerivedPullbackComparison R S f)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  refine isLeftDerivedFunctor_comp_of_isIso_on_kFlat R S _ _ _ _ (fun K hK => ?_)
  have h1 : IsIso ((tildeDerivedPullbackFactor R S f).hom.app K) :=
    ((tildeDerivedPullbackFactor R S f).app K).isIso_hom
  dsimp only [tildeDerivedPullbackComparison]
  rw [NatTrans.comp_app]
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ h1 ?_
  exact isIso_derivedPullbackComplexComparison_app_of_kFlat
    (Spec.map f).toLRSHom.toShHom _ (Stacks.TildeStalk.kFlatTilde R K hK)

/-! ### The affine comparison square -/

/-- **[Stacks, Tag 08DW] part (2), at the standard model of the derived categories.** For a
homomorphism `f : R ⟶ S` of commutative rings, derived pullback along `Spec f` of a complex of
associated sheaves is naturally isomorphic to derived extension of scalars followed by derived
sheafification,

  `Lf^*(M̃^•) ≅ (S ⊗ᴸ_R M^•)~`.

Both sides are total left derived functors of degreewise constructions which agree by
[Stacks, Tag 01I9], so this is the uniqueness of the total left derived functor. -/
def affinePullbackComparison :
    (tilde.functor R).mapDerivedCategory ⋙ specDerivedPullback f ≅
      (totalDerivedExtensionScalars.{u, u, u} f.hom).functor ⋙
        (tilde.functor S).mapDerivedCategory :=
  have := isLeftDerivedFunctor_extendScalarsTilde R S f
  have := isLeftDerivedFunctor_tildeDerivedPullback R S f
  Functor.leftDerivedNatIso _ _ (tildeDerivedPullbackComparison R S f)
    (extendScalarsTildeComparison R S f)
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (tildePullbackComplexCompQIso R S f)

/-- **[Stacks, Tag 08DW] part (2): the canonical normalisation.** On every complex of `R`-modules
the affine comparison is pinned by the two derived-functor comparisons and the ordinary
affine-pullback isomorphism of [Stacks, Tag 01I9]. The type of `affinePullbackComparison` alone
would not distinguish it from its negative, so this equation is part of the statement. -/
theorem affinePullbackComparison_fac (M : CochainComplex (ModuleCat.{u} R) ℤ) :
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

end AlgebraicGeometry.StandardModel

end
