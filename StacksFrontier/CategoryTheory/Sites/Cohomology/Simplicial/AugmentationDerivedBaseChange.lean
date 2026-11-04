module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CoefficientChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackAsATriangulatedFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.AugmentedLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.ProjectionDerivedLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModulesAbelian

/-!
# Derived extension of scalars for simplicial modules

Let `C` be a site and let `A_• ⟶ B_•` be a homomorphism of simplicial sheaves of rings on `C`.
The untagged prose preceding [Stacks, Tag 09D2] uses the derived extension of scalars

`- ⊗^𝐋_{A_•} B_• : D(A_•) ⟶ D(B_•)`

between the derived categories of simplicial modules of [Stacks, Tag 09D1], and
[Stacks, Tag 09D3] uses its instance at an augmentation `ε : A_• ⟶ O` to build derived lower
shriek `Lπ_! : D(A_•) ⟶ D(O)` as the composite of `- ⊗^𝐋_{A_•} O` with the functor
`Lπ_! : D(π^{-1}O) ⟶ D(O)` of [Stacks, Tag 09CY]. This file constructs that first factor, which
is the `base` parameter of `Stacks.SimplicialModules.augmentedLowerShriek`.

Simplicial `A_•`-modules are sheaves of modules over the sheaf of rings on `Δ × C` associated to
`A_•` (`Stacks.SimplicialModules.ringSheaf`), so extension of scalars along `A_• ⟶ B_•` is
extension of scalars along the induced map of sheaves of rings on `Δ × C`; that is a change of
coefficient rings on a fixed site, hence the pullback along a morphism of ringed topoi whose
underlying morphism of sites is the identity, and its derived functor is the derived pullback of
[Stacks, Tag 06YY]. In this development that derived pullback exists, commutes with the shift and
is exact for *every* morphism of ringed topoi presented by a morphism of sites
(`Stacks.Cohomology.DerivedPullbackOnRingedTopoi`), and the identity functor of a site is a
morphism of sites, so nothing is assumed here beyond the data `A_• ⟶ B_•`.

## Main definitions

* `Stacks.SimplicialModules.projectionTopology`: the topology on `Δ × C` inherited from
  `(C, J)` along the second projection, in which [Stacks, Tag 09D1] takes the sheaf condition.
* `Stacks.SimplicialModules.simplicialCommRingSheaf`: the sheaf of commutative rings on `Δ × C`
  associated to a simplicial sheaf of commutative rings, with its functoriality
  `simplicialCommRingSheafMap`. This is `Stacks.SimplicialModules.ringSheaf` before commutativity
  is forgotten.
* `Stacks.SimplicialModules.projectionCommRing` and
  `Stacks.SimplicialModules.projectionRingSheaf`: `π^{-1}O` on `Δ × C`, as a sheaf of commutative
  rings and as a sheaf of rings.
* `Stacks.SimplicialModules.derivedSimplicialBaseChange`: **`- ⊗^𝐋_{A_•} B_•`**, derived
  extension of scalars along a homomorphism of simplicial sheaves of commutative rings.
* `Stacks.SimplicialModules.derivedAugmentationBaseChange`: **the `base` parameter of
  [Stacks, Tag 09D3]**, `- ⊗^𝐋_{A_•} O : D(A_•) ⟶ D(π^{-1}O)`, with its target written as
  sheaves of modules over `π^{-1}O` so that it composes with the `Lπ_!` of [Stacks, Tag 09CY].
* `Stacks.SimplicialModules.derivedAugmentationBaseChangeSimplicial`: the same functor with its
  target written as simplicial modules over the constant simplicial sheaf of rings `O`, which is
  the shape `Stacks.SimplicialModules.augmentedLowerShriek` asks for.
* `Stacks.SimplicialModules.augmentationRingMap`: an augmentation of simplicial sheaves of
  commutative rings, read as an augmentation of simplicial sheaves of rings.

## Main results

* `Stacks.SimplicialModules.isContinuous_prodSnd_inheritedTopology`: the projection
  `π : Δ × C ⥤ C` is continuous for the inherited topology, with no hypothesis on `C`. This is
  what makes `π^{-1}` available on sheaves.
* `derivedSimplicialBaseChange_commShift`, `derivedSimplicialBaseChange_isTriangulated` and the
  corresponding instances for the two augmentation functors: each of these functors commutes with
  the shift and is an exact functor of triangulated categories. They are instances, so the
  exactness clause of [Stacks, Tag 09D3] is available at the constructed `base` by instance
  search; the two `example`s at the end of the file record that.

## Implementation notes

**Commutative rings.** `A_•` and `O` are simplicial sheaves of *commutative* rings, read as
simplicial sheaves of rings through `sheafCompose _ (forget₂ CommRingCat RingCat)`. This is the
Stacks Project's standing convention for a sheaf of rings on a site — it is the convention under
which this development formalises a ringed site and a ringed topos
(`AlgebraicGeometry.RingedSite`, `AlgebraicGeometry.RingedTopos`, tagged 03AD and 01D3), and the
one the `Lπ_!` of [Stacks, Tag 09CY] is built under. It is not a weakening introduced here: the
flatness theory that the derived pullback of [Stacks, Tag 06YY] rests on is stated for
`CommRingCat`-valued structure sheaves throughout.

**Not the enough-projectives route.** `Stacks.CategoryHomology.totalDerivedLeftAdjoint`, which is
how the chaotic-site analogue
`Stacks.ChaoticSite.derivedCoefficientExtension` is built, needs `EnoughProjectives` in the
source; `EnoughProjectives (SheafOfModules _)` is false in general and is not available for
simplicial modules, whose sheaf condition is taken for the inherited topology on `Δ × C` and not
for a chaotic one. The route here needs no projectives: it is the derived pullback of
[Stacks, Tag 06YY], whose existence is proved in this development from K-flat resolutions.

**Spelling discipline.** `Abelian` and `HasDerivedCategory` are arguments of
`DerivedCategory`, so two definitionally equal but differently *spelled* sheaves of rings give
two definitionally equal but differently spelled derived categories, and instance search — which
unfolds only reducible definitions — then fails to see that a `CommShift` or `IsTriangulated`
instance for one applies to the other, even though the functors compose. Every intermediate
category below is therefore written in exactly one spelling: the sheaves of modules over
`(Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.Cohomology.ringedTopos _ _).O)`, which is what
`Stacks.Cohomology.derivedCoefficientChange` is stated at, and `projectionRingSheaf` for the
target, which is what `π^{-1}O` unfolds to on the `Lπ_!` side. `equivSheafOfModulesPinned` and
`constantEquivSheafOfModulesPinned` are `Stacks.SimplicialModules.equivSheafOfModules` with the
target ascribed to the first of these spellings; the ascription is the whole content of those two
declarations.

**Transport across the equivalence of module categories is available.** Simplicial modules are a
full subcategory of presheaves of modules and sheaves of modules are Mathlib's `SheafOfModules`;
these are equivalent by `Stacks.SimplicialModules.equivSheafOfModules` and not equal.
`CategoryTheory.Functor.mapDerivedCategory` transports a functor across such an equivalence —
an equivalence of abelian categories is exact, and `mapDerivedCategory` of an exact functor
carries `CommShift ℤ` and `IsTriangulated` instances — which is what
`derivedAugmentationBaseChangeSimplicial` uses, and why both the `SheafOfModules` and the
`SimplicialModule` spelling of the target are provided here.

**Universes.** The site, its morphisms, the sections of the sheaves of rings and the sections of
the modules all lie in one universe `u`, and `C` is small. That is forced by
`Stacks.Cohomology.derivedCoefficientChange`, which is stated at
`AlgebraicGeometry.RingedTopos.{u, u, u}` because the derived pullback of ringed topoi is;
`Δ` contributes nothing, `SimplexCategory` being a `Type` with `Type`-valued homs.

## References

* [Stacks Project, Tag 09D1](https://stacks.math.columbia.edu/tag/09D1), simplicial modules.
* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2), whose preceding prose
  introduces `- ⊗^𝐋_{A_•} B_•`.
* [Stacks Project, Tag 09D3](https://stacks.math.columbia.edu/tag/09D3), the functor whose first
  factor this is.
* [Stacks Project, Tag 09CY](https://stacks.math.columbia.edu/tag/09CY), the second factor.
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY), the derived pullback.
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ), extension of scalars.
* [Stacks Project, Tag 06NV](https://stacks.math.columbia.edu/tag/06NV), the inherited site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.SimplicialModules

attribute [local instance] HasDerivedCategory.standard

section

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-! ### The site `Δ × C` and the sheaves of rings on it -/


/-- **The projection `π : Δ × C ⥤ C` is continuous** from the topology `Δ × C` inherits from
`(C, J)` to `J`, with no hypothesis on `C`.

Continuity is the statement that the restriction along `π` of a sheaf of types on `C` is a sheaf
for the inherited topology, and being a sheaf on `Δ × C` is a coordinatewise condition
(`CategoryTheory.Presieve.isSheafFor_functorPullback_snd`): in the coordinate `n` the restriction
is the sheaf itself. -/
instance isContinuous_prodSnd_inheritedTopology :
    (CategoryTheory.Prod.snd SimplexCategory C).IsContinuous
      (projectionTopology C J) J where
  op_comp_isSheaf_of_types G := by
    refine Presieve.isSheaf_inheritedTopology _ J _ fun X S hS => ?_
    refine Presieve.isSheafFor_functorPullback_snd _ X S ?_
    exact ((isSheaf_iff_isSheaf_of_type J G.obj).1 G.property) S hS

/-- `π^{-1}O`, the restriction along the projection of a sheaf of commutative rings on `C`. -/
abbrev projectionCommRing (O : Sheaf J CommRingCat.{u}) :
    Sheaf (projectionTopology C J) CommRingCat.{u} :=
  ((CategoryTheory.Prod.snd SimplexCategory C).sheafPushforwardContinuous CommRingCat.{u}
    (projectionTopology C J) J).obj O

/-- `π^{-1}O` read as a sheaf of (not necessarily commutative) rings on `Δ × C`. This is the
sheaf of rings over which the `Lπ_!` of [Stacks, Tag 09CY] takes its source modules. -/
abbrev projectionRingSheaf (O : Sheaf J CommRingCat.{u}) :
    Sheaf (projectionTopology C J) RingCat.{u} :=
  ((CategoryTheory.Prod.snd SimplexCategory C).sheafPushforwardContinuous RingCat.{u}
    (projectionTopology C J) J).obj (Stacks.SheafOfModules.Tensor.ringSheaf O)

/-- The presheaf of commutative rings on `Δ × C` obtained by uncurrying a simplicial sheaf of
commutative rings. Composing it with `forget₂ CommRingCat RingCat` is
`Stacks.SimplicialModules.associatedRingPresheaf` of the underlying simplicial sheaf of rings. -/
abbrev associatedCommRingPresheaf (A : SimplicialObject (Sheaf J CommRingCat.{u})) :
    (SimplexCategory × C)ᵒᵖ ⥤ CommRingCat.{u} :=
  (prodOpEquiv SimplexCategory (D := C)).functor ⋙
    Functor.uncurry.obj (A ⋙ sheafToPresheaf J CommRingCat.{u})

/-- The presheaf of commutative rings on `Δ × C` of a simplicial sheaf of commutative rings is a
sheaf for the inherited topology: being a sheaf on `Δ × C` is a coordinatewise condition
(`CategoryTheory.Presheaf.isSheaf_inheritedTopology_prodSnd`) and in the coordinate `n` the
presheaf is the underlying presheaf of `A_n`. -/
theorem isSheaf_associatedCommRingPresheaf (A : SimplicialObject (Sheaf J CommRingCat.{u})) :
    Presheaf.IsSheaf (projectionTopology C J) (associatedCommRingPresheaf J A) := by
  refine Presheaf.isSheaf_inheritedTopology_prodSnd J _ fun n => ?_
  refine (Presheaf.isSheaf_of_iso_iff
    (NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp [Functor.prodSectionSnd]) :
      (Functor.prodSectionSnd n).op ⋙ associatedCommRingPresheaf J A ≅
        (A.obj (op n)).obj)).2 (A.obj (op n)).property

/-- **The sheaf of commutative rings on `Δ × C` associated to a simplicial sheaf of commutative
rings.** This is `Stacks.SimplicialModules.ringSheaf` of [Stacks, Tag 09D1] before commutativity
is forgotten; composing with `forget₂ CommRingCat RingCat` returns that sheaf of rings. -/
def simplicialCommRingSheaf (A : SimplicialObject (Sheaf J CommRingCat.{u})) :
    Sheaf (projectionTopology C J) CommRingCat.{u} :=
  ⟨associatedCommRingPresheaf J A, isSheaf_associatedCommRingPresheaf J A⟩

/-- A homomorphism of simplicial sheaves of commutative rings, read as a map of the associated
sheaves of commutative rings on `Δ × C`. -/
def simplicialCommRingSheafMap {A B : SimplicialObject (Sheaf J CommRingCat.{u})} (f : A ⟶ B) :
    simplicialCommRingSheaf J A ⟶ simplicialCommRingSheaf J B :=
  ⟨Functor.whiskerLeft _ (Functor.uncurry.map
    (Functor.whiskerRight f (sheafToPresheaf J CommRingCat.{u})))⟩

/-- **The sheaf of rings on `Δ × C` of a constant simplicial sheaf of rings is `π^{-1}O`.** Both
are `(n, U) ↦ O(U)`; the two differ only in that the uncurried presheaf inserts the identity
restriction map of the simplicial direction, so the comparison is the identity in each section. -/
def constantSimplicialCommRingIso (O : Sheaf J CommRingCat.{u}) :
    simplicialCommRingSheaf J ((Functor.const SimplexCategoryᵒᵖ).obj O) ≅
      projectionCommRing J O :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro X Y f
      dsimp [simplicialCommRingSheaf, associatedCommRingPresheaf]
      exact (Category.comp_id _).trans (Category.id_comp _).symm))

/-- An augmentation `ε : A_• ⟶ O` of a simplicial sheaf of commutative rings, read as the map of
sheaves of commutative rings `A_• ⟶ π^{-1}O` on `Δ × C` along which scalars are extended. -/
def augmentationCommRingMap {A : SimplicialObject (Sheaf J CommRingCat.{u})}
    {O : Sheaf J CommRingCat.{u}} (ε : A ⟶ (Functor.const SimplexCategoryᵒᵖ).obj O) :
    simplicialCommRingSheaf J A ⟶ projectionCommRing J O :=
  simplicialCommRingSheafMap J ε ≫ (constantSimplicialCommRingIso J O).hom

/-- A simplicial sheaf of commutative rings, read as a simplicial sheaf of rings. Its simplicial
modules are those of [Stacks, Tag 09D1]. -/
abbrev simplicialRingSheaf (A : SimplicialObject (Sheaf J CommRingCat.{u})) :
    SimplicialObject (Sheaf J RingCat.{u}) :=
  A ⋙ sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})

/-- An augmentation of simplicial sheaves of commutative rings, read as an augmentation of
simplicial sheaves of rings in the sense of `Stacks.SimplicialModules.Augmentation`. -/
def augmentationRingMap {A : SimplicialObject (Sheaf J CommRingCat.{u})}
    {O : Sheaf J CommRingCat.{u}} (ε : A ⟶ (Functor.const SimplexCategoryᵒᵖ).obj O) :
    Augmentation J (simplicialRingSheaf J A)
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) :=
  Functor.whiskerRight ε (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u}))

/-! ### `- ⊗^𝐋_{A_•} B_•` -/

attribute [local instance] abelian

/-- `D(A_•)` presented as the derived category of sheaves of modules over the sheaf of rings on
`Δ × C`, at the spelling `Stacks.Cohomology.derivedCoefficientChange` is stated in: this is
`Stacks.SimplicialModules.equivSheafOfModules` with its target ascribed. -/
def equivSheafOfModulesPinned (A : SimplicialObject (Sheaf J CommRingCat.{u})) :
    SimplicialModule.{u, u, u, u} J (simplicialRingSheaf J A) ≌
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.Cohomology.ringedTopos (projectionTopology C J)
          (simplicialCommRingSheaf J A)).O) :=
  equivSheafOfModules.{u, u, u, u} J (simplicialRingSheaf J A)

/-- The functor of `equivSheafOfModulesPinned` is additive. -/
instance equivSheafOfModulesPinned_functor_additive
    (A : SimplicialObject (Sheaf J CommRingCat.{u})) :
    (equivSheafOfModulesPinned J A).functor.Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryProducts
    (equivSheafOfModulesPinned J A).functor
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The inverse of `equivSheafOfModulesPinned` is additive. -/
instance equivSheafOfModulesPinned_inverse_additive
    (A : SimplicialObject (Sheaf J CommRingCat.{u})) :
    (equivSheafOfModulesPinned J A).inverse.Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryProducts
    (equivSheafOfModulesPinned J A).inverse
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- **`- ⊗^𝐋_{A_•} B_• : D(A_•) ⟶ D(B_•)`**, derived extension of scalars along a homomorphism
`A_• ⟶ B_•` of simplicial sheaves of commutative rings, written on sheaves of modules over the
associated sheaves of rings on `Δ × C`. It is the derived pullback of [Stacks, Tag 06YY] along
the change of coefficient rings that `A_• ⟶ B_•` induces on `Δ × C`. -/
def derivedSimplicialBaseChange {A B : SimplicialObject (Sheaf J CommRingCat.{u})} (f : A ⟶ B) :
    DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (Stacks.Cohomology.ringedTopos (projectionTopology C J)
            (simplicialCommRingSheaf J A)).O)) ⥤
      DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (Stacks.Cohomology.ringedTopos (projectionTopology C J)
            (simplicialCommRingSheaf J B)).O)) :=
  Stacks.Cohomology.derivedCoefficientChange.{u} (simplicialCommRingSheafMap J f)

open Stacks.Cohomology.DerivedPullbackOnRingedTopoi in
/-- `derivedSimplicialBaseChange` commutes with the shift by `ℤ`. -/
instance derivedSimplicialBaseChange_commShift
    {A B : SimplicialObject (Sheaf J CommRingCat.{u})} (f : A ⟶ B) :
    (derivedSimplicialBaseChange J f).CommShift ℤ :=
  derivedPullbackCommShift.{u}
    (AlgebraicGeometry.RingedToposSiteHom.coefficientChange.{u, u, u}
      (projectionTopology C J) (simplicialCommRingSheafMap J f))
    (Functor.isMorphismOfSites_id _)

open Stacks.Cohomology.DerivedPullbackOnRingedTopoi in
/-- `derivedSimplicialBaseChange` is a triangulated functor. -/
instance derivedSimplicialBaseChange_isTriangulated
    {A B : SimplicialObject (Sheaf J CommRingCat.{u})} (f : A ⟶ B) :
    (derivedSimplicialBaseChange J f).IsTriangulated :=
  derivedPullback_isTriangulated_of_isMorphismOfSites.{u}
    (AlgebraicGeometry.RingedToposSiteHom.coefficientChange.{u, u, u}
      (projectionTopology C J) (simplicialCommRingSheafMap J f))
    (Functor.isMorphismOfSites_id _)

/-! ### `- ⊗^𝐋_{A_•} O` at an augmentation, with `D(π^{-1}O)` as sheaves of modules -/

/-- Derived extension of scalars along an augmentation `ε : A_• ⟶ O`, with its target written as
sheaves of modules over `π^{-1}O`. This differs from
`Stacks.SimplicialModules.derivedSimplicialBaseChange` at `ε` only in the spelling of the target
sheaf of rings, `π^{-1}O` in place of the sheaf of rings of the constant simplicial sheaf of
rings `O`; the two are identified by
`Stacks.SimplicialModules.constantSimplicialCommRingIso`. -/
def derivedBaseChangeToProjectionRing {A : SimplicialObject (Sheaf J CommRingCat.{u})}
    {O : Sheaf J CommRingCat.{u}} (ε : A ⟶ (Functor.const SimplexCategoryᵒᵖ).obj O) :
    DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (Stacks.Cohomology.ringedTopos (projectionTopology C J)
            (simplicialCommRingSheaf J A)).O)) ⥤
      DerivedCategory (SheafOfModules.{u} (projectionRingSheaf J O)) :=
  Stacks.Cohomology.derivedCoefficientChange.{u} (augmentationCommRingMap J ε)

open Stacks.Cohomology.DerivedPullbackOnRingedTopoi in
/-- `derivedBaseChangeToProjectionRing` commutes with the shift by `ℤ`. -/
instance derivedBaseChangeToProjectionRing_commShift
    {A : SimplicialObject (Sheaf J CommRingCat.{u})}
    {O : Sheaf J CommRingCat.{u}} (ε : A ⟶ (Functor.const SimplexCategoryᵒᵖ).obj O) :
    (derivedBaseChangeToProjectionRing J ε).CommShift ℤ :=
  derivedPullbackCommShift.{u}
    (AlgebraicGeometry.RingedToposSiteHom.coefficientChange.{u, u, u}
      (projectionTopology C J) (augmentationCommRingMap J ε))
    (Functor.isMorphismOfSites_id _)

open Stacks.Cohomology.DerivedPullbackOnRingedTopoi in
/-- `derivedBaseChangeToProjectionRing` is a triangulated functor. -/
instance derivedBaseChangeToProjectionRing_isTriangulated
    {A : SimplicialObject (Sheaf J CommRingCat.{u})}
    {O : Sheaf J CommRingCat.{u}} (ε : A ⟶ (Functor.const SimplexCategoryᵒᵖ).obj O) :
    (derivedBaseChangeToProjectionRing J ε).IsTriangulated :=
  derivedPullback_isTriangulated_of_isMorphismOfSites.{u}
    (AlgebraicGeometry.RingedToposSiteHom.coefficientChange.{u, u, u}
      (projectionTopology C J) (augmentationCommRingMap J ε))
    (Functor.isMorphismOfSites_id _)

/-- **Derived extension of scalars along an augmentation of a simplicial sheaf of rings:**
`- ⊗^𝐋_{A_•} O : D(A_•) ⟶ D(π^{-1}O)`, the first factor of the functor `Lπ_!` of
[Stacks, Tag 09D3]. The source is the derived category of simplicial `A_•`-modules of
[Stacks, Tag 09D1] and the target is the derived category of sheaves of modules over `π^{-1}O`,
which is where the `Lπ_! : D(π^{-1}O) ⟶ D(O)` of [Stacks, Tag 09CY] starts. -/
def derivedAugmentationBaseChange {A : SimplicialObject (Sheaf J CommRingCat.{u})}
    {O : Sheaf J CommRingCat.{u}} (ε : A ⟶ (Functor.const SimplexCategoryᵒᵖ).obj O) :
    DerivedCategory (SimplicialModule.{u, u, u, u} J (simplicialRingSheaf J A)) ⥤
      DerivedCategory (SheafOfModules.{u} (projectionRingSheaf J O)) :=
  Functor.mapDerivedCategory (equivSheafOfModulesPinned J A).functor ⋙
    derivedBaseChangeToProjectionRing J ε

/-- `derivedAugmentationBaseChange` commutes with the shift by `ℤ`. -/
instance derivedAugmentationBaseChange_commShift
    {A : SimplicialObject (Sheaf J CommRingCat.{u})}
    {O : Sheaf J CommRingCat.{u}} (ε : A ⟶ (Functor.const SimplexCategoryᵒᵖ).obj O) :
    (derivedAugmentationBaseChange J ε).CommShift ℤ := by
  unfold derivedAugmentationBaseChange
  infer_instance

/-- `derivedAugmentationBaseChange` is a triangulated functor. -/
instance derivedAugmentationBaseChange_isTriangulated
    {A : SimplicialObject (Sheaf J CommRingCat.{u})}
    {O : Sheaf J CommRingCat.{u}} (ε : A ⟶ (Functor.const SimplexCategoryᵒᵖ).obj O) :
    (derivedAugmentationBaseChange J ε).IsTriangulated := by
  unfold derivedAugmentationBaseChange
  infer_instance

/-! ### `- ⊗^𝐋_{A_•} O` at an augmentation, with `D(π^{-1}O)` as simplicial modules -/

/-- `D(π^{-1}O)` presented as the derived category of simplicial modules over the constant
simplicial sheaf of rings `O`, at the spelling
`Stacks.Cohomology.derivedCoefficientChange` is stated in. -/
def constantEquivSheafOfModulesPinned (O : Sheaf J CommRingCat.{u}) :
    SimplicialModule.{u, u, u, u} J
        (constantRing J ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)) ≌
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.Cohomology.ringedTopos (projectionTopology C J)
          (simplicialCommRingSheaf J ((Functor.const SimplexCategoryᵒᵖ).obj O))).O) :=
  equivSheafOfModules.{u, u, u, u} J
    (constantRing J ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O))

/-- The inverse of `constantEquivSheafOfModulesPinned` is additive. -/
instance constantEquivSheafOfModulesPinned_inverse_additive (O : Sheaf J CommRingCat.{u}) :
    (constantEquivSheafOfModulesPinned J O).inverse.Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryProducts
    (constantEquivSheafOfModulesPinned J O).inverse
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- **The `base` parameter of `Stacks.SimplicialModules.augmentedLowerShriek`**, that is
`- ⊗^𝐋_{A_•} O : D(A_•) ⟶ D(O_•)` with the target read as simplicial modules over the constant
simplicial sheaf of rings `O`. It is `derivedSimplicialBaseChange` at the augmentation,
transported across `Stacks.SimplicialModules.equivSheafOfModules` at both ends. -/
def derivedAugmentationBaseChangeSimplicial {A : SimplicialObject (Sheaf J CommRingCat.{u})}
    {O : Sheaf J CommRingCat.{u}} (ε : A ⟶ (Functor.const SimplexCategoryᵒᵖ).obj O) :
    DerivedCategory (SimplicialModule.{u, u, u, u} J (simplicialRingSheaf J A)) ⥤
      DerivedCategory (SimplicialModule.{u, u, u, u} J
        (constantRing J ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O))) :=
  Functor.mapDerivedCategory (equivSheafOfModulesPinned J A).functor ⋙
    derivedSimplicialBaseChange J ε ⋙
    Functor.mapDerivedCategory (constantEquivSheafOfModulesPinned J O).inverse

/-- `derivedAugmentationBaseChangeSimplicial` commutes with the shift by `ℤ`. -/
instance derivedAugmentationBaseChangeSimplicial_commShift
    {A : SimplicialObject (Sheaf J CommRingCat.{u})}
    {O : Sheaf J CommRingCat.{u}} (ε : A ⟶ (Functor.const SimplexCategoryᵒᵖ).obj O) :
    (derivedAugmentationBaseChangeSimplicial J ε).CommShift ℤ := by
  unfold derivedAugmentationBaseChangeSimplicial
  infer_instance

/-- `derivedAugmentationBaseChangeSimplicial` is a triangulated functor. -/
instance derivedAugmentationBaseChangeSimplicial_isTriangulated
    {A : SimplicialObject (Sheaf J CommRingCat.{u})}
    {O : Sheaf J CommRingCat.{u}} (ε : A ⟶ (Functor.const SimplexCategoryᵒᵖ).obj O) :
    (derivedAugmentationBaseChangeSimplicial J ε).IsTriangulated := by
  unfold derivedAugmentationBaseChangeSimplicial
  infer_instance

/-- **The exactness clause of [Stacks, Tag 09D3] at the constructed `base`.** With
`derivedAugmentationBaseChangeSimplicial` as the `base` parameter of
`Stacks.SimplicialModules.augmentedLowerShriek`, the functor is triangulated whenever `proj`
commutes with the shift and is triangulated. -/
example {A : SimplicialObject (Sheaf J CommRingCat.{u})} {O : Sheaf J CommRingCat.{u}}
    (ε : A ⟶ (Functor.const SimplexCategoryᵒᵖ).obj O)
    {D : Type u} [Category.{u} D] [Abelian D] [HasDerivedCategory D]
    (proj : DerivedCategory (SimplicialModule.{u, u, u, u} J
        (constantRing J ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O))) ⥤
      DerivedCategory D) [proj.CommShift ℤ] [proj.IsTriangulated] :
    (augmentedLowerShriek J (augmentationRingMap J ε)
      (derivedAugmentationBaseChangeSimplicial J ε) proj).IsTriangulated :=
  inferInstance

end

section

attribute [local instance] abelian

/-- **`- ⊗^𝐋_{A_•} O` composes with the `Lπ_!` of [Stacks, Tag 09CY] on sheaves of modules.** The
source of that functor is the derived category of sheaves of modules over the restriction of the
structure sheaf of a ringed site along `π : Δ × C ⥤ C`, which is the target of
`derivedAugmentationBaseChange`; the composite is exact. -/
example (Y : AlgebraicGeometry.RingedSite.{u, u, u})
    {A : SimplicialObject (Sheaf Y.J CommRingCat.{u})}
    (ε : A ⟶ (Functor.const SimplexCategoryᵒᵖ).obj Y.O)
    {D : Type u} [Category.{u} D] [Abelian D] [HasDerivedCategory D]
    (proj : DerivedCategory (SheafOfModules.{u} (projectionRingSheaf Y.J Y.O)) ⥤
      DerivedCategory D)
    [proj.CommShift ℤ] [proj.IsTriangulated] :
    (derivedAugmentationBaseChange Y.J ε ⋙ proj).IsTriangulated :=
  inferInstance

end

end Stacks.SimplicialModules

end
