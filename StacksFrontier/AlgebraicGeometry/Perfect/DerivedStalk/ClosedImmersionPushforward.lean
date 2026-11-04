module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkwiseIsomorphism
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Pushforward

/-!
# The derived stalk of `Ri_*` along a closed immersion

Let `i : (Z, 𝒪_Z) ⟶ (X, 𝒪_X)` be a morphism of ringed spaces whose underlying map is a closed
embedding. Pushforward of sheaves of modules along `i` is exact (Stacks 08KS), so:

* `Ri_*` is the functor `i_*` induces on derived categories directly, with no resolution;
* off the image of `i` every stalk of `i_* M` vanishes (Stacks 00AE), and therefore so does the
  whole derived stalk of `Ri_* K`.

## Main results

* `Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory`: `Ri_* ≅ i_*` on derived
  categories, and its closed-immersion-of-schemes instance
  `derivedPushforwardIsoMapDerivedCategoryOfSchemes`.
* `Stacks.ClosedImmersion.isZero_stalk_modulePushforward_of_notMemRange`: the sheaf-level
  vanishing of the stalk of `i_* M` off the image.
* `Stacks.ClosedImmersion.isZero_derivedStalk_mapDerivedCategory_of_notMemRange`: the
  derived-level vanishing.

## Implementation notes

`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward i` is the total right derived
  functor of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pushforwardToDerivedCategory i`, which is
  *syntactically*
`(modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh` — the
functor `Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived` is stated for. So the
first result is that isomorphism inverted, with no bridge.

`PreservesFiniteColimits (modulePushforward i)` is an instance *binder* on the ringed-space
statements rather than a hypothesis discharged inside them. It has to be: it appears in the
elaboration of `(modulePushforward i).mapDerivedCategory`, which is part of the **statement**,
and an instance seated by `haveI` in the proof arrives too late, the error
"failed to synthesize instance PreservesFiniteColimits (modulePushforward i)" being reported against
the type line of a declaration whose body seats exactly that instance. It is not a weakening:
`Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward` inhabits it for every closed
embedding, it is `Prop`-valued, and the scheme-level corollaries below are stated with it
discharged.

The derived-level vanishing is proved through homology rather than through a composite of
`mapDerivedCategory`s, because `(F ⋙ G).mapDerivedCategory ≅ F.mapDerivedCategory ⋙
G.mapDerivedCategory` is not in the library. Instead the `n`-th homology of the derived stalk is
rewritten as the stalk of the `n`-th cohomology sheaf of `i_* K`
(`AlgebraicGeometry.SheafOfModules.derivedStalkHomologyIso`), then as the stalk of `i_*` of the
`n`-th cohomology sheaf of `K` (`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`), which is
zero sheaf-level. Vanishing of all homology is turned into vanishing of the object via
`DerivedCategory.isIso_iff` applied to the zero endomorphism: on a zero object the zero
endomorphism and the identity agree, so the zero endomorphism is invertible in every degree,
hence invertible, hence the identity is zero.

Nothing here is tagged. Stacks 0E23's single clause is the assertion that a base change
comparison is an isomorphism; these are inputs to it. Stacks 00AE and Stacks 08KS are already
tagged where they are proved, and the derived restatements are not clauses of either.

## References

* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

noncomputable section

namespace Stacks.ClosedImmersion

universe u

attribute [local instance] HasDerivedCategory.standard

section RingedSpace

variable {Z X : RingedSpace.{u, u}} (i : Z ⟶ X)

/-- **`Ri_*` is `i_*`.** For a morphism of ringed spaces along which pushforward of sheaves of
modules is right exact — a closed embedding, by Stacks 08KS — the chosen unbounded derived
pushforward is the functor `i_*` induces on derived categories.

`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward i` is by definition the total
  right derived functor of
`(modulePushforward i).mapHomotopyCategory _ ⋙ DerivedCategory.Qh`, so this is
`mapDerivedCategoryIsoTotalRightDerived` inverted. -/
def derivedPushforwardIsoMapDerivedCategory
    [PreservesFiniteColimits (modulePushforward i)] :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward i ≅ (modulePushforward
      i).mapDerivedCategory :=
  (mapDerivedCategoryIsoTotalRightDerived (modulePushforward i)).symm

/-- **Stacks 00AE for sheaves of modules.** At a point outside the image of a closed embedding
the stalk of `i_* M` is a zero object of `ModuleCat 𝒪_{X,x}`.

The stalk of a sheaf of modules vanishes exactly when the stalk of its underlying presheaf of
abelian groups does (`AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff`), and that
stalk is a terminal object by `ClosedImmersionSheaves.isTerminalStalkPushforwardOfNotMemRange`;
in `AddCommGrpCat` a terminal object is a zero object. -/
theorem isZero_stalk_modulePushforward_of_notMemRange
    (hi : Topology.IsClosedEmbedding (ConcreteCategory.hom i.hom.base))
    (M : SheafOfModules.{u} (structureSheafRing Z)) (x : X.carrier)
    (hx : x ∉ Set.range (ConcreteCategory.hom i.hom.base)) :
    IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X) x).obj
      ((modulePushforward i).obj M)) := by
  rw [AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff]
  exact IsZero.of_iso (isZero_zero AddCommGrpCat.{u})
    ((ClosedImmersionSheaves.isTerminalStalkPushforwardOfNotMemRange
      i.hom.base M.isSheaf hi x hx).uniqueUpToIso HasZeroObject.zeroIsTerminal)

/-- **The derived stalk of `i_* K` vanishes off the image of a closed embedding.** Every
cohomology sheaf of `i_* K` is `i_*` of a cohomology sheaf of `K`, whose stalk off the image is
zero by `isZero_stalk_modulePushforward_of_notMemRange`; an object of the derived category whose
homology vanishes in every degree is zero.

With `derivedPushforwardIsoMapDerivedCategory` this says the derived stalk of `Ri_* K` vanishes
off the image. -/
theorem isZero_derivedStalk_mapDerivedCategory_of_notMemRange
    [PreservesFiniteColimits (modulePushforward i)]
    (hi : Topology.IsClosedEmbedding (ConcreteCategory.hom i.hom.base))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))) (x : X.carrier)
    (hx : x ∉ Set.range (ConcreteCategory.hom i.hom.base)) :
    IsZero ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheafRing X) x).obj
      ((modulePushforward i).mapDerivedCategory.obj K)) := by
  set Y := (AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheafRing X) x).obj
    ((modulePushforward i).mapDerivedCategory.obj K) with hY
  have hz : ∀ n : ℤ, IsZero ((DerivedCategory.homologyFunctor _ n).obj Y) := by
    intro n
    refine IsZero.of_iso (isZero_stalk_modulePushforward_of_notMemRange i hi
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Z)) n).obj K)
        x hx) ?_
    exact ((AlgebraicGeometry.SheafOfModules.derivedStalkHomologyIso (structureSheafRing X) x n).app
        ((modulePushforward i).mapDerivedCategory.obj K)) ≪≫
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X) x).mapIso
        (((modulePushforward i).mapDerivedCategoryHomologyIso n).app K)
  have hiso : IsIso (0 : Y ⟶ Y) := by
    rw [DerivedCategory.isIso_iff]
    intro n
    rw [(hz n).eq_of_src ((DerivedCategory.homologyFunctor _ n).map (0 : Y ⟶ Y)) (𝟙 _)]
    infer_instance
  rw [IsZero.iff_id_eq_zero]
  calc (𝟙 Y) = CategoryTheory.inv (0 : Y ⟶ Y) ≫ (0 : Y ⟶ Y) := (IsIso.inv_hom_id _).symm
    _ = 0 := Limits.comp_zero

end RingedSpace

section Scheme

/-- `derivedPushforwardIsoMapDerivedCategory` for a closed immersion of schemes, where the
exactness instance is supplied by
`preservesFiniteColimits_modulePushforward_of_isClosedImmersion`. -/
def derivedPushforwardIsoMapDerivedCategoryOfSchemes {Z X : Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward i.toLRSHom.toShHom ≅
      (modulePushforward i.toLRSHom.toShHom).mapDerivedCategory :=
  derivedPushforwardIsoMapDerivedCategory _

/-- The derived stalk of `Ri_* K` vanishes off the image, for a closed immersion of schemes. -/
theorem isZero_derivedStalk_derivedPushforward_of_notMemRange {Z X : Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i]
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (x : X.toRingedSpace.carrier)
    (hx : x ∉ Set.range (ConcreteCategory.hom i.toLRSHom.toShHom.hom.base)) :
    IsZero ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctor
        (structureSheafRing X.toRingedSpace) x).obj
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward i.toLRSHom.toShHom).obj
        K)) :=
  IsZero.of_iso
    (isZero_derivedStalk_mapDerivedCategory_of_notMemRange i.toLRSHom.toShHom
      (isClosedEmbedding_base_toShHom i) K x hx)
    ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctor
      (structureSheafRing X.toRingedSpace) x).mapIso
      ((derivedPushforwardIsoMapDerivedCategoryOfSchemes i).app K))

end Scheme

end Stacks.ClosedImmersion

end

end
