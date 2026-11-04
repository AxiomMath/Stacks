module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomGluingInSituation0D67
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation

/-!
# Restriction of morphisms in Situation 0D67, read on the ringed site

Let `(X, 𝒪_X)` be a ringed space and let `S` be a system of locally given derived objects on it
(Situation 0D67).  `Stacks.DerivedGlueing.homEquivSlice` identifies, for an object `K` over an
open `O` and an open `W ≤ O`, the group of morphisms between the restrictions `K|_W` displayed by
the system with the group of morphisms between the slice-model restrictions to `W` of the
extension by zero of `K` along `O`.  What that dictionary does not yet carry is the *restriction
maps* between those groups: `Stacks.DerivedGlueing.restrictHomBelow` on the one side and
`AlgebraicGeometry.RingedSite.restrictDerivedHom` on the other.

This file carries the comparison of the two *functors* those restriction maps are built from.
On sheaves of modules, restriction from `W` to `T ≤ W` in the open-subspace model, read on a
module coming from the slice over `W`, is restriction along the arrow `T ⟶ W` of the site:

`Stacks.DerivedGlueing.sliceRestrictOverIsoOpenModule`, which is
`Stacks.DerivedGlueing.sliceRestrictOverIso` with its source respelled through
`Stacks.DerivedGlueing.openModuleRestriction`.

That comparison is then lifted to unbounded derived categories,
`Stacks.DerivedGlueing.sliceRestrictOverDerivedIso`, and composed with the identification
`Stacks.DerivedGlueing.restrictionIsoMapDerivedCategory` of the system's displayed restriction
with the functor induced by restriction of complexes, giving
`Stacks.DerivedGlueing.sliceRestrictOverRestrictionIso`:

`(sliceToSubspace 𝒪_X W).mapDerivedCategory ⋙ S.restriction T W hTW ≅`
`  (SheafOfModules.overMap 𝒪_X hTW.hom).mapDerivedCategory ⋙`
`  (sliceToSubspace 𝒪_X T).mapDerivedCategory`

This is the `Λ` that `Stacks.DerivedGlueing.conj_eq_conj_of_iso` consumes: with it, the coherence
`restrictHomBelow_eq_restrictDerivedHom` — the one statement the chain from [Stacks, Tag 0D66]
part (2) to the uniqueness clause of [Stacks, Tag 0D68] still owes — reduces to an equation
between *isomorphisms*, with the morphism `φ` eliminated.  The two isomorphisms to be compared
are, at an object `K` over `O` (writing `K' = j_{O!}K` and `x = K'|_W` on the slice over `W`),

* `S.restrictionIsoOfExtension O T _ K ≪≫ (S.restrictionComp T W O hTW hWO).app K ≪≫`
  `  ((S.restriction T W hTW).mapIso (S.restrictionIsoOfExtension O W hWO K)).symm`,
  followed by `sliceRestrictOverRestrictionIso S hTW |>.app x`; and
* `((sliceToSubspace 𝒪_X T).mapDerivedCategory.mapIso`
  `  ((AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso _ hTW.hom).app K')).symm`.

Both are natural in `K`, so `CategoryTheory.Localization.natTrans_ext` reduces that equation to
its instances at the class of a complex, where every comparison involved has an explicit value:
`Stacks.DerivedGlueing.mapDerivedCategoryCongr_hom_app_Q`,
`Stacks.DerivedGlueing.mapDerivedCategoryCompIso_hom_app_Q` and their inverses,
`Stacks.DerivedGlueing.LocallyGiven.restrictionCompFactors'`, and
`AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso_hom_app_Q`.  The only
non-formal ingredient is the triangle identity for `ExtensionByZeroModules.jShriekAdjunction`,
and it is already discharged, at the level of sheaves of modules, as
`Stacks.DerivedGlueing.sliceExtendOverIso_hom_app_over`: the comparison
`Stacks.DerivedGlueing.sliceExtendOverIso` evaluated at the restriction of a module on the whole
space is the restriction of the *counit*, which is what the system's comparisons
`Stacks.DerivedGlueing.LocallyGiven.restrictionComp` are pinned to by `restrictionCompFactors`.

## Main definitions

* `Stacks.DerivedGlueing.sliceRestrictOverIsoOpenModule` — on sheaves of modules: restriction in
  the open-subspace model, on a module read from the slice over `W`, is restriction along an
  arrow of the site.
* `Stacks.DerivedGlueing.sliceRestrictOverDerivedIso` — the same on unbounded derived
  categories.
* `Stacks.DerivedGlueing.sliceRestrictOverRestrictionIso` — the same with the system's displayed
  restriction in place of the functor induced by restriction of complexes.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 00AB](https://stacks.math.columbia.edu/tag/00AB)

Tags covered: none.  Everything here is a step of the proof of the uniqueness clause of
Tag 0D68, not a clause of the statement of any tag.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open ExtensionByZeroModules RingedSpaceModuleAdjunction

namespace Stacks.DerivedGlueing

universe u

/-! ### Two pieces of category algebra -/

/-- **Conjugating the image of a morphism by two isomorphisms, with the source and the target
replaced along further isomorphisms.**  If `g` is the image of `φ` conjugated by `wK` and `wL`,
then conjugating `G.map φ` by `tK ≫ cK` and `tL ≫ cL` is conjugating `g` by the composites that
include the images of `wK` and `wL`.

Every object and morphism is a variable, so this applies by `exact` at one definitional
unification; stated with the spellings of a concrete situation it would need a rewrite across a
crossing. -/
theorem conj_map_eq_conj_mapIso {CC : Type*} [Category CC] {DD : Type*} [Category DD]
    (G : CC ⥤ DD) {a b A B : DD} {P Q P' Q' : CC}
    (tK : a ≅ A) (tL : b ≅ B) (cK : A ≅ G.obj P') (cL : B ≅ G.obj Q')
    (wK : P ≅ P') (wL : Q ≅ Q') (phi : P' ⟶ Q')
    (g : G.obj P ⟶ G.obj Q) (hg : g = G.map (wK.hom ≫ phi ≫ wL.inv)) :
    tK.hom ≫ (cK.hom ≫ G.map phi ≫ cL.inv) ≫ tL.inv =
      (tK ≪≫ cK ≪≫ (G.mapIso wK).symm).hom ≫ g ≫
        (tL ≪≫ cL ≪≫ (G.mapIso wL).symm).inv := by
  subst hg
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp

/-- A functor carries a threefold composite to the composite of the images.  Stated with every
object and morphism a variable, for the same reason. -/
theorem map_comp_comp {CC : Type*} [Category CC] {DD : Type*} [Category DD] (F : CC ⥤ DD)
    {p q p' q' : CC} (u : p ⟶ p') (m : p' ⟶ q') (v : q' ⟶ q) :
    F.map u ≫ F.map m ≫ F.map v = F.map (u ≫ m ≫ v) := by
  simp

/-! ### The comparison on sheaves of modules -/

section Abelian

variable {Z : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology Z) RingCat.{u})

/-- **Reading a module on the slice over `W` in the open-subspace model, extending it by zero and
restricting it to the open subspace `T`, is restricting it along the arrow `T ⟶ W` of the site
and reading the result in the open-subspace model of `T`** — as an equality of the two composites
of functors whose comparison
`Stacks.DerivedGlueing.sliceRestrictOverIso` is.

The equality is proved by reassociating and appealing to
`Stacks.DerivedGlueing.overFunctor_comp_overMap_comp_sliceToSubspace`, never by asking for the
composite `rfl`: the implementation notes of that lemma record that the direct comparison of the
two spellings of a module costs upwards of half a million heartbeats. -/
theorem slice_comp_jShriek_jStar_eq {T W : Opens Z} (hTW : T ≤ W) :
    (sliceToSubspace O W ⋙ jShriek W O ⋙ SheafOfModules.overFunctor.{u} O W) ⋙
        (SheafOfModules.overMap.{u} O hTW.hom ⋙ sliceToSubspace O T) =
      sliceToSubspace O W ⋙ (jShriek W O ⋙ jStar T O) :=
  (Functor.assoc _ _ _).trans
    (congrArg (fun F => sliceToSubspace O W ⋙ F)
      ((Functor.assoc _ _ _).trans
        (congrArg (fun F => jShriek W O ⋙ F)
          (overFunctor_comp_overMap_comp_sliceToSubspace O hTW))))

end Abelian

/-! ### The comparison on unbounded derived categories -/

section Derived

variable {X : RingedSpace.{u, u}}

attribute [local instance 10000] HasDerivedCategory.standard

/-- Restriction of sheaves of modules along an arrow of the site of opens preserves finite
limits; this is `Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits`, recorded as
an instance so that the induced functor on derived categories can be formed. -/
local instance preservesFiniteLimitsOverMap {T W : Opens X.carrier} (hTW : T ≤ W) :
    PreservesFiniteLimits
      (SheafOfModules.overMap.{u} (underlyingRingSheaf X) hTW.hom) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits hTW.hom

/-- Restriction of sheaves of modules along an arrow of the site of opens preserves finite
colimits; this is `Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits`. -/
local instance preservesFiniteColimitsOverMap {T W : Opens X.carrier} (hTW : T ≤ W) :
    PreservesFiniteColimits
      (SheafOfModules.overMap.{u} (underlyingRingSheaf X) hTW.hom) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits hTW.hom

/-- **Restriction of modules from `W` to `T ≤ W` in the open-subspace model, on a module read
from the slice over `W`, is restriction along the arrow `T ⟶ W` of the site.**

This is `Stacks.DerivedGlueing.sliceRestrictOverIso` with its source respelled through
`Stacks.DerivedGlueing.openModuleRestriction`, by
`Stacks.DerivedGlueing.slice_comp_jShriek_jStar_eq`; the comparison itself is the invertible unit
of extension by zero and restriction, whose value at the restriction of a module on the whole
space is the restriction of the counit
(`Stacks.DerivedGlueing.sliceExtendOverIso_hom_app_over`). -/
def sliceRestrictOverIsoOpenModule {T W : Opens X.carrier} (hTW : T ≤ W) :
    sliceToSubspace (underlyingRingSheaf X) W ⋙ openModuleRestriction X T W hTW ≅
      SheafOfModules.overMap.{u} (underlyingRingSheaf X) hTW.hom ⋙
        sliceToSubspace (underlyingRingSheaf X) T :=
  eqToIso (slice_comp_jShriek_jStar_eq (underlyingRingSheaf X) hTW).symm ≪≫
    sliceRestrictOverIso (underlyingRingSheaf X) hTW

/-- **`Stacks.DerivedGlueing.sliceRestrictOverIsoOpenModule` on unbounded derived
categories.**  The two halves of the identification are exact, so each composite of functors
induces a composite on derived categories
(`Stacks.DerivedGlueing.mapDerivedCategoryCompIso`), and the comparison is the derived action of
the comparison on sheaves of modules
(`Stacks.DerivedGlueing.mapDerivedCategoryCongr`). -/
def sliceRestrictOverDerivedIso {T W : Opens X.carrier} (hTW : T ≤ W) :
    (sliceToSubspace (underlyingRingSheaf X) W).mapDerivedCategory ⋙
        (openModuleRestriction X T W hTW).mapDerivedCategory ≅
      (SheafOfModules.overMap.{u} (underlyingRingSheaf X) hTW.hom).mapDerivedCategory ⋙
        (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory :=
  mapDerivedCategoryCompIso (sliceToSubspace (underlyingRingSheaf X) W)
      (openModuleRestriction X T W hTW) ≪≫
    mapDerivedCategoryCongr (sliceRestrictOverIsoOpenModule hTW) ≪≫
    (mapDerivedCategoryCompIso (SheafOfModules.overMap.{u} (underlyingRingSheaf X) hTW.hom)
      (sliceToSubspace (underlyingRingSheaf X) T)).symm

/-- **`Stacks.DerivedGlueing.sliceRestrictOverDerivedIso` with the restriction displayed by a
system of locally given derived objects.**  The displayed restriction is identified with the
functor induced by restriction of complexes by
`Stacks.DerivedGlueing.restrictionIsoMapDerivedCategory`, for every system.

This is the comparison `Λ` that reduces the coherence between
`Stacks.DerivedGlueing.restrictHomBelow` and
`AlgebraicGeometry.RingedSite.restrictDerivedHom` to an equation between isomorphisms, by
`Stacks.DerivedGlueing.conj_eq_conj_of_iso`. -/
def sliceRestrictOverRestrictionIso (S : LocallyGiven X) {T W : Opens X.carrier} (hTW : T ≤ W) :
    (sliceToSubspace (underlyingRingSheaf X) W).mapDerivedCategory ⋙
        S.restriction T W hTW ≅
      (SheafOfModules.overMap.{u} (underlyingRingSheaf X) hTW.hom).mapDerivedCategory ⋙
        (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory :=
  Functor.isoWhiskerLeft (sliceToSubspace (underlyingRingSheaf X) W).mapDerivedCategory
      (restrictionIsoMapDerivedCategory S T W hTW) ≪≫
    sliceRestrictOverDerivedIso hTW

/-! ### The coherence, reduced to an equation between isomorphisms -/

/-- **The comparison on the side of the system.**  For an object `K` over `O` and opens
`T ≤ W ≤ O`, the slice-model restriction to `T` of the extension by zero of `K` is identified
with the restriction to `T` *of the restriction to `W`* displayed by the system: first with the
displayed restriction to `T`, by
`Stacks.DerivedGlueing.LocallyGiven.restrictionIsoOfExtension`, then with its reading through
`W`, by the system's comparison `Stacks.DerivedGlueing.LocallyGiven.restrictionComp`, and
finally the inner restriction is read back on the slice over `W`. -/
def restrictionCompareIso (S : LocallyGiven X) {O : Opens X.carrier}
    (K : OpenDerivedCategory X O) {T W : Opens X.carrier} (hTW : T ≤ W) (hWO : W ≤ O) :
    (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory.obj
        ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) T).mapDerivedCategory.obj
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)) ≅
      (S.restriction T W hTW).obj
        ((sliceToSubspace (underlyingRingSheaf X) W).mapDerivedCategory.obj
          ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).mapDerivedCategory.obj
            ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K))) :=
  S.restrictionIsoOfExtension O T (hTW.trans hWO) K ≪≫
    (S.restrictionComp T W O hTW hWO).app K ≪≫
      ((S.restriction T W hTW).mapIso (S.restrictionIsoOfExtension O W hWO K)).symm

/-- **The comparison on the side of the ringed site.**  The same two objects, identified instead
by the transitivity of restriction to a slice,
`AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso`, read in the open-subspace model
of `T`.  No system is involved. -/
def overMapCompareIso {O : Opens X.carrier} (K : OpenDerivedCategory X O)
    {T W : Opens X.carrier} (hTW : T ≤ W) :
    (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory.obj
        ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) T).mapDerivedCategory.obj
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)) ≅
      (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory.obj
        ((SheafOfModules.overMap.{u} (underlyingRingSheaf X) hTW.hom).mapDerivedCategory.obj
          ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).mapDerivedCategory.obj
            ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K))) :=
  ((sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory.mapIso
    ((RingedSite.overMapDerivedCategoryRestrictIso (Stacks.SheafOfModules.ringedSite X.sheaf)
      hTW.hom).app ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K))).symm

/-- The comparison of the system, on morphisms. -/
theorem restrictionCompareIso_hom (S : LocallyGiven X) {O : Opens X.carrier}
    (K : OpenDerivedCategory X O) {T W : Opens X.carrier} (hTW : T ≤ W) (hWO : W ≤ O) :
    (restrictionCompareIso S K hTW hWO).hom =
      (S.restrictionIsoOfExtension O T (hTW.trans hWO) K).hom ≫
        (S.restrictionComp T W O hTW hWO).hom.app K ≫
          (S.restriction T W hTW).map (S.restrictionIsoOfExtension O W hWO K).inv :=
  rfl

/-- The comparison of the system, inverted. -/
theorem restrictionCompareIso_inv (S : LocallyGiven X) {O : Opens X.carrier}
    (K : OpenDerivedCategory X O) {T W : Opens X.carrier} (hTW : T ≤ W) (hWO : W ≤ O) :
    (restrictionCompareIso S K hTW hWO).inv =
      ((S.restriction T W hTW).map (S.restrictionIsoOfExtension O W hWO K).hom ≫
          (S.restrictionComp T W O hTW hWO).inv.app K) ≫
        (S.restrictionIsoOfExtension O T (hTW.trans hWO) K).inv :=
  rfl

/-- The comparison of the site, on morphisms. -/
theorem overMapCompareIso_hom {O : Opens X.carrier} (K : OpenDerivedCategory X O)
    {T W : Opens X.carrier} (hTW : T ≤ W) :
    (overMapCompareIso K hTW).hom =
      (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory.map
        ((RingedSite.overMapDerivedCategoryRestrictIso
          (Stacks.SheafOfModules.ringedSite X.sheaf) hTW.hom).inv.app
            ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)) :=
  rfl

/-- The comparison of the site, inverted. -/
theorem overMapCompareIso_inv {O : Opens X.carrier} (K : OpenDerivedCategory X O)
    {T W : Opens X.carrier} (hTW : T ≤ W) :
    (overMapCompareIso K hTW).inv =
      (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory.map
        ((RingedSite.overMapDerivedCategoryRestrictIso
          (Stacks.SheafOfModules.ringedSite X.sheaf) hTW.hom).hom.app
            ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)) :=
  rfl

/-- **The dictionary `Stacks.DerivedGlueing.homEquivSlice`, read in the open-subspace model**:
the passage between the two models carries the morphism it produces back to the given morphism
conjugated by `Stacks.DerivedGlueing.LocallyGiven.restrictionIsoOfExtension`.  This is
`CategoryTheory.Functor.FullyFaithful.map_preimage` for
`Stacks.DerivedGlueing.sliceToSubspaceDerivedFullyFaithful`. -/
theorem sliceToSubspace_map_homEquivSlice (S : LocallyGiven X) {O : Opens X.carrier}
    (K L : OpenDerivedCategory X O) {V : Opens X.carrier} (hVO : V ≤ O)
    (xi : (S.restriction V O hVO).obj K ⟶ (S.restriction V O hVO).obj L) :
    (sliceToSubspace (underlyingRingSheaf X) V).mapDerivedCategory.map
        (homEquivSlice S K L hVO xi) =
      (S.restrictionIsoOfExtension O V hVO K).hom ≫ xi ≫
        (S.restrictionIsoOfExtension O V hVO L).inv := by
  simp [homEquivSlice, Functor.FullyFaithful.map_preimage]

/-- **Restricting a morphism in the vocabulary of Situation 0D67, read in the open-subspace
model of `T`, is the conjugate of its reading over `W` by
`Stacks.DerivedGlueing.restrictionCompareIso`.**

Only the definition of `Stacks.DerivedGlueing.restrictHomBelow` and the category algebra of
`Stacks.DerivedGlueing.conj_map_eq_conj_mapIso` are involved; the two comparisons of the system
cancel against the two copies of
`Stacks.DerivedGlueing.LocallyGiven.restrictionIsoOfExtension` inserted on the inner open. -/
theorem sliceToSubspace_map_homEquivSlice_restrictHomBelow (S : LocallyGiven X)
    {O : Opens X.carrier} (K L : OpenDerivedCategory X O) {T W : Opens X.carrier}
    (hTW : T ≤ W) (hWO : W ≤ O)
    (phi : (S.restriction W O hWO).obj K ⟶ (S.restriction W O hWO).obj L) :
    (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory.map
        (homEquivSlice S K L (hTW.trans hWO) (restrictHomBelow S hTW hWO phi)) =
      (restrictionCompareIso S K hTW hWO).hom ≫
        ((sliceToSubspace (underlyingRingSheaf X) W).mapDerivedCategory ⋙
          S.restriction T W hTW).map (homEquivSlice S K L hWO phi) ≫
        (restrictionCompareIso S L hTW hWO).inv := by
  refine (sliceToSubspace_map_homEquivSlice S K L (hTW.trans hWO)
    (restrictHomBelow S hTW hWO phi)).trans ?_
  refine conj_map_eq_conj_mapIso (S.restriction T W hTW)
    (S.restrictionIsoOfExtension O T (hTW.trans hWO) K)
    (S.restrictionIsoOfExtension O T (hTW.trans hWO) L)
    ((S.restrictionComp T W O hTW hWO).app K) ((S.restrictionComp T W O hTW hWO).app L)
    (S.restrictionIsoOfExtension O W hWO K) (S.restrictionIsoOfExtension O W hWO L) phi _ ?_
  exact congrArg (S.restriction T W hTW).map (sliceToSubspace_map_homEquivSlice S K L hWO phi)

/-- **Restricting a morphism along an arrow of the ringed site, read in the open-subspace model
of `T`, is the conjugate of the morphism by
`Stacks.DerivedGlueing.overMapCompareIso`.**  This is only that the passage between the two
models is a functor: `AlgebraicGeometry.RingedSite.restrictDerivedHom` is by definition a
three-fold composite. -/
theorem overMapCompareIso_conj (S : LocallyGiven X) {O : Opens X.carrier}
    (K L : OpenDerivedCategory X O) {T W : Opens X.carrier} (hTW : T ≤ W) (hWO : W ≤ O)
    (phi : (S.restriction W O hWO).obj K ⟶ (S.restriction W O hWO).obj L) :
    (overMapCompareIso K hTW).hom ≫
        ((SheafOfModules.overMap.{u} (underlyingRingSheaf X) hTW.hom).mapDerivedCategory ⋙
          (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory).map
            (homEquivSlice S K L hWO phi) ≫
        (overMapCompareIso L hTW).inv =
      (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory.map
        (RingedSite.restrictDerivedHom (Stacks.SheafOfModules.ringedSite X.sheaf) hTW.hom
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj L)
          (homEquivSlice S K L hWO phi)) :=
  map_comp_comp (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory
    ((RingedSite.overMapDerivedCategoryRestrictIso
      (Stacks.SheafOfModules.ringedSite X.sheaf) hTW.hom).inv.app
        ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K))
    ((SheafOfModules.overMap.{u} (underlyingRingSheaf X) hTW.hom).mapDerivedCategory.map
      (homEquivSlice S K L hWO phi))
    ((RingedSite.overMapDerivedCategoryRestrictIso
      (Stacks.SheafOfModules.ringedSite X.sheaf) hTW.hom).hom.app
        ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj L))

/-- **The coherence between the restriction of morphisms of Situation 0D67 and the restriction
of morphisms on the ringed site, granted the corresponding identification of the two
comparisons at the two objects involved.**

The morphism `φ` has been eliminated: what remains to be proved is the equation
`restrictionCompareIso S K hTW hWO ≪≫ (sliceRestrictOverRestrictionIso S hTW).app _ =
overMapCompareIso K hTW` between *isomorphisms*, which is natural in `K` and so reducible by
`CategoryTheory.Localization.natTrans_ext` to its instances at the class of a complex, where the
only non-formal ingredient is the triangle identity
`Stacks.DerivedGlueing.sliceExtendOverIso_hom_app_over`.

The passage between the two models of modules on `T` is faithful, so it is enough to check the
equation after applying it; on the one side that is
`Stacks.DerivedGlueing.sliceToSubspace_map_homEquivSlice_restrictHomBelow` and on the other
`Stacks.DerivedGlueing.overMapCompareIso_conj`, and the two are matched by
`Stacks.DerivedGlueing.conj_eq_conj_of_iso`. -/
theorem restrictHomBelow_eq_restrictDerivedHom_of_compareIso (S : LocallyGiven X)
    {O : Opens X.carrier} (K L : OpenDerivedCategory X O) {T W : Opens X.carrier}
    (hTW : T ≤ W) (hWO : W ≤ O)
    (hK : restrictionCompareIso S K hTW hWO ≪≫ (sliceRestrictOverRestrictionIso S hTW).app
        ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).mapDerivedCategory.obj
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)) =
      overMapCompareIso K hTW)
    (hL : restrictionCompareIso S L hTW hWO ≪≫ (sliceRestrictOverRestrictionIso S hTW).app
        ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).mapDerivedCategory.obj
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj L)) =
      overMapCompareIso L hTW)
    (phi : (S.restriction W O hWO).obj K ⟶ (S.restriction W O hWO).obj L) :
    homEquivSlice S K L (hTW.trans hWO) (restrictHomBelow S hTW hWO phi) =
      RingedSite.restrictDerivedHom (Stacks.SheafOfModules.ringedSite X.sheaf) hTW.hom
        ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)
        ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj L)
        (homEquivSlice S K L hWO phi) := by
  have := faithful_sliceToSubspace_mapDerivedCategory (underlyingRingSheaf X) T
  refine (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory.map_injective ?_
  refine (sliceToSubspace_map_homEquivSlice_restrictHomBelow S K L hTW hWO phi).trans ?_
  refine Eq.trans ?_ (overMapCompareIso_conj S K L hTW hWO phi)
  exact conj_eq_conj_of_iso (sliceRestrictOverRestrictionIso S hTW)
    (restrictionCompareIso S K hTW hWO) (overMapCompareIso K hTW)
    (restrictionCompareIso S L hTW hWO) (overMapCompareIso L hTW) hK hL
    (homEquivSlice S K L hWO phi)

end Derived

end Stacks.DerivedGlueing

end
