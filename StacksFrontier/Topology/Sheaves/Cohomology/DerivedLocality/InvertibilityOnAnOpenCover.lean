module

public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.SelfExtOnACollectionOfOpens
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology

/-!
# Invertibility in the derived category of modules is local on an open cover

Let `𝒪` be a sheaf of rings on a topological space `X` and let `U : ι → Opens X` be a family of
opens with `⨆ i, U i = ⊤`.  A morphism of `D(𝒪)` is invertible as soon as its restriction to
each `U i` is invertible in the derived category of `𝒪|_{U i}`-modules.

## Main results

* `Stacks.Cohomology.isIso_stalk_of_isIso_jStar_map`: a morphism of sheaves of modules which
  becomes invertible after restriction to an open is invertible on every stalk at a point of
  that open.
* `Stacks.Cohomology.isIso_of_isIso_jStar_map_of_iSup_eq_top`: invertibility of a morphism of
  sheaves of modules is local on an open cover.
* `Stacks.Cohomology.isIso_of_isIso_jStar_mapDerivedCategory_map`: **the statement above**,
  invertibility in `D(𝒪)` over an arbitrary open cover.

## Route

Through stalks, and not through the slice site.  `DerivedCategory.isIso_iff` reduces
invertibility in `D(𝒪)` to invertibility of every homology map, which is a morphism of sheaves
of modules; `ExtensionByZeroModules.isIso_of_stalk_isIso` reduces that to the stalks; and
`TopCat.Presheaf.isIso_stalkFunctor_map_whiskerLeft_iff` identifies the stalk at a point of `U`
of the restriction with the stalk at that point of the original sheaf, which is what turns the
hypothesis at `U i` into the stalk statement at the points of `U i`.  The passage between the
derived level and the homology level is
`CategoryTheory.Functor.isIso_mapDerivedCategory_map_iff`, available because restriction is
exact (`Stacks.ExtensionByZero.jStar_additive_and_exact`).

Two other statements of this shape are already in the library, and neither is this one:

* `Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory` and the near-duplicate
  `Stacks.Cohomology.isIso_of_isIso_mapDerivedCategory_overFunctor` are the statement on an
  arbitrary site, with restriction taken to the *slice* site over a member of a covering family,
  i.e. with `CategoryTheory.SheafOfModules.overFunctor` in place of
  `ExtensionByZeroModules.jStar`.  Deducing the present statement from them would need the
  identification of modules on the slice site `Opens X / U` with modules on the open subspace
  `U`, through `CategoryTheory.GrothendieckTopology.overPullback`; that identification exists
  (`AlgebraicGeometry.RingedSpace.restrictModulesIsoOverComp` is one instance of it), but it is
  attached to a *third* spelling of restriction, so the bridge costs more than the proof.
* `Stacks.Cohomology.PushforwardRestriction.isIso_derived_of_isIso_restrictions_on_cover` is
  the present statement for a *two-open* cover, privately, in
  `StacksFrontier/Topology/Sheaves/Cohomology/SupportedComplexes/PushforwardAndRestriction.lean`;
  it is the `ι = Bool` case of the theorem below, by the same proof.  Its three steps are what
  is generalized here.

The hypotheses `[∀ i, …]` on restriction are not a weakening: all three are theorems for every
open.  `ExtensionByZeroModules.jStar_additive` and the two exactness instances
`ExtensionByZeroModules.jStar_preservesFiniteLimits` and
`ExtensionByZeroModules.jStar_preservesFiniteColimits` are global instances, which is why
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedCategory/SelfExtOnACollectionOfOpens.lean` is
imported above: with it a consumer needs to supply none of them, and without it each consumer
would have to re-derive them from `Stacks.ExtensionByZero.jStar_additive_and_exact` by hand.
They appear as binders at all only because `CategoryTheory.Functor.mapDerivedCategory` needs
them in order for the statement to be typed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open ExtensionByZeroModules

universe w u

namespace Stacks.Cohomology

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- **A morphism of sheaves of modules invertible after restriction to `V` is invertible on the
stalks at the points of `V`.**

On underlying abelian presheaves, restriction to `V` is precomposition with the functor on opens
induced by the inclusion (`ExtensionByZeroModules.toAb_jStar_map`), and the stalk at a point of
`V` of such a precomposition is the stalk at that point of the original presheaf
(`TopCat.Presheaf.isIso_stalkFunctor_map_whiskerLeft_iff`). -/
theorem isIso_stalk_of_isIso_jStar_map (V : Opens X)
    {M N : SheafOfModules.{u} O} (f : M ⟶ N)
    (hf : IsIso ((jStar V O).map f)) (x : X) (hx : x ∈ V) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((toAb O).map f)) := by
  have hab : IsIso ((toAb (resRing V O)).map ((jStar V O).map f)) := Functor.map_isIso _ _
  have hrestr : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
      (⟨x, hx⟩ : Usp V)).map
        (Functor.whiskerLeft (TopCat.Presheaf.imF V).op ((toAb O).map f))) := by
    rw [← toAb_jStar_map V O f]
    exact @Functor.map_isIso _ _ _ _ _ _ _ _ hab
  exact (TopCat.Presheaf.isIso_stalkFunctor_map_whiskerLeft_iff V _ _
    ((toAb O).map f) ⟨x, hx⟩).mp hrestr

/-- **Invertibility of a morphism of sheaves of modules is local on an open cover.**  If
`⨆ i, U i = ⊤` and `f` becomes invertible after restriction to each `U i`, then `f` is
invertible.

Every point lies in some `U i`, so `isIso_stalk_of_isIso_jStar_map` gives invertibility on every
stalk, and `ExtensionByZeroModules.isIso_of_stalk_isIso` concludes. -/
theorem isIso_of_isIso_jStar_map_of_iSup_eq_top {ι : Type*} (U : ι → Opens X)
    (hU : iSup U = ⊤) {M N : SheafOfModules.{u} O} (f : M ⟶ N)
    (h : ∀ i, IsIso ((jStar (U i) O).map f)) : IsIso f := by
  refine isIso_of_stalk_isIso O f fun x => ?_
  have hx : x ∈ iSup U := hU ▸ Opens.mem_top x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact isIso_stalk_of_isIso_jStar_map O (U i) f (h i) x hi

/-- **Invertibility in the derived category of modules is local on an open cover.**  Let `𝒪` be a
sheaf of rings on a topological space `X`, let `U : ι → Opens X` satisfy `⨆ i, U i = ⊤`, and let
`f` be a morphism of `D(𝒪)` whose restriction to each `U i` is invertible in
`D(𝒪|_{U i})`.  Then `f` is invertible.

The index type is arbitrary and no hypothesis is placed on `X`, on `𝒪` or on the two objects.
This is the indexed, open-subspace form of the locality statement; see the module documentation
for the two statements it is *not*. -/
theorem isIso_of_isIso_jStar_mapDerivedCategory_map {ι : Type*} (U : ι → Opens X)
    (hU : iSup U = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u} O)]
    [∀ i, HasDerivedCategory.{w} (SheafOfModules.{u} (resRing (U i) O))]
    [∀ i, (jStar (U i) O).Additive]
    [∀ i, PreservesFiniteLimits (jStar (U i) O)]
    [∀ i, PreservesFiniteColimits (jStar (U i) O)]
    {E F : DerivedCategory (SheafOfModules.{u} O)} (f : E ⟶ F)
    (h : ∀ i, IsIso ((jStar (U i) O).mapDerivedCategory.map f)) : IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_isIso_jStar_map_of_iSup_eq_top O U hU _ fun i => ?_
  exact ((jStar (U i) O).isIso_mapDerivedCategory_map_iff f).mp (h i) n

end Stacks.Cohomology

end
