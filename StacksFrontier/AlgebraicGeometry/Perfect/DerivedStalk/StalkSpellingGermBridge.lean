module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMate
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkSpellingFunctorBridge

/-!
# The two spellings of the germ map of a pushforward, identified

For a morphism of schemes `f : X ⟶ Y` and a point `x` of `X`, the comparison map on stalks

`(f_*M)_{f x} ⟶ M_x`,  `germ_{f x} s ↦ germ_x s`,

is underlyingly `TopCat.Presheaf.stalkPushforward` of the presheaves of abelian groups, and it is
constructed twice in the library, over two different spellings of the stalk ring:

* `Stacks.ModuleSkyscraper.pushStalkMap`, over the **local ring** `𝒪_{X,x}`, as a morphism of
  functors `f_* ⋙ (−)_{f x} ⟶ (−)_x ⋙ restrictScalars (f^♯_x)`.  It is the mate of the stalk
  formula of Tag 0098 under `f^* ⊣ f_*`, so it is the spelling in which the comparison is tied to
  the pullback-pushforward adjunction — `Stacks.ModuleSkyscraper.pushStalkMap_germ` identifies it
  as the germ map and
  `Stacks.ModuleSkyscraper.extendScalars_map_pushStalkMap_comp_counit` is the compatibility with
  the counit that the derived theory consumes.
* `Stacks.ClosedImmersion.stalkPushforwardModuleMap`, over the **`RingCat`-valued stalk** of the
  sheaf of rings, with its germ formula
  `Stacks.ClosedImmersion.stalkPushforwardModuleMap_germ`.  It is the spelling in which the
  comparison is known to be *invertible* on the image of a closed embedding
  (`Stacks.ClosedImmersion.isIso_stalkPushforwardModuleMap`) and the one that the closed-immersion
  computation of a derived pushforward stalk descends from.

No lemma related the two, so the counit compatibility and the invertibility could not be used in a
single chain.  This file identifies them.

## Main definitions

* `AlgebraicGeometry.restrictScalarsStalkPushforwardMap`: the `RingCat`-stalk comparison map read
  in the local-ring spelling, by `AlgebraicGeometry.restrictScalarsStalkObjIso` at both points and
  `AlgebraicGeometry.restrictScalarsStalkMapSquareIso` on the germ square.
* `AlgebraicGeometry.restrictScalarsStalkPushforwardIso`: the same as an isomorphism, when the
  underlying continuous map is inducing.
* `AlgebraicGeometry.pushStalkFunctorIso`: `Stacks.ModuleSkyscraper.pushStalkMap` as an
  isomorphism of functors.

## Main results

* `AlgebraicGeometry.pushStalkMap_app_eq_restrictScalarsStalkPushforwardMap`: **the two spellings
  agree.**  At every sheaf of modules `M`, the local-ring comparison map is the `RingCat`-stalk
  comparison map read in the local-ring spelling.
* `AlgebraicGeometry.restrictScalarsStalkObjIso_hom_comp_pushStalkMap_app`: the same equality with
  the comparison of stalk rings moved to the other side, which is the form a consumer travelling
  along the `RingCat`-spelled chain rewrites with.
* `AlgebraicGeometry.restrictScalarsStalkPushforwardMap_germ`: the identified map is the germ map.
* `AlgebraicGeometry.restrictScalarsStalkPushforwardMap_naturality`: it is natural in `M`.
* `AlgebraicGeometry.isIso_pushStalkMap`: **the local-ring comparison map is invertible** whenever
  the underlying continuous map is inducing — in particular for a closed immersion,
  `AlgebraicGeometry.isIso_pushStalkMap_of_isClosedImmersion`.  This is the invertibility of the
  `RingCat` spelling transported across the identification; it was not available on the local-ring
  side at all.
* `AlgebraicGeometry.extendScalars_map_restrictScalarsStalkPushforwardMap_comp_counit`: **the
  counit compatibility, restated for the `RingCat`-stalk comparison map.**  This is the point of
  the identification: the compatibility of the stalk formula with `f^* ⊣ f_*` was available only
  for `pushStalkMap`, while the pushforward step of the chain Tag 0E23 needs descends from
  `stalkPushforwardModuleMap`, so the two halves could not be composed.

## Implementation notes

*The proof is stalk extensionality on germs.*  A morphism out of a stalk is determined by its
values on germs, because every element of a stalk is a germ
(`TopCat.Presheaf.exists_germ_eq`).  Both maps have a germ formula, and the two formulas say the
same thing, so one `obtain` and the two formulas close the identification.  Nothing about either
construction is unfolded: the mate construction behind `pushStalkMap` is reached only through
`Stacks.ModuleSkyscraper.pushStalkMap_germ`.

*Why the three comparison isomorphisms cost nothing.*  `restrictScalarsStalkObjIso` is the
identity on underlying abelian groups, and both halves of `restrictScalarsStalkMapSquareIso` are
`ModuleCat.restrictScalarsComp'`, whose components are also the identity on carriers.  So the
composite defining `restrictScalarsStalkPushforwardMap`, applied to an element, *is*
`stalkPushforwardModuleMap` applied to it, and the germ formula of the latter applies to the
former with no transport.  The same accounts for `restrictScalarsStalkPushforwardIso_hom` holding
by `rfl`.

*Why invertibility is phrased through `IsIso` of the components.*  The two categories
`X.Modules` and `SheafOfModules X.ringCatSheaf` carry instance paths that are definitionally but
not reducibly equal, so a statement about a *component of a composite of morphisms of functors* is
not rewritable by a consumer.  `CategoryTheory.NatIso.isIso_of_isIso_app` turns the pointwise
statement into invertibility of the morphism of functors without any whiskering appearing in a
statement, and `pushStalkFunctorIso` then names the isomorphism so that a consumer whiskers it
rather than reassociating it.

*What this does not do.*  It is the underived identification.  Carrying it to the derived
categories — comparing
`AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing` with the derived image of
`pushStalkFunctorIso` — is a further step, and nothing here is tagged: Tag 0E23 asserts that a
base change comparison map is an isomorphism, and this is one input to that.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction

noncomputable section

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)

/-! ### The `RingCat`-stalk comparison map, read in the local-ring spelling -/

/-- **The comparison `(f_*M)_{f x} ⟶ M_x` of the `RingCat`-stalk spelling, read over the local
rings.**  `Stacks.ClosedImmersion.stalkPushforwardModuleMap` is a map of modules over the
`RingCat`-valued stalk of the sheaf of rings; restricting scalars along
`AlgebraicGeometry.ringCatStalkRingEquiv` at `f x` and moving the result across
`AlgebraicGeometry.restrictScalarsStalkObjIso` at both points and
`AlgebraicGeometry.restrictScalarsStalkMapSquareIso` on the germ square presents it as a map of
`𝒪_{Y,f x}`-modules of exactly the type of `Stacks.ModuleSkyscraper.pushStalkMap`.

It *is* that map, by `pushStalkMap_app_eq_restrictScalarsStalkPushforwardMap`. -/
def restrictScalarsStalkPushforwardMap (M : X.Modules) :
    (Stacks.ModuleSkyscraper.modulesStalkFunctor Y (f.base x)).obj
        ((Scheme.Modules.pushforward f).obj M) ⟶
      (ModuleCat.restrictScalars.{u, u, u} (f.stalkMap x).hom).obj
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj M) :=
  (restrictScalarsStalkObjIso (f.base x) ((Scheme.Modules.pushforward f).obj M)).inv ≫
    (ModuleCat.restrictScalars.{u, u, u}
        (ringCatStalkRingEquiv (f.base x)).symm.toRingHom).map
      (Stacks.ClosedImmersion.stalkPushforwardModuleMap f.toLRSHom.toShHom x M) ≫
    (restrictScalarsStalkMapSquareIso f x).hom.app
      (AlgebraicGeometry.SheafOfModules.stalkObj X.ringCatSheaf x M) ≫
    (ModuleCat.restrictScalars.{u, u, u} (f.stalkMap x).hom).map
      (restrictScalarsStalkObjIso x M).hom

/-! ### The identification -/

/-- **The two spellings of the germ map agree.**  The mate of the stalk formula of Tag 0098 under
`f^* ⊣ f_*`, taken over the local ring `𝒪_{X,x}`, is the `RingCat`-stalk comparison map read over
the local rings.

A morphism out of a stalk is determined by its values on germs, every element of a stalk is a
germ by `TopCat.Presheaf.exists_germ_eq`, and on a germ the two maps agree by their two germ
formulas, `Stacks.ModuleSkyscraper.pushStalkMap_germ` and
`Stacks.ClosedImmersion.stalkPushforwardModuleMap_germ`. -/
theorem pushStalkMap_app_eq_restrictScalarsStalkPushforwardMap (M : X.Modules) :
    (Stacks.ModuleSkyscraper.pushStalkMap f x).app M =
      restrictScalarsStalkPushforwardMap f x M := by
  refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
  obtain ⟨V, hV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    ((Scheme.Modules.pushforward f).obj M).presheaf s
  rw [Stacks.ModuleSkyscraper.pushStalkMap_germ f x M V hV t]
  exact (Stacks.ClosedImmersion.stalkPushforwardModuleMap_germ
    f.toLRSHom.toShHom x M V hV t).symm

/-- The identification with the comparison of stalk rings moved to the other side: travelling
along the `RingCat`-spelled chain and then into the local-ring spelling is passing into the
local-ring spelling and then applying `Stacks.ModuleSkyscraper.pushStalkMap`.

This is the orientation in which the identification is used, since the chain the derived theory
builds runs through the `RingCat` spelling. -/
theorem restrictScalarsStalkObjIso_hom_comp_pushStalkMap_app (M : X.Modules) :
    (restrictScalarsStalkObjIso (f.base x) ((Scheme.Modules.pushforward f).obj M)).hom ≫
        (Stacks.ModuleSkyscraper.pushStalkMap f x).app M =
      (ModuleCat.restrictScalars.{u, u, u}
          (ringCatStalkRingEquiv (f.base x)).symm.toRingHom).map
        (Stacks.ClosedImmersion.stalkPushforwardModuleMap f.toLRSHom.toShHom x M) ≫
      (restrictScalarsStalkMapSquareIso f x).hom.app
        (AlgebraicGeometry.SheafOfModules.stalkObj X.ringCatSheaf x M) ≫
      (ModuleCat.restrictScalars.{u, u, u} (f.stalkMap x).hom).map
        (restrictScalarsStalkObjIso x M).hom :=
  (Iso.eq_inv_comp _).mp (pushStalkMap_app_eq_restrictScalarsStalkPushforwardMap f x M)

/-- **The identified map is the germ map.**  A section `s` of `M` over `f⁻¹V` is a section of
`f_*M` over `V`; its germ at `f x` is sent to its germ at `x`. -/
theorem restrictScalarsStalkPushforwardMap_germ (M : X.Modules) (V : Y.Opens)
    (hx : f.base x ∈ V) (s : Γ(M, f ⁻¹ᵁ V)) :
    (restrictScalarsStalkPushforwardMap f x M)
        ((((Scheme.Modules.pushforward f).obj M).presheaf.germ V (f x) hx) s)
      = (M.presheaf.germ (f ⁻¹ᵁ V) x hx) s :=
  (pushStalkMap_app_eq_restrictScalarsStalkPushforwardMap f x M) ▸
    Stacks.ModuleSkyscraper.pushStalkMap_germ f x M V hx s

/-- **The identified map is natural in `M`.**  This is the naturality of
`Stacks.ModuleSkyscraper.pushStalkMap`, which is a morphism of functors, transported across the
identification. -/
theorem restrictScalarsStalkPushforwardMap_naturality {M N : X.Modules} (φ : M ⟶ N) :
    (Stacks.ModuleSkyscraper.modulesStalkFunctor Y (f.base x)).map
          ((Scheme.Modules.pushforward f).map φ) ≫
        restrictScalarsStalkPushforwardMap f x N =
      restrictScalarsStalkPushforwardMap f x M ≫
        (ModuleCat.restrictScalars.{u, u, u} (f.stalkMap x).hom).map
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).map φ) := by
  simp only [← pushStalkMap_app_eq_restrictScalarsStalkPushforwardMap]
  exact (Stacks.ModuleSkyscraper.pushStalkMap f x).naturality φ

/-! ### Invertibility, transported to the local-ring spelling -/

/-- **The comparison map, as an isomorphism over the local rings.**  For a morphism of schemes
whose underlying continuous map is inducing — a closed immersion, for instance — the stalk of
`f_*M` at `f x` is the stalk of `M` at `x` with scalars restricted along `𝒪_{Y,f x} ⟶ 𝒪_{X,x}`.

Invertibility is `Stacks.ClosedImmersion.stalkPushforwardModuleIso`; the other three factors are
isomorphisms of stalk spellings. -/
def restrictScalarsStalkPushforwardIso
    (hi : Topology.IsInducing (ConcreteCategory.hom f.toLRSHom.toShHom.hom.base))
    (M : X.Modules) :
    (Stacks.ModuleSkyscraper.modulesStalkFunctor Y (f.base x)).obj
        ((Scheme.Modules.pushforward f).obj M) ≅
      (ModuleCat.restrictScalars.{u, u, u} (f.stalkMap x).hom).obj
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj M) :=
  (restrictScalarsStalkObjIso (f.base x) ((Scheme.Modules.pushforward f).obj M)).symm ≪≫
    (ModuleCat.restrictScalars.{u, u, u}
        (ringCatStalkRingEquiv (f.base x)).symm.toRingHom).mapIso
      (Stacks.ClosedImmersion.stalkPushforwardModuleIso f.toLRSHom.toShHom x hi M) ≪≫
    (restrictScalarsStalkMapSquareIso f x).app
      (AlgebraicGeometry.SheafOfModules.stalkObj X.ringCatSheaf x M) ≪≫
    (ModuleCat.restrictScalars.{u, u, u} (f.stalkMap x).hom).mapIso
      (restrictScalarsStalkObjIso x M)

/-- The isomorphism is the map: `Stacks.ClosedImmersion.stalkPushforwardModuleIso` is `asIso` of
`Stacks.ClosedImmersion.stalkPushforwardModuleMap`, and the three spelling isomorphisms enter both
sides the same way, so the two are the same term. -/
theorem restrictScalarsStalkPushforwardIso_hom
    (hi : Topology.IsInducing (ConcreteCategory.hom f.toLRSHom.toShHom.hom.base))
    (M : X.Modules) :
    (restrictScalarsStalkPushforwardIso f x hi M).hom =
      restrictScalarsStalkPushforwardMap f x M := rfl

/-- `restrictScalarsStalkPushforwardMap` is invertible when the underlying continuous map is
inducing. -/
theorem isIso_restrictScalarsStalkPushforwardMap
    (hi : Topology.IsInducing (ConcreteCategory.hom f.toLRSHom.toShHom.hom.base))
    (M : X.Modules) : IsIso (restrictScalarsStalkPushforwardMap f x M) := by
  rw [← restrictScalarsStalkPushforwardIso_hom f x hi M]
  infer_instance

/-- **`Stacks.ModuleSkyscraper.pushStalkMap` is invertible at every `M`**, when the underlying
continuous map of `f` is inducing.  This is the invertibility of the `RingCat`-stalk spelling
carried across the identification; the local-ring spelling had none. -/
theorem isIso_pushStalkMap_app
    (hi : Topology.IsInducing (ConcreteCategory.hom f.toLRSHom.toShHom.hom.base))
    (M : X.Modules) : IsIso ((Stacks.ModuleSkyscraper.pushStalkMap f x).app M) := by
  rw [pushStalkMap_app_eq_restrictScalarsStalkPushforwardMap]
  exact isIso_restrictScalarsStalkPushforwardMap f x hi M

/-- **`Stacks.ModuleSkyscraper.pushStalkMap` is an isomorphism of functors**, when the underlying
continuous map of `f` is inducing.  A morphism of functors invertible at every object is
invertible, by `CategoryTheory.NatIso.isIso_of_isIso_app`. -/
theorem isIso_pushStalkMap
    (hi : Topology.IsInducing (ConcreteCategory.hom f.toLRSHom.toShHom.hom.base)) :
    IsIso (Stacks.ModuleSkyscraper.pushStalkMap f x) :=
  have := isIso_pushStalkMap_app f x hi
  NatIso.isIso_of_isIso_app _

/-- `isIso_pushStalkMap` for a closed immersion of schemes, where the inducing hypothesis is
discharged by `Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom`. -/
theorem isIso_pushStalkMap_of_isClosedImmersion [AlgebraicGeometry.IsClosedImmersion f] :
    IsIso (Stacks.ModuleSkyscraper.pushStalkMap f x) :=
  isIso_pushStalkMap f x (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom f).isInducing

/-- **The stalk of a pushforward on the image, over the local rings, as an isomorphism of
functors.**  `f_* ⋙ (−)_{f x} ≅ (−)_x ⋙ restrictScalars (f^♯_x)`, by the germ map.

This is the local-ring counterpart of
`Stacks.ClosedImmersion.stalkPushforwardModuleFunctorIso`, and it is the form in which the
computation enters a diagram alongside `Stacks.ModuleSkyscraper.pullbackStalkIso`, which lives
over the local rings. -/
def pushStalkFunctorIso
    (hi : Topology.IsInducing (ConcreteCategory.hom f.toLRSHom.toShHom.hom.base)) :
    Scheme.Modules.pushforward f ⋙ Stacks.ModuleSkyscraper.modulesStalkFunctor Y (f.base x) ≅
      Stacks.ModuleSkyscraper.modulesStalkFunctor X x ⋙
        ModuleCat.restrictScalars.{u, u, u} (f.stalkMap x).hom :=
  haveI := isIso_pushStalkMap f x hi
  asIso (Stacks.ModuleSkyscraper.pushStalkMap f x)

/-- `pushStalkFunctorIso` is `Stacks.ModuleSkyscraper.pushStalkMap`. -/
theorem pushStalkFunctorIso_hom
    (hi : Topology.IsInducing (ConcreteCategory.hom f.toLRSHom.toShHom.hom.base)) :
    (pushStalkFunctorIso f x hi).hom = Stacks.ModuleSkyscraper.pushStalkMap f x := rfl

/-! ### The counit compatibility, restated for the `RingCat`-stalk comparison map -/

/-- **The two counits correspond, for the `RingCat`-stalk comparison map.**  Taking the stalk at
`x` of the counit `f^*(f_*M) ⟶ M` of `f^* ⊣ f_*` and transporting along the stalk formula of
Tag 0098 gives the counit of `extendScalars (f^♯_x) ⊣ restrictScalars (f^♯_x)` at `M_x`,
precomposed with `extendScalars` of the `RingCat`-stalk comparison map read over the local rings.

This is `Stacks.ModuleSkyscraper.extendScalars_map_pushStalkMap_comp_counit` after the
identification, and it is what the identification is for: the compatibility of the stalk formula
with the pullback-pushforward adjunction was stated only for
`Stacks.ModuleSkyscraper.pushStalkMap`, while the pushforward step of the chain of isomorphisms
Tag 0E23 needs descends from `Stacks.ClosedImmersion.stalkPushforwardModuleMap`. -/
theorem extendScalars_map_restrictScalarsStalkPushforwardMap_comp_counit (M : X.Modules) :
    (ModuleCat.extendScalars (f.stalkMap x).hom).map
          (restrictScalarsStalkPushforwardMap f x M) ≫
        (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).counit.app
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj M) =
      (Stacks.ModuleSkyscraper.pullbackStalkIso f x).hom.app
          ((Scheme.Modules.pushforward f).obj M) ≫
        (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M) :=
  (pushStalkMap_app_eq_restrictScalarsStalkPushforwardMap f x M) ▸
    Stacks.ModuleSkyscraper.extendScalars_map_pushStalkMap_comp_counit f x M

end AlgebraicGeometry

end

end
