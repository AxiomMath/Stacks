module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ObjectRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatCohomologyCounit

/-!
# The restriction comparison of [Stacks, Tag 0756] clause (2), sectionwise

Clause (2) of [Stacks, Tag 0756] asserts that a canonical map

  `g^*_{τ,small}(𝒢|_{S_τ}) ⟶ 𝒢|_{U_τ}`

is an isomorphism for every flat, locally finitely presented `g : U → S`.  At `τ = Zar` that map
is the adjoint transpose, under
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`, of a *restriction comparison*
`𝒢|_{S_Zar} ⟶ g_*(𝒢|_{U_Zar})`.  Sectionwise, the restriction comparison is the pushforward of
sheaves of modules applied to a natural transformation of the two functors that take an open of
`S` into the big fppf site over `S`:

  `V ↦ (g^{-1}V ↪ X → S)`  and  `V ↦ (V ↪ S)`.

This file supplies that natural transformation and the structure-sheaf compatibility it has to
satisfy before `CategoryTheory.SheafOfModules.pushforwardNatTrans` can be applied to it.  Those
two are the geometric and the ring-level content of the construction, and with them the
transpose is assembled here: `AlgebraicGeometry.BigFppfOver.zariskiBaseChangeMap`.  The canonical
map itself, defined as the base-change map of the square of ringed sites, is
`AlgebraicGeometry.BigFppfOver.zariskiClause2Map`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.objPreimageObj`: the object `(g^{-1}V ↪ X → S)` of the big fppf
  site over `S` attached to an open `V` of `S` and an object `T` of that site with scheme `X` and
  structure morphism `g : X ⟶ S`.
* `AlgebraicGeometry.BigFppfOver.objPreimageHom`: **the projection
  `(g^{-1}V ↪ X → S) ⟶ (V ↪ S)`**, the restriction `g|_{g^{-1}V} : g^{-1}V ⟶ V` of `g` read in
  the big fppf site.
* `AlgebraicGeometry.BigFppfOver.objPreimageFunctor` and
  `AlgebraicGeometry.BigFppfOver.objPreimageNatTrans`: **the natural transformation
  `(V ↦ (g^{-1}V ↪ X → S)) ⟶ (V ↦ (V ↪ S))`** of functors `Opens S ⥤ (Sch/S)_fppf`.
* `AlgebraicGeometry.BigFppfOver.objZariskiPushforward`: `𝒢 ↦ 𝒢|_{X_Zar}`, the pushforward of
  sheaves of modules along `W ↦ (W ↪ X → S)`.
* `AlgebraicGeometry.BigFppfOver.objPreimageRestrictionComparison` and
  `AlgebraicGeometry.BigFppfOver.objZariskiRestrictionComparison`: **the restriction comparison
  `𝒢|_{S_Zar} ⟶ g_*(𝒢|_{X_Zar})`**, first as the pushforward along the natural transformation and
  then with its target rewritten as a pushforward along `g`.
* `AlgebraicGeometry.BigFppfOver.zariskiBaseChangeMap`: the adjoint transpose
  `g^*(𝒢|_{S_Zar}) ⟶ 𝒢|_{X_Zar}` of the sectionwise restriction comparison under
  `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.homOfLE_comp_resLE`: the restriction of a morphism of schemes to
  preimages of opens is natural in the open.
* `AlgebraicGeometry.BigFppfOver.structureMap_comp_objPreimageHom`: **the structure-sheaf
  compatibility**.  Over an open `V` of `S` the two routes

      `Γ(V, 𝒪_S) → Γ(S|_V, 𝒪) → Γ(X|_{g^{-1}V}, 𝒪)`   (comparison of `S`, then the projection)
      `Γ(V, 𝒪_S) → Γ(g^{-1}V, 𝒪_X) → Γ(X|_{g^{-1}V}, 𝒪)`   (`g^♯`, then the comparison of `X`)

  agree.  This is the square that
  `CategoryTheory.SheafOfModules.pushforwardNatTrans` consumes.
* `AlgebraicGeometry.BigFppfOver.isContinuous_objPreimageFunctor`: `V ↦ (g^{-1}V ↪ X → S)` is
  continuous, so there is a pushforward of sheaves of modules along it.
* `AlgebraicGeometry.BigFppfOver.objPreimageStructureMap_eq`: the two readings of the
  structure-sheaf comparison along `V ↦ (g^{-1}V ↪ X → S)` agree, which is what lets the target of
  the restriction comparison be rewritten as a pushforward along `g`.
* `AlgebraicGeometry.BigFppfOver.objZariskiRestrictIso`: the pushforward along
  `W ↦ (W ↪ X → S)` is `objRestrict ⋙ restrictModule`, so `𝒢|_{X_Zar}` here is the same
  `𝒢|_{X_Zar}` as in `AlgebraicGeometry.BigFppfOver.objZariskiRestrict`, which
  `AlgebraicGeometry.BigFppfOver.zariskiComparisonRestrictIso` is stated with.

## Implementation notes

The ring-level content is entirely `AlgebraicGeometry.Scheme.Opens.topIso_inv_appTop_of_comp`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/ObjectRestriction.lean`): restriction
along a morphism of schemes commutes with the identification `Γ(Y, V) ≅ Γ(V, 𝒪_V)`.  Both
structure-sheaf comparisons of the big fppf site are that identification
(`AlgebraicGeometry.BigFppfOver.structureMap_hom_app`), and the restriction map of the structure
sheaf along a morphism of the site is `Scheme.Hom.appTop` of the underlying morphism of schemes,
so the square is that lemma pushed through `CategoryTheory.forget₂ CommRingCat RingCat`.

The projection is built from `AlgebraicGeometry.Scheme.Hom.resLE` rather than from a fibre
product: `g^{-1}V` *is* the fibre product `X ×_S V` here, but the restriction presentation needs
no limit and makes both the over-condition and the naturality a one-line consequence of
`AlgebraicGeometry.Scheme.Hom.resLE_comp_ι`.

The two spellings of the structure map along `V ↦ (g^{-1}V ↪ X → S)` are kept apart on purpose:
`AlgebraicGeometry.BigFppfOver.objPreimageStructureMap` is what
`CategoryTheory.SheafOfModules.pushforwardNatTrans` produces, and
`AlgebraicGeometry.BigFppfOver.objPreimageCompStructureMap` is what the composite of two
`CategoryTheory.SheafOfModules.pushforwardComp`s produces.  Only their *equality* is a theorem;
each pushforward functor is then available in whichever spelling its consumer needs, and the
restriction comparison is transported between them by
`CategoryTheory.SheafOfModules.pushforwardCongr`.

The instance bridges `AlgebraicGeometry.BigFppfOver.isContinuous_overMap_objHom` and the
`haveI` inside `AlgebraicGeometry.BigFppfOver.objZariskiRestrictIsoOfEq` are `inferInstanceAs`
restatements of instances Mathlib already has, for the reason recorded on
`AlgebraicGeometry.BigFppfOver.isContinuous_iteratedSliceBackward`: the topologies carry a
`B.Contains` proof that unification cannot recover at the transparency instance search uses, so
`AlgebraicGeometry.BigFppfOver.topology B X hX` and `B.topology.over T.left` are the same
topology that instance search cannot match.

`AlgebraicGeometry.BigFppfOver.zariskiBaseChangeMap_eq`
(`StacksFrontier/AlgebraicGeometry/Descent/Parasitic/FlatCohomologyBaseChangeFactor.lean`) identifies
`AlgebraicGeometry.BigFppfOver.zariskiBaseChangeMap` with the canonical map
`AlgebraicGeometry.BigFppfOver.zariskiClause2Map` followed by
`AlgebraicGeometry.BigFppfOver.objZariskiRestrictIso`.  Nothing here carries a `stacks`
attribute.

## References

* [Stacks Project, Tag 0756](https://stacks.math.columbia.edu/tag/0756)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The restriction of a morphism of schemes to preimages of opens is natural in the open.**
For `f : X ⟶ Y` and `V ≤ W` opens of `Y`, including `f^{-1}V` into `f^{-1}W` and then
restricting `f` over `W` is restricting `f` over `V` and then including `V` into `W`.

Both sides are morphisms `f^{-1}V ⟶ W`, and `W.ι` is a monomorphism, so it is enough to compare
the composites with it; each is `(f^{-1}V).ι ≫ f` by
`AlgebraicGeometry.Scheme.Hom.resLE_comp_ι`. -/
public theorem Scheme.Hom.homOfLE_comp_resLE {X Y : Scheme.{u}} (f : X ⟶ Y) {V W : Y.Opens}
    (h : V ≤ W) (h' : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ W) :
    X.homOfLE h' ≫ f.resLE W (f ⁻¹ᵁ W) le_rfl =
      f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ Y.homOfLE h := by
  rw [← cancel_mono W.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
    Scheme.homOfLE_ι, Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι]

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (T : BigFppfOver B S hS)

/-- **The object `(g^{-1}V ↪ X → S)`** of the big fppf site over `S`, for `V` an open of `S` and
`g : X ⟶ S` the structure morphism of `T`: the preimage of `V` in the scheme of `T`, read over
`S` through `T`. -/
public abbrev objPreimageObj (V : S.Opens) : BigFppfOver B S hS :=
  (Over.map T.hom).obj
    (opensObj B (objScheme B S hS T) (contains_objScheme B S hS T) (objHom B S hS T ⁻¹ᵁ V))

/-- **The projection `(g^{-1}V ↪ X → S) ⟶ (V ↪ S)`**, the restriction
`g|_{g^{-1}V} : g^{-1}V ⟶ V` of the structure morphism of `T` read as a morphism of the big fppf
site over `S`.  The over-condition is `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι`. -/
public def objPreimageHom (V : S.Opens) :
    objPreimageObj B S hS T V ⟶ opensObj B S hS V :=
  Over.homMk
    (ObjectProperty.homMk
      (X := B.obj (contains_opens B (contains_objScheme B S hS T) (objHom B S hS T ⁻¹ᵁ V)))
      (Y := B.obj (contains_opens B hS V))
      ((objHom B S hS T).resLE V (objHom B S hS T ⁻¹ᵁ V) le_rfl))
    (by
      apply ObjectProperty.hom_ext
      simp only [ObjectProperty.FullSubcategory.comp_hom, Over.map_obj_hom, opensObj_hom_hom]
      exact Scheme.Hom.resLE_comp_ι _ _)

/-- The underlying morphism of schemes of `AlgebraicGeometry.BigFppfOver.objPreimageHom` at `V`
is the restriction `g|_{g^{-1}V} : g^{-1}V ⟶ V`. -/
@[simp]
public theorem objPreimageHom_left_hom (V : S.Opens) :
    (objPreimageHom B S hS T V).left.hom =
      (objHom B S hS T).resLE V (objHom B S hS T ⁻¹ᵁ V) le_rfl := rfl

/-- The functor `V ↦ (g^{-1}V ↪ X → S)` from the opens of `S` to the big fppf site over `S`:
take the preimage in the scheme of `T`, read it in the big fppf site of that scheme, and push
along the structure morphism of `T`. -/
public abbrev objPreimageFunctor : S.Opens ⥤ BigFppfOver B S hS :=
  Opens.map (objHom B S hS T).base ⋙
    opensToBig B (objScheme B S hS T) (contains_objScheme B S hS T) ⋙ Over.map T.hom

/-- **The natural transformation `(V ↦ (g^{-1}V ↪ X → S)) ⟶ (V ↦ (V ↪ S))`** of functors from
the opens of `S` into the big fppf site over `S`, given at `V` by the projection
`AlgebraicGeometry.BigFppfOver.objPreimageHom`.  Naturality is
`AlgebraicGeometry.Scheme.Hom.homOfLE_comp_resLE`.

This is the natural transformation that
`CategoryTheory.SheafOfModules.pushforwardNatTrans` turns into the restriction comparison
`𝒢|_{S_Zar} ⟶ g_*(𝒢|_{X_Zar})` of clause (2) of [Stacks, Tag 0756]. -/
public def objPreimageNatTrans :
    objPreimageFunctor B S hS T ⟶ opensToBig B S hS where
  app V := objPreimageHom B S hS T V
  naturality V W h := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    simp only [Over.comp_left, ObjectProperty.FullSubcategory.comp_hom, Over.map_map_left,
      objPreimageHom_left_hom, opensToBig_map, opensHom_left_hom, opensToBig_obj,
      Functor.comp_map, Functor.comp_obj, opensHom_left_hom]
    exact Scheme.Hom.homOfLE_comp_resLE (objHom B S hS T) (leOfHom h) _

/-- **The structure-sheaf compatibility of the projection.**  Over an open `V` of `S`, the
comparison of structure sheaves of the big fppf site of `S` followed by restriction along the
projection `(g^{-1}V ↪ X → S) ⟶ (V ↪ S)` is `g^♯` followed by the comparison of structure
sheaves of the big fppf site of the scheme `X` of `T`:

    `Γ(V, 𝒪_S) → Γ(S|_V, 𝒪) → Γ(X|_{g^{-1}V}, 𝒪)`
      `=`
    `Γ(V, 𝒪_S) → Γ(g^{-1}V, 𝒪_X) → Γ(X|_{g^{-1}V}, 𝒪)`.

Both comparisons are the identification `Γ(Y, V) ≅ Γ(V, 𝒪_V)`
(`AlgebraicGeometry.BigFppfOver.structureMap_hom_app`) and the restriction map of the structure
sheaf is `Scheme.Hom.appTop` of the projection, so this is
`AlgebraicGeometry.Scheme.Opens.topIso_inv_appTop_of_comp` pushed through
`CategoryTheory.forget₂ CommRingCat RingCat`.

This is the square `CategoryTheory.SheafOfModules.pushforwardNatTrans` consumes for
`AlgebraicGeometry.BigFppfOver.objPreimageNatTrans`. -/
public theorem structureMap_comp_objPreimageHom (V : S.Opens) :
    (structureMap B S hS).hom.app (op V) ≫
        (structureSheaf B S hS).val.map (objPreimageHom B S hS T V).op =
      (objHom B S hS T).toRingCatSheafHom.hom.app (op V) ≫
        (structureMap B (objScheme B S hS T) (contains_objScheme B S hS T)).hom.app
          (op (objHom B S hS T ⁻¹ᵁ V)) := by
  have hcomm :
      ((objHom B S hS T).resLE V (objHom B S hS T ⁻¹ᵁ V) le_rfl) ≫ V.ι =
        (objHom B S hS T ⁻¹ᵁ V).ι ≫ objHom B S hS T :=
    Scheme.Hom.resLE_comp_ι _ _
  have hring := Scheme.Opens.topIso_inv_appTop_of_comp (objHom B S hS T) V
    ((objHom B S hS T).resLE V (objHom B S hS T ⁻¹ᵁ V) le_rfl) hcomm
  rw [structureMap_hom_app, structureMap_hom_app]
  exact (((forget₂ CommRingCat RingCat.{u}).map_comp _ _).symm.trans
    (congrArg (forget₂ CommRingCat RingCat.{u}).map hring)).trans
    ((forget₂ CommRingCat RingCat.{u}).map_comp _ _)

/-! ### The restriction comparison of clause (2) -/

section Comparison

/-- Pushing along the structure morphism of `T` is continuous for the localized fppf topologies.
This is Mathlib's instance for `CategoryTheory.Over.map`, restated at
`AlgebraicGeometry.BigFppfOver.topology`; instance search does not find it in that form, for the
reason recorded on `AlgebraicGeometry.BigFppfOver.isContinuous_iteratedSliceBackward`. -/
public instance isContinuous_overMap_objHom : (Over.map T.hom).IsContinuous
    (topology B (objScheme B S hS T) (contains_objScheme B S hS T)) (topology B S hS) :=
  inferInstanceAs ((Over.map T.hom).IsContinuous (B.topology.over T.left)
    (B.topology.over (B.obj hS)))

/-- The small Zariski site of the scheme of `T`, included in the big fppf site of that scheme and
pushed along the structure morphism of `T`, is continuous into the big fppf site over `S`. -/
public instance isContinuous_opensToBig_comp_overMap :
    (opensToBig B (objScheme B S hS T) (contains_objScheme B S hS T) ⋙
        Over.map T.hom).IsContinuous
      (Opens.grothendieckTopology ↥(objScheme B S hS T)) (topology B S hS) :=
  haveI := isContinuous_overMap_objHom B S hS T
  Functor.isContinuous_comp _ _ _
    (topology B (objScheme B S hS T) (contains_objScheme B S hS T)) _

/-- **`V ↦ (g^{-1}V ↪ X → S)` is continuous**, so sheaves of modules can be pushed forward along
it: the preimage functor on opens is continuous for the small Zariski topologies, and the rest is
`AlgebraicGeometry.BigFppfOver.isContinuous_opensToBig_comp_overMap`. -/
public instance isContinuous_objPreimageFunctor :
    (objPreimageFunctor B S hS T).IsContinuous
      (Opens.grothendieckTopology ↥S) (topology B S hS) :=
  haveI := isContinuous_opensToBig_comp_overMap B S hS T
  Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology ↥(objScheme B S hS T)) _

/-- The comparison of structure sheaves along `V ↦ (g^{-1}V ↪ X → S)`: the comparison of the big
fppf site of `S` followed by restriction along the projection.  By
`AlgebraicGeometry.BigFppfOver.structureMap_comp_objPreimageHom` this is also `g^♯` followed by
the comparison of the big fppf site of the scheme of `T`, which is the spelling the composite
`objRestrict ⋙ restrictModule ⋙ Scheme.Modules.pushforward` presents. -/
public def objPreimageStructureMap :
    S.ringCatSheaf ⟶
      ((objPreimageFunctor B S hS T).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥S) (topology B S hS)).obj (structureSheaf B S hS) :=
  structureMap B S hS ≫
    (Functor.sheafPushforwardContinuousNatTrans (objPreimageNatTrans B S hS T) RingCat.{u}
      (Opens.grothendieckTopology ↥S) (topology B S hS)).app (structureSheaf B S hS)

/-- **The restriction comparison `𝒢|_{S_Zar} ⟶ g_*(𝒢|_{X_Zar})` of clause (2) of
[Stacks, Tag 0756]**, natural in `𝒢`: over an open `V` of `S` it is restriction of sections of
`𝒢` along the projection `(g^{-1}V ↪ X → S) ⟶ (V ↪ S)`.

The target is written as the pushforward of sheaves of modules along
`AlgebraicGeometry.BigFppfOver.objPreimageFunctor`, which is what
`CategoryTheory.SheafOfModules.pushforwardNatTrans` produces.  It is the composite
`objRestrict ⋙ restrictModule ⋙ Scheme.Modules.pushforward g` — a threefold
`CategoryTheory.SheafOfModules.pushforwardComp` followed by a
`CategoryTheory.SheafOfModules.pushforwardCongr` along
`AlgebraicGeometry.BigFppfOver.structureMap_comp_objPreimageHom` — but **that identification is
not carried out here**, and so neither is the adjoint transpose that clause (2) is literally
about.  See the module documentation. -/
public def objPreimageRestrictionComparison :
    restrictModule B S hS ⟶ SheafOfModules.pushforward.{u} (objPreimageStructureMap B S hS T) :=
  SheafOfModules.pushforwardNatTrans (structureMap B S hS) (objPreimageNatTrans B S hS T)

/-- The restriction comparison is, on sections over an open `V` of `S`, restriction of sections
along the projection `(g^{-1}V ↪ X → S) ⟶ (V ↪ S)`. -/
@[simp]
public theorem objPreimageRestrictionComparison_app_val_app
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (V : (S.Opens)ᵒᵖ) (x) :
    ((objPreimageRestrictionComparison B S hS T).app G).val.app V x =
      G.val.map (objPreimageHom B S hS T V.unop).op x := rfl

/-! ### The base-change map of clause (2) -/

/-- The comparison of structure sheaves along `W ↦ (W ↪ X → S)`: the comparison of the big fppf
site of the scheme `X` of `T`, followed by the identification of the structure sheaf of the big
fppf site of `X` with the restriction along `Over.map` of the structure sheaf of the big fppf
site of `S`.  Both are the presheaf of global functions, so the identification is
`CategoryTheory.Sheaf.pushforwardOverMapIso`, which is the identity on sections. -/
public abbrev objZariskiStructureMap :
    (objScheme B S hS T).ringCatSheaf ⟶
      ((opensToBig B (objScheme B S hS T) (contains_objScheme B S hS T) ⋙
          Over.map T.hom).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥(objScheme B S hS T)) (topology B S hS)).obj
        (structureSheaf B S hS) :=
  SheafOfModules.comparisonComp
    (structureMap B (objScheme B S hS T) (contains_objScheme B S hS T))
    (Sheaf.pushforwardOverMapIso B.structureSheaf T.hom).inv

/-- **Restriction of a module on the big fppf site over `S` to the small Zariski site of the
scheme `X` of `T`**, `𝒢 ↦ 𝒢|_{X_Zar}`: the pushforward of sheaves of modules along
`W ↦ (W ↪ X → S)`. -/
public abbrev objZariskiPushforward :
    SheafOfModules.{u} (structureSheaf B S hS) ⥤ (objScheme B S hS T).Modules :=
  SheafOfModules.pushforward.{u} (objZariskiStructureMap B S hS T)

/-- **`𝒢 ↦ 𝒢|_{X_Zar}` through any functor equal to restriction along `Over.map`.**  For a functor
`F` from modules on the big fppf site over `S` to modules on the big fppf site of the scheme `X`
of `T` that is equal to `SheafOfModules.overMap` of the structure morphism, `F` followed by
restriction to the small Zariski site of `X` is the pushforward along `W ↦ (W ↪ X → S)`: the
transport along the equality, then `CategoryTheory.SheafOfModules.pushforwardComp`.

Taking the equality as an argument is what lets a statement about this isomorphism be proved
by `subst`, at `F = SheafOfModules.overMap`, where every factor is the identity on sections. -/
public def objZariskiRestrictIsoOfEq
    (F : SheafOfModules.{u} (structureSheaf B S hS) ⥤
      SheafOfModules.{u} (structureSheaf B (objScheme B S hS T) (contains_objScheme B S hS T)))
    (hF : F = SheafOfModules.overMap.{u} B.structureSheaf T.hom) :
    F ⋙ restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T) ≅
      objZariskiPushforward B S hS T := by
  haveI : (opensToBig B (objScheme B S hS T) (contains_objScheme B S hS T)).IsContinuous
      (Opens.grothendieckTopology ↥(objScheme B S hS T)) (B.topology.over T.left) :=
    inferInstanceAs ((opensToBig B (objScheme B S hS T)
      (contains_objScheme B S hS T)).IsContinuous
        (Opens.grothendieckTopology ↥(objScheme B S hS T))
        (topology B (objScheme B S hS T) (contains_objScheme B S hS T)))
  exact eqToIso (congrArg (fun K => K ⋙ restrictModule B (objScheme B S hS T)
      (contains_objScheme B S hS T)) hF) ≪≫ SheafOfModules.pushforwardComp _ _

/-- **The two spellings of `𝒢 ↦ 𝒢|_{X_Zar}` agree**: restricting to the big fppf site of the
scheme `X` of `T` and then to the small Zariski site of `X` is the pushforward along
`W ↦ (W ↪ X → S)`.  Restriction to the big fppf site of `X` *is* restriction along `Over.map` of
the structure morphism by `AlgebraicGeometry.BigFppfOver.objRestrict_eq_overMap`, and then this is
`CategoryTheory.SheafOfModules.pushforwardComp`.

This is what makes the target of
`AlgebraicGeometry.BigFppfOver.zariskiBaseChangeMap` the same `𝒢|_{X_Zar}` as the one in
`AlgebraicGeometry.BigFppfOver.objZariskiRestrict`, which
`AlgebraicGeometry.BigFppfOver.zariskiComparisonRestrictIso` is stated with. -/
public def objZariskiRestrictIso :
    objRestrict B S hS T ⋙
        restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T) ≅
      objZariskiPushforward B S hS T :=
  objZariskiRestrictIsoOfEq B S hS T (objRestrict B S hS T) (objRestrict_eq_overMap B S hS T)

/-- The comparison of structure sheaves along `V ↦ (g^{-1}V ↪ X → S)` read through the small
Zariski site of `X`: `g^♯` followed by
`AlgebraicGeometry.BigFppfOver.objZariskiStructureMap`.  This is the structure map that
`CategoryTheory.SheafOfModules.pushforwardComp` produces for
`objZariskiPushforward ⋙ Scheme.Modules.pushforward g`. -/
public abbrev objPreimageCompStructureMap :
    S.ringCatSheaf ⟶
      ((objPreimageFunctor B S hS T).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥S) (topology B S hS)).obj (structureSheaf B S hS) :=
  SheafOfModules.comparisonComp (objHom B S hS T).toRingCatSheafHom
    (objZariskiStructureMap B S hS T)

/-- **The two readings of the structure-sheaf comparison along `V ↦ (g^{-1}V ↪ X → S)` agree.**
Going round the big fppf site of `S` — its comparison, then restriction along the projection —
is going round the small Zariski site of `X` — `g^♯`, then the comparison of the big fppf site of
`X`.  Componentwise this is
`AlgebraicGeometry.BigFppfOver.structureMap_comp_objPreimageHom`, the identification of structure
sheaves contributing the identity on sections. -/
public theorem objPreimageStructureMap_eq :
    objPreimageStructureMap B S hS T = objPreimageCompStructureMap B S hS T := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_))
  refine Eq.trans (structureMap_comp_objPreimageHom B S hS T V.unop) ?_
  exact congrArg (fun k => (objHom B S hS T).toRingCatSheafHom.hom.app V ≫ k)
    (Category.comp_id ((structureMap B (objScheme B S hS T)
      (contains_objScheme B S hS T)).hom.app
        (op ((Opens.map (objHom B S hS T).base).obj V.unop)))).symm

/-- **The restriction comparison `𝒢|_{S_Zar} ⟶ g_*(𝒢|_{X_Zar})` of clause (2)**, with its target
written as the pushforward along `g` of the restriction to the small Zariski site of `X`.  This is
`AlgebraicGeometry.BigFppfOver.objPreimageRestrictionComparison` transported along
`AlgebraicGeometry.BigFppfOver.objPreimageStructureMap_eq` and the threefold
`CategoryTheory.SheafOfModules.pushforwardComp`. -/
public def objZariskiRestrictionComparison :
    restrictModule B S hS ⟶
      objZariskiPushforward B S hS T ⋙ Scheme.Modules.pushforward (objHom B S hS T) :=
  objPreimageRestrictionComparison B S hS T ≫
    (SheafOfModules.pushforwardCongr (objPreimageStructureMap_eq B S hS T)).hom ≫
    (SheafOfModules.pushforwardComp (objHom B S hS T).toRingCatSheafHom
      (objZariskiStructureMap B S hS T)).inv

/-- **The base-change map `g^*(𝒢|_{S_Zar}) ⟶ 𝒢|_{X_Zar}` of clause (2) of [Stacks, Tag 0756]**,
at `τ = Zar`: the adjoint transpose, under
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`, of the restriction comparison
`AlgebraicGeometry.BigFppfOver.objZariskiRestrictionComparison`.

It is the canonical map of clause (2), `AlgebraicGeometry.BigFppfOver.zariskiClause2Map`,
followed by the identification of the two spellings of `𝒢|_{X_Zar}`:
`AlgebraicGeometry.BigFppfOver.zariskiBaseChangeMap_eq`. -/
public def zariskiBaseChangeMap (G : SheafOfModules.{u} (structureSheaf B S hS)) :
    (Scheme.Modules.pullback (objHom B S hS T)).obj ((restrictModule B S hS).obj G) ⟶
      (objZariskiPushforward B S hS T).obj G :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T)).homEquiv
    ((restrictModule B S hS).obj G) ((objZariskiPushforward B S hS T).obj G)).symm
      ((objZariskiRestrictionComparison B S hS T).app G)

end Comparison

end BigFppfOver

end AlgebraicGeometry

end
