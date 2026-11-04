module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedPointStalkRing
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic

/-!
# Sections of a sheaf of modules on a space with at most one point are its stalk

Let `(Z, 𝒪_Z)` be a ringed space whose underlying space has at most one point, let `z ∈ Z` and let
`U` be an open containing `z`. Then `U` is the whole space, so it is the initial open
neighbourhood of `z`, the colimit computing a stalk is attained at `U`, and the germ map

`Γ(U, ℱ) ⟶ ℱ_z`

is an isomorphism for every sheaf of `𝒪_Z`-modules `ℱ`, naturally in `ℱ`. The two sides are
modules over different rings — `Γ(U, 𝒪_Z)` and `𝒪_{Z,z}` — so the statement is an isomorphism of
functors into `Mod(Γ(U, 𝒪_Z))`, the stalk functor being followed by restriction of scalars along
the germ `Γ(U, 𝒪_Z) ⟶ 𝒪_{Z,z}` of the structure sheaf.

`Stacks.Cohomology.SupportedComplexes.sectionsAtPointStructureSheafIso` records the ring half of
this, `Γ({x}, 𝒪_X|_{\{x\}}) ≅ 𝒪_{X,x}`; the implementation notes of that declaration name the
present statement as the module half still owed, because it is what carries
`Stacks.Cohomology.SupportedComplexes.derivedSectionsIsoSectionsAtClosedPoint` — the reduction of
`RΓ(X, -)` at a closed point performed in the proof of [Stacks, Tag 0G02] — from sections on the
one-point space `{x}` to the stalk at `x`. The open is left general rather than taken to be `⊤`
precisely so that it applies at the open `i⁻¹⊤` that the Leray isomorphism of [Stacks, Tag 0D5W]
produces there.

## Main definitions

* `Stacks.Topology.isTerminal_op_openNhds`: every open neighbourhood of the point is initial among
  them, stated as terminality in the opposite category indexing the stalk.
* `Stacks.Topology.sectionsOverOpenIsoStalk`: the germ map `Γ(U, F) ⟶ F_z` as an isomorphism, for
  a presheaf with values in any category with colimits.
* `Stacks.Cohomology.SubsingletonSections.structureGerm`: the germ `Γ(U, 𝒪_Z) ⟶ 𝒪_{Z,z}` of the
  structure sheaf, as a ring homomorphism.
* `Stacks.Cohomology.SubsingletonSections.sectionsStalkApp`: the germ map `Γ(U, ℱ) ⟶ ℱ_z` as a
  map of `Γ(U, 𝒪_Z)`-modules.
* `Stacks.Cohomology.SubsingletonSections.sectionsStalkNatTrans`: the same, as a natural
  transformation of functors on sheaves of modules.
* `Stacks.Cohomology.SubsingletonSections.sectionsIsoStalkFunctor`: **the isomorphism**
  `Γ(U, -) ≅ (-)_z` of functors `Mod(𝒪_Z) ⥤ Mod(Γ(U, 𝒪_Z))`.
* `Stacks.Cohomology.SupportedComplexes.sectionsAtPointGerm`: the ring homomorphism
  `Γ(X, 𝒪_X) ⟶ (𝒪_X|_{\{x\}})_x` the reduction at a closed point is linear over.
* `Stacks.Cohomology.SupportedComplexes.sectionsAtPointIsoStalkFunctor`: sections at a closed
  point are the stalk there.
* `Stacks.Cohomology.SupportedComplexes.derivedSectionsIsoStalkAtClosedPoint`:
  `RΓ(X, K) ≅ (R𝓗_{\{x\}}(K))_x` for `K` with cohomology sheaves supported on the closed point.
* `Stacks.Cohomology.SupportedComplexes.homologyIsoStalkAtClosedPoint`: the same in each degree.

## Main results

* `Stacks.Topology.isIso_germ_of_subsingleton`: the germ map at `U` is an isomorphism.
* `Stacks.Cohomology.SubsingletonSections.isIso_sectionsStalkApp`: each component of the
  comparison of functors is invertible.

## Implementation notes

`isIso_germ_of_subsingleton` is `CategoryTheory.Limits.isIso_ι_of_isTerminal`: the germ map at an
open *is* the colimit inclusion at `op ⟨U, hzU⟩` by definition of `TopCat.Presheaf.germ`, and that
object is terminal in the index category because every open neighbourhood of the point is the
whole space. This generalises `Stacks.Topology.isIso_Γgerm_of_subsingleton`, which is the case
`U = ⊤`; the diagram `(OpenNhds.inclusion z).op ⋙ F` has to be given explicitly rather than left
to unification, or the `HasColimit` instance is searched for at a metavariable and not found.

The component of the comparison is `ModuleCat.ofHom` of the germ map, whose semilinearity over the
germ of the structure sheaf is `AlgebraicGeometry.SheafOfModules.germ_hom_smul`; after restriction
of scalars along that germ the map is linear, which is why the target is written with
`ModuleCat.restrictScalars` rather than as a semilinear equivalence. Both the source and the
target `ModuleCat` have to be ascribed in `ModuleCat.ofHom`: the module structure on
`(ModuleCat.restrictScalars f).obj M` is `Module.compHom` bound by a `let` inside
`ModuleCat.RestrictScalars.obj'`, so instance search does not find it from the carrier alone.
Naturality is `TopCat.Presheaf.stalkFunctor_map_germ_apply` on the underlying presheaves of
abelian groups, `AlgebraicGeometry.SheafOfModules.stalkMap` being that map by definition.

Invertibility of a component is read off the underlying abelian groups: the germ is invertible
there, hence bijective, hence invertible in `Mod(Γ(U, 𝒪_Z))` because the forgetful functor of a
module category reflects isomorphisms. No exactness or sheaf-condition input is used; in
particular this is independent of
`Stacks.Cohomology.SubsingletonSections.subsingletonForgetEquivalence`, which is about the sheaf
condition rather than about sections.

The stalk functor used is `AlgebraicGeometry.SheafOfModules.stalkFunctor` at the sheaf of rings
`structureSheafRing Z`, which is the spelling the ringed-space cohomology cluster is written in,
and the module universe is pinned to that of the space as everywhere in that cluster.

The closed-point statements at the end are the one-point case applied at the open `i⁻¹⊤`, with the
two restrictions of scalars — the structure morphism of the inclusion and the germ — fused by
`ModuleCat.restrictScalarsComp'`; the derived form then descends along
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso`, both functors being exact. They
are stated at `CategoryTheory.HasDerivedCategory.standard`, which is the model
`Stacks.Cohomology.SupportedComplexes.derivedSectionsIsoSectionsAtClosedPoint` is stated at.

*What this is not.* The stalk here is that of `𝒪_X|_{\{x\}}` on the one-point space, not of `𝒪_X`
on `X`: the identification `(R𝓗_{\{x\}}(K))_x ≅ K_x` needs the stalk of a pushforward along the
inclusion of a closed subset, which is not proved here. The ring the two are modules over is
identified by `Stacks.Cohomology.SupportedComplexes.sectionsAtPointStructureSheafIso`; the module
comparison is not.

## References

* [Stacks Project, Tag 0G02](https://stacks.math.columbia.edu/tag/0G02)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.GlobalKunneth

universe v u

namespace Stacks.Topology

variable {C : Type u} [Category.{v} C] [HasColimits.{v} C] {X : TopCat.{v}}
  [Subsingleton X] (x : X)

/-- **Every open neighbourhood of a point of a space with at most one point is the initial
one**, stated as terminality of `op ⟨U, hxU⟩` in the opposite category, which is the shape the
colimit computing the stalk is indexed by. An open containing the point is the whole space, so it
is contained in every other one. -/
public def isTerminal_op_openNhds (U : Opens X) (hxU : x ∈ U) :
    IsTerminal (op (⟨U, hxU⟩ : OpenNhds x)) :=
  IsTerminal.ofUniqueHom
    (fun V => Quiver.Hom.op (homOfLE (Subtype.coe_le_coe.mp
      (le_of_le_of_eq le_top
        (eq_top_of_mem_of_subsingleton x V.unop.1 V.unop.2).symm))))
    (fun _ _ => Subsingleton.elim _ _)

/-- **The germ map at an open containing the point is an isomorphism on a space with at most one
point.** The germ map at an open is the colimit inclusion of the diagram computing the stalk, and
that open is terminal in the diagram's index category. -/
public theorem isIso_germ_of_subsingleton (F : TopCat.Presheaf C X) (U : Opens X) (hxU : x ∈ U) :
    IsIso (F.germ U x hxU) :=
  isIso_ι_of_isTerminal (isTerminal_op_openNhds x U hxU) ((OpenNhds.inclusion x).op ⋙ F)

/-- **Sections on an open containing the point are the stalk, on a space with at most one
point.** -/
public def sectionsOverOpenIsoStalk (F : TopCat.Presheaf C X) (U : Opens X) (hxU : x ∈ U) :
    F.obj (op U) ≅ F.stalk x :=
  letI := isIso_germ_of_subsingleton x F U hxU
  asIso (F.germ U x hxU)

end Stacks.Topology

namespace Stacks.Cohomology.SubsingletonSections

variable (Z : RingedSpace.{u, u}) [Subsingleton Z.carrier] (z : Z.carrier)
  (U : Opens Z.carrier) (hzU : z ∈ U)

/-- **The germ of the structure sheaf on sections over `U`**, `Γ(U, 𝒪_Z) ⟶ 𝒪_{Z,z}`, as a ring
homomorphism. The scalars of the two sides of the comparison below are related by it. -/
public abbrev structureGerm :
    (structureSheafRing Z).obj.obj (op U) →+*
      TopCat.Presheaf.stalk (C := RingCat.{u}) (structureSheafRing Z).obj z :=
  (TopCat.Presheaf.germ (C := RingCat.{u}) (structureSheafRing Z).obj U z hzU).hom

/-- **The germ map on sections of a sheaf of modules**, `Γ(U, ℱ) ⟶ ℱ_z`, as a map of
`Γ(U, 𝒪_Z)`-modules: the stalk is a module over `𝒪_{Z,z}` and the germ is semilinear over the
germ of the structure sheaf, so it is linear once the scalars of the stalk are restricted along
`Stacks.Cohomology.SubsingletonSections.structureGerm`. -/
public def sectionsStalkApp (M : SheafOfModules.{u} (structureSheafRing Z)) :
    (sectionsOverOpen Z U).obj M ⟶
      (ModuleCat.restrictScalars (structureGerm Z z U hzU)).obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Z) z).obj M) :=
  ModuleCat.ofHom (X := (sectionsOverOpen Z U).obj M)
      (Y := (ModuleCat.restrictScalars (structureGerm Z z U hzU)).obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Z) z).obj M))
    { toFun := fun s =>
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf U z hzU).hom s
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r s => by
        simp only [RingHom.id_apply]
        exact AlgebraicGeometry.SheafOfModules.germ_hom_smul (structureSheafRing Z) z M.val U
          hzU r s }

/-- The germ map on sections over `U` is natural in the sheaf of modules. -/
public def sectionsStalkNatTrans :
    sectionsOverOpen Z U ⟶
      AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Z) z ⋙
        ModuleCat.restrictScalars (structureGerm Z z U hzU) where
  app := sectionsStalkApp Z z U hzU
  naturality M N f := by
    ext s
    simp only [ConcreteCategory.comp_apply]
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U z hzU
      ((PresheafOfModules.toPresheaf (structureSheafRing Z).obj).map f.val) s).symm

/-- **The germ map on sections over `U` is invertible on a space with at most one point.** It is
invertible on the underlying abelian groups, `U` being the initial open neighbourhood of the
point, and the forgetful functor of a module category reflects isomorphisms. -/
public instance isIso_sectionsStalkApp (M : SheafOfModules.{u} (structureSheafRing Z)) :
    IsIso (sectionsStalkApp Z z U hzU M) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  let := Stacks.Topology.isIso_germ_of_subsingleton z M.val.presheaf U hzU
  exact ConcreteCategory.bijective_of_isIso
    (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.val.presheaf U z hzU)

/-- The germ map on sections over `U` is invertible as a natural transformation, being invertible
at every sheaf of modules. -/
public instance isIso_sectionsStalkNatTrans : IsIso (sectionsStalkNatTrans Z z U hzU) :=
  haveI : ∀ M, IsIso ((sectionsStalkNatTrans Z z U hzU).app M) :=
    fun M => isIso_sectionsStalkApp Z z U hzU M
  NatIso.isIso_of_isIso_app _

/-- **Sections on a space with at most one point are the stalk, naturally in the sheaf of
modules**:

`Γ(U, -) ≅ (-)_z : Mod(𝒪_Z) ⥤ Mod(Γ(U, 𝒪_Z))`

for any open `U` containing the point, the stalk being read as a `Γ(U, 𝒪_Z)`-module along the germ
of the structure sheaf. -/
public def sectionsIsoStalkFunctor :
    sectionsOverOpen Z U ≅
      AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Z) z ⋙
        ModuleCat.restrictScalars (structureGerm Z z U hzU) :=
  asIso (sectionsStalkNatTrans Z z U hzU)

end Stacks.Cohomology.SubsingletonSections

/-! ### Sections at a closed point are the stalk there -/

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) (x : X.carrier)

/-- The ring homomorphism `Γ(X, 𝒪_X) ⟶ (𝒪_X|_{\{x\}})_x` along which
`Stacks.Cohomology.SupportedComplexes.sectionsAtPoint` reads the stalk at the point as a module
over the global functions: the structure morphism of the inclusion of `{x}`, followed by the germ
on the one-point space. -/
public abbrev sectionsAtPointGerm :
    (structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)) →+*
      TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafRing (closedSubsetRingedSpace X ({x} : Set X.carrier))).obj
        (singletonPoint X x) :=
  (Stacks.Cohomology.SubsingletonSections.structureGerm
      (closedSubsetRingedSpace X ({x} : Set X.carrier)) (singletonPoint X x)
      ((opensMap (closedSubsetInclusion X ({x} : Set X.carrier))).obj ⊤) trivial).comp
    ((structureSheafHom (closedSubsetInclusion X ({x} : Set X.carrier))).hom.app
      (op (⊤ : Opens X.carrier))).hom

/-- **Sections at the closed point are the stalk there, naturally in the sheaf of modules.**

`Stacks.Cohomology.SupportedComplexes.sectionsAtPoint` is sections on the one-point space `{x}`
with scalars in `Γ(X, 𝒪_X)`; the space has one point, so those sections are the stalk at it, and
the comparison is an isomorphism of functors `Mod(𝒪_X|_{\{x\}}) ⥤ Mod(Γ(X, 𝒪_X))`.

Together with `Stacks.Cohomology.SupportedComplexes.sectionsAtPointStructureSheafIso`, which
identifies the ring the stalk is a module over as `𝒪_{X,x}`, this is the module half of the
reduction to the point that
`Stacks.Cohomology.SupportedComplexes.derivedSectionsIsoSectionsAtClosedPoint` lands in, and which
the proof of [Stacks, Tag 0G02] performs on `H^0(X, -)`. -/
public def sectionsAtPointIsoStalkFunctor :
    sectionsAtPoint X x ≅
      AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafRing (closedSubsetRingedSpace X ({x} : Set X.carrier)))
          (singletonPoint X x) ⋙
        ModuleCat.restrictScalars (sectionsAtPointGerm X x) :=
  Functor.isoWhiskerRight
      (Stacks.Cohomology.SubsingletonSections.sectionsIsoStalkFunctor
        (closedSubsetRingedSpace X ({x} : Set X.carrier)) (singletonPoint X x)
        ((opensMap (closedSubsetInclusion X ({x} : Set X.carrier))).obj ⊤) trivial) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ModuleCat.restrictScalarsComp' _ _ _ rfl).symm

/-- **Derived global sections of a complex supported at a closed point are the stalk at that
point.** For `x` a point of a ringed space `X` whose singleton is closed and `K` an object of
`D(𝒪_X)` whose cohomology sheaves are supported on `{x}`,

`RΓ(X, K) ≅ (R𝓗_{\{x\}}(K))_x`

in `D(Γ(X, 𝒪_X))`, the stalk being that of the one-point space `({x}, 𝒪_X|_{\{x\}})` read as a
module over the global functions.

This is `Stacks.Cohomology.SupportedComplexes.derivedSectionsIsoSectionsAtClosedPoint` with its
target rewritten by `Stacks.Cohomology.SupportedComplexes.sectionsAtPointIsoStalkFunctor`: both
functors are exact, so the isomorphism between them descends to the derived categories by
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso`. It is the reduction of
`H^i(X, -)` to the local ring at `x` that the proof of [Stacks, Tag 0G02] performs. -/
public def derivedSectionsIsoStalkAtClosedPoint
    (hx : IsClosed ({x} : Set X.carrier))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hK : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X)
      ({x} : Set X.carrier) K) :
    (baseSections X).obj K ≅
      (AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafRing (closedSubsetRingedSpace X ({x} : Set X.carrier)))
            (singletonPoint X x) ⋙
          ModuleCat.restrictScalars
            (sectionsAtPointGerm X x)).mapDerivedCategory.obj
        ((derivedSupportedSectionsOnClosed X ({x} : Set X.carrier) hx).obj K) :=
  derivedSectionsIsoSectionsAtClosedPoint X x hx K hK ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (sectionsAtPointIsoStalkFunctor X x)).app _

/-- **The reduction to the stalk in each degree**: `H^n(X, K) ≅ H^n((R𝓗_{\{x\}}(K))_x)` for `K`
with cohomology sheaves supported on the closed point `x`. -/
public def homologyIsoStalkAtClosedPoint
    (hx : IsClosed ({x} : Set X.carrier))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hK : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X)
      ({x} : Set X.carrier) K) (n : ℤ) :
    (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)))) n).obj
        ((baseSections X).obj K) ≅
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)))) n).obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (structureSheafRing (closedSubsetRingedSpace X ({x} : Set X.carrier)))
              (singletonPoint X x) ⋙
            ModuleCat.restrictScalars
              (sectionsAtPointGerm X x)).mapDerivedCategory.obj
          ((derivedSupportedSectionsOnClosed X ({x} : Set X.carrier) hx).obj K)) :=
  (DerivedCategory.homologyFunctor _ n).mapIso
    (derivedSectionsIsoStalkAtClosedPoint X x hx K hK)

end Stacks.Cohomology.SupportedComplexes

end
