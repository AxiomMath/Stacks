module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSiteDerivedInternalHom
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom

/-!
# `ε^* RSheafHom_{𝒪_S}(E, F)`, the left-hand side of Stacks 08JP

Let `S` be a scheme and let `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of ringed sites
of Stacks 08H7 (Equation 75.4.0.1), `AlgebraicGeometry.SmallEtale.toZariskiRingedToposHom`.
Stacks 08JP asserts, for `E` pseudo-coherent with `F` in `D^+(𝒪_S)` or for `E` perfect and `F`
arbitrary, a canonical isomorphism

`ε^* RSheafHom_{𝒪_S}(E, F) ≅ RSheafHom_𝒪(ε^* E, ε^* F)`.

This module writes the *left*-hand side of that formula. Its two ingredients are
available and are only put together here: the derived internal Hom `RSheafHom_{𝒪_S}(-, -)` of a
ringed space, `Stacks.SheafOfModules.derivedSheafHom`, at the structure sheaf of `S`; and the
inverse image `ε^*` of sheaves of modules along `ε`, which is the associated-module functor of
Stacks 03DU (4) at `τ = étale`,
`AlgebraicGeometry.SmallEtale.associatedModule`; that it is the pullback of modules along `ε`
is `AlgebraicGeometry.SmallEtale.toZariskiRingedToposHom_fSharpRing`.

## The two sides of 08JP are modules over the same sheaf of rings at *different* module
universes

`AlgebraicGeometry.SmallEtale.smallEtaleRingedSite_ringSheaf` and
`AlgebraicGeometry.SmallEtale.zariskiRingedSite_ringSheaf` below record that the sheaves of
rings of the two ringed sites are the structure sheaves of Stacks 03DU and of the scheme. So
the left-hand side written here is an object of `D(Mod_u(𝒪))` on the small étale site, whereas
`AlgebraicGeometry.SmallEtale.derivedSheafHom`, the right-hand side, is an object of
`D(Mod_{u+1}(𝒪))` over the *same* sheaf of rings: the internal Hom complex of Stacks 0A8X
raises the module universe on the small étale site, whose objects form a type in `Type (u + 1)`,
and does not raise it on the Zariski site, whose objects form a type in `Type u`. Stacks 08JP
is therefore not yet statable, and the two things that would make it statable are a universe
comparison of module sheaves in the derived category and the canonical map itself; see the
implementation notes.

## Main definitions

* `AlgebraicGeometry.SmallEtale.derivedAssociatedModuleFunctor`: `ε^*` on the full derived
  categories of sheaves of modules, `D(𝒪_S) ⥤ D(S_étale, 𝒪)`.
* `AlgebraicGeometry.SmallEtale.derivedAssociatedModuleDerivedSheafHom`:
  **`ε^* RSheafHom_{𝒪_S}(E, F)`**, the left-hand side of Stacks 08JP.

## Main results

* `AlgebraicGeometry.SmallEtale.zariskiRingedSite_ringSheaf` and
  `AlgebraicGeometry.SmallEtale.smallEtaleRingedSite_ringSheaf`: the sheaves of rings of the two
  ringed sites `ε` connects are the structure sheaf of the scheme and the structure sheaf of
  Stacks 03DU.

## What is carried as a hypothesis

Exactness of `ε^*`, the second assertion of Stacks 08H8, as
`[PreservesFiniteLimits (associatedModuleOfSheaf B S hS)]`. This is the hypothesis under which
`AlgebraicGeometry.SmallEtale.derivedAssociatedModule` — the corestriction of the same derived
functor to the subcategories of complexes with quasi-coherent cohomology, which is the functor
of Stacks 071Q — is already stated, and nothing further is assumed here: additivity and right
exactness of `ε^*` are proved unconditionally, `ε^*` being a left adjoint
(`AlgebraicGeometry.SmallEtale.additive_associatedModuleOfSheaf` and
`AlgebraicGeometry.SmallEtale.preservesFiniteColimits_associatedModuleOfSheaf`). The flatness
assertion of 08H8, which is what makes `ε^* = Lε^*` in the source, is proved separately as
`AlgebraicGeometry.SmallEtale.isFlatMapULift_inverseImageStructureMap`.

## Implementation notes

`ε^*` is applied to the derived category through `CategoryTheory.Functor.mapDerivedCategory`,
the derived functor of an exact functor, which is how
`AlgebraicGeometry.SmallEtale.derivedAssociatedModule` is built; so the functor named here and
that one are the same construction, the latter corestricted. The source's `Lε^*` agrees with it
because `ε` is flat.

Neither the canonical map of 08JP nor its inverse is constructed here, and neither is available.
The canonical map `Lh^* RSheafHom(K, L) ⟶ RSheafHom(Lh^* K, Lh^* L)` of Stacks 08JF is available,
as `AlgebraicGeometry.RingedToposSiteHom.derivedPullbackSheafHomMap`, but only for a morphism of
ringed topoi both of whose sides are a `AlgebraicGeometry.RingedTopos.{u, u, u}`, and `ε` is not
of that shape: the small Zariski site of `S` is presented by the opens of its underlying space,
so its objects form a type one universe below those of the small étale site. That is the same
obstruction that stops `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos` from being the
pullback of modules along `ε` — which is why the pullback used here is the associated-module
functor instead — and it is why `ε^*` rather than `Lε^*` appears in the type: no derived
pullback along `ε` as a morphism of ringed topoi is available either.

The universe comparison that the statement of 08JP needs is a functor
`D(Mod_u(𝒪)) ⥤ D(Mod_{u+1}(𝒪))` on the small étale site, or a descent of
`AlgebraicGeometry.SmallEtale.derivedSheafHomBifunctor` to `Mod_u(𝒪)`. The first of the two is
`AlgebraicGeometry.SmallEtale.derivedModuleULift`, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleUniverseComparison`: the
universe-raising functor on module sheaves, `Stacks.SheafOfModules.moduleULift`, is additive and
exact, so it has a derived functor, and
`AlgebraicGeometry.SmallEtale.raisedDerivedAssociatedModuleDerivedSheafHom` is the left-hand side
written here moved along it into the module universe of the right-hand side. The second remains
unavailable: the descent of a *single* internal Hom sheaf is available
(`AlgebraicGeometry.SmallEtale.internalHomSheaf`, identified with the raised one by
`AlgebraicGeometry.SmallEtale.moduleULiftInternalHomSheafIso`), but not the degreewise shrinking
of the internal Hom complex, as the notes of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSiteDerivedInternalHom` describe.

Having both sides in one category is not the canonical map. That map is still missing, and what
it waits on is a mixed-universe tensor–internal-Hom bijection and a mixed-universe monoidality of
`ε^*`; its abstract shape, with the proof that at equal universes it is the construction behind
Stacks 08JF/08I3, is
`Stacks.Cohomology.DerivedInternalHomPullback.MixedTranspose.homComparison`.

## References

* [Stacks Project, Tag 08JP](https://stacks.math.columbia.edu/tag/08JP)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two ringed sites that `ε` connects have the expected sheaves of rings -/

/-- The sheaf of rings of the Zariski ringed site of a scheme `S` — the site of opens of the
underlying space of `S` with its structure sheaf of commutative rings — is the sheaf of rings
`AlgebraicGeometry.Scheme.ringCatSheaf` of `S`, over which the sheaves of `𝒪_S`-modules that
`ε^*` takes as arguments are indexed. -/
@[simp]
public theorem zariskiRingedSite_ringSheaf :
    (Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.ringedSite S.sheaf).O) =
      S.ringCatSheaf := rfl

/-- The sheaf of rings of the small étale ringed site of `S` is the structure sheaf of
Stacks 03DU, over which the sheaves of modules in the image of `ε^*` are indexed.

This is `AlgebraicGeometry.SmallEtale.sheafCompose_forget₂_commRingStructureSheaf` read through
`AlgebraicGeometry.RingedSite.ringSheaf`; it names no new fact, and is recorded so that the
value of `ε^*` and the derived internal Hom of
`AlgebraicGeometry.SmallEtale.derivedSheafHomBifunctor` are visibly modules over one sheaf of
rings, differing only in their module universe. -/
@[simp]
public theorem smallEtaleRingedSite_ringSheaf :
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O) =
      structureSheaf B S hS :=
  sheafCompose_forget₂_commRingStructureSheaf B S hS

/-! ### `ε^*` on the derived category, and the left-hand side of Stacks 08JP -/

variable [PreservesFiniteLimits (associatedModuleOfSheaf B S hS)]

/-- **`ε^* : D(𝒪_S) ⥤ D(S_étale, 𝒪)`**, the derived functor of the exact inverse image of
sheaves of modules along `ε`, on the full derived categories.

`AlgebraicGeometry.SmallEtale.derivedAssociatedModule`, the functor of Stacks 071Q, is this
functor corestricted to the complexes with quasi-coherent cohomology on either side. Since `ε`
is flat (Stacks 08H8, `AlgebraicGeometry.SmallEtale.isFlatMapULift_inverseImageStructureMap`),
this is the `Lε^*` of the source. -/
public def derivedAssociatedModuleFunctor :
    DerivedCategory (SheafOfModules.{u} S.ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS)) :=
  (associatedModuleOfSheaf B S hS).mapDerivedCategory

/-- **`ε^* RSheafHom_{𝒪_S}(E, F)`, the left-hand side of Stacks 08JP**, for objects `E` and `F`
of the derived category of sheaves of `𝒪_S`-modules on the Zariski site of the scheme `S`: the
inverse image along `ε` of the derived internal Hom of Stacks 0A97 of the Zariski ringed site.

The derived internal Hom used is `Stacks.SheafOfModules.derivedSheafHom`, the derived internal
Hom of a ringed space, at the structure sheaf of `S`; it is
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` at the ringed site
`Stacks.SheafOfModules.ringedSite` of `𝒪_S`. -/
public def derivedAssociatedModuleDerivedSheafHom
    (E F : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) :
    DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS)) :=
  (derivedAssociatedModuleFunctor B S hS).obj
    (((Stacks.SheafOfModules.derivedSheafHom S.sheaf).obj (op E)).obj F)

/-- `ε^* RSheafHom_{𝒪_S}(E, F)` is the value of `ε^*` on the derived internal Hom, by
definition. -/
public theorem derivedAssociatedModuleDerivedSheafHom_eq
    (E F : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) :
    derivedAssociatedModuleDerivedSheafHom B S hS E F =
      (derivedAssociatedModuleFunctor B S hS).obj
        (((Stacks.SheafOfModules.derivedSheafHom S.sheaf).obj (op E)).obj F) := rfl

end AlgebraicGeometry.SmallEtale

end
