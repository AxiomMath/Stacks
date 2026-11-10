module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartComparisonMap
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.ExtendScalars.IndependentUniverses
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived stalk at a point of an affine open is the derived localization of the sections

Let `i : Spec R ⟶ X` be an open immersion with image `U`, let `y` be a point of `Spec R`, and let
`K ∈ D(𝒪_X)` have quasi-coherent cohomology sheaves. This module identifies the derived stalk of
`K` at the point `i y` of `U` with the derived localization of `RΓ(U, K)` at `y`:

```
RΓ(U,K) ⊗ᴸ_R 𝒪_{Spec R, y}  ≅  (K_{i y}) ⊗ᴸ_{𝒪_{X, i y}} 𝒪_{Spec R, y}
```

the extension of scalars on the right being along the germ isomorphism `𝒪_{X, i y} ≅
𝒪_{Spec R, y}` of the open immersion. This is the first of the two inputs that
`StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartCohomologyComparison`
records as missing for turning condition (1) of Stacks 0DJ8 into condition (2).

The statement proved is slightly more general and asks nothing of `i`: for *any* morphism
`i : Spec R ⟶ X` of schemes out of an affine scheme the two displayed objects are isomorphic,
`RΓ(U, -)` being read as `AlgebraicGeometry.affineDerivedSections i`. It is only when `i` is an
open immersion that `𝒪_{X, i y} ⟶ 𝒪_{Spec R, y}` is invertible and the right-hand side is the
derived stalk of `K` at `i y` rather than a base change of it.

## The proof

Nothing is computed about `AlgebraicGeometry.tilde`. The stalk of `M̃` at `y` over the local ring
`𝒪_{Spec R, y}` is the extension of scalars of `M` along the germ map `R ⟶ 𝒪_{Spec R, y}`, and
both sides of that assertion are left adjoints: sheafification followed by the stalk is left
adjoint to the skyscraper at `y` followed by global sections, base change is left adjoint to
restriction of scalars, and the two right adjoints agree because a global section of a skyscraper
at `y` is a function on a subsingleton with values in the stalk module, scaled by the germ.
That is `specSkyscraperSectionsIso`, the only computation here, and all of its obligations hold by
`rfl`. Uniqueness of a left adjoint then gives `tildeLocalRingStalkIso`, which is Stacks 01HV.

Passing to derived categories uses that the germ map is a localization, hence flat, so that the
total derived extension of scalars along it is the degreewise functor read on derived categories;
and `AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_counit_app` to replace `K` by
the sheafification of its sections over `U`. The passage from the affine scheme to a point of an
affine open of an arbitrary scheme is `AlgebraicGeometry.derivedPullbackStalkIso`.

## Main definitions

* `AlgebraicGeometry.specSkyscraperSectionsIso`: the global sections of a skyscraper sheaf of
  `𝒪_{Spec R}`-modules at `y` are its value with scalars restricted along the germ map.
* `AlgebraicGeometry.tildeLocalRingStalkIso`: **Stacks 01HV over the local ring.** The stalk of
  `M̃` at `y` is `𝒪_{Spec R, y} ⊗_R M`, naturally in `M`.
* `AlgebraicGeometry.derivedTildeStalkIsoToStalk`: the same identification of functors on unbounded
  derived categories.
* `AlgebraicGeometry.affineDerivedStalkSectionsIso`: the derived stalk at `y` of an object of
  `D(𝒪_{Spec R})` with quasi-coherent cohomology is the derived localization at `y` of its
  derived global sections.
* `AlgebraicGeometry.derivedStalkAffineSectionsIsoToStalk`: **the identification this module exists
  for**, at a point of an affine open of an arbitrary scheme.

## Main results

* `AlgebraicGeometry.flat_toStalk`: the germ map `R ⟶ 𝒪_{Spec R, y}` is flat, being a
  localization.

## Implementation notes

*Two spellings of the stalk ring.* The stalk of the structure sheaf is taken here over the local
ring `𝒪_{Spec R, y}`, the `CommRingCat`-valued stalk, which is the ring
`AlgebraicGeometry.derivedPullbackStalkIso` and `AlgebraicGeometry.Scheme.Hom.stalkMap` are stated
over. The existing identifications `AlgebraicGeometry.tildeStalkIso` and
`Stacks.TildeStalk.tildeStalkFunctorIso` are both stated over the `RingCat`-valued stalk of the
sheaf of rings instead, which is the ring the K-flatness criterion of Stacks 06YB needs; crossing
between the two spellings costs an extension of scalars along a ring isomorphism, so
`tildeLocalRingStalkIso` is obtained by running the adjoint-uniqueness argument of
`Stacks.TildeStalk.tildeStalkFunctorIso` again over the local ring rather than by transporting it.
Nothing of that file is reproved: only its architecture is reused, and the stalk–skyscraper
adjunction over the local ring is `Stacks.ModuleSkyscraper.modulesStalkSkyAdjunction`.

*Two spellings of the stalk of the structure sheaf, and where they have to be pinned by hand.*
`AlgebraicGeometry.StructureSheaf.toStalk` is declared with target
`(structurePresheafInCommRingCat R).stalk y`, which is `(Spec R).presheaf.stalk y` by definition
but not by syntax, while `AlgebraicGeometry.derivedStalkFunctor` and
`Stacks.ModuleSkyscraper.modulesStalkFunctor` are stated at the second. Both occur in every
statement from `derivedTildeStalkIsoToStalk` on, and the elaborator unifies them to whichever it
meets first, so the named argument `A := ` fixes it to the second once and for all. The cost is
that `ModuleCat.extendScalars` at the pinned spelling is a term whose `Additive`,
`PreservesFiniteLimits` and `PreservesFiniteColimits` instances are no longer *found* — the
discrimination tree misses them, although `extendScalars_additive` applied by hand produces them
— so each of the three is seated with `letI` at the pinned spelling inside
`derivedTildeStalkIsoToStalk`, which is the one declaration where the exactness of that functor is
needed.

*The model of the derived category.* The locally small one throughout, which is what the global
instances `ModuleCat.hasDerivedCategory` and `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`
supply, as in `AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_counit_app` and in
`AlgebraicGeometry.BaseChangeChart.comparison`. Free `[HasDerivedCategory.{w} ·]` binders are not
used: the two spellings of the stalk ring above would then carry *different* instances, the binder
at one and the global instance at the other, and the statement of `derivedTildeStalkIsoToStalk`
does not typecheck. `HasDerivedCategory.standard` is installed nowhere here.

*The point of `Spec R` is typed `↥(Spec R)` and not `PrimeSpectrum R`.* The instances
`AlgebraicGeometry.modulesStalkFunctor_additive` and its exactness companions are keyed at
`(x : ↥X)` for a scheme `X`, and are not found when the point is presented as a prime of the
coordinate ring — a hard synthesis failure. The primality of `y.asIdeal`, which
`Ideal.primeCompl` needs, is therefore supplied inside `flat_toStalk` by reading `y` back as a
prime.

*What is not proved here.* Only the identification. Turning condition (1) of Stacks 0DJ8 into
condition (2) needs one further input, that the base-change comparison of Stacks 065Z for the
chart's square of rings is compatible with passing to the square of local rings, and nothing is
stated about Stacks 065Z and localization anywhere in the library.

## References

* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)
open Stacks.ModuleSkyscraper (modulesStalkFunctor skyModulesFunctor skyModules
  modulesStalkSkyAdjunction)
open Stacks.Cohomology.PerfectComplexTriangles (mapDerivedCategoryIsoOfNatIso
  mapDerivedCategoryCompIso)

universe u

namespace AlgebraicGeometry

variable (R : CommRingCat.{u}) (y : Spec R)

/-! ### The stalk of an associated sheaf over the local ring -/

/-- **The global sections of a skyscraper sheaf of `𝒪_{Spec R}`-modules at `y`**, as an
`R`-module, are the value of the skyscraper with scalars restricted along the germ map
`R ⟶ 𝒪_{Spec R, y}`.

A section over `⊤` is a function on `PLift (y ∈ ⊤)`, a subsingleton, so evaluating at the unique
proof is bijective; and `r : R` acts on such a section by scaling its value by the germ at `y` of
`r`, which is `AlgebraicGeometry.StructureSheaf.toStalk` applied to `r`. Both linearity
obligations and both inverse laws therefore hold by `rfl`. -/
public def specSkyscraperSectionsObjIso
    (A : ModuleCat.{u} ((Spec R).presheaf.stalk y : Type u)) :
    moduleSpecΓFunctor.obj (skyModules (Spec R) y A) ≅
      (ModuleCat.restrictScalars.{u, u, u} (StructureSheaf.toStalk R y).hom).obj A where
  hom := ModuleCat.ofHom
    (X := moduleSpecΓFunctor.obj (skyModules (Spec R) y A))
    (Y := (ModuleCat.restrictScalars.{u, u, u} (StructureSheaf.toStalk R y).hom).obj A)
    { toFun := fun s => s ⟨trivial⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  inv := ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars.{u, u, u} (StructureSheaf.toStalk R y).hom).obj A)
    (Y := moduleSpecΓFunctor.obj (skyModules (Spec R) y A))
    { toFun := fun a => fun _ => a
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  hom_inv_id := by ext s; funext h; rfl
  inv_hom_id := by ext a; rfl

/-- **The right adjoint of `~ ⋙ (-)_y` is restriction of scalars along the germ map.** This is
`specSkyscraperSectionsObjIso` as an isomorphism of functors; naturality is `rfl`, both sides
applying the given linear map to the value of a section. -/
public def specSkyscraperSectionsIso :
    skyModulesFunctor (Spec R) y ⋙ moduleSpecΓFunctor ≅
      ModuleCat.restrictScalars.{u, u, u} (StructureSheaf.toStalk R y).hom :=
  NatIso.ofComponents (specSkyscraperSectionsObjIso R y) (fun _ => by ext; rfl)

/-- **Stacks 01HV over the local ring, functorially.** The stalk at `y` of the sheaf associated to
an `R`-module is the base change of that module along the germ map `R ⟶ 𝒪_{Spec R, y}`, naturally
in the module:

`~ ⋙ (-)_y ≅ 𝒪_{Spec R,y} ⊗_R -`.

Both sides are left adjoints — `AlgebraicGeometry.tilde.adjunction` composed with
`Stacks.ModuleSkyscraper.modulesStalkSkyAdjunction` on the left,
`ModuleCat.extendRestrictScalarsAdj` on the right — and their right adjoints are isomorphic by
`specSkyscraperSectionsIso`, so this is the uniqueness of a left adjoint. This is
`Stacks.TildeStalk.tildeStalkFunctorIso` over `𝒪_{Spec R,y}` instead of over the `RingCat`-valued
stalk of the sheaf of rings; see the implementation notes for why it is not transported. -/
public def tildeLocalRingStalkIso :
    tilde.functor R ⋙ modulesStalkFunctor (Spec R) y ≅
      ModuleCat.extendScalars.{u, u, u} (StructureSheaf.toStalk R y).hom :=
  (((tilde.adjunction (R := R)).comp (modulesStalkSkyAdjunction (Spec R) y)).ofNatIsoRight
      (specSkyscraperSectionsIso R y)).leftAdjointUniq
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (StructureSheaf.toStalk R y).hom)

/-- **The germ map `R ⟶ 𝒪_{Spec R, y}` is flat.** It is the localization of `R` at the prime `y`
by `AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`, and a localization is flat. -/
public theorem flat_toStalk : (StructureSheaf.toStalk R y).hom.Flat := by
  have : (show PrimeSpectrum (R : Type u) from y).asIdeal.IsPrime :=
    (show PrimeSpectrum (R : Type u) from y).isPrime
  let : Algebra (R : Type u) (((Spec R).presheaf.stalk y : CommRingCat.{u}) : Type u) :=
    (StructureSheaf.toStalk R y).hom.toAlgebra
  have : IsLocalization.AtPrime (((Spec R).presheaf.stalk y : CommRingCat.{u}) : Type u)
      (show PrimeSpectrum (R : Type u) from y).asIdeal :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk (R := (R : Type u)) y
  exact RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat (((Spec R).presheaf.stalk y : CommRingCat.{u}) : Type u)
      (show PrimeSpectrum (R : Type u) from y).asIdeal.primeCompl)

/-! ### The derived stalk of a sheafification -/

section Derived

/-- **Stacks 01HV in the derived category.** Total derived extension of scalars along the germ map
`R ⟶ 𝒪_{Spec R, y}` is derived sheafification followed by the derived stalk at `y`.

The germ map is flat by `flat_toStalk`, so extension of scalars along it is exact and its total
left derived functor is the functor it induces degreewise on derived categories: both are left
derived functors of the same functor, and `CategoryTheory.Functor.leftDerivedNatIso` identifies
them. What remains is `tildeLocalRingStalkIso` carried along `mapDerivedCategoryIsoOfNatIso`,
with `mapDerivedCategoryCompIso` splitting the composite. -/
public def derivedTildeStalkIsoToStalk :
    (totalDerivedExtensionScalars.{u, u, u}
        (A := ((Spec R).presheaf.stalk y : Type u)) (StructureSheaf.toStalk R y).hom).functor ≅
      (tilde.functor R).mapDerivedCategory ⋙ derivedStalkFunctor (X := Spec R) y := by
  letI : (ModuleCat.extendScalars.{u, u, u}
      (S := ((Spec R).presheaf.stalk y : Type u)) (StructureSheaf.toStalk R y).hom).Additive :=
    extendScalars_additive _
  letI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u}
      (S := ((Spec R).presheaf.stalk y : Type u)) (StructureSheaf.toStalk R y).hom) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat.{u, u, u} _ (flat_toStalk R y)
  letI : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u}
      (S := ((Spec R).presheaf.stalk y : Type u)) (StructureSheaf.toStalk R y).hom) :=
    ModuleCat.extendScalars_preservesFiniteColimits.{u, u, u} _
  haveI := Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (ModuleCat.{u} (R : Type u)) (ComplexShape.up ℤ))
    (ModuleCat.extendScalars.{u, u, u} (S := ((Spec R).presheaf.stalk y : Type u))
      (StructureSheaf.toStalk R y).hom).mapDerivedCategory
    (ModuleCat.extendScalars.{u, u, u} (S := ((Spec R).presheaf.stalk y : Type u))
      (StructureSheaf.toStalk R y).hom).mapDerivedCategoryFactors
  haveI := (totalDerivedExtensionScalars.{u, u, u}
    (A := ((Spec R).presheaf.stalk y : Type u)) (StructureSheaf.toStalk R y).hom).isLeftDerived
  exact Functor.leftDerivedNatIso
      (totalDerivedExtensionScalars.{u, u, u}
        (A := ((Spec R).presheaf.stalk y : Type u)) (StructureSheaf.toStalk R y).hom).functor
      (ModuleCat.extendScalars.{u, u, u} (S := ((Spec R).presheaf.stalk y : Type u))
        (StructureSheaf.toStalk R y).hom).mapDerivedCategory
      (totalDerivedExtensionScalars.{u, u, u}
        (A := ((Spec R).presheaf.stalk y : Type u)) (StructureSheaf.toStalk R y).hom).comparison
      (ModuleCat.extendScalars.{u, u, u} (S := ((Spec R).presheaf.stalk y : Type u))
        (StructureSheaf.toStalk R y).hom).mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso (ModuleCat.{u} (R : Type u)) (ComplexShape.up ℤ))
      (Iso.refl _) ≪≫
    mapDerivedCategoryIsoOfNatIso
      (ModuleCat.extendScalars.{u, u, u} (S := ((Spec R).presheaf.stalk y : Type u))
        (StructureSheaf.toStalk R y).hom)
      (tilde.functor R ⋙ modulesStalkFunctor (Spec R) y)
      (tildeLocalRingStalkIso R y).symm ≪≫
    mapDerivedCategoryCompIso (tilde.functor R) (modulesStalkFunctor (Spec R) y)

/-- **The derived stalk on an affine scheme is the derived localization of the derived global
sections.** For `E ∈ D(𝒪_{Spec R})` with quasi-coherent cohomology sheaves, the derived stalk of
`E` at `y` is `RΓ(Spec R, E) ⊗ᴸ_R 𝒪_{Spec R, y}`.

`E` is the sheafification of its derived global sections, the counit of the derived Spec–Γ
adjunction being invertible on quasi-coherent cohomology
(`AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_counit_app`, Stacks 06Z0), and
`derivedTildeStalkIsoToStalk` computes the derived stalk of a sheafification. -/
public def affineDerivedStalkSectionsIso (E : DerivedCategory (Spec R).Modules)
    (hE : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj E).IsQuasicoherent) :
    (totalDerivedExtensionScalars.{u, u, u}
        (A := ((Spec R).presheaf.stalk y : Type u))
        (StructureSheaf.toStalk R y).hom).functor.obj
        ((derivedGlobalSectionsOver (𝟙 (Spec R))).obj E) ≅
      (derivedStalkFunctor (X := Spec R) y).obj E :=
  haveI : IsIso ((derivedTildeGlobalSectionsAdjunction R).val.counit.app E) :=
    isIso_derivedTildeGlobalSectionsAdjunction_counit_app R ⟨E, hE⟩
  (derivedTildeStalkIsoToStalk R y).app _ ≪≫
    (derivedStalkFunctor (X := Spec R) y).mapIso
      (((derivedTildeCompι R).app
          ((derivedGlobalSectionsOver (𝟙 (Spec R))).obj E)).symm ≪≫
        asIso ((derivedTildeGlobalSectionsAdjunction R).val.counit.app E))

end Derived

/-! ### The derived stalk at a point of an affine open -/

section OpenImmersion

attribute [local instance] hasDerivedCategory_ringedSpaceModules

/-- **The derived stalk at a point of an affine open is the derived localization of the sections
over that open.** Let `i : Spec R ⟶ X` be a morphism of schemes out of an affine scheme, `y` a
point of `Spec R`, and `K ∈ D(𝒪_X)` an object with quasi-coherent cohomology sheaves. Then

`RΓ(U, K) ⊗ᴸ_R 𝒪_{Spec R, y} ≅ (K_{i y}) ⊗ᴸ_{𝒪_{X, i y}} 𝒪_{Spec R, y}`,

where `RΓ(U, K)` is `AlgebraicGeometry.affineDerivedSections i` applied to `K`.  When `i` is an
open immersion with image `U` the extension of scalars on the right is along the germ
isomorphism `𝒪_{X, i y} ≅ 𝒪_{Spec R, y}`, so the right-hand side *is* the derived stalk of `K`
at the point `i y` of `U`, and the two sides are the two readings of that derived stalk; the
statement itself asks nothing of `i`.

The left-hand side is the derived localization at `y` of the derived global sections of the
derived pullback of `K` to `Spec R`, which has quasi-coherent cohomology by Stacks 08DW, so
`affineDerivedStalkSectionsIso` identifies it with the derived stalk at `y` of that pullback;
`AlgebraicGeometry.derivedPullbackStalkIso` then moves the stalk from `Spec R` to `X`. -/
@[stacks 0DJ8 "the first of the two inputs still needed to turn condition (1) into condition \
(2): the derived stalk of K at a point of an affine open, identified with the derived \
localization of RGamma(U,K) there. This is that identification only; the compatibility of the \
base-change comparison of Tag 065Z with localization, which is the second input, is not proved \
anywhere, so condition (1) implies condition (2) is NOT formalized"]
public def derivedStalkAffineSectionsIsoToStalk {X : Scheme.{u}} {A : CommRingCat.{u}}
    (i : Spec A ⟶ X) (y : Spec A) (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent) :
    (totalDerivedExtensionScalars.{u, u, u}
        (A := ((Spec A).presheaf.stalk y : Type u))
        (StructureSheaf.toStalk A y).hom).functor.obj
        ((affineDerivedSections i).obj K) ≅
      (totalDerivedExtensionScalars.{u, u, u} (i.stalkMap y).hom).functor.obj
        ((derivedStalkFunctor (i y)).obj K) :=
  affineDerivedStalkSectionsIso A y ((Stacks.Duality.derivedPullback i).obj K)
      (fun n => Stacks.Duality.isQuasicoherent_homology_derivedPullback' i ⟨K, hK⟩ n) ≪≫
    (derivedPullbackStalkIso i y).app K

end OpenImmersion

end AlgebraicGeometry

end
