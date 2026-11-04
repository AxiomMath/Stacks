module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.AssociatedModuleColimits
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.TopologyIndependence

/-!
# Direct sums, colimits and right exactness of `𝓕 ↦ 𝓕^a` on every big site

Clauses (2), (3) and (4) of Stacks 06VE say that the functor
`QCoh(𝒪_S) ⥤ Mod((Sch/S)_τ, 𝒪)`, `𝓕 ↦ 𝓕^a`, commutes with direct sums, commutes with colimits,
and is right exact.  The module
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.AssociatedModuleColimits`
proves the first two for `τ = fppf`.  This file proves all three for **every**
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.

The two inputs are the same at every `τ` and both are already available.

* The functor is a left adjoint, hence cocontinuous:
  `AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_baseAssociatedModule`
  (`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseRingedSite.lean:317`) is the
  instance, for every `τ : SiteKind`, got from
  `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleAdjunction`.
* The colimits of the source category are the colimits of all `𝒪_S`-modules — Schemes,
  Section 01LA — which is
  `AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_isQuasicoherent_ι`, a statement about
  `QCoh(𝒪_S)` alone and so independent of `τ`.

The functor itself is `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleQcoh`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseFullyFaithful.lean:148`), over which
clause (1) of 06VE is already registered at every `τ`.

## Main results

* `AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_discrete_baseAssociatedModuleQcoh`:
  **Stacks 06VE (2) at every `τ`** — `𝓕 ↦ 𝓕^a` commutes with direct sums.
* `AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_baseAssociatedModuleQcoh`:
  **Stacks 06VE (3) at every `τ`** — it commutes with colimits.
* `AlgebraicGeometry.BigFppfOver.preservesFiniteColimits_baseAssociatedModuleQcoh`:
  **Stacks 06VE (4) at every `τ`** — it is right exact.
* `AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_of_isoBaseAssociatedModule`: the same
  three conclusions for any functor isomorphic to it, the form in which Remark 03FH transfers
  them to the sections description of Definition 03DU (3).

## Implementation notes

Right exactness is *not* deduced from the size-indexed clause (3): `PreservesFiniteColimits`
quantifies over finite categories in `Type 0`, whereas
`CategoryTheory.Limits.PreservesColimitsOfSize.{u, u}` quantifies over index categories at the
universe of the site, and neither contains the other.  It is instead the composite of the two
factors' finite-colimit preservation, the first factor's being
`CategoryTheory.ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass` applied to
`Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerreClass` — that
quasi-coherent modules on a scheme are a weak Serre subcategory, which is more than closure
under colimits but is what is available and is what makes the inclusion right exact with no
colimit-existence hypothesis.

The per-shape statement keeps the hypotheses of
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_isQuasicoherent_ι`: colimits of shape `K`
in the modules over a commutative ring and in all `𝒪_S`-modules.  Both are automatic at
`K : Type u` with `Category.{u} K`, the instantiation the size statement makes.

The size spelling is `PreservesColimitsOfSize.{u, u}`, at the universe of the site, following
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_associatedModuleQcoh`; a bare
`CategoryTheory.Limits.PreservesColimits` would bind the index universe to the hom universe of
the source, which is unrelated to the universe of `S`.

At `τ = .fppf` the functor here is
`AlgebraicGeometry.BigFppfOver.associatedModuleQcoh` definitionally — `baseAssociatedModule`
and `associatedModule` agree by `rfl` — so the fppf statements of
`…Descent.AssociatedModuleColimits` are the `τ = .fppf` case of these and are left in place:
they are the ones the rest of the development cites.

The source's *second* functor, `QCoh(𝒪_S) ⥤ Mod(S_τ, 𝒪)` into a small site, is a different
construction; at `τ = étale` clauses (2) and (3) for it are
`AlgebraicGeometry.SmallEtale.preservesColimitsOfShape_discrete_associatedModuleQcoh` and
`…preservesColimitsOfSize_associatedModuleQcoh`.

## References

* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 03DC](https://stacks.math.columbia.edu/tag/03DC)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 01LA](https://stacks.math.columbia.edu/tag/01LA)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe uK vK u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inclusion `QCoh(𝒪_S) ⥤ Mod(𝒪_S)` is right exact: quasi-coherent modules on a scheme are
a weak Serre subcategory, and the inclusion of such a subcategory preserves finite colimits.

This is the half of Stacks 06VE (4) that concerns the source category, and like
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_isQuasicoherent_ι` it is independent of
the topology. -/
public theorem preservesFiniteColimits_isQuasicoherent_ι :
    PreservesFiniteColimits (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι :=
  ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _


variable (τ : SiteKind)

/-- **Stacks 06VE (2), for every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.**  The functor
`QCoh(𝒪_S) ⥤ Mod((Sch/S)_τ, 𝒪)`, `𝓕 ↦ 𝓕^a`, commutes with direct sums: a direct sum is a
colimit over a discrete index category, so this is the discrete case of clause (3).

The earlier `AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_discrete_associatedModuleQcoh`
carries the clause string "big site at τ = fppf only", on the ground that the clause's inputs
were proved at fppf only.  They are not: the adjunction, and with it cocontinuity of
`𝓕 ↦ 𝓕^a`, exists at every `τ` as
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_baseAssociatedModule`, and the other
input is about `QCoh(𝒪_S)` alone.  Hence this statement, which drops the restriction. -/
@[stacks 06VE "part (2), big site (Sch/S)_τ, every τ"]
public theorem preservesColimitsOfShape_discrete_baseAssociatedModuleQcoh (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (baseAssociatedModuleQcoh B S hS τ) :=
  preservesColimitsOfShape_baseAssociatedModuleQcoh B S hS τ (Discrete I)

/-- **Stacks 06VE (3), for every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.**  The functor
`QCoh(𝒪_S) ⥤ Mod((Sch/S)_τ, 𝒪)`, `𝓕 ↦ 𝓕^a`, commutes with all colimits indexed at the size of
the site.

Scope as on
`AlgebraicGeometry.BigFppfOver.preservesColimitsOfShape_discrete_baseAssociatedModuleQcoh`. -/
@[stacks 06VE "part (3), big site (Sch/S)_τ, every τ"]
public theorem preservesColimitsOfSize_baseAssociatedModuleQcoh :
    PreservesColimitsOfSize.{u, u} (baseAssociatedModuleQcoh B S hS τ) := by
  constructor
  intro K _
  exact preservesColimitsOfShape_baseAssociatedModuleQcoh B S hS τ K

/-- **Stacks 06VE (4), for every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.**  The functor
`QCoh(𝒪_S) ⥤ Mod((Sch/S)_τ, 𝒪)`, `𝓕 ↦ 𝓕^a`, is right exact, i.e. commutes with finite colimits.

The source deduces this from clause (3); here it is the composite of the two factors' finite
colimit preservation, because `CategoryTheory.Limits.PreservesFiniteColimits` quantifies over
finite categories in `Type 0` while clause (3) above is stated at the universe of the site, and
neither statement contains the other. -/
@[stacks 06VE "part (4), big site (Sch/S)_τ, every τ"]
public theorem preservesFiniteColimits_baseAssociatedModuleQcoh :
    PreservesFiniteColimits (baseAssociatedModuleQcoh B S hS τ) := by
  have := preservesFiniteColimits_isQuasicoherent_ι S
  have : PreservesFiniteColimits (baseAssociatedModuleOfSheaf B S hS τ) :=
    inferInstanceAs (PreservesFiniteColimits (baseAssociatedModule B S hS τ))
  exact Limits.comp_preservesFiniteColimits
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι (baseAssociatedModuleOfSheaf B S hS τ)

/-- **Stacks 06VE (2), (3), (4) for the sections description, at every `τ`.**  Any functor out of
the quasi-coherent modules of `S` isomorphic to the associated-module functor of `(Sch/S)_τ`
commutes with direct sums, with colimits, and with finite colimits.

Stacks Definition 03DU (3) describes `𝓕^a` by its sections and Remark 03FH identifies that
description with the pullback along the morphism of ringed sites; this is the form in which that
identification discharges the three clauses for the sections description, the isomorphism being
its only input. -/
public theorem preservesColimitsOfSize_of_isoBaseAssociatedModule
    (G : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ))
    (e : G ≅ baseAssociatedModuleQcoh B S hS τ) :
    PreservesColimitsOfSize.{u, u} G ∧ PreservesFiniteColimits G := by
  have h := preservesColimitsOfSize_baseAssociatedModuleQcoh B S hS τ
  have h' := preservesFiniteColimits_baseAssociatedModuleQcoh B S hS τ
  exact ⟨preservesColimits_of_natIso e.symm, preservesFiniteColimits_of_natIso e.symm⟩

end AlgebraicGeometry.BigFppfOver

end
