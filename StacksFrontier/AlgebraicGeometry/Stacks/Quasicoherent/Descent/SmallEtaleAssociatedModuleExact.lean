module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExactAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.SmallEtaleAssociatedModuleColimits

/-!
# `QCoh(𝒪_S) ⥤ Mod(S_étale, 𝒪)` is exact

Clause (5) of Stacks 06VE says that the second functor of that lemma, `𝓕 ↦ 𝓕^a` into the
`𝒪`-modules of the **small étale** site of `S`, is exact — unlike the first functor, into the
modules of a big site, which by clause (6) is only right exact.  The source's reason is that an
étale morphism is flat, Morphisms, Lemma 02GS.  Clause (4), right exactness, is the half of this
that holds for both functors.

Both halves follow from facts about the two factors of
`AlgebraicGeometry.SmallEtale.associatedModuleQcoh = ι ⋙ (𝓕 ↦ 𝓕^a)`.

* `𝓕 ↦ 𝓕^a` is left exact.  This is the exactness assertion of Stacks 08H8,
  `AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModuleOfSheaf`, and it is where
  the flatness of Stacks 02GS/0GNA enters: the criterion is Stacks 04JC applied to
  `AlgebraicGeometry.SmallEtale.isFlatMapULift_inverseImageStructureMap`.
* `𝓕 ↦ 𝓕^a` is right exact, being a left adjoint:
  `AlgebraicGeometry.SmallEtale.preservesFiniteColimits_associatedModuleOfSheaf`.
* The inclusion `QCoh(𝒪_S) ⥤ Mod(𝒪_S)` is exact, quasi-coherent modules on a scheme being a
  weak Serre subcategory —
  `Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerreClass`.

## Main results

* `AlgebraicGeometry.SmallEtale.preservesFiniteColimits_associatedModuleQcoh`:
  **Stacks 06VE (4) for the second functor** — `𝓕 ↦ 𝓕^a` into `Mod(S_étale, 𝒪)` is right exact.
* `AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModuleQcoh`: its left exactness,
  the half of **Stacks 06VE (5)** that distinguishes the small étale site from a big one.
* `AlgebraicGeometry.SmallEtale.shortExact_map_associatedModuleQcoh`: **Stacks 06VE (5)** in the
  form the word "exact" abbreviates — a short exact sequence of quasi-coherent `𝒪_S`-modules
  stays short exact after `𝓕 ↦ 𝓕^a`.

## Implementation notes

Left exactness is stated of
`AlgebraicGeometry.SmallEtale.associatedModuleQcoh`, the composite through
`AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf`, which is the retyping of
`AlgebraicGeometry.SmallEtale.associatedModule` onto the category instance of
`SheafOfModules.{u} S.ringCatSheaf`; the retyping is forced by
`CategoryTheory.ObjectProperty.ι` and is explained on
`AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf` itself.

The first functor of 06VE, into a big site, is **not** exact — that is clause (6);
`AlgebraicGeometry.BigFppfOver.preservesFiniteColimits_baseAssociatedModuleQcoh` is its
clause (4).

## References

* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 02GS](https://stacks.math.columbia.edu/tag/02GS)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 0GNA](https://stacks.math.columbia.edu/tag/0GNA)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06VE (4) for the second functor of the lemma.**  The functor
`QCoh(𝒪_S) ⥤ Mod(S_étale, 𝒪)`, `𝓕 ↦ 𝓕^a`, is right exact: the inclusion of the quasi-coherent
modules is right exact, quasi-coherence on a scheme being a weak Serre class, and `𝓕 ↦ 𝓕^a` is
right exact because it is a left adjoint. -/
@[stacks 06VE "part (4), small site at τ = étale"]
public theorem preservesFiniteColimits_associatedModuleQcoh :
    PreservesFiniteColimits (AlgebraicGeometry.SmallEtale.associatedModuleQcoh B S hS) := by
  have := ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass
    (SheafOfModules.isQuasicoherent S.ringCatSheaf)
  have : PreservesFiniteColimits (associatedModuleOfSheaf B S hS) :=
    ⟨fun _ _ _ => preservesColimitsOfShape_associatedModuleOfSheaf B S hS _⟩
  exact Limits.comp_preservesFiniteColimits
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι (associatedModuleOfSheaf B S hS)

/-- **The half of Stacks 06VE (5) that is special to the small étale site.**  The functor
`QCoh(𝒪_S) ⥤ Mod(S_étale, 𝒪)`, `𝓕 ↦ 𝓕^a`, is left exact.

The inclusion of the quasi-coherent modules is left exact because quasi-coherence on a scheme is
a weak Serre class, and `𝓕 ↦ 𝓕^a` is left exact because `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` is
flat — an étale morphism is flat, Morphisms, Lemma 02GS, which is Stacks 0GNA for `ε` and gives
the exactness assertion of Stacks 08H8. -/
@[stacks 06VE "part (5), left exactness half"]
public theorem preservesFiniteLimits_associatedModuleQcoh :
    PreservesFiniteLimits (associatedModuleQcoh B S hS) := by
  have := ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass
    (SheafOfModules.isQuasicoherent S.ringCatSheaf)
  exact Limits.comp_preservesFiniteLimits
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι (associatedModuleOfSheaf B S hS)

/-- **Stacks 06VE (5).**  The functor `QCoh(𝒪_S) ⥤ Mod(S_étale, 𝒪)`, `𝓕 ↦ 𝓕^a`, is exact: it
carries a short exact sequence of quasi-coherent `𝒪_S`-modules to a short exact sequence of
`𝒪`-modules on the small étale site. -/
@[stacks 06VE "part (5), as preservation of short exact sequences"]
public theorem shortExact_map_associatedModuleQcoh
    {T : ShortComplex (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory}
    (hT : T.ShortExact) : (T.map (associatedModuleQcoh B S hS)).ShortExact :=
  have := preservesFiniteLimits_associatedModuleQcoh B S hS
  have := preservesFiniteColimits_associatedModuleQcoh B S hS
  hT.map_of_exact _

end AlgebraicGeometry.SmallEtale

end
