module

public import StacksFrontier.AlgebraicGeometry.Generators.Kernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Epimorphy of the conormal quotient map, [Stacks, Tag 01R3] part (1)

This file closes the part (1) label "sheaf quotient map is epimorphic" of
[Stacks, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3): for an immersion `i : Z ⟶ X` and
any closed-immersion factorization `i' : Z ⟶ U` of it, the ideal sheaf of `i'` surjects onto the
direct image along `i'` of the conormal sheaf of `i`.

## A recorded blocker that the affine formula dissolves

`StacksDraft.AlgebraicGeometry.F3.Conormal.IdealSheafComparison` reduces this label, by
`Stacks.Conormal.epi_conormalQuotientMap_iff`, to epimorphy of the adjunction unit
`I ⟶ i'_* i'^* I` at the ideal sheaf of a closed immersion, and records that as unproved,
"a statement about local surjectivity of `I ⟶ I ⊗ 𝒪_Z`, which needs the local generation of the
ideal sheaf … and the sheafification in the definition of the module pullback".

**No part of that is needed.** With the affine quotient formula of
`StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Factorization`, surjectivity over an affine open is
`Ideal.toCotangent_surjective` transported across
`Stacks.Conormal.pushforwardConormalIsoCotangent`: every class in `I.Cotangent` is
`I.toCotangent a` for some `a ∈ I`, every such `a` names a section of the ideal sheaf
(`Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff_mem_ker_ideal`), and the
formula says the quotient generator attached to that section is the class. Affine opens are a
basis, so local surjectivity follows at once, and
`Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective` converts it to epimorphy. The
adjunction unit is never mentioned, and neither is the pullback's sheafification.

## Main results

* `Stacks.Conormal.Tag01R3Generators.surjective_conormalQuotientMap_app`: over an affine open the
  quotient map is surjective on sections — not merely locally so.
* `Stacks.Conormal.Tag01R3Generators.isLocallySurjective_conormalQuotientMap`: hence locally
  surjective, affine opens being a basis
  (`AlgebraicGeometry.Scheme.isBasis_affineOpens`).
* `Stacks.Conormal.Tag01R3Generators.conormalQuotientMap_epi`: **the statement of the tag**, carrying
  the `stacks` attribute.

## Universe situation

A single universe `u`, as in the rest of the Tag 01R3 development.

## What is not done

* The adjunction unit's own epimorphy, which
  `StacksDraft.AlgebraicGeometry.F3.Conormal.IdealSheafComparison` names as the missing input, is
  a corollary and is recorded as `epi_unit_idealSheaf`; it is not a labelled assertion of the
  tag.
* **No part (2) label.** See the "What is not done" section of
  `StacksFrontier.AlgebraicGeometry.Generators.Basic`.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Conormal.Tag01R3Generators

open Stacks.Conormal.AffineCotangent

/-- **Over an affine open the conormal quotient map is surjective on sections.** Given a section
`t` of the direct image, the affine identification
`Stacks.Conormal.pushforwardConormalIsoCotangent` sends it to a class in `I.Cotangent`;
`Ideal.toCotangent_surjective` names that class by some `a ∈ I`,
`Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff_mem_ker_ideal` turns `a`
into a section `x` of the ideal sheaf, and
`Stacks.Conormal.pushforwardConormalIsoCotangent_apply` says the identification sends the
quotient generator of `x` to that same class. The identification being an isomorphism, `x` is a
preimage of `t`.

The presentation data is produced inside the proof, and its ideal identified with
`i'.ker.ideal ⟨V, hV⟩` by `presentationIdeal_eq_ker_app`, exactly as in
`conormalQuotientMap_kernel`. -/
theorem surjective_conormalQuotientMap_app {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i)
    (V : U.toScheme.Opens) (hV : IsAffineOpen V) :
    Function.Surjective
      ((Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (.op V)) := by
  intro t
  obtain ⟨I, e, he⟩ := Stacks.DiagonalPresentation.exists_presentation i' V hV
  have hI : I = i'.ker.ideal ⟨V, hV⟩ :=
    ((Stacks.DiagonalPresentation.presentation_ideal_eq i' V hV I e he).symm.trans
      (presentationIdeal_eq_ker_app i' V hV)).trans (i'.ker_apply ⟨V, hV⟩).symm
  obtain ⟨a, ha⟩ := Ideal.toCotangent_surjective I
    ((Stacks.Conormal.pushforwardConormalIsoCotangent i U i' hfac V hV I e he).hom.hom t)
  obtain ⟨x, hxa⟩ :=
    (Sections.exists_idealSheaf_section_iff_mem_ker_ideal i' V hV (a : Γ(U.toScheme, V))).2
      (hI ▸ a.2)
  have hxI : (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom i'.toLRSHom.toShHom))).val.app (.op V) x ∈ I := hxa ▸ a.2
  have : IsIso (Stacks.Conormal.pushforwardConormalIsoCotangent
    i U i' hfac V hV I e he).hom := Iso.isIso_hom _
  refine ⟨x, (ConcreteCategory.bijective_of_isIso
    (Stacks.Conormal.pushforwardConormalIsoCotangent i U i' hfac V hV I e he).hom).1 ?_⟩
  refine ((Stacks.Conormal.pushforwardConormalIsoCotangent_apply
    i U i' hfac V hV I e he x hxI).trans ?_).trans ha
  exact congrArg I.toCotangent (Subtype.ext hxa)

/-- **The conormal quotient map is locally surjective.** Immediate from
`surjective_conormalQuotientMap_app`, since the affine opens of a scheme are a basis
(`AlgebraicGeometry.Scheme.isBasis_affineOpens`): a section over an arbitrary open restricts to
an affine open around any of its points, and there it is hit on the nose. -/
theorem isLocallySurjective_conormalQuotientMap {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology U.toScheme)
      ((PresheafOfModules.toPresheaf _).map
        (Stacks.Conormal.conormalQuotientMap i U i' hfac).val) := by
  refine (TopCat.Presheaf.isLocallySurjective_iff _).mpr ?_
  intro W t p hp
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVW⟩ :=
    U.toScheme.isBasis_affineOpens.exists_subset_of_mem_open hp W.2
  obtain ⟨s, hs⟩ := surjective_conormalQuotientMap_app i U i' hfac V hV
    (((modulePushforward i'.toLRSHom.toShHom).obj (Stacks.Conormal.conormalSheaf i)).val.map
      (homOfLE hVW).op t)
  exact ⟨V, hVW, ⟨s, hs⟩, hpV⟩

/-- **[Stacks, Tag 01R3], part (1): the ideal sheaf surjects onto the pushforward conormal
sheaf.** For an immersion `i : Z ⟶ X` and any closed-immersion factorization `i' : Z ⟶ U`,
`Stacks.Conormal.conormalQuotientMap` is an epimorphism of sheaves of modules.

`Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective` at
`isLocallySurjective_conormalQuotientMap`. No affineness, Noetherian or finiteness hypothesis is
used, and `Stacks.Conormal.epi_conormalQuotientMap_iff`'s named blocker — epimorphy of the
adjunction unit — is bypassed rather than proved; see the module docstring. -/
@[stacks 01R3 "part (1): sheaf quotient map is epimorphic"]
theorem conormalQuotientMap_epi {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i) :
    Epi (Stacks.Conormal.conormalQuotientMap i U i' hfac) :=
  Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    (isLocallySurjective_conormalQuotientMap i U i' hfac)

/-- **The adjunction unit at the ideal sheaf of a closed immersion is an epimorphism.** This is
the statement `StacksDraft.AlgebraicGeometry.F3.Conormal.IdealSheafComparison` records as
unproved, and as what its epimorphy label reduces to by
`Stacks.Conormal.epi_conormalQuotientMap_iff`. That reduction is an iff, so with
`conormalQuotientMap_epi` it runs in the other direction too: the second factor of
`Stacks.Conormal.conormalQuotientMap` is the direct image of an isomorphism, hence an
isomorphism, and an isomorphism may be cancelled from the right of an epimorphism.

So `I ⟶ i'_* i'^* I` is an epimorphism at the ideal sheaf of any closed-immersion
factorization, with no appeal to the local generation of the ideal sheaf and none to the
sheafification in the definition of the module pullback. -/
theorem epi_unit_idealSheaf {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i) :
    Epi ((modulePullbackPushforwardAdjunction i'.toLRSHom.toShHom).unit.app
      (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom)) :=
  (Stacks.Conormal.epi_conormalQuotientMap_iff i U i' hfac).1
    (conormalQuotientMap_epi i U i' hfac)

end Stacks.Conormal.Tag01R3Generators

end
