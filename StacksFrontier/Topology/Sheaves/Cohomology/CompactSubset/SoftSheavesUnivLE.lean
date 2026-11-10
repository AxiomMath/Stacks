module

public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.SubsetSectionsUnivLE
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Acyclicity of soft sheaves, in a coefficient universe of its own

`CompactSubset/SoftAcyclic.lean` proves that a soft sheaf of abelian groups on a compact Hausdorff
space is right acyclic for global sections, but with the coefficient universe pinned to the
universe of the space: it is stated for
`Sheaf AddCommGrpCat.{u} Z` with `Z : TopCat.{u}`. The shape the derived clause of
[Stacks, Tag 0DCU] has — spaces in `TopCat.{u}`, coefficients `AddCommGrpCat.{max (u + 1) v}` —
is not an instance of that, so the pinned statement does not apply to it at all.

This file removes the pinning for the dimension-shifting half of that argument. The patching half
is already general: `Stacks.Topology.IsSoft`, `IsSoft.of_isFlasque`, `eq_zero_of_bot`,
`exists_glue_pair`, `restrict_add`, `restrict_sub`, `correction_agree`,
`exists_preimage_of_app_eq_zero`, `exists_lift_of_finset_univLE`,
`exists_lift_of_isSoft_of_isCompact_univLE`, `surjective_sections_of_isSoft_univLE` and
`IsSoft.of_shortExact_univLE` are all stated in `SoftSheaves.lean` itself at a coefficient universe
independent of the space. So softness is **one predicate**, not two, the patching theorem is **one
theorem**, and no transport mediates between the pinned theory and this one.

## Main definitions

All in the namespace `Stacks.Topology`.

* `sectionsFunctorUnivLE`: global sections. This is `Stacks.Topology.sectionsFunctor` with the
  coefficients freed, and is *definitionally* its `t := s` case.
* `isSoftPropertyUnivLE`: the class of soft abelian sheaves, as an `ObjectProperty`.

## Main results

* `exists_mono_isSoft_univLE`, `isSoft_and_shortExact_map_sections_univLE`,
  `rightAcyclic_sections_of_isSoft_univLE`: **a soft sheaf on a compact Hausdorff space is right
  acyclic for global sections, at a coefficient universe independent of the space.**
* `sectionsFunctorUnivLE_eq_sectionsFunctor`, `surjective_sections_of_isSoft_of_univLE`,
  `rightAcyclic_sections_of_isSoft_of_univLE`: nothing is weakened — at `t := s` these are the
  statements the development had while its coefficient universe was pinned, among them the
  library's own `Stacks.Topology.rightAcyclic_sections_of_isSoft`, with exactly the originals'
  hypotheses.

## Implementation notes

`EnoughInjectives` is *not* a hypothesis here, unlike in `SoftAcyclic.lean`: at mixed universes it
is a theorem, `Stacks.Topology.enoughInjectives_sheafOpens`. The derived-category hypotheses are
hypotheses, as they are in `CompactSubset/RestrictionVanishingUnivLE.lean`, and their indices are
free universe variables rather than the space's — an inhabitant of the first is
`CategoryTheory.HasDerivedCategory.standard` at `w := max (max (t + 1) s) t` given
`Stacks.Topology.isGrothendieckAbelian_sheafOpens`.

Sheaves are written in the site spelling `Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{t}`,
as in `SoftAcyclic.lean`, while `IsSoft` is stated for `TopCat.Sheaf`; the two types are
definitionally equal, so they are applied across the spelling with no transport, exactly as the
pinned `SoftAcyclic.lean` already does.

`EnoughInjectives` is *not* a hypothesis here, unlike in `SoftAcyclic.lean`: at mixed universes it
is a theorem, `Stacks.Topology.enoughInjectives_sheafOpens`. The derived-category hypotheses are
hypotheses, as they are in `CompactSubset/RestrictionVanishingUnivLE.lean`, and their indices are
free universe variables rather than the space's — an inhabitant of the first is
`CategoryTheory.HasDerivedCategory.standard` at `w := max (max (t + 1) s) t` given
`Stacks.Topology.isGrothendieckAbelian_sheafOpens`.

These declarations carry no tag. Stacks 0DCU has eight claim-sites and the covering set of the
tag is not complete until all of them are in the library; clause 8 is still unproved.

## References

* [Stacks Project, Tag 05T8](https://stacks.math.columbia.edu/tag/05T8)
* [Stacks Project, Tag 01EA](https://stacks.math.columbia.edu/tag/01EA)
* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped AlgebraicGeometry

namespace Stacks.Topology

universe w w' t s

noncomputable section

variable {Z : TopCat.{s}} [UnivLE.{s, t}]

/-- **The global sections functor on abelian sheaves over `Z`**, at a coefficient universe
independent of the space. This is `Stacks.Topology.sectionsFunctor` with the coefficients freed. -/
abbrev sectionsFunctorUnivLE (Z : TopCat.{s}) :
    Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{t} ⥤ AddCommGrpCat.{t} :=
  sectionsAtFunctorUnivLE.{t} Z ⊤

/-- The class of soft abelian sheaves on `Z`, at a coefficient universe independent of the space.
-/
abbrev isSoftPropertyUnivLE (Z : TopCat.{s}) :
    ObjectProperty (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{t}) :=
  fun F ↦ IsSoft F

/-- **Every abelian sheaf embeds into a soft one**, at a coefficient universe independent of the
space. An injective abelian sheaf has surjective restriction maps, hence is flasque, hence soft.
`EnoughInjectives` is not a hypothesis: at mixed universes it is
`Stacks.Topology.enoughInjectives_sheafOpens`. -/
theorem exists_mono_isSoft_univLE
    (F : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{t}) :
    ∃ (G : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{t})
      (_ : isSoftPropertyUnivLE.{t} Z G) (i : F ⟶ G), Mono i := by
  have _hei : EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{t} Z) :=
    enoughInjectives_sheafOpens.{t} Z
  obtain ⟨p⟩ := EnoughInjectives.presentation (C := TopCat.Sheaf AddCommGrpCat.{t} Z) F
  have : Injective p.J := p.injective
  have := isFlasque_of_injective.{t} p.J
  exact ⟨p.J, IsSoft.of_isFlasque p.J, p.f, p.mono⟩

variable [CompactSpace Z] [T2Space Z]

/-- **The two-out-of-three property for soft sheaves, with exactness of global sections**, at a
coefficient universe independent of the space. -/
theorem isSoft_and_shortExact_map_sections_univLE
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{t}))
    (hS : S.ShortExact) (h₁ : isSoftPropertyUnivLE.{t} Z S.X₁)
    (h₂ : isSoftPropertyUnivLE.{t} Z S.X₂) :
    isSoftPropertyUnivLE.{t} Z S.X₃ ∧ (S.map (sectionsFunctorUnivLE.{t} Z)).ShortExact := by
  refine ⟨IsSoft.of_shortExact_univLE.{t} hS h₁ h₂, ?_⟩
  obtain ⟨hExact, hMono⟩ :=
    (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
      (sectionsFunctorUnivLE.{t} Z)).mp inferInstance S hS
  refine { exact := hExact, mono_f := hMono, epi_g := ?_ }
  exact (AddCommGrpCat.epi_iff_surjective _).2 (surjective_sections_of_isSoft_univLE.{t} hS h₁)

variable [HasDerivedCategory.{w} (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{t})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{t}]
  [((sectionsFunctorUnivLE.{t} Z).mapHomotopyCategoryPlus ⋙
    DerivedCategory.Plus.Qh).HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{t}))]

/-- **A soft sheaf on a compact Hausdorff space is acyclic for global sections, at a coefficient
universe independent of the space.** Its higher cohomology therefore vanishes.

This is the acyclicity that [Stacks, Tag 09V3] needs of the restriction of an injective abelian
sheaf to a quasi-compact subset with separated points, in the universes the derived clause of
[Stacks, Tag 0DCU] presents it at. -/
@[sga "4 V 4.13" "special case", sga "6 II 2.3.1" "special case"]
theorem rightAcyclic_sections_of_isSoft_univLE
    (F : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{t}) (hF : IsSoft F) :
    (sectionsFunctorUnivLE.{t} Z).rightAcyclic F :=
  have _hei : EnoughInjectives (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{t}) :=
    enoughInjectives_sheafOpens.{t} Z
  Functor.le_rightAcyclic (sectionsFunctorUnivLE.{t} Z) (isSoftPropertyUnivLE.{t} Z)
    exists_mono_isSoft_univLE.{t} isSoft_and_shortExact_map_sections_univLE.{t} F hF

end

section NoWeakening

noncomputable section

variable {Z : TopCat.{s}}

/-- **Nothing is weakened: at `t := s` the global sections functor of this file is the library's
`Stacks.Topology.sectionsFunctor`**, and not merely isomorphic to it. -/
theorem sectionsFunctorUnivLE_eq_sectionsFunctor :
    sectionsFunctorUnivLE.{s} Z = sectionsFunctor Z :=
  rfl

variable [CompactSpace Z] [T2Space Z]

/-- **Nothing is weakened: at `t := s` the patching theorem of `SoftSheaves.lean` is the
statement `surjective_sections_of_isSoft_univLE` it is proved from** — the same statement about
the same map, in the `TopCat.Sheaf` spelling, with exactly the original's hypotheses. -/
theorem surjective_sections_of_isSoft_of_univLE
    {S : ShortComplex (Sheaf AddCommGrpCat.{s} Z)} (hS : S.ShortExact) (hsoft : IsSoft S.X₁) :
    Function.Surjective (ConcreteCategory.hom (S.g.hom.app (op (⊤ : Opens Z)))) :=
  surjective_sections_of_isSoft_univLE.{s} hS hsoft

/-- **Nothing is weakened: at `t := s` the acyclicity proved here is the library's
`Stacks.Topology.rightAcyclic_sections_of_isSoft`** — the same conclusion about the library's own
`Stacks.Topology.sectionsFunctor`, with exactly the original's hypotheses. -/
theorem rightAcyclic_sections_of_isSoft_of_univLE
    [HasDerivedCategory.{w} (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{s})]
    [HasDerivedCategory.{w'} AddCommGrpCat.{s}]
    [EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{s} Z)]
    [((sectionsFunctor Z).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{s}))]
    (F : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{s}) (hF : IsSoft F) :
    (sectionsFunctor Z).rightAcyclic F :=
  rightAcyclic_sections_of_isSoft_univLE.{w, w', s} F hF

end

end NoWeakening

end Stacks.Topology

end
