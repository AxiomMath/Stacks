module

public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.InjectiveSheavesRestrictOnto
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.SoftSheaves
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Soft sheaves on a compact Hausdorff space are acyclic

Let `Z` be a compact Hausdorff space. This file proves that a soft sheaf of abelian groups on `Z`
is right acyclic for the global sections functor, so that its higher cohomology vanishes.

The proof is the acyclicity criterion [Stacks, Tag 05T8], `Functor.le_rightAcyclic`, run against
the class of soft sheaves. Its two hypotheses are exactly the two results of
`StacksFrontier/Topology/Sheaves/Cohomology/CompactSubset/SoftSheaves.lean`
together with one input from the library:

* every abelian sheaf embeds into a soft one, because it embeds into an injective one, an injective
  abelian sheaf has surjective restriction maps
  (`Stacks.Cohomology.InjectiveRestriction.injective_abelian_restriction_surjective`, Stacks 01EA)
  and a flasque sheaf is soft (`Stacks.Topology.IsSoft.of_isFlasque`);
* for a short exact sequence with soft `X₁` and `X₂` the quotient `X₃` is soft
  (`Stacks.Topology.IsSoft.of_shortExact_univLE`) and global sections stay exact — left exactness
  is formal and surjectivity is `Stacks.Topology.surjective_sections_of_isSoft_univLE`, the
  patching theorem.

## Main results

* `Stacks.Topology.exists_mono_isSoft`: every abelian sheaf on a compact Hausdorff space embeds
  into a soft one.
* `Stacks.Topology.isSoft_and_shortExact_map_sections`: the two-out-of-three property of soft
  sheaves, together with the exactness of global sections.
* `Stacks.Topology.rightAcyclic_sections_of_isSoft`: a soft sheaf is right acyclic for global
  sections.

## Implementation notes

The global sections functor is spelled as the composite `sheafToPresheaf ⋙ evaluation at ⊤`, not
as `(sheafSections _ _).obj (op ⊤)`, although the two are definitionally equal: it is the
composite spelling whose additivity and preservation of finite limits are available from those of
its two factors by instance search.

Softness is stated in `SoftSheaves.lean` for `TopCat.Sheaf AddCommGrpCat Z` while the derived
functor machinery and [Stacks, Tag 09V3] use `Sheaf (Opens.grothendieckTopology Z)
AddCommGrpCat`. The two types are definitionally equal — `TopCat.Sheaf` is a `nonrec def` for the
second with its category instance derived from it — so a sheaf, a short complex of sheaves, and
the short exactness of one are accepted in either spelling with no transport; this file is stated
in the site spelling throughout.

The derived category and the existence of the right derived functor are hypotheses, as in
[Stacks, Tag 09SY] for flasque sheaves of modules; under `EnoughInjectives` they are satisfied by
the standard derived category.

## References

* [Stacks Project, Tag 05T8](https://stacks.math.columbia.edu/tag/05T8)
* [Stacks Project, Tag 01EA](https://stacks.math.columbia.edu/tag/01EA)
* [Stacks Project, Tag 09V2](https://stacks.math.columbia.edu/tag/09V2)
* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped AlgebraicGeometry

namespace Stacks.Topology

universe w w' u

noncomputable section

variable {Z : TopCat.{u}}

/-- The global sections functor on abelian sheaves over `Z`. -/
abbrev sectionsFunctor (Z : TopCat.{u}) :
    Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⋙
    (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)

/-- The class of soft abelian sheaves on `Z`. -/
abbrev isSoftProperty (Z : TopCat.{u}) :
    ObjectProperty (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) :=
  fun F ↦ IsSoft F

/-- **Every abelian sheaf embeds into a soft one.** An injective abelian sheaf has surjective
restriction maps, hence is flasque, hence soft. -/
theorem exists_mono_isSoft [EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{u} Z)]
    (F : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) :
    ∃ (G : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) (_ : isSoftProperty Z G)
      (i : F ⟶ G), Mono i := by
  obtain ⟨p⟩ := EnoughInjectives.presentation (C := TopCat.Sheaf AddCommGrpCat.{u} Z) F
  have : Injective p.J := p.injective
  have : TopCat.Sheaf.IsFlasque p.J :=
    ⟨fun {U V} i ↦ (AddCommGrpCat.epi_iff_surjective _).2
      (Stacks.Cohomology.InjectiveRestriction.injective_abelian_restriction_surjective
        p.J (leOfHom i.unop))⟩
  exact ⟨p.J, IsSoft.of_isFlasque p.J, p.f, p.mono⟩

variable [CompactSpace Z] [T2Space Z]

/-- **The two-out-of-three property for soft sheaves, with exactness of global sections.** For a
short exact sequence of abelian sheaves on a compact Hausdorff space whose first two terms are
soft, the third is soft and the sequence of global sections is short exact. -/
theorem isSoft_and_shortExact_map_sections
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}))
    (hS : S.ShortExact) (h₁ : isSoftProperty Z S.X₁) (h₂ : isSoftProperty Z S.X₂) :
    isSoftProperty Z S.X₃ ∧ (S.map (sectionsFunctor Z)).ShortExact := by
  refine ⟨IsSoft.of_shortExact_univLE.{u} hS h₁ h₂, ?_⟩
  obtain ⟨hExact, hMono⟩ :=
    (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono (sectionsFunctor Z)).mp
      inferInstance S hS
  refine { exact := hExact, mono_f := hMono, epi_g := ?_ }
  exact (AddCommGrpCat.epi_iff_surjective _).2 (surjective_sections_of_isSoft_univLE.{u} hS h₁)

variable [HasDerivedCategory.{w} (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u}]
  [EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{u} Z)]
  [((sectionsFunctor Z).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}))]

/-- **A soft sheaf on a compact Hausdorff space is acyclic for global sections.** Its higher
cohomology therefore vanishes.

This is the vanishing that [Stacks, Tag 09V3] needs of the restriction of an injective abelian
sheaf to a quasi-compact subset with separated points: that restriction is soft. -/
@[sga "4 V 4.13" "special case", sga "6 II 2.3.1" "special case"]
theorem rightAcyclic_sections_of_isSoft
    (F : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}) (hF : IsSoft F) :
    (sectionsFunctor Z).rightAcyclic F :=
  Functor.le_rightAcyclic (sectionsFunctor Z) (isSoftProperty Z) exists_mono_isSoft
    isSoft_and_shortExact_map_sections F hF

end

end Stacks.Topology

end
