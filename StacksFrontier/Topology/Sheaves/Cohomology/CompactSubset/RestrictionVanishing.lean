module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.NativeCohomologyCocones
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.FlasqueSoft

/-!
# Vanishing of the higher cohomology of the restriction of an injective sheaf

Let `X` be a topological space, let `Z ⊆ X` be a quasi-compact subset any two distinct points of
which have disjoint open neighbourhoods in `X`, and let `I` be an injective sheaf of abelian
groups on `X`. This file proves

`H^p(Z, I|_Z) = 0` for every `p > 0`,

where the cohomology is Mathlib's `CategoryTheory.Sheaf.cohomologyPresheaf` — the `Ext`-group out
of the free abelian sheaf on a representable presheaf — evaluated at the whole of `Z`.

This is the input of the positive-degree half of [Stacks, Tag 09V3], and it is what
[Stacks, Tag 09V5] uses to compute the cohomology of the fibre of a proper separated map.

## Main results

* `Stacks.Topology.isZero_cohomologyPresheaf_pullback_of_isFlasque`: the vanishing for the
  restriction of a flasque sheaf.
* `Stacks.Topology.isZero_cohomologyPresheaf_pullback_of_injective`: the vanishing for the
  restriction of an injective sheaf.

## Implementation notes

The route avoids Čech cohomology, and so avoids [Stacks, Tag 09V2], which the Stacks proof
uses: the restriction of a flasque sheaf is *soft*
(`Stacks.Topology.isSoft_pullback_of_isFlasque`), a soft sheaf on a compact Hausdorff space is
right acyclic for global sections (`Stacks.Topology.rightAcyclic_sections_of_isSoft`), right
acyclicity for a left exact functor is the vanishing of all its higher right derived functors
([Stacks, Tag 015C],
`CategoryTheory.Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus`), and
`Stacks.Cohomology.SpectralLimit.cohomologyIsoRightDerivedSections` identifies right derived
sections with the `Ext`-group that `Sheaf.cohomologyPresheaf` is.

Each hypothesis is stated in the spelling of the category of abelian sheaves on `Z` in which it
is consumed — `HasDerivedCategory` and the existence of the right derived functor in
`Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat`, `EnoughInjectives` in
`TopCat.Sheaf AddCommGrpCat Z`. The two types are definitionally equal, but instance search does
not cross the `nonrec def` between them, so an instance supplied in one spelling is not found in
the other.

## References

* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 09V5](https://stacks.math.columbia.edu/tag/09V5)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

namespace Stacks.Topology

universe w w' u

noncomputable section

variable {X : TopCat.{u}}
variable (F : X.Sheaf AddCommGrpCat.{u}) {Z : Set X}
variable [HasDerivedCategory.{w} (Sheaf (Opens.grothendieckTopology (TopCat.of Z))
  AddCommGrpCat.{u})]
variable [HasDerivedCategory.{w'} AddCommGrpCat.{u}]
variable [EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z))]
variable [((sectionsFunctor (TopCat.of Z)).mapHomotopyCategoryPlus ⋙
  DerivedCategory.Plus.Qh).HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso
    (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}))]

/-- The higher cohomology of the restriction of a flasque abelian sheaf to a quasi-compact
subset with separated points vanishes. -/
theorem isZero_cohomologyPresheaf_pullback_of_isFlasque [TopCat.Sheaf.IsFlasque F]
    (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    (p : ℕ) (hp : 0 < p) :
    IsZero ((((TopCat.Sheaf.pullback AddCommGrpCat.{u}
      (Stacks.subsetInclusion X Z)).obj F).cohomologyPresheaf p).obj (op ⊤)) := by
  have hacyc := rightAcyclic_sections_pullback_of_isFlasque F hZ hSep
  have hiff := (Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    (sectionsFunctor (TopCat.of Z))
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (Stacks.subsetInclusion X Z)).obj F)).2
    inferInstance
  have hzero : IsZero (((sectionsFunctor (TopCat.of Z)).rightDerived p).obj
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (Stacks.subsetInclusion X Z)).obj F)) :=
    (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ p _).2
      (hiff.1 hacyc (p : ℤ) (by exact_mod_cast hp))
  exact hzero.of_iso (Stacks.Cohomology.SpectralLimit.cohomologyIsoRightDerivedSections
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (Stacks.subsetInclusion X Z)).obj F) p ⊤)

/-- The higher cohomology of the restriction of an injective abelian sheaf to a quasi-compact
subset with separated points vanishes: `H^p(Z, I|_Z) = 0` for `p > 0`. -/
theorem isZero_cohomologyPresheaf_pullback_of_injective [Injective F] (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    (p : ℕ) (hp : 0 < p) :
    IsZero ((((TopCat.Sheaf.pullback AddCommGrpCat.{u}
      (Stacks.subsetInclusion X Z)).obj F).cohomologyPresheaf p).obj (op ⊤)) :=
  have : TopCat.Sheaf.IsFlasque F := isFlasque_of_injective F
  isZero_cohomologyPresheaf_pullback_of_isFlasque F hZ hSep p hp

end

end Stacks.Topology

end
