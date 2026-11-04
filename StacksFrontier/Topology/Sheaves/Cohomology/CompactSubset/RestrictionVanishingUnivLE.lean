module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaRightDerivedUnivLE
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.RestrictionUnivLE

/-!
# Vanishing of the higher cohomology of a restriction, in a coefficient universe of its own

`Stacks.Topology.isZero_cohomologyPresheaf_pullback_of_isFlasque` proves
`H^p(Z, F|_Z) = 0` for `p > 0`, for `F` flasque on `X` and `Z ⊆ X` quasi-compact with separated
points, but only with the coefficient universe pinned to the universe of the space: it is stated
for `F : X.Sheaf AddCommGrpCat.{u}` with `X : TopCat.{u}`, and *cannot be instantiated* at the
shape the derived clause of [Stacks, Tag 0DCU] has. The failure, at spaces in `TopCat.{u}`
and coefficients `AddCommGrpCat.{max (u + 1) v}`, is

```
failed to synthesize instance of type class
  Category.{u, max (u + 2) (v + 1)} AddCommGrpCat
```

— the restriction itself cannot be written, because `TopCat.Sheaf.pullback` ties the coefficients
to the space. Two further pinnings sit behind that one: `Sheaf.cohomologyPresheaf`, whose
coefficient universe is the hom universe of the site, and
`Stacks.Cohomology.SpectralLimit.cohomologyIsoRightDerivedSections`, which is stated only at
`.{u, u, u}`.

This file removes all three. The restriction is
`Stacks.Topology.restrictionFunctorUnivLE`, the cohomology presheaf is
`Stacks.Cohomology.FreeYonedaUnivLE.cohomologyPresheaf`, and the comparison with right-derived
sections is `Stacks.Cohomology.FreeYonedaUnivLE.cohomologyPresheafObjIsoRightDerivedSections`.

What remains pinned, and is therefore a hypothesis here rather than a conclusion, is the
*acyclicity* input: `Stacks.Topology.rightAcyclic_sections_of_isSoft` and the softness of the
restriction of a flasque sheaf are proved only at `AddCommGrpCat.{u}` on `TopCat.{u}`, because
the whole soft-sheaf development is. So the theorems below take right-acyclicity of sections of
the restriction as a hypothesis and discharge everything downstream of it. At `t := s` that
hypothesis is exactly what `Stacks.Topology.rightAcyclic_sections_pullback_of_isFlasque` supplies,
which is the content of `isZero_sheafCohomologyPresheaf_pullback_of_isFlasque` below — the
no-weakening statement.

## Main results

All in the namespace `Stacks.Topology`.

* `isZero_cohomologyPresheaf_restriction_of_isZero_rightDerived`: the transport, with vanishing of
  right-derived sections as the hypothesis.
* `isZero_cohomologyPresheaf_restriction_of_rightAcyclic`: the same with right-acyclicity of
  sections of the restriction as the hypothesis, in the shape
  `Stacks.Topology.rightAcyclic_sections_of_isSoft` produces.
* `isZero_sheafCohomologyPresheaf_pullback_of_isFlasque`: the `t := s` case, which is
  `Stacks.Topology.isZero_cohomologyPresheaf_pullback_of_isFlasque` verbatim — same hypotheses,
  same conclusion about Mathlib's `CategoryTheory.Sheaf.cohomologyPresheaf` — so nothing is
  weakened.

## Implementation notes

The `HasDerivedCategory` indices are free universe variables, as they are in
`CompactSubset/RestrictionVanishing.lean`. That is not cosmetic: pinning one of them to the
universe of the space gives a statement that builds, is complete and passes `#print axioms`,
and has no inhabitant anywhere. An inhabitant of the index
used here is `CategoryTheory.HasDerivedCategory.standard`, and `EnoughInjectives` at mixed
universes is `Stacks.Topology.enoughInjectives_sheafOpens`; both are exercised by an
instantiation check for this file.

These declarations carry no tag. Stacks 0DCU has eight claim-sites and the covering set of the
tag is not complete until all of them are in the library.

## References

* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 09V5](https://stacks.math.columbia.edu/tag/09V5)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

namespace Stacks.Topology

universe w w' t s

noncomputable section

variable {X : TopCat.{s}} (F : X.Sheaf AddCommGrpCat.{max s t}) {Z : Set X}

/-- Global sections of abelian sheaves on a space, in any coefficient universe dominating it.
This is `Stacks.Topology.sectionsFunctor` with the coefficients freed. -/
abbrev restrictionSectionsFunctor (Y : TopCat.{s}) :
    Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{max s t} ⥤ AddCommGrpCat.{max s t} :=
  (sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{max s t}).obj (op ⊤)

/-- The cohomology presheaf of an abelian sheaf on a space, in any coefficient universe
dominating it. This is `Stacks.Cohomology.FreeYonedaUnivLE.cohomologyPresheaf` at the site of
opens; `Sheaf.cohomologyPresheaf` is the same presheaf with the coefficients pinned. -/
abbrev restrictionCohomologyPresheaf (Y : TopCat.{s})
    [HasExt.{max s t} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{max s t})]
    (G : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{max s t}) (p : ℕ) :
    (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{max s t} :=
  Stacks.Cohomology.FreeYonedaUnivLE.cohomologyPresheaf.{max s t, max s t}
    (J := Opens.grothendieckTopology Y) G p

variable [HasExt.{max s t} (Sheaf (Opens.grothendieckTopology (TopCat.of Z))
    AddCommGrpCat.{max s t})]
  [HasInjectiveResolutions (Sheaf (Opens.grothendieckTopology (TopCat.of Z))
    AddCommGrpCat.{max s t})]

/-- **The cohomology presheaf of a restriction vanishes where right-derived sections do**, at a
coefficient universe independent of the space. This is the transport along
`Stacks.Cohomology.FreeYonedaUnivLE.cohomologyPresheafObjIsoRightDerivedSections`, which is the
mixed-universe form of
`Stacks.Cohomology.SpectralLimit.cohomologyIsoRightDerivedSections`. -/
theorem isZero_cohomologyPresheaf_restriction_of_isZero_rightDerived (p : ℕ)
    (hzero : IsZero (((restrictionSectionsFunctor.{t} (TopCat.of Z)).rightDerived p).obj
      ((restrictionFunctorUnivLE.{max s t} X Z).obj F))) :
    IsZero ((restrictionCohomologyPresheaf.{t} (TopCat.of Z)
      ((restrictionFunctorUnivLE.{max s t} X Z).obj F) p).obj (op ⊤)) :=
  hzero.of_iso
    (Stacks.Cohomology.FreeYonedaUnivLE.cohomologyPresheafObjIsoRightDerivedSections.{t}
      (Opens.grothendieckTopology (TopCat.of Z))
      ((restrictionFunctorUnivLE.{max s t} X Z).obj F) p ⊤)

variable [HasDerivedCategory.{w} (Sheaf (Opens.grothendieckTopology (TopCat.of Z))
  AddCommGrpCat.{max s t})]
variable [HasDerivedCategory.{w'} AddCommGrpCat.{max s t}]
variable [EnoughInjectives (Sheaf (Opens.grothendieckTopology (TopCat.of Z))
  AddCommGrpCat.{max s t})]
variable [((restrictionSectionsFunctor.{t} (TopCat.of Z)).mapHomotopyCategoryPlus ⋙
  DerivedCategory.Plus.Qh).HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso
    (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t}))]

/-- **The higher cohomology of a restriction vanishes as soon as sections of the restriction are
right acyclic**, at a coefficient universe independent of the space. The hypothesis is the shape
`Stacks.Topology.rightAcyclic_sections_of_isSoft` produces; everything downstream of it — the
passage from right acyclicity to the vanishing of the higher right-derived functors, and from
those to the cohomology presheaf — is discharged here at mixed universes. -/
theorem isZero_cohomologyPresheaf_restriction_of_rightAcyclic
    (hacyc : (restrictionSectionsFunctor.{t} (TopCat.of Z)).rightAcyclic
      ((restrictionFunctorUnivLE.{max s t} X Z).obj F))
    (p : ℕ) (hp : 0 < p) :
    IsZero ((restrictionCohomologyPresheaf.{t} (TopCat.of Z)
      ((restrictionFunctorUnivLE.{max s t} X Z).obj F) p).obj (op ⊤)) := by
  have hiff := (Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    (restrictionSectionsFunctor.{t} (TopCat.of Z))
    ((restrictionFunctorUnivLE.{max s t} X Z).obj F)).2 inferInstance
  refine isZero_cohomologyPresheaf_restriction_of_isZero_rightDerived F p ?_
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ p _).2
    (hiff.1 hacyc (p : ℤ) (by exact_mod_cast hp))

section Pinned

omit [HasDerivedCategory.{w'} AddCommGrpCat.{max s t}] in
/-- **Nothing is weakened: at `t := s` the theorem above is
`Stacks.Topology.isZero_cohomologyPresheaf_pullback_of_isFlasque`.** Instantiated at `t := s` the
conclusion above is about
`Stacks.Cohomology.FreeYonedaUnivLE.cohomologyPresheaf`, and
`Stacks.Cohomology.FreeYonedaUnivLE.cohomologyPresheafObjIsoPinned` carries it to Mathlib's
`CategoryTheory.Sheaf.cohomologyPresheaf`; the right-acyclicity hypothesis is supplied by
`Stacks.Topology.rightAcyclic_sections_pullback_of_isFlasque`, which is where the pinned proof
gets it. So the generalisation implies the original, with exactly the original's hypotheses. -/
theorem isZero_sheafCohomologyPresheaf_pullback_of_isFlasque
    {Y : TopCat.{s}} (G : Y.Sheaf AddCommGrpCat.{s}) {W : Set Y}
    [HasExt.{s} (Sheaf (Opens.grothendieckTopology (TopCat.of W)) AddCommGrpCat.{s})]
    [HasInjectiveResolutions (Sheaf (Opens.grothendieckTopology (TopCat.of W))
      AddCommGrpCat.{s})]
    [HasDerivedCategory.{w} (Sheaf (Opens.grothendieckTopology (TopCat.of W))
      AddCommGrpCat.{s})]
    [HasDerivedCategory.{w'} AddCommGrpCat.{s}]
    [EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{s} (TopCat.of W))]
    [((sectionsFunctor (TopCat.of W)).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (Opens.grothendieckTopology (TopCat.of W)) AddCommGrpCat.{s}))]
    [TopCat.Sheaf.IsFlasque G] (hW : IsCompact W)
    (hSep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y →
      ∃ A B : Set Y, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    (p : ℕ) (hp : 0 < p) :
    IsZero ((Sheaf.cohomologyPresheaf ((TopCat.Sheaf.pullback AddCommGrpCat.{s}
      (Stacks.subsetInclusion Y W)).obj G) p).obj (op ⊤)) :=
  have _hei : EnoughInjectives
      (Sheaf (Opens.grothendieckTopology (TopCat.of W)) AddCommGrpCat.{s}) :=
    inferInstanceAs (EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{s} (TopCat.of W)))
  have _hrd : ((restrictionSectionsFunctor.{s} (TopCat.of W)).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (Opens.grothendieckTopology (TopCat.of W)) AddCommGrpCat.{s})) :=
    inferInstanceAs (((sectionsFunctor (TopCat.of W)).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (Opens.grothendieckTopology (TopCat.of W)) AddCommGrpCat.{s})))
  (isZero_cohomologyPresheaf_restriction_of_rightAcyclic G
      (rightAcyclic_sections_pullback_of_isFlasque G hW hSep) p hp).of_iso
    (Stacks.Cohomology.FreeYonedaUnivLE.cohomologyPresheafObjIsoPinned
      (Opens.grothendieckTopology (TopCat.of W))
      ((TopCat.Sheaf.pullback AddCommGrpCat.{s} (Stacks.subsetInclusion Y W)).obj G) p ⊤).symm

end Pinned

end

end Stacks.Topology

end
