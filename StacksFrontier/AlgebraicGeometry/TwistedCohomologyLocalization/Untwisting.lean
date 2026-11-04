module

public import StacksFrontier.AlgebraicGeometry.Cohomology.SchemeOpenRestriction.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NonvanishingSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare

/-!
# Untwisting by a power of a nonvanishing section, on cohomology

Let `X` be a scheme, `ℒ` an invertible `𝒪_X`-module, `s ∈ Γ(X, ℒ)` a global section and `ℱ` an
arbitrary `𝒪_X`-module. For every open `W ⊆ X_s` inside the nonvanishing locus of `s` and every
`n : ℕ`, multiplication by `sⁿ` induces an **isomorphism**

`H^p(W, ℱ) ⟶ H^p(W, ℱ ⊗ ℒ^{⊗ n})`

in every cohomological degree `p`. Its inverse is the map written `s^{-n}` in
[Stacks, Tag 09MR], and this is the statement that gives that map a meaning.

## Why this is the missing step

[Stacks, Tag 01CY] gives the trivialization of `ℒ` on `X_s`, and
`Stacks.InverseSection.bijective_sectionPowerAction_app` turns it into bijectivity of
`Γ(W, ℱ) ⟶ Γ(W, ℱ ⊗ ℒ^{⊗ n})` for **every** open `W ⊆ X_s`, every `n` and an arbitrary `ℱ`.
`Stacks.Cohomology.SchemeOpenRestriction.isIso_hfunctor_map_of_bijective_app` promotes a
sectionwise statement over all opens inside `W` to an isomorphism on `H^p(W, -)`. Composing the
two is the result below, and it is the input without which the comparison map of
[Stacks, Tag 09MR] has no definition.

## Main results

* `Stacks.Cohomology.Untwisting.nonvanishingOpen_eq_trivialize`: the nonvanishing open of
  [Stacks, Tag 01CY] in the spelling of the tensor-power development is the one of the
  trivialization development.
* `Stacks.Cohomology.Untwisting.isIso_hfunctor_map_sectionPowerAction`: **multiplication by
  `sⁿ` is an isomorphism on the cohomology of every open inside `X_s`**, in every degree.
* `Stacks.Cohomology.Untwisting.isIso_hfunctor_map_sectionPowerAction_of_isSectionPowerHom`: the
  same for an arbitrary morphism representing `sⁿ`, which is the form in which consumers of
  [Stacks, Tag 01XR] state multiplication by a power.

## Implementation notes

**Three spellings of the nonvanishing open are in play**, and this file crosses two of them.
`Stacks.SheafOfModules.nonvanishingOpen` forms `𝔪_x · ℒ_x` in the stalk module of
[Stacks, Tag 01CB] and is the spelling of the tensor-power and graded-section-ring development;
`Stacks.NonvanishingTrivialize.nonvanishingOpen` forms it in Mathlib's stalk module and is the
spelling in which the trivialization clause of [Stacks, Tag 01CY] is proved. They are identified
through the scheme-level `Stacks.Ample.nonvanishingLocus` by
`Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq` and
`Stacks.NonvanishingSpelling.nonvanishingLocus_eq`.

**The invertibility hypothesis is taken once and transported twice.** There are two
`IsInvertible` classes with the same content, `Stacks.SheafOfModules.IsInvertible` and
`AlgebraicGeometry.SheafOfModules.IsInvertible`; the statements below take the former, which is
the one the graded section ring and the nonvanishing open of the tensor-power development are
indexed by, and `Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry` supplies the latter,
which the trivialization development is indexed by. Instance search crosses neither that gap nor
the one from invertibility to `(tensorRightFunctor _ _ ℒ).IsEquivalence`, so all four are
installed as local instances, as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/NonvanishingSections.lean`.

Nothing here assumes quasi-coherence of `ℱ`, compactness or quasi-separatedness of `X`, or
positivity of `p`: the statement is about an open inside `X_s`, where the invertible module is
trivial, and no cohomology vanishes.

## References

* [Stacks Project, Tag 09MR](https://stacks.math.columbia.edu/tag/09MR)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SheafOfModules

universe u

namespace Stacks.Cohomology.Untwisting

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.presheaf
    (structureSheafRing X.toRingedSpace).property L]

/-- The invertibility hypothesis at the spelling of the structure sheaf in which the
trivialization clause of [Stacks, Tag 01CY] is stated. Instance search does not cross the two
spellings, so the bridge is applied by hand. -/
local instance isInvertibleSheafObj :
    IsInvertible (SheafedSpace.sheaf X.toRingedSpace).obj
      (_root_.structureSheaf X.toRingedSpace.sheaf).property L := ‹_›

/-- The same hypothesis for the parallel `AlgebraicGeometry.SheafOfModules.IsInvertible`, the
class by which `Stacks.NonvanishingTrivialize.nonvanishingOpen` is indexed. The two classes have
the same content, by `Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`. -/
local instance isInvertibleAlgebraicGeometry :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (SheafedSpace.sheaf X.toRingedSpace).obj
      (_root_.structureSheaf X.toRingedSpace.sheaf).property L :=
  IsInvertible.toAlgebraicGeometry _ _ L ‹_›

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

/-- The same at the spelling of the structure sheaf used by the trivialization development. -/
local instance tensorRightEquivalenceSheafObj :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
      ⟨(SheafedSpace.sheaf X.toRingedSpace).obj,
        Presheaf.isSheaf_of_isSheaf_comp _ ((SheafedSpace.sheaf X.toRingedSpace).obj)
          (forget₂ CommRingCat RingCat)
          ((_root_.structureSheaf X.toRingedSpace.sheaf).property)⟩).flip.obj (L))).IsEquivalence :=
  TensorPower.isEquivalence_tensorRightFunctor (SheafedSpace.sheaf X.toRingedSpace).obj
    (_root_.structureSheaf X.toRingedSpace.sheaf).property L

/-- **The two spellings of the nonvanishing open `X_s` of [Stacks, Tag 01CY] agree.** The left
side forms `𝔪_x · ℒ_x` in the stalk module of [Stacks, Tag 01CB], the right side in Mathlib's;
both are identified with the scheme-level locus by
`StacksFrontier/AlgebraicGeometry/NonvanishingSpelling/Basic.lean`. -/
theorem nonvanishingOpen_eq_trivialize (s : L.sections) :
    nonvanishingOpen L s = Stacks.NonvanishingTrivialize.nonvanishingOpen X.toRingedSpace L s :=
  Opens.ext ((Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq X L s).trans
    (Stacks.NonvanishingSpelling.nonvanishingLocus_eq X L s).symm)

/-- **Multiplication by `sⁿ` is an isomorphism on the cohomology of every open inside the
nonvanishing locus of `s`.**

Let `X` be a scheme, `ℒ` an invertible `𝒪_X`-module, `s` a global section of `ℒ`, `ℱ` an
arbitrary `𝒪_X`-module, `n : ℕ` and `W ⊆ X_s` an open inside the nonvanishing locus. Then the
map `H^p(W, ℱ) ⟶ H^p(W, ℱ ⊗ ℒ^{⊗ n})` induced by multiplication by `sⁿ` is an isomorphism, in
every cohomological degree `p`.

The section-level input is `Stacks.InverseSection.bijective_sectionPowerAction_app`, the
trivialization clause of [Stacks, Tag 01CY] read for an arbitrary module and an arbitrary power;
it is available over *every* open inside `X_s`, which is exactly what
`Stacks.Cohomology.SchemeOpenRestriction.isIso_hfunctor_map_of_bijective_app` consumes. -/
theorem isIso_hfunctor_map_sectionPowerAction (s : L.sections) (F : X.Modules) (n : ℕ)
    (W : X.Opens) (hW : W ≤ nonvanishingOpen L s) (p : ℕ) :
    IsIso ((Hfunctor X.ringCatSheaf W p).map
      (sectionPowerAction (sectionSiteRing X) (sectionSiteSheaf X) L F (n : ℤ)
        (sectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s n))) := by
  refine Stacks.Cohomology.SchemeOpenRestriction.isIso_hfunctor_map_of_bijective_app W p _
    fun V hV => ?_
  exact Stacks.InverseSection.bijective_sectionPowerAction_app X.toRingedSpace L s
    (hV.trans (nonvanishingOpen_eq_trivialize X L s ▸ hW)) F n

/-- **Multiplication by any morphism representing `sⁿ` is an isomorphism on the cohomology of an
open inside `X_s`.** The representing morphism in a given degree is unique
(`Stacks.SheafOfModules.IsSectionPowerHom.unique`), so this is
`isIso_hfunctor_map_sectionPowerAction`. This is the form in which the consumers of
[Stacks, Tag 01XR] quantify over a power of a section. -/
theorem isIso_hfunctor_map_sectionPowerAction_of_isSectionPowerHom (s : L.sections)
    (F : X.Modules) (n : ℕ)
    (t : _root_.SheafOfModules.unit X.ringCatSheaf ⟶
      TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (n : ℤ))
    (ht : IsSectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s (n : ℤ) t)
    (W : X.Opens) (hW : W ≤ nonvanishingOpen L s) (p : ℕ) :
    IsIso ((Hfunctor X.ringCatSheaf W p).map
      (sectionPowerAction (sectionSiteRing X) (sectionSiteSheaf X) L F (n : ℤ) t)) := by
  have heq : t = sectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s n :=
    IsSectionPowerHom.unique (sectionSiteRing X) (sectionSiteSheaf X) L ht
      (isSectionPowerHom_sectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s n)
  rw [heq]
  exact isIso_hfunctor_map_sectionPowerAction X L s F n W hW p

end Stacks.Cohomology.Untwisting

end
