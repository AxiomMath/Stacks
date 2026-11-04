module

public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison

/-!
# The nonvanishing locus of the section carried by a morphism out of the structure sheaf

`StacksFrontier/AlgebraicGeometry/NonvanishingSpelling/Basic.lean` identifies the three spellings of
the nonvanishing locus of [Stacks, Tag 01CY] that this repository carries, as functions of a
*section*: of a restriction-compatible family `s : M.sections`, or of a global section
`s : Γ(M, ⊤)`. This file adds the one leg that identification was missing, the leg through the
**morphism out of the structure sheaf** that a global section also is: a consumer that multiplies
by a section writes that section as `σ : 𝒪_X ⟶ M` and names its nonvanishing locus through
`SheafOfModules.unitHomEquiv`, while every producer of a nonvanishing section delivers a
`Γ(M, ⊤)` and names the locus through `Stacks.NonvanishingOpen.nonvanishingOpen`.

## Main results

* `Stacks.NonvanishingSpelling.sectionsEquiv_sectionsTopEquiv`: the two terminal-object
  section equivalences of the repository, `Stacks.NonvanishingSpelling.sectionsEquiv` (through
  `Stacks.SectionRingGeometric.sectionsEquivObj`) and
  `AlgebraicGeometry.Scheme.Modules.sectionsTopEquiv` (through
  `Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal`), are inverse to each other.
  Both evaluate a family at `⊤`, so this is `Equiv.apply_symm_apply` once the two are seen to be
  the same map.
* `Stacks.NonvanishingSpelling.stalkNonvanishingLocus_unitHomEquiv_unitHomEquivTop`: **the
  identification.** The nonvanishing locus, in the stalk module of [Stacks, Tag 01CB], of the
  section carried by the morphism `𝒪_X ⟶ M` attached to a global section `x : Γ(M, ⊤)` is the
  scheme-level nonvanishing locus of `x`.
* `Stacks.NonvanishingSpelling.forall_exists_opens_mem_stalkNonvanishingLocus_unitHomEquivTop`:
  **the identification in the shape the consumers ask for.** A set contained in the bundled
  nonvanishing open of `x` meets the per-point hypothesis of
  `Stacks.SectionProduct.mono_mulRight_of_associatedPoints` — one open neighbourhood inside the
  nonvanishing locus per point — with the nonvanishing open itself as that neighbourhood.

## Implementation notes

**Nothing here is about invertibility, except where the bundled open is.** The locus
identification holds for any `𝒪_X`-module; only
`forall_exists_opens_mem_stalkNonvanishingLocus_unitHomEquivTop`, which names
`Stacks.NonvanishingOpen.nonvanishingOpen`, needs `Stacks.Ample.IsInvertibleModule`, and that is
because the openness of the locus is where invertibility enters.

**`Stacks.Ample.unitModule X` and `AlgebraicGeometry.Scheme.unitModule X` are the same module.**
Both are `SheafOfModules.unit X.ringCatSheaf`; the first is an `abbrev` and the second a `def`,
so a morphism produced by `AlgebraicGeometry.Scheme.Modules.unitHomEquivTop` is accepted where
one out of `Stacks.Ample.unitModule X` is wanted, by unfolding and not by transport.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.NonvanishingSpelling

variable (X : Scheme.{u}) (M : X.Modules)

/-! ### The two terminal-object section equivalences agree -/

/-- **The repository's two section-against-global-section equivalences are mutually inverse.**
`Stacks.NonvanishingSpelling.sectionsEquiv` is
`Stacks.SectionRingGeometric.sectionsEquivObj` and
`AlgebraicGeometry.Scheme.Modules.sectionsTopEquiv` is the inverse of
`Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal`; both forward maps evaluate a
restriction-compatible family at `⊤`, so the two equivalences are equal and this is
`Equiv.apply_symm_apply`. -/
theorem sectionsEquiv_sectionsTopEquiv (x : Γ(M, ⊤)) :
    sectionsEquiv X M (Scheme.Modules.sectionsTopEquiv M x) = x :=
  (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal M
    (isTerminalTop (α := X.Opens))).apply_symm_apply x

/-! ### The nonvanishing locus of the section a morphism out of `𝒪_X` carries -/

/-- **The identification the induction step of [Stacks, Tag 0F27] was waiting on.** Writing a
global section `x : Γ(M, ⊤)` as a morphism `𝒪_X ⟶ M` and taking the nonvanishing locus of the
section that morphism carries gives back the scheme-level nonvanishing locus of `x`. -/
theorem stalkNonvanishingLocus_unitHomEquiv_unitHomEquivTop (x : Γ(M, ⊤)) :
    Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) M
        (SheafOfModules.unitHomEquiv M (Scheme.Modules.unitHomEquivTop M x))
      = Stacks.Ample.nonvanishingLocus M x := by
  rw [Scheme.Modules.unitHomEquiv_unitHomEquivTop]
  exact (stalkNonvanishingLocus_eq X M _).trans
    (congrArg (Stacks.Ample.nonvanishingLocus M) (sectionsEquiv_sectionsTopEquiv X M x))

/-- **The identification in the shape the monicity consumers ask for.**
`Stacks.SectionProduct.mono_mulRight_of_associatedPoints`, and everything derived from it, asks
for one open neighbourhood inside the nonvanishing locus per point of a set; a producer that
delivers a global section nonvanishing on that set, as a subset of the bundled nonvanishing open,
discharges it with the nonvanishing open itself as the neighbourhood at every point. -/
theorem forall_exists_opens_mem_stalkNonvanishingLocus_unitHomEquivTop
    [Stacks.Ample.IsInvertibleModule X M] (x : Γ(M, ⊤)) {S : Set X}
    (hS : S ⊆ (Stacks.NonvanishingOpen.nonvanishingOpen X M x : Set X)) :
    ∀ p ∈ S, ∃ W : X.Opens, p ∈ W ∧ ∀ y ∈ W,
      y ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) M
        (SheafOfModules.unitHomEquiv M (Scheme.Modules.unitHomEquivTop M x)) := by
  intro p hp
  refine ⟨Stacks.NonvanishingOpen.nonvanishingOpen X M x, hS hp, fun y hy => ?_⟩
  rw [stalkNonvanishingLocus_unitHomEquiv_unitHomEquivTop]
  exact hy

end Stacks.NonvanishingSpelling

end
