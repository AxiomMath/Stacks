module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFreeFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomFilteredColimitSections
public import StacksFrontier.Topology.Sheaves.Limits.SpectralCovers

/-!
# Hom out of a finite locally free module on a qcqs scheme and filtered colimits

Let `X` be a quasi-compact quasi-separated scheme and let `E` be a finite locally free
`𝒪_X`-module. Then `Hom_{𝒪_X}(E, -)` commutes with filtered colimits of `𝒪_X`-modules:

`colim_λ Hom_{𝒪_X}(E, G_λ) = Hom_{𝒪_X}(E, colim_λ G_λ)`.

This is [Stacks, Tag 01BS] specialised to a qcqs scheme and to a finite locally free module. The
two inputs are that a finite locally free module is of finite presentation, and that the
underlying space of a quasi-compact quasi-separated scheme has a cofinal system of finite open
coverings with quasi-compact pairwise intersections.

## Main results

* `Stacks.FiniteLocallyFree.hasFiniteCompactCofinalCovers_top_of_compactSpace`: the underlying
  space of a quasi-compact quasi-separated scheme satisfies hypothesis (3) of [Stacks, Tag 009F]
  at `⊤`.
* `Stacks.FiniteLocallyFree.preservesFilteredColimits_coyoneda_of_isFiniteLocallyFree`:
  **`Hom_{𝒪_X}(E, -)` commutes with filtered colimits** for `E` a finite locally free module on a
  quasi-compact quasi-separated scheme.

## Implementation notes

The hypothesis on the space is `DirectedColimitOfSheaves.HasFiniteCompactCofinalCovers ⊤`, which
`hasFiniteCompactCofinalCovers_of_isCompact` supplies for a quasi-compact open of a prespectral
quasi-separated space. A scheme is prespectral because the affine opens form a basis and are
quasi-compact; quasi-separatedness is the hypothesis, and quasi-compactness of `⊤` is
`CompactSpace.isCompact_univ`. No Noetherian hypothesis, no affineness and no finite
presentation hypothesis is used: finite presentation is *derived* from finite local freeness by
`Stacks.SheafOfModules.isFinitePresentation_of_isFiniteLocallyFree`.

The sheaf of rings over which the general statement is phrased is
`Stacks.SheafOfModules.structureSheaf X.sheaf`, which is by definition
`AlgebraicGeometry.Scheme.ringCatSheaf X`: both are `X.sheaf` composed with the forgetful functor
`CommRingCat ⥤ RingCat` along `Opens.grothendieckTopology`. So `X.Modules`, which is
`SheafOfModules.{u} X.ringCatSheaf`, is the category the general statement speaks about and no
transport is needed.

## References

* [Stacks Project, Tag 01BS](https://stacks.math.columbia.edu/tag/01BS)
* [Stacks Project, Tag 009F](https://stacks.math.columbia.edu/tag/009F)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.FiniteLocallyFree

/-- **The underlying space of a quasi-compact quasi-separated scheme has a cofinal system of
finite open coverings with quasi-compact pairwise intersections.** This is hypothesis (3) of
[Stacks, Tag 009F] at the open `⊤`: a scheme is prespectral, since its affine opens form a basis
and are quasi-compact, and `⊤` is quasi-compact because `X` is. -/
theorem hasFiniteCompactCofinalCovers_top_of_compactSpace (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] :
    DirectedColimitOfSheaves.HasFiniteCompactCofinalCovers (X := (X : TopCat.{u})) ⊤ :=
  hasFiniteCompactCofinalCovers_of_isCompact ⊤ CompactSpace.isCompact_univ

/-- **Morphisms out of a finite locally free module on a quasi-compact quasi-separated scheme
commute with filtered colimits**, i.e.

`colim_λ Hom_{𝒪_X}(E, G_λ) = Hom_{𝒪_X}(E, colim_λ G_λ)`

for `E` a finite locally free `𝒪_X`-module and `λ ↦ G_λ` a filtered system of `𝒪_X`-modules.
This is [Stacks, Tag 01BS] for such an `E`: the module is of finite presentation by
[Stacks, Tag 05P2], and the qcqs scheme `X` satisfies the hypothesis of [Stacks, Tag 009F] (4) on
its open coverings. -/
theorem preservesFilteredColimits_coyoneda_of_isFiniteLocallyFree (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    (K : Type u) [Category.{u} K] [IsFiltered K] :
    PreservesColimitsOfShape K (coyoneda.obj (op E)) :=
  have : (E : _root_.SheafOfModules.{u} X.ringCatSheaf).IsFinitePresentation :=
    Stacks.SheafOfModules.isFinitePresentation_of_isFiniteLocallyFree E
  Stacks.SheafOfModules.preservesColimitsOfShape_coyoneda_of_isFinitePresentation X.sheaf E K
    (hasFiniteCompactCofinalCovers_top_of_compactSpace X)

end Stacks.FiniteLocallyFree

end
