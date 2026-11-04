module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.AbutmentIsCohomology

/-!
# The Čech-to-cohomology spectral sequence of Stacks 01ES, assembled

For an open covering `𝒰` of an open subset of a ringed space, [Stacks, Tag 01ES] asserts that
there is a spectral sequence, functorial in the sheaf of `O`-modules, whose second page is the
Čech cohomology of the cohomology presheaves and which converges to the cohomology of the covered
open.  `CechSpectralSequenceData` bundles that assertion -- the functorial spectral sequence, its
second-page comparison, and its functorial filtered abutment -- and `cechSpectralSequence` supplies
it.

All four fields are proved, in three files:

* `enoughInjectives` is `SheafOfModules.enoughInjectives_opens`
  (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GrothendieckAbelian.lean`), which needs no
  hypothesis on the ringed space -- existence of enough injectives is part of the conclusion here,
  not an assumption;
* `sequence` is `Stacks.Cohomology.CechSpectral.cechSpectralSequenceFunctor` and `pageTwoIso` is
  `Stacks.Cohomology.CechSpectral.cechPageTwoIso`, both from the construction of the sequence and
  its second page;
* `abutment` is `Stacks.Cohomology.CechSpectral.cechAbutment`, the functorial filtered abutment
  `Stacks.Cohomology.CechSpectral.cechFunctorialAbutment` with its abutment transported onto the
  derived evaluation functor by the convergence identification of [Stacks, Tag 0133].

## Main definitions

* `Stacks.Cohomology.CechSpectral.CechSpectralSequenceData`: the data [Stacks, Tag 01ES] asserts.
* `Stacks.Cohomology.CechSpectral.cechSpectralSequence`: that data, for an open covering.

## Implementation notes

The cohomology presheaf is represented by the right derived functors of the inclusion from sheaves
to presheaves of modules, as in [Stacks, Tag 01ER], so the second page is stated directly with the
Čech cohomology functor of [Stacks, Tag 01EN]; cohomology on the covered open is the derived
evaluation functor.  The space, structure rings, coefficient modules and cover index have
independent universes, the module universe being enlarged to `max u r v w` to accommodate the cover
products and the injective resolutions.

The three instance hypotheses that `Stacks.Cohomology.CechSpectral.cechSpectralSequenceFunctor`
and its successors carry -- `HasSheafify`, `GrothendieckTopology.WEqualsLocallyBijective` and
`EnoughInjectives` at `max u r v w` -- are discharged unconditionally here by
`SheafOfModules.hasSheafify_opens`, `SheafOfModules.wEqualsLocallyBijective_opens` and
`SheafOfModules.enoughInjectives_opens`.  Each is applied with its universe arguments written out
in universe-command order: the module universe is unavoidably a `max`, so `inferInstance` sticks on
`max u r ?t =?= max u r v w` and the instances have to be named.

`Abelian (SheafOfModules.{max u r v w} O)` is not assumed either: `moduleSheavesAbelian` derives it
from essential smallness of the site of opens, which `EssentiallySmall.{max u r v w} (Opens X)`
supplies.  It has to be stated at a single universe variable rather than at `max u r v w`; see its
docstring.

## References

* [Stacks Project, Tag 01ES](https://stacks.math.columbia.edu/tag/01ES)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 01EN](https://stacks.math.columbia.edu/tag/01EN)
* [Stacks Project, Tag 01ER](https://stacks.math.columbia.edu/tag/01ER)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u r v w m

namespace Stacks.Cohomology.CechSpectral

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{r})
  (𝒰 : CechExactFunctor.CechOpenCover.{u, w} (TopCat.of X))

/-- Sheaves of modules on a space form an abelian category, in any coefficient universe in which
the site of opens is essentially small.

The statement uses a single universe variable `m`: an instance whose statement contains a `max`
does not apply at the universe `max u r v w`, since instance search sticks on
`max (max (max r u) ?v) ?w =?= max (max (max r u) v) w`. Kept `local`: it is baked into the field
types of the structure below, and nothing downstream should pick it up as a global instance
keyed on `SheafOfModules`. -/
local instance moduleSheavesAbelian [EssentiallySmall.{m} (Opens X)] :
    Abelian (SheafOfModules.{m} O) := by
  letI : HasSheafify
      ((equivSmallModel.{m} (Opens X)).inverse.inducedTopology
        (Opens.grothendieckTopology X)) AddCommGrpCat.{m} := inferInstance
  letI : ((equivSmallModel.{m} (Opens X)).inverse.inducedTopology
      (Opens.grothendieckTopology X)).WEqualsLocallyBijective AddCommGrpCat.{m} := inferInstance
  letI : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{m} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, m} _ _
  letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{m} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, m} _
  infer_instance

/-- **The complete functorial Čech-to-cohomology spectral sequence for sheaves of modules on a
ringed space**, which is the assertion of [Stacks, Tag 01ES]. -/
structure CechSpectralSequenceData where
  /-- Injective resolutions exist in the enlarged coefficient universe. -/
  [enoughInjectives : EnoughInjectives (SheafOfModules.{max u r v w} O)]
  /-- The spectral sequence is functorial in the coefficient sheaf. -/
  sequence : SheafOfModules.{max u r v w} O ⥤
    E₂CohomologicalSpectralSequenceNat
      (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))
  /-- Its second page is Čech cohomology of the cohomology presheaf. -/
  pageTwoIso (p q : ℕ) :
    sequence ⋙ SpectralSequence.pageFunctor _ _ 2 2 ⋙
        HomologicalComplex.eval _ _ (p, q) ≅
      (SheafOfModules.forget.{max u r v w} O).rightDerived q ⋙
        cechCohomologyFunctor.{u, r, v, w} O 𝒰 p
  /-- The functorial finite filtered abutment is sheaf cohomology on the covered open. -/
  abutment : Leray.FunctorialFirstQuadrantAbutsTo sequence
    (fun n ↦ (SheafOfModules.evaluation.{max u r v w} O
      (op 𝒰.U)).rightDerived n)

/-- **The functorial Čech spectral sequence of an open covering**, with second page
`Ȟ^p(𝒰, H^q(ℱ))` and abutment `H^{p+q}(U, ℱ)`.

This is [Stacks, Tag 01ES]: the four fields are `SheafOfModules.enoughInjectives_opens`,
`cechSpectralSequenceFunctor`, `cechPageTwoIso` and `cechAbutment`. -/
@[stacks 01ES, sga "4 V 3.2" "ringed space, open cover"]
def cechSpectralSequence : CechSpectralSequenceData.{u, r, v, w} O 𝒰 :=
  letI : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u r v w} :=
    SheafOfModules.hasSheafify_opens.{max r v w, u} X
  letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective
      AddCommGrpCat.{max u r v w} :=
    SheafOfModules.wEqualsLocallyBijective_opens.{max r v w, u} X
  letI : EnoughInjectives (SheafOfModules.{max u r v w} O) :=
    SheafOfModules.enoughInjectives_opens.{max v w, u, r} X O
  { enoughInjectives := SheafOfModules.enoughInjectives_opens.{max v w, u, r} X O
    sequence := cechSpectralSequenceFunctor.{u, r, v, w} O 𝒰
    pageTwoIso p q := cechPageTwoIso.{u, r, v, w} O 𝒰 p q
    abutment := cechAbutment.{u, r, v, w} O 𝒰 }

end Stacks.Cohomology.CechSpectral

end
