module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.ProblemIdealSections

/-!
# The generators of the ideal of the extension problem of a flat deformation

Let `Z ⊂ Y'` be a first order thickening of algebraic spaces and `g : X ⟶ Z`. A global section
`t` of the conormal module gives the section `g⁻¹t` of the ideal of the extension problem of
[Stacks, Tag 0D17] (`AlgebraicGeometry.Space.FlatThickeningDeformation.problemIdealSection`) and
the pulled-back section `g^*t` of its prescribed module. This file records them as global
sections of the fields of the problem itself
(`AlgebraicGeometry.Space.FlatThickeningDeformation.problemIdealGenerator`,
`AlgebraicGeometry.Space.FlatThickeningDeformation.problemConormalGenerator`), over the rings
through which the problem reads them, and restates that the prescribed map carries the first to
the second in that form.

## References

* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.SheafOfModules.ChangeOfRings (unitToRestrictScalarsUnit)

universe u

namespace AlgebraicGeometry.Space.FlatThickeningDeformation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  (hZ : IsFirstOrderThickening B S hS Y' Z.1) {X : AlgebraicSpaces B S hS}
  (g : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
  (t : SheafOfModules.unit (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ :
    AlgebraicSpaces B S hS)) ⟶ conormalModule B S hS Y' Z)

/-- **The section `g⁻¹t` of the ideal of the problem**, as a global section of the field `I` of
`problem g hZ`, over the ring `g⁻¹𝒪_Z` through which the problem reads it. -/
def problemIdealGenerator :
    SheafOfModules.unit ((sheafCompose (smallEtaleRingedTopos B S hS X).J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((inverseImageCommRingFunctor (problem g hZ).f.toToposHom).obj
          (smallEtaleRingedTopos B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).O)) ⟶
      (problem g hZ).I :=
  problemIdealSection hZ g t

/-- **The pulled-back section `g^*t`**, as a global section of the field `G` of `problem g hZ`. -/
def problemConormalGenerator :
    SheafOfModules.unit ((sheafCompose (smallEtaleRingedTopos B S hS X).J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O) ⟶
      (problem g hZ).G :=
  modulePullbackGlobalSection B S hS g t

/-- **The prescribed map of the problem carries `g⁻¹t` to `g^*t`**
(`AlgebraicGeometry.Space.FlatThickeningDeformation.problemIdealSection_comp_problem_c`, in terms
of the fields of the problem). -/
theorem problemIdealGenerator_comp_c :
    problemIdealGenerator hZ g t ≫ (problem g hZ).c =
      unitToRestrictScalarsUnit ((sheafCompose (smallEtaleRingedTopos B S hS X).J
          (forget₂ CommRingCat.{u} RingCat.{u})).map (problem g hZ).f.fSharpInverseImage) ≫
        (SheafOfModules.restrictScalars ((sheafCompose (smallEtaleRingedTopos B S hS X).J
          (forget₂ CommRingCat.{u} RingCat.{u})).map (problem g hZ).f.fSharpInverseImage)).map
          (problemConormalGenerator hZ g t) :=
  problemIdealSection_comp_problem_c hZ g t

end AlgebraicGeometry.Space.FlatThickeningDeformation
