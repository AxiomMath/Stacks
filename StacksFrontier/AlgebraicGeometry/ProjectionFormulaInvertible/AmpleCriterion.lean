module

public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaMap.AmpleCriterion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 0B5P

[Stacks, Tag 0B5P] says that on a quasi-compact scheme `X` an invertible `𝒪_X`-module `L` is
ample as soon as, for every quasi-coherent sheaf of ideals `I ⊆ 𝒪_X`, some `n ≥ 1` makes
`H¹(X, I ⊗ L^{⊗ n})` vanish.

The projection formula morphism of [Stacks, Tag 0FZE] at the structure sheaf is an isomorphism
when its second argument is invertible, so global sections take it to an epimorphism; this
proves `Stacks.Tag0B5PClopenLift.ProjectionFormulaConsequence X` for every scheme `X`, the one
hypothesis of `Stacks.Tag0B5PClopenLift.isAmple_of_hasEventuallyVanishingH1` beyond those of
the tag.

## Main results

* `Stacks.ProjectionFormula.projectionFormulaConsequence`:
  `Stacks.Tag0B5PClopenLift.ProjectionFormulaConsequence X` for every scheme `X`,
  unconditionally.
* `Stacks.ProjectionFormula.isAmple_of_hasEventuallyVanishingH1`: **[Stacks, Tag 0B5P]**: on a
  quasi-compact scheme, an invertible module with eventually vanishing `H¹` is ample.

## References

* [Stacks Project, Tag 0B5P](https://stacks.math.columbia.edu/tag/0B5P)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/


@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open RingedSpaceModuleAdjunction Stacks.RingedSpace

universe u

namespace Stacks.ProjectionFormula

/-- An invertible module on a scheme in the `Stacks.Ample.IsInvertibleModule` spelling is
invertible in the `Stacks.SheafOfModules.IsInvertible` spelling of its underlying ringed space.
The two classes both realise [Stacks, Tag 01CS]. -/
theorem isInvertible_of_isInvertibleModule (X : Scheme.{u}) (P : X.Modules)
    [h : Stacks.Ample.IsInvertibleModule X P] :
    Stacks.SheafOfModules.IsInvertible X.toRingedSpace.sheaf.obj
      (structureRingSheaf X.toRingedSpace).property P :=
  (@Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _
    X.toRingedSpace.sheaf.obj (structureRingSheaf X.toRingedSpace).property _ _ P).mpr h

/-- **The projection formula at the structure sheaf of a morphism of schemes, for an invertible
module.** For `i : Z ⟶ X` and `P` an invertible `𝒪_X`-module,
`i_* 𝒪_Z ⊗ P ⟶ i_*(𝒪_Z ⊗ i^* P)` is an isomorphism. -/
theorem isIso_projectionFormulaMap_unit {Z X : Scheme.{u}} (i : Z ⟶ X) (P : X.Modules)
    [Stacks.Ample.IsInvertibleModule X P] :
    IsIso (projectionFormulaMap' i.toLRSHom.toShHom
      (SheafOfModules.unit (structureRingSheaf Z.toRingedSpace)) P) :=
  have := isInvertible_of_isInvertibleModule X P
  isIso_projectionFormulaMap i.toLRSHom.toShHom _ P

/-- Global sections take the projection formula morphism at the structure sheaf to an
epimorphism, for an invertible `P`. -/
theorem epi_evaluation_map_projectionFormulaMap {Z X : Scheme.{u}} (i : Z ⟶ X) (P : X.Modules)
    [Stacks.Ample.IsInvertibleModule X P] :
    Epi ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map
      (projectionFormulaMap' i.toLRSHom.toShHom
        (SheafOfModules.unit (structureRingSheaf Z.toRingedSpace)) P)) :=
  have := isInvertible_of_isInvertibleModule X P
  epi_map_projectionFormulaMap i.toLRSHom.toShHom _ P
    (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))

/-- `Stacks.Tag0B5PClopenLift.ProjectionFormulaConsequence X` holds for every scheme `X`, with
no hypothesis. -/
theorem projectionFormulaConsequence (X : Scheme.{u}) :
    Stacks.Tag0B5PClopenLift.ProjectionFormulaConsequence X :=
  projectionFormulaConsequence_of_epi X fun i P => epi_evaluation_map_projectionFormulaMap i P

/-- Let `X` be a quasi-compact scheme and `L` an invertible `𝒪_X`-module. If for every
quasi-coherent sheaf of ideals `I ⊆ 𝒪_X` there is an `n ≥ 1` with `H¹(X, I ⊗ L^{⊗ n}) = 0`, then
`L` is ample.

Here `CompactSpace X` is "`X` is quasi-compact", `Stacks.Ample.IsInvertibleModule X L` is "`L` is
an invertible `𝒪_X`-module", and `Stacks.AmpleCohomologicalCriterion.HasEventuallyVanishingH1 X L`
is the vanishing hypothesis. -/
@[stacks 0B5P, ega "III 2.6.1" "c) => a), absolute"]
theorem isAmple_of_hasEventuallyVanishingH1 (X : Scheme.{u}) [CompactSpace X] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L]
    (h : Stacks.AmpleCohomologicalCriterion.HasEventuallyVanishingH1 X L) :
    Stacks.Ample.IsAmple X L :=
  Stacks.Tag0B5PClopenLift.isAmple_of_hasEventuallyVanishingH1 X L
    (projectionFormulaConsequence X) h

end Stacks.ProjectionFormula

end
