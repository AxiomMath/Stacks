module

public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat

/-!
# The chosen projective resolution is K-flat

`StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex M` is the chosen projective resolution of
a module `M`, read as a cochain complex in nonpositive degrees. It is termwise projective and
concentrated in degrees `≤ 0`, so it is termwise flat and K-flat.

## Main results

* `projResComplex_isStrictlyLE`: the complex is concentrated in degrees `≤ 0`.
* `projResComplex_projective`: each term is projective.
* `projResComplex_flat`: each term is flat.
* `projResComplex_kFlat`: the complex is K-flat.

## Implementation notes

These four facts were restated privately in six modules of the tree, three of them proving only
the K-flatness and two the conjunction of K-flatness with termwise flatness; they live here so
that both forms are assembled from one proof. The only import is
`StacksFrontier.Homology.TorAmplitude.Comparison`, which supplies both
`StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex` and
`kFlat_of_isStrictlyLE_projective`, and which every one of those six modules already has in its
import closure.
-/

@[expose] public section

open CategoryTheory StacksDraft.TorAmplitude

universe u

namespace StacksDraft.TorAmplitude.FaithfullyFlat

variable {R : Type u} [CommRing R]

/-- The chosen projective resolution, read as a cochain complex, is concentrated in degrees
`≤ 0`. -/
public lemma projResComplex_isStrictlyLE (M : ModuleCat.{u} R) :
    (projResComplex M).IsStrictlyLE 0 := by
  change CochainComplex.IsStrictlyLE
    ((CategoryTheory.ProjectiveResolution.of M).complex.extend
      ComplexShape.embeddingDownNat) 0
  infer_instance

/-- Every term of the chosen projective resolution is projective. -/
public lemma projResComplex_projective (M : ModuleCat.{u} R) (i : ℤ) :
    Projective ((projResComplex M).X i) := by
  change Projective
    (((CategoryTheory.ProjectiveResolution.of M).complex.extend
      ComplexShape.embeddingDownNat).X i)
  infer_instance

/-- Every term of the chosen projective resolution is flat, being projective. -/
public lemma projResComplex_flat (M : ModuleCat.{u} R) (i : ℤ) :
    Module.Flat R ((projResComplex M).X i) := by
  have := projResComplex_projective M i
  infer_instance

/-- **The chosen projective resolution of a module is K-flat.** It is a complex of projective,
hence flat, modules concentrated in nonpositive degrees, and such a complex is K-flat. -/
public lemma projResComplex_kFlat (M : ModuleCat.{u} R) :
    (projResComplex M).KFlat := by
  have := projResComplex_isStrictlyLE M
  exact kFlat_of_isStrictlyLE_projective _ 0 (projResComplex_projective M)

end StacksDraft.TorAmplitude.FaithfullyFlat

end
