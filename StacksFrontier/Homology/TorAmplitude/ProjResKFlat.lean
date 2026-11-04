module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat

/-!
# The chosen projective resolution is K-flat

`StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex M` is the chosen projective resolution of
a module, read as a cochain complex in nonpositive degrees. It is a bounded-above complex of
projective, hence flat, modules, so it is K-flat.
-/

@[expose] public section

open CategoryTheory

namespace StacksDraft.TorAmplitude.FaithfullyFlat

universe u

/-- The chosen projective resolution of a module, read as a cochain complex in nonpositive
degrees, is K-flat: it is a bounded-above complex of projective, hence flat, modules. -/
theorem projResComplex_kFlat {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    (projResComplex M).KFlat := by
  let P := projResComplex M
  have : P.IsStrictlyLE 0 := by
    show CochainComplex.IsStrictlyLE
      ((ProjectiveResolution.of M).complex.extend ComplexShape.embeddingDownNat) 0
    infer_instance
  have : ∀ i, Module.Flat R (P.X i) := by
    intro i
    show Module.Flat R
      (((ProjectiveResolution.of M).complex.extend ComplexShape.embeddingDownNat).X i)
    have : Projective
        (((ProjectiveResolution.of M).complex.extend ComplexShape.embeddingDownNat).X i) :=
      inferInstance
    infer_instance
  exact (CochainComplex.KFlat.kFlat_of_flat P 0)

/-- Every term of the chosen projective resolution is flat, being projective. -/
theorem projResComplex_flat_X {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (i : ℤ) :
    Module.Flat R ((projResComplex M).X i) := by
  show Module.Flat R
    (((ProjectiveResolution.of M).complex.extend ComplexShape.embeddingDownNat).X i)
  have : Projective
      (((ProjectiveResolution.of M).complex.extend ComplexShape.embeddingDownNat).X i) :=
    inferInstance
  infer_instance

end StacksDraft.TorAmplitude.FaithfullyFlat
