module

public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The homology functor on homological complexes is linear

Let `C` be an `R`-linear category with homology. Then `HomologicalComplex.homologyFunctor C c n`
is `R`-linear.

## Main definitions

* `HomologicalComplex.homologyFunctor_linear`: the homology functor in degree `n` is `R`-linear.

## Main results

* `HomologicalComplex.homologyMap_smul_id_of_linear`: in an `R`-linear category, multiplication by
  a scalar on a complex induces multiplication by that scalar on its homology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {R : Type*} [Semiring R] {C : Type*} [Category* C] [Preadditive C]
  [CategoryTheory.Linear R C] {ι : Type*} (c : ComplexShape ι)

/-- **Homology in a fixed degree is `R`-linear.** -/
public instance homologyFunctor_linear [CategoryWithHomology C] (n : ι) :
    Functor.Linear R (homologyFunctor C c n) where
  map_smul f r := ShortComplex.homologyMap_smul ((shortComplexFunctor C c n).map f) r

/-- Multiplication by a scalar `r` on a complex `K` induces multiplication by `r` on the homology
of `K`. -/
public lemma homologyMap_smul_id_of_linear {c : ComplexShape ι} (K : HomologicalComplex C c)
    (n : ι) [K.HasHomology n] (r : R) : homologyMap (r • 𝟙 K) n = r • 𝟙 (K.homology n) := by
  change ShortComplex.homologyMap ((shortComplexFunctor C c n).map (r • 𝟙 K)) = _
  rw [show (shortComplexFunctor C c n).map (r • 𝟙 K) =
      r • (shortComplexFunctor C c n).map (𝟙 K) from rfl, ShortComplex.homologyMap_smul,
    CategoryTheory.Functor.map_id, ShortComplex.homologyMap_id]
  rfl

end HomologicalComplex

end
