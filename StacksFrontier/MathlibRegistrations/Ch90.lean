module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.RingTheory.Kaehler.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks tags of chapter 90 (Formal Deformation Theory) covered by Mathlib

Each tag registered here is stated in Mathlib; this file only records the correspondence.

An `R`-linear functor in the sense of Stacks is a functor that is both additive and
`R`-homogeneous on morphisms; Mathlib splits this into `Functor.Additive` and `Functor.Linear`.
-/

add_to_stacks 06I3 "additivity on Hom_R(M, N)" CategoryTheory.Functor.Additive
add_to_stacks 06I3 "R-homogeneity: L(r • f) = r • L(f)" CategoryTheory.Functor.Linear
add_to_stacks 06I3 "L on Hom_R(M, N) as a map of R-modules" CategoryTheory.Functor.mapLinearMap

add_to_stacks 06S6 "the map m_A/m_A² → k ⊗_A Ω_{A/Λ}" KaehlerDifferential.kerCotangentToTensor
add_to_stacks 06S6 "the map k ⊗_A Ω_{A/Λ} → Ω_{k/Λ}" KaehlerDifferential.mapBaseChange
add_to_stacks 06S6 "exactness at k ⊗_A Ω_{A/Λ}"
  KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange
add_to_stacks 06S6 "exactness at Ω_{k/Λ} (→ 0)" KaehlerDifferential.mapBaseChange_surjective
