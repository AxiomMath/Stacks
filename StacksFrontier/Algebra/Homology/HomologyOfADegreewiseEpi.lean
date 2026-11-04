module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# The cohomology of a morphism of complexes which is only surjective in one degree

Let `φ : K ⟶ L` be a morphism of homological complexes in an abelian category. This file gives
the statements on cocycles and cohomology in degree `i` that hold when `φ` is an epimorphism,
rather than an isomorphism, in some of the degrees `c.prev i`, `i` and `c.next i`.

## Main results

* `HomologicalComplex.epi_cyclesMap_of_epi_f`: the map `K.cycles i ⟶ L.cycles i` is an
  epimorphism when `φ` is an epimorphism in degree `i` and a monomorphism in degree `c.next i`.
* `HomologicalComplex.epi_homologyMap_of_epi_f`: under the same hypotheses, so is the map on
  cohomology in degree `i`.
* `HomologicalComplex.isIso_homologyMap_of_epi_f`: the map on cohomology in degree `i` is an
  isomorphism when `φ` is an epimorphism in degree `c.prev i`, an isomorphism in degree `i` and a
  monomorphism in degree `c.next i`.

## Implementation notes

The hypotheses are explicit arguments rather than instances: they are indexed by `c.prev i` and
`c.next i`, which no instance for a morphism indexed by `i - 1` or `i + 1` will match.
-/

@[expose] public noncomputable section

open CategoryTheory Category CategoryTheory.Limits

namespace HomologicalComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex C c}

/-- **The comparison of cocycles is surjective where the morphism is.** If `φ : K ⟶ L` is an
epimorphism in degree `i` and a monomorphism in degree `c.next i`, then the induced map
`K.cycles i ⟶ L.cycles i` is an epimorphism. -/
theorem epi_cyclesMap_of_epi_f (φ : K ⟶ L) (i : ι)
    (h₂ : Epi (φ.f i)) (h₃ : Mono (φ.f (c.next i))) :
    Epi (cyclesMap φ i) := by
  have := h₂
  have := h₃
  have hfst : pullback.fst (φ.f i) (L.iCycles i) ≫ K.d i (c.next i) = 0 := by
    rw [← cancel_mono (φ.f (c.next i)), Category.assoc, zero_comp, ← φ.comm i (c.next i),
      ← Category.assoc, pullback.condition, Category.assoc, L.iCycles_d, comp_zero]
  set h : pullback (φ.f i) (L.iCycles i) ⟶ K.cycles i :=
    K.liftCycles (pullback.fst (φ.f i) (L.iCycles i)) (c.next i) rfl hfst with hh
  have key : h ≫ cyclesMap φ i = pullback.snd (φ.f i) (L.iCycles i) := by
    rw [← cancel_mono (L.iCycles i), Category.assoc, cyclesMap_i, hh, ← Category.assoc,
      liftCycles_i, pullback.condition]
  have : Epi (h ≫ cyclesMap φ i) := by
    rw [key]
    exact Abelian.epi_pullback_of_epi_f _ _
  exact epi_of_epi h (cyclesMap φ i)

/-- **The cohomology of a morphism which is surjective in one degree is surjective there.** The
degree-`i` cohomology of a morphism of homological complexes is an epimorphism as soon as the
morphism is an epimorphism in degree `i` and a monomorphism in degree `c.next i`; the degree
`c.prev i` plays no part. -/
theorem epi_homologyMap_of_epi_f (φ : K ⟶ L) (i : ι)
    (h₂ : Epi (φ.f i)) (h₃ : Mono (φ.f (c.next i))) :
    Epi (homologyMap φ i) :=
  ShortComplex.epi_homologyMap_of_epi_cyclesMap' ((shortComplexFunctor C c i).map φ)
    (epi_cyclesMap_of_epi_f φ i h₂ h₃)

/-- **Cohomology of a morphism which is invertible in one degree and only surjective in the
previous one.** The degree-`i` cohomology of a morphism of homological complexes is an
isomorphism as soon as the morphism is an epimorphism in degree `c.prev i`, an isomorphism in
degree `i` and a monomorphism in degree `c.next i`. -/
theorem isIso_homologyMap_of_epi_f (φ : K ⟶ L) (i : ι)
    (h₁ : Epi (φ.f (c.prev i))) (h₂ : IsIso (φ.f i)) (h₃ : Mono (φ.f (c.next i))) :
    IsIso (homologyMap φ i) := by
  have : IsIso ((shortComplexFunctor C c i).map φ).τ₂ := h₂
  have : Mono ((shortComplexFunctor C c i).map φ).τ₃ := h₃
  exact ShortComplex.isIso_homologyMap_of_isIso_cyclesMap_of_epi
    (φ := (shortComplexFunctor C c i).map φ)
    (ShortComplex.isIso_cyclesMap_of_isIso_of_mono _) h₁

end HomologicalComplex

end
