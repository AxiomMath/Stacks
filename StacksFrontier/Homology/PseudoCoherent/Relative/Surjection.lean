module

public import StacksFrontier.Homology.PseudoCoherent.Relative.Composition
public import StacksFrontier.Homology.PseudoCoherent.Relative.Finite
public import StacksFrontier.Homology.PseudoCoherent.Relative.Localization
public import StacksFrontier.RingTheory.PseudoCoherentMap.Flat

/-!
# Relative pseudo-coherence through a surjection from a flat algebra of finite presentation

Let `R → P` be flat and of finite presentation and `P → B` surjective. An object `K` of `D(B)`
whose restriction of scalars to `P` is `m`-pseudo-coherent is `m`-pseudo-coherent relative to
`R`: restriction of scalars along the finite map `P → B` reflects relative pseudo-coherence
(Stacks 0673), `P` is pseudo-coherent over `R` (Stacks 067J), so relative pseudo-coherence over
`P` and over `R` agree (Stacks 067D), and relative to `P` itself it is pseudo-coherence.

## Main results

* `PseudoCoherence.isRelativelyPseudoCoherentFrom_self_iff`
* `PseudoCoherence.isRelativelyPseudoCoherentFrom_of_surjective`
-/

@[expose] public section

open CategoryTheory
open StacksDraft.PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

namespace PseudoCoherence

/-- **Pseudo-coherence relative to the ring itself is pseudo-coherence.** -/
theorem isRelativelyPseudoCoherentFrom_self_iff {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ) :
    IsRelativelyPseudoCoherentFrom (R := A) (A := A) K m ↔ IsPseudoCoherentFrom K m := by
  let e : MvPolynomial (Fin 0) A ≃ₐ[A] A := MvPolynomial.isEmptyAlgEquiv A (Fin 0)
  have hs : Function.Surjective e.toAlgHom := e.surjective
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact (isPseudoCoherentFrom_restrictScalars_ringEquiv e.toRingEquiv K m).2 (h 0 e.toAlgHom hs)
  · exact ((isPseudoCoherentFrom_polynomialPresentation_independent.{u, u, u} K m).1.1
      ⟨0, e.toAlgHom, hs, (isPseudoCoherentFrom_restrictScalars_ringEquiv e.toRingEquiv K m).1 h⟩)

/-- Over a flat algebra of finite presentation, relative and absolute pseudo-coherence agree. -/
private theorem isRelativelyPseudoCoherentFrom_iff_of_flat_aux {R A : Type u} [CommRing R]
    [CommRing A] [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ) :
    IsRelativelyPseudoCoherentFrom (R := R) K m ↔ IsPseudoCoherentFrom K m := by
  have hA := Algebra.pseudoCoherent_iff_isModuleRelativelyPseudoCoherent.mp
    (Algebra.PseudoCoherent.of_flat_of_finitePresentation R A)
  exact (relativelyPseudoCoherent_iff_of_comp (R := R) (A := A) (B := A) hA K m).1.symm.trans
    (isRelativelyPseudoCoherentFrom_self_iff K m)

/-- **Relative pseudo-coherence through a surjection from a flat algebra of finite presentation.**
For `R → P` flat and of finite presentation and `P → B` surjective, an object of `D(B)` whose
restriction of scalars to `P` is `m`-pseudo-coherent is `m`-pseudo-coherent relative to `R`. -/
theorem isRelativelyPseudoCoherentFrom_of_surjective {R P B : Type u} [CommRing R] [CommRing P]
    [CommRing B] [Algebra R P] [Algebra P B] [Algebra R B] [IsScalarTower R P B]
    [Module.Flat R P] [Algebra.FinitePresentation R P]
    (hs : Function.Surjective (algebraMap P B)) (K : DerivedCategory (ModuleCat.{u} B)) (m : ℤ)
    (h : IsPseudoCoherentFrom
      ((ModuleCat.restrictScalars.{u} (algebraMap P B)).mapDerivedCategory.obj K) m) :
    letI : Module.Finite P B := Module.Finite.of_surjective (Algebra.linearMap P B) hs
    letI : Algebra.FiniteType R B :=
      Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R P)
        (Module.Finite.finiteType B)
    IsRelativelyPseudoCoherentFrom (R := R) K m := by
  let : Module.Finite P B := Module.Finite.of_surjective (Algebra.linearMap P B) hs
  have h₁ := (isRelativelyPseudoCoherentFrom_and_isRelativelyPseudoCoherent_iff_restrictScalars
    (R := R) (A := P) K m).1
  exact h₁.2 ((isRelativelyPseudoCoherentFrom_iff_of_flat_aux (R := R) _ m).2 h)

/-- **Relative and absolute pseudo-coherence agree over a flat algebra of finite presentation.**
For `R → A` flat and of finite presentation, an object of `D(A)` is `m`-pseudo-coherent relative
to `R` exactly when it is `m`-pseudo-coherent. -/
theorem isRelativelyPseudoCoherentFrom_iff_of_flat {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ) :
    IsRelativelyPseudoCoherentFrom (R := R) K m ↔ IsPseudoCoherentFrom K m :=
  isRelativelyPseudoCoherentFrom_iff_of_flat_aux K m

end PseudoCoherence
