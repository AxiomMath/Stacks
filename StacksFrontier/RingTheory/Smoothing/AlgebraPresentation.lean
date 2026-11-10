module

public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import StacksFrontier.RingTheory.Smoothing.BaseChangeOfPresentation

/-!
# From a presentation to Mathlib's `Algebra.Presentation`

The presentations of Stacks 16.2 are recorded by the structure `Presentation` of
`StacksFrontier.RingTheory.Smoothing.BaseChangeOfPresentation`: two integers `n, m`, a family
of relations
`f : Fin m → R[x_1, …, x_n]` and an isomorphism `A ≃ₐ[R] R[x]/(f_1, …, f_m)`.
Mathlib's `Algebra.Presentation` records the same data differently, as a surjection
from a polynomial ring whose kernel is spanned by the relations, and it is the form
that carries the cotangent complex machinery. This file converts the former into the
latter and records the dictionary between the two: what the surjection does to a
polynomial, what the coordinates of the class of a relation in the cotangent space
are, and that the classes of the relations generate the cotangent module.

## Main definitions

* `Stacks.Smoothing.toAlgebraPresentation`: the `Algebra.Presentation` attached to a
  `Presentation`.

## Main results

* `Stacks.Smoothing.aeval_toAlgebraPresentation`: the surjection of
  `toAlgebraPresentation P` is `Presentation.lift`.
* `Stacks.Smoothing.ker_toAlgebraPresentation`: its kernel is the ideal of relations.
* `Stacks.Smoothing.relation_coordinates`: the coordinates, in the basis of the
  cotangent space given by the variables, of the class of the `j`-th relation are the
  elements of `A` represented by the partial derivatives of that relation.
* `Stacks.Smoothing.relation_classes_surjective`: the classes of the relations span
  the cotangent module.

## Implementation notes

The underlying ring of the extension attached to a set of generators is the
polynomial ring itself, but only up to unfolding the definition of
`Algebra.Generators.toExtension`; the `RingEquiv`
`Stacks.Smoothing.generatorsToExtensionRingEquiv` is the identity presented as an
isomorphism, and exists so that memberships and ideals can be transported across that
identification without relying on definitional unfolding.

## References

* [Stacks Project, Tag 07C7](https://stacks.math.columbia.edu/tag/07C7)
-/

@[expose] public section

namespace Stacks.Smoothing

universe u v

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]

/-- Mathlib's presentation attached to a `Presentation`: the same polynomial ring,
the same relations, and the surjection `Presentation.lift`. -/
noncomputable def toAlgebraPresentation (P : Presentation R A) :
    Algebra.Presentation R A (Fin P.n) (Fin P.m) := by
  let φ : MvPolynomial (Fin P.n) R →ₐ[R] A :=
    P.iso.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R P.relIdeal)
  have hsurj : Function.Surjective φ :=
    P.iso.symm.surjective.comp (Ideal.Quotient.mkₐ_surjective R P.relIdeal)
  refine
    { toGenerators := Algebra.Generators.ofAlgHom φ hsurj
      relation := P.f
      span_range_relation_eq_ker := ?_ }
  rw [Algebra.Generators.ker_ofAlgHom]
  change P.relIdeal = RingHom.ker φ.toRingHom
  ext p
  change p ∈ P.relIdeal ↔ φ p = 0
  constructor
  · intro hp
    change P.iso.symm (Ideal.Quotient.mkₐ R P.relIdeal p) = 0
    rw [← map_zero P.iso.symm]
    exact congrArg P.iso.symm (Ideal.Quotient.eq_zero_iff_mem.mpr hp)
  · intro hp
    change P.iso.symm (Ideal.Quotient.mkₐ R P.relIdeal p) = 0 at hp
    rw [← map_zero P.iso.symm] at hp
    exact Ideal.Quotient.eq_zero_iff_mem.mp (P.iso.symm.injective hp)

/-- The surjection of `toAlgebraPresentation P` sends a polynomial to the element of
`A` it represents. -/
theorem aeval_toAlgebraPresentation (P : Presentation R A)
    (p : MvPolynomial (Fin P.n) R) :
    MvPolynomial.aeval (toAlgebraPresentation P).toGenerators.val p = P.lift p := by
  have hh : MvPolynomial.aeval (toAlgebraPresentation P).toGenerators.val =
      P.iso.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R P.relIdeal) := by
    ext i
    simp [toAlgebraPresentation, Algebra.Generators.ofAlgHom,
      Algebra.Generators.ofSurjective]
  rw [hh]
  rfl

/-- The kernel of the surjection of `toAlgebraPresentation P` is the ideal of
relations of `P`. -/
theorem ker_toAlgebraPresentation (P : Presentation R A) :
    (toAlgebraPresentation P).toGenerators.ker = P.relIdeal := by
  rw [← (toAlgebraPresentation P).span_range_relation_eq_ker]
  rfl

/-- The coordinates of the class of the `j`-th relation in the cotangent space, in
the basis given by the variables, are the elements of `A` represented by the partial
derivatives of that relation. -/
theorem relation_coordinates (P : Presentation R A) (j : Fin P.m) :
    (toAlgebraPresentation P).toGenerators.cotangentSpaceBasis.repr
      ((toAlgebraPresentation P).toGenerators.toExtension.cotangentComplex
        (Algebra.Extension.Cotangent.mk ⟨P.f j,
          (toAlgebraPresentation P).relation_mem_ker j⟩)) =
      fun i ↦ P.lift (MvPolynomial.pderiv i (P.f j)) := by
  ext i
  rw [Algebra.Extension.cotangentComplex_mk,
    (toAlgebraPresentation P).toGenerators.cotangentSpaceBasis_repr_one_tmul]
  exact aeval_toAlgebraPresentation P (MvPolynomial.pderiv i (P.f j))

/-- The classes of the relations of a finite presentation span its cotangent module:
every element of the cotangent module is an `A`-linear combination of them. -/
theorem relation_classes_surjective {n m : ℕ}
    (P : Algebra.Presentation R A (Fin n) (Fin m)) :
    Function.Surjective (Fintype.linearCombination A fun j ↦
      Algebra.Extension.Cotangent.mk (P := P.toGenerators.toExtension)
        ⟨P.relation j, P.relation_mem_ker j⟩) := by
  intro x
  obtain ⟨y, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  have hy : (y : P.toExtension.Ring) ∈ Ideal.span (Set.range P.relation) := by
    rw [P.span_range_relation_eq_ker]
    exact y.2
  obtain ⟨d, hd⟩ := Ideal.mem_span_range_iff_exists_fun.mp hy
  refine ⟨fun j ↦ algebraMap P.toExtension.Ring A (d j), ?_⟩
  rw [Fintype.linearCombination_apply]
  have hy' : y = ∑ j, d j •
      (⟨P.relation j, P.relation_mem_ker j⟩ : P.toExtension.ker) := by
    refine Subtype.ext ?_
    rw [Submodule.coe_sum, ← hd]
    exact Finset.sum_congr rfl fun j _ ↦ rfl
  rw [hy', map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smul]
  exact algebraMap_smul A (d j) _

/-- The underlying ring of the extension attached to a set of generators is the
polynomial ring of those generators, presented as a ring isomorphism. -/
noncomputable def generatorsToExtensionRingEquiv {ι : Type*}
    (G : Algebra.Generators R A ι) : G.Ring ≃+* G.toExtension.Ring := by
  have h : G.Ring = G.toExtension.Ring := G.toExtension_Ring.symm
  cases h
  exact RingEquiv.refl _

/-- The ring isomorphism `generatorsToExtensionRingEquiv` commutes with the algebra maps to `A`. -/
theorem generatorsToExtensionRingEquiv_algebraMap {ι : Type*}
    (G : Algebra.Generators R A ι) (p : G.Ring) :
    algebraMap G.toExtension.Ring A (generatorsToExtensionRingEquiv G p) =
      algebraMap G.Ring A p := by
  with_unfolding_all rfl

/-- The ring isomorphism `generatorsToExtensionRingEquiv` is the identity on underlying
elements. -/
theorem generatorsToExtensionRingEquiv_apply {ι : Type*}
    (G : Algebra.Generators R A ι) (p : G.Ring) :
    (generatorsToExtensionRingEquiv G p : G.toExtension.Ring) = p := by
  with_unfolding_all rfl

/-- The ring isomorphism `generatorsToExtensionRingEquiv` carries the kernel of the generators
onto the kernel of the associated extension. -/
theorem generatorsToExtensionRingEquiv_map_ker {ι : Type*}
    (G : Algebra.Generators R A ι) :
    Ideal.map (generatorsToExtensionRingEquiv G) G.ker = G.toExtension.ker := by
  ext y
  rw [Ideal.mem_map_iff_of_surjective _ (generatorsToExtensionRingEquiv G).surjective]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change algebraMap G.Ring A x = 0 at hx
    change algebraMap G.toExtension.Ring A (generatorsToExtensionRingEquiv G x) = 0
    rwa [generatorsToExtensionRingEquiv_algebraMap]
  · intro hy
    change algebraMap G.toExtension.Ring A y = 0 at hy
    refine ⟨(generatorsToExtensionRingEquiv G).symm y, ?_,
      (generatorsToExtensionRingEquiv G).apply_symm_apply y⟩
    change algebraMap G.Ring A ((generatorsToExtensionRingEquiv G).symm y) = 0
    rw [← generatorsToExtensionRingEquiv_algebraMap]
    simpa using hy

end Stacks.Smoothing

end
