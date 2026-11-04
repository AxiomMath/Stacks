module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.DirectedColimit
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars

/-!
# The derived base change of the cotangent complex

Let `A → B → C` be ring maps. The cotangent complex `L_{B/A}` is a complex of free `B`-modules
vanishing in positive degrees, so it is its own K-flat model: the derived base change
`L_{B/A} ⊗^𝐋_B C` is computed by the degreewise extension of scalars `C ⊗_B L_{B/A}`.

## Main results

* `CommAlgCat.free_cotangentComplex_X` and `CommAlgCat.projective_cotangentComplex_X'`: every
  term of the cotangent complex is a free, hence projective, `B`-module.
* `CommAlgCat.cotangentComplex_isStrictlyLE_zero'`: the cotangent complex is concentrated in
  nonpositive degrees, at two universes.
* `CommAlgCat.nonempty_derivedExtensionScalars_cotangentComplex_iso`: the derived base change
  of `L_{B/A}` along `B → C` is the degreewise extension of scalars of `L_{B/A}`.

## Implementation notes

Freeness of the degree `-n` term is `CommAlgCat.cotangentComplexBasis`, whose basis is indexed
by the variables of the `n`th polynomial algebra of the standard resolution. Projectivity of the
remaining terms is projectivity of a zero object, by `CommAlgCat.cotangentComplex_isZero_pos`.
These two facts are exactly the hypotheses of the `comparison_isIso_of_projective` field of
`CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars`, so the comparison map of
the derived functor is invertible at the cotangent complex and no K-flat resolution has to be
chosen.

## References

* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v wB wC

namespace CommAlgCat

/-- The term of the cotangent complex in cohomological degree `-n` is a free `B`-module, on the
variables of the `n`th polynomial algebra of the standard resolution. -/
theorem free_cotangentComplex_X (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A) (n : ℕ) :
    Module.Free B ((cotangentComplex.{u, v} A B).X (-(n : ℤ))) :=
  Module.Free.of_basis (cotangentComplexBasis.{u, v} A B n)

/-- Every term of the cotangent complex is a projective `B`-module: in a nonpositive degree it is
free, and in a positive degree it is zero. Stated for an algebra whose carrier may live in a
larger universe than the base ring; the case of a single universe is
`CommAlgCat.projective_cotangentComplex_X`. -/
theorem projective_cotangentComplex_X' (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)
    (i : ℤ) : Projective ((cotangentComplex.{u, v} A B).X i) := by
  by_cases hi : 0 < i
  · exact (cotangentComplex_isZero_pos.{u, v} A B i hi).projective
  · rw [show i = -(((-i).toNat : ℕ) : ℤ) by omega]
    exact ModuleCat.projective_of_free (cotangentComplexBasis.{u, v} A B ((-i).toNat))

/-- The cotangent complex vanishes in positive cohomological degrees, for an algebra whose
carrier may live in a larger universe than the base ring. The case of a single universe is
`CommAlgCat.cotangentComplex_isStrictlyLE_zero`. -/
instance cotangentComplex_isStrictlyLE_zero' (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) : (cotangentComplex.{u, v} A B).IsStrictlyLE 0 :=
  (CochainComplex.isStrictlyLE_iff _ 0).2 fun i hi =>
    cotangentComplex_isZero_pos.{u, v} A B i hi

/-- **The derived base change of the cotangent complex is computed degreewise.**

For ring maps `A → B → C`, the derived base change `L_{B/A} ⊗^𝐋_B C` is the image in `D(C)` of
the degreewise extension of scalars `C ⊗_B L_{B/A}`, because `L_{B/A}` is a complex of free
`B`-modules vanishing in positive degrees. -/
theorem nonempty_derivedExtensionScalars_cotangentComplex_iso (A : Type u) [CommRing A]
    (B : Type (max u v)) [CommRing B] [Algebra A B] (C : Type (max u v)) [CommRing C]
    [Algebra B C]
    [HasDerivedCategory.{wB} (ModuleCat.{max u v} B)]
    [HasDerivedCategory.{wC} (ModuleCat.{max u v} C)] :
    Nonempty
      ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
            (algebraMap B C)).functor.obj
          (DerivedCategory.Q.obj (cotangentComplex.{u, v} A (CommAlgCat.of A B))) ≅
        (CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral
            (algebraMap B C)).obj (cotangentComplex.{u, v} A (CommAlgCat.of A B))) := by
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
    (R := B) (A := C) (algebraMap B C)
  have : ∀ i : ℤ, Projective ((cotangentComplex.{u, v} A (CommAlgCat.of A B)).X i) :=
    projective_cotangentComplex_X'.{u, v} A (CommAlgCat.of A B)
  have : (cotangentComplex.{u, v} A (CommAlgCat.of A B)).IsStrictlyLE 0 :=
    cotangentComplex_isStrictlyLE_zero'.{u, v} A (CommAlgCat.of A B)
  exact ⟨@asIso _ _ _ _ _ (D.comparison_isIso_of_projective _ 0)⟩

end CommAlgCat

end
