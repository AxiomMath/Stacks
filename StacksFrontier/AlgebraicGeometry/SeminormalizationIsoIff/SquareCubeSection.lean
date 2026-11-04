module

public import StacksFrontier.AlgebraicGeometry.SeminormalizationIsoIff.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.SquareCubeAlg

/-!
# Seminormality from sections of the square-cube extension

A reduced ring `R` is seminormal as soon as, for every `x, y : R` with `x ^ 3 = y ^ 2`, the
canonical morphism `Spec (R[t]/(t ^ 2 - x, t ^ 3 - y)) ⟶ Spec R` admits a section.  The
section provides the required common square and cube root of `x` and `y`, namely the image of
`t`, and reducedness makes it unique.

## Main results

* `AlgebraicGeometry.isSeminormalRing_of_squareCube_sections` is the criterion.

## Implementation notes

The criterion is the affine-local step of one implication of Stacks Tag 0EUS, where the required
section is produced from the initiality of the relative seminormalization.

The section is converted into a ring map by `Spec.fullyFaithful.preimage`, and the identity
`algebraMap R _ ≫ (that ring map) = id` is extracted from the categorical identity by
`Scheme.Spec.map_injective`, which is where full faithfulness of `Spec` is used.

## References

* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
* [Stacks Project, Tag 0EUI](https://stacks.math.columbia.edu/tag/0EUI)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A reduced ring all of whose square-cube extensions admit a section on spectra is
seminormal. -/
theorem isSeminormalRing_of_squareCube_sections (R : Type u) [CommRing R]
    [_root_.IsReduced R]
    (hsection : ∀ x y : R, x ^ 3 = y ^ 2 →
      ∃ s : Spec (.of R) ⟶ Spec (.of (SquareCubeAlgebra R x y)),
        s ≫ squareCubeSpecMap R x y = 𝟙 _) :
    IsSeminormalRing R := by
  intro x y hxy
  obtain ⟨s, hs⟩ := hsection x y hxy
  let S := SquareCubeAlgebra R x y
  let relations : Ideal (Polynomial R) := Ideal.span
    ({Polynomial.X ^ 2 - Polynomial.C x, Polynomial.X ^ 3 - Polynomial.C y} :
      Set (Polynomial R))
  let root : S := Ideal.Quotient.mk relations Polynomial.X
  let φ : CommRingCat.of S ⟶ CommRingCat.of R := (Spec.fullyFaithful.preimage s).unop
  have hφ : CommRingCat.ofHom (algebraMap R S) ≫ φ = 𝟙 (CommRingCat.of R) := by
    apply Quiver.Hom.op_inj
    apply Scheme.Spec.map_injective
    simpa [φ, Functor.map_comp] using hs
  have hrestrict (r : R) : φ.hom (algebraMap R S r) = r :=
    congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of R => k.hom r) hφ
  have hpow (n : ℕ) (a : R) (ha : Polynomial.X ^ n - Polynomial.C a ∈ relations) :
      a = φ.hom root ^ n := by
    have hrel : (Ideal.Quotient.mk relations (Polynomial.X ^ n - Polynomial.C a) : S) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr ha
    have hC : (Ideal.Quotient.mk relations (Polynomial.C a) : S) = algebraMap R S a := by
      simpa [Polynomial.algebraMap_eq] using Ideal.Quotient.mk_algebraMap R relations a
    have hroot : root ^ n = algebraMap R S a :=
      (sub_eq_zero.mp (by simpa only [map_sub, map_pow] using hrel)).trans hC
    simpa only [map_pow, hrestrict] using (congrArg φ.hom hroot).symm
  have h₂ : x = φ.hom root ^ 2 := hpow 2 x (Ideal.subset_span (by simp))
  have h₃ : y = φ.hom root ^ 3 := hpow 3 y (Ideal.subset_span (by simp))
  exact ⟨φ.hom root, ⟨h₂, h₃⟩, fun a ha =>
    Stacks.RingTheory.Seminormal.eq_of_sq_eq_of_cube_eq (ha.1.symm.trans h₂)
      (ha.2.symm.trans h₃)⟩

end AlgebraicGeometry

end
