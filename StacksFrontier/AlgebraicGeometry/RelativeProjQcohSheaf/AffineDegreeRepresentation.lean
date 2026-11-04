module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineFdRepresentable
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineRelativeDegreeOpen

/-!
# Naturality of the bijection `F_d(T) ≃ Mor(T, U_d)` over an affine base

Let `S` be an **affine** scheme, `𝒜` a graded `𝒪_S`-algebra with quasi-coherent homogeneous
pieces (Situation 01NN), `d ≥ 1`, and let `X` be a relative homogeneous spectrum of `𝒜` — in
particular `Proj_S(𝒜)` of Lemma 01NQ. The bijection
`...RelativeProjQcohSheaf.Quadruple.fdEquivDegreeOpen'` of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineRelativeDegreeOpen.lean` identifies
`F_d(T)` with `Mor(T, U_d)` for the degree-`d` open `U_d` of `X`. This file proves that
identification is **natural in the test scheme**, which is the `equiv_pullback` field of
`...RelativeProjQcohSheaf.ProjDegreeRepresentation`.

## Main results

* `...RelativeProjQcohSheaf.Quadruple.fdEquivDegreeOpen_pullback`: the naturality, with the
  degree a natural number.
* `...RelativeProjQcohSheaf.Quadruple.fdEquivDegreeOpen'_pullback`: the same at an integer
  degree, which is the shape the `equiv_pullback` field of `ProjDegreeRepresentation` is stated
  at.
* `...RelativeProjQcohSheaf.ProjDegreeRepresentation.ofAffineOfScale`: a
  `ProjDegreeRepresentation` over an affine base from the compatibility with the transitions
  `F_d → F_{a d}` alone.

## Implementation notes

`Quadruple.fdEquivDegreeOpen` is the classifying morphism of [Stacks, Tag 01N8] followed by an
isomorphism of the two readings of `U_d`, so its naturality is the naturality
`...RelativeProjQcohSheaf.Quadruple.classifyingHomOfClass_pullback` of the classifying morphism.

## References

* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

open Stacks.AlgebraicGeometry.RelativeProj

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-- **The bijection of Tag 01NU at the relative `U_d` is natural in the test scheme.**
For `S` affine and `𝒜` with quasi-coherent homogeneous pieces, the morphism
`T' ⟶ U_d` that `Quadruple.fdEquivDegreeOpen` attaches to the pullback of a class along
`g : T' ⟶ T` is `g` followed by the morphism it attaches to the class.

`Quadruple.fdEquivDegreeOpen` is `...RelativeProjQcohSheaf.Quadruple.classifyingHomOfClass`
followed by the isomorphism `...RelativeProj.RelativeProjData.degreeOpenAffineIso` of the
absolute degree-`d` open with the relative one (`Quadruple.fdEquivDegreeOpen_apply`), so this is
`Quadruple.classifyingHomOfClass_pullback` composed with that isomorphism. -/
theorem Quadruple.fdEquivDegreeOpen_pullback [IsAffine S] (P : RelativeProjData A) {d : ℕ}
    (hd : 0 < d) (hqc : ∀ n : ℤ, ((situationAlgebra A).piece n).IsQuasicoherent)
    {T' T : Scheme.{u}} (g : T' ⟶ T) (ξ : Fd (situationAlgebra A) (d : ℤ) T) :
    Quadruple.fdEquivDegreeOpen P hd hqc T' (Fd.pullback g ξ)
      = g ≫ Quadruple.fdEquivDegreeOpen P hd hqc T ξ := by
  rw [Quadruple.fdEquivDegreeOpen_apply, Quadruple.fdEquivDegreeOpen_apply,
    Quadruple.classifyingHomOfClass_pullback, Category.assoc]

/-- **The `equiv_pullback` field of `...RelativeProjQcohSheaf.ProjDegreeRepresentation` over an
affine base.** `Quadruple.fdEquivDegreeOpen_pullback` with the degree an integer, which is the
type the field is stated at.

The integer degree `d` is replaced by the natural number it is the cast of, after which the
degree transport `...RelativeProjQcohSheaf.Quadruple.fdEquivDegreeOpen'` performs is the
identity. -/
theorem Quadruple.fdEquivDegreeOpen'_pullback [IsAffine S] (P : RelativeProjData A) {d : ℤ}
    (hd : 0 < d) (hqc : ∀ n : ℤ, ((situationAlgebra A).piece n).IsQuasicoherent)
    {T' T : Scheme.{u}} (g : T' ⟶ T) (ξ : Fd (situationAlgebra A) d T) :
    Quadruple.fdEquivDegreeOpen' P hd hqc T' (Fd.pullback g ξ)
      = g ≫ Quadruple.fdEquivDegreeOpen' P hd hqc T ξ := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hd.le
  exact Quadruple.fdEquivDegreeOpen_pullback P (by exact_mod_cast hd) hqc g ξ

/-- For `S` affine and `𝒜` with quasi-coherent homogeneous pieces, a
`...RelativeProjQcohSheaf.ProjDegreeRepresentation` from the compatibility of the bijection with
the transitions `...RelativeProjQcohSheaf.Fd.scale : F_d → F_{a d}`. This is
`...RelativeProjQcohSheaf.ProjDegreeRepresentation.ofAffine` with its `hpullback` hypothesis
discharged by `Quadruple.fdEquivDegreeOpen'_pullback`. -/
def ProjDegreeRepresentation.ofAffineOfScale [IsAffine S] (P : RelativeProjData A)
    (hqc : ∀ n : ℤ, ((situationAlgebra A).piece n).IsQuasicoherent)
    (hscale : ∀ (d a : ℤ) (hd : 0 < d) (ha : 0 < a) (W : Scheme.{u}) (_hW : CompactSpace W)
      (ξ : Fd (situationAlgebra A) d W),
      Quadruple.fdEquivDegreeOpen' P (mul_pos ha hd) hqc W (Fd.scale ha ξ)
        = Quadruple.fdEquivDegreeOpen' P hd hqc W ξ ≫ P.scheme.homOfLE
            (P.degreeOpen_toNat_le_of_dvd hd (mul_pos ha hd) ⟨a, mul_comm a d⟩)) :
    ProjDegreeRepresentation A P :=
  ProjDegreeRepresentation.ofAffine P hqc
    (fun _ hd _ _ _ _ h ξ => Quadruple.fdEquivDegreeOpen'_pullback P hd hqc h ξ) hscale

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
