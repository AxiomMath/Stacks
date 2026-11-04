module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjModuleDegreeZeroFlat
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import StacksFrontier.AlgebraicGeometry.RelativeProjFlat.GradedPieces

/-!
# Flatness of the twist sections of a relative `Proj` chart over the base

Let `A` be a quasi-coherent graded `𝒪_S`-algebra and `U` an affine open of the base. The chart of
the relative projective spectrum over `U` is the absolute `Proj` of the graded ring of sections
`A(U)`, and the twist `𝒪(t)` on that chart has, over the standard open `D₊(f)` attached to a
homogeneous `f ∈ A(U)_d` of positive degree, the degree-zero part of the localization of the
`t`-th twist of `A(U)` away from `f` as its module of sections.

This file proves that this module of sections is flat over `Γ(S, U)` as soon as the homogeneous
pieces of `A` of all large degrees are flat `𝒪_S`-modules. That is the local content of the second
assertion of Stacks tag 0D4C, and the argument is the same as for the first: the degree-zero part
of the twisted localization is the direct limit of the pieces `A(U)_{kd + t}`, and a direct limit
of flat modules is flat. Only the bookkeeping differs, because a twist by `t` shifts the degrees
that occur and `t` may be negative; starting the system at `N + |t|` absorbs that.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.flat_twistLocalization`: the
  degree-zero part of the twisted localization is a flat `Γ(S, U)`-module.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.flat_twistSections`: the
  sections of the twisting sheaf over a standard affine open of the chart are a flat
  `Γ(S, U)`-module.

## Implementation notes

The `Γ(S, U)`-module structure on the sections of the twisting sheaf is restriction of scalars
along `Γ(S, U) → A(U)_0 → A(U)_(f) → Γ(𝒪(t), D₊(f))`, the last map being
`AlgebraicGeometry.Proj.awayToSection`; it is introduced by `let` in the statements, as the
corresponding criteria of `AlgebraicGeometry.isFlatOver_tfae` are.

The graded ring of sections is a direct sum, so it carries a second `Γ(S, U)`-module structure,
acting summandwise, besides the one its structure map defines. The two agree, but not
definitionally, and the summandwise one is the one instance search finds; so the module structure
coming from the structure map is installed as a local instance before the criterion of
`AlgebraicGeometry.ProjectiveSpectrum.Proj.flat_degreeZeroLocalization` is applied.

The degree action of `ℕ` on `ℤ` is the local `VAdd ℕ ℤ` instance adding the cast, as in the files
that define the integer-graded twist of a graded ring.

## References

* [Stacks Project, Tag 0D4C](https://stacks.math.columbia.edu/tag/0D4C)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

/-- The grading action of natural-number ring degrees on integer module degrees, by addition. -/
local instance twistSectionDegreeVAdd : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

namespace Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U : S.Opens)

include A in
/-- **The degree-zero part of the `t`-th twisted localization of the graded ring of sections at a
homogeneous element of positive degree is a flat `Γ(S, U)`-module** when the homogeneous pieces of
the graded algebra of all large enough degree are flat `𝒪_S`-modules.

The system whose direct limit it is runs over the pieces of degree `(K + i) d + t` with
`K = N + |t|`, and those degrees are all at least `N`, so every term of the system is flat. -/
public theorem flat_twistLocalization (N : ℕ)
    (hNflat : ∀ n : ℕ, N ≤ n →
      IsFlatOver (𝟙 S : S ⟶ S).toLRSHom.toShHom (A.piece (n : ℤ)))
    (hU : IsAffineOpen U) {d : ℕ} (hd : 0 < d) {f : A.sectionRing U}
    (hf : f ∈ A.grading U d) (t : ℤ) :
    letI := A.sectionRingAlgebra U
    letI : Module Γ(S, U)
        (GradedModuleDegreeZeroLocalization (A.grading U)
          (twistGrading (A.grading U) t) f) :=
      Module.compHom _
        ((HomogeneousLocalization.fromZeroRingHom (A.grading U) (Submonoid.powers f)).comp
          (GradedRing.toGradeZero (A.grading U) (A.strHom_mem U)))
    Module.Flat Γ(S, U)
      (GradedModuleDegreeZeroLocalization (A.grading U)
        (twistGrading (A.grading U) t) f) := by
  let _ := A.sectionRingAlgebra U
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = N + t.natAbs := ⟨_, rfl⟩
  have hbound (i : ℕ) : (N : ℤ) ≤ (((K + i) * d : ℕ) : ℤ) + t := by
    have hmul : K + i ≤ (K + i) * d := Nat.le_mul_of_pos_right _ hd
    have hmul' : ((K + i : ℕ) : ℤ) ≤ (((K + i) * d : ℕ) : ℤ) := Int.ofNat_le.mpr hmul
    push_cast at hmul'
    omega
  refine flat_degreeZeroLocalization (A.grading U) (twistGrading (A.grading U) t)
    (GradedRing.toGradeZero (A.grading U) (A.strHom_mem U)) hf K
    (fun i => GradedRing.toSubmodules (A.grading U) (A.strHom_mem U)
      ((((K + i) * d : ℕ) : ℤ) + t).toNat) ?_ ?_
  · intro i x
    have hi : 0 ≤ (((K + i) * d : ℕ) : ℤ) + t := (Int.natCast_nonneg N).trans (hbound i)
    have hdeg : (K + i) • (d : ℤ) + t = (((((K + i) * d : ℕ) : ℤ) + t).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg hi]
      push_cast
      ring
    rw [twistGrading_apply, hdeg, integerGrading_natCast]
    exact Iff.rfl
  · intro i
    refine A.flat_grading U (hNflat _ ?_) hU
    have := hbound i
    omega

include A in
/-- **The sections of the `t`-th twisting sheaf over a standard affine open of a chart of the
relative `Proj` are a flat `Γ(S, U)`-module** when the homogeneous pieces of the graded algebra of
all large enough degree are flat `𝒪_S`-modules.

The sections over `D₊(f)` are the degree-zero part of the twisted localization, by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv`, and that
identification is `A(U)_(f)`-linear, hence `Γ(S, U)`-linear for the two induced actions. -/
public theorem flat_twistSections (N : ℕ)
    (hNflat : ∀ n : ℕ, N ≤ n →
      IsFlatOver (𝟙 S : S ⟶ S).toLRSHom.toShHom (A.piece (n : ℤ)))
    (hU : IsAffineOpen U) {d : ℕ} (hd : 0 < d) {f : A.sectionRing U}
    (hf : f ∈ A.grading U d) (t : ℤ) :
    letI := A.sectionRingAlgebra U
    let T : (AlgebraicGeometry.Proj (A.grading U)).Modules :=
      twistingSheaf (A.grading U) t
    letI : Module Γ(S, U) Γ(T, Proj.basicOpen (A.grading U) f) :=
      Module.compHom _ ((Proj.awayToSection (A.grading U) f).hom.comp
        ((HomogeneousLocalization.fromZeroRingHom (A.grading U) (Submonoid.powers f)).comp
          (GradedRing.toGradeZero (A.grading U) (A.strHom_mem U))))
    Module.Flat Γ(S, U) Γ(T, Proj.basicOpen (A.grading U) f) := by
  let _ := A.sectionRingAlgebra U
  let T : (AlgebraicGeometry.Proj (A.grading U)).Modules := twistingSheaf (A.grading U) t
  let φ : Γ(S, U) →+* HomogeneousLocalization.Away (A.grading U) f :=
    (HomogeneousLocalization.fromZeroRingHom (A.grading U) (Submonoid.powers f)).comp
      (GradedRing.toGradeZero (A.grading U) (A.strHom_mem U))
  let _ : Module Γ(S, U) Γ(T, Proj.basicOpen (A.grading U) f) :=
    Module.compHom _ ((Proj.awayToSection (A.grading U) f).hom.comp φ)
  let _ : Module Γ(S, U)
      (GradedModuleDegreeZeroLocalization (A.grading U)
        (twistGrading (A.grading U) t) f) :=
    Module.compHom _ φ
  let e := associatedModuleSheafStandardOpenEquiv (A.grading U)
    (twistGrading (A.grading U) t) hf hd
  let eR : Γ(T, Proj.basicOpen (A.grading U) f) ≃ₗ[Γ(S, U)]
      GradedModuleDegreeZeroLocalization (A.grading U) (twistGrading (A.grading U) t) f :=
    { e.toAddEquiv with map_smul' := fun r x => e.map_smul (φ r) x }
  exact (Module.Flat.equiv_iff eR).mpr (A.flat_twistLocalization U N hNflat hU hd hf t)

end Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra

end
