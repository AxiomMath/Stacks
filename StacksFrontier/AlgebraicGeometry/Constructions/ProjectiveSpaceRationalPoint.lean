module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace

/-!
# A section of projective space over an arbitrary base

Projective `n`-space over a scheme `S` is the base change of its integral model, so a point of
the integral model gives a section of the structure morphism `ℙⁿ_S ⟶ S`.  The point used here
is the one all of whose homogeneous coordinates are `1`: evaluating the coordinates at `1`
inverts the zeroth one, so the evaluation extends over the localization away from it and gives
a morphism `Spec ℤ ⟶ ℙⁿ_ℤ` through the standard affine chart.

## Main definitions

* `AlgebraicGeometry.allOnesPointAtUniverse`: the point of the integral model of projective
  space all of whose homogeneous coordinates are `1`, read on an arbitrary scheme.

## Main results

* `AlgebraicGeometry.allOnesSection_comp_structureMorphism` and
  `AlgebraicGeometry.exists_section_projectiveSpaceOver`: the structure morphism of projective
  space over any base scheme has a section.

## References

* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The point of the integral model of projective space all of whose homogeneous coordinates
are `1`, read on an arbitrary scheme through the terminal morphism to `Spec ℤ`. -/
def allOnesPointAtUniverse (S : Scheme.{u}) (n : ℕ) : S ⟶ projectiveSpaceAtUniverse.{u} n := by
  let R := ULift.{u} ℤ
  let A := MvPolynomial (Fin (n + 1)) R
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
  let : GradedAlgebra 𝒜 := MvPolynomial.gradedAlgebra
  let x : A := MvPolynomial.X 0
  let ε : A →+* R := MvPolynomial.eval₂Hom (RingHom.id R) (fun _ => 1)
  have hx : IsUnit (ε x) := by
    change IsUnit (MvPolynomial.eval₂Hom (RingHom.id R) (fun _ => 1) (MvPolynomial.X 0))
    rw [MvPolynomial.eval₂Hom_X']
    exact isUnit_one
  let e : HomogeneousLocalization.Away 𝒜 x →+* R :=
    (Localization.awayLift ε x hx).comp
      (algebraMap (HomogeneousLocalization.Away 𝒜 x) (Localization.Away x))
  exact specULiftZIsTerminal.from S ≫ Spec.map (CommRingCat.ofHom e) ≫
    Proj.awayι 𝒜 x (MvPolynomial.isHomogeneous_X R 0) (by omega)

/-- The section of `ℙⁿ_S ⟶ S` named by the point all of whose homogeneous coordinates
are `1`. -/
def allOnesSection (S : Scheme.{u}) (n : ℕ) : S ⟶ projectiveSpaceOver n S :=
  pullback.lift (𝟙 S) (allOnesPointAtUniverse S n) (terminal.hom_ext _ _)

/-- The morphism `allOnesSection S n` is a section of the structure morphism `ℙⁿ_S ⟶ S`. -/
@[simp]
theorem allOnesSection_comp_structureMorphism (S : Scheme.{u}) (n : ℕ) :
    allOnesSection S n ≫ (projectiveSpaceOver n S ↘ S) = 𝟙 S :=
  pullback.lift_fst _ _ _

/-- **The structure morphism of projective space over any base scheme has a section.** -/
theorem exists_section_projectiveSpaceOver (S : Scheme.{u}) (n : ℕ) :
    ∃ s : S ⟶ projectiveSpaceOver n S, s ≫ (projectiveSpaceOver n S ↘ S) = 𝟙 S :=
  ⟨allOnesSection S n, allOnesSection_comp_structureMorphism S n⟩

/-- **The structure morphism of projective space over a ring has a section.** -/
theorem exists_section_projectiveSpaceOverRing (R : CommRingCat.{u}) (n : ℕ) :
    ∃ s : Spec R ⟶ projectiveSpaceOverRing n R,
      s ≫ (projectiveSpaceOverRing n R ↘ Spec R) = 𝟙 (Spec R) :=
  exists_section_projectiveSpaceOver (Spec R) n

end AlgebraicGeometry

end
