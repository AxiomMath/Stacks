module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.Proper
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.OverField
public import StacksFrontier.AlgebraicGeometry.RelativeProj.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.ProjectiveSpaceMorphism
public import StacksFrontier.RingTheory.GradedAlgebra.SymmetricAway.DegreeOneChart
public import StacksCore.Tactic.StacksAttribute

/-!
# The projection of a projective bundle: finite type, flatness, relative dimension

Stacks 02TX attaches four assertions to the projective bundle `π : 𝐏(ℰ) ⟶ X` of a finite locally
free sheaf of modules of rank `r`: that `π` is locally of finite type, that it is flat, that it
has relative dimension `r - 1`, and that the resulting map of Chow groups is an isomorphism.
This file proves the first three for a free module; see the section *Elsewhere* below.

## What is proved, and for which bundle

Local finite type is unconditional for the projective bundle
`Stacks.RelativeProj.projectiveBundleToBase` of an arbitrary finite locally free `ℰ`: it is one
of the three component conditions of properness, and properness of that projection is
`Stacks.RelativeProj.isProper_projectiveBundleToBase`.

Flatness and relative dimension are proved for the projective bundle of a *free* module sheaf of
finite rank, `Stacks.SymGraded.freeProjectiveBundle`, by way of the identification of that bundle
with relative projective space (Stacks 01OE,
`Stacks.SymGraded.projectiveBundleIsoProjectiveSpace`). Both statements are therefore first
proved for `AlgebraicGeometry.projectiveSpaceOver` and then transported along that
identification, which is an isomorphism over the base.

For `ℙⁿ_S ⟶ S` the two statements have short proofs. Flatness is base change from the integral
model: `ℙⁿ_S ⟶ S` is the base change of `ℙⁿ_ℤ ⟶ Spec ℤ`, that morphism is the degree-zero
structure morphism of `Proj ℤ[T₀, …, Tₙ]` up to an isomorphism of the target, and flatness of the
latter is the chartwise computation
`Stacks.SymmetricAway.flatChartRing`. Relative dimension is the fibrewise statement that
`ℙⁿ` over a field is equidimensional of dimension `n`, which is
`Stacks.ProjectiveSpace.equidimensional_and_topologicalKrullDim_proj_fin`, together with the
identification of the fibre of `ℙⁿ_S ⟶ S` at `s` with `ℙⁿ` over the residue field at `s`.

## Main results

* `AlgebraicGeometry.Proj.flat_toSpecZero_mvPolynomial`: the structure morphism of `Proj` of a
  polynomial ring, graded by total degree, is flat over `Spec` of its degree-zero part.
* `AlgebraicGeometry.flat_projectiveSpaceOver` and
  `AlgebraicGeometry.locallyOfFiniteType_projectiveSpaceOver`: **`ℙⁿ_S ⟶ S` is flat and locally
  of finite type.**
* `AlgebraicGeometry.relativeDimension_projectiveSpaceOver`: **`ℙⁿ_S ⟶ S` has relative dimension
  `n`.**
* `AlgebraicGeometry.relativeDimension_of_iso_over`: relative dimension is invariant under an
  isomorphism of the source over the base.
* `Stacks.SymGraded.flat_freeProjectiveBundleToBase` and
  `Stacks.SymGraded.relativeDimension_freeProjectiveBundleToBase`: **the projection of
  `𝐏(𝒪_X^{n+1})` is flat and has relative dimension `n`.**
* `Stacks.RelativeProj.locallyOfFiniteType_projectiveBundleToBase`: **the projection of the
  projective bundle of a finite locally free sheaf of modules is locally of finite type.**

## Implementation notes

The degree-zero part of `ℤ[T₀, …, Tₙ]` for the grading by total degree is the ring of constants,
not the ring `ℤ` itself, so `AlgebraicGeometry.Proj.toSpecZero` of the integral model lands in
`Spec` of that ring rather than in the terminal scheme. The two agree because the ring of
constants is isomorphic to `ℤ` (`Stacks.SymmetricAway.gradeZeroRingEquiv`), hence its spectrum is
terminal, hence the comparison with the terminal scheme is an isomorphism; flatness is invariant
under composition with an isomorphism.

## Elsewhere

The Chow-group isomorphism of Stacks 02TX is `Stacks.Chow.projectiveBundle_formula` of
`StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Formula`, where the `@[stacks 02TX]`
attribute sits. Flatness and relative dimension for a finite locally free `ℰ` of constant rank
are `Stacks.ProjectiveBundle.flat_toBase` and `Stacks.ProjectiveBundle.relativeDimension_toBase`
of `StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeFlat`, deduced locally from the
free case proved here.

## References

* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

universe u v

namespace AlgebraicGeometry

/-! ### Projective space over a base -/

/-- **`Proj` of a polynomial ring is flat over `Spec` of the degree-zero part of its grading by
total degree.** The standard affine charts `D₊(Tᵢ)` cover `Proj`, and each is a polynomial
algebra over the ring of constants, hence free. -/
theorem Proj.flat_toSpecZero_mvPolynomial (R : Type u) [CommRing R] (σ : Type v) :
    Flat (Proj.toSpecZero (homogeneousSubmodule σ R)) :=
  Proj.flat_toSpecZero_of_flat_away (homogeneousSubmodule σ R) (X : σ → MvPolynomial σ R)
    (fun _ => 1) (fun _ => Nat.one_pos)
    (fun i => Stacks.SymmetricAway.X_mem_homogeneousSubmodule_one i)
    (Stacks.SymmetricAway.adjoin_range_X_gradeZero R σ)
    (fun i => Stacks.SymmetricAway.flatChartRing i)

/-- **The spectrum of the degree-zero part of `ℤ[T₀, …, Tₙ]` is a terminal scheme.** The
degree-zero part for the grading by total degree is the ring of constants, which is `ℤ`. -/
def Proj.isTerminal_specGradeZero_mvPolynomialInt (n : ℕ) :
    IsTerminal (Spec (.of (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) 0))) :=
  specULiftZIsTerminal.{u}.ofIso
    (asIso (Spec.map
      ((Stacks.SymmetricAway.gradeZeroRingEquiv (ULift.{u} ℤ)
        (Fin (n + 1))).symm.toCommRingCatIso).hom))

/-- **The integral model of projective `n`-space is flat over the terminal scheme.** Its
structure morphism is the degree-zero structure morphism of `Proj ℤ[T₀, …, Tₙ]` followed by an
isomorphism, because the spectrum of the ring of constants is terminal. -/
theorem flat_terminal_from_projectiveSpaceAtUniverse (n : ℕ) :
    Flat (terminal.from (projectiveSpaceAtUniverse.{u} n)) := by
  have hiso := isIso_of_isTerminal (Proj.isTerminal_specGradeZero_mvPolynomialInt.{u} n)
    terminalIsTerminal
    (terminal.from (Spec (.of (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) 0))))
  have hsrc : IsZariskiLocalAtSource @Flat :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat)
  have := hsrc.toRespects
  have heq : terminal.from (projectiveSpaceAtUniverse.{u} n) =
      Proj.toSpecZero (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) ≫
        terminal.from (Spec (.of (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) 0))) :=
    terminal.hom_ext _ _
  rw [heq]
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @Flat)
    (Proj.toSpecZero (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)))
    (terminal.from (Spec (.of (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) 0))))).mpr
    (Proj.flat_toSpecZero_mvPolynomial (ULift.{u} ℤ) (Fin (n + 1)))

/-- **The structure morphism of `ℙⁿ_S` is flat**, being the base change of the structure morphism
of the integral model. -/
instance flat_projectiveSpaceOver (n : ℕ) (S : Scheme.{u}) :
    Flat (projectiveSpaceOver n S ↘ S) :=
  have := flat_terminal_from_projectiveSpaceAtUniverse.{u} n
  inferInstanceAs (Flat (pullback.fst (terminal.from S) _))

/-- **The structure morphism of `ℙⁿ_S` is locally of finite type**, being proper. -/
instance locallyOfFiniteType_projectiveSpaceOver (n : ℕ) (S : Scheme.{u}) :
    LocallyOfFiniteType (projectiveSpaceOver n S ↘ S) :=
  have := isProper_projectiveSpaceOver n S
  inferInstance

/-- **The structure morphism of `ℙⁿ_S` has relative dimension `n`.** Its fibre at `s` is `ℙⁿ`
over the residue field at `s`, which is equidimensional of Krull dimension `n`. -/
theorem relativeDimension_projectiveSpaceOver (n : ℕ) (S : Scheme.{u}) :
    RelativeDimension (projectiveSpaceOver n S ↘ S) n := by
  intro s _
  have e : (projectiveSpaceOver n S ↘ S).fiber s ≅
      projectiveSpaceOverRing n (S.residueField s) :=
    projectiveSpaceOverBaseChangeIso n (S.fromSpecResidueField s)
  have ec := (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison
    (↥(S.residueField s)) n).iso
  have hh := (e ≪≫ ec).hom.homeomorph
  refine ⟨Equidimensional.of_homeomorph hh
    (Stacks.ProjectiveSpace.equidimensional_proj_fin _ (n + 1)), ?_⟩
  rw [IsHomeomorph.topologicalKrullDim_eq _ hh.isHomeomorph]
  simpa using Stacks.ProjectiveSpace.topologicalKrullDim_proj_fin
    (↥(S.residueField s)) (r := n + 1) n.succ_pos

/-! ### Relative dimension along an isomorphism over the base -/

/-- The fibres of two morphisms to the same base that differ by an isomorphism of their sources
are homeomorphic: the isomorphism carries one set-theoretic fibre onto the other. -/
def Scheme.Hom.fiberHomeoCompIso {X Y S : Scheme.{u}} (e : X ≅ Y) (g : Y ⟶ S) (s : S) :
    (e.hom ≫ g).fiber s ≃ₜ g.fiber s :=
  ((e.hom ≫ g).fiberHomeo s).trans
    ((e.hom.homeomorph.subtype (p := fun x => x ∈ (e.hom ≫ g) ⁻¹' {s})
        (q := fun y => y ∈ g ⁻¹' {s}) (fun x => by simp)).trans
      (g.fiberHomeo s).symm)

/-- **Relative dimension is invariant under an isomorphism of the source over the base.** -/
theorem relativeDimension_of_iso_over {X Y S : Scheme.{u}} (e : X ≅ Y) (g : Y ⟶ S)
    (f : X ⟶ S) (hf : e.hom ≫ g = f) [LocallyOfFiniteType g] [LocallyOfFiniteType f] {d : ℕ}
    (h : RelativeDimension g d) : RelativeDimension f d := by
  intro s hs
  have hh : f.fiber s ≃ₜ g.fiber s := hf ▸ Scheme.Hom.fiberHomeoCompIso e g s
  obtain ⟨heq, hdim⟩ := h s ⟨hh hs.some⟩
  refine ⟨Equidimensional.of_homeomorph hh heq, ?_⟩
  rw [IsHomeomorph.topologicalKrullDim_eq _ hh.isHomeomorph]
  exact hdim

end AlgebraicGeometry

/-! ### The projective bundle of a free module sheaf -/

namespace Stacks.SymGraded

variable (X : Scheme.{u}) (n : ℕ)

/-- **The projection of `𝐏(𝒪_X^{n+1})` is locally of finite type.** The bundle is `ℙⁿ_X` over
`X` by Stacks 01OE, and the structure morphism of `ℙⁿ_X` is proper. -/
instance locallyOfFiniteType_freeProjectiveBundleToBase :
    LocallyOfFiniteType (freeProjectiveBundle (X := X) n).toBase := by
  rw [← projectiveBundleIsoProjectiveSpace_hom_comp_fst (X := X) n]
  exact inferInstanceAs (LocallyOfFiniteType
    ((projectiveBundleIsoProjectiveSpace (X := X) n).hom ≫ (projectiveSpaceOver n X ↘ X)))

/-- **Stacks 02TX, the flatness assertion for a free module sheaf of finite rank.** The
projection of the projective bundle `𝐏(𝒪_X^{n+1})` is flat: the bundle is `ℙⁿ_X` over `X` by
Stacks 01OE, and `ℙⁿ_X` is flat over `X`. -/
instance flat_freeProjectiveBundleToBase :
    Flat (freeProjectiveBundle (X := X) n).toBase := by
  rw [← projectiveBundleIsoProjectiveSpace_hom_comp_fst (X := X) n]
  exact inferInstanceAs (Flat
    ((projectiveBundleIsoProjectiveSpace (X := X) n).hom ≫ (projectiveSpaceOver n X ↘ X)))

/-- **Stacks 02TX, the relative-dimension assertion for a free module sheaf of finite rank.** The
projection of the projective bundle `𝐏(𝒪_X^{n+1})` has relative dimension `n`, one less than the
rank: the bundle is `ℙⁿ_X` over `X` by Stacks 01OE, and `ℙⁿ_X ⟶ X` has relative dimension
`n`. -/
theorem relativeDimension_freeProjectiveBundleToBase :
    RelativeDimension (freeProjectiveBundle (X := X) n).toBase n :=
  relativeDimension_of_iso_over (projectiveBundleIsoProjectiveSpace (X := X) n)
    (projectiveSpaceOver n X ↘ X) _
    (projectiveBundleIsoProjectiveSpace_hom_comp_fst (X := X) n)
    (relativeDimension_projectiveSpaceOver n X)

end Stacks.SymGraded

/-! ### The projective bundle of a finite locally free module sheaf -/

namespace Stacks.RelativeProj

/-- **Stacks 02TX, the finite-type assertion.** The projection `π : 𝐏(ℰ) ⟶ X` of the projective
bundle of a finite locally free sheaf of modules is locally of finite type, local finite type
being one of the three component conditions of properness. -/
theorem locallyOfFiniteType_projectiveBundleToBase (X : Scheme.{u}) (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    LocallyOfFiniteType (projectiveBundleToBase X E) :=
  have := isProper_projectiveBundleToBase X E
  inferInstance

end Stacks.RelativeProj

end
