module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceProper
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Smooth
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Projective space over a field is a smooth projective variety

Let `k` be a field. Projective `n`-space over `k` is smooth over `k`, is projective over `k`, and
is a variety over `k`; together with the computation of its dimension in
`StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.OverField` these are the four assertions
of Tag 0B2P.

Smoothness and projectivity hold over an arbitrary base scheme and are stated there. Projective
space over `S` is the base change of its integral model along `S ⟶ Spec ℤ`, and the integral model
is smooth over `Spec ℤ` because the polynomial model is smooth over its coefficient ring; since
smoothness is stable under base change, `ℙⁿ_S ⟶ S` is smooth. Projectivity is immediate from the
definition of H-projectivity, the identity being a closed immersion of `ℙⁿ_S` into `ℙⁿ_S`.

The variety structure needs the base to be a field. Separatedness and finite type come from
properness; quasi-compactness also holds over an arbitrary base, the integral model being covered
by `n + 1` affine charts; and integrality comes from the identification of `ℙⁿ_R` with the
polynomial model `Proj R[T₀, …, Tₙ]`, which is integral whenever `R` is a domain.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.projectiveSpaceOver.smooth`: `ℙⁿ_S ⟶ S` is smooth.
* `AlgebraicGeometry.isProjectiveMorphism_projectiveSpaceOver`: `ℙⁿ_S ⟶ S` is projective.
* `AlgebraicGeometry.projectiveSpaceOver.quasiCompact`: `ℙⁿ_S ⟶ S` is quasi-compact.
* `AlgebraicGeometry.projectiveSpaceOverRing.isIntegral`: `ℙⁿ_R` is integral over a domain `R`.
* `AlgebraicGeometry.projectiveSpaceOverRing.isVariety`: `ℙⁿ_k` is a variety over a field `k`.

## Implementation notes

Projectivity is the repository's notion of Tag 01W8,
`AlgebraicGeometry.IsProjectiveMorphism`, which is clause (2) of that definition — H-projectivity,
a closed immersion over the base into a finite-dimensional projective space. It is the stronger of
the two notions in the source, since a closed immersion into `ℙⁿ_S = ℙ(𝒪_S^{n+1})` exhibits the
source as a closed subscheme of a projective bundle.

The comparison with the polynomial model is the coordinate-pinned isomorphism
`Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison`, whose `iso` field goes from the
base-change model `ℙⁿ_R` to `Proj R[T₀, …, Tₙ]`; integrality and compactness are transported along
it, and smoothness is not, being obtained over an arbitrary base scheme by base change instead.

## References

* [Stacks Project, Tag 0B2P](https://stacks.math.columbia.edu/tag/0B2P)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 020D](https://stacks.math.columbia.edu/tag/020D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart

namespace AlgebraicGeometry

universe u

/-! ### Smoothness -/

/-- The integral model of projective `n`-space is smooth over the terminal scheme: the terminal
scheme is `Spec (ULift ℤ)`, and the integral model is `Proj (ULift ℤ)[T₀, …, Tₙ]`, which is
smooth over `Spec (ULift ℤ)`. -/
public theorem smooth_terminalFrom_projectiveSpaceAtUniverse (n : ℕ) :
    Smooth (terminal.from (projectiveSpaceAtUniverse.{u} n)) := by
  have hiso : IsIso (terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ)))) :=
    isIso_of_isTerminal specULiftZIsTerminal terminalIsTerminal _
  have hbase : projToSpecCoeff (ULift.{u} ℤ) n ≫
      terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ))) =
      terminal.from (projectiveSpaceAtUniverse.{u} n) :=
    terminalIsTerminal.hom_ext _ _
  rw [← hbase]
  exact MorphismProperty.comp_mem @Smooth (projToSpecCoeff (ULift.{u} ℤ) n)
    (terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (smooth_projToSpecCoeff (ULift.{u} ℤ) n) inferInstance

namespace projectiveSpaceOver

/-- **Stacks Project, Tag 0B2P (smoothness).** Projective `n`-space over a scheme `S` is smooth
over `S`, being the base change of the integral model, which is smooth over the terminal
scheme. -/
@[stacks 0B2P "projective_space_smooth", ega "IV 17.3.9" "free E, P^n_S"]
public instance smooth (n : ℕ) (S : Scheme.{u}) : Smooth (projectiveSpaceOver n S ↘ S) :=
  smooth_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n))).flip
    (smooth_terminalFrom_projectiveSpaceAtUniverse n)

end projectiveSpaceOver

/-! ### Projectivity -/

/-- **Stacks Project, Tag 0B2P (projectivity).** Projective `n`-space over a scheme `S` is
projective over `S`: the identity is a closed immersion of `ℙⁿ_S` into `ℙⁿ_S` over `S`. -/
@[stacks 0B2P "projective_space_projective"]
public theorem isProjectiveMorphism_projectiveSpaceOver (n : ℕ) (S : Scheme.{u}) :
    IsProjectiveMorphism (projectiveSpaceOver n S ↘ S) :=
  ⟨n, 𝟙 (projectiveSpaceOver n S), inferInstance, Category.id_comp _⟩

/-! ### Quasi-compactness -/

/-- The integral model of projective `n`-space is quasi-compact over the terminal scheme: it is
`Proj (ULift ℤ)[T₀, …, Tₙ]`, which has a finite affine chart cover. -/
public theorem quasiCompact_terminalFrom_projectiveSpaceAtUniverse (n : ℕ) :
    QuasiCompact (terminal.from (projectiveSpaceAtUniverse.{u} n)) := by
  have h : CompactSpace (projectiveSpaceAtUniverse.{u} n) := compactSpace_proj (ULift.{u} ℤ) n
  exact (compactSpace_iff_quasiCompact _).mp h

namespace projectiveSpaceOver

/-- Projective `n`-space over a scheme `S` is quasi-compact over `S`, being the base change of
the integral model, which is quasi-compact over the terminal scheme. -/
public instance quasiCompact (n : ℕ) (S : Scheme.{u}) :
    QuasiCompact (projectiveSpaceOver n S ↘ S) := by
  have h : QuasiCompact (terminal.from (projectiveSpaceAtUniverse.{u} n)) :=
    quasiCompact_terminalFrom_projectiveSpaceAtUniverse n
  change QuasiCompact (pullback.fst (terminal.from S)
    (terminal.from (projectiveSpaceAtUniverse.{u} n)))
  infer_instance

end projectiveSpaceOver

/-! ### Integrality and the variety structure -/

namespace projectiveSpaceOverRing

variable (R : Type u) [CommRing R] (n : ℕ)

/-- **Projective `n`-space over a domain is integral.** It is isomorphic to the polynomial model
`Proj R[T₀, …, Tₙ]`, which is irreducible and reduced because its standard charts are spectra of
polynomial rings over `R` and all contain the zero ideal. -/
public instance isIntegral [IsDomain R] :
    IsIntegral (projectiveSpaceOverRing n (CommRingCat.of R)) := by
  have e := (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison R n).iso
  refine (isIntegral_iff_irreducibleSpace_and_isReduced _).2 ⟨?_, ?_⟩
  · exact e.hom.homeomorph.irreducibleSpace_iff.mpr inferInstance
  · exact isReduced_of_isOpenImmersion e.hom

/-- **Stacks Project, Tag 0B2P (variety).** Projective `n`-space over a field is a variety over
that field: it is integral, and its structure morphism is separated and of finite type because it
is proper, and quasi-compact because projective space is quasi-compact. -/
@[stacks 0B2P "projective_space_variety"]
public instance isVariety (k : Type u) [Field k] (n : ℕ) :
    IsVariety k (projectiveSpaceOverRing n (CommRingCat.of k) ↘ Spec (CommRingCat.of k)) :=
  IsVariety.mk

end projectiveSpaceOverRing

end AlgebraicGeometry

end
