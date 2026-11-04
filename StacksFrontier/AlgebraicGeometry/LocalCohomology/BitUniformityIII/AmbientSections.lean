module

public import StacksFrontier.AlgebraicGeometry.Blowup.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesGrading
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionRing
public import StacksCore.Tactic.StacksAttribute

/-!
# The twists of the structure sheaf of a blowup and the canonical map out of `Iᑫ`

Let `A` be a commutative ring and `I ⊆ A` an ideal. The blowup of `Spec A` in `I` is
`X = Proj(⨁_{n ≥ 0} Iⁿ)`, and the twists `𝒪_X(q)` of its structure sheaf are the twisting
sheaves of [Stacks, Tag 01MS] for the Rees grading. The canonical map `Iᑫ ⟶ Γ(X, 𝒪_X(q))` is the
degree-`q` section map of [Stacks, Tag 0AG2], read through the identification
`Stacks.Blowup.reesGradingEquivPow` of `Iᑫ` with the degree-`q` piece of the Rees algebra.

Only this much of the geometry is needed to *state* [Stacks, Tag 0AG6] part (3) on the blowup —
that the canonical map is bijective for every large `q`. Both halves of that statement are
proved further down the import graph, the injective half in
`StacksFrontier/AlgebraicGeometry/LocalCohomology/BitUniformityIII/AmbientSectionsInjective.lean`
and the surjective half in
`StacksFrontier/AlgebraicGeometry/Blowup/ProjectiveAmbientSections.lean`, and both of those files
need the definitions below. They are therefore kept here, upstream of the thickenings of the
exceptional divisor and of the cohomology of
`StacksFrontier/AlgebraicGeometry/LocalCohomology/BitUniformityIII/BlowupTwists.lean`, which is
where they used to live: with them there, the four clauses of [Stacks, Tag 0GA7] could not cite
[Stacks, Tag 0AG6] part (3) at all, because the files proving it import the file stating the
clauses.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.blowupScheme`: the blowup `X` of `Spec A` in `I`.
* `Stacks.LocalCohomology.UniformityIII.blowupTwist`: the twist `𝒪_X(q)`.
* `Stacks.LocalCohomology.UniformityIII.blowupΓ`: global sections `Γ(X, ℱ)`.
* `Stacks.LocalCohomology.UniformityIII.ambientSections`: the canonical `Iᑫ ⟶ Γ(X, 𝒪_X(q))`.

## References

* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 0AG2](https://stacks.math.columbia.edu/tag/0AG2)
* [Stacks Project, Tag 0AG6](https://stacks.math.columbia.edu/tag/0AG6)
* [Stacks Project, Tag 0GA6](https://stacks.math.columbia.edu/tag/0GA6)
* [Stacks Project, Tag 0GA7](https://stacks.math.columbia.edu/tag/0GA7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf twistGlobalSections degreeSection)

universe u

namespace Stacks.LocalCohomology.UniformityIII

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- **The blowup `X` of `Spec(A)` in `I`**, the scheme of the Situation of [Stacks, Tag 0GA6]:
`Proj` of the Rees algebra `⨁_{n ≥ 0} Iⁿ`. -/
abbrev blowupScheme : Scheme.{u} := Stacks.Blowup.blowUpSpec I

/-- **The twist `𝒪_X(q)`** of the structure sheaf of the blowup. -/
abbrev blowupTwist (q : ℕ) : (blowupScheme I).Modules :=
  twistingSheaf (Stacks.Blowup.reesGrading I) (q : ℤ)

/-- Global sections `Γ(X, ℱ) = H⁰(X, ℱ)` of a sheaf of modules on the blowup. -/
abbrev blowupΓ (F : (blowupScheme I).Modules) : Type u := F.val.obj (op ⊤)

/-- The canonical section map of [Stacks, Tag 0AG2] in degree `q`, as an additive map. The
underlying function is `AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection`; only its
additivity is recorded here. -/
def degreeSectionHom (q : ℕ) :
    Stacks.Blowup.reesGrading I q →+ twistGlobalSections (Stacks.Blowup.reesGrading I) q where
  toFun := degreeSection _ q
  map_zero' := by unfold degreeSection; exact map_zero _
  map_add' a b := by
    unfold degreeSection
    rw [← map_add]
    congr 1

/-- **The canonical map `Iᑫ → H⁰(X, 𝒪_X(q))`**: the degree-`q` section map of [Stacks,
Tag 0AG2] for the Rees algebra, whose degree-`q` piece is `Iᑫ` by
`Stacks.Blowup.reesGradingEquivPow`. -/
def ambientSections (q : ℕ) : (I ^ q : Ideal A) →+ blowupΓ I (blowupTwist I q) :=
  (degreeSectionHom I q).comp (Stacks.Blowup.reesGradingEquivPow I q).toAddMonoidHom

end Stacks.LocalCohomology.UniformityIII

end
