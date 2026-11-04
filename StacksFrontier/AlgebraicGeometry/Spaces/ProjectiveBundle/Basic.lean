module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SymmetricAlgebraQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Space
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria

/-!
# The projective bundle of a quasi-coherent module on an algebraic space

Let `X` be an algebraic space over a scheme `S` and `ℰ` a quasi-coherent `𝒪_X`-module.  Its
projective bundle is `𝐏(ℰ) = Proj_X(Sym(ℰ))`, the relative homogeneous spectrum of Stacks 084C
of the symmetric algebra of `ℰ`, with its structure morphism `π : 𝐏(ℰ) ⟶ X`.

## Main definitions

* `AlgebraicGeometry.Space.projectiveBundleSituation`: Situation 0849 for `Sym(ℰ)`.
* `AlgebraicGeometry.Space.relativeProjSymmetricAlgebra`: the algebraic space `𝐏(ℰ)`.
* `AlgebraicGeometry.Space.projectiveBundleπ`: its structure morphism `π : 𝐏(ℰ) ⟶ X`.

## Main results

* `AlgebraicGeometry.Space.isSeparated_projectiveBundleπ`: `π` is separated (Stacks 084E).
* `AlgebraicGeometry.Space.isClosedImmersion_of_section_projectiveBundleπ`: a section of `π` is
  a closed immersion, being a section of a separated morphism (Stacks 03KP, part (3)).

## Implementation notes

The homogeneous sections of `Sym(ℰ)` are assumed bounded by the size cutoff of the big fppf
site (`AlgebraicGeometry.Space.SymmetricAlgebraBounded`).  This is the set-theoretic convention
of Stacks 025T recorded by the field
`AlgebraicGeometry.Space.RelativeProjSituation.sections_hasCardinalLT` of Situation 0849, and
nothing more: the relative Proj of Stacks 084C is only an algebraic space over the chosen site
when it holds.

## References

* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The homogeneous sections of the symmetric algebra of `ℰ` are bounded by the size cutoff of
the big fppf site, as Situation 0849 requires of its graded algebra. -/
def SymmetricAlgebraBounded (X : AlgebraicSpaces B S hS)
    (E : SheafOfModules.{u} (structureRingSheaf B S hS X)) : Prop :=
  ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥(((symmetricAlgebra B S hS X E).piece n).val.obj U) B.cutoff

/-- **Situation 0849 for the symmetric algebra** of a quasi-coherent `𝒪_X`-module `ℰ`. -/
def projectiveBundleSituation (X : AlgebraicSpaces B S hS)
    (E : SheafOfModules.{u} (structureRingSheaf B S hS X)) (hE : E.IsQuasicoherentOnSite)
    (hb : SymmetricAlgebraBounded X E) : RelativeProjSituation.{u, u} where
  site := B
  base := S
  containsBase := hS
  space := X
  algebra := symmetricAlgebra B S hS X E
  mul_comm := symmetricAlgebra_mul_comm B S hS X E
  negative_isZero := isZero_symmetricAlgebra_piece_of_neg B S hS X E
  isQuasicoherent :=
    isQuasicoherentOnSite_symmetricAlgebra_piece_of_isQuasicoherentOnSite B S hS X E hE
  sections_hasCardinalLT := hb

/-- **The projective bundle `𝐏(ℰ) = Proj_X(Sym(ℰ))`** of a quasi-coherent `𝒪_X`-module on an
algebraic space, the relative Proj of Stacks 084C of its symmetric algebra. -/
abbrev relativeProjSymmetricAlgebra (X : AlgebraicSpaces B S hS)
    (E : SheafOfModules.{u} (structureRingSheaf B S hS X)) (hE : E.IsQuasicoherentOnSite)
    (hb : SymmetricAlgebraBounded X E) : AlgebraicSpaces B S hS :=
  (projectiveBundleSituation X E hE hb).Proj

/-- **The projection `π : 𝐏(ℰ) ⟶ X`** of the projective bundle. -/
abbrev projectiveBundleπ (X : AlgebraicSpaces B S hS)
    (E : SheafOfModules.{u} (structureRingSheaf B S hS X)) (hE : E.IsQuasicoherentOnSite)
    (hb : SymmetricAlgebraBounded X E) : relativeProjSymmetricAlgebra X E hE hb ⟶ X :=
  (projectiveBundleSituation X E hE hb).π

variable (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite) (hb : SymmetricAlgebraBounded X E)

/-- The projection of a projective bundle is separated (Stacks 084E). -/
theorem isSeparated_projectiveBundleπ :
    IsSeparated B S hS (projectiveBundleπ X E hE hb).hom :=
  (projectiveBundleSituation X E hE hb).isSeparated_relativeProjπ

/-- **A section of the projection of a projective bundle is a closed immersion**: it is a
section of a separated morphism (Stacks 03KP, part (3)). -/
theorem isClosedImmersion_of_section_projectiveBundleπ
    (σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb) (hσ : σ ≫ projectiveBundleπ X E hE hb = 𝟙 X) :
    IsClosedImmersion B S hS σ.hom :=
  isClosedImmersion_of_isSeparated_of_section B S hS _ (isSeparated_projectiveBundleπ X E hE hb)
    σ.hom (congrArg InducedCategory.Hom.hom hσ)

end AlgebraicGeometry.Space

end
