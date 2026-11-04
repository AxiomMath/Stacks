module

public import StacksFrontier.Algebra.Homology.Koszul.AlternatingCechTotal
import StacksCore.Tactic.StacksAttribute

/-!
# The standing situation of the section on Koszul complexes

A commutative ring `A` together with a finite sequence `f₁, …, f_r` of elements of `A`
determines the affine scheme `X = Spec(A)`, the open `U = D(f₁) ∪ ⋯ ∪ D(f_r) ⊆ X` and the
open covering `𝒰 : U = ⋃ᵢ D(fᵢ)` of `U` by the standard opens. This is the situation in which
the Koszul complex of `f₁, …, f_r` is compared with the alternating Čech complex of `𝒰`.

## Main definitions

* `Koszul.CechSituation`: the ring and the finite sequence, as a bundle of data.
* `Koszul.CechSituation.X`, `Koszul.CechSituation.U`, `Koszul.CechSituation.cover`: the affine
  scheme, the open it covers and the covering itself.
* `Koszul.CechSituation.alternatingCechFunctor` and `Koszul.CechSituation.cechTotalFunctor`:
  the alternating Čech complex of `𝒰` and its total complex, as functors of the coefficients.

## Main results

* `Koszul.CechSituation.iSup_cover`: the standard opens really do cover `U`.

## Implementation notes

The situation fixes no condition on the sequence; in particular the standard opens are not
required to cover `X`. The covering `𝒰` is recorded as a family of opens of `U` and the
covering property `iSup_cover` is a theorem rather than a field, since it holds by
construction of `U` as the supremum of the standard opens.

The Čech constructions of `StacksFrontier.Algebra.Homology.Koszul.AlternatingCechTotal` take the
standard opens as opens of `X`, which is equivalent because a family of opens covers its own
supremum; `alternatingCechFunctor_obj` records that the situation's own family of standard
opens is the one they use.

## References

* [Stacks Project, Tag 08CZ](https://stacks.math.columbia.edu/tag/08CZ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open Stacks.LocalCohomology (associatedAbPresheaf)

universe u

namespace Koszul

/-- **Stacks Project, Tag 08CZ.** The standing situation of the section on Koszul complexes:
a commutative ring `A` and a finite sequence `f₁, …, f_r` of elements of `A`. The affine
scheme `X = Spec(A)`, the open `U = D(f₁) ∪ ⋯ ∪ D(f_r)` and the covering `𝒰` of `U` by the
standard opens `D(fᵢ)` are derived from these data. -/
@[stacks 08CZ]
structure CechSituation where
  /-- The ring `A`. -/
  A : Type u
  /-- The commutative ring structure on `A`. -/
  [commRing : CommRing A]
  /-- The length `r` of the sequence. -/
  r : ℕ
  /-- The sequence `f₁, …, f_r` of elements of `A`. -/
  f : Fin r → A

namespace CechSituation

attribute [instance] CechSituation.commRing

variable (S : CechSituation.{u})

/-- The affine scheme `X = Spec(A)` of the situation. -/
abbrev X : Scheme.{u} := Spec (CommRingCat.of S.A)

/-- The standard open `D(fᵢ) ⊆ X`. -/
abbrev basicOpen (i : Fin S.r) : S.X.Opens := PrimeSpectrum.basicOpen (S.f i)

/-- The open `U = D(f₁) ∪ ⋯ ∪ D(f_r) ⊆ X`. -/
abbrev U : S.X.Opens := ⨆ i, S.basicOpen i

/-- The open `U` as a scheme, that is, as an open subscheme of `X`. -/
abbrev scheme : Scheme.{u} := S.U.toScheme

/-- The open immersion `U ⟶ X`. -/
abbrev ι : S.scheme ⟶ S.X := S.U.ι

/-- The covering `𝒰 : U = ⋃ᵢ D(fᵢ)`, as the family of opens `D(fᵢ) ∩ U` of `U`. -/
abbrev cover (i : Fin S.r) : S.scheme.Opens := S.ι ⁻¹ᵁ S.basicOpen i

/-- The standard opens cover `U`: the family `𝒰` is an open covering of `U`. -/
theorem iSup_cover : ⨆ i, S.cover i = ⊤ := by
  rw [show (⨆ i, S.cover i) = S.ι ⁻¹ᵁ S.U from (Opens.map_iSup _ _).symm]
  exact S.U.ι_preimage_self

/-- The alternating Čech complex of `𝒰` with coefficients in the sheaf associated to an
`A`-module, as a functor of the module. -/
abbrev alternatingCechFunctor : ModuleCat.{u} S.A ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
  moduleAlternatingCechFunctor S.f

/-- The total complex of the alternating Čech complex of `𝒰` with coefficients in the complex
of sheaves associated to a complex of `A`-modules. -/
abbrev cechTotalFunctor :
    CochainComplex (ModuleCat.{u} S.A) ℤ ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  moduleCechTotalFunctor S.f

/-- The situation's alternating Čech functor is the alternating Čech complex of the
situation's own family of standard opens. -/
theorem alternatingCechFunctor_obj (M : ModuleCat.{u} S.A) :
    S.alternatingCechFunctor.obj M =
      Stacks.Cech.alternatingCechComplex S.basicOpen (associatedAbPresheaf M) :=
  rfl

end CechSituation

end Koszul
