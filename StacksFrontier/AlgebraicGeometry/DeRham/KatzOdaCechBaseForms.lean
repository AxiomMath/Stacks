module

public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechPullback

/-!
# The base cochain of a form as the cochain of a pulled-back global form

Let `f : X ⟶ Y` be smooth with `Y` and `S` affine, `A = Γ(Y, 𝒪_Y)`, `R = Γ(S, 𝒪_S)`, and let `U`
be a finite open covering of `X` with affine intersections. The Čech `0`-cochain of the
pull-backs to the intersections of a form `ν` of `Ω^•_{A/R}` (`baseTot`) is the cochain
`t ↦ (f^*σ)|_{U_t}` of the pull-back of the global form `σ` of `Y/S` corresponding to `ν`.

## Main results

* `AlgebraicGeometry.DeRhamKatzOdaCech.baseTot_eq_restrictTot`: the base cochain of a form is
  the cochain of the restrictions of the pulled-back global form.

## Implementation notes

The identity is obtained from the generic `Stacks.KatzOda.Cech.FormsBaseData.baseCochain_eq`,
applied to `formsBaseDataTotal`, whose fields are those of `formsDataTotal` written out literally
together with the restrictions of the pulled-back global forms; the scheme-level identifications
of forms are never compared by unfolding.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex Stacks.AlgebraicGeometry.SectionsBaseChange
open Stacks.Cech.Hypercohomology (cocycleClass toMor)

universe u

namespace AlgebraicGeometry.DeRhamKatzOdaCech

section Base

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsAffine Y] [IsAffine S]

variable [Smooth f] {ι : Type u} [Fintype ι] [DecidableEq ι] (U : ι → X.Opens)
  (haff : ∀ {m : ℕ} (t : Fin (m + 1) → ι), IsAffineOpen (inter U t))

/-- **The forms of `X/S` on the Čech intersections, with the restrictions of the pull-backs of
the global forms of `Y/S`**: the data `formsDataTotal` together with, for a form `ν` of
`Γ(Y, 𝒪_Y)` over `Γ(S, 𝒪_S)`, the restrictions to the intersections of the pull-back of the
corresponding global form of `Y/S`. -/
def formsBaseDataTotal :
    Stacks.KatzOda.Cech.FormsBaseData (U := U) (chartData f g U haff)
      (P := (f ≫ g).sectionsDeRhamComplex) where
  L a _ t := Γ(Scheme.Hom.relativeDifferentialForms (f ≫ g) (a : ℤ), inter U t)
  instAddCommGroup _ _ _ := inferInstance
  instModule a _ t := baseModule (f ≫ g) (Scheme.Hom.relativeDifferentialForms (f ≫ g) (a : ℤ))
    (inter U t)
  s a _ t := sectionsEquiv (f ≫ g) a (inter U t)
  e' a m t := formsEquiv (f ≫ g) (@haff m t) a
  e'_smul a m t r y := formsEquiv_smul (f ≫ g) (@haff m t) a r y
  e'_cres a m t j y := formsEquiv_sectionsEquiv_cres U haff (f ≫ g) a m t j y
  e'_d a m t y := formsEquiv_sectionsEquiv_d (f ≫ g) (@haff m t) a y
  base b _ t ν := (sectionsEquiv (f ≫ g) b (inter U t)).symm
    ((Scheme.Hom.relativeDifferentialForms (f ≫ g) (b : ℤ)).presheaf.map
      (homOfLE (le_top : inter U t ≤ ⊤)).op
        (pullbackSection f g b ((formsEquiv g (isAffineOpen_top Y) b).symm ν)))
  e'_base b m t ν := formsEquiv_sectionsEquiv_base f g (@haff m t) b ν

/-- The underlying forms data of `formsBaseDataTotal` is `formsDataTotal`. -/
theorem formsBaseDataTotal_toFormsData :
    (formsBaseDataTotal f g U haff).toFormsData = formsDataTotal f g U haff :=
  rfl

/-- **The base cochain of a form is the cochain of the pull-back of the global form**: the
Čech `0`-cochain of the pull-backs of `ν` to the intersections is the cochain `t ↦ (f^*σ)|_{U_t}`
of the pull-back of the global form `σ` of `Y/S` corresponding to `ν`. -/
theorem baseTot_eq_restrictTot (b : ℕ)
    (ν : ⋀[Γ(Y, ⊤)]^b ↑(CommRingCat.KaehlerDifferential (baseMap g))) :
    baseTot f g U haff b ν = restrictTot (f ≫ g) U b
      (pullbackSection f g b ((formsEquiv g (isAffineOpen_top Y) b).symm ν)) := by
  rw [baseTot, ← formsBaseDataTotal_toFormsData,
    Stacks.KatzOda.Cech.FormsBaseData.baseCochain_eq]
  rfl

end Base

end AlgebraicGeometry.DeRhamKatzOdaCech

end
