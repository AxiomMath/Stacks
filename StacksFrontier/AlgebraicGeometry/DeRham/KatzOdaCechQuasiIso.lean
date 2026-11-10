module

public import StacksFrontier.RingTheory.Kaehler.KatzOdaCechMul
public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechFiltration
public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechKFlat
public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechClasses

/-!
# The cup product with the Čech cocycles of a family of classes is a quasi-isomorphism

Let `f : X ⟶ Y` be a smooth morphism and `g : Y ⟶ S` a morphism with `Y` and `S` affine,
`A = Γ(Y, 𝒪_Y)`, `R = Γ(S, 𝒪_S)`, and let `U` be a finite family of opens of `X` with affine Čech
intersections. Given cocycles `x_i` of degree `n_i` of the total Čech complex
`K = Tot(Č(U, Ω^•_{X/S}))`, the map

`x̃ : ⨁_i Ω^•_{A/R}[-n_i] ⟶ K`, `ω ↦ x_i ∧ ω` on the `i`-th summand,

is a quasi-isomorphism as soon as its zeroth graded piece, the map
`⨁_i A[-n_i] ⟶ Tot(Č(U, Ω^•_{X/Y}))` sending the `i`-th basis vector to the image `x̄_i` of `x_i`,
is one. This is the core of the proof of [Stacks, Tag 0FUM]: the filtrations by the degree of the
forms from the base, the identification of the graded pieces as tensor products
(`Stacks.KatzOda.Cech.quasiIso_cupHom`), and the K-flatness of `Tot(Č(U, Ω^•_{X/Y}))`
([Stacks, Tag 0FMQ], `AlgebraicGeometry.DeRhamKatzOdaCech.kFlat_cechTot_sectionsDeRhamComplex`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex

universe u

namespace AlgebraicGeometry.DeRhamKatzOdaCech

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsAffine Y] [IsAffine S] [Smooth f]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (U : ι → X.Opens)
  (haff : ∀ {m : ℕ} (t : Fin (m + 1) → ι), IsAffineOpen (inter U t))
  {I : Type u} [Fintype I] (n : I → ℕ)
  (x : ∀ i, TotX U (f ≫ g).sectionsDeRhamComplex (n i))
  (hx : ∀ i, totDTo U (f ≫ g).sectionsDeRhamComplex (n i) (n i + 1) rfl (x i) = 0)

/-- The map `x̃ : ⨁_i Ω^•_{A/R}[-n_i] ⟶ Tot(Č(U, Ω^•_{X/S}))`, `ω ↦ x_i ∧ ω`. -/
abbrev cupHomScheme :=
  Stacks.KatzOda.Cech.cupHom (chartData f g U haff) (formsDataTotal f g U haff) n x hx

/-- The map `⨁_i A[-n_i] ⟶ Tot(Č(U, Ω^•_{X/Y}))` sending the `i`-th basis vector to the image of
`x_i`. -/
abbrev unitHomScheme :=
  Stacks.KatzOda.Cech.unitHom (chartData f g U haff) (formsDataTotal f g U haff) n x hx
    (formsDataRel f g U haff)

/-- **`x̃` is a quasi-isomorphism when its zeroth graded piece is.** -/
theorem quasiIso_cupHomScheme [QuasiIso (unitHomScheme f g U haff n x hx)] :
    QuasiIso (cupHomScheme f g U haff n x hx) :=
  Stacks.KatzOda.Cech.quasiIso_cupHom _ _ n x hx (formsDataRel f g U haff)
    (Stacks.KatzOda.ShiftedSum.kFlat_unitComplex _)
    (kFlat_cechTot_sectionsDeRhamComplex f U haff)

/-- **The de Rham cohomology of `X/S` in terms of the base**, before identifying the map with
cup products: when the zeroth graded piece of `x̃` is a quasi-isomorphism, for a covering of a
scheme with affine diagonal by affine opens with affine Čech intersections, the map

`H^N(⨁_i Ω^•_{A/R}[-n_i]) ⟶ H^N_{dR}(X/S)`, `[ω] ↦ [x̃(ω)]`,

is bijective in every degree. -/
theorem bijective_classMap_cupHomScheme [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hU : ⊤ = ⨆ i, U i) [QuasiIso (unitHomScheme f g U haff n x hx)] (N : ℤ) :
    Function.Bijective (HomologicalComplex.homologyMap (cupHomScheme f g U haff n x hx) N ≫
      classMap (f ≫ g) U hU N).hom := by
  have := quasiIso_cupHomScheme f g U haff n x hx
  have h1 := ConcreteCategory.bijective_of_isIso
    (HomologicalComplex.homologyMap (cupHomScheme f g U haff n x hx) N)
  have hUaff (i : ι) : IsAffineOpen (U i) := by
    have h := haff (m := 0) fun _ => i
    rwa [inter_eq_single] at h
  exact (bijective_classMap (f ≫ g) U hU hUaff N).comp h1

end AlgebraicGeometry.DeRhamKatzOdaCech

end
