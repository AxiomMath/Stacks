module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalModelRescale
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalModelZeroScheme
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.Branches
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorTrivialization

/-!
# The scheme of Tag 0F97 is a local-model bundle

Let `Y` be a scheme, let `L₁` and `L₂` be invertible `𝒪_Y`-modules and let `s` be a global
section of `L₁ ⊗ L₂`. The scheme `p : L ⟶ Y` of [Stacks, Tag 0F97] is the zero scheme of
`z₁ ⊗ z₂ - q^*s` inside the fibre product `T = Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1})`. The tag's own
proof reads it, over an affine open `V = Spec B` of `Y` trivializing both modules, as

  `p^{-1}V = Spec B[z₁, z₂]/(z₁z₂ - f)`,

the local model `Stacks.AffineBundle.LocalModel` of the function `f` cutting out `D = Z(s)` on
`V`. This file performs exactly that reduction: it isolates the chart data the reading needs as
`Stacks.Chow.TensorZeroScheme.HasLocalModelChart` and proves that a construction admitting such
charts has `Stacks.AffineBundle.IsLocalModelBundle` for its structure morphism — whence, by the
three transfer theorems of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalModelBundle`, the flatness and
relative-dimension-one halves of the tag's condition (2).

## Main definitions

* `Stacks.Chow.TensorZeroScheme.HasLocalModelChart`: **the chart data of the tag's own proof** —
  at every point of `Y` an affine open `V` over which the ambient space `T` has affine inverse
  image, the two pulled-back modules are trivialized, the ring of sections of `T` there is a
  polynomial ring in two variables over `Γ(Y, V)`, the two fibre coordinates generate the same
  ideals as the two variables, and the pullback of `s` has a local equation coming from `V`.

## Main results

* `Stacks.Chow.TensorZeroScheme.tensorTrivialization_equation`: **the local equation of
  `z₁ ⊗ z₂ - q^*s`** on such a chart is `h₀h₁ - f`, the product of the local equations of the two
  fibre coordinates minus the pullback of the local equation of `s`.
* `Stacks.Chow.TensorZeroScheme.isLocalModelBundle_proj_of_hasLocalModelChart`: **the structure
  morphism `p` of the scheme of Tag 0F97 is a local-model bundle** as soon as the construction
  admits such charts. It does: the hypothesis is discharged by
  `Stacks.Chow.TensorZeroScheme.hasLocalModelChart` in
  `StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.FlatRelativeDimension`, which is where
  condition (2) is concluded.

## Implementation notes

The chart is stated with `AlgebraicGeometry.Scheme.Hom.appLE` for the comorphism of `q` on the
pair `(V, q^{-1}V)`, which is the spelling
`Stacks.AffineBundle.isLocalModelBundle_zeroScheme_of_charts` consumes and the one
`AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec` is stated at.

The two fibre coordinates are constrained only through the *ideals* they generate, not through
their values: the trivializations of the two pulled-back modules on `q^{-1}V` are chosen along
with the chart, and a different choice rescales each local equation by a unit. That is exactly the
slack `Stacks.AffineBundle.localModelEquivOfCoordSpanEq` absorbs, so no normalization of the two
coordinates is needed anywhere.

The local equation of the equation is computed by linearity from the two local equations of the
fibre coordinates, through `Stacks.Divisors.tensorTrivialization`, whose defining property
`Stacks.Divisors.tensorTrivialization_map_tensorSection` is that the local equation of a product
of two sections is the product of their local equations.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.Divisors (tensorModules tensorSection tensorTrivialization)
open Stacks.PullbackTensorIso (pullbackTensorSection)

universe u

namespace Stacks.Chow.TensorZeroScheme

variable (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [hL₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [hL₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(tensorModules L₁ L₂, ⊤))

/-- Abbreviation for the ring of sections of the ambient space over the inverse image of an open
of the base. -/
local notation3 "Γq(" Y ", " L₁ ", " L₂ ", " V ")" =>
  Γ(totalSpace Y L₁ L₂, totalProj Y L₁ L₂ ⁻¹ᵁ V)

include hL₁ hL₂ in
/-- **The local equation of the equation `z₁ ⊗ z₂ - q^*s`** on a chart over an affine open `V` of
the base: the product of the local equations of the two fibre coordinates, minus the local
equation of `q^*s`. This is pure linearity of a trivialization together with the defining property
of `Stacks.Divisors.tensorTrivialization`. -/
theorem tensorTrivialization_equation {V : Y.Opens}
    (hW : IsAffineOpen (totalProj Y L₁ L₂ ⁻¹ᵁ V))
    (e₁ : Γ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁,
        totalProj Y L₁ L₂ ⁻¹ᵁ V) ≃ₗ[Γq(Y, L₁, L₂, V)] Γq(Y, L₁, L₂, V))
    (e₂ : Γ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂,
        totalProj Y L₁ L₂ ⁻¹ᵁ V) ≃ₗ[Γq(Y, L₁, L₂, V)] Γq(Y, L₁, L₂, V)) :
    tensorTrivialization ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
        ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂) hW e₁ e₂
        ((tensorModules ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
            ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂)).presheaf.map
          (homOfLE le_top).op (equation Y L₁ L₂ s)) =
      e₁ (((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁).presheaf.map
            (homOfLE le_top).op (coord₁ Y L₁ L₂)) *
          e₂ (((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂).presheaf.map
            (homOfLE le_top).op (coord₂ Y L₁ L₂)) -
        tensorTrivialization ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
          ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂) hW e₁ e₂
          ((tensorModules ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
              ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂)).presheaf.map
            (homOfLE le_top).op
            (pullbackTensorSection (totalProj Y L₁ L₂) L₁ L₂ s)) := by
  have hprod : tensorTrivialization ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
      ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂) hW e₁ e₂
      ((tensorModules ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
          ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂)).presheaf.map
        (homOfLE le_top).op (coordProduct Y L₁ L₂)) =
      e₁ (((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁).presheaf.map
            (homOfLE le_top).op (coord₁ Y L₁ L₂)) *
        e₂ (((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂).presheaf.map
            (homOfLE le_top).op (coord₂ Y L₁ L₂)) :=
    Stacks.Divisors.tensorTrivialization_map_tensorSection
      ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
      ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂)
      ⟨totalProj Y L₁ L₂ ⁻¹ᵁ V, hW⟩ e₁ e₂ (coord₁ Y L₁ L₂) (coord₂ Y L₁ L₂)
  rw [equation, map_sub, map_sub, hprod]

include hL₁ hL₂ in
/-- **The chart data of the proof of [Stacks, Tag 0F97].** At every point of `Y` there is an
affine open `V` containing it such that

* the inverse image of `V` in the ambient space `T = Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1})` is affine;
* the two pulled-back modules `q^*L₁` and `q^*L₂` are trivialized there, by `e₁` and `e₂`;
* `Γ(T, q^{-1}V)` is a polynomial ring in two variables over `Γ(Y, V)`, by `χ`, compatibly with
  the comorphism of `q`;
* the local equations of the two fibre coordinates generate, in that polynomial ring, the ideals
  of the two variables; and
* the pullback of `s` has, on `q^{-1}V`, a local equation pulled back from a function `f` on `V`.

This is what makes `p^{-1}V` the local model `Γ(Y, V)[z₁, z₂]/(z₁z₂ - f)`. -/
def HasLocalModelChart : Prop :=
  ∀ y : Y, ∃ (V : Y.Opens) (_hV : IsAffineOpen V) (_ : y ∈ V)
    (hW : IsAffineOpen (totalProj Y L₁ L₂ ⁻¹ᵁ V))
    (e₁ : Γ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁,
        totalProj Y L₁ L₂ ⁻¹ᵁ V) ≃ₗ[Γq(Y, L₁, L₂, V)] Γq(Y, L₁, L₂, V))
    (e₂ : Γ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂,
        totalProj Y L₁ L₂ ⁻¹ᵁ V) ≃ₗ[Γq(Y, L₁, L₂, V)] Γq(Y, L₁, L₂, V))
    (χ : Γq(Y, L₁, L₂, V) ≃+* MvPolynomial (Fin 2) Γ(Y, V)) (f : Γ(Y, V)),
    (∀ c : Γ(Y, V),
        χ (((totalProj Y L₁ L₂).appLE V (totalProj Y L₁ L₂ ⁻¹ᵁ V) le_rfl).hom c) =
          MvPolynomial.C c) ∧
      tensorTrivialization ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
          ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂) hW e₁ e₂
          ((tensorModules ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
              ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂)).presheaf.map
            (homOfLE le_top).op (pullbackTensorSection (totalProj Y L₁ L₂) L₁ L₂ s)) =
        ((totalProj Y L₁ L₂).appLE V (totalProj Y L₁ L₂ ⁻¹ᵁ V) le_rfl).hom f ∧
      Ideal.span {χ (e₁ (((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁).presheaf.map
            (homOfLE le_top).op (coord₁ Y L₁ L₂)))} =
        Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) Γ(Y, V))} ∧
      Ideal.span {χ (e₂ (((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂).presheaf.map
            (homOfLE le_top).op (coord₂ Y L₁ L₂)))} =
        Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) Γ(Y, V))}

include hL₁ hL₂ in
/-- **The structure morphism `p` of the scheme of [Stacks, Tag 0F97] is a local-model bundle**,
given the chart data of the tag's own proof. With
`Stacks.AffineBundle.flat_of_isLocalModelBundle`,
`locallyOfFiniteType_of_isLocalModelBundle` and `relativeDimension_of_isLocalModelBundle` this is
the flatness and relative-dimension halves of the tag's condition (2). -/
theorem isLocalModelBundle_proj_of_hasLocalModelChart
    (hch : HasLocalModelChart Y L₁ L₂ s) :
    Stacks.AffineBundle.IsLocalModelBundle (proj Y L₁ L₂ s) := by
  refine Stacks.AffineBundle.isLocalModelBundle_zeroScheme_of_charts (totalProj Y L₁ L₂)
    (tensorModules ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
      ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂)) (equation Y L₁ L₂ s) fun y ↦ ?_
  obtain ⟨V, hV, hyV, hW, e₁, e₂, χ, f, hχC, hfeq, hsp₀, hsp₁⟩ := hch y
  -- the local equation of the equation, and its image in the polynomial ring
  set a := tensorTrivialization ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
    ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂) hW e₁ e₂
    ((tensorModules ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
        ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂)).presheaf.map
      (homOfLE le_top).op (equation Y L₁ L₂ s)) with ha
  set h₀ := e₁ (((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁).presheaf.map
    (homOfLE le_top).op (coord₁ Y L₁ L₂)) with hh₀
  set h₁ := e₂ (((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂).presheaf.map
    (homOfLE le_top).op (coord₂ Y L₁ L₂)) with hh₁
  have haval : a = h₀ * h₁ -
      ((totalProj Y L₁ L₂).appLE V (totalProj Y L₁ L₂ ⁻¹ᵁ V) le_rfl).hom f := by
    rw [ha, tensorTrivialization_equation Y L₁ L₂ s hW e₁ e₂, hfeq]
  have hχa : χ a = χ h₀ * χ h₁ - MvPolynomial.C f := by
    rw [haval, map_sub, map_mul, hχC f]
  -- transport the quotient along the chart, then recognize the local model
  have hmap : Ideal.span ({χ h₀ * χ h₁ - MvPolynomial.C f} :
        Set (MvPolynomial (Fin 2) Γ(Y, V))) =
      Ideal.map (χ : Γq(Y, L₁, L₂, V) →+* MvPolynomial (Fin 2) Γ(Y, V))
        (Ideal.span ({a} : Set Γq(Y, L₁, L₂, V))) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg
      (fun x => Ideal.span ({x} : Set (MvPolynomial (Fin 2) Γ(Y, V)))) hχa.symm
  refine ⟨V, hV, hyV, hW,
    tensorTrivialization ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁)
      ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂) hW e₁ e₂, a, rfl, f,
    (Ideal.quotientEquiv (Ideal.span ({a} : Set Γq(Y, L₁, L₂, V)))
          (Ideal.span ({χ h₀ * χ h₁ - MvPolynomial.C f} :
            Set (MvPolynomial (Fin 2) Γ(Y, V)))) χ hmap).trans
      (Stacks.AffineBundle.localModelEquivOfCoordSpanEq (χ h₀) (χ h₁) hsp₀ hsp₁ f).toRingEquiv,
    fun c ↦ ?_⟩
  show (Stacks.AffineBundle.localModelEquivOfCoordSpanEq (χ h₀) (χ h₁) hsp₀ hsp₁ f)
      (Ideal.Quotient.mk _ (χ (((totalProj Y L₁ L₂).appLE V
        (totalProj Y L₁ L₂ ⁻¹ᵁ V) le_rfl).hom c))) = _
  rw [hχC c]
  exact (Stacks.AffineBundle.localModelEquivOfCoordSpanEq (χ h₀) (χ h₁) hsp₀ hsp₁ f).commutes c

end Stacks.Chow.TensorZeroScheme

end
