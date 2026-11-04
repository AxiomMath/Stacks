module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.AmbientTwoVariableChart
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.LocalModelChart
public import StacksFrontier.AlgebraicGeometry.Divisors.PullbackTensorTrivialization

/-!
# The scheme of Tag 0F97 is flat of relative dimension one over the base

Let `Y` be a scheme, let `L₁` and `L₂` be invertible `𝒪_Y`-modules and let `s` be a global
section of `L₁ ⊗_{𝒪_Y} L₂`. The scheme `p : L ⟶ Y` of [Stacks, Tag 0F97] is built in
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.Basic` as the zero scheme of
`z₁ ⊗ z₂ - q^*s` inside the fibre product `T = Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1})` of the two
line bundles of [Stacks, Tag 01M2].

This file proves the flatness and relative-dimension parts of the tag's **condition (2)**: `p` is
**flat** and of **relative dimension one**. Together with
`Stacks.Chow.TensorZeroScheme.locallyOfFiniteType_proj` and `quasiCompact_proj`, which are the
finite-type part, that is all of condition (2).

Over an affine open `V = Spec B` of `Y` trivializing both modules the ambient space is the
two-variable polynomial ring, `Γ(T, q^{-1}V) = B[z₁, z₂]`, and the equation becomes `z₁z₂ - f` for
`f` the local equation of `s`; so

  `p^{-1}V = Spec B[z₁, z₂]/(z₁z₂ - f)`,

the local model `Stacks.AffineBundle.LocalModel` of `f`.

## Main results

* `Stacks.Chow.TensorZeroScheme.hasLocalModelChart`: **the construction has local-model charts**
  at every point of `Y`.
* `Stacks.Chow.TensorZeroScheme.isLocalModelBundle_proj`: **`p` is a local-model bundle.**
* `Stacks.Chow.TensorZeroScheme.flat_proj`: **Tag 0F97(2), flatness** — `p` is flat.
* `Stacks.Chow.TensorZeroScheme.relativeDimension_proj`: **Tag 0F97(2), relative dimension** —
  `p` has relative dimension one.

## Implementation notes

The two trivializations of `q^*L₁` and `q^*L₂` on `q^{-1}V` are the pullbacks of
trivializations of `L₁` and `L₂` on `V`, so that the local equation of `q^*s` is the pullback of
a function on `V` (`Stacks.Divisors.exists_pullbackTensorTrivialization`).

Relative dimension is stated under the `letI` supplying
`Stacks.Chow.TensorZeroScheme.locallyOfFiniteType_proj`, which
`AlgebraicGeometry.RelativeDimension` takes as an argument of its definition;
`LocallyOfFiniteType` is `Prop`-valued, so the choice of instance does not affect the statement.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.Divisors (tensorModules tensorTrivialization)
open Stacks.PullbackTensorIso (pullbackTensorSection)

universe u

namespace Stacks.Chow.TensorZeroScheme

variable (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [hL₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [hL₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(tensorModules L₁ L₂, ⊤))

include hL₁ hL₂ in
/-- **The construction of [Stacks, Tag 0F97] has local-model charts.** At every point of `Y`
there is an affine open `V` over which the ambient space has affine inverse image, the two
pulled-back modules are trivialized, `Γ(T, q^{-1}V)` is a polynomial ring in two variables over
`Γ(Y, V)`, the two fibre coordinates generate the ideals of the two variables, and `q^*s` has a
local equation pulled back from `V`. -/
theorem hasLocalModelChart : HasLocalModelChart Y L₁ L₂ s := by
  intro y
  obtain ⟨V, hyV, hW, u₁, u₂, ψ, hψC, h₀, h₁⟩ := exists_ambientTwoVariableChart Y L₁ L₂ y
  obtain ⟨e₁, e₂, hf⟩ := Stacks.Divisors.exists_pullbackTensorTrivialization
    (totalProj Y L₁ L₂) L₁ L₂ s V.2 hW u₁ u₂
  refine ⟨(V.1 : Y.Opens), V.2, hyV, hW, e₁, e₂, ψ,
    tensorTrivialization L₁ L₂ V.2 u₁ u₂
      ((tensorModules L₁ L₂).presheaf.map (homOfLE le_top).op s), fun c ↦ ?_, hf, ?_, ?_⟩
  · rw [Scheme.Hom.appLE_preimage_self]
    exact hψC c
  all_goals
    have key : ∀ (M : (totalSpace Y L₁ L₂).Modules)
        [AlgebraicGeometry.SheafOfModules.IsInvertible
          (totalSpace Y L₁ L₂).sheaf.obj (totalSpace Y L₁ L₂).ringCatSheaf.property M]
        (c : Γ(M, ⊤)) (e : Γ(M, totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens)) ≃ₗ[Γ(totalSpace Y L₁ L₂,
          totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens))] Γ(totalSpace Y L₁ L₂,
          totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens))) (g),
        (Stacks.Divisors.zeroScheme (totalSpace Y L₁ L₂) M c).ideal
          ⟨totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens), hW⟩ = Ideal.span {ψ.symm g} →
        Ideal.span {ψ (e (M.presheaf.map (homOfLE le_top).op c))} = Ideal.span {g} := by
      intro M _ c e g h
      have hA := Stacks.Divisors.zeroScheme_ideal_of_trivialization (totalSpace Y L₁ L₂) M c
        ⟨totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens), hW⟩ e _ rfl
      have hmap := congrArg (Ideal.map (ψ : _ ≃+* _).toRingHom) (hA.symm.trans h)
      rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton] at hmap
      simpa using hmap
  · exact key _ _ e₁ _ h₀
  · exact key _ _ e₂ _ h₁

include hL₁ hL₂ in
/-- **The structure morphism `p : L ⟶ Y` of [Stacks, Tag 0F97] is a local-model bundle**: over an
affine open of `Y` trivializing both modules it is `Spec(B[z₁, z₂]/(z₁z₂ - f)) ⟶ Spec B`. -/
theorem isLocalModelBundle_proj :
    Stacks.AffineBundle.IsLocalModelBundle (proj Y L₁ L₂ s) :=
  isLocalModelBundle_proj_of_hasLocalModelChart Y L₁ L₂ s (hasLocalModelChart Y L₁ L₂ s)

include hL₁ hL₂ in
/-- **Stacks Project, Tag 0F97(2), the flatness clause**: the structure morphism `p : L ⟶ Y` is
flat. -/
theorem flat_proj : AlgebraicGeometry.Flat (proj Y L₁ L₂ s) :=
  Stacks.AffineBundle.flat_of_isLocalModelBundle (proj Y L₁ L₂ s)
    (isLocalModelBundle_proj Y L₁ L₂ s)

include hL₁ hL₂ in
/-- **Stacks Project, Tag 0F97(2), the relative-dimension clause**: the structure morphism
`p : L ⟶ Y` has relative dimension one. -/
theorem relativeDimension_proj :
    letI : LocallyOfFiniteType (proj Y L₁ L₂ s) := locallyOfFiniteType_proj Y L₁ L₂ s
    AlgebraicGeometry.RelativeDimension (proj Y L₁ L₂ s) 1 :=
  let : LocallyOfFiniteType (proj Y L₁ L₂ s) := locallyOfFiniteType_proj Y L₁ L₂ s
  Stacks.AffineBundle.relativeDimension_of_isLocalModelBundle (proj Y L₁ L₂ s)
    (isLocalModelBundle_proj Y L₁ L₂ s)

end Stacks.Chow.TensorZeroScheme

end
