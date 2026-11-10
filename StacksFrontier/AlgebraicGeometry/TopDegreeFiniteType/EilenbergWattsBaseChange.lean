module

public import Mathlib.Algebra.Module.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWatts

/-!
# Finite presentation of the value of a tensor functor at an algebra

Paragraph four of the proof of [Stacks, Tag 0EX4] — which is also the proof of
[Stacks, Tag 0EX5] — ends by reading the displayed equality

> `H ᵈ (X, F) = H ᵈ (X₀, F₀) ⊗_{R₀} R`

as a statement about `R`-modules, not merely about `R₀`-modules: what is wanted is that
`H ᵈ (X, F)` is a finitely presented module over `R`, and finite presentation over `R₀` of the
right-hand side says nothing about that. The Eilenberg-Watts comparison of
[Stacks, Tag 0EX3] (b) is only `R₀`-linear, since `R₀` is the ring of the base over which the
functor `Φ` is defined.

This file supplies the bridge, in pure module theory. The `R`-module structure on `Φ(R)` is
recovered from `Φ` itself: multiplication by `r` on `R` is an `R₀`-linear endomorphism, so `Φ`
applies to it, and the hypothesis `hsmul` below says that an `R₀`-linear identification of
`Φ(R)` with an `R`-module `N` carries `Φ(r ·)` to multiplication by `r`. That single
compatibility upgrades the Eilenberg-Watts equivalence to an `R`-linear one, and finite
presentation then transfers.

## Main results

* `Stacks.EilenbergWatts.algebraLinearEquiv`: the Eilenberg-Watts equivalence at an
  `R₀`-algebra `A`, upgraded to an `A`-linear equivalence `A ⊗_{R₀} Φ(R₀) ≃ₗ[A] N`.
* `Stacks.EilenbergWatts.finitePresentation_of_compatible_smul`: if `Φ(R₀)` is a finitely
  presented `R₀`-module then `N` is a finitely presented `A`-module.

## Implementation notes

The two hypotheses on `N` are the standard pair `Module R₀ N` and `IsScalarTower R₀ A N`: the
`R₀`-linear equivalence `e` and the `A`-action have to refer to actions that agree on the image
of `R₀`, and without the tower law they need not.

The `A`-linearity computation is the identity

> `LinearMap.toSpanSingleton R₀ A (a * a') = LinearMap.mulLeft R₀ a ∘ₗ
>   LinearMap.toSpanSingleton R₀ A a'`

together with functoriality of `Φ`, so `hsmul` is used exactly once. Additivity of the two
`A`-actions extends the pure-tensor case to all of `A ⊗_{R₀} Φ(R₀)` by
`TensorProduct.inductionOn`.

No `@[stacks]` attribute is attached: nothing here is a statement the source makes. It is the
`R`-linearity step that the source's "`= H ᵈ (X₀, F₀) ⊗_{R₀} R`" leaves implicit.

## References

* [Stacks Project, Tag 0EX5](https://stacks.math.columbia.edu/tag/0EX5)
* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory
open scoped TensorProduct

universe u

namespace Stacks.EilenbergWatts

variable {R₀ : Type u} [CommRing R₀] (F : ModuleCat.{u} R₀ ⥤ ModuleCat.{u} R₀) [F.Additive]
  [Functor.Linear R₀ F] [∀ ι : Type u, PreservesColimitsOfShape (Discrete ι) F]
  [PreservesFiniteColimits F]
  {A : Type u} [CommRing A] [Algebra R₀ A]
  {N : Type u} [AddCommGroup N] [Module A N] [Module R₀ N] [IsScalarTower R₀ A N]
  (e : F.obj (ModuleCat.of R₀ A) ≃ₗ[R₀] N)

/-- The underlying `R₀`-linear equivalence `A ⊗_{R₀} Φ(R₀) ≃ₗ[R₀] N`: the Eilenberg-Watts
comparison at `A`, read with the factors in the order in which the `A`-action sits on the left,
followed by the given identification. -/
noncomputable def algebraLinearEquivAux :
    A ⊗[R₀] (F.obj (ModuleCat.of R₀ R₀)) ≃ₗ[R₀] N :=
  (TensorProduct.comm R₀ A _).trans ((linearEquiv F (ModuleCat.of R₀ A)).trans e)

omit [Module A N] [IsScalarTower R₀ A N] in
/-- `algebraLinearEquivAux` sends `a ⊗ₜ x` to `e (Φ(r ↦ r • a) x)`. -/
@[simp] theorem algebraLinearEquivAux_tmul (a : A) (x : F.obj (ModuleCat.of R₀ R₀)) :
    algebraLinearEquivAux F e (a ⊗ₜ x) =
      e ((F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R₀ A a))).hom x) := rfl

/-- **The Eilenberg-Watts equivalence at an algebra, upgraded to an `A`-linear equivalence.**
Given an `R₀`-linear identification `e` of `Φ(A)` with an `A`-module `N` carrying `Φ(a ·)` to
multiplication by `a`, the Eilenberg-Watts comparison becomes an `A`-linear equivalence
`A ⊗_{R₀} Φ(R₀) ≃ₗ[A] N`. -/
noncomputable def algebraLinearEquiv
    (hsmul : ∀ (a : A) (y : F.obj (ModuleCat.of R₀ A)),
      e ((F.map (ModuleCat.ofHom (LinearMap.mulLeft R₀ a))).hom y) = a • e y) :
    A ⊗[R₀] (F.obj (ModuleCat.of R₀ R₀)) ≃ₗ[A] N where
  toFun := algebraLinearEquivAux F e
  map_add' := map_add _
  map_smul' := by
    intro a z
    induction z using TensorProduct.inductionOn with
    | tmul a' x =>
      have hcomp : LinearMap.toSpanSingleton R₀ A (a * a') =
          (LinearMap.mulLeft R₀ a).comp (LinearMap.toSpanSingleton R₀ A a') := by
        ext
        simp [LinearMap.toSpanSingleton_apply, Algebra.smul_def, mul_comm]
      have hsm : a • (a' ⊗ₜ[R₀] x) = (a * a') ⊗ₜ[R₀] x := rfl
      rw [hsm, algebraLinearEquivAux_tmul, hcomp]
      rw [show ModuleCat.ofHom ((LinearMap.mulLeft R₀ a).comp
            (LinearMap.toSpanSingleton R₀ A a')) =
          ModuleCat.ofHom (LinearMap.toSpanSingleton R₀ A a') ≫
            ModuleCat.ofHom (LinearMap.mulLeft R₀ a) from rfl, F.map_comp]
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, hsmul,
        algebraLinearEquivAux_tmul]
      rfl
    | add z w hz hw =>
      rw [smul_add, map_add, map_add, hz, hw, smul_add]
  invFun := (algebraLinearEquivAux F e).symm
  left_inv := (algebraLinearEquivAux F e).left_inv
  right_inv := (algebraLinearEquivAux F e).right_inv

omit [IsScalarTower R₀ A N] in
/-- **Finite presentation transfers across the Eilenberg-Watts equivalence at an algebra.** If
`Φ(R₀)` is a finitely presented `R₀`-module and `e` carries `Φ(a ·)` to multiplication by `a`,
then `N` is a finitely presented `A`-module.

This is the step the source's displayed equality `H ᵈ (X, F) = H ᵈ (X₀, F₀) ⊗_{R₀} R` is used
for. Finite presentation of the base change is Mathlib's instance for `A ⊗_{R₀} M`, and
`Module.FinitePresentation.of_equiv` moves it along the `A`-linear equivalence. -/
theorem finitePresentation_of_compatible_smul
    (hsmul : ∀ (a : A) (y : F.obj (ModuleCat.of R₀ A)),
      e ((F.map (ModuleCat.ofHom (LinearMap.mulLeft R₀ a))).hom y) = a • e y)
    (hfp : Module.FinitePresentation R₀ (F.obj (ModuleCat.of R₀ R₀))) :
    Module.FinitePresentation A N := by
  have := hfp
  have : Module.FinitePresentation A (A ⊗[R₀] (F.obj (ModuleCat.of R₀ R₀))) := inferInstance
  exact Module.FinitePresentation.of_equiv (algebraLinearEquiv F e hsmul)

end Stacks.EilenbergWatts

end
