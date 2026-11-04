module

public import StacksFrontier.Examples.Flatness.OrdinaryCone.CompletedBaseChange
public import StacksFrontier.Examples.Flatness.OrdinaryCone.Descent
public import StacksFrontier.Examples.Flatness.OrdinaryCone.NoFiniteFreeAlgebra
public import StacksFrontier.Examples.Flatness.OrdinaryCone.SegreBaseInjective
public import StacksFrontier.RingTheory.AbsolutelyIntegrallyClosed.HochsterHuneke.Flat
public import StacksFrontier.RingTheory.GradedCompletion.MvPowerSeries

/-!
# A flat algebra in characteristic two which is not a filtered colimit

Let `A = 𝔽₂[X₀, X₁, X₂]` and let `A⁺` be its absolute integral closure. Then `A⁺` is flat over
`A` (Hochster–Huneke, in dimension three), but it is the colimit of no filtered diagram of finitely
presented flat `A`-algebras. This is the positive characteristic alternative of **Stacks 0ATF**,
following Bhatt.

Let `Γ` be the Segre product over `𝔽₂` of the cone over the ordinary elliptic curve
`z³ + (y² + xy) z + x³ = 0` with `𝔽₂[s, t]`, an integral domain finite over `A`, so that `Γ`
embeds into `A⁺`. Let `k` be an algebraic closure of `𝔽₂` and `R = k⟦X₀, X₁, X₂⟧`, a henselian
local `A`-algebra. Then `R ⊗_A Γ ≅ R ⊗_{k[X₀, X₁, X₂]} Γ_k` admits no `R`-algebra map to a nonzero
finite free `R`-algebra, because of an Artin–Schreier–Witt Čech cocycle on the punctured spectrum
coming from the ordinary elliptic curve. A presentation of `A⁺` as a filtered colimit of finitely
presented flat `A`-algebras would produce such a map.

## Main results

* `Stacks.Examples.exists_charTwo_finiteType_flat_algebra_not_filteredColimit`: a finite type
  `𝔽₂`-algebra together with a flat algebra over it which is the colimit of no filtered diagram of
  finitely presented flat algebras.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct Stacks.Examples.OrdinaryCone

universe u v

namespace Stacks.Examples

/-- The characteristic two alternative of Stacks 0ATF: the absolute integral closure of
`A = 𝔽₂[X₀, X₁, X₂]`, a finite type `𝔽₂`-algebra, is a flat `A`-algebra which is the colimit of
no filtered diagram of finitely presented flat `A`-algebras. -/
theorem exists_charTwo_finiteType_flat_algebra_not_filteredColimit :
    ∃ (A : CommRingCat.{max u v}) (_ : Algebra (ZMod 2) A), Algebra.FiniteType (ZMod 2) A ∧
      ∃ B : CommAlgCat.{max u v} A, Module.Flat A B ∧
        ∀ (J : Type v) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommAlgCat.{max u v} A),
          (∀ j, Algebra.FinitePresentation A (F.obj j) ∧ Module.Flat A (F.obj j)) →
            ∀ c : Cocone F, c.pt = B → IsEmpty (IsColimit c) := by
  let k₀ : Type (max u v) := ULift.{max u v} (ZMod 2)
  let A := MvPolynomial (Fin 3) k₀
  have : Module.Finite (ZMod 2) k₀ := Module.Finite.of_finite
  have hft : Algebra.FiniteType (ZMod 2) A :=
    Algebra.FiniteType.trans (S := k₀) inferInstance inferInstance
  have hflat : Module.Flat A (absoluteIntegralClosure A) :=
    MvPolynomial.flat_absoluteIntegralClosure 2 (by norm_num)
  refine ⟨CommRingCat.of A, inferInstance, hft, CommAlgCat.of A (absoluteIntegralClosure A),
    hflat, ?_⟩
  obtain ⟨g, -⟩ := absoluteIntegralClosure.exists_injective_algHom A (segre k₀)
  have : Algebra.FinitePresentation A (segre k₀) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact isEmpty_isColimit_of_isEmpty_hom_tensor_finite_free.{u, v}
    (B := CommAlgCat.of A (absoluteIntegralClosure A)) g
    (MvPowerSeries (Fin 3) (AlgebraicClosure k₀)) fun T _ _ _ _ _ =>
      isEmpty_algHom_completedSegre k₀ (AlgebraicClosure k₀) T
        (isEmpty_algHom_tensor_segre T)

end Stacks.Examples
