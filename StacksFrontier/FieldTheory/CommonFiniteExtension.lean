module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.FieldTheory.SeparableClosure
import StacksCore.Tactic.StacksAttribute

/-!
# A common finite extension for a finite family of finite extensions

A finite family of finite field extensions of `K` admits a single finite extension of `K` into
which every member embeds over `K`: take the compositum, inside an algebraic closure of `K`, of
the images of the members under liftings to that closure. If every member of the family is
moreover separable over `K`, so is that compositum, each image being separable and a supremum of
separable subextensions being separable.

We also record that adjoining finitely many algebraic elements to `K` gives a finite extension
(`IntermediateField.finiteDimensional_adjoin_range_of_isAlgebraic`).
-/

public noncomputable section

add_to_stacks 09GH "for a finite set `S` of elements integral over `K`, which over a field is \
  the same as algebraic" IntermediateField.finiteDimensional_adjoin

universe u v

/-- Finitely many finite field extensions of `K` embed into a common finite extension of `K`. -/
theorem exists_finiteDimensional_algHom_forall {K : Type u} [Field K] {ι : Type v} [Finite ι]
    (F : ι → Type u) [∀ i, Field (F i)] [∀ i, Algebra K (F i)] [∀ i, Module.Finite K (F i)] :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Module.Finite K E),
      Nonempty (∀ i, F i →ₐ[K] E) := by
  let f (i : ι) : F i →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let T : IntermediateField K (AlgebraicClosure K) := ⨆ i, (f i).fieldRange
  have (i : ι) : Module.Finite K (f i).fieldRange :=
    Module.Finite.equiv (f i).equivFieldRange.toLinearEquiv
  have : Module.Finite K T := IntermediateField.finiteDimensional_iSup_of_finite
  refine ⟨T, inferInstance, inferInstance, inferInstance, ⟨fun i => ?_⟩⟩
  exact (IntermediateField.inclusion (le_iSup (fun i => (f i).fieldRange) i)).comp
    (f i).equivFieldRange.toAlgHom

/-- Finitely many finite separable field extensions of `K` embed into a common finite **separable**
extension of `K`. The compositum of the images inside an algebraic closure of `K` is separable
over `K` because each image is isomorphic over `K` to a separable extension and a supremum of
separable intermediate fields is separable. -/
theorem exists_finiteDimensional_isSeparable_algHom_forall {K : Type u} [Field K] {ι : Type v}
    [Finite ι] (F : ι → Type u) [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
    [∀ i, Module.Finite K (F i)] [∀ i, Algebra.IsSeparable K (F i)] :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Module.Finite K E)
      (_ : Algebra.IsSeparable K E), Nonempty (∀ i, F i →ₐ[K] E) := by
  let f (i : ι) : F i →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let T : IntermediateField K (AlgebraicClosure K) := ⨆ i, (f i).fieldRange
  have (i : ι) : Module.Finite K (f i).fieldRange :=
    Module.Finite.equiv (f i).equivFieldRange.toLinearEquiv
  have (i : ι) : Algebra.IsSeparable K (f i).fieldRange :=
    AlgEquiv.Algebra.isSeparable (f i).equivFieldRange
  have : Module.Finite K T := IntermediateField.finiteDimensional_iSup_of_finite
  have : Algebra.IsSeparable K T := IntermediateField.isSeparable_iSup K (AlgebraicClosure K)
  refine ⟨T, inferInstance, inferInstance, inferInstance, inferInstance, ⟨fun i => ?_⟩⟩
  exact (IntermediateField.inclusion (le_iSup (fun i => (f i).fieldRange) i)).comp
    (f i).equivFieldRange.toAlgHom

/-- Let `k` be a field and `α₁, …, αₙ` elements of an extension field `L`, each algebraic over
`k`. Then `k(α₁, …, αₙ) / k` is a finite extension. This is the field-adjoin form of the
statement; `fg_adjoin_of_finite` is the ring-adjoin version, about `k[α₁, …, αₙ]` as a finitely
generated `k`-module. -/
@[stacks 09GH "the field `k(α₁, …, αₙ)` is `IntermediateField.adjoin k (Set.range α)`"]
theorem IntermediateField.finiteDimensional_adjoin_range_of_isAlgebraic {K L : Type*} [Field K]
    [Field L] [Algebra K L] {n : ℕ} (α : Fin n → L) (hα : ∀ i, IsAlgebraic K (α i)) :
    FiniteDimensional K (IntermediateField.adjoin K (Set.range α)) :=
  IntermediateField.finiteDimensional_adjoin <| by
    rintro _ ⟨i, rfl⟩
    exact (hα i).isIntegral
