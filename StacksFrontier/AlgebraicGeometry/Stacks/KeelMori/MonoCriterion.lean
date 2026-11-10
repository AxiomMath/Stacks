module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Cardinality
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Diagonal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism

/-!
# An unramified morphism injective on geometric points of bounded size is a monomorphism

This is the first half of Stacks 0DT7, in the form needed when the geometric points are tested
only on spectra of algebraically closed fields that are small enough to lie in a big fppf site:
an unramified morphism of schemes `ρ : X ⟶ Y` whose fibre product `X ×_Y X` has size below an
uncountable cardinal `κ`, and which is injective on `Spec k`-valued points for every algebraically
closed field `k` with `Spec k` of size below `κ`, is a monomorphism. The diagonal of `ρ` is an open
immersion because `ρ` is unramified, and it is surjective because every point of `X ×_Y X` has
a geometric point over the algebraic closure of its residue field, which is small.

## Main results

* `AlgebraicGeometry.Scheme.size_Spec_algebraicClosure_residueField_lt`
* `AlgebraicGeometry.mono_of_unramified_of_injective_geometricPoints`

## References

* [Stacks Project, Tag 0DT7](https://stacks.math.columbia.edu/tag/0DT7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry

/-- The spectrum of the algebraic closure of a residue field of a scheme of size below an
uncountable cardinal `κ` has size below `κ`. -/
theorem Scheme.size_Spec_algebraicClosure_residueField_lt {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (P : Scheme.{u}) (hP : P.size < κ) (q : P) :
    (Spec (.of (AlgebraicClosure (P.residueField q)))).size < κ := by
  have hs : (Spec (P.residueField q)).size ≤ P.size :=
    Scheme.size_le_of_mono_quasiCompact (P.fromSpecResidueField q)
  rw [Scheme.size_Spec] at hs ⊢
  refine max_lt hκ ?_
  calc #(AlgebraicClosure (P.residueField q))
      ≤ max #(P.residueField q) ℵ₀ := Algebra.IsAlgebraic.cardinalMk_le_max _ _
    _ ≤ max P.size ℵ₀ := max_le_max ((le_max_right _ _).trans hs) le_rfl
    _ < κ := max_lt hP hκ

/-- **An unramified morphism injective on small geometric points is a monomorphism** (the first
half of Stacks 0DT7). -/
theorem mono_of_unramified_of_injective_geometricPoints {X Y : Scheme.{u}} (ρ : X ⟶ Y)
    [Unramified ρ] {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hP : (pullback ρ ρ).size < κ)
    (hfield : ∀ (k : Type u) [Field k] [IsAlgClosed k], (Spec (.of k)).size < κ →
      ∀ a b : Spec (.of k) ⟶ X, a ≫ ρ = b ≫ ρ → a = b) : Mono ρ := by
  have : IsOpenImmersion (pullback.diagonal ρ) := Unramified.isOpenImmersion_diagonal ρ
  have : Surjective (pullback.diagonal ρ) := by
    refine (surjective_iff (pullback.diagonal ρ)).2 fun q => ?_
    let P := pullback.diagonalObj ρ
    let k := AlgebraicClosure (P.residueField q)
    let g : Spec (.of k) ⟶ P :=
      Spec.map (CommRingCat.ofHom (algebraMap (P.residueField q) k)) ≫ P.fromSpecResidueField q
    have hlegs : g ≫ pullback.fst ρ ρ = g ≫ pullback.snd ρ ρ :=
      hfield k (Scheme.size_Spec_algebraicClosure_residueField_lt hκ P hP q) _ _
        (by simp only [Category.assoc, pullback.condition])
    have hg : g = (g ≫ pullback.fst ρ ρ) ≫ pullback.diagonal ρ := by
      apply pullback.hom_ext
      · simp
      · simpa [Category.assoc, pullback.diagonal_snd] using hlegs.symm
    refine ⟨(g ≫ pullback.fst ρ ρ) default, ?_⟩
    change ((g ≫ pullback.fst ρ ρ) ≫ pullback.diagonal ρ) default = q
    rw [← hg, Scheme.Hom.comp_apply]
    exact P.fromSpecResidueField_apply q _
  exact (pullback.isIso_diagonal_iff ρ).1
    ((isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, inferInstance⟩)

end AlgebraicGeometry

end
