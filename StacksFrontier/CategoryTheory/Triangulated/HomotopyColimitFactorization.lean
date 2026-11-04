module

public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
import StacksCore.Tactic.StacksAttribute

/-!
# A map from a compact object into a derived colimit factors through a term

Let `D` be a pre-triangulated category with direct sums, let `F : ℕ ⥤ D` be a system of objects
and let `K` be a derived colimit of it (Definition [Stacks, Tag 090Z]). A morphism from a compact
object `A` into `K` factors as `A ⟶ F.obj n ⟶ K` for some `n`.

This is the half of [Stacks, Tag 094A] that says the canonical map
`colim Hom(A, Kₙ) ⟶ Hom(A, K)` is surjective, in the shape a cell-filtration argument consumes:
the source's statement is an isomorphism of abelian groups, and extracting a factorization from
it means going back through the colimit, which this statement does once and for all.

## Main results

* `CategoryTheory.Pretriangulated.exists_fac_obj_of_isHomotopyColimit`.

## Implementation notes

The two halves of [Stacks, Tag 094A] themselves are
`CategoryTheory.eq_zero_of_comp_eq_zero_of_isColimitCofan` and
`CategoryTheory.exists_factor_comp_of_isColimitCofan` of
`StacksFrontier/CategoryTheory/Triangulated/CompactObjects.lean`, stated there for a direct sum
presented by an arbitrary colimit cofan. They are applied here to the chosen coproduct
`∐ F.obj` and its coprojections, which `CategoryTheory.Limits.coproductIsCoproduct` exhibits as
such a cofan.

The universe `w` in which compactness is read is independent of the morphism universe of `D`, as
it is in the two halves: nothing here involves a direct sum other than the `ℕ`-indexed one of
the system.

## References

* [Stacks Project, Tag 094A](https://stacks.math.columbia.edu/tag/094A)
* [Stacks Project, Tag 090Z](https://stacks.math.columbia.edu/tag/090Z)
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Pretriangulated

open Limits Preadditive

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [HasCoproducts.{w} D]

/-- The first map of the triangle defining a derived colimit of `F`, namely `1 - fₙ` on the
`n`-th summand of `∐ F.obj`. -/
private noncomputable def oneSubTransition (F : ℕ ⥤ D) : ∐ F.obj ⟶ ∐ F.obj :=
  Sigma.desc fun n ↦
    Sigma.ι F.obj n - F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1)

omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
private lemma ι_comp_oneSubTransition (F : ℕ ⥤ D) (n : ℕ) :
    Sigma.ι F.obj n ≫ oneSubTransition F =
      Sigma.ι F.obj n - F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1) :=
  Sigma.ι_desc _ _

/-- **A map from a compact object into a derived colimit factors through a term of the system**:
the surjectivity half of [Stacks, Tag 094A]. If `K = hocolim Kₙ` for the system `F : ℕ ⥤ D` and
`A` is compact, then every `ζ : A ⟶ K` is of the form `ρ ≫ σ` for some `n`, some
`ρ : A ⟶ F.obj n` and some `σ : F.obj n ⟶ K`.

The third map `q : K ⟶ (∐ F.obj)⟦1⟧` of the defining triangle annihilates `ζ`, because `1 - fₙ`
is injective on the morphisms out of the compact object `A⟦-1⟧`; so `ζ` factors through
`p : ∐ F.obj ⟶ K`, and `A` being compact that factorization goes through a single coprojection
after composition with `p`. -/
theorem exists_fac_obj_of_isHomotopyColimit {F : ℕ ⥤ D} {K : D} (hK : IsHomotopyColimit F K)
    (A : D) [IsCompactObject.{w} A] (ζ : A ⟶ K) :
    ∃ (n : ℕ) (ρ : A ⟶ F.obj n) (σ : F.obj n ⟶ K), ζ = ρ ≫ σ := by
  have : IsCompactObject.{w} (A⟦(-1 : ℤ)⟧) := isCompactObject_shift inferInstance (-1)
  obtain ⟨p, q, hT⟩ := hK
  have hT : Triangle.mk (oneSubTransition F) p q ∈ distTriang D := hT
  have h₁₂ : oneSubTransition F ≫ p = 0 := comp_distTriang_mor_zero₁₂ _ hT
  have h₃₁ : q ≫ (oneSubTransition F)⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
  have hp : ∀ n : ℕ, Sigma.ι F.obj n ≫ p
      = F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1) ≫ p := by
    intro n
    have h : (Sigma.ι F.obj n ≫ oneSubTransition F) ≫ p = 0 := by
      rw [Category.assoc, h₁₂, comp_zero]
    rwa [ι_comp_oneSubTransition, sub_comp, sub_eq_zero, Category.assoc] at h
  have hζq : ζ ≫ q = 0 := by
    refine eq_zero_of_comp_shift_map_eq_zero (b := oneSubTransition F) (fun g hg ↦
      eq_zero_of_comp_eq_zero_of_isColimitCofan F.obj (fun n ↦ F.map (homOfLE (Nat.le_succ n)))
        (Sigma.ι F.obj) (coproductIsCoproduct F.obj) (ι_comp_oneSubTransition F) _ g hg) _ ?_
    rw [Category.assoc, h₃₁, comp_zero]
  obtain ⟨ψ, hψ⟩ := Triangle.coyoneda_exact₃ _ hT ζ hζq
  obtain ⟨N, ρ, hρ⟩ := exists_factor_comp_of_isColimitCofan F.obj
    (fun n ↦ F.map (homOfLE (Nat.le_succ n))) (Sigma.ι F.obj) (coproductIsCoproduct F.obj) p hp
    A ψ
  refine ⟨N, ρ, Sigma.ι F.obj N ≫ p, ?_⟩
  rw [hψ]
  exact hρ

end CategoryTheory.Pretriangulated

end
