/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.InverseSequence.UniformInverses
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers
public import StacksFrontier.RingTheory.LocalCohomology.StrictProRepresentatives
public import StacksFrontier.RingTheory.Module.AdicSystem.UniformDerivedReduction

/-!
# The natural map from system (2) to system (1) of Stacks 0GA5 is a strict pro-isomorphism

Let `I` be an ideal of a Noetherian ring `A` and `M` a bounded complex of finite `A`-modules.
Stacks 0GA5 asserts that the natural map of More on Algebra, Lemma 15.102.3 ([Stacks, Tag 0G9M])
from the system (2) `M ⊗ᴸ_A A/Iⁿ` to the system (1) `M/IⁿM` is a *strict* pro-isomorphism, that
is, an isomorphism in the strict pro-category of `D(A)`. Here (2) is computed by the reductions
`P/IⁿP` of a bounded above resolution `P ⟶ M` by finite flat modules.

## Main results

* `Stacks.LocalCohomology.isIso_proHom_of_hasUniformInverses`: a morphism of inverse sequences
  with uniform inverses is an isomorphism of the strict pro-category.
* `Stacks.LocalCohomology.UniformityII.isIso_proHom_derivedReductionComparison`: **the map from
  (2) to (1) is an isomorphism of the strict pro-category of `D(A)`.**
* `Stacks.LocalCohomology.UniformityII.derivedReductionComparison_hasEventualInverses`: in
  particular the systems (1) and (2) are pro-isomorphic.

## References

* [Stacks Project, Tag 0GA5](https://stacks.math.columbia.edu/tag/0GA5)
* [Stacks Project, Tag 0G9M](https://stacks.math.columbia.edu/tag/0G9M)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.InverseSequence

namespace Stacks.LocalCohomology

universe v u

variable {C : Type u} [Category.{v} C]

/-- Uniform inverses are in particular eventual inverses: a strict pro-isomorphism is a
pro-isomorphism. -/
theorem _root_.CategoryTheory.InverseSequence.HasUniformInverses.hasEventualInverses
    {X Y : Functor ℕᵒᵖ C} {φ : NatTrans X Y} (hφ : HasUniformInverses φ) :
    NoetherianAdicCompletion.HasEventualInverses φ := by
  obtain ⟨c, hc⟩ := hφ
  intro n
  obtain ⟨s, h, hs₁, hs₂⟩ := hc n (n + c) le_rfl
  exact ⟨n + c, h, s, hs₁, hs₂⟩

/-- **Uniform inverses give an isomorphism of the strict pro-category.** If `φ : X ⟶ Y` has
uniform inverses, then the strict pro-morphism it represents (with shift `0`) is an
isomorphism. -/
theorem isIso_proHom_of_hasUniformInverses {X Y : Functor ℕᵒᵖ C} (φ : NatTrans X Y)
    (hφ : HasUniformInverses φ) : IsIso (proHom (⟨0, φ⟩ : StrictProHomRep X Y)) := by
  obtain ⟨c, hc⟩ := hφ
  choose s hle hs₁ hs₂ using hc
  let v : ∀ n : ℕ, Y.obj (op (n + c)) ⟶ X.obj (op n) := fun n ↦ s n (n + c) le_rfl
  have hv₁ : ∀ n, φ.app (op (n + c)) ≫ v n = tr X (Nat.le_add_right n c) := fun n ↦ hs₁ _ _ _
  have hv₂ : ∀ n, v n ≫ φ.app (op n) = tr Y (Nat.le_add_right n c) := fun n ↦ hs₂ _ _ _
  have key : ∀ {n n' : ℕ} (h : n ≤ n'),
      tr Y (show n + c ≤ n' + 2 * c by omega) ≫ v n =
        tr Y (show n' + c ≤ n' + 2 * c by omega) ≫ v n' ≫ tr X h := by
    intro n n' h
    let w := s (n' + c) (n' + 2 * c) (by omega)
    have a₁ : tr Y (show n + c ≤ n' + 2 * c by omega) =
        tr Y (show n' + c ≤ n' + 2 * c by omega) ≫ tr Y (show n + c ≤ n' + c by omega) :=
      (tr_comp _ _ _).symm
    have a₂ : tr Y (show n' + c ≤ n' + 2 * c by omega) = w ≫ φ.app (op (n' + c)) :=
      (hs₂ _ _ _).symm
    have hL : tr Y (show n + c ≤ n' + 2 * c by omega) ≫ v n =
        w ≫ tr X (show n ≤ n' + c by omega) := by
      rw [a₁, a₂, Category.assoc, Category.assoc, ← tr_naturality_assoc, hv₁, tr_comp]
    have hR : tr Y (show n' + c ≤ n' + 2 * c by omega) ≫ v n' ≫ tr X h =
        w ≫ tr X (show n ≤ n' + c by omega) := by
      rw [a₂, Category.assoc, reassoc_of% (hv₁ n'), tr_comp]
    rw [hL, hR]
  let ψ : NatTrans (shiftedInverseSequence Y (2 * c)) X :=
    { app := fun n ↦ tr Y (show n.unop + c ≤ n.unop + 2 * c by omega) ≫ v n.unop
      naturality := by
        intro n n' f
        have h : n'.unop ≤ n.unop := leOfHom f.unop
        dsimp [shiftedInverseSequence, inverseSequenceShift]
        rw [show f = (homOfLE h).op from Subsingleton.elim _ _]
        show tr Y (show n'.unop + 2 * c ≤ n.unop + 2 * c by omega) ≫ _ = _ ≫ tr X h
        rw [← Category.assoc, tr_comp, key h, Category.assoc] }
  have hψ₁ : ∀ n : ℕ, φ.app (op (n + 2 * c)) ≫ ψ.app (op n) =
      X.map (opHomOfLE (Nat.le_add_right n (2 * c))) := by
    intro n
    show φ.app (op (n + 2 * c)) ≫ tr Y _ ≫ v n = tr X _
    rw [← tr_naturality_assoc, hv₁, tr_comp]
  have hψ₂ : ∀ n : ℕ, ψ.app (op n) ≫ φ.app (op n) =
      Y.map (opHomOfLE (Nat.le_add_right n (2 * c))) := by
    intro n
    show (tr Y _ ≫ v n) ≫ φ.app (op n) = tr Y _
    rw [Category.assoc, hv₂, tr_comp]
  let f : StrictProHomRep X Y := ⟨0, φ⟩
  let g : StrictProHomRep Y X := ⟨2 * c, ψ⟩
  refine ⟨proHom g, ?_, ?_⟩
  · rw [proHom_comp, ← proHom_id X]
    refine proHom_eq_of_equivalent ⟨2 * c, 0, Nat.le_refl _, Nat.zero_le _, fun n _ ↦ ?_⟩
    dsimp [StrictProHomRep.comp, StrictProHomRep.id, shiftedInverseSequenceTransition,
      shiftedInverseSequence, inverseSequenceShift, f, g]
    rw [hψ₁, ← X.map_comp, ← X.map_comp, Category.comp_id]
    exact inverseSequence_map_eq X _ _
  · rw [proHom_comp, ← proHom_id Y]
    refine proHom_eq_of_equivalent
      ⟨2 * c, 0, Nat.le_of_eq (Nat.zero_add _), Nat.zero_le _, fun n _ ↦ ?_⟩
    dsimp [StrictProHomRep.comp, StrictProHomRep.id, shiftedInverseSequenceTransition,
      shiftedInverseSequence, inverseSequenceShift, f, g]
    rw [hψ₂, ← Y.map_comp, ← Y.map_comp, Category.comp_id]
    exact inverseSequence_map_eq Y _ _

namespace UniformityII

open Stacks.AdicSystem.DerivedReductionProIso

attribute [local instance 2000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A]

/-- **The natural map from system (2) to system (1) is a strict pro-isomorphism.** Let `I` be an
ideal of a Noetherian ring `A`, let `M` be a bounded complex of finite `A`-modules and
`p : P ⟶ M` a quasi-isomorphism from a bounded above complex of finite flat modules, so that
`P/IⁿP` computes `M ⊗ᴸ_A A/Iⁿ`. Then the natural map from the inverse system `n ↦ P/I^(n+1)P` to
the inverse system `n ↦ M/I^(n+1)M` in `D(A)` is an isomorphism in the strict pro-category of
`D(A)`. -/
@[stacks 0GA5 "the natural map from (2) to (1) is a strict pro-isomorphism"]
theorem isIso_proHom_derivedReductionComparison [IsNoetherianRing A] (I : Ideal A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hMbounded : ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b)
    (hMfinite : ∀ i : ℤ, Module.Finite A (M.X i))
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) (hPbounded : ∃ b : ℤ, P.IsStrictlyLE b)
    (hPfinite : ∀ i : ℤ, Module.Finite A (P.X i) ∧ Module.Flat A (P.X i))
    (hp : IsIso (DerivedCategory.Q.map p)) :
    IsIso (proHom (⟨0, Functor.whiskerRight (reductionComplexSystemMap I p) DerivedCategory.Q⟩ :
      StrictProHomRep (reductionComplexSystem I P ⋙ DerivedCategory.Q)
        (reductionComplexSystem I M ⋙ DerivedCategory.Q))) :=
  isIso_proHom_of_hasUniformInverses _
    (derivedReduction_hasUniformInverses I M hMbounded hMfinite p hPbounded hPfinite hp)

/-- **The systems (1) and (2) are pro-isomorphic.** Let `I` be an ideal of a Noetherian ring `A`,
let `M` be a bounded complex of finite `A`-modules and `p : P ⟶ M` a quasi-isomorphism from a
bounded above complex of finite flat modules, so that `P/IⁿP` computes `M ⊗ᴸ_A A/Iⁿ`. Then the
natural map from the system (2) `n ↦ P/I^(n+1)P` to the system (1) `n ↦ M/I^(n+1)M` in `D(A)` is
a pro-isomorphism. -/
@[stacks 0GA5 "the systems (1) and (2) are pro-isomorphic, via Lemma 15.102.3"]
theorem derivedReductionComparison_hasEventualInverses [IsNoetherianRing A] (I : Ideal A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hMbounded : ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b)
    (hMfinite : ∀ i : ℤ, Module.Finite A (M.X i))
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) (hPbounded : ∃ b : ℤ, P.IsStrictlyLE b)
    (hPfinite : ∀ i : ℤ, Module.Finite A (P.X i) ∧ Module.Flat A (P.X i))
    (hp : IsIso (DerivedCategory.Q.map p)) :
    NoetherianAdicCompletion.HasEventualInverses
      (Functor.whiskerRight (reductionComplexSystemMap I p) DerivedCategory.Q) :=
  (derivedReduction_hasUniformInverses I M hMbounded hMfinite p hPbounded hPfinite
    hp).hasEventualInverses

end UniformityII

end Stacks.LocalCohomology

end
