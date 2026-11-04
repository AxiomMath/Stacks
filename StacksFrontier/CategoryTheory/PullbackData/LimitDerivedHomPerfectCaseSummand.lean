module

public import Mathlib.CategoryTheory.Retract
public import StacksFrontier.CategoryTheory.PullbackData.LimitSystemColimShift

/-!
# The colimit statement of a system over a base is closed under direct summands

Let `P` be a coherent pullback pseudofunctor datum and let `S` be a directed system over a base
`b` with a cone, a `CategoryTheory.PullbackData.LimitSystem`.  For objects `X`, `Y` of `D b` the
statement that `Hom(k^*X, k^*Y)` is the filtered colimit of the `Hom(k_j^*X, k_j^*Y)` is
`CategoryTheory.PullbackData.LimitSystem.IsColim`, and its version at every shift of the first
argument is `CategoryTheory.PullbackData.LimitSystem.ShiftedIsColim`.

`StacksFrontier/CategoryTheory/PullbackData/LimitSystemColimShift.lean` proves that the class of
first arguments satisfying `ShiftedIsColim` is closed under isomorphism, shift, the vertices of a
distinguished triangle, and hence binary biproducts.  This file adds the remaining closure
property a dévissage needs: closure under **direct summands**.  It is what lets a dévissage over
an affine base terminate, because over a ring a finite projective module is in general only a
summand of a finite free one and not itself free, so a class closed only under finite biproducts
never reaches it.

The proof is elementary and needs neither an additive nor a triangulated structure.  If `X` is a
retract of `C`, with `i : X ⟶ C` and `r : C ⟶ X` such that `i ≫ r = 𝟙 X`, then for every
morphism `f` of the base the pullback functor `P.pull f` carries this to a retract of
`(P.pull f).obj C` onto `(P.pull f).obj X`, so precomposition exhibits the hom-set
`Hom((P.pull f).obj X, (P.pull f).obj Y)` as a retract of
`Hom((P.pull f).obj C, (P.pull f).obj Y)`, naturally in `f`.  Each of the three clauses of
`Stacks.IsStagesColimit` transports along a retraction of systems: an element of the vertex is
pushed into the `C`-system by `r`, lifted to a stage there, and pulled back by `i`; and two
elements of a stage that agree in the vertex are pushed by `r`, equalised at a later stage, and
pulled back by `i`.

## Main results

* `CategoryTheory.PullbackData.LimitSystem.IsColim.of_retract`: the colimit statement passes from
  `C` to any retract of `C`.
* `CategoryTheory.PullbackData.LimitSystem.IsColim.of_biprod_left`,
  `CategoryTheory.PullbackData.LimitSystem.IsColim.of_biprod_right`: the two summands of a binary
  biproduct.
* `CategoryTheory.PullbackData.LimitSystem.ShiftedIsColim.of_retract`,
  `CategoryTheory.PullbackData.LimitSystem.ShiftedIsColim.of_biprod_left`,
  `CategoryTheory.PullbackData.LimitSystem.ShiftedIsColim.of_biprod_right`,
  `CategoryTheory.PullbackData.LimitSystem.ShiftedIsColim.of_biprod_iso`: the same statements for
  the version quantified over the shifts of the first argument, the last of them in the form in
  which a dévissage meets it, namely an isomorphism `X ⊞ X' ≅ C`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂

namespace CategoryTheory.PullbackData.LimitSystem

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]
  {P : PullbackData A D} {b : A} {J : Type w} [Preorder J] {S : LimitSystem (A := A) b J}

/-- **The colimit statement is closed under direct summands of its first argument.**  If `X` is a
retract of `C` and `Hom(k^*C, k^*Y)` is the filtered colimit of the `Hom(k_j^*C, k_j^*Y)`, then
`Hom(k^*X, k^*Y)` is the filtered colimit of the `Hom(k_j^*X, k_j^*Y)`.

Neither directedness of the index nor any additive structure is used: the retraction
`i ≫ r = 𝟙 X` transports each of the three clauses of `Stacks.IsStagesColimit` on its own. -/
theorem IsColim.of_retract (hP : P.IsCoherent) {X C Y : D b} (h : Retract X C)
    (hC : S.IsColim P C Y) : S.IsColim P X Y where
  ι_trans i j hij φ := projHom_trans hP X Y hij φ
  exists_stage ψ := by
    obtain ⟨i, φ, hφ⟩ := hC.exists_stage ((P.pull S.limitToBase).map h.r ≫ ψ)
    refine ⟨i, (P.pull (S.toBase i)).map h.i ≫ φ, ?_⟩
    rw [projHom_map_comp, hφ, ← Functor.map_comp_assoc, h.retract, Functor.map_id,
      Category.id_comp]
  exists_trans_eq i φ φ' hφ := by
    obtain ⟨j, hij, hj⟩ := hC.exists_trans_eq i ((P.pull (S.toBase i)).map h.r ≫ φ)
      ((P.pull (S.toBase i)).map h.r ≫ φ') (by rw [projHom_map_comp, projHom_map_comp, hφ])
    refine ⟨j, hij, ?_⟩
    rw [trans_map_comp, trans_map_comp] at hj
    have := congrArg (fun t => (P.pull (S.toBase j)).map h.i ≫ t) hj
    simpa only [← Functor.map_comp_assoc, h.retract, Functor.map_id, Category.id_comp] using this

section Biprod

variable [∀ a, Preadditive (D a)]

/-- **The colimit statement passes from a binary biproduct to its first summand.** -/
theorem IsColim.of_biprod_left (hP : P.IsCoherent) {X X' Y : D b} [HasBinaryBiproduct X X']
    (hC : S.IsColim P (X ⊞ X') Y) : S.IsColim P X Y :=
  hC.of_retract hP ⟨biprod.inl, biprod.fst, by simp⟩

/-- **The colimit statement passes from a binary biproduct to its second summand.** -/
theorem IsColim.of_biprod_right (hP : P.IsCoherent) {X X' Y : D b} [HasBinaryBiproduct X X']
    (hC : S.IsColim P (X ⊞ X') Y) : S.IsColim P X' Y :=
  hC.of_retract hP ⟨biprod.inr, biprod.snd, by simp⟩

end Biprod

variable [∀ a, HasShift (D a) ℤ]

/-- **The colimit statement at every shift is closed under direct summands of its first
argument.** -/
theorem ShiftedIsColim.of_retract (hP : P.IsCoherent) {X C Y : D b} (h : Retract X C)
    (hC : ShiftedIsColim S P C Y) : ShiftedIsColim S P X Y :=
  fun n ↦ (hC n).of_retract hP (h.map (shiftFunctor (D b) n))

section ShiftedBiprod

variable [∀ a, Preadditive (D a)]

/-- **The colimit statement at every shift passes from a binary biproduct to its first
summand.** -/
theorem ShiftedIsColim.of_biprod_left (hP : P.IsCoherent) {X X' Y : D b}
    [HasBinaryBiproduct X X'] (hC : ShiftedIsColim S P (X ⊞ X') Y) : ShiftedIsColim S P X Y :=
  hC.of_retract hP ⟨biprod.inl, biprod.fst, by simp⟩

/-- **The colimit statement at every shift passes from a binary biproduct to its second
summand.** -/
theorem ShiftedIsColim.of_biprod_right (hP : P.IsCoherent) {X X' Y : D b}
    [HasBinaryBiproduct X X'] (hC : ShiftedIsColim S P (X ⊞ X') Y) : ShiftedIsColim S P X' Y :=
  hC.of_retract hP ⟨biprod.inr, biprod.snd, by simp⟩

variable [IsDirected J (· ≤ ·)]

/-- **The direct-summand closure in the form a dévissage meets it**: if `X ⊞ X'` is isomorphic to
an object `C` for which the colimit statement holds at every shift, it holds at every shift for
`X`.

This is the step that makes a dévissage over an affine base terminate.  There a finite projective
module is exhibited as a summand of a finite free one by an isomorphism `P ⊞ Q ≅ R^n`, not as a
literal biproduct factor of it, so the iso has to be absorbed. -/
theorem ShiftedIsColim.of_biprod_iso (hP : P.IsCoherent) {X X' C Y : D b}
    [HasBinaryBiproduct X X'] (e : X ⊞ X' ≅ C) (hC : ShiftedIsColim S P C Y) :
    ShiftedIsColim S P X Y :=
  ShiftedIsColim.of_biprod_left (X' := X') hP (hC.of_iso hP e.symm)

end ShiftedBiprod

end CategoryTheory.PullbackData.LimitSystem

end
