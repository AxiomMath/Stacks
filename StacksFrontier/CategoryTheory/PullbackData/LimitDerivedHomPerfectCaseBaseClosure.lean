module

public import StacksFrontier.CategoryTheory.PullbackData.LimitDerivedHomPerfectCaseSummand

/-!
# The colimit statement of a system over a base, at a zero object and at a finite biproduct

Let `P` be a coherent pullback pseudofunctor datum and let `S` be a directed system over a base
`b` with a cone, a `CategoryTheory.PullbackData.LimitSystem`.  For objects `X`, `Y` of `D b` the
statement that `Hom(k^*X, k^*Y)` is the filtered colimit of the `Hom(k_j^*X, k_j^*Y)` is
`CategoryTheory.PullbackData.LimitSystem.IsColim`, and its version at every shift of the first
argument is `CategoryTheory.PullbackData.LimitSystem.ShiftedIsColim`.

`StacksFrontier/CategoryTheory/PullbackData/LimitSystemColimShift.lean` proves that the class of
first arguments satisfying `ShiftedIsColim` is closed under isomorphism, shift, the three
vertices of a distinguished triangle and *binary* biproducts, and
`StacksFrontier/CategoryTheory/PullbackData/LimitDerivedHomPerfectCaseSummand.lean` adds closure
under direct summands.  Two closure properties are still missing, and they are exactly the two
that the dévissage of a strictly perfect complex
(`Stacks.Cohomology.StrictlyPerfectDevissage.property_of_isStrictlyPerfect`) asks for on top of
those: the statement at a **zero object**, and the statement at a biproduct of an arbitrary
**finite family** rather than of two objects.

Both are proved here by hand rather than by induction on the family.  At a zero object every
hom-set in sight is a zero group, because the inverse images are additive, so all three clauses
of `Stacks.IsStagesColimit` are vacuous once the index is nonempty.  At a finite biproduct the
proof is the one of `CategoryTheory.PullbackData.LimitSystem.IsColim.biprod` with the two
summands replaced by a finite family: a morphism out of `k^*(⨁ f)` is the sum over the family of
its components, by `CategoryTheory.Limits.biproduct.total` and the additivity of `k^*`, the
finitely many stages produced by the summands are bounded above by directedness
(`Finset.exists_le`), and the maps of the system are additive.

## Main results

* `CategoryTheory.PullbackData.LimitSystem.IsColim.of_isZero` and
  `ShiftedIsColim.of_isZero`: the statement holds at a zero object.
* `CategoryTheory.PullbackData.LimitSystem.IsColim.biproduct` and
  `ShiftedIsColim.biproduct`: the statement is closed under biproducts of a finite family of
  first arguments.
* `CategoryTheory.PullbackData.LimitSystem.ShiftedIsColim.of_shift`: the converse of
  `ShiftedIsColim.shift` — the statement at `X⟦m⟧` gives the statement at `X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v₁ u₁ v₂ u₂

namespace CategoryTheory.PullbackData.LimitSystem

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]
  {P : PullbackData A D} {b : A} {J : Type w} [Preorder J] {S : LimitSystem (A := A) b J}

section Additive

variable [∀ a, Preadditive (D a)] [∀ {a b : A} (f : a ⟶ b), (P.pull f).Additive]

/-- **The colimit statement holds at a zero first argument.**  The inverse images are additive,
so `k^*X` is a zero object and every hom-set out of it is a zero group; all three clauses then
hold for want of anything to say. -/
theorem IsColim.of_isZero [Nonempty J] {X Y : D b} (hX : IsZero X) : S.IsColim P X Y where
  ι_trans _ _ _ _ := ((P.pull S.limitToBase).map_isZero hX).eq_of_src _ _
  exists_stage _ := ⟨Classical.arbitrary J, 0,
    ((P.pull S.limitToBase).map_isZero hX).eq_of_src _ _⟩
  exists_trans_eq i _ _ _ := ⟨i, le_refl i, ((P.pull (S.toBase i)).map_isZero hX).eq_of_src _ _⟩

/-- **A morphism out of the image of a finite biproduct under an additive functor is the sum of
its components.**  This is the finite-family form of
`CategoryTheory.PullbackData.LimitSystem.eq_map_fst_comp_add`. -/
theorem eq_sum_map_π_comp {C E : Type*} [Category* C] [Category* E] [Preadditive C]
    [Preadditive E] (F : C ⥤ E) [F.Additive] {ι : Type} [Fintype ι] (f : ι → C)
    [HasBiproduct f] {W : E} (x : F.obj (⨁ f) ⟶ W) :
    x = ∑ j : ι, F.map (biproduct.π f j) ≫ F.map (biproduct.ι f j) ≫ x := by
  have h : ∀ j : ι, F.map (biproduct.π f j) ≫ F.map (biproduct.ι f j) ≫ x =
      F.map (biproduct.π f j ≫ biproduct.ι f j) ≫ x := fun j => by
    rw [F.map_comp, Category.assoc]
  rw [Finset.sum_congr rfl fun j _ => h j, ← Preadditive.sum_comp, ← F.map_sum,
    biproduct.total, F.map_id, Category.id_comp]

/-- The map of the system to the vertex is additive over a finite sum. -/
theorem projHom_sum (X Y : D b) (j : J) {ι : Type} (s : Finset ι)
    (φ : ι → ((P.pull (S.toBase j)).obj X ⟶ (P.pull (S.toBase j)).obj Y)) :
    S.projHom P X Y j (∑ k ∈ s, φ k) = ∑ k ∈ s, S.projHom P X Y j (φ k) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa only [Finset.sum_empty] using projHom_zero (S := S) X Y j
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, projHom_add, ih]

/-- The transition map of the system is additive. -/
theorem trans_add (X Y : D b) {i j : J} (h : i ≤ j)
    (φ ψ : (P.pull (S.toBase i)).obj X ⟶ (P.pull (S.toBase i)).obj Y) :
    S.trans P X Y i j h (φ + ψ) = S.trans P X Y i j h φ + S.trans P X Y i j h ψ :=
  factorHom_add _ φ ψ

/-- The transition map of the system is additive over a finite sum. -/
theorem trans_sum (X Y : D b) {i j : J} (h : i ≤ j) {ι : Type} (s : Finset ι)
    (φ : ι → ((P.pull (S.toBase i)).obj X ⟶ (P.pull (S.toBase i)).obj Y)) :
    S.trans P X Y i j h (∑ k ∈ s, φ k) = ∑ k ∈ s, S.trans P X Y i j h (φ k) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa only [Finset.sum_empty] using trans_zero (S := S) X Y h
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, trans_add, ih]

variable (hP : P.IsCoherent)
include hP

/-- **The colimit statement is closed under biproducts of a finite family of first arguments.**

The proof is `CategoryTheory.PullbackData.LimitSystem.IsColim.biprod` with the two summands
replaced by a finite family: a morphism out of `k^*(⨁ f)` is the sum of its components, the
finitely many stages the summands produce have an upper bound by directedness, and the maps of
the system are additive. -/
theorem IsColim.biproduct [IsDirected J (· ≤ ·)] [Nonempty J] {ι : Type} [Finite ι] (f : ι → D b)
    [HasBiproduct f] (Y : D b) (h : ∀ j, S.IsColim P (f j) Y) : S.IsColim P (⨁ f) Y := by
  classical
  have _ : Fintype ι := Fintype.ofFinite ι
  refine ⟨fun i j hij φ => projHom_trans hP _ Y hij φ, fun ψ => ?_, fun i φ φ' hφ => ?_⟩
  · choose m φ hφ using fun j : ι =>
      (h j).exists_stage ((P.pull S.limitToBase).map (biproduct.ι f j) ≫ ψ)
    obtain ⟨M, hM⟩ := Finset.exists_le (Finset.univ.image m)
    have hm : ∀ j : ι, m j ≤ M := fun j =>
      hM _ (Finset.mem_image_of_mem m (Finset.mem_univ j))
    refine ⟨M, ∑ j : ι, (P.pull (S.toBase M)).map (biproduct.π f j) ≫
      S.trans P (f j) Y (m j) M (hm j) (φ j), ?_⟩
    rw [projHom_sum]
    refine (Finset.sum_congr rfl fun j _ => ?_).trans
      (eq_sum_map_π_comp (P.pull S.limitToBase) f ψ).symm
    rw [projHom_map_comp, projHom_trans hP, hφ]
  · choose M hiM hM using fun j : ι => (h j).exists_trans_eq i
      ((P.pull (S.toBase i)).map (biproduct.ι f j) ≫ φ)
      ((P.pull (S.toBase i)).map (biproduct.ι f j) ≫ φ')
      (by rw [projHom_map_comp, projHom_map_comp, hφ])
    obtain ⟨N, hN⟩ := Finset.exists_le (insert i (Finset.univ.image M))
    have hMN : ∀ j : ι, M j ≤ N := fun j =>
      hN _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem M (Finset.mem_univ j)))
    have hiN : i ≤ N := hN _ (Finset.mem_insert_self i _)
    refine ⟨N, hiN, ?_⟩
    have key : ∀ j : ι, (P.pull (S.toBase N)).map (biproduct.ι f j) ≫
        S.trans P (⨁ f) Y i N hiN φ =
        (P.pull (S.toBase N)).map (biproduct.ι f j) ≫ S.trans P (⨁ f) Y i N hiN φ' := by
      intro j
      have e := congrArg (S.trans P (f j) Y (M j) N (hMN j)) (hM j)
      rw [trans_trans hP, trans_trans hP] at e
      rw [trans_map_comp, trans_map_comp] at e
      exact e
    rw [eq_sum_map_π_comp (P.pull (S.toBase N)) f (S.trans P (⨁ f) Y i N hiN φ),
      eq_sum_map_π_comp (P.pull (S.toBase N)) f (S.trans P (⨁ f) Y i N hiN φ')]
    exact Finset.sum_congr rfl fun j _ => by rw [key j]

end Additive

section Shifted

variable [∀ a, HasShift (D a) ℤ] [∀ a, Preadditive (D a)]
  [∀ {a b : A} (f : a ⟶ b), (P.pull f).Additive] [IsDirected J (· ≤ ·)]

variable (hP : P.IsCoherent)
include hP

omit [IsDirected J (· ≤ ·)] hP in
/-- **The statement at every shift holds at a zero first argument.** -/
theorem ShiftedIsColim.of_isZero [Nonempty J] [∀ a (n : ℤ), (shiftFunctor (D a) n).Additive]
    {X Y : D b} (hX : IsZero X) : ShiftedIsColim S P X Y :=
  fun n => IsColim.of_isZero ((shiftFunctor (D b) n).map_isZero hX)

/-- **The statement at every shift is closed under biproducts of a finite family of first
arguments.** -/
theorem ShiftedIsColim.biproduct [Nonempty J] [HasFiniteBiproducts (D b)]
    [∀ (n : ℤ), (shiftFunctor (D b) n).Additive] {ι : Type} [Finite ι] (f : ι → D b)
    (Y : D b) (h : ∀ j, ShiftedIsColim S P (f j) Y) :
    ShiftedIsColim S P (⨁ f) Y := by
  classical
  have _ : Fintype ι := Fintype.ofFinite ι
  intro n
  exact (IsColim.biproduct hP (fun j => (f j)⟦n⟧) Y fun j => h j n).of_iso_fst hP
    ((shiftFunctor (D b) n).mapBiproduct f).symm

omit [∀ {a b : A} (f : a ⟶ b), (P.pull f).Additive] in
/-- **The statement at every shift at `X⟦m⟧` gives it at `X`**, the converse of
`CategoryTheory.PullbackData.LimitSystem.ShiftedIsColim.shift`. -/
theorem ShiftedIsColim.of_shift [∀ a (n : ℤ), (shiftFunctor (D a) n).Additive] {X Y : D b}
    (m : ℤ) (hX : ShiftedIsColim S P (X⟦m⟧) Y) : ShiftedIsColim S P X Y :=
  (hX.shift hP (-m)).of_iso hP ((shiftFunctorCompIsoId (D b) m (-m) (by omega)).app X)

end Shifted

end CategoryTheory.PullbackData.LimitSystem

end
