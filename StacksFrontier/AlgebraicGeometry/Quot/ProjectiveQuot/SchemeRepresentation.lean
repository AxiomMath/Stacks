module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.HilbertLocusProper
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.ChangeOfField
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible

/-!
# `Quot^P_{𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ}` is represented by a scheme proper over `Spec ℤ`

For `n ≥ 0`, `r ≥ 1` and `P ∈ ℚ[t]`, the functor `T ↦ Quot^P_{𝒪^{⊕ r}/ℙⁿ/ℤ}(T)` on schemes
(`AlgebraicGeometry.ProjectiveQuot.hilbertFunctor`) is represented by a scheme proper over
`Spec ℤ`, the scheme-level content of Stacks 0DPA. With `m`, `N`, `p` as in the proof:

* if `p ≤ N`, by the Hilbert locus `Z_P ⊆ G(N - p, N)`
  (`AlgebraicGeometry.ProjectiveQuot.hilbertFunctorIso`,
  `AlgebraicGeometry.ProjectiveQuot.isProper_hilbertLocus_terminalFrom`);
* if `N < p`, `Quot^P(T)` is empty for every nonempty `T`
  (`AlgebraicGeometry.ProjectiveQuot.hilbertFamilies_eq_empty_of_lt`) and a singleton for the empty
  scheme (every module on it is zero), so the empty scheme represents it.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.exists_isProper_iso_hilbertFunctor`.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveQuot

variable {n r : ℕ}

/-- Over an empty scheme `Quot^P(T)` has exactly one element: every module on `ℙⁿ_T` is zero. -/
theorem subsingleton_subobject_freeModule_of_isEmpty {T : Scheme.{u}} [IsEmpty T] :
    Subsingleton (Subobject (freeModule n r T)) := by
  have : IsEmpty (projectiveSpaceOver n T) :=
    ⟨fun x => IsEmpty.false ((projectiveSpaceOver n T ↘ T) x)⟩
  refine ⟨fun K K' => Subobject.eq_of_comm
    ((Stacks.Duality.ProperOverField.isZero_modules_of_isEmpty _).iso
      (Stacks.Duality.ProperOverField.isZero_modules_of_isEmpty _)) ?_⟩
  exact (Stacks.Duality.ProperOverField.isZero_modules_of_isEmpty (freeModule n r T)).eq_of_tgt _ _

/-- Over an empty scheme `T`, every subobject of `𝒪^{⊕ r}` on `ℙⁿ_T` lies in `Quot^P(T)`. -/
theorem mem_hilbertFamilies_of_isEmpty {P : Polynomial ℚ} {T : Scheme.{u}} [IsEmpty T]
    (K : Subobject (freeModule n r T)) : K ∈ hilbertFamilies n r P T := by
  have : IsEmpty (projectiveSpaceOver n T) :=
    ⟨fun x => IsEmpty.false ((projectiveSpaceOver n T ↘ T) x)⟩
  have hfp : (quotient K).IsFinitePresentation :=
    Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
      ((Stacks.Duality.ProperOverField.isZero_modules_of_isEmpty _).iso
        (Stacks.Duality.ProperOverField.isZero_modules_of_isEmpty _))
      (Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_free_of_finite
        (projectiveSpaceOver n T) PEmpty)
  exact ⟨⟨hfp, fun x => isEmptyElim x⟩, fun t => isEmptyElim t⟩

/-- A scheme carrying a member of `Quot^P` is empty when `N < p`. -/
theorem isEmpty_of_mem_hilbertFamilies_of_lt (hr : 1 ≤ r) {P : Polynomial ℚ}
    (hlt : freeRank.{u} n r (regularityIndex.{u} n r hr P) < quotRank.{u} n r hr P)
    {T : Scheme.{u}} {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T) :
    IsEmpty T :=
  ⟨fun t => by
    rw [hilbertFamilies_eq_empty_of_lt hr hlt t] at hK
    exact hK⟩

/-- If `N < p`, then `Quot^P(T)` has at most one element, for every scheme `T`. -/
theorem subsingleton_hilbertFamilies_of_lt (hr : 1 ≤ r) {P : Polynomial ℚ}
    (hlt : freeRank.{u} n r (regularityIndex.{u} n r hr P) < quotRank.{u} n r hr P)
    (T : Scheme.{u}) : Subsingleton (hilbertFamilies n r P T) :=
  ⟨fun K K' => by
    have := isEmpty_of_mem_hilbertFamilies_of_lt hr hlt K.2
    have : Subsingleton (Subobject (freeModule n r T)) :=
      subsingleton_subobject_freeModule_of_isEmpty
    exact Subtype.ext (Subsingleton.elim _ _)⟩

/-- There is at most one morphism from any scheme `T` to the empty scheme. -/
theorem subsingleton_hom_empty (T : Scheme.{u}) : Subsingleton (T ⟶ (∅ : Scheme.{u})) :=
  ⟨fun f g => by
    have : IsEmpty T := ⟨fun t => isEmptyElim (f t)⟩
    exact isInitialOfIsEmpty.hom_ext _ _⟩

/-- **The scheme-level form of Stacks 0DPA**: `Quot^P_{𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ}` is represented by a scheme
proper over `Spec ℤ`. -/
theorem exists_isProper_iso_hilbertFunctor (n r : ℕ) (hr : 1 ≤ r) (P : Polynomial ℚ) :
    ∃ X : Scheme.{u}, IsProper (terminal.from X) ∧
      Nonempty (hilbertFunctor.{u} n r P ≅ yoneda.obj X ⋙ uliftFunctor.{u + 1}) := by
  by_cases hp : quotRank.{u} n r hr P ≤ freeRank.{u} n r (regularityIndex.{u} n r hr P)
  · exact ⟨_, isProper_hilbertLocus_terminalFrom hr hp, ⟨hilbertFunctorIso hr hp⟩⟩
  · have hlt := Nat.lt_of_not_le hp
    have hsub : ∀ T : Scheme.{u}ᵒᵖ,
        Subsingleton ((yoneda.obj (∅ : Scheme.{u}) ⋙ uliftFunctor.{u + 1}).obj T) := fun T =>
      have := subsingleton_hom_empty T.unop
      inferInstanceAs (Subsingleton (ULift.{u + 1} (T.unop ⟶ (∅ : Scheme.{u}))))
    refine ⟨∅, inferInstance, ⟨NatIso.ofComponents (fun T => Equiv.toIso
      (@equivOfSubsingletonOfSubsingleton ((hilbertFunctor.{u} n r P).obj T)
        ((yoneda.obj (∅ : Scheme.{u}) ⋙ uliftFunctor.{u + 1}).obj T)
        (subsingleton_hilbertFamilies_of_lt hr hlt T.unop) (hsub T)
        (fun K => have := isEmpty_of_mem_hilbertFamilies_of_lt hr hlt K.2
          ULift.up (isInitialOfIsEmpty.to _))
        (fun f => have : IsEmpty T.unop :=
            ⟨fun t => isEmptyElim ((show T.unop ⟶ (∅ : Scheme.{u}) from f.down) t)⟩
          ⟨⊤, mem_hilbertFamilies_of_isEmpty _⟩)))
      (fun _ => by ext; exact @Subsingleton.elim _ (hsub _) _ _)⟩⟩

end AlgebraicGeometry.ProjectiveQuot

end
