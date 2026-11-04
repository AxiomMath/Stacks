module

public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.ExternalTensorFunctorial
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteLocallyFreeBiprod

/-!
# Gathering finitely many external tensor products into one

Let `X` and `Y` be schemes over `S` and let `F` be a module on `X ×_S Y`. Given finitely many
morphisms `𝓔_l ⊠ 𝓖_l ⟶ F` with every `𝓔_l` finite locally free on `X` and every `𝓖_l` finite
locally free on `Y`, there is a single morphism `𝓔 ⊠ 𝓖 ⟶ F` with `𝓔` finite locally free on `X`
and `𝓖` finite locally free on `Y` through which each of them factors, namely the one attached
to `𝓔 = ⨁ 𝓔_l` and `𝓖 = ⨁ 𝓖_l`.

## Main results

* `AlgebraicGeometry.isFiniteLocallyFree_zero`: a zero module on a scheme is finite locally
  free.
* `AlgebraicGeometry.exists_factor_externalTensorProduct_fin` and
  `AlgebraicGeometry.exists_factor_externalTensorProduct`: **finitely many morphisms out of
  external tensor products of finite locally free modules factor through one**, for a family
  indexed by `Fin k` and by an arbitrary finite type.

## Implementation notes

The biproduct is formed one factor at a time, by induction on `Fin k`, so only the binary
statement `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_biprod` is needed and no
instance of `CategoryTheory.Limits.HasFiniteBiproducts` is required.

The factorizing morphism is produced inside an existential rather than as a function of the
index, which is what makes the passage from `Fin k` to an arbitrary finite type a substitution
along `Finite.equivFin` with no transport of morphisms.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 0FZ0](https://stacks.math.columbia.edu/tag/0FZ0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ZeroObject

universe u v

noncomputable section

namespace AlgebraicGeometry

/-- **A zero module on a scheme is finite locally free.** -/
theorem isFiniteLocallyFree_zero (Z : Scheme.{u}) :
    SheafOfModules.IsFiniteLocallyFree (R := Z.ringCatSheaf) (0 : Z.Modules) :=
  Stacks.Perfect.BoundedLocallyFreeComplexes.finiteLocallyFree_of_isZero Z 0 (isZero_zero _)

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **Finitely many morphisms out of external tensor products of finite locally free modules
factor through a single one.** For a family indexed by `Fin k`; the module on `X` is the
biproduct of the `k` modules on `X` and likewise on `Y`. -/
theorem exists_factor_externalTensorProduct_fin (F : (pullback f g).Modules) :
    ∀ (k : ℕ) (E : Fin k → X.Modules) (G : Fin k → Y.Modules),
      (∀ l, SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) (E l)) →
      (∀ l, SheafOfModules.IsFiniteLocallyFree (R := Y.ringCatSheaf) (G l)) →
      ∀ φ : (l : Fin k) → (externalTensorProduct f g (E l) (G l) ⟶ F),
      ∃ (E' : X.Modules) (G' : Y.Modules)
        (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E')
        (_ : SheafOfModules.IsFiniteLocallyFree (R := Y.ringCatSheaf) G')
        (θ : externalTensorProduct f g E' G' ⟶ F), ∀ l,
          ∃ ι : externalTensorProduct f g (E l) (G l) ⟶ externalTensorProduct f g E' G',
            ι ≫ θ = φ l := by
  intro k
  induction k with
  | zero =>
    intro E G _ _ φ
    exact ⟨0, 0, isFiniteLocallyFree_zero X, isFiniteLocallyFree_zero Y, 0, fun l => l.elim0⟩
  | succ k ih =>
    intro E G hE hG φ
    obtain ⟨E'', G'', hE'', hG'', θ'', hfac⟩ :=
      ih (fun j => E j.succ) (fun j => G j.succ) (fun j => hE _) (fun j => hG _)
        (fun j => φ j.succ)
    have := hE 0
    have := hG 0
    refine ⟨E 0 ⊞ E'', G 0 ⊞ G'', SheafOfModules.isFiniteLocallyFree_biprod _ _,
      SheafOfModules.isFiniteLocallyFree_biprod _ _,
      externalTensorProductMap f g biprod.fst biprod.fst ≫ φ 0 +
        externalTensorProductMap f g biprod.snd biprod.snd ≫ θ'', ?_⟩
    refine Fin.cases ⟨externalTensorProductMap f g biprod.inl biprod.inl, ?_⟩ fun j => ?_
    · rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
        externalTensorProductMap_comp, externalTensorProductMap_comp]
      simp [externalTensorProductMap_id, externalTensorProductMap_zero_zero]
    · obtain ⟨ι₀, hι₀⟩ := hfac j
      refine ⟨ι₀ ≫ externalTensorProductMap f g biprod.inr biprod.inr, ?_⟩
      rw [Category.assoc, Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
        externalTensorProductMap_comp, externalTensorProductMap_comp]
      simp [externalTensorProductMap_id, externalTensorProductMap_zero_zero, hι₀]

/-- **Finitely many morphisms out of external tensor products of finite locally free modules
factor through a single one**, for a family indexed by an arbitrary finite type. -/
theorem exists_factor_externalTensorProduct (F : (pullback f g).Modules)
    {Λ : Type v} [Finite Λ] (E : Λ → X.Modules) (G : Λ → Y.Modules)
    (hE : ∀ l, SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) (E l))
    (hG : ∀ l, SheafOfModules.IsFiniteLocallyFree (R := Y.ringCatSheaf) (G l))
    (φ : (l : Λ) → (externalTensorProduct f g (E l) (G l) ⟶ F)) :
    ∃ (E' : X.Modules) (G' : Y.Modules)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E')
      (_ : SheafOfModules.IsFiniteLocallyFree (R := Y.ringCatSheaf) G')
      (θ : externalTensorProduct f g E' G' ⟶ F), ∀ l,
        ∃ ι : externalTensorProduct f g (E l) (G l) ⟶ externalTensorProduct f g E' G',
          ι ≫ θ = φ l := by
  obtain ⟨E', G', hE', hG', θ, hfac⟩ :=
    exists_factor_externalTensorProduct_fin f g F (Nat.card Λ)
      (fun j => E ((Finite.equivFin Λ).symm j)) (fun j => G ((Finite.equivFin Λ).symm j))
      (fun j => hE _) (fun j => hG _) (fun j => φ ((Finite.equivFin Λ).symm j))
  refine ⟨E', G', hE', hG', θ, fun l => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, (Finite.equivFin Λ).symm j = l :=
    ⟨Finite.equivFin Λ l, Equiv.symm_apply_apply _ _⟩
  subst hj
  exact hfac j

end AlgebraicGeometry

end

end
